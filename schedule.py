#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
当日任务排程器。

用法:
    python3 -I schedule.py tasks.json slots.json day_plan.csv

输出:
    day_plan.csv      列: task, slot, site, order, note
    plan_checks.json  五项检查结果(拓扑序 / 槽位不越界 / 配额分配 / 覆盖全部任务 / 无环)

规则:
  1. 上游编号在任务清单中不存在的任务(直接或经依赖链间接引用缺失任务)不参加
     当日排程, 也不写入当日计划。
  2. 参加排程的任务按依赖拓扑序决定先后(Kahn + 最小堆, 键为 (earliest, id));
     同站点内即按 earliest 再按 id 排序。order 从 1 起连续编号。
  3. 配额比例之和 > 1 时先归一化。配额是计划供给、容量是上限:
       a. 各站全天连续目标 = 全天容量池 * 归一化份额;
       b. 各站独立取离目标最近的整数并截断到该站全天容量(容量约束下 L1 偏差
          全局最优, 半数取较小值, 确定性);
       c. 全天整数配额按各小时容量权重以最大余数法分摊到小时, 每小时不越容量。
  4. 任务不可拆分: 需要的整槽数 n = max(1, ceil(dur_min / 60))。
     不足一小时与零时长任务各占一整槽; 超出一小时的部分向上进位成整槽;
     一个任务占用同一站点连续 n 个小时, 每小时各占一个槽。
  5. 配额槽位在就绪小时放不下时, 任务顺延到后续第一个能完整容纳它的小时,
     note 标注 "顺延"; 溢出规划窗口的小时按该站末小时容量兜底, 同样标注顺延。
  6. slot 写两位数字的起始小时(如 "08"), 不写槽号; 顺延任务 note 写 "顺延"。
  7. 五项检查任一失败, plan_checks.json 的 overall 为 fail 且进程退出码为 1。
  8. 全程确定性排序, 重复生成同日计划字节级一致。
"""

import argparse
import csv
import heapq
import json
import math
import sys
from collections import defaultdict


# ---------------------------------------------------------------- 输入
def load_json(path):
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


# ------------------------------------------------------------ 悬空依赖过滤
def split_tasks(tasks):
    """
    把任务划分为参加排程 / 不参加排程两类。
    上游编号不存在(直接或间接)的任务不参加; 依赖图上不可达缺失任务的才参加。
    """
    by_id = {t["id"]: t for t in tasks}
    excluded = set()

    def bad(tid, stack):
        """该任务(经依赖链)是否引用了清单中不存在的上游。"""
        if tid in excluded or tid in stack:
            return tid in excluded
        stack.add(tid)
        for d in by_id[tid]["deps"]:
            if d not in by_id or bad(d, stack):
                excluded.add(tid)
                break
        stack.discard(tid)
        return tid in excluded

    for t in tasks:
        bad(t["id"], set())

    participating = [t for t in tasks if t["id"] not in excluded]
    return participating, sorted(excluded)


# ---------------------------------------------------------------- 配额与槽位
def normalize_quota(sites, quota):
    """配额比例之和可能 > 1(也可能 < 1), 归一化为份额。"""
    total = sum(quota[s] for s in sites)
    return {s: quota[s] / total for s in sites}


def largest_remainder(weights, total):
    """最大余数整数分摊: weights 为权重 dict, 结果之和为 total, 平局按键名。"""
    raw = {k: total * weights[k] for k in weights}
    out = {k: int(raw[k]) for k in weights}           # 正数截断即向下取整
    left = total - sum(out.values())
    order = sorted(weights, key=lambda k: (-(raw[k] - out[k]), k))
    for k in order[:left]:
        out[k] += 1
    return out


def nearest_integer_clamped(x, hi):
    """离 x 最近的整数截断到 [0, hi]; 恰好半数时取较小值(确定性)。"""
    lo = math.floor(x)
    candidates = [lo] if lo == math.ceil(x) else [lo, lo + 1]
    best = min(candidates, key=lambda c: (abs(c - x), c))
    return max(0, min(hi, best))


def allocate_slots(sites, hours, capacity, quota_norm):
    """
    配额是计划供给、容量是上限。返回:
      alloc[s][h]    站点 s 在小时 h 的配额可用槽位(可小于物理容量)
      target_cont    连续目标(报告用)
      day_alloc      各站全天整数配额
      deviation      全天合计相对连续目标的 L1 偏差
    """
    cap_total = {s: sum(capacity[s][h] for h in hours) for s in sites}
    day_pool = sum(cap_total.values())
    target_cont = {s: day_pool * quota_norm[s] for s in sites}

    # 站点间无总量耦合, 各自取容量内最近整数即 L1 全局最优
    day_alloc = {
        s: nearest_integer_clamped(target_cont[s], cap_total[s]) for s in sites
    }

    alloc = {s: {} for s in sites}
    for s in sites:
        weights = {h: capacity[s][h] / cap_total[s] for h in hours}
        spread = largest_remainder(weights, day_alloc[s])
        for h in hours:
            assert 0 <= spread[h] <= capacity[s][h]
            alloc[s][h] = spread[h]

    deviation = sum(abs(day_alloc[s] - target_cont[s]) for s in sites)
    return alloc, target_cont, day_alloc, deviation


# ---------------------------------------------------------------- 拓扑序
def topo_sort(tasks):
    """Kahn + 最小堆 (earliest, id); 返回 (拓扑顺序, 环上任务)。"""
    by_id = {t["id"]: t for t in tasks}
    indeg = {t["id"]: 0 for t in tasks}
    children = defaultdict(list)
    for t in tasks:
        for d in t["deps"]:
            indeg[t["id"]] += 1
            children[d].append(t["id"])

    heap = []
    for tid, d in indeg.items():
        if d == 0:
            heapq.heappush(heap, (by_id[tid]["earliest"], tid))

    order = []
    while heap:
        _, tid = heapq.heappop(heap)
        order.append(tid)
        for c in children[tid]:
            indeg[c] -= 1
            if indeg[c] == 0:
                heapq.heappush(heap, (by_id[c]["earliest"], c))

    cyclic = sorted(tid for tid, d in indeg.items() if d > 0)
    return order, cyclic


# ---------------------------------------------------------------- 排程
def slots_needed(dur_min):
    """不可拆分: 不足一小时与零时长各占一整槽, 超出部分向上进位。"""
    return max(1, math.ceil(dur_min / 60))


def schedule_tasks(tasks, order, hours, capacity, alloc):
    """
    按拓扑序贪心放置。返回 placements:
      {tid: {site, n, start, end, slots:[slot_idx...], deferred}}
    溢出规划窗口的小时按该站末小时容量兜底, 并一律视为顺延。
    """
    by_id = {t["id"]: t for t in tasks}
    first_hour = int(hours[0])
    labels = list(hours)

    def label(hi):
        while len(labels) <= hi:
            labels.append(f"{(first_hour + len(labels)) % 24:02d}")
        return labels[hi]

    def available(site, hi):
        if hi < len(hours):
            return alloc[site][hours[hi]]
        return capacity[site][hours[-1]]              # 窗口外兜底: 物理容量

    used = defaultdict(set)                           # (site, hi) -> {slot_idx}
    end_at = {}                                       # task id -> 最后占用小时
    placements = {}

    for topo_pos, tid in enumerate(order, start=1):
        t = by_id[tid]
        site = t["site"]
        n = slots_needed(t["dur_min"])
        earliest_idx = int(t["earliest"]) - first_hour
        dep_ends = [end_at[d] for d in t["deps"]]
        eligible = max([earliest_idx] + [x + 1 for x in dep_ends]) \
            if dep_ends else earliest_idx

        h0 = eligible
        while True:                                   # 首个连续 n 小时都有空槽的起点
            if all(len(used[(site, h0 + k)]) < available(site, h0 + k)
                   for k in range(n)):
                break
            h0 += 1

        deferred = h0 > eligible
        slots = []
        for k in range(n):
            hi = h0 + k
            cap = available(site, hi)
            free = next(i for i in range(1, cap + 1)
                        if i not in used[(site, hi)])
            used[(site, hi)].add(free)
            slots.append(free)

        placements[tid] = {
            "site": site,
            "n": n,
            "start": h0,
            "end": h0 + n - 1,
            "slots": slots,
            "deferred": deferred or h0 + n - 1 >= len(hours),
            "order": topo_pos,
            "label": label(h0),
        }
        end_at[tid] = h0 + n - 1

    return placements, labels


# ---------------------------------------------------------------- 五项检查
def check_acyclic(all_tasks):
    """检查 5: 无环(DFS 三色法, 基于完整清单, 缺失上游视为无边)。"""
    by_id = {t["id"]: t for t in all_tasks}
    color = {tid: 0 for tid in by_id}                 # 0 白 1 灰 2 黑
    ok = True

    def dfs(u):
        nonlocal ok
        color[u] = 1
        for v in by_id[u]["deps"]:
            if v not in by_id:
                continue
            if color[v] == 1:
                ok = False
            elif color[v] == 0:
                dfs(v)
        color[u] = 2

    for tid in sorted(by_id):
        if color[tid] == 0:
            dfs(tid)
    return ok, ("依赖图无环" if ok else "依赖图存在环")


def check_topology(tasks, placements, hours):
    """检查 1: 拓扑序(order 连续、earliest 约束、依赖先后、顺延标注一致)。"""
    by_id = {t["id"]: t for t in tasks}
    base = int(hours[0])
    problems = []

    orders = sorted(p["order"] for p in placements.values())
    if orders != list(range(1, len(placements) + 1)):
        problems.append("order 不是从 1 起的连续编号")

    for t in tasks:
        tid = t["id"]
        if tid not in placements:
            continue                                    # 环上任务未放置, 由无环检查判定
        p = placements[tid]
        earliest_idx = int(t["earliest"]) - base
        if p["start"] < earliest_idx:
            problems.append(f"{tid} 起始小时早于 earliest")
        for d in t["deps"]:
            if placements[d]["end"] >= p["start"]:
                problems.append(f"{tid} 未排在依赖 {d} 完成之后")
            if placements[d]["order"] >= p["order"]:
                problems.append(f"{tid} 的 order 未排在依赖 {d} 之后")
        dep_ready = [placements[d]["end"] + 1 for d in t["deps"]]
        eligible = max([earliest_idx] + dep_ready) if dep_ready else earliest_idx
        expect_defer = p["start"] > eligible or p["end"] >= len(hours)
        if expect_defer != p["deferred"]:
            problems.append(f"{tid} 的顺延标注与实际不符")

    return not problems, ("拓扑先后、earliest 与顺延标注均正确"
                          if not problems else "; ".join(problems))


def check_slots(tasks, placements, hours, capacity, alloc):
    """检查 2: 槽位不越界(配额可用数内、同站同时刻槽位不重复、占槽数正确)。"""
    by_id = {t["id"]: t for t in tasks}
    problems = []
    seen = defaultdict(set)

    for t in tasks:
        tid = t["id"]
        if tid not in placements:
            continue                                    # 环上任务未放置, 由无环检查判定
        p = placements[tid]
        need = slots_needed(t["dur_min"])
        if p["n"] != need or len(p["slots"]) != need:
            problems.append(f"{tid} 占槽数 {p['n']}, 应为 {need}")
        for k in range(p["n"]):
            hi, si = p["start"] + k, p["slots"][k]
            site = p["site"]
            limit = alloc[site][hours[hi]] if hi < len(hours) \
                else capacity[site][hours[-1]]
            if not (1 <= si <= limit):
                problems.append(f"{tid} 槽位越界({site} 小时{hi} 槽{si} 上限{limit})")
            if si in seen[(site, hi)]:
                problems.append(f"{site} 小时{hi} 槽{si} 重复占用")
            seen[(site, hi)].add(si)

    return not problems, ("槽位均在配额可用范围内且无重复"
                          if not problems else "; ".join(problems))


def check_quota(sites, hours, capacity, quota_norm, alloc, deviation):
    """检查 3: 配额分配(逐小时不越容量、全天 L1 最优、逐小时最大余数一致)。"""
    problems = []
    cap_total = {s: sum(capacity[s][h] for h in hours) for s in sites}
    day_pool = sum(cap_total.values())
    target = {s: day_pool * quota_norm[s] for s in sites}
    day_total = {s: sum(alloc[s][h] for h in hours) for s in sites}

    for h in hours:
        for s in sites:
            if not (0 <= alloc[s][h] <= capacity[s][h]):
                problems.append(f"{s} 小时 {h} 分配 {alloc[s][h]} 越容量")

    for s in sites:
        expect = min(range(0, cap_total[s] + 1),
                     key=lambda x: (abs(x - target[s]), x))
        if day_total[s] != expect:
            problems.append(f"{s} 全天 {day_total[s]} 非 L1 最优(应为 {expect})")
        weights = {h: capacity[s][h] / cap_total[s] for h in hours}
        expect_h = largest_remainder(weights, day_total[s])
        for h in hours:
            if expect_h[h] != alloc[s][h]:
                problems.append(f"{s} 小时 {h} 分摊与最大余数法不一致")

    best_possible = sum(
        min(abs(x - target[s]) for x in range(0, cap_total[s] + 1))
        for s in sites
    )
    if deviation > best_possible + 1e-9:
        problems.append(f"L1 偏差 {deviation:.4f} 未达理论最小 {best_possible:.4f}")

    msg = (f"全天 L1 偏差 {deviation:.4f}(理论最小 {best_possible:.4f}), "
           f"逐小时不越容量且为最大余数分摊")
    return not problems, (msg if not problems else "; ".join(problems))


def check_coverage(all_tasks, participating, placements, excluded):
    """检查 4: 覆盖全部参加排程的任务, 且不含被排除的任务。"""
    want = {t["id"] for t in participating}
    got = set(placements)
    missing, extra = sorted(want - got), sorted(got - want)
    leaked = sorted(got & set(excluded))
    ok = not missing and not extra and not leaked
    msg = (f"覆盖全部 {len(want)} 个参加排程任务"
           + (f", 排除 {len(excluded)} 个悬空上游任务" if excluded else ""))
    if not ok:
        msg = f"缺失 {missing} 多余 {extra} 误入 {leaked}"
    return ok, msg


# ---------------------------------------------------------------- 主流程
def main():
    ap = argparse.ArgumentParser(description="当日任务排程")
    ap.add_argument("tasks_json")
    ap.add_argument("slots_json")
    ap.add_argument("out_csv")
    ap.add_argument("--checks", default="plan_checks.json",
                    help="五项检查结果输出路径(默认 plan_checks.json)")
    args = ap.parse_args()

    tasks_doc = load_json(args.tasks_json)
    slots_doc = load_json(args.slots_json)
    all_tasks = tasks_doc["tasks"]
    sites = slots_doc["sites"]
    hours = slots_doc["hours"]
    capacity = slots_doc["capacity"]
    quota = slots_doc["quota"]

    # 1. 悬空上游任务不参加排程
    participating, excluded = split_tasks(all_tasks)

    # 2. 配额 -> 每站每小时可用槽位
    quota_norm = normalize_quota(sites, quota)
    alloc, target_cont, day_alloc, deviation = allocate_slots(
        sites, hours, capacity, quota_norm
    )

    # 3. 拓扑序 + 贪心放置
    order, cyclic = topo_sort(participating)
    placements, labels = schedule_tasks(
        participating, order, hours, capacity, alloc
    )

    # 4. 写 day_plan.csv: 每任务一行, slot 为两位起始小时, note 标注顺延
    with open(args.out_csv, "w", encoding="utf-8", newline="") as f:
        w = csv.writer(f)
        w.writerow(["task", "slot", "site", "order", "note"])
        for tid in sorted(placements, key=lambda x: placements[x]["order"]):
            p = placements[tid]
            w.writerow([tid, p["label"], p["site"], p["order"],
                        "顺延" if p["deferred"] else ""])

    # 5. 五项检查
    checks = [
        ("拓扑序",       check_topology(participating, placements, hours)),
        ("槽位不越界",   check_slots(participating, placements, hours,
                                     capacity, alloc)),
        ("配额分配",     check_quota(sites, hours, capacity, quota_norm,
                                     alloc, deviation)),
        ("覆盖全部任务", check_coverage(all_tasks, participating,
                                        placements, excluded)),
        ("无环",         check_acyclic(all_tasks)),
    ]
    overall_ok = all(ok for _, (ok, _) in checks) and not cyclic

    cap_total = {s: sum(capacity[s][h] for h in hours) for s in sites}
    report = {
        "date": tasks_doc.get("date"),
        "overall": "pass" if overall_ok else "fail",
        "checks": [
            {"name": name, "pass": ok, "message": msg}
            for name, (ok, msg) in checks
        ],
        "summary": {
            "tasks_total": len(all_tasks),
            "tasks_scheduled": len(placements),
            "tasks_excluded": len(excluded),
            "excluded_ids": excluded,
            "tasks_deferred": sorted(
                tid for tid, p in placements.items() if p["deferred"]
            ),
            "cyclic_ids": cyclic,
            "window_hours": hours,
            "actual_last_hour": labels[-1],
        },
        "quota": {
            "raw_sum": round(sum(quota[s] for s in sites), 6),
            "normalized": {s: round(quota_norm[s], 6) for s in sites},
            "continuous_target": {s: round(target_cont[s], 4) for s in sites},
            "day_allocation": day_alloc,
            "site_capacity_total": cap_total,
            "l1_deviation": round(deviation, 4),
            "hourly_allocation": {s: {h: alloc[s][h] for h in hours}
                                  for s in sites},
        },
    }
    with open(args.checks, "w", encoding="utf-8") as f:
        json.dump(report, f, ensure_ascii=False, indent=2)
        f.write("\n")

    # ---- 控制台摘要
    print(f"日期: {tasks_doc.get('date')}  任务 {len(all_tasks)} "
          f"(参加 {len(placements)}, 排除 {len(excluded)})  "
          f"窗口 {hours[0]}..{hours[-1]}"
          + (f" 实际溢出至 {labels[-1]}" if len(labels) > len(hours) else ""))
    if excluded:
        print(f"排除(上游不存在): {', '.join(excluded)}")
    if cyclic:
        print(f"环上任务: {', '.join(cyclic)}")
    deferred = [tid for tid, p in placements.items() if p["deferred"]]
    print(f"顺延任务: {', '.join(deferred) if deferred else '无'}")
    print(f"全天 L1 偏差: {deviation:.4f}")
    for name, (ok, msg) in checks:
        print(f"  [{'PASS' if ok else 'FAIL'}] {name}: {msg}")
    print(f"计划判定: {'合格' if overall_ok else '不合格'}")
    print(f"已写出: {args.out_csv}, {args.checks}")
    sys.exit(0 if overall_ok else 1)


if __name__ == "__main__":
    main()
