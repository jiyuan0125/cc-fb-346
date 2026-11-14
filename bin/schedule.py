#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
当日任务排程器。

用法:
    python3 -I schedule.py tasks.json slots.json day_plan.csv

规则摘要:
  1. 依赖决定拓扑先后(Kahn + 最小堆), 同站点可运行任务按 earliest 再按 id 排序;
     依赖中引用了不存在任务的, 记为悬空依赖并告警忽略, 否则无法覆盖全部任务。
  2. 配额比例之和 > 1 时先归一化; 配额是计划供给、容量是上限。各站全天配额
     取"全天容量池*归一化份额"在该站容量内的最近整数(容量约束下 L1 偏差的
     全局最优), 再按各小时容量权重以最大余数法分摊到小时, 每小时不越容量。
     配额槽位可以少于物理容量, 缺口即任务顺延的来源。
  3. 任务不可拆分: dur_min > 0 占用 ceil(dur_min/60) 个连续小时, 每个小时各占
     一个槽; dur_min == 0 不占槽(slot 记为 HH#-)。
  4. 配额槽位不足时任务顺延到后续第一个可容纳的小时, 计划中用 :defer 标注。
  5. 五项检查: 拓扑序 / 槽位不越界 / 配额分配 / 覆盖全部任务 / 无环, 任一失败
     即以退出码 1 判计划不合格。
  6. 全程确定性排序, 重复生成同日计划字节级一致。
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


# ---------------------------------------------------------------- 配额与槽位
def normalize_quota(sites, quota):
    """配额比例之和可能 > 1, 归一化为份额。"""
    total = sum(quota[s] for s in sites)
    return {s: quota[s] / total for s in sites}


def largest_remainder(weights, total):
    """无容量约束的最大余数整数分摊, weights 之和为 1, 结果之和为 total。"""
    raw = {k: total * weights[k] for k in weights}
    out = {k: int(raw[k]) for k in weights}          # 正数截断即向下取整
    left = total - sum(out.values())
    order = sorted(weights, key=lambda k: (-(raw[k] - out[k]), k))
    for k in order[:left]:
        out[k] += 1
    return out


def nearest_integer_clamped(x, hi):
    """离 x 最近的整数, 截断到 [0, hi]; 恰好半数时取较小值(确定性)。"""
    lo = math.floor(x)
    candidates = [lo] + ([] if lo == math.ceil(x) else [lo + 1])
    best = min(candidates, key=lambda c: (abs(c - x), c))
    return max(0, min(hi, best))


def allocate_slots(sites, hours, capacity, quota_norm):
    """
    配额是计划供给、容量是上限。返回:
      alloc[s][h]  站点 s 在小时 h 的配额可用槽位(可小于容量, 缺口即顺延来源)
      其余为报告/检查用的目标与实际全天合计。

    第一步: 连续目标 target[s] = 全天容量池 * 归一化配额;
    第二步: 各站独立取离目标最近的整数并截断到该站全天容量, 这是仅受容量
            约束下 L1 偏差的全局最优(站点间无总量耦合, 可独立取最优);
    第三步: 把各站全天整数配额按各小时容量权重做最大余数分摊, 逐小时不越容量。
    """
    pools = {h: sum(capacity[s][h] for s in sites) for h in hours}
    day_pool = sum(pools.values())
    cap_total = {s: sum(capacity[s][h] for h in hours) for s in sites}
    target_cont = {s: day_pool * quota_norm[s] for s in sites}
    target_int = largest_remainder(quota_norm, day_pool)

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
    return alloc, target_cont, target_int, day_alloc, deviation


# ---------------------------------------------------------------- 拓扑序
def topo_sort(tasks):
    """Kahn + 最小堆 (earliest, id); 返回 (顺序列表, 悬空依赖列表, 环上任务列表)。"""
    by_id = {t["id"]: t for t in tasks}
    indeg = {t["id"]: 0 for t in tasks}
    children = defaultdict(list)
    dangling = []
    for t in tasks:
        for d in t["deps"]:
            if d not in by_id:
                dangling.append((t["id"], d))
                continue
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
    return order, sorted(dangling), cyclic


# ---------------------------------------------------------------- 排程
def ceil_slots(dur_min):
    return 0 if dur_min <= 0 else math.ceil(dur_min / 60)


def schedule_tasks(tasks, order, sites, hours, capacity, alloc):
    """
    生成行: dict(task, slot, site, order, hour_idx, slot_idx, deferred)。
    溢出定义窗口(08..17)的小时按该站末小时容量兜底, 并一律标注 :defer。
    """
    by_id = {t["id"]: t for t in tasks}
    hour_idx = {h: i for i, h in enumerate(hours)}
    labels = list(hours)
    first_hour = int(hours[0])

    def label(hi):
        while len(labels) <= hi:
            labels.append(f"{(first_hour + len(labels)) % 24:02d}")
        return labels[hi]

    def available(site, hi):
        if hi < len(hours):
            return alloc[site][hours[hi]]
        return capacity[site][hours[-1]]          # 窗口外兜底容量

    used = defaultdict(set)                       # (site, hi) -> {slot_idx}
    end_at = {}                                   # task id -> 最后占用小时
    rows = []
    deferrals = []

    for topo_pos, tid in enumerate(order, start=1):
        t = by_id[tid]
        site = t["site"]
        earliest = hour_idx[t["earliest"]]
        dep_end = [end_at[d] for d in t["deps"] if d in end_at]
        eligible = max([earliest] + [x + 1 for x in dep_end]) if dep_end else earliest
        n = ceil_slots(t["dur_min"])

        if n == 0:
            h0 = eligible
            rows.append({
                "task": tid, "site": site, "order": topo_pos,
                "hour_idx": h0, "slot_idx": -1, "deferred": False,
                "slot_text": f"{label(h0)}#-",
            })
            end_at[tid] = h0
            continue

        h0 = eligible
        while True:                               # 找首个连续 n 小时都有空槽的起点
            ok = all(
                len(used[(site, h0 + k)]) < available(site, h0 + k)
                for k in range(n)
            )
            if ok:
                break
            h0 += 1

        deferred = h0 > eligible
        for k in range(n):
            hi = h0 + k
            cap = available(site, hi)
            free = next(i for i in range(1, cap + 1) if i not in used[(site, hi)])
            used[(site, hi)].add(free)
            text = f"{label(hi)}#{free}"
            if deferred or hi >= len(hours):
                text += ":defer"
            rows.append({
                "task": tid, "site": site, "order": topo_pos,
                "hour_idx": hi, "slot_idx": free, "deferred": deferred,
                "slot_text": text,
            })
        end_at[tid] = h0 + n - 1
        if deferred:
            deferrals.append(tid)

    rows.sort(key=lambda r: (r["order"], r["hour_idx"],
                             r["slot_idx"] if r["slot_idx"] >= 0 else 1 << 30))
    return rows, labels, deferrals


# ---------------------------------------------------------------- 五项检查
def check_acyclic(tasks):
    """检查 5: 无环(DFS 三色法, 仅统计存在的任务节点)。"""
    by_id = {t["id"]: t for t in tasks}
    color = {tid: 0 for tid in by_id}             # 0 白 1 灰 2 黑
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
    return ok, "依赖图无环" if ok else "依赖图存在环"


def check_topology(tasks, rows):
    """检查 1: 拓扑序(含 earliest 约束、连续小时、:defer 标注与实际顺延一致)。"""
    by_id = {t["id"]: t for t in tasks}
    problems = []
    order_of = {}
    spans = defaultdict(list)
    for r in rows:
        if r["order"] in order_of and order_of[r["order"]] != r["task"]:
            problems.append(f"order {r['order']} 被多个任务占用")
        order_of[r["task"]] = r["order"]
        spans[r["task"]].append(r)

    if sorted(order_of.values()) != list(range(1, len(by_id) + 1)):
        problems.append("order 不是 1..N 的完整排列")

    for tid, rs in spans.items():
        his = [r["hour_idx"] for r in rs]
        if his != sorted(his):
            problems.append(f"{tid} 占用小时非升序")
        if len(his) > 1 and his != list(range(his[0], his[0] + len(his))):
            problems.append(f"{tid} 占用小时不连续")

    # 依赖先后、earliest 约束、defer 标注复核
    end_at = {tid: max(r["hour_idx"] for r in rs) for tid, rs in spans.items()}
    base = int(min(t["earliest"] for t in tasks))
    for t in tasks:
        tid = t["id"]
        earliest_idx = int(t["earliest"]) - base
        start = min(r["hour_idx"] for r in spans[tid])
        if start < earliest_idx:
            problems.append(f"{tid} 开始小时 {start} 早于 earliest {earliest_idx}")
        known_dep_ends = [end_at[d] for d in t["deps"] if d in end_at]
        eligible = max([earliest_idx] + [x + 1 for x in known_dep_ends]) \
            if known_dep_ends else earliest_idx
        for d in t["deps"]:
            if d in end_at and order_of[d] >= order_of[tid]:
                problems.append(f"{tid} 未排在依赖 {d} 之后")
            if d in end_at and end_at[d] >= start:
                problems.append(f"{tid} 与依赖 {d} 的结束小时不满足先后")
        expect_defer = start > eligible
        actual_defer = any(r["deferred"] for r in spans[tid])
        if expect_defer != actual_defer:
            problems.append(f"{tid} 的 :defer 标注与实际顺延不一致")

    return not problems, "拓扑序/earliest/连续性/标注均正确" if not problems \
        else "; ".join(problems)


def check_slots(tasks, rows, sites, hours, capacity, alloc):
    """检查 2: 槽位不越界(同一站点同一小时槽位不重复、不超过配额可用数)。"""
    problems = []
    seen = defaultdict(set)
    for r in rows:
        if r["slot_idx"] < 0:
            continue                                # 零时长不占槽
        site, hi = r["site"], r["hour_idx"]
        limit = alloc[site][hours[hi]] if hi < len(hours) \
            else capacity[site][hours[-1]]
        if not (1 <= r["slot_idx"] <= limit):
            problems.append(f"{r['task']} 槽位 {r['slot_text']} 越界(上限 {limit})")
        if r["slot_idx"] in seen[(site, hi)]:
            problems.append(f"{site} 小时 {hi} 槽位 {r['slot_idx']} 重复占用")
        seen[(site, hi)].add(r["slot_idx"])

    # 行数与时长一致
    by_id = {t["id"]: t for t in tasks}
    count = defaultdict(int)
    for r in rows:
        if r["slot_idx"] >= 0:
            count[r["task"]] += 1
    for tid, t in by_id.items():
        need = ceil_slots(t["dur_min"])
        if need == 0:
            zero_rows = [r for r in rows if r["task"] == tid]
            if len(zero_rows) != 1 or zero_rows[0]["slot_idx"] != -1:
                problems.append(f"{tid} 零时长任务占位方式错误")
        elif count[tid] != need:
            problems.append(f"{tid} 占 {count[tid]} 槽, 应为 {need}")

    return not problems, "槽位均在配额可用范围内且无重复" if not problems \
        else "; ".join(problems)


def check_quota(sites, hours, capacity, quota_norm, alloc, deviation):
    """
    检查 3: 配额分配。
      a. 逐小时 0 <= 分配 <= 物理容量;
      b. 全天合计等于"连续配额目标在容量内取最近整数", 即容量约束下 L1 全局最优;
      c. 各小时分摊与按容量权重的最大余数法一致(逐小时不越容量, 偏差不再增大)。
    """
    problems = []
    cap_total = {s: sum(capacity[s][h] for h in hours) for s in sites}
    day_pool = sum(cap_total[s] for s in sites)
    target = {s: day_pool * quota_norm[s] for s in sites}
    day_total = {s: sum(alloc[s][h] for h in hours) for s in sites}

    for h in hours:
        for s in sites:
            if not (0 <= alloc[s][h] <= capacity[s][h]):
                problems.append(f"{s} 小时 {h} 分配 {alloc[s][h]} 越界")

    # b: 全局最优复核 —— 站点间无总量耦合, 逐站枚举可行整数取 L1 最小
    for s in sites:
        expect = min(
            range(0, cap_total[s] + 1),
            key=lambda x: (abs(x - target[s]), x),
        )
        if day_total[s] != expect:
            problems.append(
                f"{s} 全天分配 {day_total[s]} 不是最优, 应为 {expect}"
                f"(连续目标 {target[s]:.3f}, 容量 {cap_total[s]})"
            )

    # c: 逐小时最大余数复核
    for s in sites:
        weights = {h: capacity[s][h] / cap_total[s] for h in hours}
        expect_h = largest_remainder(weights, day_total[s])
        for h in hours:
            if expect_h[h] != alloc[s][h]:
                problems.append(
                    f"{s} 小时 {h} 分摊 {alloc[s][h]} 与最大余数法 {expect_h[h]} 不一致"
                )

    # 独立枚举确认不存在任何可行全天方案有更小 L1 偏差
    best_possible = sum(
        min(abs(x - target[s]) for x in range(0, cap_total[s] + 1))
        for s in sites
    )
    if deviation > best_possible + 1e-9:
        problems.append(f"L1 偏差 {deviation:.4f} 未达理论最小 {best_possible:.4f}")

    msg = (f"全天 L1 偏差 = {deviation:.4f}(理论最小 {best_possible:.4f}, "
           f"容量约束下配额全局最优)")
    return not problems, msg if not problems else "; ".join(problems)


def check_coverage(tasks, rows):
    """检查 4: 覆盖全部任务。"""
    want = {t["id"] for t in tasks}
    got = {r["task"] for r in rows}
    missing, extra = sorted(want - got), sorted(got - want)
    ok = not missing and not extra
    msg = f"覆盖全部 {len(want)} 个任务" if ok \
        else f"缺失 {missing} 多余 {extra}"
    return ok, msg


# ---------------------------------------------------------------- 主流程
def main():
    ap = argparse.ArgumentParser(description="当日任务排程")
    ap.add_argument("tasks_json")
    ap.add_argument("slots_json")
    ap.add_argument("out_csv")
    args = ap.parse_args()

    tasks_doc = load_json(args.tasks_json)
    slots_doc = load_json(args.slots_json)
    tasks = tasks_doc["tasks"]
    sites = slots_doc["sites"]
    hours = slots_doc["hours"]
    capacity = slots_doc["capacity"]
    quota = slots_doc["quota"]

    quota_norm = normalize_quota(sites, quota)
    alloc, target_cont, target_int, day_alloc, deviation = allocate_slots(
        sites, hours, capacity, quota_norm
    )

    order, dangling, cyclic = topo_sort(tasks)

    rows, labels, deferrals = schedule_tasks(
        tasks, order, sites, hours, capacity, alloc
    )

    with open(args.out_csv, "w", encoding="utf-8", newline="") as f:
        w = csv.writer(f)
        w.writerow(["task", "slot", "site", "order"])
        for r in rows:
            w.writerow([r["task"], r["slot_text"], r["site"], r["order"]])

    print(f"日期: {tasks_doc.get('date')}  任务数: {len(tasks)}  "
          f"站点数: {len(sites)}  规划小时: {hours[0]}..{hours[-1]}"
          + (f"  实际溢出至 {labels[-1]}" if len(labels) > len(hours) else ""))
    raw_sum = sum(quota[s] for s in sites)
    note = ">1, 已归一化" if raw_sum > 1 else (
        "<1, 已归一化" if raw_sum < 1 else "=1")
    print(f"配额原始合计 = {raw_sum:.2f} ({note})")
    print("\n各站全天配额槽位: 目标(连续) / 目标(整数) / 实际分配 / 物理容量")
    cap_total = {s: sum(capacity[s][h] for h in hours) for s in sites}
    for s in sites:
        print(f"  {s}: {target_cont[s]:7.3f} / {target_int[s]:3d} / "
              f"{day_alloc[s]:3d} / 容量 {cap_total[s]:3d}")
    print(f"全天 L1 偏差 = {deviation:.4f}")

    if dangling:
        print("\n警告: 悬空依赖(被依赖任务不存在, 已忽略):")
        for tid, d in dangling:
            print(f"  {tid} -> {d}")

    # 有环: 环上任务无法进入拓扑序, 计划必然不完整, 直接判不合格
    if cyclic:
        print(f"\n五项检查:")
        print(f"  [FAIL] 无环: 依赖图存在环, 环上任务 {cyclic}")
        print(f"\n计划判定: 不合格")
        print(f"已写出(不完整): {args.out_csv} ({len(rows)} 行)")
        sys.exit(1)

    if deferrals:
        print(f"\n顺延任务({len(deferrals)}): {', '.join(deferrals)}")
    else:
        print("\n无任务顺延")

    # ---- 五项检查
    checks = [
        ("拓扑序",       check_topology(tasks, rows)),
        ("槽位不越界",   check_slots(tasks, rows, sites, hours, capacity, alloc)),
        ("配额分配",     check_quota(sites, hours, capacity, quota_norm, alloc, deviation)),
        ("覆盖全部任务", check_coverage(tasks, rows)),
        ("无环",         check_acyclic(tasks)),
    ]

    print("\n五项检查:")
    all_ok = True
    for name, (ok, msg) in checks:
        all_ok &= ok
        print(f"  [{'PASS' if ok else 'FAIL'}] {name}: {msg}")
    print(f"\n计划判定: {'合格' if all_ok else '不合格'}")
    print(f"已写出: {args.out_csv} ({len(rows)} 行)")
    sys.exit(0 if all_ok else 1)


if __name__ == "__main__":
    main()
