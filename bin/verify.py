#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
独立验证器: 不导入 schedule.py, 仅凭 tasks.json / slots.json / day_plan.csv
重新核对五项检查。用法:
    python3 -I verify.py tasks.json slots.json day_plan.csv
退出码 0 = 五项全过, 1 = 存在不合格项。
"""
import csv
import json
import math
import sys
from collections import defaultdict


def largest_remainder(weights, total):
    raw = {k: total * weights[k] for k in weights}
    out = {k: int(raw[k]) for k in weights}
    order = sorted(weights, key=lambda k: (-(raw[k] - out[k]), k))
    for k in order[:total - sum(out.values())]:
        out[k] += 1
    return out


def main(tasks_path, slots_path, plan_path):
    all_tasks = json.load(open(tasks_path, encoding="utf-8"))["tasks"]
    doc = json.load(open(slots_path, encoding="utf-8"))
    sites, hours, cap, quota = doc["sites"], doc["hours"], doc["capacity"], doc["quota"]
    by_id = {t["id"]: t for t in all_tasks}
    base = int(hours[0])
    hpos = {h: i for i, h in enumerate(hours)}
    fails = []

    # ---- 复算: 悬空上游任务(直接或间接引用缺失任务) ----
    excluded = set()

    def bad(tid, stack):
        if tid in excluded or tid in stack:
            return tid in excluded
        stack.add(tid)
        for d in by_id[tid]["deps"]:
            if d not in by_id or bad(d, stack):
                excluded.add(tid)
                break
        stack.discard(tid)
        return tid in excluded

    for t in all_tasks:
        bad(t["id"], set())
    participating = [t for t in all_tasks if t["id"] not in excluded]

    # ---- 检查 5: 无环(完整清单, 缺失上游视为无边) ----
    color = {t["id"]: 0 for t in all_tasks}
    cyclic = False

    def dfs(u):
        nonlocal cyclic
        color[u] = 1
        for v in by_id[u]["deps"]:
            if v not in by_id:
                continue
            if color[v] == 1:
                cyclic = True
            elif color[v] == 0:
                dfs(v)
        color[u] = 2

    for tid in sorted(by_id):
        if color[tid] == 0:
            dfs(tid)
    if cyclic:
        fails.append("无环: 依赖图存在环")

    # ---- 复算配额分配 ----
    qsum = sum(quota[s] for s in sites)
    qn = {s: quota[s] / qsum for s in sites}
    cap_total = {s: sum(cap[s][h] for h in hours) for s in sites}
    day_pool = sum(cap_total.values())
    target = {s: day_pool * qn[s] for s in sites}
    alloc = {}
    for s in sites:
        x = target[s]
        lo = math.floor(x)
        cands = [lo] if lo == math.ceil(x) else [lo, lo + 1]
        day_n = max(0, min(min(cands, key=lambda c: (abs(c - x), c)),
                           cap_total[s]))
        w = {h: cap[s][h] / cap_total[s] for h in hours}
        alloc[s] = largest_remainder(w, day_n)

    # ---- 读计划 ----
    with open(plan_path, encoding="utf-8") as f:
        rows = list(csv.DictReader(f))
    if (rows and list(rows[0].keys()) !=
            ["task", "slot", "site", "order", "note"]):
        fails.append(f"表头错误: {list(rows[0].keys()) if rows else '空文件'}")

    # ---- 检查 4: 覆盖全部参加排程任务, 排除任务不得出现 ----
    planned = {r["task"] for r in rows}
    want = {t["id"] for t in participating}
    if planned != want:
        fails.append(f"覆盖: 缺{sorted(want - planned)} 多{sorted(planned - want)}")
    leaked = planned & excluded
    if leaked:
        fails.append(f"覆盖: 悬空上游任务误入计划 {sorted(leaked)}")

    # ---- 重建每任务放置 ----
    info = {}
    for r in rows:
        tid = r["task"]
        if tid not in by_id:
            fails.append(f"拓扑序: 未知任务 {tid}")
            continue
        if not (len(r["slot"]) == 2 and r["slot"].isdigit()):
            fails.append(f"拓扑序: {tid} slot 不是两位数字小时: {r['slot']}")
        if r["site"] != by_id[tid]["site"]:
            fails.append(f"拓扑序: {tid} 站点不匹配")
        note_defer = r["note"] == "顺延"
        if r["note"] not in ("", "顺延"):
            fails.append(f"拓扑序: {tid} note 非法: {r['note']}")
        info[tid] = {"start": int(r["slot"]) - base,
                     "order": int(r["order"]), "defer": note_defer}

    # order 从 1 起连续
    orders = sorted(v["order"] for v in info.values())
    if orders != list(range(1, len(info) + 1)):
        fails.append("拓扑序: order 不是从 1 起的连续编号")

    # ---- 检查 1: 拓扑序 / earliest / 依赖先后 / 顺延标注 ----
    def slots_needed(t):
        return max(1, math.ceil(t["dur_min"] / 60))

    end = {tid: v["start"] + slots_needed(by_id[tid]) - 1
           for tid, v in info.items()}
    for tid, v in info.items():
        t = by_id[tid]
        if v["start"] < hpos[t["earliest"]]:
            fails.append(f"拓扑序: {tid} 早于 earliest")
        dep_ready = [end[d] + 1 for d in t["deps"] if d in end]
        eligible = max([hpos[t["earliest"]]] + dep_ready) if dep_ready \
            else hpos[t["earliest"]]
        for d in t["deps"]:
            if d in end and not (end[d] < v["start"]
                                 and info[d]["order"] < v["order"]):
                fails.append(f"拓扑序: {tid} 未严格排在依赖 {d} 之后")
        expect_defer = v["start"] > eligible or end[tid] >= len(hours)
        if expect_defer != v["defer"]:
            fails.append(f"拓扑序: {tid} 顺延标注 {v['defer']} 与实际 {expect_defer} 不符")

    # ---- 检查 2: 槽位不越界 + 占槽数正确 ----
    # CSV 只记起始小时, 验证器按 order 顺序重放: 每任务在其占用的每个小时
    # 取最小空闲槽号, 再核对该槽号不越配额/物理容量。
    used = defaultdict(set)
    for tid in sorted(info, key=lambda x: info[x]["order"]):
        v = info[tid]
        t = by_id[tid]
        n = slots_needed(t)
        site = t["site"]
        for k in range(n):
            hi = v["start"] + k
            limit = alloc[site][hours[hi]] if hi < len(hours) \
                else cap[site][hours[-1]]
            hard = cap[site][hours[hi]] if hi < len(hours) \
                else cap[site][hours[-1]]
            free = next((i for i in range(1, hard + 1)
                         if i not in used[(site, hi)]), None)
            if free is None:
                fails.append(f"槽位: {site} 小时{hi} 物理容量已耗尽, {tid} 无法放置")
                continue
            used[(site, hi)].add(free)
            if free > hard:
                fails.append(f"槽位: {tid} 超出物理容量 {hard}")
            if hi < len(hours) and free > limit:
                fails.append(f"槽位: {tid} 超出配额槽位 {limit}")

    # ---- 检查 3: 配额分配(逐小时越界 + 全天 L1 最优 + 最大余数一致) ----
    for s in sites:
        for h in hours:
            if not (0 <= alloc[s][h] <= cap[s][h]):
                fails.append(f"配额: {s} {h} 越界")
        best = min(range(cap_total[s] + 1),
                   key=lambda x: (abs(x - target[s]), x))
        if sum(alloc[s].values()) != best:
            fails.append(f"配额: {s} 全天分配非 L1 最优")
        w = {h: cap[s][h] / cap_total[s] for h in hours}
        if largest_remainder(w, best) != alloc[s]:
            fails.append(f"配额: {s} 逐小时分摊与最大余数法不一致")

    print("独立验证结果:")
    if fails:
        for fmsg in fails:
            print("  FAIL", fmsg)
        print(f"判定: 不合格 ({len(fails)} 项)")
        return 1
    print("  五项检查全部通过")
    print(f"判定: 合格; 参加任务 {len(want)}, 排除 {sorted(excluded) or '无'}, "
          f"计划行 {len(rows)}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2], sys.argv[3]))
