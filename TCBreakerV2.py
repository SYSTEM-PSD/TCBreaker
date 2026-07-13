"""
基于V1的多输出共享综合器（内存优化 + 进度显示版）
- 继承V1单输出逻辑，性能与正确性不变
- 多输出搜索实时显示候选数量与搜索阶段
- 防止组合爆炸：候选上限150，延迟计算子表达式集
"""

import time
from collections import defaultdict
from functools import lru_cache


class LogicSynthesizer:
    def __init__(self, num_inputs, target_truth_table, max_delay,
                 output_mode="all", per_delay=False):
        self.n = num_inputs
        self.N = 1 << num_inputs
        self.all_mask = (1 << self.N) - 1

        if isinstance(target_truth_table, list):
            self.multi_output = True
            self.targets = [t & self.all_mask for t in target_truth_table]
            self.num_targets = len(self.targets)
            self.target_set = set(self.targets)
        else:
            self.multi_output = False
            self.targets = [target_truth_table & self.all_mask]
            self.num_targets = 1
            self.target_set = set(self.targets)
            self.target = self.targets[0]

        self.D = max_delay
        self.output_all = (output_mode == "all")
        self.per_delay = per_delay

        self.layers = [[] for _ in range(max_delay + 1)]

        self.MAX_LOGIC_PER_KEY = 5 if self.multi_output else 3
        self.MAX_TRI_PER_KEY = 3 if self.multi_output else 2

        self.best_logic = defaultdict(list)
        self.best_tri = defaultdict(list)

        self.target_candidates = [[] for _ in range(self.num_targets)]
        for i in range(self.num_targets):
            self.target_candidates[i] = [[] for _ in range(max_delay + 1)]

        self.solutions = []
        self.delay_solutions = {}

        self.best_gates_found = 999999
        self._init_base()

    # ---------- 候选添加（V1原逻辑） ----------
    def _add_candidate(self, mask, gates, expr, is_tri, en, data, delay, switches_list=None):
        if switches_list is None:
            switches_list = [(en, data)] if is_tri else []
        mask &= self.all_mask
        if (mask == 0 or mask == self.all_mask) and gates > 0:
            return

        if not self.multi_output:
            if gates > self.best_gates_found and mask != self.target:
                return
            if mask == self.target:
                self.target_candidates[0][delay].append((gates, expr, switches_list))
                if gates < self.best_gates_found:
                    self.best_gates_found = gates
                return
        else:
            for ti, tmask in enumerate(self.targets):
                if mask == tmask:
                    self.target_candidates[ti][delay].append((gates, expr, switches_list))

        if switches_list:
            key = (mask, delay)
            lst = self.best_tri[key]
            for idx, (g, e, s) in enumerate(lst):
                if s == switches_list:
                    if gates > g or (gates == g and expr >= e):
                        return
                    lst[idx] = (gates, expr, switches_list)
                    lst.sort(key=lambda x: (x[0], x[1]))
                    if len(lst) > self.MAX_TRI_PER_KEY:
                        lst.pop()
                    self.layers[delay].append((mask, gates, expr, is_tri, en, data, switches_list))
                    return
            lst.append((gates, expr, switches_list))
            lst.sort(key=lambda x: (x[0], x[1]))
            if len(lst) > self.MAX_TRI_PER_KEY:
                lst.pop()
            self.layers[delay].append((mask, gates, expr, is_tri, en, data, switches_list))
            return

        key = (mask, delay)
        lst = self.best_logic[key]
        if not lst:
            lst.append((gates, expr))
            self.layers[delay].append((mask, gates, expr, is_tri, en, data, switches_list))
            return
        min_g = lst[0][0]
        if gates > min_g:
            return
        elif gates < min_g:
            lst.clear()
            lst.append((gates, expr))
            self.layers[delay].append((mask, gates, expr, is_tri, en, data, switches_list))
            return
        else:
            for i, (g, e) in enumerate(lst):
                if e == expr:
                    return
            lst.append((gates, expr))
            lst.sort(key=lambda x: x[1])
            if len(lst) > self.MAX_LOGIC_PER_KEY:
                lst.pop()
            self.layers[delay].append((mask, gates, expr, is_tri, en, data, switches_list))

    def _init_base(self):
        self._add_candidate(0, 0, "0", False, 0, 0, 0)
        self._add_candidate(self.all_mask, 0, "1", False, 0, 0, 0)
        for i in range(self.n):
            mask = 0
            for row in range(self.N):
                if (row >> i) & 1:
                    mask |= (1 << row)
            self._add_candidate(mask, 0, f"x{i}", False, 0, 0, 0)

    def _is_short_free(self, list1, list2):
        for en1, data1 in list1:
            for en2, data2 in list2:
                if (en1 & en2 & (data1 ^ data2)) != 0:
                    return False
        return True

    # ---------- 核心枚举（V1结构） ----------
    def _synthesize_exact(self):
        start_time = time.time()
        last_time = start_time
        all_mask = self.all_mask
        layers = self.layers
        D = self.D
        best_logic = self.best_logic
        best_tri = self.best_tri
        multi = self.multi_output
        forbidden_prefixes = ("AND(", "OR(", "NAND(", "NOR(", "NOT(")

        for delay in range(1, D + 1):
            # 压缩层
            for d in range(D + 1):
                layer = layers[d]
                if not layer:
                    continue
                logic_set = {m: {(g, e) for g, e in lst} for (m, dl), lst in best_logic.items() if dl == d}
                tri_set = {m: {(g, e, tuple(s)) for g, e, s in lst} for (m, dl), lst in best_tri.items() if dl == d}

                compressed = []
                for cand in layer:
                    mask, gates, expr, is_tri, en, data, swl = cand
                    if swl:
                        if mask in tri_set and (gates, expr, tuple(swl)) in tri_set[mask]:
                            compressed.append(cand)
                    else:
                        if mask in logic_set and (gates, expr) in logic_set[mask]:
                            compressed.append(cand)
                layers[d] = compressed

            for d in range(D + 1):
                layers[d].sort(key=lambda cand: cand[1])

            # NOT
            for m1, g1, e1, _, _, _, _ in layers[delay - 1]:
                if not any(e1.startswith(p) for p in forbidden_prefixes):
                    self._add_candidate(all_mask ^ m1, g1 + 1, f"NOT({e1})", False, 0, 0, delay)

            # 二目门与 SWITCH
            pairs = [(d1, d2) for d1 in range(delay) for d2 in range(d1, delay) if max(d1, d2) == delay - 1]
            for d1, d2 in pairs:
                list1 = layers[d1]
                list2 = layers[d2]
                for i1, (m1, g1, e1, _, _, _, swl1) in enumerate(list1):
                    if m1 == 0 or m1 == all_mask:
                        continue
                    for i2, (m2, g2, e2, _, _, _, swl2) in enumerate(list2):
                        if m2 == 0 or m2 == all_mask:
                            continue
                        if d1 == d2 and i1 >= i2:
                            continue
                        base_gates = g1 + g2 + 1
                        if not multi and base_gates > self.best_gates_found:
                            break

                        m_and = m1 & m2
                        m_or = m1 | m2

                        if m_and not in (m1, m2):
                            self._add_candidate(m_and, base_gates, f"AND({e1},{e2})", False, 0, 0, delay)
                        if m_or not in (m1, m2):
                            self._add_candidate(m_or, base_gates, f"OR({e1},{e2})", False, 0, 0, delay)
                        self._add_candidate(all_mask ^ m_and, base_gates, f"NAND({e1},{e2})", False, 0, 0, delay)
                        self._add_candidate(all_mask ^ m_or, base_gates, f"NOR({e1},{e2})", False, 0, 0, delay)

                        sw_delay = max(d1, d2) + 1
                        if sw_delay <= D:
                            sw_base_gates = g1 + g2 + 2
                            if not swl1 and m1 != all_mask and m2 not in (0, all_mask):
                                sw = m1 & m2
                                if sw not in (m1, m2):
                                    self._add_candidate(sw, sw_base_gates, f"SWITCH({e1},{e2})", True, m1, m2, sw_delay, [(m1, m2)])
                            if not swl2 and m2 != all_mask and m1 not in (0, all_mask):
                                if d1 != d2 or m1 != m2:
                                    sw = m2 & m1
                                    if sw not in (m1, m2):
                                        self._add_candidate(sw, sw_base_gates, f"SWITCH({e2},{e1})", True, m2, m1, sw_delay, [(m2, m1)])

            # BUS_OR
            tri_map = defaultdict(list)
            for dl in range(D + 1):
                for cand in layers[dl]:
                    mask, gates, expr, is_tri, en, data, swl = cand
                    if swl:
                        tri_map[(mask, dl)].append((gates, expr, swl))
            tri_cands = []
            for (m, dl), items in tri_map.items():
                items.sort(key=lambda x: (x[0], x[1]))
                for g, e, s in items[:self.MAX_TRI_PER_KEY]:
                    tri_cands.append((m, g, e, s, dl))

            for i in range(len(tri_cands)):
                m1, g1, e1, swl1, dl1 = tri_cands[i]
                for j in range(i+1, len(tri_cands)):
                    m2, g2, e2, swl2, dl2 = tri_cands[j]
                    new_gates = g1 + g2
                    if not multi and new_gates > self.best_gates_found:
                        continue
                    if not self._is_short_free(swl1, swl2):
                        continue
                    new_mask = (m1 | m2) & all_mask
                    new_delay = max(dl1, dl2)
                    self._add_candidate(new_mask, new_gates, f"BUS_OR({e1},{e2})", False, 0, 0, new_delay, swl1 + swl2)

            layer_end = time.time()
            total_candidates = sum(len(l) for l in layers)
            print(f"枚举延迟 {delay}/{D} | 候选 {total_candidates} | 本层 {layer_end-last_time:.1f}s | 累计 {layer_end-start_time:.1f}s")
            last_time = layer_end

        print(f"枚举完成，总耗时: {time.time()-start_time:.2f}s\n")

    # ---------- 表达式工具（静态+缓存） ----------
    @staticmethod
    @lru_cache(maxsize=65536)
    def _split_top_level(inner):
        depth = 0
        for i, c in enumerate(inner):
            if c == '(': depth += 1
            elif c == ')': depth -= 1
            elif c == ',' and depth == 0:
                return inner[:i].strip(), inner[i+1:].strip()
        return inner.strip(), ""

    @staticmethod
    @lru_cache(maxsize=65536)
    def _canonicalize_expr(expr):
        if expr in ('0', '1') or (expr[0] == 'x' and expr[1:].isdigit()):
            return expr
        if expr.startswith('NOT('):
            return f"NOT({LogicSynthesizer._canonicalize_expr(expr[4:-1])})"
        if expr.startswith('SWITCH('):
            inner = expr[7:-1]
            en, data = LogicSynthesizer._split_top_level(inner)
            return f"SWITCH({LogicSynthesizer._canonicalize_expr(en)},{LogicSynthesizer._canonicalize_expr(data)})"
        if expr.startswith('BUS_OR('):
            inner = expr[7:-1]
            args = []
            depth = 0
            start = 0
            for i, c in enumerate(inner):
                if c == '(': depth += 1
                elif c == ')': depth -= 1
                elif c == ',' and depth == 0:
                    args.append(inner[start:i].strip())
                    start = i + 1
            args.append(inner[start:].strip())
            flat = []
            for a in args:
                ca = LogicSynthesizer._canonicalize_expr(a)
                if ca.startswith('BUS_OR('):
                    inner_bus = ca[7:-1]
                    sub_args = []
                    d = 0
                    s = 0
                    for j, ch in enumerate(inner_bus):
                        if ch == '(': d += 1
                        elif ch == ')': d -= 1
                        elif ch == ',' and d == 0:
                            sub_args.append(inner_bus[s:j].strip())
                            s = j + 1
                    sub_args.append(inner_bus[s:].strip())
                    flat.extend(sub_args)
                else:
                    flat.append(ca)
            flat.sort()
            return "BUS_OR(" + ",".join(flat) + ")"
        else:
            op_end = expr.index('(')
            op = expr[:op_end]
            inner = expr[op_end+1:-1]
            left, right = LogicSynthesizer._split_top_level(inner)
            cl = LogicSynthesizer._canonicalize_expr(left)
            cr = LogicSynthesizer._canonicalize_expr(right)
            if op in ("AND", "OR", "NAND", "NOR") and cl > cr:
                cl, cr = cr, cl
            return f"{op}({cl},{cr})"

    # ---------- DAG 门数 ----------
    @staticmethod
    def _collect_sub_exprs(expr, sub_set):
        if expr in sub_set:
            return
        sub_set.add(expr)
        if expr in ('0', '1') or (expr[0] == 'x' and expr[1:].isdigit()):
            return
        if expr.startswith('NOT('):
            LogicSynthesizer._collect_sub_exprs(expr[4:-1], sub_set)
        elif expr.startswith('BUS_OR('):
            inner = expr[7:-1]
            args = []
            depth = 0
            start = 0
            for i, c in enumerate(inner):
                if c == '(': depth += 1
                elif c == ')': depth -= 1
                elif c == ',' and depth == 0:
                    args.append(inner[start:i].strip())
                    start = i + 1
            args.append(inner[start:].strip())
            for a in args:
                LogicSynthesizer._collect_sub_exprs(a, sub_set)
        else:
            paren = expr.index('(')
            inner = expr[paren+1:-1]
            left, right = LogicSynthesizer._split_top_level(inner)
            LogicSynthesizer._collect_sub_exprs(left, sub_set)
            LogicSynthesizer._collect_sub_exprs(right, sub_set)

    @staticmethod
    def _dag_gate_count(expr):
        sub_set = set()
        LogicSynthesizer._collect_sub_exprs(expr, sub_set)
        gates = 0
        for s in sub_set:
            if s in ('0', '1') or (s[0] == 'x' and s[1:].isdigit()):
                continue
            if s.startswith('SWITCH('):
                gates += 2
            elif s.startswith('BUS_OR('):
                pass
            else:
                gates += 1
        return gates

    @staticmethod
    def _multi_dag_gate_count(exprs):
        all_sub = set()
        for e in exprs:
            LogicSynthesizer._collect_sub_exprs(e, all_sub)
        gates = 0
        for s in all_sub:
            if s in ('0', '1') or (s[0] == 'x' and s[1:].isdigit()):
                continue
            if s.startswith('SWITCH('):
                gates += 2
            elif s.startswith('BUS_OR('):
                pass
            else:
                gates += 1
        return gates

    @staticmethod
    @lru_cache(maxsize=65536)
    def _sub_frozen(expr):
        sub = set()
        LogicSynthesizer._collect_sub_exprs(expr, sub)
        return frozenset(s for s in sub if s not in ('0','1') and not (s[0]=='x' and s[1:].isdigit()))

    # ---------- 多输出共享搜索（带详细进度） ----------
    def _combine_multi_output(self):
        print("开始多输出共享搜索...")
        # 收集每个输出的候选（规范化+真实门数）
        raw_opts = []
        for ti in range(self.num_targets):
            opts = []
            for d in range(self.D + 1):
                for gates_tree, expr, swl in self.target_candidates[ti][d]:
                    canon = self._canonicalize_expr(expr)
                    real_g = self._dag_gate_count(canon)
                    opts.append((d, real_g, canon))
            best = {}
            for d, g, e in opts:
                if e not in best or g < best[e][1] or (g == best[e][1] and d < best[e][0]):
                    best[e] = (d, g, e)
            uniq = list(best.values())
            print(f"  输出 {ti}: 原始候选 {len(opts)} -> 去重后 {len(uniq)}")
            raw_opts.append(uniq)

        solutions_by_delay = {}
        for global_delay in range(self.D + 1):
            print(f"\n--- 全局延迟 {global_delay} ---")
            # 筛选符合延迟的候选
            delay_opts = []
            delay_min_gates = []
            for ti in range(self.num_targets):
                cands = []
                min_g = 999999
                for d, g, e in raw_opts[ti]:
                    if d <= global_delay:
                        cands.append((d, g, e))
                        if g < min_g:
                            min_g = g
                if not cands:
                    print(f"  输出 {ti} 无符合延迟候选，跳过")
                    break
                delay_opts.append(cands)
                delay_min_gates.append(min_g)

            if len(delay_opts) != self.num_targets:
                continue

            upper_bound = sum(delay_min_gates)
            print(f"  独立最小门数和 (初始上界): {upper_bound}")

            # 过滤与截断
            MAX_CANDS = 150
            filtered_opts = []
            for ti, cands in enumerate(delay_opts):
                bound = upper_bound - delay_min_gates[ti]
                cands.sort(key=lambda x: x[1])
                filtered = []
                seen = set()
                before = len(cands)
                for d, g, e in cands:
                    if g > bound:
                        break
                    if e not in seen:
                        seen.add(e)
                        filtered.append((d, g, e))
                if len(filtered) > MAX_CANDS:
                    filtered = filtered[:MAX_CANDS]
                filtered_opts.append(filtered)
                print(f"  输出 {ti}: 延迟内候选 {before} -> 过滤后 {len(filtered)} (门数≤{bound})")

            # 更新独立最小值
            for ti in range(self.num_targets):
                cands = filtered_opts[ti]
                delay_min_gates[ti] = min(g for _, g, _ in cands) if cands else 999999

            remain_min = [0] * (self.num_targets + 1)
            for i in range(self.num_targets - 1, -1, -1):
                remain_min[i] = remain_min[i + 1] + delay_min_gates[i]

            best_total = upper_bound
            best_combos = []
            nodes_visited = 0

            def dfs(ti, current_union, lower_bound):
                nonlocal best_total, best_combos, nodes_visited
                nodes_visited += 1
                if nodes_visited % 100000 == 0:
                    print(f"    已探索节点: {nodes_visited}, 当前最优: {best_total}")
                if lower_bound + remain_min[ti] >= best_total:
                    return
                if ti == self.num_targets:
                    real_gates = self._multi_dag_gate_count(exprs)
                    if real_gates < best_total:
                        best_total = real_gates
                        best_combos = [(exprs[:], real_gates)]
                        print(f"    发现更优解: {real_gates}")
                    elif real_gates == best_total:
                        best_combos.append((exprs[:], real_gates))
                    return
                for _, g, e in filtered_opts[ti]:
                    cand_frozen = self._sub_frozen(e)
                    new_union = current_union | cand_frozen
                    new_lower = len(new_union)
                    if new_lower + remain_min[ti + 1] >= best_total:
                        continue
                    exprs.append(e)
                    dfs(ti + 1, new_union, new_lower)
                    exprs.pop()

            exprs = []
            print(f"  开始DFS (上界={best_total})...")
            dfs(0, frozenset(), 0)
            print(f"  搜索完成，访问节点 {nodes_visited}，找到解 {len(best_combos)} 个，最优门数 {best_total if best_combos else '无'}")

            if best_combos:
                solutions_by_delay[global_delay] = best_combos

        # 整理结果
        if self.per_delay:
            self.delay_solutions = {}
            for d in sorted(solutions_by_delay.keys()):
                combos = solutions_by_delay[d]
                unique_combos = []
                seen_frozen = set()
                for exprs, total_g in combos:
                    frozen = tuple(exprs)
                    if frozen not in seen_frozen:
                        seen_frozen.add(frozen)
                        unique_combos.append((total_g, exprs))
                if not self.output_all:
                    unique_combos = unique_combos[:1]
                self.delay_solutions[d] = unique_combos
        else:
            global_best_gates = None
            global_best_combos = []
            for d, combos in solutions_by_delay.items():
                for exprs, total_g in combos:
                    if global_best_gates is None or total_g < global_best_gates:
                        global_best_gates = total_g
                        global_best_combos = [(d, exprs, total_g)]
                    elif total_g == global_best_gates:
                        global_best_combos.append((d, exprs, total_g))
            self.solutions = []
            seen = set()
            for d, exprs, total_g in global_best_combos:
                frozen = tuple(exprs)
                if frozen not in seen:
                    seen.add(frozen)
                    self.solutions.append((d, total_g, exprs))
            if not self.output_all and self.solutions:
                self.solutions = self.solutions[:1]

    def _collect_solutions(self):
        if self.multi_output:
            self._combine_multi_output()
            return

        # 单输出
        if self.per_delay:
            self.delay_solutions = {}
            for delay in range(self.D + 1):
                candidates = self.target_candidates[0][delay]
                if not candidates:
                    continue
                best_gates = None
                best_sols = []
                for gates_tree, expr, swl in candidates:
                    canon = self._canonicalize_expr(expr)
                    real_g = self._dag_gate_count(canon)
                    if best_gates is None or real_g < best_gates:
                        best_gates = real_g
                        best_sols = [(canon, real_g)]
                    elif real_g == best_gates:
                        best_sols.append((canon, real_g))
                seen = set()
                sols = []
                for e, g in best_sols:
                    if e not in seen:
                        seen.add(e)
                        sols.append((delay, g, e))
                if sols:
                    self.delay_solutions[delay] = sols if self.output_all else [sols[0]]
        else:
            valid = [d for d in range(self.D + 1) if self.target_candidates[0][d]]
            if not valid:
                self.solutions = []
                return
            all_candidates = []
            for d in valid:
                for gates_tree, expr, _ in self.target_candidates[0][d]:
                    canon = self._canonicalize_expr(expr)
                    all_candidates.append((d, canon))
            real_all = [(d, self._dag_gate_count(e), e) for d, e in all_candidates]
            global_min_g = min(g for _, g, _ in real_all)
            seen = set()
            self.solutions = []
            for d, g, e in real_all:
                if g == global_min_g and e not in seen:
                    seen.add(e)
                    self.solutions.append((d, g, e))
            if not self.output_all and self.solutions:
                self.solutions = [self.solutions[0]]

    def synthesize(self):
        start_time = time.time()
        print(f"精确枚举 (n={self.n}, 最大延迟={self.D}, 输出数={self.num_targets})")
        self._synthesize_exact()
        self._collect_solutions()
        elapsed = time.time() - start_time
        print(f"总耗时: {elapsed:.2f} 秒")

        if self.multi_output:
            if self.per_delay:
                if not self.delay_solutions:
                    print("在给定延迟内无共享解")
                else:
                    print("\n各全局延迟下的最优共享电路:")
                    for d in sorted(self.delay_solutions.keys()):
                        sols = self.delay_solutions[d]
                        print(f"  全局延迟 {d}: 最小总门数 {sols[0][0]}, 共 {len(sols)} 种")
                        for total_g, exprs in (sols if self.output_all else [sols[0]]):
                            print(f"    总门数 {total_g}:")
                            for i, e in enumerate(exprs):
                                print(f"      输出{i}: {e}")
                return self.delay_solutions
            else:
                if not self.solutions:
                    print("在给定延迟内无全局最优共享解")
                    return []
                min_g = self.solutions[0][1]
                print(f"\n全局最小总门数 = {min_g}, 共 {len(self.solutions)} 种组合")
                for d, total_g, exprs in self.solutions:
                    print(f"  整体延迟 {d} | 总门数 {total_g}:")
                    for i, e in enumerate(exprs):
                        print(f"    输出{i}: {e}")
                return self.solutions
        else:
            if self.per_delay:
                if not self.delay_solutions:
                    print("在延迟 0~D 内均无解")
                else:
                    print("\n每层最优解 (该延迟下门数最小):")
                    for delay in sorted(self.delay_solutions.keys()):
                        for d, g, e in self.delay_solutions[delay]:
                            print(f"  延迟 {d} | 门数 {g} | {e}")
                return self.delay_solutions
            else:
                if not self.solutions:
                    print("在给定延迟内无解")
                    return []
                min_g = min(g for _, g, _ in self.solutions)
                print(f"\n全局最优: 最小门数 = {min_g}, 共 {len(self.solutions)} 种解")
                for d, g, e in self.solutions:
                    print(f"  延迟 {d} | 门数 {g} | {e}")
                return self.solutions


if __name__ == "__main__":
    print("=== 全加器 SUM (单输出) ===")
    LogicSynthesizer(3, 0x96, 6, output_mode="all", per_delay=True).synthesize()

    print("\n=== 全加器 Cout (单输出) ===")
    LogicSynthesizer(3, 0xE8, 6, output_mode="all", per_delay=True).synthesize()

    print("\n=== 全加器 SUM + Cout (共享) ===")
    LogicSynthesizer(3, [0x96, 0xE8], 6, output_mode="all", per_delay=True).synthesize()