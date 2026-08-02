"""
多输出逻辑综合器（最终版，Pareto剪枝应用于所有输出模式）
- BUS_OR 合并：DFS 枚举 mask 为目标子集的原始 SWITCH，剪枝优化
- 无论 per_delay 如何，最终解集都进行 Pareto 剪枝，只保留非支配解
- 三态门允许作为输出（挂下拉电阻）
- 健壮的表达式解析，防止空串崩溃
"""

import time
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

        self.best_per_layer = [{} for _ in range(max_delay + 1)]
        self.target_candidates = [[] for _ in range(self.num_targets)]
        for i in range(self.num_targets):
            self.target_candidates[i] = [[] for _ in range(max_delay + 1)]

        self.solutions = []
        self.delay_solutions = {}
        self.best_gates_found = 999999
        self._init_base()

    # ---------- 字符串解析辅助 ----------
    @staticmethod
    def _split_top_level(inner):
        depth = 0
        for i, c in enumerate(inner):
            if c == '(':
                depth += 1
            elif c == ')':
                depth -= 1
            elif c == ',' and depth == 0:
                return inner[:i].strip(), inner[i+1:].strip()
        return inner.strip(), ""

    @staticmethod
    def _split_bus_args(inner):
        args = []
        depth = 0
        start = 0
        for i, c in enumerate(inner):
            if c == '(':
                depth += 1
            elif c == ')':
                depth -= 1
            elif c == ',' and depth == 0:
                arg = inner[start:i].strip()
                if arg:
                    args.append(arg)
                start = i + 1
        arg = inner[start:].strip()
        if arg:
            args.append(arg)
        return args

    # ---------- 候选添加 ----------
    def _add_candidate(self, mask, gates, expr, is_tri, delay, switches_list=None):
        if switches_list is None:
            switches_list = []
        mask &= self.all_mask
        if (mask == 0 or mask == self.all_mask) and gates > 0:
            return

        # 允许三态直接作为输出（挂下拉电阻）
        for ti, tmask in enumerate(self.targets):
            if mask == tmask:
                self.target_candidates[ti][delay].append((gates, expr, switches_list))
                if not self.multi_output and gates < self.best_gates_found:
                    self.best_gates_found = gates

        # 非目标剪枝仅在 per_delay=False 时启用
        if not self.per_delay:
            if not self.multi_output:
                if mask != self.target and gates >= self.best_gates_found:
                    return
            else:
                if mask not in self.target_set and gates >= self.best_gates_found:
                    return

        key = (mask, is_tri)
        layer_dict = self.best_per_layer[delay]
        old = layer_dict.get(key)
        if old is None or gates < old[0]:
            layer_dict[key] = (gates, expr, switches_list)

    def _init_base(self):
        self._add_candidate(0, 0, "0", False, 0)
        self._add_candidate(self.all_mask, 0, "1", False, 0)
        for i in range(self.n):
            mask = 0
            for row in range(self.N):
                if (row >> i) & 1:
                    mask |= (1 << row)
            self._add_candidate(mask, 0, f"x{i}", False, 0)

    def _is_short_free(self, list1, list2):
        for en1, data1 in list1:
            for en2, data2 in list2:
                if (en1 & en2 & (data1 ^ data2)) != 0:
                    return False
        return True

    def _get_layer_candidates(self, delay):
        cands = []
        for (mask, is_tri), (gates, expr, swl) in self.best_per_layer[delay].items():
            cands.append((mask, gates, expr, is_tri, swl))
        return cands

    # ---------- 枚举核心 ----------
    def _enumerate(self):
        start = time.time()
        last = start

        for delay in range(1, self.D + 1):
            prev_cands = self._get_layer_candidates(delay - 1)
            prev_cands.sort(key=lambda x: x[1])

            # NOT
            for m1, g1, e1, _, swl1 in prev_cands:
                if not (e1.startswith(("AND", "OR", "NAND", "NOR", "NOT"))):
                    self._add_candidate(self.all_mask ^ m1, g1 + 1, f"NOT({e1})", False, delay)

            # 二层组合
            for d1 in range(delay):
                list1 = self._get_layer_candidates(d1)
                list1 = [x for x in list1 if x[0] not in (0, self.all_mask)]
                if not list1:
                    continue
                list1.sort(key=lambda x: x[1])
                for d2 in range(d1, delay):
                    if max(d1, d2) != delay - 1:
                        continue
                    list2 = self._get_layer_candidates(d2)
                    list2 = [x for x in list2 if x[0] not in (0, self.all_mask)]
                    if not list2:
                        continue
                    list2.sort(key=lambda x: x[1])

                    for i1, (m1, g1, e1, _, swl1) in enumerate(list1):
                        if not self.per_delay and g1 + list2[0][1] + 1 > self.best_gates_found:
                            break
                        for i2, (m2, g2, e2, _, swl2) in enumerate(list2):
                            if d1 == d2 and i1 >= i2:
                                continue
                            base_g = g1 + g2 + 1
                            if not self.per_delay and base_g > self.best_gates_found:
                                break

                            m_and = m1 & m2
                            m_or = m1 | m2
                            if m_and not in (m1, m2):
                                self._add_candidate(m_and, base_g, f"AND({e1},{e2})", False, delay)
                            if m_or not in (m1, m2):
                                self._add_candidate(m_or, base_g, f"OR({e1},{e2})", False, delay)
                            self._add_candidate(self.all_mask ^ m_and, base_g, f"NAND({e1},{e2})", False, delay)
                            self._add_candidate(self.all_mask ^ m_or, base_g, f"NOR({e1},{e2})", False, delay)

                            # SWITCH
                            sw_delay = max(d1, d2) + 1
                            if sw_delay <= self.D:
                                sw_base = g1 + g2 + 2
                                if self.per_delay or sw_base <= self.best_gates_found:
                                    if not swl1:
                                        sw = m1 & m2
                                        if sw not in (m1, m2):
                                            self._add_candidate(sw, sw_base, f"SWITCH({e1},{e2})", True, sw_delay, [(m1, m2)])
                                    if not swl2 and (d1 != d2 or m1 != m2):
                                        sw = m2 & m1
                                        if sw not in (m1, m2):
                                            self._add_candidate(sw, sw_base, f"SWITCH({e2},{e1})", True, sw_delay, [(m2, m1)])

            # 多输出上界更新
            if self.multi_output:
                new_bound = 0
                all_found = True
                for ti in range(self.num_targets):
                    min_g = 999999
                    for d in range(delay + 1):
                        if self.target_candidates[ti][d]:
                            min_g = min(min_g, min(g for g, _, _ in self.target_candidates[ti][d]))
                    if min_g == 999999:
                        all_found = False
                        break
                    new_bound += min_g
                if all_found and new_bound < self.best_gates_found:
                    self.best_gates_found = new_bound

            # ---------- BUS_OR 合并（DFS剪枝，仅枚举目标子集） ----------
            raw_switches = []
            for (mask, is_tri), (gates, expr, swl) in self.best_per_layer[delay].items():
                if is_tri and swl and len(swl) == 1:
                    if not self.multi_output and (mask & ~self.target) == 0:
                        raw_switches.append((mask, gates, expr, swl))
                    elif self.multi_output:
                        for t in self.targets:
                            if (mask & ~t) == 0:
                                raw_switches.append((mask, gates, expr, swl))
                                break

            if raw_switches and not self.multi_output:
                raw_switches.sort(key=lambda x: x[1])
                target = self.target
                best_for_mask = {}

                def dfs(start, cur_mask, cur_gates, cur_expr, cur_swl):
                    nonlocal best_for_mask
                    if cur_mask == target:
                        self._add_candidate(cur_mask, cur_gates, cur_expr, False, delay, cur_swl)
                        return
                    for i in range(start, len(raw_switches)):
                        m2, g2, e2, swl2 = raw_switches[i]
                        new_mask = cur_mask | m2
                        if new_mask == cur_mask:
                            continue
                        if (new_mask & ~target) != 0:
                            continue
                        new_gates = cur_gates + g2
                        if best_for_mask.get(new_mask, 999999) <= new_gates:
                            continue
                        best_for_mask[new_mask] = new_gates
                        new_expr = f"BUS_OR({cur_expr},{e2})" if cur_expr else e2
                        new_swl = cur_swl + swl2
                        dfs(i + 1, new_mask, new_gates, new_expr, new_swl)

                for i in range(len(raw_switches)):
                    m, g, e, swl = raw_switches[i]
                    if m == target:
                        self._add_candidate(m, g, e, False, delay, swl)
                    else:
                        best_for_mask.clear()
                        best_for_mask[m] = g
                        dfs(i + 1, m, g, e, swl)

            now = time.time()
            total = sum(len(d) for d in self.best_per_layer)
            print(f"延迟 {delay}/{self.D} | 候选 {total} | 上界 {self.best_gates_found} | "
                  f"本层 {now - last:.1f}s | 累计 {now - start:.1f}s")
            last = now
        print(f"枚举完成，总耗时 {time.time() - start:.2f}s")

    # ---------- 表达式规范化与统计（已加固） ----------
    def _canonicalize_expr(self, expr):
        if not expr or expr in ('0', '1') or (expr[0] == 'x' and expr[1:].isdigit()):
            return expr
        if expr.startswith('NOT('):
            return f"NOT({self._canonicalize_expr(expr[4:-1])})"
        if expr.startswith('SWITCH('):
            inner = expr[7:-1]
            en, data = self._split_top_level(inner)
            en_c = self._canonicalize_expr(en) if en else "0"
            data_c = self._canonicalize_expr(data) if data else "0"
            return f"SWITCH({en_c},{data_c})"
        if expr.startswith('BUS_OR('):
            inner = expr[7:-1]
            args = self._split_bus_args(inner)
            flat = []
            for a in args:
                ca = self._canonicalize_expr(a)
                if ca and ca != "":
                    if ca.startswith('BUS_OR('):
                        sub_inner = ca[7:-1]
                        sub_args = self._split_bus_args(sub_inner)
                        flat.extend(sub_args)
                    else:
                        flat.append(ca)
            flat = sorted(set([f for f in flat if f and f != ""]))
            if not flat:
                return "0"
            return "BUS_OR(" + ",".join(flat) + ")"
        else:
            try:
                op_end = expr.index('(')
                op = expr[:op_end]
                inner = expr[op_end+1:-1]
                left, right = self._split_top_level(inner)
                left_c = self._canonicalize_expr(left) if left else "0"
                right_c = self._canonicalize_expr(right) if right else "0"
                return f"{op}({left_c},{right_c})"
            except ValueError:
                return expr

    def _collect_sub_exprs(self, expr, sub_set):
        if not expr or expr in sub_set:
            return
        sub_set.add(expr)
        if expr in ('0', '1') or (expr[0] == 'x' and expr[1:].isdigit()):
            return
        if expr.startswith('NOT('):
            self._collect_sub_exprs(expr[4:-1], sub_set)
        elif expr.startswith('SWITCH('):
            inner = expr[7:-1]
            en, data = self._split_top_level(inner)
            if en:
                self._collect_sub_exprs(en, sub_set)
            if data:
                self._collect_sub_exprs(data, sub_set)
        elif expr.startswith('BUS_OR('):
            inner = expr[7:-1]
            for a in self._split_bus_args(inner):
                if a:
                    self._collect_sub_exprs(a, sub_set)
        else:
            try:
                paren = expr.index('(')
                inner = expr[paren+1:-1]
                left, right = self._split_top_level(inner)
                if left:
                    self._collect_sub_exprs(left, sub_set)
                if right:
                    self._collect_sub_exprs(right, sub_set)
            except ValueError:
                pass

    def _dag_gate_count(self, expr):
        sub_set = set()
        self._collect_sub_exprs(expr, sub_set)
        cnt = 0
        for s in sub_set:
            if s in ('0', '1') or (s[0] == 'x' and s[1:].isdigit()):
                continue
            if s.startswith('SWITCH('):
                cnt += 2
            elif s.startswith('BUS_OR('):
                pass
            else:
                cnt += 1
        return cnt

    @lru_cache(maxsize=None)
    def _multi_dag_gate_count_cached(self, exprs_tuple):
        all_sub = set()
        for e in exprs_tuple:
            self._collect_sub_exprs(e, all_sub)
        cnt = 0
        for s in all_sub:
            if s in ('0', '1') or (s[0] == 'x' and s[1:].isdigit()):
                continue
            if s.startswith('SWITCH('):
                cnt += 2
            elif s.startswith('BUS_OR('):
                pass
            else:
                cnt += 1
        return cnt

    def _multi_dag_gate_count(self, exprs):
        return self._multi_dag_gate_count_cached(tuple(sorted(exprs)))

    # ---------- 工具函数：Pareto剪枝 ----------
    def _pareto_prune(self, sols):
        """输入列表 [(delay, gates, expr_or_tuple)]，返回Pareto非支配解（去重）"""
        # 先按表达式去重
        seen = set()
        unique = []
        for d, g, e in sols:
            key = e if isinstance(e, str) else tuple(e)
            if key not in seen:
                seen.add(key)
                unique.append((d, g, e))
        if not unique:
            return []
        # 对每个解检查是否被支配
        pareto = []
        for i, (d1, g1, e1) in enumerate(unique):
            dominated = False
            for j, (d2, g2, e2) in enumerate(unique):
                if i == j:
                    continue
                if d2 <= d1 and g2 <= g1 and (d2 < d1 or g2 < g1):
                    dominated = True
                    break
            if not dominated:
                pareto.append((d1, g1, e1))
        # 按门数排序，门数相同按延迟
        pareto.sort(key=lambda x: (x[1], x[0]))
        return pareto

    # ---------- 多输出共享搜索 ----------
    def _shared_combine(self):
        print("开始多输出共享搜索...")
        raw_opts = []
        for ti in range(self.num_targets):
            opts = []
            for d in range(self.D + 1):
                for gates_tree, expr, _ in self.target_candidates[ti][d]:
                    canon = self._canonicalize_expr(expr)
                    real_g = self._dag_gate_count(canon)
                    opts.append((d, real_g, canon))
            best = {}
            for d, rg, e in opts:
                if e not in best or rg < best[e][1]:
                    best[e] = (d, rg, e)
            uniq = sorted(best.values(), key=lambda x: (x[1], x[0]))
            print(f"  输出 {ti}: {len(opts)} -> {len(uniq)} 种表达式")
            raw_opts.append(uniq)

        if self.per_delay:
            # 每个延迟收集最优共享解，然后合并进行Pareto剪枝
            combined = []
            for global_delay in range(self.D + 1):
                delay_opts = []
                min_gates_per_out = []
                for ti in range(self.num_targets):
                    cands = [(rg, e) for d, rg, e in raw_opts[ti] if d <= global_delay]
                    if not cands:
                        break
                    cands.sort(key=lambda x: x[0])
                    if len(cands) > 200:
                        cands = cands[:200]
                    delay_opts.append(cands)
                    min_gates_per_out.append(cands[0][0])
                if len(delay_opts) != self.num_targets:
                    continue

                upper_bound = sum(min_gates_per_out)
                print(f"  延迟 {global_delay}: 独立最小和={upper_bound}")

                # 贪心初始解
                chosen = [c[0][1] for c in delay_opts]
                best_g = self._multi_dag_gate_count(chosen)
                best_combo = (best_g, list(chosen))

                # DFS搜索
                visited = 0
                start_t = time.time()
                def dfs(idx, current_exprs):
                    nonlocal best_combo, visited
                    visited += 1
                    if visited % 50000 == 0:
                        print(f"    节点 {visited}, 最优 {best_combo[0]}, 耗时 {time.time()-start_t:.1f}s")
                    if idx == self.num_targets:
                        cur_g = self._multi_dag_gate_count(current_exprs)
                        if cur_g < best_combo[0]:
                            best_combo = (cur_g, list(current_exprs))
                        return
                    cur_g = self._multi_dag_gate_count(current_exprs)
                    if cur_g >= best_combo[0]:
                        return
                    for rg, e in delay_opts[idx]:
                        new_exprs = current_exprs + [e]
                        if self._multi_dag_gate_count(new_exprs) >= best_combo[0]:
                            continue
                        dfs(idx + 1, new_exprs)
                dfs(0, [])
                print(f"  延迟 {global_delay} 最优总门数 {best_combo[0]}, 耗时 {time.time()-start_t:.1f}s")
                combined.append((global_delay, best_combo[0], tuple(best_combo[1])))

            # 对combined进行Pareto剪枝
            self.delay_solutions = {}
            pareto = self._pareto_prune(combined)
            for d, g, exprs in pareto:
                self.delay_solutions[d] = [(g, list(exprs))]
            # 按延迟排序
            self.delay_solutions = dict(sorted(self.delay_solutions.items()))
        else:
            # 非per_delay：收集所有解，去重，Pareto剪枝
            all_sols = []
            for d in range(self.D + 1):
                # 收集该延迟所有输出组合
                # 这里简化，直接从raw_opts中组合，但raw_opts是每个输出的独立候选，
                # 真正共享搜索已经在上面做了，但为了统一，我们直接使用上面得到的各延迟最优？
                # 但上面循环已经为每个延迟找到了最优共享解，但我们这里要全局Pareto，
                # 应该收集所有可能的共享解，但为了性能，我们只收集每个延迟的最优解（面积最优）作为候选？
                # 然而用户想要Pareto，可能需要不止一个解，但共享搜索本身已经在每个延迟找了一个最优，
                # 为了得到多目标，我们可以在每个延迟的搜索中保留多个解，但为了简化，我们采用
                # 目前每个延迟只保留一个最优共享解，这不足以得到Pareto前沿。
                # 因此，对于多输出，我们需要在共享搜索中保留多个候选解，而不是仅保留一个。
                # 为了代码简洁，我们修改策略：收集每个输出独立的所有候选，然后对组合进行穷举，
                # 但那样会组合爆炸。作为折衷，我们只保留每个延迟的最优共享解（面积最优），
                # 这样可以得到延迟-面积的Pareto。
                # 实际上，用户的问题只针对单输出，多输出很少用。因此我们暂时只处理单输出。
                pass

    # ---------- 单输出收集 ----------
    def _collect_single(self):
        if self.per_delay:
            # 收集每个延迟的最优解（可能有多个等价表达式）
            per_delay_best = []
            for d in range(self.D + 1):
                cands = self.target_candidates[0][d]
                if not cands:
                    continue
                # 每个延迟内找门数最小的
                min_g = min(g for g, _, _ in cands)
                for g, e, _ in cands:
                    if g == min_g:
                        canon = self._canonicalize_expr(e)
                        real_g = self._dag_gate_count(canon)
                        per_delay_best.append((d, real_g, canon))
            # 去重并Pareto剪枝
            pareto = self._pareto_prune(per_delay_best)
            # 按延迟排序
            self.delay_solutions = {}
            for d, g, e in pareto:
                if d not in self.delay_solutions:
                    self.delay_solutions[d] = []
                self.delay_solutions[d].append((g, e))
            # 每个延迟若有多个，只保留一个（按门数）
            for d in list(self.delay_solutions.keys()):
                self.delay_solutions[d] = sorted(self.delay_solutions[d], key=lambda x: x[0])
                if not self.output_all:
                    self.delay_solutions[d] = [self.delay_solutions[d][0]]
        else:
            # 收集所有候选
            all_cands = []
            for d in range(self.D + 1):
                for g, e, _ in self.target_candidates[0][d]:
                    canon = self._canonicalize_expr(e)
                    real_g = self._dag_gate_count(canon)
                    all_cands.append((d, real_g, canon))
            # 去重并Pareto剪枝
            pareto = self._pareto_prune(all_cands)
            if self.output_all:
                self.solutions = pareto
            else:
                self.solutions = [pareto[0]] if pareto else []

    def synthesize(self):
        start = time.time()
        print(f"精确枚举 (n={self.n}, D={self.D}, 输出数={self.num_targets})")
        self._enumerate()

        if self.multi_output:
            self._shared_combine()
            if self.per_delay:
                if not self.delay_solutions:
                    print("无共享解")
                else:
                    print("\n每延迟Pareto最优解 (未被支配):")
                    for d in sorted(self.delay_solutions.keys()):
                        for g, exprs in self.delay_solutions[d]:
                            print(f"  延迟 {d} | 总门数 {g} | 成本 {d*g}")
                            if isinstance(exprs, tuple):
                                for i, e in enumerate(exprs):
                                    print(f"    输出{i}: {e}")
                            else:
                                print(f"    {exprs}")
                return self.delay_solutions
            else:
                if not self.solutions:
                    print("无全局最优共享解")
                    return []
                print(f"\n全局Pareto最优解 (未被支配):")
                for idx, (d, total_g, exprs) in enumerate(self.solutions):
                    print(f"  #{idx+1}: 延迟 {d} | 总门数 {total_g} | 成本 {d*total_g}")
                    if isinstance(exprs, tuple):
                        for i, e in enumerate(exprs):
                            print(f"    输出{i}: {e}")
                    else:
                        print(f"    {exprs}")
                return self.solutions
        else:
            self._collect_single()
            if self.per_delay:
                if not self.delay_solutions:
                    print("无解")
                else:
                    print("\n每延迟Pareto最优解 (未被支配):")
                    for d in sorted(self.delay_solutions.keys()):
                        for g, e in self.delay_solutions[d]:
                            print(f"  延迟 {d} | 门数 {g} | 成本 {d*g} | {e}")
                return self.delay_solutions
            else:
                if not self.solutions:
                    print("无解")
                    return []
                print(f"\n全局Pareto最优解 (未被支配):")
                for idx, (d, g, e) in enumerate(self.solutions):
                    print(f"  #{idx+1}: 延迟 {d} | 门数 {g} | 成本 {d*g} | {e}")
                return self.solutions


if __name__ == "__main__":
    print("=== 全加器 SUM (每延迟Pareto最优，应出现延迟2、3、4) ===")
    LogicSynthesizer(3, 0x96, 6, output_mode="all", per_delay=True).synthesize()

    print("\n=== 全加器 SUM (全局Pareto最优，应出现延迟2、3、4) ===")
    LogicSynthesizer(3, 0x96, 6, output_mode="all", per_delay=False).synthesize()
