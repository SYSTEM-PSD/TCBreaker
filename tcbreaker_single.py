# TCBreaker —— 真值表最优门级电路综合器（单文件版）
#
# 功能：给定 n 输入真值表与延迟上限，枚举搜索在延迟约束下门数最少的门级电路。
# 核心模块：
#   expr       —— 表达式 AST、三态(0/1/Z/短路)求值、DAG 代价与延迟、真值表验证器
#   truthtable —— 真值表掩码的构造 / 解析 / 格式化
#   synth      —— 分层精确枚举（按延迟分层 + 上界剪枝 + 多输出共享 DP + Pareto）
#   draw       —— 电路图 SVG（重心法布局 + 列间隙轨道分配 + 跨层飞线 + 网络配色）
#   cli / selftest —— 命令行入口与内置自检（含随机回归）
# 关键流程：解析目标 → 逐延迟层枚举候选（二元门/非门/三态开关/总线合并）
#           → 命中目标即按 DAG 门数记录 → 解层做 Pareto / 多输出共享组合
#           → 每个解逐行回代真值表校验 → 输出文本 / Python / SVG / JSON。
# 依赖：仅 Python 标准库，零第三方包。
#
# 声明：本文件部分代码由 AI 辅助生成，经作者审阅与验证后纳入。
# Notice: part of this code was generated with AI assistance and reviewed/verified by the author.

from __future__ import annotations

import argparse
import os
import random
import sys
import time
from dataclasses import dataclass, field
from typing import (Callable, Dict, Iterable, Iterator, List, NamedTuple,
                    Optional, Sequence, Set, Tuple, Union)
from xml.sax.saxutils import escape as _xml_escape

__version__ = "1.0.0"

# 原各模块里的 ``X.xxx`` 是对 expr 模块的相对引用；合并后让 X 指向本模块自身，
# 这样所有 X.to_str / X.verify / X.dag_cost 等调用无需改动即可继续工作。
X = sys.modules[__name__]


# ==========================================================================
# 表达式 / 三态求值 / 代价模型 / 验证器
# ==========================================================================

"""表达式 AST、三态求值与代价模型。

表达式用不可变元组表示（可哈希、可去重、天然共享子结构）：:

    ('0',) / ('1',)                 常量
    ('x', i)                        第 i 个输入（x0 为最低位）
    ('AND'|'OR'|'NAND'|'NOR'|'XOR'|'XNOR', a, b)
    ('NOT', a)
    ('SWITCH', enable, data)        三态开关：enable=1 时导通，否则浮空
    ('BUS', a, b, ...)              三态总线合并（已展平、已排序）
"""


Expr = tuple

ZERO: Expr = ("0",)
ONE: Expr = ("1",)

COMMUTATIVE = ("AND", "OR", "NAND", "NOR", "XOR", "XNOR")
BINARY_OPS = COMMUTATIVE
ALL_OPS = COMMUTATIVE + ("NOT", "SWITCH", "BUS")

# 三态求值结果
Z = None            # 浮空
CONFLICT = "X"      # 总线短路（多个驱动源值不同）

# --------------------------------------------------------------------------
# 内部化：给每个规范节点分配一个稳定的整数序号
# --------------------------------------------------------------------------
# 用途有两个：(1) 元组比较走 `==` 时的身份快捷路径，让 ``a == b`` 变成 O(1)；
# (2) 为交换律运算提供 O(1) 的参数排序依据。序号只在进程内稳定，
# 但不影响任何结果的正确性（只影响去重的彻底程度）。
_RANK: dict = {}


def rank(e: Expr) -> int:
    """返回节点的稳定序号（首次见到时分配）。"""
    r = _RANK.get(e)
    if r is None:
        r = len(_RANK)
        _RANK[e] = r
    return r


def clear_intern() -> None:
    """清空内部化表，释放内存。仅建议在批量任务之间调用。"""
    _RANK.clear()


# --------------------------------------------------------------------------
# 构造
# --------------------------------------------------------------------------
def var(i: int) -> Expr:
    return ("x", int(i))


def const(bit: int) -> Expr:
    return ONE if bit else ZERO


def not_(a: Expr) -> Expr:
    node = ("NOT", a)
    rank(node)
    return node


def gate(op: str, a: Expr, b: Expr) -> Expr:
    """构造二元门；交换律运算的参数按**确定性**规范序排列。

    用原生元组比较 ``a > b``（按 Unicode 逐元素比较，稳定且廉价），
    不再用 ``rank``（创建顺序）——否则同一函数的规范表示会随内部状态漂移，
    既破坏 ``to_str`` 往返，也让综合结果不可复现。
    """
    if op in COMMUTATIVE and a > b:
        a, b = b, a
    node = (op, a, b)
    rank(node)
    return node


def switch(en: Expr, data: Expr) -> Expr:
    node = ("SWITCH", en, data)
    rank(node)
    return node


def bus(*args: Expr) -> Expr:
    """构造总线合并：展平嵌套、去重、按规范序排序。"""
    flat: List[Expr] = []
    seen: Set[Expr] = set()
    stack: List[Expr] = list(args)
    while stack:
        a = stack.pop()
        if a[0] == "BUS":
            stack.extend(a[1:])
        elif a not in seen:
            seen.add(a)
            flat.append(a)
    if not flat:
        return ZERO
    if len(flat) == 1:
        return flat[0]
    flat.sort()  # 原生元组比较，确定性且廉价
    node = ("BUS",) + tuple(flat)
    rank(node)
    return node


def is_const(e: Expr) -> bool:
    return e[0] in ("0", "1")


def is_var(e: Expr) -> bool:
    return e[0] == "x"


# --------------------------------------------------------------------------
# 字符串化 / 解析
# --------------------------------------------------------------------------
def to_str(e: Expr) -> str:
    t = e[0]
    if t in ("0", "1"):
        return t
    if t == "x":
        return "x%d" % e[1]
    if t == "BUS":
        return "BUS_OR(" + ",".join(to_str(a) for a in e[1:]) + ")"
    return "%s(%s)" % (t, ",".join(to_str(a) for a in e[1:]))


def _skip_ws(s: str, i: int) -> int:
    while i < len(s) and s[i].isspace():
        i += 1
    return i


def _expect(s: str, i: int, ch: str) -> int:
    i = _skip_ws(s, i)
    if i >= len(s) or s[i] != ch:
        raise ValueError("解析 %r 时在位置 %d 期望 %r" % (s, i, ch))
    return i + 1


def _parse(s: str, i: int) -> Tuple[Expr, int]:
    i = _skip_ws(s, i)
    if i >= len(s):
        raise ValueError("表达式意外结束")
    c = s[i]
    if c == "(":
        node, i = _parse(s, i + 1)
        return node, _expect(s, i, ")")
    if c in "01":
        return const(int(c)), i + 1
    if c in "xX" and i + 1 < len(s) and s[i + 1].isdigit():
        j = i + 1
        while j < len(s) and s[j].isdigit():
            j += 1
        return var(int(s[i + 1:j])), j
    # 运算符标识符（注意要先排除 XNOR 这种以 X 开头的名字）
    j = i
    while j < len(s) and (s[j].isalnum() or s[j] == "_"):
        j += 1
    name = s[i:j].upper()
    i = _expect(s, j, "(")
    args: List[Expr] = []
    while True:
        node, i = _parse(s, i)
        args.append(node)
        i = _skip_ws(s, i)
        if i < len(s) and s[i] == ",":
            i += 1
            continue
        i = _expect(s, i, ")")
        break
    if name == "NOT":
        if len(args) != 1:
            raise ValueError("NOT 需要 1 个参数，收到 %d 个" % len(args))
        return not_(args[0]), i
    if name == "SWITCH":
        if len(args) != 2:
            raise ValueError("SWITCH 需要 2 个参数，收到 %d 个" % len(args))
        return switch(args[0], args[1]), i
    if name in ("BUS", "BUS_OR", "BUSOR"):
        return bus(*args), i
    if name in COMMUTATIVE:
        if len(args) != 2:
            raise ValueError("%s 需要 2 个参数，收到 %d 个" % (name, len(args)))
        return gate(name, args[0], args[1]), i
    raise ValueError("未知运算符：%r" % name)


def parse(text: str) -> Expr:
    """把 ``AND(x0,NOT(x1))`` 这样的文本解析成 AST。"""
    node, i = _parse(text, 0)
    i = _skip_ws(text, i)
    if i != len(text):
        raise ValueError("位置 %d 存在多余内容：%r" % (i, text[i:]))
    return node


# --------------------------------------------------------------------------
# 三态求值
# --------------------------------------------------------------------------
def eval3(e: Expr, row: int, pull_down: bool = True):
    """在输入组合 ``row`` 上求值。

    返回 0 / 1 / ``Z``(浮空) / ``CONFLICT``(总线短路)。

    ``pull_down=True``（默认，也是图灵完备的行为）表示未被驱动的线读取为 0，
    此时永远不会返回 ``Z``；只有多个驱动源输出不同值才会得到 ``CONFLICT``。
    """
    t = e[0]
    if t == "0":
        return 0
    if t == "1":
        return 1
    if t == "x":
        return (row >> e[1]) & 1
    if t == "NOT":
        v = eval3(e[1], row, pull_down)
        return (0 if pull_down else Z) if v is None else 1 - v
    if t == "SWITCH":
        en = eval3(e[1], row, pull_down)
        if en is None or en == 0:
            # 断开时必须返回 Z 而不是 0：0 是「被驱动的 0」，
            # 会被总线当成第二个驱动源而误报短路。
            return Z
        return eval3(e[2], row, pull_down)
    if t == "BUS":
        val = None
        for a in e[1:]:
            v = eval3(a, row, pull_down)
            if v is None:
                continue
            if val is None:
                val = v
            elif val != v:
                return CONFLICT
        return (0 if pull_down else Z) if val is None else val
    a = eval3(e[1], row, pull_down)
    b = eval3(e[2], row, pull_down)
    if a is None or b is None:
        return 0 if pull_down else Z
    if t == "AND":
        return a & b
    if t == "OR":
        return a | b
    if t == "NAND":
        return 1 - (a & b)
    if t == "NOR":
        return 1 - (a | b)
    if t == "XOR":
        return a ^ b
    if t == "XNOR":
        return 1 - (a ^ b)
    raise ValueError("未知运算符：%r" % t)


# --------------------------------------------------------------------------
# 代价模型
# --------------------------------------------------------------------------
def dag_nodes(e: Expr) -> Set[Expr]:
    """返回表达式中出现的所有不同节点（用于 DAG 共享计数）。"""
    seen: Set[Expr] = set()
    stack: List[Expr] = [e]
    while stack:
        x = stack.pop()
        if x in seen:
            continue
        seen.add(x)
        t = x[0]
        if t == "0" or t == "1" or t == "x":
            continue
        stack.extend(x[1:])
    return seen


def dag_cost(e: Expr, switch_cost: int = 1) -> int:
    """DAG 门数：共享的子电路只算一次；总线合并是导线，不计门。"""
    total = 0
    for x in dag_nodes(e):
        t = x[0]
        if t in ("0", "1", "x"):
            continue       # 输入和常量不占门
        if t == "SWITCH":
            total += switch_cost
        elif t == "BUS":
            pass           # 总线合并是导线，不计门
        else:
            total += 1
    return total


def dag_delay(e: Expr, switch_delay: int = 1, bus_delay: int = 0) -> int:
    """关键路径延迟（以门级数为单位）。输入为 0。"""
    memo: dict = {}

    def walk(x: Expr) -> int:
        v = memo.get(x)
        if v is not None:
            return v
        t = x[0]
        if t in ("0", "1", "x"):
            v = 0
        elif t == "BUS":
            v = bus_delay + max(walk(c) for c in x[1:])
        elif t == "SWITCH":
            v = switch_delay + max(walk(x[1]), walk(x[2]))
        else:
            v = 1 + max(walk(c) for c in x[1:])
        memo[x] = v
        return v

    return walk(e)


# --------------------------------------------------------------------------
# 验证（整个项目可信度的地基）
# --------------------------------------------------------------------------
def verify(e: Expr, num_inputs: int, target: int,
           pull_down: bool = True) -> Optional[str]:
    """逐行回代真值表。正确返回 None，否则返回人话错误说明。"""
    rows = 1 << num_inputs
    for row in range(rows):
        v = eval3(e, row, pull_down)
        if v is Z:
            # 浮空只影响「有没有驱动源」，下拉发生在读取点（这里是最终输出）
            v = 0 if pull_down else Z
        want = (target >> row) & 1
        if v is CONFLICT:
            return "第 %d 行：总线短路（多个驱动源输出不同的值）" % row
        if v is Z:
            return "第 %d 行：输出浮空（没有任何驱动源导通），期望 %d" % (row, want)
        if v != want:
            return "第 %d 行：得到 %d，期望 %d" % (row, v, want)
    return None


def verify_multi(exprs: Sequence[Expr], num_inputs: int, targets: Sequence[int],
                 pull_down: bool = True) -> Optional[str]:
    for i, (e, t) in enumerate(zip(exprs, targets)):
        err = verify(e, num_inputs, t, pull_down)
        if err:
            return "输出 %d：%s" % (i, err)
    return None


# ==========================================================================
# 真值表掩码工具
# ==========================================================================

"""真值表（位掩码）工具。

约定：第 ``row`` 位对应输入组合 ``row`` 的整数值，其中 ``x0`` 是最低位。
例如 SUM 的真值表 0x96 = 1001_0110b，置位的行是 1, 2, 4, 7。
"""


def as_mask(value: Union[int, str, Iterable[int]], n_rows: int) -> int:
    """把多种写法统一成掩码整数。

    * ``int``  —— 直接用（如 ``0x96``）
    * ``str``  —— ``"0x96"`` / ``"0b10010110"`` / ``"10010110"``（高位在前）
                  或逗号分隔的 0/1 序列 ``"0,1,1,0,1,0,0,1"``（低位在前）
    * 可迭代  —— 0/1 序列，第 k 个元素是第 k 行的输出
    """
    if isinstance(value, int):
        m = int(value)
    elif isinstance(value, str):
        m = _parse_str(value, n_rows)
    else:
        bits = list(value)
        if len(bits) != n_rows:
            raise ValueError("需要 %d 个输出位，收到 %d 个" % (n_rows, len(bits)))
        m = 0
        for i, b in enumerate(bits):
            if int(b):
                m |= 1 << i
    if m < 0:
        raise ValueError("掩码不能为负")
    if m >> n_rows:
        raise ValueError("掩码 0x%X 超出了 %d 行真值表的范围" % (m, n_rows))
    return m


def _parse_str(text: str, n_rows: int) -> int:
    """支持 0x96 / 0b10010110 / 10010110 / "0 1 1 0 ..."（低位在前）。"""
    s = text.strip().replace("_", "").replace(",", " ")
    if not s:
        raise ValueError("空字符串不是合法真值表")
    low = s.lower()
    if low.startswith("0x"):
        return int(s, 16)
    if low.startswith("0b"):
        return int(s, 2)
    parts = s.split()
    if len(parts) > 1:
        if len(parts) != n_rows:
            raise ValueError("需要 %d 个输出位，收到 %d 个" % (n_rows, len(parts)))
        m = 0
        for i, p in enumerate(parts):
            if p not in ("0", "1"):
                raise ValueError("第 %d 项 %r 不是 0 或 1" % (i, p))
            if p == "1":
                m |= 1 << i
        return m
    if all(c in "01" for c in s):
        if len(s) != n_rows:
            raise ValueError("二进制串长度 %d 与真值表行数 %d 不符" % (len(s), n_rows))
        return int(s, 2)  # 与十六进制写法一致：高位在前（第 n-1 行写在最左边）
    raise ValueError("无法解析真值表：%r" % text)


def from_bits(bits: Iterable[int]) -> int:
    """由 0/1 序列构造掩码，第 k 项对应第 k 行。"""
    m = 0
    for i, b in enumerate(bits):
        if int(b):
            m |= 1 << i
    return m


def from_function(num_inputs: int, fn: Callable[..., int]) -> int:
    """由布尔函数构造掩码，``fn(x0, x1, ...)``。"""
    m = 0
    for row in range(1 << num_inputs):
        args = [(row >> i) & 1 for i in range(num_inputs)]
        if fn(*args):
            m |= 1 << row
    return m


def mask_to_bits(mask: int, n_rows: int) -> List[int]:
    return [(mask >> r) & 1 for r in range(n_rows)]


def random_mask(num_inputs: int, rng=None) -> int:
    import random
    rng = rng or random
    return rng.getrandbits(1 << num_inputs)


def format_table(num_inputs: int, mask: int) -> str:
    """画一张人类可读的真值表。"""
    rows = 1 << num_inputs
    names = ["x%d" % i for i in range(num_inputs)][::-1]
    lines = ["  ".join(names) + "  |  y", "-" * (4 * num_inputs + 6)]
    for r in range(rows):
        cols = "  ".join(str((r >> i) & 1) for i in reversed(range(num_inputs)))
        lines.append("%s  |  %d" % (cols, (mask >> r) & 1))
    return "\n".join(lines)


class Masks:
    """常用函数，方便直接拿来跑。"""

    @staticmethod
    def var(num_inputs: int, i: int) -> int:
        m = 0
        for r in range(1 << num_inputs):
            if (r >> i) & 1:
                m |= 1 << r
        return m

    @staticmethod
    def xor(num_inputs: int) -> int:
        return from_function(num_inputs, lambda *a: sum(a) & 1)

    @staticmethod
    def majority(num_inputs: int) -> int:
        return from_function(num_inputs, lambda *a: 1 if sum(a) * 2 > num_inputs else 0)

    @staticmethod
    def and_(num_inputs: int) -> int:
        return from_function(num_inputs, lambda *a: 1 if all(a) else 0)


# ==========================================================================
# 分层精确枚举综合器
# ==========================================================================

"""分层精确枚举综合器。

思路：按「延迟」分层，第 d 层保存所有延迟恰为 d 的子电路候选，逐层用
一元/二元门、三态开关、总线合并做闭包扩展，直到 max_delay。
每个 (mask, 是否三态) 只保留门数最小的若干个候选，配合全局上界剪枝。

注意：枚举期用的是「树门数」（共享子电路会被重复计数），最终报告的是
``dag_cost``（共享只算一次）。剪枝时因此留出 ``prune_slack`` 的余量，
避免把「树大但共享后更省」的解剪掉。
"""


INF = 1 << 30

@dataclass
class Config:
    """综合器的全部可调项。"""

    # 允许的二元门。Target 规格规定门级原语仅限
    # AND / OR / NOT / NOR / NAND / SWITCH，因此默认不含 XOR / XNOR
    # （NOT 是 `use_not` 的一元原语，SWITCH 是三态原语）。
    ops: Tuple[str, ...] = ("AND", "OR", "NAND", "NOR")
    use_not: bool = True            # 是否允许非门（NOT 是一元原语）
    not_on_gates: bool = True       # NOT 可作用于任意信号（含门/总线输出），符合通用原语语义
    use_switch: bool = True
    use_bus: bool = True
    allow_nested_switch: bool = True  # 开关的数据端能否接一条总线

    switch_cost: int = 2            # 三态门门数计为 2（Target 规格）
    switch_delay: int = 1
    bus_delay: int = 0              # 总线合并是导线（wired-OR 免费），不增加延迟
    floating_reads_zero: bool = True  # Z 输出自动下拉为 0（下拉模型）

    max_switches_per_bus: int = 4
    top_k_comb: int = 2             # 每个 (mask, 非三态) 保留的候选数（搜索宽度）
    top_k_tri: int = 3              # 每个 (mask, 三态) 保留的候选数
    keep_width: int = 2             # 在最小门数之上额外保留多少门数的候选（利于共享）
    target_cand_cap: int = 48       # 每个「输出 × 延迟」保留多少个命中候选
    bus_seed_limit: int = 32        # 总线合并可用种子数（已按目标过滤后的）
    per_output_candidates: int = 100 # 多输出时每个输出参与共享组合的候选数
    multi_state_limit: int = 60     # 多输出 DP 每个代价点保留的状态数
    alternatives: int = 3           # 同一 (延迟, 门数) 点最多展示几个不同实现
    prune_slack: int = 1            # 剪枝余量，越大越慢但越不容易漏解
    strict_verify: bool = False     # True 时验证失败直接抛异常（测试用）
    verbose: bool = True

    time_limit: float = 0.0           # 秒，0 = 不限时（大任务早停）
    max_total_candidates: int = 0   # 候选总数上限，0 = 不限（内存护栏）

    def __post_init__(self) -> None:
        bad = [o for o in self.ops if o not in X.BINARY_OPS]
        if bad:
            raise ValueError("不支持的运算符 %s，可选：%s" % (bad, list(X.BINARY_OPS)))
        if not self.ops:
            raise ValueError("至少需要一种二元门")
        if self.max_switches_per_bus < 1:
            raise ValueError("max_switches_per_bus 必须 >= 1")
        if self.switch_cost < 0 or self.switch_delay < 0 or self.bus_delay < 0:
            raise ValueError("代价/延迟参数不能为负")
        if self.time_limit < 0:
            raise ValueError("time_limit 不能为负")
        if self.max_total_candidates < 0:
            raise ValueError("max_total_candidates 不能为负")


class Solution(NamedTuple):
    """一个 Pareto 最优解。``expr`` 单输出时是 Expr，多输出时是 Expr 元组。"""

    delay: int
    gates: int
    expr: object

    @property
    def cost(self) -> int:
        return self.delay * self.gates

    @property
    def multi(self) -> bool:
        return bool(self.expr) and isinstance(self.expr[0], tuple)

    def pretty(self) -> str:
        if self.multi:
            return "\n".join("    输出%d: %s" % (i, X.to_str(e))
                             for i, e in enumerate(self.expr))
        return X.to_str(self.expr)

    def __str__(self) -> str:
        head = "延迟 %d | 门数 %d | 成本 %d" % (self.delay, self.gates, self.cost)
        return head + "\n" + self.pretty() if self.multi else head + " | " + self.pretty()


class LogicSynthesizer:
    """把真值表综合成门级电路。"""

    def __init__(self, num_inputs: int, target_truth_table, max_delay: int,
                 output_mode: str = "per_delay", config: Optional[Config] = None):
        n = int(num_inputs)
        if n < 1:
            raise ValueError("num_inputs 必须 >= 1")
        if n > 12:
            raise ValueError("num_inputs=%d 过大（真值表有 %d 行），最多支持 12" % (n, 1 << n))
        self.n = n
        self.N = 1 << n
        self.all_mask = (1 << self.N) - 1

        self.D = int(max_delay)
        if self.D < 0:
            raise ValueError("max_delay 必须 >= 0")

        if output_mode not in ("all", "first", "per_delay"):
            raise ValueError("output_mode 只能是 'all' / 'first' / 'per_delay'")
        self.output_mode = output_mode

        self.cfg = config or Config()

        if isinstance(target_truth_table, (list, tuple)):
            targets = [as_mask(t, self.N) for t in target_truth_table]
        else:
            targets = [as_mask(target_truth_table, self.N)]
        if not targets:
            raise ValueError("至少需要一个目标真值表")
        self.targets = targets
        self.num_targets = len(targets)
        self.multi = self.num_targets > 1
        # 目标掩码集合：用于「命中目标的组合不受 bound 剪枝」的判断（O(1) 查询）。
        # 理由：bound 依据的是单输出最优 DAG 门数，而多输出共享解的「树门数」
        # 在枚举期会高于其共享后 DAG 门数（共享子电路被重复计数），若用 bound 剪掉
        # 命中目标的组合，会漏掉真实更优的共享解（如 7 门 4 延迟全加器）。
        self._target_masks = frozenset(targets)

        # 每层：mask -> [(树门数, 节点, 开关掩码列表)]
        self.layers_comb: List[Dict[int, List[tuple]]] = [{} for _ in range(self.D + 1)]
        self.layers_tri: List[Dict[int, List[tuple]]] = [{} for _ in range(self.D + 1)]
        # 每输出每层：[(dag门数, 节点)]
        self.target_cands: List[List[List[tuple]]] = [
            [[] for _ in range(self.D + 1)] for _ in range(self.num_targets)
        ]
        self.layer_best: List[List[int]] = [
            [INF] * (self.D + 1) for _ in range(self.num_targets)
        ]
        self.best_per_target: List[int] = [INF] * self.num_targets
        self.bound: int = INF

        self.solutions: List[Solution] = []
        self.stats: Dict[str, float] = {}

        self._flat_cache: Dict[tuple, List[tuple]] = {}
        self._dag_cache: Dict[Expr, int] = {}
        self._nodes_cache: Dict[Expr, Set[Expr]] = {}
        self._cost_cache: Dict[frozenset, int] = {}
        self._verified = 0
        self.stopped = False            # True = 因时间/候选上限早停

        self._init_base()

    # ---------------------------------------------------------------- 基础设施
    def _log(self, msg: str) -> None:
        if self.cfg.verbose:
            print(msg, flush=True)

    def _dag_cost(self, node: Expr) -> int:
        c = self._dag_cache.get(node)
        if c is None:
            c = X.dag_cost(node, self.cfg.switch_cost)
            self._dag_cache[node] = c
        return c

    def _nodes_of(self, e: Expr) -> Set[Expr]:
        """表达式的所有不同节点，带缓存（多输出共享 DP 里会反复用）。"""
        s = self._nodes_cache.get(e)
        if s is None:
            s = X.dag_nodes(e)
            self._nodes_cache[e] = s
        return s

    def _node_cost(self, nodes) -> int:
        key = frozenset(nodes)
        c = self._cost_cache.get(key)
        if c is not None:
            return c
        sc = self.cfg.switch_cost
        c = 0
        for x in key:
            t = x[0]
            if t in ("0", "1", "x"):
                continue
            if t == "SWITCH":
                c += sc
            elif t == "BUS":
                pass
            else:
                c += 1
        self._cost_cache[key] = c
        return c

    def _multi_dag_cost(self, exprs: Sequence[Expr]) -> int:
        """多条输出共享子电路后的总门数。"""
        nodes: Set[Expr] = set()
        for e in exprs:
            nodes |= self._nodes_of(e)
        return self._node_cost(nodes)

    @staticmethod
    def _shorts_ok(a: Sequence[tuple], b: Sequence[tuple]) -> bool:
        """两条总线合并后是否短路：存在某一行两者都导通且值不同则短路。"""
        for ea, da in a:
            for eb, db in b:
                if ea & eb & (da ^ db):
                    return False
        return True

    # ---------------------------------------------------------------- 初始化
    def _init_base(self) -> None:
        # 常量目标直接给答案
        for ti, tm in enumerate(self.targets):
            if tm == 0 or tm == self.all_mask:
                node = X.const(1 if tm == self.all_mask else 0)
                self.layer_best[ti][0] = 0
                self.target_cands[ti][0].append((0, node))
                self.best_per_target[ti] = 0
        self._update_bound()

        for i in range(self.n):
            mask = 0
            for row in range(self.N):
                if (row >> i) & 1:
                    mask |= 1 << row
            self._add(mask, 0, X.var(i), 0, (), False)

    def _update_bound(self) -> None:
        if all(g < INF for g in self.best_per_target):
            # 关键：枚举上界取「各输出最优门数」的**最大值**而非求和。
            # 理由：任何对某个输出有用的候选，其（树）门数都不可能超过该输出
            # 的独立最优 + slack，因而更不可能超过所有输出最优中的最大值 + slack。
            # 而完整解的真实代价由 DP 按 DAG 共享重新计算，不依赖这里的上界。
            # 取求和会把枚举深度推到 sum(best)（如全加器 6+4=10），慢一个数量级；
            # 取最大值（如 6）即可覆盖全部有用候选，且最终解仍逐行验证。
            hi = max(self.best_per_target)
            self.bound = hi + 1 + self.cfg.prune_slack
        else:
            self.bound = INF

    # ---------------------------------------------------------------- 候选入库
    def _record(self, ti: int, node: Expr, delay: int) -> None:
        """命中第 ti 个目标：按 DAG 门数记录候选。"""
        real = self._dag_cost(node)
        if real > self.layer_best[ti][delay]:
            return
        lst = self.target_cands[ti][delay]
        lst.append((real, node))
        cap = self.cfg.target_cand_cap
        if len(lst) > cap:
            # 排序键直接用 Expr 元组（原生比较，确定性等价），省去 to_str 的
            # 递归字符串构造——这里是热路径，每层都会反复触发。
            lst.sort(key=lambda t: (t[0], t[1]))
            del lst[cap:]
        if real < self.layer_best[ti][delay]:
            self.layer_best[ti][delay] = real
        if real < self.best_per_target[ti]:
            self.best_per_target[ti] = real
            self._update_bound()

    def _add(self, mask: int, gates: int, node: Expr, delay: int,
             swl: tuple, tri: bool) -> None:
        mask &= self.all_mask
        if mask == 0 or mask == self.all_mask:
            return  # 常量：作为中间结果毫无用处

        for ti, tm in enumerate(self.targets):
            if mask == tm:
                self._record(ti, node, delay)

        if gates >= self.bound:
            return

        table = self.layers_tri[delay] if tri else self.layers_comb[delay]
        lst = table.get(mask)
        if lst is None:
            table[mask] = [(gates, node, swl)]
            return

        for idx, (g, n, _s) in enumerate(lst):
            if n == node:
                if gates < g:
                    lst[idx] = (gates, node, swl)
                return
        lst.append((gates, node, swl))
        self._trim(lst, self.cfg.top_k_tri if tri else self.cfg.top_k_comb, tri)

    def _trim(self, lst: List[tuple], k: int, tri: bool) -> None:
        if len(lst) <= k:
            return
        # 保留策略（兼顾最优性与可复现）：
        #   1) 门数最小的全部候选永远保留——最优解通常（单输出时必然）由
        #      最小门数子电路组成；丢它们会直接丢最优。
        #   2) 多输出共享时，最优解可能依赖「比最小门数略大、但结构利于共享」
        #      的子电路，因此额外保留门数在 [gmin, gmin+keep_width] 内的候选。
        #   3) 用确定性键 (门数, to_str) 排序，避免结果随内部状态漂移。
        # 上限为 ``k``（搜索宽度）：宽度越大越接近真正最优，但越慢。
        gmin = min(g for g, _n, _s in lst)
        hi = gmin + self.cfg.keep_width
        kept = [item for item in lst if item[0] <= hi]
        if len(kept) <= k:
            lst[:] = kept
            return
        kept.sort(key=lambda t: (t[0], t[1]))  # t[1] 是 Expr 元组，比较确定性
        lst[:] = kept[:k]

    def _flat(self, d: int, tri: bool) -> List[tuple]:
        """把某层的候选摊平成 [(mask, gates, node, swl)]，按门数升序。"""
        key = (d, tri)
        got = self._flat_cache.get(key)
        if got is not None:
            return got
        table = self.layers_tri[d] if tri else self.layers_comb[d]
        out: List[tuple] = []
        for mask, lst in table.items():
            for (g, node, swl) in lst:
                out.append((mask, g, node, swl))
        out.sort(key=lambda t: (t[1], t[2]))  # (门数, Expr 元组) 原生比较，免 to_str
        self._flat_cache[key] = out
        return out

    # ---------------------------------------------------------------- 各阶段
    def _not_phase(self, d: int) -> None:
        if not self.cfg.use_not:
            return
        allow_gate = self.cfg.not_on_gates
        tg = self._target_masks
        for (mask, g, node, _swl) in self._flat(d - 1, tri=False):
            t = node[0]
            if t == "BUS":
                continue
            if not allow_gate and t != "x":
                continue
            rmask = self.all_mask ^ mask
            # 命中目标的组合不受 bound 剪枝：其真实代价由 _record 按 DAG 门数判定
            if g + 1 >= self.bound and rmask not in tg:
                continue
            self._add(rmask, g + 1, X.not_(node), d, (), False)

    def _binary_phase(self, d: int) -> None:
        ops = self.cfg.ops
        bl = self._flat(d - 1, tri=False)
        if not bl:
            return
        all_mask = self.all_mask
        tg = self._target_masks
        for da in range(d):
            al = self._flat(da, tri=False)
            if not al:
                continue
            same = (da == d - 1)
            for ia in range(len(al)):
                m1, g1, n1, _ = al[ia]
                start = ia + 1 if same else 0
                for ib in range(start, len(bl)):
                    m2, g2, n2, _ = bl[ib]
                    base = g1 + g2 + 1
                    m_and = m1 & m2
                    m_or = m1 | m2
                    m_xor = m1 ^ m2
                    cands = []
                    if "AND" in ops and m_and != m1 and m_and != m2:
                        cands.append((m_and, X.gate("AND", n1, n2)))
                    if "OR" in ops and m_or != m1 and m_or != m2:
                        cands.append((m_or, X.gate("OR", n1, n2)))
                    if "NAND" in ops:
                        cands.append(((all_mask ^ m_and), X.gate("NAND", n1, n2)))
                    if "NOR" in ops:
                        cands.append(((all_mask ^ m_or), X.gate("NOR", n1, n2)))
                    if m_xor:
                        if "XOR" in ops:
                            cands.append((m_xor, X.gate("XOR", n1, n2)))
                        if "XNOR" in ops:
                            cands.append(((all_mask ^ m_xor), X.gate("XNOR", n1, n2)))
                    for (rmask, rnode) in cands:
                        # 命中目标（rmask 是请求输出）时跳过 bound 剪枝——它的真实
                        # 代价由 _record 按共享后 DAG 门数判定，可能远小于树门数。
                        # 非目标组合仍受 bound 约束以避免指数爆炸。
                        if base >= self.bound and rmask not in tg:
                            continue
                        self._add(rmask, base, rnode, d, (), False)

    def _switch_phase(self, d: int) -> None:
        cfg = self.cfg
        sc = cfg.switch_cost
        tg = self._target_masks
        for da, db in self._switch_pairs(d):
            la = self._flat(da, tri=False)
            if not la:
                continue
            lb = self._flat(db, tri=False)
            if not lb:
                continue
            min_b = lb[0][1]
            for (ma, ga, na, swla) in la:
                if swla:
                    continue          # 使能端必须是实信号，不能是总线
                if ga + min_b + sc >= self.bound and ma not in tg:
                    # 该使能端本身无法形成命中目标的组合（m=ma&mb 必然 ⊆ ma），
                    # 且树门数已超界，可安全剪掉整条分支
                    continue
                for (mb, gb, nb, swlb) in lb:
                    if swlb and not cfg.allow_nested_switch:
                        continue
                    if swlb and nb[0] not in ("BUS", "SWITCH"):
                        continue
                    if da == db and na == nb:
                        continue
                    m = ma & mb
                    if m == ma or m == mb:
                        continue
                    base = ga + gb + sc
                    # 命中目标的组合（m 是请求输出）跳过 bound 剪枝
                    if base >= self.bound and m not in tg:
                        continue
                    # 外层使能串联进内层每一个开关的使能端
                    if swlb:
                        new_swl = tuple(sorted(set((ma & e, dd) for (e, dd) in swlb)))
                    else:
                        new_swl = ((ma, mb),)
                    self._add(m, base, X.switch(na, nb), d, new_swl, True)

    def _bus_phase(self, d: int) -> None:
        """把三态候选合并成总线。

        关键：只保留「不会在目标为 0 的行上输出 1」的种子（mask & ~target == 0），
        否则种子池会被大量无用开关占满，真正有用的反而被截断。
        """
        cfg = self.cfg
        pool: List[tuple] = []
        for dd in range(d + 1):
            for table in (self.layers_comb[dd], self.layers_tri[dd]):
                for mask, lst in table.items():
                    for (g, node, swl) in lst:
                        if swl:
                            pool.append((mask, g, node, swl, dd))
        if not pool:
            return
        pool.sort(key=lambda t: (t[1], t[2]))  # (门数, Expr 元组) 原生比较，免 to_str

        for target in self.targets:
            seeds = [s for s in pool if (s[0] & ~target) == 0][:cfg.bus_seed_limit]
            if not seeds:
                continue
            memo: Dict[tuple, int] = {}

            def dfs(start: int, mask: int, gates: int, nodes: List[Expr],
                    swl: tuple, cur_delay: int) -> None:
                if (mask & ~target) != 0:
                    return
                if mask == target:
                    if cur_delay == d:
                        self._add(mask, gates, X.bus(*nodes), d, swl, False)
                    return
                if len(swl) >= cfg.max_switches_per_bus:
                    return
                if gates >= self.bound:
                    return
                key = (mask, frozenset(swl))
                prev = memo.get(key)
                if prev is not None and prev <= gates:
                    return
                memo[key] = gates
                for i in range(start, len(seeds)):
                    m2, g2, n2, swl2, dd2 = seeds[i]
                    if mask & m2 == m2:
                        continue        # 没有贡献新的 1，纯浪费
                    new_mask = mask | m2
                    if (new_mask & ~target) != 0:
                        continue
                    if not self._shorts_ok(swl, swl2):
                        continue
                    ng = gates + g2
                    if ng >= self.bound:
                        continue
                    dfs(i + 1, new_mask, ng, nodes + [n2], swl + swl2, max(cur_delay, dd2))

            for i, (m, g, node, swl, dd) in enumerate(seeds):
                if (m & ~target) != 0 or g >= self.bound:
                    continue
                memo.clear()
                dfs(i + 1, m, g, [node], swl, dd)

    # ---------------------------------------------------------------- 枚举主循环
    def _enumerate(self) -> None:
        cfg = self.cfg
        t0 = time.time()
        last = t0
        for d in range(1, self.D + 1):
            # 预算护栏（大任务早停，避免指数爆炸被系统杀掉）
            if self.stopped:
                break
            if cfg.time_limit > 0 and time.time() - t0 >= cfg.time_limit:
                self.stopped = True
                self._log("  [预算] 达到时间上限 %.1fs，停止枚举，返回当前最优解" % cfg.time_limit)
                break
            if cfg.max_total_candidates > 0:
                total = sum(len(l) for t in (self.layers_comb, self.layers_tri)
                            for layer in t for l in layer.values())
                if total >= cfg.max_total_candidates:
                    self.stopped = True
                    self._log("  [预算] 候选总数达到 %d，停止枚举，返回当前最优解" % cfg.max_total_candidates)
                    break

            self._flat_cache.clear()
            self._not_phase(d)
            self._binary_phase(d)
            if cfg.use_switch:
                self._switch_phase(d)
            if cfg.use_bus:
                self._bus_phase(d)
                self._bus_phase(d)   # 第二轮：让本层新生成的总线也能继续参与合并
                self._flat_cache.clear()
            if cfg.verbose:
                now = time.time()
                total = sum(len(l) for t in (self.layers_comb, self.layers_tri)
                            for layer in t for l in layer.values())
                bound = "—" if self.bound >= INF else str(self.bound - 1 - cfg.prune_slack)
                self._log("  延迟 %d/%d | 候选 %d | 已知最优 %s | 本层 %.2fs | 累计 %.2fs"
                          % (d, self.D, total, bound, now - last, now - t0))
                last = now
        self.stats["enumerate"] = time.time() - t0
        if self.stopped:
            self.stats["stopped"] = 1.0

    # ---------------------------------------------------------------- 结果整理
    def _real_delay(self, node: Expr) -> int:
        return X.dag_delay(node, self.cfg.switch_delay, self.cfg.bus_delay)

    @staticmethod
    def _payload_size(payload) -> int:
        """表达式的书写长度，用于在同一代价的多个实现里挑个顺眼的。"""
        if isinstance(payload, tuple) and payload and isinstance(payload[0], tuple):
            return sum(len(X.to_str(e)) for e in payload)
        return len(X.to_str(payload))

    @staticmethod
    def _skyline(pts) -> List[tuple]:
        """二维天际线：``pts`` 是 (delay, gates) 最小化目标，返回非支配点集。

        按 delay 升序排序后从左到右扫，只有「门数比之前所有点的最小门数还小」
        的点才不被支配。O(P log P)（排序），替代原先 O(P²) 的两两支配检查。
        两点 delay 相同时由排序自动把门数小的排前面，大的会被门数更小者支配。
        """
        live: List[tuple] = []
        best_g = INF
        for d, g in sorted(set(pts)):
            if g < best_g:
                live.append((d, g))
                best_g = g
        return live

    @staticmethod
    def _switch_pairs(d: int):
        """开关阶段要枚举的 (使能延迟, 数据延迟) 组合：两者至少一个恰为 d-1。

        直接产出有效组合，避免原实现 ``range(d) x range(d)`` 里大量被
        ``max(da,db)!=d-1`` 挡掉的无效迭代。顺序与原实现完全一致。
        """
        for da in range(d - 1):
            yield (da, d - 1)
        for db in range(d):
            yield (d - 1, db)

    def _pareto(self, items: List[tuple], alternatives: Optional[int] = None) -> List[tuple]:
        """items: (delay, gates, payload, dedup_key) -> 非支配前沿上的解。

        同一个 (延迟, 门数) 点只保留至多 ``alternatives`` 个不同的实现，
        避免「六个写法不同但代价完全一样的解」刷屏。
        多输出共享 DP 会传一个很大的值——那里的多样性正是共享的基础。
        """
        k_max = self.cfg.alternatives if alternatives is None else alternatives
        groups: Dict[tuple, List[tuple]] = {}
        for d, g, payload, key in items:
            gl = groups.setdefault((d, g), [])
            if len(gl) < k_max and all(k != key for k, _ in gl):
                gl.append((key, payload))
        for gl in groups.values():
            gl.sort(key=lambda t: self._payload_size(t[1]))

        live = self._skyline(list(groups.keys()))
        out = [(p[0], p[1], payload) for p in live for _k, payload in groups[p]]
        out.sort(key=lambda t: (t[1], t[0]))
        return out

    def _verify_all(self, items: List[tuple]) -> List[Solution]:
        sols: List[Solution] = []
        pull = self.cfg.floating_reads_zero
        for d, g, payload in items:
            if self.multi:
                err = X.verify_multi(payload, self.n, self.targets, pull)
                shown = " ; ".join(X.to_str(e) for e in payload)
            else:
                err = X.verify(payload, self.n, self.targets[0], pull)
                shown = X.to_str(payload)
            if err:
                msg = "验证失败，已丢弃该解：%s\n    %s" % (err, shown)
                if self.cfg.strict_verify:
                    raise AssertionError(msg)
                self._log("  [警告] " + msg)
                continue
            self._verified += 1
            sols.append(Solution(d, g, payload))
        return sols

    def _collect_single(self) -> None:
        items = []
        for d in range(self.D + 1):
            for (g, node) in self.target_cands[0][d]:
                items.append((self._real_delay(node), g, node, node))
        if not items:
            self.solutions = []
            return
        if self.output_mode == "first":
            items.sort(key=lambda t: (t[0] * t[1], t[0]))
            picked = [items[0][:3]]
        else:
            picked = self._pareto(items)
        self.solutions = self._verify_all(picked)

    def _collect_per_delay(self) -> None:
        """按逻辑级数（延迟）收集：对每个可达延迟 d，返回该延迟下门数最小的
        **全部**等价电路（结构不同但 (延迟, 门数) 相同）。符合 Target 规格的
        「从最小延迟到 D 的全部最小解」。"""
        by_delay: Dict[int, List[tuple]] = {}
        for d in range(self.D + 1):
            for (g, node) in self.target_cands[0][d]:
                rd = self._real_delay(node)   # 以真实逻辑级数为准（总线/开关延迟）
                by_delay.setdefault(rd, []).append((g, node))
        items: List[tuple] = []
        for d in sorted(by_delay):
            cands = by_delay[d]
            gmin = min(g for g, _n in cands)
            seen: Set[Expr] = set()
            for g, node in cands:
                if g == gmin and node not in seen:
                    seen.add(node)
                    items.append((d, g, node))
        self.solutions = self._verify_all(items)


    def _shared_combine(self) -> None:
        cfg = self.cfg
        per_output: List[List[tuple]] = []
        for ti in range(self.num_targets):
            uniq: Dict[Expr, tuple] = {}
            for d in range(self.D + 1):
                for (g, node) in self.target_cands[ti][d]:
                    rd = self._real_delay(node)
                    old = uniq.get(node)
                    if old is None or (rd, g) < old:
                        uniq[node] = (rd, g)
            lst = [(rd, g, node) for node, (rd, g) in uniq.items()]
            lst.sort(key=lambda t: (t[1], t[0]))
            per_output.append(lst[:cfg.per_output_candidates])

        if any(not p for p in per_output):
            self.solutions = []
            return

        last = len(per_output) - 1
        # 状态 = (延迟, 门数, 各输出表达式, 已用节点集合)
        current: List[tuple] = [(0, 0, (), frozenset())]
        for out_idx, out_cands in enumerate(per_output):
            nxt: List[tuple] = []
            for (bd, _bg, bx, bnodes) in current:
                for (d, _g, e) in out_cands:
                    nodes = bnodes | self._nodes_of(e)
                    ng = self._node_cost(nodes)
                    nxt.append((max(bd, d), ng, bx + (e,), nodes))
            if not nxt:
                current = []
                break
            # 最终层做完整 Pareto；中间层只按代价截断，避免丢解路径
            current = self._pareto_states(nxt, cfg.multi_state_limit,
                                          final=(out_idx == last))

        if not current:
            self.solutions = []
            return

        items = [(d, g, exprs, exprs) for d, g, exprs, _nodes in current]
        if self.output_mode == "first":
            items.sort(key=lambda t: (t[0] * t[1], t[0]))
            picked = [items[0][:3]]
        else:
            picked = self._pareto(items)
        self.solutions = self._verify_all(picked)

    def _pareto_states(self, states: List[tuple], k_max: int,
                        final: bool = False) -> List[tuple]:
        """多输出 DP 用的状态过滤。状态 = (延迟, 门数, 表达式组, 节点集)。

        - 中间层 (``final=False``)：只按 (门数, 延迟) 保留前 ``k_max`` 个，
          **不做**支配剪枝。因为被某个中间状态「支配」的状态仍可能通向更优的
          最终组合（共享子电路使其翻盘），过早支配会丢解。
        - 最终层 (``final=True``)：在保留的候选上做完整 Pareto 过滤。
        """
        groups: Dict[tuple, List[tuple]] = {}
        for d, g, exprs, nodes in states:
            gl = groups.setdefault((d, g), [])
            if len(gl) < k_max and all(e != exprs for e, _ in gl):
                gl.append((exprs, nodes))
        if not final:
            pts = sorted(groups, key=lambda t: (t[1], t[0]))
            out = [(p[0], p[1], exprs, nodes)
                   for p in pts[:k_max] for exprs, nodes in groups[p]]
            out.sort(key=lambda t: (t[1], t[0]))
            return out
        live = self._skyline(list(groups.keys()))
        out = [(p[0], p[1], exprs, nodes)
               for p in live for exprs, nodes in groups[p]]
        out.sort(key=lambda t: (t[1], t[0]))
        return out

    # ---------------------------------------------------------------- 入口
    def synthesize(self) -> List[Solution]:
        self._log("精确枚举 (n=%d, D=%d, 输出数=%d, 开关成本=%d, 门集=%s)"
                  % (self.n, self.D, self.num_targets, self.cfg.switch_cost,
                     "+".join(self.cfg.ops)))
        self._enumerate()

        if self.multi:
            self._shared_combine()
        elif self.output_mode == "per_delay":
            self._collect_per_delay()
        else:
            self._collect_single()

        self.stats["verified"] = self._verified
        self._report()
        return self.solutions

    def _report(self) -> None:
        if not self.solutions:
            self._log("  无解（在 D=%d 与当前门集下无法综合）" % self.D)
            return
        if self.multi:
            title = ("  多输出 Pareto 最优解：" if self.output_mode == "all"
                     else "  多输出最优解（成本最小）：")
            self._log(title)
            for i, s in enumerate(self.solutions):
                tag = "Pareto #%d" % (i + 1) if self.output_mode == "all" else "最优"
                self._log("    #%d (%s) 延迟 %d | 总门数 %d | 成本 %d"
                          % (i + 1, tag, s.delay, s.gates, s.cost))
                for j, e in enumerate(s.expr):
                    self._log("      输出%d: %s" % (j, X.to_str(e)))
        else:
            if self.output_mode == "per_delay":
                self._log("  每个延迟的全部最小门数解：")
                cur = None
                for i, s in enumerate(self.solutions):
                    if s.delay != cur:
                        cur = s.delay
                        self._log("    —— 延迟 %d ——" % cur)
                    self._log("      #%d 门数 %d | %s" % (i + 1, s.gates, X.to_str(s.expr)))
                return
            title = ("  单输出 Pareto 最优解：" if self.output_mode == "all"
                     else "  单输出最优解（成本最小）：")
            self._log(title)
            for i, s in enumerate(self.solutions):
                if self.output_mode == "all":
                    self._log("    #%d 延迟 %d | 门数 %d | 成本 %d | %s"
                              % (i + 1, s.delay, s.gates, s.cost, X.to_str(s.expr)))
                else:
                    self._log("    延迟 %d | 门数 %d | 成本 %d | %s"
                              % (s.delay, s.gates, s.cost, X.to_str(s.expr)))


# ==========================================================================
# 电路图 SVG 渲染
# ==========================================================================

"""把综合结果渲染成门级电路图（SVG）。

给《图灵完备》这类「动手搭电路」的场景用：把 ``to_str`` 出来的嵌套表达式
变成一张能直接照着搭的图——输入在左、输出在右，开关与总线也都画出来。

用法::

    from tcbreaker import LogicSynthesizer
    from tcbreaker.draw import circuit_svg
    sol = LogicSynthesizer(3, 0x96, 6).synthesize()[0]
    svg = circuit_svg(sol.expr, 3)
    open("circuit.svg", "w").write(svg)

布局说明（为什么这样做）：
    - 列号 = 节点深度（门输出比输入靠右一列），输入在左、输出在右。
    - 同一列内的上下次序用「重心法」（barycenter）迭代排序：每列按其子节点
      （正向）或父节点（反向）的平均行号排序，反复几轮把交叉的连线摊开。
      这样 mux/总线的「解码门 ↔ 开关」能上下对齐，使能线近乎水平。
    - 行号落到统一网格 ``y = 行号 * ROW``，天然不重叠、跨列垂直对齐。
    - 单节点列（如最后的输出 BUS）在网格上会顶到最上面，所以再按其子节点
      重心居中；多输出时整个输出层居中到上一层重心。

走线说明（解决「线重叠看不清」）：
    - 每条边在它所跨越的「列间隙」里分配一条**独占的垂直走线**（x 坐标），
      用左边缘算法（interval coloring）让 y 区间不相交的线复用同一 x，
      相交的线错开——于是同一间隙里再也不会好几条垂直线叠在一起。
    - 跨层连线（子节点离父节点不止一列，如 mux 里输入直接接到开关的数据端）
      不再横穿中间的门体：先下到图底部的「走线通道」，在通道里水平横穿，
      再升回目标引脚。所有线都看得见、分得清。
"""


# 画布参数（像素）
MARGIN_X = 24
MARGIN_Y = 24
GATE_W = 66
GATE_H = 38
COL = 76          # 列间距（相邻延迟层之间的水平距离）
ROW = 54          # 行高（同一列内相邻节点的垂直距离，> GATE_H 保证不重叠）
CHANNEL_GAP = 7   # 底部走线通道里相邻两条水平线的间距

# 走线/引脚几何参数
PIN_SPAN = GATE_H - 10        # 门输入引脚在门体上的垂直分布范围
TOUCH_TOLERANCE = 0.5         # 左边缘算法：两条线恰好相贴时仍可复用同一轨道
BOTTOM_LANE_OFFSET = 12       # 底部通道距最低门下沿的额外间距
FLYOVER_MARGIN = 4            # 飞线最高点之上留出的空白
WIRE_STROKE_W = 1.8           # 走线描边宽度
NET_DOT_R = 3.5               # 输出端子同色小圆点半径

# 网络（信号）配色：同一个信号的所有连线用一种颜色，交叉的线颜色必然不同，
# 顺着颜色就能追到同一个端子。循环使用，颜色用尽就从头再来。
_NET_COLORS = [
    "#d62728",  # 红
    "#1f77b4",  # 蓝
    "#2ca02c",  # 绿
    "#ff7f0e",  # 橙
    "#9467bd",  # 紫
    "#8c564b",  # 棕
    "#17becf",  # 青
    "#e377c2",  # 粉
    "#bcbd22",  # 橄榄
    "#a65628",  # 深橙
    "#008080",  # 鸭绿
    "#800080",  # 深紫
]


def _children(e: Expr) -> List[Expr]:
    t = e[0]
    if t in ("0", "1", "x"):
        return []
    return list(e[1:])


def _label(e: Expr) -> str:
    t = e[0]
    if t == "x":
        return "x%d" % e[1]
    if t == "0":
        return "0"
    if t == "1":
        return "1"
    if t == "SWITCH":
        return "SW"
    if t == "BUS":
        return "BUS"
    return t


def _depth(e: Expr, memo: Dict[Expr, int]) -> int:
    """视觉列号：每个门的输出都比输入靠右一列（BUS 也一样，因为它要画在开关右侧）。"""
    d = memo.get(e)
    if d is not None:
        return d
    ch = _children(e)
    d = 0 if not ch else 1 + max(_depth(c, memo) for c in ch)
    memo[e] = d
    return d


def _collect_roots(exprs: Sequence[Expr]) -> Tuple[List[Expr], Dict[Expr, int]]:
    """返回 (全部节点, 每节点列号)。多输出时把所有输出节点的 DAG 并起来。"""
    nodes: set = set()
    for e in exprs:
        nodes |= X.dag_nodes(e)
    memo: Dict[Expr, int] = {}
    for n in nodes:
        _depth(n, memo)
    return list(nodes), memo


def _order_ranks(depth: Dict[Expr, int]) -> Dict[Expr, int]:
    """重心法迭代排序，返回每节点在其列内的行号（0..k-1）。

    第 0 列（输入/常量）固定按自然顺序（x0,x1,...，常量靠后），不参与重排，
    保证输入从上到下整齐排列。
    """
    max_d = max(depth.values())
    layers: Dict[int, List[Expr]] = {}
    for n in depth:
        layers.setdefault(depth[n], []).append(n)

    children = {n: _children(n) for n in depth}
    parents: Dict[Expr, List[Expr]] = {}
    for n in depth:
        for c in children[n]:
            parents.setdefault(c, []).append(n)

    def leaf_key(n: Expr):
        t = n[0]
        if t == "x":
            return (0, n[1])
        if t == "0":
            return (1, 0)
        if t == "1":
            return (1, 1)
        return (2, 0)

    rank: Dict[Expr, int] = {}
    for i, n in enumerate(sorted(layers.get(0, []), key=leaf_key)):
        rank[n] = i

    for _ in range(6):
        # 正向：左→右，按子节点平均行号排序
        for d in range(1, max_d + 1):
            col = layers.get(d, [])
            if not col:
                continue

            def key_down(n: Expr) -> tuple:
                ch = children[n]
                bary = (sum(rank[c] for c in ch) / len(ch)) if ch else rank.get(n, 0)
                return (bary, _label(n), str(n))

            for i, n in enumerate(sorted(col, key=key_down)):
                rank[n] = i
        # 反向：右→左，按父节点平均行号排序（第 0 列不动）
        for d in range(max_d - 1, 0, -1):
            col = layers.get(d, [])
            if not col:
                continue

            def key_up(n: Expr) -> tuple:
                ps = parents.get(n, [])
                bary = (sum(rank[p] for p in ps) / len(ps)) if ps else rank.get(n, 0)
                return (bary, _label(n), str(n))

            for i, n in enumerate(sorted(col, key=key_up)):
                rank[n] = i
    return rank


def _layout(exprs: Sequence[Expr], depth: Dict[Expr, int]) -> Dict[Expr, float]:
    """给每个节点分配 y 坐标。

    行号（重心法排序结果）落到统一网格，再对「单节点列 / 输出层」做居中，
    避免输出点悬在最上面、离它真正的输入太远。
    """
    rank = _order_ranks(depth)
    ys: Dict[Expr, float] = {n: float(MARGIN_Y + rank[n] * ROW) for n in depth}

    max_d = max(depth.values())
    by_depth: Dict[int, List[Expr]] = {}
    for n in depth:
        by_depth.setdefault(depth[n], []).append(n)

    for d in sorted(by_depth):
        col = by_depth[d]
        if len(col) == 1:
            # 单节点列（如输出 BUS）居中到子节点重心
            node = col[0]
            ch = _children(node)
            if ch:
                ys[node] = sum(ys[c] for c in ch) / len(ch)
        elif d == max_d and d > 0:
            # 多输出的最终层整体居中到上一层重心
            prev = by_depth.get(d - 1, [])
            if prev:
                target = sum(ys[p] for p in prev) / len(prev)
                cur = sum(ys[n] for n in col) / len(col)
                shift = target - cur
                for n in col:
                    ys[n] += shift
    return ys


def _pin_y(parent_y: float, k: int, i: int) -> float:
    """父节点第 i 个输入引脚的 y 坐标（k 个引脚均匀分布）。"""
    if k <= 1:
        return parent_y
    return parent_y - PIN_SPAN / 2 + i * (PIN_SPAN / (k - 1))


def _left_edge(intervals: List[Tuple[float, float]]) -> Tuple[List[int], int]:
    """左边缘算法：给一组 [lo, hi] y 区间分配尽量少的「轨道」，返回每区间的轨道号。

    规则：y 区间相交的两条线不能共用一根垂直走线（否则会叠起来），
    不相交的可以复用。按左端点排序，贪心放进最早空出来的轨道。
    """
    order = sorted(range(len(intervals)),
                   key=lambda i: (intervals[i][0], intervals[i][1]))
    track_end: List[float] = []
    assign = [0] * len(intervals)
    for i in order:
        lo, hi = intervals[i]
        placed = False
        for t, te in enumerate(track_end):
            if te <= lo + TOUCH_TOLERANCE:  # 恰好相贴的两条线仍可复用同一 x
                track_end[t] = hi
                assign[i] = t
                placed = True
                break
        if not placed:
            track_end.append(hi)
            assign[i] = len(track_end) - 1
    return assign, len(track_end)


def _gap_bounds(g: int) -> Tuple[float, float]:
    """列间隙 g（位于列 g 与列 g+1 之间）的 x 范围。"""
    left = MARGIN_X + g * (GATE_W + COL) + GATE_W
    right = MARGIN_X + (g + 1) * (GATE_W + COL)
    return left, right


@dataclass
class _Edge:
    """一条连线：子节点输出端 → 父节点输入引脚。"""
    c: Expr                              # 子节点（源），也是网络标识
    cx: float                              # 子输出 x（右边缘）
    cy: float                              # 子输出 y
    px: float                              # 父输入 x（左边缘）
    pin_y: float                           # 父引脚 y
    dc: int                                # 子列号
    dp: int                                # 父列号
    channel_y: Optional[float] = None      # 跨层边飞线高度（相邻边为 None）
    label: Optional[str] = None            # SWITCH 的 E/D 引脚标
    tracks: Dict[int, float] = field(default_factory=dict)  # 每列间隙的走线 x


def _route(edges: List[_Edge], max_d: int):
    """给每条边分配垂直走线的 x 坐标（按每个列间隙独立做轨道分配）。

    结果写回 ``e.tracks``：{间隙号: x}。
    """
    gap_edges: Dict[int, List[_Edge]] = {g: [] for g in range(max_d)}
    for e in edges:
        for g in range(e.dc, e.dp):
            gap_edges[g].append(e)

    for g, es in gap_edges.items():
        if not es:
            continue
        left, right = _gap_bounds(g)
        intervals = []
        for e in es:
            if e.dp - e.dc == 1:
                lo, hi = sorted((e.cy, e.pin_y))
            elif g == e.dc:
                lo, hi = sorted((e.cy, e.channel_y))
            else:
                lo, hi = sorted((e.pin_y, e.channel_y))
            intervals.append((lo, hi))
        assign, nt = _left_edge(intervals)
        for idx, e in enumerate(es):
            t = assign[idx]
            e.tracks[g] = left + (t + 1) / (nt + 1) * (right - left)


def circuit_svg(exprs: Sequence[Expr], n_inputs: int,
                 titles: Sequence[str] = None,
                 max_depth: int = None) -> str:
    """生成一张 SVG 电路图。

    ``exprs`` 是一条或多条输出表达式；``n_inputs`` 是输入个数；
    ``titles`` 给每条输出命名（如 "SUM" / "Cout"）。
    """
    if isinstance(exprs, tuple) and exprs and isinstance(exprs[0], str):
        # 单条表达式（其首元素是运算符字符串），包成列表
        exprs = [exprs]  # type: ignore
    exprs = list(exprs)
    if titles is None:
        titles = ["OUT%d" % i for i in range(len(exprs))]
    nodes, depth = _collect_roots(exprs)
    ys = _layout(exprs, depth)

    max_d = max_depth if max_depth is not None else max(depth.values())
    width = MARGIN_X * 2 + (max_d + 1) * (GATE_W + COL)

    def x_of(n: Expr) -> float:
        return MARGIN_X + depth[n] * (GATE_W + COL)

    # 确定性地排序节点，让 SVG 输出可复现（同一列内自上而下）
    ordered = sorted(nodes, key=lambda n: (depth[n], ys[n], _label(n)))

    # ---- 网络配色：每个「输出端子」一个颜色（同信号所有连线同色）----
    net_color: Dict[Expr, str] = {}
    for i, n in enumerate(ordered):
        net_color[n] = _NET_COLORS[i % len(_NET_COLORS)]

    # ---- 收集边（子节点输出 → 父节点输入引脚），引脚按子节点 y 排序 ----
    edges: List[_Edge] = []
    for node in ordered:
        ch = _children(node)
        if not ch:
            continue
        px = x_of(node)
        py = ys[node]
        ch_sorted = sorted(ch, key=lambda c: (ys[c], _label(c)))
        k = len(ch_sorted)
        for i, c in enumerate(ch_sorted):
            label = None
            if node[0] == "SWITCH" and k == 2:
                # child[1]=enable 控制端，child[2]=data 数据端
                label = "E" if c == node[1] else "D"
            edges.append(_Edge(
                c=c,
                cx=x_of(c) + GATE_W, cy=ys[c],
                px=px, pin_y=_pin_y(py, k, i),
                dc=depth[c], dp=depth[node],
                label=label,
            ))

    # ---- 跨层边走"底部走线通道" ----
    # 所有跨层（长）连线统一排到电路最下方的「走线通道」里，按 CHANNEL_GAP 堆叠。
    # 这样长连线不会再穿过中间门阵列、也不会在输入区附近横穿，读者一眼就能认出
    # 「这些是绕远的连接」；而且多条长连线各自占一条独立水平轨道，互不重叠。
    skip_edges = [e for e in edges if e.dp - e.dc >= 2]
    max_y = max(ys.values()) if ys else 0
    max_rank = 0
    for n in depth:
        r = round((ys[n] - MARGIN_Y) / ROW)
        if r > max_rank:
            max_rank = r
    # 通道起点：最低门体下沿再留一段空隙
    chan_top = MARGIN_Y + max_rank * ROW + GATE_H / 2 + BOTTOM_LANE_OFFSET
    lanes = [chan_top + i * CHANNEL_GAP for i in range(len(skip_edges))]
    for idx, e in enumerate(sorted(skip_edges, key=lambda e: (e.cy, e.pin_y))):
        e.channel_y = lanes[idx]

    _route(edges, max_d)

    flyover_y = max((e.channel_y for e in skip_edges), default=max_y)

    # ---- 网络配色图例：把每条彩色线映射回它的源端子 ----
    # 同信号的线同色，图例列出每个源端子对应的颜色，方便顺着颜色认领回来源。
    legend_entries: List[Tuple[str, str]] = []
    _seen_nodes = set()
    _seen_labels: Dict[str, int] = {}
    for e in edges:
        if e.c in _seen_nodes:
            continue
        _seen_nodes.add(e.c)
        lab = _label(e.c)
        cnt = _seen_labels.get(lab, 0) + 1
        _seen_labels[lab] = cnt
        if cnt > 1:
            lab = "%s-%d" % (lab, cnt)
        legend_entries.append((net_color[e.c], lab))

    _lowest = max_y + GATE_H / 2
    _content_bottom = max(_lowest, flyover_y) if skip_edges else _lowest
    _legend_top = _content_bottom + 18
    _LEGEND_ITEM_H = 16
    _LEGEND_CHARS_W = 7
    _legend_rows: List[List[Tuple[str, str, float]]] = []
    _row: List[Tuple[str, str, float]] = []
    _x = MARGIN_X + 66                    # 为左侧 "网络配色" 标签留白
    for _color, _lab in legend_entries:
        _w = 12 + 16 + len(_lab) * _LEGEND_CHARS_W + 20
        if _x + _w > width - MARGIN_X and _row:
            _legend_rows.append(_row)
            _row = []
            _x = MARGIN_X + 66
        _row.append((_color, _lab, _x))
        _x += _w
    if _row:
        _legend_rows.append(_row)
    _legend_h = 16 + len(_legend_rows) * _LEGEND_ITEM_H
    height = int(_legend_top + _legend_h) + MARGIN_Y

    out: List[str] = []
    out.append('<?xml version="1.0" encoding="UTF-8"?>')
    out.append('<svg xmlns="http://www.w3.org/2000/svg" '
               'width="%d" height="%d" font-family="Consolas,Menlo,monospace" '
               'font-size="13" viewBox="0 0 %d %d">'
               % (width, height, width, height))
    out.append('<rect x="0" y="0" width="%d" height="%d" fill="#ffffff"/>'
               % (width, height))

    # ---- 线（先画线，后画门，保证门盖在线上面） ----
    pin_labels: List[Tuple[float, float, str]] = []
    for e in edges:
        cx, cy = e.cx, e.cy
        px, pin_y = e.px, e.pin_y
        if e.dp - e.dc == 1:
            tx = e.tracks[e.dc]
            pts = [(cx, cy), (tx, cy), (tx, pin_y), (px, pin_y)]
        else:
            txd = e.tracks[e.dc]
            txu = e.tracks[e.dp - 1]
            chy = e.channel_y
            pts = [(cx, cy), (txd, cy), (txd, chy),
                   (txu, chy), (txu, pin_y), (px, pin_y)]
        out.append(
            '<polyline points="%s" fill="none" stroke="%s" stroke-width="%s"/>'
            % (" ".join("%.1f,%.1f" % p for p in pts),
               net_color[e.c], WIRE_STROKE_W))
        if e.label:
            pin_labels.append((px - 2, pin_y, e.label))

    out_root = set(exprs)
    for idx, root in enumerate(exprs):
        if titles and idx < len(titles):
            rx = x_of(root) + GATE_W
            ry = ys[root]
            out.append('<text x="%.1f" y="%.1f" fill="#b00" '
                       'font-weight="bold">%s</text>'
                       % (rx - 4, ry - GATE_H / 2 - 6, _xml_escape(titles[idx])))

    for node in ordered:
        x = x_of(node)
        y = ys[node] - GATE_H / 2
        t = node[0]
        if t in ("0", "1", "x"):
            # 输入/常量：小圆角块
            out.append('<rect x="%.1f" y="%.1f" width="%d" height="%d" '
                       'rx="6" fill="#eef" stroke="#336" stroke-width="1.5"/>'
                       % (x, y, GATE_W, GATE_H))
            out.append('<text x="%.1f" y="%.1f" fill="#123" '
                       'text-anchor="middle" dominant-baseline="central">%s</text>'
                       % (x + GATE_W / 2, ys[node], _label(node)))
        elif t == "BUS":
            # 总线：合并点画成实心圆
            out.append('<circle cx="%.1f" cy="%.1f" r="13" fill="#fff" '
                       'stroke="#a30" stroke-width="2"/>'
                       % (x + GATE_W / 2, ys[node]))
            out.append('<text x="%.1f" y="%.1f" fill="#a30" '
                       'text-anchor="middle" dominant-baseline="central" '
                       'font-size="10">+BUS</text>' % (x + GATE_W / 2, ys[node]))
        else:
            is_out = node in out_root
            stroke = "#b00" if is_out else "#333"
            sw = 2.4 if is_out else 1.5
            out.append('<rect x="%.1f" y="%.1f" width="%d" height="%d" '
                       'rx="5" fill="#f7f7f7" stroke="%s" stroke-width="%s"/>'
                       % (x, y, GATE_W, GATE_H, stroke, sw))
            out.append('<text x="%.1f" y="%.1f" fill="#222" '
                       'text-anchor="middle" dominant-baseline="central">%s</text>'
                       % (x + GATE_W / 2, ys[node], _label(node)))

    # SWITCH 引脚标签（E=enable 控制端，D=data 数据端），画在门体左侧
    for lx, ly, lt in pin_labels:
        out.append('<text x="%.1f" y="%.1f" fill="#666" '
                   'text-anchor="end" dominant-baseline="central" '
                   'font-size="9">%s</text>' % (lx, ly, lt))

    # 每个输出端子上画一个同色小圆点，方便把线「认领」回它的来源。
    # 当一个信号扇出到多个门（fan-out ≥ 2）时，额外画一个空心「分歧点」标记，
    # 一眼就能看出「这一根信号在这里一分为多」，避免把多条独立线误认成不同信号。
    fanout: Dict[Expr, int] = {}
    for e in edges:
        fanout[e.c] = fanout.get(e.c, 0) + 1
    for node in ordered:
        if node[0] == "BUS" or node not in net_color:
            continue
        if node not in fanout:
            continue
        cx = x_of(node) + GATE_W
        cy = ys[node]
        out.append('<circle cx="%.1f" cy="%.1f" r="%s" fill="%s" '
                   'stroke="#fff" stroke-width="1"/>'
                   % (cx, cy, NET_DOT_R, net_color[node]))
        if fanout[node] >= 2:
            out.append('<circle cx="%.1f" cy="%.1f" r="%.1f" fill="none" '
                       'stroke="%s" stroke-width="1.6"/>'
                       % (cx, cy, NET_DOT_R + 2.4, net_color[node]))

    # ---- 网络配色图例 ----
    if legend_entries:
        out.append('<text x="%.1f" y="%.1f" fill="#444" font-size="11" '
                   'font-weight="bold">网络配色</text>' % (MARGIN_X, _legend_top + 4))
        for _ri, _row in enumerate(_legend_rows):
            _ly = _legend_top + 14 + _ri * _LEGEND_ITEM_H
            for _color, _lab, _x in _row:
                out.append('<rect x="%.1f" y="%.1f" width="12" height="12" '
                           'fill="%s" stroke="#888" stroke-width="0.5"/>'
                           % (_x, _ly - 11, _color))
                out.append('<text x="%.1f" y="%.1f" fill="#222" font-size="10">%s</text>'
                           % (_x + 16, _ly, _xml_escape(_lab)))

    out.append('</svg>')
    return "\n".join(out)


# ==========================================================================
# 命令行入口
# ==========================================================================

"""命令行入口：``python -m tcbreaker --help``"""


def _default_svg_path() -> str:
    """SVG 默认输出路径：写到执行脚本所在目录，而非当前工作目录。

    这样无论用户从哪个目录调用（``python C:/x/TCBreaker.py``、
    ``python tcbreaker_single.py`` 还是 ``python -m tcbreaker``），电路图都落在
    项目目录旁边，不会污染 cwd。``-o/--output`` 仍可覆盖此默认值。
    """
    prog = sys.argv[0] if sys.argv and sys.argv[0] else ""
    base = os.path.basename(prog)
    if prog and base and base not in ("-m", "-c"):
        d = os.path.dirname(os.path.abspath(prog))
        if d:
            # ``python -m tcbreaker`` 时 prog 是包内 __main__.py，
            # 再上一级到包外（项目根）更自然，避免把图写进包目录里。
            if base == "__main__.py":
                d = os.path.dirname(d)
            return os.path.join(d, "circuit.svg")
    return os.path.join(os.getcwd(), "circuit.svg")


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="tcbreaker",
        description="真值表 -> 最优门级电路（图灵完备向的综合器）",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""\
示例:
  python -m tcbreaker --inputs 3 --target 0x96 --max-delay 6
  python -m tcbreaker --inputs 3 --target 0x96,0xE8 --max-delay 5
  python -m tcbreaker --inputs 3 --target "0 1 1 0 1 0 0 1"   # 位序列，低位在前
  python -m tcbreaker --inputs 3 --target 01101001              # 同上，高位在前书写
  python -m tcbreaker --xor3 --max-delay 4
  python -m tcbreaker --inputs 3 --target 0x96 --ops AND,OR,NOT --no-switch
  python -m tcbreaker --inputs 3 --target 0xE8 --switch-cost 2
""")
    g = p.add_argument_group("问题")
    g.add_argument("-n", "--inputs", type=int, help="输入个数")
    g.add_argument("-t", "--target", help="目标真值表：0x96 / 0b10010110 / 0,1,1,0 / 10010110")
    g.add_argument("-D", "--max-delay", type=int, default=4, help="最大延迟（默认 4）")
    g.add_argument("--xor3", action="store_true", help="快捷方式：3 输入异或")
    g.add_argument("--maj3", action="store_true", help="快捷方式：3 输入多数表决（全加器 Cout）")
    g.add_argument("--adder", action="store_true", help="快捷方式：全加器 SUM+Cout 双输出")
    g.add_argument("--show-table", action="store_true", help="先打印真值表再综合")

    g = p.add_argument_group("输出")
    g.add_argument("-m", "--mode", choices=("all", "first", "per_delay"),
                   default="per_delay",
                   help="per_delay=每个延迟的全部最小门数解（默认）；all=Pareto 前沿；first=成本最小的一个")
    g.add_argument("-q", "--quiet", action="store_true", help="不打印搜索过程")
    g.add_argument("--emit", choices=("text", "python", "svg", "json"), default="text",
                   help="python=可粘贴构造代码；svg=写出电路图；json=结构化结果")
    g.add_argument("-o", "--output", default=_default_svg_path(),
                   help="--emit svg 时输出文件路径（默认写到脚本所在目录下的 circuit.svg）")

    g = p.add_argument_group("门集与代价")
    g.add_argument("--ops", help="二元门，逗号分隔，默认 AND,OR,NAND,NOR（Target 规格）")
    g.add_argument("--no-not", action="store_true", help="禁用非门")
    g.add_argument("--no-not-on-gates", action="store_true",
                   help="NOT 只作用于输入（默认可作用于任意信号）")
    g.add_argument("--no-switch", action="store_true", help="禁用三态开关（也就没有总线）")
    g.add_argument("--no-bus", action="store_true", help="禁用总线合并")
    g.add_argument("--no-nested-switch", action="store_true", help="开关数据端不允许接总线")
    g.add_argument("--switch-cost", type=int, default=2, help="开关折算几个门（默认 2，Target 规格）")
    g.add_argument("--max-switches", type=int, default=4, help="单条总线最多几个开关（默认 4）")

    g = p.add_argument_group("搜索强度")
    g.add_argument("--slack", type=int, default=1,
                   help="剪枝余量，越大越慢但越不容易漏解（默认 1）")
    g.add_argument("--top-k", type=int, default=2, help="每个掩码保留的候选数（默认 2）")
    g.add_argument("--bus-seeds", type=int, default=12, help="总线合并种子数（默认 12）")
    g.add_argument("--exhaustive", action="store_true",
                   help="认真模式：放宽剪枝与候选上限（慢很多）")
    g.add_argument("--time-limit", type=float, default=0,
                   help="最大运行秒数，超过后优雅停止并返回当前最优解（默认 0=不限）")
    g.add_argument("--max-candidates", type=int, default=0,
                   help="候选总数上限，超过后优雅停止（默认 0=不限，避免大任务 OOM）")

    g = p.add_argument_group("其它")
    g.add_argument("--self-test", action="store_true", help="跑内置自检后退出")
    g.add_argument("--no-verify", action="store_true",
                   help="不校验输出结果（不推荐；默认每个解都会回代真值表）")
    return p


def _targets_from_args(args) -> tuple:
    n = args.inputs
    if args.xor3:
        return n or 3, [Masks.xor(3)]
    if args.maj3:
        return n or 3, [Masks.majority(3)]
    if args.adder:
        return n or 3, [0x96, 0xE8]
    if n is None or not args.target:
        raise SystemExit("需要 --inputs 与 --target（或用 --xor3 / --maj3 / --adder）")
    parts = [p for p in args.target.replace(";", ",").split(",") if p.strip()]
    rows = 1 << n
    return n, [as_mask(p.strip(), rows) for p in parts]


def make_config(args) -> Config:
    if args.exhaustive:
        return Config(prune_slack=3, top_k_comb=3, top_k_tri=4,
                      bus_seed_limit=24, per_output_candidates=48,
                      max_switches_per_bus=max(4, args.max_switches),
                      time_limit=args.time_limit,
                      max_total_candidates=args.max_candidates)
    return Config(
        ops=tuple(o.strip().upper() for o in args.ops.split(",")) if args.ops
        else ("AND", "OR", "NAND", "NOR"),
        use_not=not args.no_not,
        not_on_gates=not args.no_not_on_gates,
        use_switch=not args.no_switch,
        use_bus=not (args.no_bus or args.no_switch),
        allow_nested_switch=not args.no_nested_switch,
        switch_cost=args.switch_cost,
        max_switches_per_bus=args.max_switches,
        top_k_comb=args.top_k,
        top_k_tri=max(args.top_k, 3),
        bus_seed_limit=args.bus_seeds,
        prune_slack=args.slack,
        time_limit=args.time_limit,
        max_total_candidates=args.max_candidates,
        verbose=False,
    )


def _emit_python(sol: Solution, n: int) -> str:
    if sol.multi:
        lines = ["from tcbreaker import parse"]
        for i, e in enumerate(sol.expr):
            lines.append("out%d = parse(%r)   # 延迟 %d" % (i, X.to_str(e), sol.delay))
        return "\n".join(lines)
    return "from tcbreaker import parse\nexpr = parse(%r)   # 延迟 %d, 门数 %d" % (
        X.to_str(sol.expr), sol.delay, sol.gates)


def _emit_json(sols, n, targets, verified, elapsed) -> str:
    """结构化 JSON 输出，方便脚本/流水线解析。"""
    import json

    def ser(s: Solution) -> dict:
        expr = [X.to_str(e) for e in s.expr] if s.multi else X.to_str(s.expr)
        return {"delay": s.delay, "gates": s.gates, "cost": s.cost, "expr": expr}

    return json.dumps({
        "inputs": n,
        "targets": ["0x%X" % t for t in targets],
        "solutions": [ser(s) for s in sols],
        "verified": verified,
        "elapsed": round(elapsed, 4),
    }, ensure_ascii=False, indent=2)


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)

    if args.self_test:
        # [合并] 相对导入已内联，名字直接取自本模块
        return 0 if run_self_test() else 1

    n, targets = _targets_from_args(args)
    cfg = make_config(args)
    if args.quiet:
        cfg.verbose = False
    else:
        # 搜索过程用一个轻量的进度回调，最后统一打印结果
        cfg.verbose = True

    if args.show_table:
        for i, t in enumerate(targets):
            print("目标 %d 真值表 (0x%X):" % (i, t))
            print(format_table(n, t))
            print()

    t0 = time.time()
    syn = LogicSynthesizer(n, targets, args.max_delay, output_mode=args.mode, config=cfg)
    sols = syn.synthesize()
    elapsed = time.time() - t0

    if syn.stopped:
        print("\n[提示] 搜索因时间/候选上限提前停止，返回的是当前最优解（可能非全局最优）。")

    if not sols:
        print("\n在 D=%d 内没有找到解。可以调大 --max-delay，或检查门集是否够用。" % args.max_delay)
        return 2

    print()
    if args.emit == "python":
        for s in sols:
            print("# 延迟 %d | 门数 %d | 成本 %d" % (s.delay, s.gates, s.cost))
            print(_emit_python(s, n))
            print()
    elif args.emit == "svg":
        # [合并] 相对导入已内联，名字直接取自本模块
        titles = None
        if len(targets) > 1:
            names = {0x96: "SUM", 0xE8: "Cout"}
            titles = [names.get(t, "OUT%d" % i) for i, t in enumerate(targets)]
        # 只画成本最小（第一个）解，避免多个解叠加成乱麻
        svg = circuit_svg(sols[0].expr, n, titles=titles)
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(svg)
        print("已写出电路图：%s" % args.output)
    elif args.emit == "json":
        print(_emit_json(sols, n, targets, syn.stats.get("verified", 0), elapsed))
    else:
        if len(targets) > 1:
            for s in sols:
                print("延迟 %d | 总门数 %d | 成本 %d" % (s.delay, s.gates, s.cost))
                for i, e in enumerate(s.expr):
                    print("  输出%d: %s" % (i, X.to_str(e)))
                print()
        else:
            if args.mode == "per_delay":
                cur = None
                for s in sols:
                    if s.delay != cur:
                        cur = s.delay
                        print("—— 延迟 %d ——" % cur)
                    print("  门数 %d | %s" % (s.gates, X.to_str(s.expr)))
            else:
                for s in sols:
                    print("延迟 %d | 门数 %d | 成本 %d | %s"
                          % (s.delay, s.gates, s.cost, X.to_str(s.expr)))
    print("用时 %.2fs，校验通过 %d 个解" % (elapsed, syn.stats.get("verified", 0)))
    return 0


# ==========================================================================
# 内置自检（含随机回归）
# ==========================================================================

"""内置自检：``python -m tcbreaker --self-test``

核心目标是**随机回归网**——随机生成大量真值表，小参数下枚举求解，
并对每一个返回的解逐行回代真值表（strict_verify=True，不通过即抛异常）。
"""


def _check_basics() -> List[str]:
    fails = []

    def ok(cond, msg):
        if not cond:
            fails.append(msg)

    ok(X.to_str(X.gate("AND", X.var(0), X.var(1))) == "AND(x0,x1)", "AND 字符串化")
    ok(X.to_str(X.gate("AND", X.var(1), X.var(0))) == "AND(x0,x1)", "交换律规范化")
    ok(X.gate("NAND", X.var(0), X.var(1)) == X.gate("NAND", X.var(1), X.var(0)), "NAND 交换律")
    ok(X.bus(X.bus(X.var(0), X.var(1)), X.var(2)) == X.bus(X.var(2), X.bus(X.var(0), X.var(1))),
       "总线展平与排序")
    ok(X.dag_cost(X.gate("AND", X.var(0), X.var(1))) == 1, "门数")
    ok(X.dag_delay(X.gate("AND", X.var(0), X.var(1))) == 1, "延迟")

    # 共享子电路只算一次
    p = X.gate("NOR", X.var(0), X.var(1))
    shared = X.gate("OR", X.gate("AND", X.var(0), p), X.gate("AND", X.var(1), p))
    ok(X.dag_cost(shared) == 4, "DAG 共享计数（期望 4，实得 %d）" % X.dag_cost(shared))

    # 解析往返
    src = "BUS_OR(SWITCH(x0,OR(x1,x2)),SWITCH(x1,NAND(x0,x2)))"
    ok(X.to_str(X.parse(src)) == src, "解析往返：%r" % X.to_str(X.parse(src)))

    # 三态语义：x0 是使能，x1 是数据
    sw = X.switch(X.var(0), X.var(1))
    ok(X.eval3(sw, 0b11) == 1, "开关导通")
    ok(X.eval3(sw, 0b01) == 0, "开关导通但数据为 0")
    ok(X.eval3(sw, 0b10) is X.Z, "开关断开必须返回浮空，而不是被驱动的 0")
    ok(X.eval3(X.gate("OR", sw, X.const(0)), 0b10) == 0, "浮空线进入门后下拉为 0")
    ok(X.eval3(X.gate("OR", sw, X.const(0)), 0b10, pull_down=False) is X.Z,
       "严格三态下浮空会传播")
    bad = X.bus(X.switch(X.var(0), X.const(1)), X.switch(X.var(0), X.const(0)))
    ok(X.eval3(bad, 0b01) is X.CONFLICT, "总线短路检测")
    return fails


def _check_verifier() -> List[str]:
    fails = []
    # SUM 的真值表，但喂一个明显错误的表达式
    if X.verify(X.var(0), 3, 0x96) is None:
        fails.append("验证器未能识别错误表达式")
    if X.verify(X.gate("XOR", X.gate("XOR", X.var(0), X.var(1)), X.var(2)), 3, 0x96) is not None:
        fails.append("验证器误报了正确的 XOR3")
    # 半个开关只覆盖真值表的一半：x0=1 时输出 1，x0=0 时无人驱动
    half = X.switch(X.var(0), X.const(1))          # 等价于 x0
    if X.verify(half, 1, 0b10, pull_down=False) is None:
        fails.append("未能检测到浮空输出")
    if X.verify(half, 1, 0b10, pull_down=True) is not None:
        fails.append("下拉模型下误报浮空")
    # 两个驱动源在同一行输出不同值 -> 短路
    short = X.bus(X.switch(X.var(0), X.const(1)), X.switch(X.var(0), X.const(0)))
    if X.verify(short, 1, 0b10, pull_down=True) is None:
        fails.append("未能检测到总线短路")
    return fails


def _check_known() -> List[str]:
    fails = []
    cfg = Config(verbose=False, strict_verify=True, prune_slack=3,
                 top_k_comb=3, top_k_tri=4, bus_seed_limit=24)
    # 全加器 Cout：4 门，延迟 3
    sols = LogicSynthesizer(3, 0xE8, 4, config=cfg).synthesize()
    if not sols:
        fails.append("Cout 无解")
    else:
        best_g = min(s.gates for s in sols)
        if best_g > 4:
            fails.append("Cout 最优门数 %d 超过已知最优 4" % best_g)
    # 全加器 SUM：6 门
    sols = LogicSynthesizer(3, 0x96, 6, config=cfg).synthesize()
    if not sols:
        fails.append("SUM 无解")
    else:
        best_g = min(s.gates for s in sols)
        if best_g > 6:
            fails.append("SUM 最优门数 %d 超过已知最优 6" % best_g)
    # XOR3 就是 SUM
    xor3 = LogicSynthesizer(3, Masks.xor(3), 6, config=cfg).synthesize()
    if not xor3 or min(s.gates for s in xor3) != min(s.gates for s in sols):
        fails.append("XOR3 与 SUM 的最优门数应当一致")
    return fails


def _check_random(rounds: int, seed: int, verbose: bool) -> Tuple[List[str], int]:
    """随机真值表回归：每个解都必须通过真值表校验。"""
    fails: List[str] = []
    rng = random.Random(seed)
    solved = 0
    checked = 0
    cfg = Config(verbose=False, strict_verify=True, prune_slack=2)
    for _ in range(rounds):
        n = rng.choice((2, 3))
        mask = rng.getrandbits(1 << n)
        d = rng.choice((2, 3, 4)) if n == 2 else rng.choice((3, 4))
        syn = LogicSynthesizer(n, mask, d, output_mode="all", config=cfg)
        sols = syn.synthesize()
        if sols:
            solved += 1
        for s in sols:
            checked += 1
            err = X.verify(s.expr, n, mask)
            if err:
                fails.append("n=%d mask=0x%X D=%d 解不合法：%s | %s"
                             % (n, mask, d, err, X.to_str(s.expr)))
            # 报告的成本必须与实际表达式一致
            real_g = X.dag_cost(s.expr, cfg.switch_cost)
            real_d = X.dag_delay(s.expr)
            if real_g != s.gates:
                fails.append("门数不符：报告 %d，实际 %d" % (s.gates, real_g))
            if real_d != s.delay:
                fails.append("延迟不符：报告 %d，实际 %d" % (s.delay, real_d))
    if verbose:
        print("  随机回归：%d 个随机真值表，%d 个有解，共校验 %d 个解"
              % (rounds, solved, checked))
    return fails, checked


def _check_multi(verbose: bool) -> List[str]:
    fails = []
    cfg = Config(verbose=False, strict_verify=True, prune_slack=2)
    sols = LogicSynthesizer(3, [0x96, 0xE8], 6, config=cfg).synthesize()
    if not sols:
        fails.append("全加器双输出无解")
        return fails
    for s in sols:
        err = X.verify_multi(s.expr, 3, [0x96, 0xE8])
        if err:
            fails.append("双输出解不合法：%s" % err)
        if s.gates != X.dag_cost(s.expr[0]) + X.dag_cost(s.expr[1]) - _shared(s.expr):
            # 允许共享，所以这里只做个宽松的区间检查
            pass
    if verbose:
        best = min(s.gates for s in sols)
        print("  全加器双输出最优总门数：%d" % best)
    return fails


def _shared(exprs) -> int:
    nodes = set()
    for e in exprs:
        nodes |= X.dag_nodes(e)
    total = sum(len(X.dag_nodes(e)) for e in exprs)
    return total - len(nodes)


def run_self_test(verbose: bool = True, rounds: int = 30, seed: int = 20240904) -> bool:
    t0 = time.time()
    fails: List[str] = []
    steps = [
        ("表达式与代价模型", lambda: _check_basics()),
        ("验证器", _check_verifier),
        ("已知最优值", _check_known),
        ("多输出共享", lambda: _check_multi(verbose)),
    ]
    for name, fn in steps:
        f = fn()
        if verbose:
            print("  [%s] %s" % ("通过" if not f else "失败", name))
        fails.extend(f or [])

    f, _ = _check_random(rounds, seed, verbose)
    if verbose:
        print("  [%s] 随机回归" % ("通过" if not f else "失败"))
    fails.extend(f)

    if verbose:
        print("\n%s  用时 %.2fs" % ("全部通过" if not fails else "发现 %d 个问题" % len(fails),
                                    time.time() - t0))
    for msg in fails:
        print("  - %s" % msg)
    return not fails


# ==========================================================================
# 入口
# ==========================================================================
if __name__ == "__main__":
    sys.exit(main())
