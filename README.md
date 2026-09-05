# TCBreaker

> 把真值表综合成**最优门级电路**的小工具 · Synthesize optimal gate-level circuits from truth tables.
> 严格遵循 Target 规格：AND / OR / NOT / NOR / NAND / SWITCH，开关计 2 门，总线免费 wired-OR。
> Strictly follows the Target spec: AND/OR/NOT/NOR/NAND/SWITCH, switch = 2 gates, bus is a free wired-OR.

![Python](https://img.shields.io/badge/python-3.10%2B-blue)
![Zero Dependency](https://img.shields.io/badge/dependencies-zero-brightgreen)
![Tests](https://img.shields.io/badge/tests-52%20passed-brightgreen)
![Verified](https://img.shields.io/badge/verified--by%20truth%20table-success)

---

# 中文文档  ·  Chinese

## 简介

TCBreaker 是一个把**真值表**综合成**最优门级电路**的小工具。给定任意 `n` 输入、`m` 输出的真值表，
它在延迟约束下最小化门数（门数按 DAG 计，共享子电路只算一次），并返回每个延迟下门数最小的**全部**等价电路。

特性 / Features：

- **最优且可验证**：分层精确枚举，每个返回的解都逐行回代真值表，不过就丢弃并告警。
- **多输出共享**：SUM + Cout 这类电路会自动共享中间子电路，全加器因此只需 **7 个门 / 4 级延迟**。
- **Target 规格**：门级原语仅 AND / OR / NOT / NOR / NAND / SWITCH；三态开关计 2 门；`Z` 浮空下拉为 0；总线免费 wired-OR 并带短路校验。
- **零依赖**：标准库实现，单文件版可直接拷走运行。
- **大任务护栏**：到达时间 / 候选数上限后优雅停止并返回当前最优解，不会卡死或 OOM。
- **电路图**：可把结果渲染成 SVG，照着在游戏里搭；同色网络 + 图例 + 扇出分歧点标记，连线一眼可追。

## 安装 / Install

```bash
# 方式一：作为包安装（推荐，支持 python -m tcbreaker）
cd tcbreaker_project
pip install -e .

# 方式二：单文件版，直接拷走 tcbreaker_single.py 即可，零依赖、零安装
python tcbreaker_single.py --adder --max-delay 6
```

## 快速开始 / Quick Start

```bash
# 全加器 SUM + Cout 双输出（共享子电路，最优 7 门 / 4 延迟）
python -m tcbreaker --adder --max-delay 6

# 单输出：3 输入异或，真值表 0x96，最多 6 层延迟
python -m tcbreaker --inputs 3 --target 0x96 --max-delay 6

# 跑内置自检（含 30 个随机回归）
python -m tcbreaker --self-test

# 跑单元测试套件
python -m unittest discover -s tests -v
```

### 全加器示例（7 门 / 4 延迟）

```bash
python -m tcbreaker --adder --max-delay 4
```

输出（节选）：

```
多输出最优解（成本最小）：
  延迟 4 | 总门数 7 | 成本 28
    输出0: AND(NAND(AND(NAND(x0,x1),OR(x0,x1)),x2), OR(AND(NAND(x0,x1),OR(x0,x1)),x2))
    输出1: NAND(NAND(AND(NAND(x0,x1),OR(x0,x1)),x2), NAND(x0,x1))
```

其中 `Y = AND(NAND(x0,x1), OR(x0,x1))` 就是共享的 XOR 节点（= `NOR(AND(x0,x1), NOR(x0,x1))`），
被 SUM 和 Cout 共用，所以总共只要 7 个门。

画成电路图（照着搭）：

```bash
python -m tcbreaker --adder --max-delay 6 --emit svg
# 默认把 circuit.svg 写到执行脚本所在目录；用 -o/--output 可指定路径
```

## 真值表怎么写

第 `row` 位对应输入组合 `row` 的整数值，`x0` 是最低位。以 SUM 为例：行 1、2、4、7 输出 1，
于是掩码 `0x96 = 0b1001_0110`。

命令行支持四种等价写法：

| 写法 | 说明 |
| --- | --- |
| `0x96` | 十六进制（推荐） |
| `0b10010110` | 二进制 |
| `10010110` | 裸二进制串，高位在前 |
| `0 1 1 0 1 0 0 1` | 位序列，低位在前 |

多个输出用逗号分隔：`--target 0x96,0xE8`。

## 电路语义

| 元件 | 表示 | 门数 | 延迟（逻辑级数） |
| --- | --- | --- | --- |
| 输入 / 常量 | `x0` / `0` `1` | 0 | 0 |
| 二元门 | `AND` `OR` `NAND` `NOR` | 1 | 1 + max(输入) |
| 非门 | `NOT(a)` | 1 | 1 + max(输入) |
| 三态开关 | `SWITCH(使能, 数据)` | **2** | 1 + max(使能, 数据) |
| 总线合并 | `BUS_OR(a,b,...)` | 0（导线） | max(输入) |

约定：

- **门数按 DAG 算**：共享子电路只计一次。`OR(AND(x0,p),AND(x1,p))` 是 4 个门而非 5 个。
- **浮空读作 0**：开关断开输出 `Z`，进入下一级自动下拉为 0（浮空不参与总线，驱动 0 会）。
- **总线短路校验**：合并前逐行检查 `(EN1 & EN2 & (DATA1 ^ DATA2)) == 0`，存在一行都导通且数据相反即判短路。
- **退化门剪枝**：`AND(x,x)`、`AND(x,1)` 等退化为线/常量立即丢弃，不再展开。

## 它做了什么

按延迟分层穷举：第 `d` 层保存所有延迟恰为 `d` 的子电路候选，逐层用一元/二元门、三态开关、
总线合并做闭包扩展。每个「掩码」永远保留门数最小的候选（并留 `keep_width` 余量以利多输出共享），
配合全局上界剪枝。最后对每个候选逐行回代真值表，只返回验证通过的解。

## 调参 / Tuning

```python
from tcbreaker import Config
Config(
    ops=("AND", "OR", "NAND", "NOR"),  # 二元门；规格默认不含 XOR/XNOR（需要可加）
    use_not=True, not_on_gates=True,   # NOT 是一元原语，可作用于任意信号
    use_switch=True, use_bus=True,
    switch_cost=2,                     # 三态门门数计为 2（Target 规格）
    prune_slack=1,                     # 剪枝余量，越大越慢但越不易漏解；--exhaustive 调到很大
    keep_width=2,                      # 最小门数之上额外保留的候选宽度（利于共享）
    top_k_comb=2, top_k_tri=3,         # 每个掩码的搜索宽度
)
```

## 大任务（时间 / 内存预算）

综合是指数级穷举，输入多或延迟大时迅速膨胀。命令行提供两道护栏，到达上限后**优雅停止并返回当前最优解**：

```bash
python -m tcbreaker --inputs 4 --target 0x6996 --max-delay 5 --time-limit 30
python -m tcbreaker --inputs 4 --target 0x6996 --max-delay 5 --max-candidates 20000
```

| 参数 | 含义 |
| --- | --- |
| `--time-limit SEC` | 最大运行秒数，0 = 不限（默认） |
| `--max-candidates N` | 候选总数上限，0 = 不限（默认）；用于挡住指数爆炸占用内存 |

## 作为库使用 / As a Library

```python
from tcbreaker import LogicSynthesizer, Config, circuit_svg

# 默认 per_delay 模式：每个延迟下门数最小的全部等价电路
sols = LogicSynthesizer(3, 0x96, 6).synthesize()
for s in sols:
    print(s.delay, s.gates, s.pretty())

# 只要成本最小的一个 / Pareto 前沿
LogicSynthesizer(3, 0x96, 6, output_mode="first").synthesize()
LogicSynthesizer(3, 0x96, 6, output_mode="all").synthesize()

open("circuit.svg", "w").write(circuit_svg(sols[-1].expr, 3))
```

## 验证 / Verification

**每个返回的解都会逐行回代真值表**，不通过直接丢弃并告警——这不是可选步骤。
`Config(strict_verify=True)` 让验证失败直接抛异常（测试里用它）。

## 目录结构 / Layout

```
tcbreaker/
  expr.py        表达式 AST、三态求值、代价模型、验证器
  synth.py       分层枚举综合器（含短路校验与退化门剪枝）
  truthtable.py  真值表掩码工具
  draw.py        电路图 SVG 渲染
  cli.py         命令行
  selftest.py    内置自检（含随机回归）
tests/           单元测试（52 个）
tcbreaker_single.py  单文件版（全部模块合并，零依赖，可直接拷走）
pyproject.toml   打包配置（pip install -e .）
```

## 声明 / Disclaimer

> 本项目的**部分代码与文档由 AI 辅助生成**（综合内核 `synth.py`、SVG 渲染 `draw.py`、单元测试与本文档），
> 经作者审阅与验证后纳入。如发现问题欢迎提 issue / PR。

---

# English Documentation

## Overview

TCBreaker synthesizes **optimal gate-level circuits** from **truth tables**. Given a truth table with
`n` inputs and `m` outputs, it minimizes gate count under a delay constraint (gates counted on the DAG,
so shared subcircuits are counted once) and returns **every** minimal-gate equivalent circuit at each
reachable delay.

Features:

- **Optimal & verified**: exact layered enumeration; every returned solution is back-substituted row by row into the truth table and discarded if it fails.
- **Multi-output sharing**: circuits like SUM + Cout automatically share subcircuits — the full adder needs only **7 gates / 4 logic levels**.
- **Target spec**: primitives limited to AND / OR / NOT / NOR / NAND / SWITCH; tri-state switch costs 2 gates; `Z` floats down to 0; bus is a free wired-OR with short-circuit checking.
- **Zero dependency**: standard-library only; the single-file build runs anywhere with just Python.
- **Large-task guardrails**: stops gracefully and returns the current best at the time/memory budget instead of hanging or OOM-ing.
- **Schematic**: renders the result to SVG for build-along; color-coded nets + legend + fan-out junction markers make every wire traceable.

## Install

```bash
# Option A: install as a package (enables `python -m tcbreaker`)
cd tcbreaker_project
pip install -e .

# Option B: single-file build — just copy tcbreaker_single.py, zero deps, zero install
python tcbreaker_single.py --adder --max-delay 6
```

## Quick Start

```bash
# Full adder SUM + Cout (shared subcircuits, optimal 7 gates / 4 delays)
python -m tcbreaker --adder --max-delay 6

# Single output: 3-input XOR, truth table 0x96, up to 6 delay levels
python -m tcbreaker --inputs 3 --target 0x96 --max-delay 6

# Built-in self-test (includes 30 random regressions)
python -m tcbreaker --self-test

# Unit-test suite
python -m unittest discover -s tests -v
```

### Full adder example (7 gates / 4 delays)

```bash
python -m tcbreaker --adder --max-delay 4
```

Output (excerpt):

```
多输出最优解（成本最小）：
  延迟 4 | 总门数 7 | 成本 28
    输出0: AND(NAND(AND(NAND(x0,x1),OR(x0,x1)),x2), OR(AND(NAND(x0,x1),OR(x0,x1)),x2))
    输出1: NAND(NAND(AND(NAND(x0,x1),OR(x0,x1)),x2), NAND(x0,x1))
```

Here `Y = AND(NAND(x0,x1), OR(x0,x1))` is the shared XOR node (equals `NOR(AND(x0,x1), NOR(x0,x1))`),
driven by both SUM and Cout, so the whole circuit is only 7 gates.

Render it as a schematic:

```bash
python -m tcbreaker --adder --max-delay 6 --emit svg
# circuit.svg is written next to the running script by default; use -o/--output to choose a path
```

## Truth table format

Bit `row` corresponds to the integer value of the input combination, with `x0` as the least significant bit.
For SUM, rows 1, 2, 4, 7 output 1, so the mask is `0x96 = 0b1001_0110`.

Four equivalent forms are accepted on the command line:

| Form | Note |
| --- | --- |
| `0x96` | hexadecimal (recommended) |
| `0b10010110` | binary |
| `10010110` | bare binary string, MSB first |
| `0 1 1 0 1 0 0 1` | bit sequence, LSB first |

Multiple outputs are comma-separated: `--target 0x96,0xE8`.

## Circuit semantics

| Element | Notation | Gates | Delay (logic levels) |
| --- | --- | --- | --- |
| Input / const | `x0` / `0` `1` | 0 | 0 |
| Binary gate | `AND` `OR` `NAND` `NOR` | 1 | 1 + max(inputs) |
| Inverter | `NOT(a)` | 1 | 1 + max(inputs) |
| Tri-state switch | `SWITCH(enable, data)` | **2** | 1 + max(enable, data) |
| Bus merge | `BUS_OR(a,b,...)` | 0 (wire) | max(inputs) |

Conventions:

- **Gates counted on the DAG**: shared subcircuits counted once. `OR(AND(x0,p),AND(x1,p))` is 4 gates, not 5.
- **Floating reads as 0**: an off switch outputs `Z`, pulled down to 0 at the next stage (floating does not drive the bus; a driven 0 does).
- **Bus short-circuit check**: before merging, row by row `(EN1 & EN2 & (DATA1 ^ DATA2)) == 0`; if both conduct with opposite data on any row, the merge is rejected.
- **Degenerate-gate pruning**: `AND(x,x)`, `AND(x,1)`, etc. collapse to a wire/constant and are dropped immediately.

## How it works

Exact enumeration layered by delay: layer `d` holds every subcircuit whose delay is exactly `d`, extended
layer by layer with unary/binary gates, tri-state switches, and bus merges. Each mask always keeps the
minimal-gate candidates (plus a `keep_width` margin for multi-output sharing), with a global upper bound
for pruning. Finally every candidate is back-substituted into the truth table; only verified solutions
are returned.

## Tuning

```python
from tcbreaker import Config
Config(
    ops=("AND", "OR", "NAND", "NOR"),  # binary gates; spec excludes XOR/XNOR by default (add if wanted)
    use_not=True, not_on_gates=True,   # NOT is a unary primitive, usable on any signal
    use_switch=True, use_bus=True,
    switch_cost=2,                     # tri-state switch costs 2 gates (Target spec)
    prune_slack=1,                     # pruning margin; larger = slower but safer; --exhaustive sets it high
    keep_width=2,                      # extra candidate width above the minimum (helps sharing)
    top_k_comb=2, top_k_tri=3,         # search width per mask
)
```

## Large tasks (time / memory budget)

Synthesis is exponential; many inputs or large delays blow up fast. Two guardrails stop gracefully and
return the current best at the limit:

```bash
python -m tcbreaker --inputs 4 --target 0x6996 --max-delay 5 --time-limit 30
python -m tcbreaker --inputs 4 --target 0x6996 --max-delay 5 --max-candidates 20000
```

| Flag | Meaning |
| --- | --- |
| `--time-limit SEC` | max run seconds, 0 = unlimited (default) |
| `--max-candidates N` | total candidate cap, 0 = unlimited (default); bounds memory against exponential blow-up |

## As a library

```python
from tcbreaker import LogicSynthesizer, Config, circuit_svg

# default per_delay mode: every minimal-gate circuit at each delay
sols = LogicSynthesizer(3, 0x96, 6).synthesize()
for s in sols:
    print(s.delay, s.gates, s.pretty())

# only the minimal-cost one / the Pareto front
LogicSynthesizer(3, 0x96, 6, output_mode="first").synthesize()
LogicSynthesizer(3, 0x96, 6, output_mode="all").synthesize()

open("circuit.svg", "w").write(circuit_svg(sols[-1].expr, 3))
```

## Verification

**Every returned solution is back-substituted row by row into the truth table** and discarded if it fails —
this is not optional. `Config(strict_verify=True)` raises on verification failure (used in tests).

## Project layout

```
tcbreaker/
  expr.py        expression AST, tri-state evaluation, cost model, verifier
  synth.py       layered enumeration synthesizer (short-circuit + degenerate-gate pruning)
  truthtable.py   truth-table mask utilities
  draw.py         circuit SVG renderer
  cli.py          command line
  selftest.py     built-in self-test (with random regressions)
tests/           unit tests (52)
tcbreaker_single.py  single-file build (all modules merged, zero dependency, copy-and-run)
pyproject.toml    packaging config (pip install -e .)
```

## Disclaimer

> Part of the code and documentation in this project was generated with AI assistance (the synthesis
> core `synth.py`, the SVG renderer `draw.py`, the unit tests, and this document), reviewed and
> verified by the author before inclusion. Issues and PRs are welcome.
