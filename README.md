# LogicSynthesizer
Exact multi-output logic synthesis with AND/OR/NAND/NOR/NOT/SWITCH/BUS_OR gates. Finds minimal gate count under delay constraints, supporting shared sub-expressions for multiple outputs. Based on a verified stable single-output engine.

# Target
1. Input: Truth table (arbitrary n inputs, 1 output).
2. Output: Logic circuit netlist, with gate-level primitives restricted to AND, OR, NOT, NOR, NAND, and SWITCH (tri-state gate).
3. Core constraint: Strictly enforce delay (logic levels), i.e., the delay of all paths must be ≤ the given max_delay.
4. Optimization objective: Under this delay constraint, minimize the gate count.
5. Multi-solution requirement: Return all minimum solutions (all equivalent circuits with the same gate count but different structures) for delays from the minimum delay up to a specified delay (i.e., delays 0~D).
6. Special tri-state rules:
   · Tri-state gates are allowed; outputs with Z are automatically pulled low to 0 (i.e., buses can implement a free "wired-OR").
   · Short-circuit prevention is mandatory: when merging buses, it must be strictly verified that (EN1 & EN2 & (DATA1 ^ DATA2)) == 0.
7. Pruning rule: During generation, if a useless gate appears (e.g., AND(x,x), AND(x,1), etc., degenerating into a wire or constant), discard that candidate immediately and do not expand it further.

# Problems
-SEVERE performance issues(now fixing XD)
