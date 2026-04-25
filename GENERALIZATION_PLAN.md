# Generalization Plan: From Register to Arbitrary Contracts

This document distils what's *contract-specific* and what's *generic*
in the Register balance-monotonicity proof, and proposes what to lift
into the framework so that proving similar reentrancy-resistant
inductive invariants for other contracts becomes mostly a matter of
filling in a small per-contract closure.

## Inventory: where the work lives now

The Register proof spans roughly three regions:

* **Generic frame library** (`EVMYulLean/EvmYul/Frame/*`, ~8,700 LoC) —
  fully reusable, contains nothing Register-specific.
* **Register-bytecode closure** (`EvmSmith/Demos/Register/BytecodeFrame.lean`,
  ~800 LoC) — defines `RegisterTrace`, the 14-case bytecode walk, and
  the six closure lemmas the framework's `ΞPreservesAtC_of_Reachable`
  consumes.
* **Register-tx composition** (`EvmSmith/Demos/Register/BalanceMono.lean`,
  ~360 LoC) — assembles `Υ_balanceOf_ge` with three witnesses
  (`bytecodePreservesBalance`, `register_Υ_tail_invariant`,
  `register_Υ_body_factors`).

The framework already factors out **what stays the same** for any
single-contract balance invariant. The third bucket is mostly generic
glue with one or two small contract-specific pieces (the SD-exclusion
and dead-filter-exclusion hypotheses on the tx's post-Υ substate).

The second bucket is where each contract has its own work — but the
*shape* of the work is identical across contracts.

## What's already generic (no further work needed)

* **`Υ_balanceOf_ge`** (`UpsilonFrame.lean`) — top-level entry point.
  Takes `(C, b₀)` plus three witnesses; works for any `C`.
* **`ΞPreservesAtC_of_Reachable`** (`MutualFrame.lean`) — turns a
  per-contract reachability predicate into the bytecode witness
  `ΞPreservesAtC C`. Works for any `Reachable : EVM.State → Prop`.
* **`Θ_balanceOf_ge` / `Λ_balanceOf_ge` / `Ξ_balanceOf_ge_bundled`** —
  the joint mutual closure. These don't know about Register at all;
  they're the C ≠ codeOwner case feeding from a generic
  `ΞPreservesAtC C` witness.
* **`StateWF`, `TxValid`, the no-wrap arithmetic helpers** — generic.

## What the per-contract closure needs (the second bucket)

To prove `ΞPreservesAtC C` for a new contract via
`ΞPreservesAtC_of_Reachable`, six closure lemmas are needed. Their
*shape* is fixed by the framework; their *content* is bytecode-specific.
Looking at Register's instances:

| Lemma | Shape | Register's content |
|-------|-------|--------------------|
| `Reachable_Z_preserves` | gas-only updates preserve `Reachable` | trivial — `RegisterTrace` doesn't constrain gas |
| `Reachable_step_preserves` | step preserves `Reachable` | **14-case bytecode walk** |
| `Reachable_decodeSome` | every reachable state decodes to `some` | `decide` over fixed PCs |
| `Reachable_op_in_8` | decoded op is in the contract's instruction set | `decide` over fixed PCs |
| `Reachable_v0_at_CALL` | CALL's value is 0 | extract from PC-specific stack-shape clause |
| `Reachable_initial` | initial state is reachable | uses the contract-specific code-identity axiom |

All six follow from the structure of `Reachable` (Register's was
`RegisterTrace`). The interesting one is `Reachable_step_preserves`:
14 PC cases × ~30-40 LoC ≈ ~500 LoC of mechanical proof.

## Where the leverage is

Most of the per-contract work is *reasoning about a single step at a
specific PC* — i.e., "at PC=k with stack-shape X, executing op O
yields a state with stack-shape Y at PC=k'". This is the same shape
for every contract.

Three things to lift into the framework:

### 1. A "generic per-PC step shape" library

For each opcode, a single-step shape lemma:

```lean
theorem step_PUSH1_shape (s s' : EVM.State) (cost f' : ℕ) (arg : Option (UInt256 × Nat))
    (hArg : arg = some (v, 1)) (hStep : EVM.step (f'+1) cost (some (.Push .PUSH1, arg)) s = .ok s') :
    s'.executionEnv = s.executionEnv ∧
    s'.createdAccounts = s.createdAccounts ∧
    s'.accountMap = s.accountMap ∧
    s'.pc = s.pc + UInt256.ofNat 2 ∧
    s'.stack = v :: s.stack
```

…and similar for CALLDATALOAD, CALLER, GAS, POP, STOP, SSTORE, JUMP,
JUMPI, JUMPDEST, DUP*, SWAP*, ADD, SUB, MUL, DIV, MOD, LT, GT, EQ,
ISZERO, AND, OR, XOR, NOT, SHL, SHR, KECCAK256, …, plus a CALL/CREATE
shape that bottoms out in the framework's existing arms.

These lemmas already exist *inside* `RegisterTrace_step_preserves`'s
local helpers (the previous agent extracted `step_PUSH1_shape`,
`step_CALLDATALOAD_shape`, `step_CALLER_shape`, `step_SSTORE_shape`,
`step_GAS_shape`, `step_POP_shape`, `step_STOP_shape`, `step_CALL_shape`).
They just need to move to `EVMYulLean/EvmYul/Frame/StepShapes.lean`
and be made `theorem` (not `private theorem`) so any consumer can use
them. Estimated ~30 opcodes for a useful coverage subset, ~1000 LoC.

### 2. A "PC-walk" tactic or proof template

Once shape lemmas exist, the per-contract `Reachable_step_preserves`
becomes a structured 14-case dispatch:

```lean
theorem RegisterTrace_step_preserves (...) := by
  -- Common preamble: extract op, hCO, hCode from RegisterTrace
  obtain ⟨hCO, hCode, hPC⟩ := h
  rcases hPC with caseList
  -- For each case, apply the matching shape lemma + reconstruct the next disjunct
  case PC0  => apply_step_shape PUSH1_shape ; show next_disjunct (PC=2, length=1)
  case PC2  => apply_step_shape CALLDATALOAD_shape ; ...
  ...
```

The `apply_step_shape` tactic could be a small Lean macro that handles
the boilerplate: substitute `op` and `arg` from `op_eq_of_fetchInstr_decode`,
unfold `EVM.step` via the shape lemma, derive the post-state, and
wrap the next-disjunct.

This would compress each PC case from ~30-40 LoC to ~5-10 LoC. For a
14-PC contract, total drops from ~500 LoC to ~100 LoC.

### 3. A "trace predicate generator" / DSL

The shape of `RegisterTrace` is mechanical from the bytecode: list the
valid PCs, write the stack-length invariant per PC, and add `stack[k]?
= some 0` clauses where the contract pushes a constant 0 that flows
into a CALL's value position. A small Lean meta-program (or even just
a Lean macro) could generate the predicate definition + the
`Reachable_decodeSome` + `Reachable_op_in_8` + `Reachable_v0_at_CALL`
proofs from the bytecode.

This is more invasive than the previous two but would compress the
per-contract work to: define bytecode → run macro → write
`Reachable_step_preserves` (which is the only really proof-shaped
piece) → declare contract-specific code-identity axiom → invoke
`ΞPreservesAtC_of_Reachable`.

## Generalising the tx-level composition (third bucket)

`BalanceMono.lean`'s structure is essentially generic. What's
contract-specific:

* The `RegSDExclusion` and `RegDeadAtσP` hypotheses on
  `register_balance_mono` are real-world structural facts the contract
  author declares. These should be lifted into a generic
  `BodyTailInvariants` predicate parameterised by C, and the
  `register_balance_mono` ⇒ `contract_balance_mono` skeleton
  parameterised over a generic `bytecodePreservesBalance` witness.

A library-level theorem along the lines of:

```lean
theorem contract_balance_mono
    (C : AccountAddress) (Reachable : EVM.State → Prop)
    (codeIdAxiom : ∀ I, I.codeOwner = C → I.code = expected_code)
    (closures : ContractTraceClosures C Reachable expected_code)
    -- ... standard tx-level hypotheses ...
    (hSDExcl : RegSDExclusion ...) (hDeadAtσP : RegDeadAtσP ...) :
    -- ... b₀ ≤ balanceOf σ' C ...
```

reduces a contract balance-monotonicity proof to:

1. Define expected_code (the bytecode).
2. Define `Reachable` (the trace predicate).
3. Prove the closure pack `ContractTraceClosures`.
4. Declare the per-contract code-identity axiom.
5. Invoke `contract_balance_mono`.

## What does NOT generalise easily

* Contracts emitting CALLs with **non-zero value** require a different
  invariant. The current `step_CALL_arm_at_C_v0` chain is hard-wired
  to `value = 0`. For non-zero CALLs, the at_C balance can decrease,
  so balance-monotonicity is *not* the right invariant — instead, a
  caller-specific bound or the relative invariant
  `balanceOf σ' C ≥ balanceOf σ C - sum_of_outbound_values`
  would be needed. This is a meaningfully different proof shape.

* Contracts with **conditional control flow** (JUMP, JUMPI on dynamic
  conditions) can't have a finite `Reachable` predicate enumerating PC
  values. They'd need a parametric `Reachable` that depends on
  storage/calldata/etc. Loops similarly require `Reachable` to be
  invariant under multiple step iterations.

* Contracts with **CREATE/CREATE2** — the framework currently relies
  on the contract-specific code-identity axiom (Register's analogue:
  *no contract in this tx tree creates address C*). A contract that
  itself does CREATE/CREATE2 invalidates this assumption unless it
  proves its own derived addresses are ≠ C; this requires bytecode
  reasoning about salt and constructor input.

* Contracts with **SELFDESTRUCT** — Register's argument relies on no
  SELFDESTRUCT in its own bytecode; SELFDESTRUCT-emitting contracts
  need a different `RegSDExclusion` analogue.

## Concrete plan if you want to prove a second contract

Suppose the next demo is a simple non-payable router that emits CALLs
with value=0 to its caller (similar shape to Register but different
opcodes). Then:

1. **Reuse**: framework, `Υ_balanceOf_ge`,
   `ΞPreservesAtC_of_Reachable`, all step shape helpers (already in
   `BytecodeFrame.lean` for Register; lift to framework first).
2. **Write per-contract**: `RouterTrace` predicate (PC × stack-shape),
   `RouterTrace_step_preserves` (one case per PC; ~30 LoC each, less
   if shape lemmas + macro tactics in place), tx-level body
   factorisation helpers (~100 LoC, mostly copy from
   `BalanceMono.lean` substituting `Router*` for `Register*`).
3. **Declare**: contract-specific code-identity axiom; `RouterSDExclusion`
   and `RouterDeadAtσP` hypotheses on the top-level theorem.

Estimated total per new contract: ~300-500 LoC. Most of that is the
`Reachable_step_preserves` walk; everything else is mechanical glue.

## Sequencing the framework lift

If the goal is to make the next contract's proof cheap:

1. **First** (small payoff, easy): pull `step_PUSH1_shape`, etc., out
   of `BytecodeFrame.lean` into a new
   `EVMYulLean/EvmYul/Frame/StepShapes.lean`. Make them public. ~1 hour.

2. **Second** (medium payoff, medium effort): cover more opcodes (DUP*,
   SWAP*, JUMP, JUMPI, arithmetic, KECCAK256). ~6-12 hours.

3. **Third** (big payoff, medium effort): write a `pc_walk` tactic
   that handles the boilerplate of each PC case. This is the single
   biggest LoC reduction. ~4-8 hours.

4. **Fourth** (open-ended): support contracts with non-zero CALL value.
   This requires a different at-C invariant and a different
   `step_CALL_arm` chain. Substantial.

5. **Fifth** (open-ended): strengthen `Θ_balanceOf_ge` / `Λ_balanceOf_ge`
   to expose substate-tracking + code-frame outputs, so
   `RegSDExclusion` / `RegDeadAtσP` become derivable inside Lean
   instead of caller-supplied. This eliminates the last vestige of
   "real-world structural fact"-style hypothesis on consumer theorems.

The first three lift Register-style proofs to "fill in a 50-100 LoC
bytecode walk + declare hypotheses". Steps 4 and 5 broaden the scope
to other invariant shapes and tighten the framework's ground
assumptions.
