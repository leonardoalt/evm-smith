---
name: prove-balance-invariant
description: Prove a cross-transaction, reentrancy-resistant per-account invariant about a contract's bytecode (e.g. "this contract's balance never decreases", "Σ storage[k] ≤ contract.balance"). Goes through the EVMYulLean Frame library — `ΞPreservesAtC_of_Reachable` for the per-bytecode witness, then `Υ_balanceOf_ge` for the transaction-level frame. Use this skill *after* `add-program` when the property you want to prove holds across a full Ethereum transaction (`Υ`) and through any reentrant CALL/CREATE/SELFDESTRUCT path.
---

# Proving a cross-transaction reentrancy-resistant invariant

The headline use case is balance monotonicity at a fixed contract
address `C`: "after any single Ethereum transaction, my contract has
at least as much ETH as it started with." The Register demo
(`EvmSmith/Demos/Register/`) is the worked example; copy its shape.

## When this skill applies

Use this skill when **all** of the following hold:

* Your invariant talks about post-Υ state — i.e. it's a cross-tx claim
  ("after the whole transaction"), not just a single-opcode or single
  `runSeq` claim. (For single-tx claims, use `/prove-program`.)
* Your invariant is reentrancy-aware — the bytecode emits a `CALL`
  (or `CALLCODE`/`DELEGATECALL`/`STATICCALL`) that could trigger
  arbitrary user-controlled code, and the invariant must survive
  that.
* Your invariant is *per-account* — it talks about
  `balanceOf σ' C` (or storage at `C`, or "code at `C` preserved").
  Whole-state invariants (e.g. "totalETH conserved") need different
  framework support.

## High-level recipe

1. **Pick the predicate**: define `Reachable : EVM.State → Prop`
   capturing "this state is on the bytecode trace of my contract at
   `C`, with the stack-shape consistent with the current PC". For
   value-zero CALLs (the Register pattern), include `stack[2]? =
   some 0` at the CALL's PC.
2. **Discharge the 6 closure obligations** of
   `ΞPreservesAtC_of_Reachable`:
   - `Z`-stability (gas-only updates preserve `Reachable`)
   - **step**-stability (the bytecode walk — biggest piece)
   - decode-some at every reachable state
   - decoded op is in your bytecode's instruction set
   - if op is CALL, `stack[2]? = some 0`
   - initial state is reachable
3. **Compose with `Υ_balanceOf_ge`** in `BalanceMono.lean` to get the
   tx-level claim. Three additional witnesses are needed at this
   layer: the bytecode preservation (output of step 2),
   `ΥTailInvariant`, `ΥBodyFactors`. The latter two are mostly
   mechanical — the structural facts (no SELFDESTRUCT in your
   bytecode, code at `C` preserved) currently surface as
   caller-supplied hypotheses (`*SDExclusion`, `*DeadAtσP`) until
   the framework's substate-tracking refactor (Step 5 of
   `GENERALIZATION_PLAN.md`) fully lands.

## File layout

For a contract called `<Name>`:

```
EvmSmith/Demos/<Name>/
├── Program.lean         # bytecode (already exists from /add-program)
├── Invariant.lean       # RegInv-style precondition predicate (b₀ ≤ balance, code matches, etc.)
├── Proofs.lean          # local single-tx proofs (if any) via runSeq
├── BytecodeFrame.lean   # the bytecode walk + ΞPreservesAtC witness
└── BalanceMono.lean     # the tx-level theorem composing everything
```

The Register demo follows this exact layout. **Read it first.**

## Step 1 — define `Reachable`

Open `EvmSmith/Demos/<Name>/BytecodeFrame.lean`:

```lean
import EvmYul.Frame
import EvmSmith.Lemmas
import EvmSmith.Demos.<Name>.Invariant

namespace EvmSmith.<Name>
open EvmYul EvmYul.EVM EvmYul.Frame

/-- Trace predicate for `<Name>`'s bytecode at `C`. -/
private def <Name>Trace (C : AccountAddress) (s : EVM.State) : Prop :=
  C = s.executionEnv.codeOwner ∧
  s.executionEnv.code = bytecode ∧
  -- For each valid PC in the bytecode, an `(pc, stack-shape)` clause:
  ((s.pc.toNat = 0 ∧ s.stack.length = 0) ∨
   (s.pc.toNat = 2 ∧ s.stack.length = 1) ∨
   ...
   (s.pc.toNat = 17 ∧ s.stack.length = 7 ∧ s.stack[2]? = some ⟨0⟩) ∨ -- the CALL with v=0
   ...)
```

Key design choices:

* **Enumerate every PC** the contract can be at. For straight-line
  code, this is the byte offset of every opcode. For control-flow
  (JUMP/JUMPI), every reachable JUMPDEST.
* **At each PC, pin the stack length** that the bytecode invariant
  requires.
* **At any CALL PC**, pin the value-position element (`stack[2]?`)
  if the CALL is value-0.
* For storage-shape invariants, add storage-shape clauses too — but
  these don't enter the framework's closure obligations directly
  (they appear in the `ΥBodyFactors` discharge instead).

## Step 2 — discharge the six closure obligations

```lean
/-- Z (gas-only) preserves the trace. Trivial. -/
private theorem <Name>Trace_Z_preserves
    (C : AccountAddress) (s : EVM.State) (g : UInt256)
    (h : <Name>Trace C s) :
    <Name>Trace C { s with gasAvailable := g } := h

/-- decode_bytecode_at_<N> for each PC. -/
private theorem decode_bytecode_at_0 :
    decode bytecode (UInt256.ofNat 0)
      = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
  native_decide
-- ... one per PC

/-- decode-some, op-in-set, v0-at-CALL: discharge by case-split on
    the trace's PC disjuncts + the matching `decode_bytecode_at_<N>`. -/
private theorem <Name>Trace_decodeSome     ... := ...
private theorem <Name>Trace_op_in_<N>      ... := ...
private theorem <Name>Trace_v0_at_CALL     ... := ...

/-- Initial-state lemma: invokes the deployment-pinned axiom. -/
private axiom I_code_at_C_is_<Name>_bytecode
    (I : ExecutionEnv .EVM) (C : AccountAddress) :
    I.codeOwner = C → I.code = bytecode

private theorem <Name>Trace_initial ... := ...
```

The bytecode-walk lemma `<Name>Trace_step_preserves` is the heaviest:
one case per valid PC, dispatching to a `step_OP_at_pc` wrapper from
`EvmYul.Frame.PcWalk`:

```lean
private theorem <Name>Trace_step_preserves
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : <Name>Trace C s)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    <Name>Trace C s' := by
  obtain ⟨hCO, hCode, hPC⟩ := h
  rcases hPC with ⟨hpc, hLen⟩ | ... | ⟨hpc, hLen⟩  -- enumerate disjuncts
  -- one case per PC, each ~5-10 lines via PcWalk wrappers:
  · -- PC = 0
    obtain ⟨hpc_post, hstack_post, henv_post⟩ :=
      step_PUSH1_at_pc s s' f' cost _ _ _ hFetch hCode
        (pc_eq_ofNat_of_toNat _ _ hpc) decode_bytecode_at_0 hStep
    -- Land in the next-PC disjunct (PC = 2 in this case):
    refine ⟨?_, ?_, ?_⟩
    · rw [henv_post]; exact hCO
    · rw [henv_post]; exact hCode
    · right; left
      refine ⟨?_, ?_⟩
      · -- s'.pc.toNat = 2: derived from hpc_post + hpc
        ...
      · -- post-stack length = 1
        ...
  -- ... 13 more cases for Register
```

The `step_OP_at_pc` wrapper API (in
[`PcWalk.lean`](../../EVMYulLean/EvmYul/Frame/PcWalk.lean)) exists for
54 opcodes today: PUSH1, CALLDATALOAD, CALLER, GAS, CALLVALUE,
ADDRESS, ORIGIN, etc.; CALL; SSTORE; ADD/SUB/MUL/DIV/MOD/LT/GT/EQ/AND/OR;
KECCAK256; MLOAD/MSTORE/MSTORE8; SLOAD; JUMP/JUMPI; ISZERO/NOT/POP;
DUP1; etc. If your contract uses an opcode not in `PcWalk.lean`, see
**Extending the framework** below.

## Step 3 — assemble the witness

```lean
theorem bytecodePreservesBalance (C : AccountAddress) :
    ΞPreservesAtC C := by
  exact ΞPreservesAtC_of_Reachable C (<Name>Trace C)
    (<Name>Trace_Z_preserves C)
    (<Name>Trace_step_preserves C)
    (<Name>Trace_decodeSome C)
    (<Name>Trace_op_in_<N> C)
    (<Name>Trace_v0_at_CALL C)
    (<Name>Trace_initial C)
```

## Step 4 — compose with `Υ_balanceOf_ge` in `BalanceMono.lean`

Mirror Register's `BalanceMono.lean`. The top-level theorem takes
seven hypotheses:

```lean
theorem <name>_balance_mono
    (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks)
    (tx : Transaction) (S_T C : AccountAddress) (b₀ : ℕ)
    (hWF : StateWF σ)                      -- T1: total ETH < 2^255
    (hInv : <Name>Inv σ C b₀)              -- pre-tx invariant
    (hS_T : C ≠ S_T)                       -- C is not the tx sender
    (hBen : C ≠ H.beneficiary)             -- C is not the miner
    (hValid : TxValid σ S_T tx H H_f)      -- T4: tx-validity (a hypothesis, not axiom)
    (hSDExcl : <Name>SDExclusion ...)      -- post-Υ A.SD-set excludes C
    (hDeadAtσP : <Name>DeadAtσP ...) :     -- code at C preserved through Θ/Λ
    match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
    | .ok (σ', _, _, _) => b₀ ≤ balanceOf σ' C
    | .error _ => True :=
  Υ_balanceOf_ge fuel σ H_f H H_gen blocks tx S_T C b₀
    hWF hInv.bal hS_T hBen (bytecodePreservesBalance C)
    (<name>_Υ_tail_invariant ... hSDExcl)
    (<name>_Υ_body_factors ... hWF hS_T hValid hInv.code hDeadAtσP)
```

The two structural hypotheses `<Name>SDExclusion` and `<Name>DeadAtσP`
are caller-supplied today (a follow-up framework lift will eliminate
them — see [`GENERALIZATION_PLAN.md`](../../GENERALIZATION_PLAN.md)
Step 5).

## Pitfalls

* **`partial def D_J`** in
  `EVMYulLean/EvmYul/EVM/Semantics.lean` means `D_J bytecode 0` doesn't
  reduce by `decide`. Don't rely on it; use `native_decide` for closed
  bytecode/PC computations.
* **Stack indexing**: `s.stack[k]?` is `List.get? s.stack k` —
  zero-indexed from the **top**. CALL pops `gas, addr, value, ...`, so
  `value` is at `stack[2]?`.
* **`UInt256` modular arithmetic**: `s.pc + UInt256.ofNat 2` doesn't
  evaluate to `UInt256.ofNat (s.pc.toNat + 2)` automatically. Use
  helper `pc_eq_ofNat_of_toNat` and reason via `.toNat` lifts.
* **Ξ runs at codeOwner = C are the at-C path**;
  Ξ runs at codeOwner ≠ C are handled by the framework's existing
  `ΞFrameAtC` / `Ξ_balanceOf_ge_bundled` infrastructure. Your
  `Reachable` predicate only needs to capture the at-C states.
* **The `Reachable` predicate is closed under steps but not under
  arbitrary state injections**: the closure obligations exclude
  arbitrary universes. Don't try to make `Reachable` true for every
  state — make it true exactly for the bytecode-trace states.
* **For non-zero-value CALLs with a relative invariant** (e.g.
  `Σ storage[sender] ≤ balanceOf σ C`): the framework's at-C / v=0
  chain (`step_CALL_arm_at_C_v0`) doesn't apply directly. Use the
  `_inv_aware` slack-dispatch variant
  (`ΞPreservesInvariantAtC_of_Reachable_general_call_slack_dispatch_inv_aware`,
  `MutualFrame.lean`), which exposes a per-step
  `<YourInv> s.accountMap C` precondition to your `hReach_step`
  callback so the bytecode walk can use the *current* invariant to
  bound CALL value. **Worked example**:
  `EvmSmith/Demos/Weth/Solvency.lean :: weth_solvency_invariant`
  (sorry-free) — copy its `WethInvFr` / `WethReachable` /
  `WethAssumptions` shape. See `EvmSmith/Demos/Weth/REPORT_WETH.md`
  and `EvmSmith/Demos/Weth/REPORT_FRAMEWORK.md` for the end-to-end
  walkthrough.

## Extending the framework

If your bytecode uses an opcode not in `EvmYul.Frame.PcWalk`:

1. Look in `EvmYul.Frame.StepShapes` (81 lemmas) — your opcode may
   already have a shape lemma.
2. If yes, add the matching `_at_pc` wrapper in `PcWalk.lean`
   following the existing wrapper pattern.
3. If no shape lemma exists for the opcode, add one in `StepShapes`.
   Most opcodes follow the `unfold EVM.step → simp [bind, ...] →
   unfold EvmYul.step → simp [Id.run] → unfold dispatchXxx → simp →
   subst → refine` template — see existing shapes for the matching
   dispatcher (`dispatchUnary`, `dispatchBinary`, `dispatchUnaryStateOp`, etc.).

These extensions live in the framework (the `EVMYulLean/` working
fork), not in your contract's directory.

## Build / verify

```bash
cd /home/leo/devel/evm-smith
~/.elan/bin/lake build       # full repo + framework
```

A clean `sorry`-free build is the verification. If a specific lemma
is failing, build just its file:

```bash
lake build EvmSmith.Demos.<Name>.BytecodeFrame
lake build EvmSmith.Demos.<Name>.BalanceMono
```

## References

- Register end-to-end:
  [`EvmSmith/Demos/Register/BALANCE_MONOTONICITY.md`](../../EvmSmith/Demos/Register/BALANCE_MONOTONICITY.md)
- Frame library overview:
  [`EVMYulLean/FRAME_LIBRARY.md`](../../EVMYulLean/FRAME_LIBRARY.md)
- Step shapes:
  [`EVMYulLean/EvmYul/Frame/StepShapes.lean`](../../EVMYulLean/EvmYul/Frame/StepShapes.lean)
- PC-walk wrappers:
  [`EVMYulLean/EvmYul/Frame/PcWalk.lean`](../../EVMYulLean/EvmYul/Frame/PcWalk.lean)
- Framework lift roadmap:
  [`GENERALIZATION_PLAN.md`](../../GENERALIZATION_PLAN.md)
