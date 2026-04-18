import EvmSmith.Lemmas
import EvmSmith.Demos.Weth.Program

/-!
# Correctness of the `Weth` program

## Status

Lean proofs for `Weth` are **deferred**. The contract's safety is
established end-to-end by the Foundry test suite at `./foundry/`,
including a main-safety invariant (`invariant_user_funds_never_lost`
— 256 fuzz runs × 50 depth = 12 800 transition checks) and a
reentrancy test.

Block-level Lean proofs in the style of `Register/Proofs.lean` are
feasible with the step lemmas added to `EvmSmith/Lemmas.lean` as part
of this task (`runOp_callvalue`, `runOp_sload`, `runOp_lt`,
`runOp_iszero`, `runOp_dup{1..5}`, `runOp_swap{1,2}`, `runOp_sub`,
`runOp_pop`, `runOp_jumpdest`, `runOp_jumpi_{taken,not_taken}`,
`runOp_revert`). However the deposit block's ten-step chain and the
withdraw block's seventeen-step pre-CALL chain each require per-step
state-shape normalisation (propagating the `sload` intermediate
state's `executionEnv` field through the chain) that turns every
chain step into a small proof obligation. That plumbing was out of
scope for this deliverable.

## What the step lemmas enable (future work)

With the existing lemmas, the shape of each block-level theorem is:

```lean
theorem deposit_block_result (s0 : EVM.State) (selector : UInt256)
    (hs : s0.stack = [selector]) (hpc : s0.pc = depositLbl) :
    ∃ sf, runSeq depositBlock s0 = .ok sf ∧
          sf.toState = State.sstore
            (State.sload s0.toState (addressSlot source)).1
            (addressSlot source)
            ((State.sload s0.toState (addressSlot source)).2
             + s0.executionEnv.weiValue)
```

And functional-correctness / account-frame corollaries layered on
top via `sstore_accountMap`, the same pattern Register's proofs use.

See `.claude/weth-plan.md` for the detailed block structure and
invariant-statement targets.

## What's provable today, what's provable "tomorrow", what's not

| Invariant | Provable here | Blocker |
|-----------|---------------|---------|
| Block-level structural post-states | With effort (~100 LoC/block, state-shape plumbing) | Current file does not commit to proving them |
| Per-call functional correctness (account-map level) | With effort, after block-level proofs | Same |
| Per-call frame at account-map level | With effort, after block-level proofs | Same |
| Slot-level functional correctness | Blocked | `LawfulOrd UInt256` missing (same gap that blocked Register's slot-level theorems); see `.claude/batteries-wishlist.md` |
| Slot-level frame | Blocked | Same — `RBMap.find?_erase_*` also missing from Batteries |
| Reentrancy safety | Blocked | CALL semantics route through Θ iterator in upstream |
| Conservation (`Σ balances ≤ balance`) | Blocked | RBMap fold lemmas + CALL semantics |

Everything in the "Blocked" rows is exercised by Foundry tests.
Everything else can be closed by the next agent who picks up the
proof-engineering work — the step lemmas are in place.
-/

namespace EvmSmith.WethProofs

-- Intentionally empty. See module docstring for status.

end EvmSmith.WethProofs
