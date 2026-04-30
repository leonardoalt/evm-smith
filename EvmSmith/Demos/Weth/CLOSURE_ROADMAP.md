# Weth solvency proof — closure roadmap

**State (2026-04-30, post-session)**: `weth_solvency_invariant` is a
typed Lean theorem. Build green, 2 axioms (T2 + T5), 0 sorries. The
theorem is conditional on `WethAssumptions` (9 fields), all of which
are strictly narrower than the prior opaque cascade-fact predicates.

All three bytecode-cascade-fact predicates (`WethPC40CascadeFacts`,
`WethPC60CascadeFacts`, `WethPC72CascadeFacts`) are now **theorems**
in `BytecodeFrame.lean`, derived from the narrower structural facts
in `WethAssumptions`.

## Current `WethAssumptions` shape

```lean
structure WethAssumptions ... : Prop where
  -- Register-shape (4): direct mirrors of register_balance_mono's hypotheses.
  deployed         : DeployedAtC C
  sd_excl          : WethSDExclusion σ ...
  dead_at_σP       : WethDeadAtσP    σ ...
  inv_at_σP        : WethInvAtσP     σ ...
  -- Bytecode-narrowed (5): replace prior opaque cascade-fact fields.
  account_at_C     : WethAccountAtC C
  call_no_wrap     : WethCallNoWrapAt72 C
  call_slack       : WethCallSlackAt72 C
  deposit_cascade  : WethDepositCascadeStruct C
  deposit_slack    : WethDepositPreCredit C
```

## What's a theorem now (this session)

* `weth_pc60_cascade : WethAccountAtC C → WethPC60CascadeFacts C`
  — derived from the threaded WethTrace cascade PCs 47..60 plus
  σ-has-C.

* `weth_pc72_cascade :
    WethCallNoWrapAt72 C → WethCallSlackAt72 C → WethPC72CascadeFacts C`
  — derived from the bundled slack/funds/no-wrap structural facts.

* `weth_pc40_cascade :
    WethDepositCascadeStruct C → WethDepositPreCredit C →
    WethPC40CascadeFacts C` — derived from the bundled
  bytecode-cascade + Θ-pre-credit structural facts.

* `bytecodePreservesInvariant_fully_narrowed` — the final composition
  entry that takes only the narrowed structural facts and produces
  `ΞPreservesInvariantAtC C`.

## Which assumptions are bytecode-derivable in principle

The following could be discharged as theorems with mechanical
threading work (the same pattern used for PCs 47..60):

* **`account_at_C`** (σ-has-C): extend `WethReachable` with
  `∃ acc, σ.find? C = some acc`. Update ~61 walks to preserve. For
  most opcodes, σ unchanged ⇒ trivial via
  `EvmYul.step_accountMap_eq_of_strict`. For SSTORE/CALL, use the
  existing dischargers. ~300 LoC.

* **`call_slack`** (post-PC-60 slack at PC 72): extend
  `WethReachable` with `WethInvFr σ C`, update walks (most via
  accountMap-preservation), thread the slack invariant through PCs
  60..72 disjuncts. PC 60 walk uses `WethInvFr σ_60` to discharge PC
  61 slack via the SSTORE delta. PCs 61..71 walks preserve the
  slack via σ-unchanged. ~500 LoC of cascade threading + 200 LoC of
  walk preservation updates.

* **`deposit_cascade`** (stack/storage shape at PC 40): cascade
  threading PCs 32..40. Same pattern as PCs 47..60 (already done).
  Estimated ~500 LoC.

## Genuinely irreducible assumptions

The following encode facts about the world or framework that
**cannot** be derived from WETH bytecode analysis:

* **`call_no_wrap`** (recipient balance + value < 2^256):
  Real-world chain bound. The total ETH supply plus any single
  contract balance fits in `UInt256` (in practice the chain enforces
  this, and the EVM's UInt256 arithmetic guarantees it for actual
  chain state). Orthogonal to WETH's bytecode.

* **`deposit_slack`** (Θ-pre-credit at PC 40): the Υ-side fact that
  msg.value was already added to C's balance by Θ before Ξ entered
  to execute the deposit. Lives in the framework's outer Θ/Λ layer,
  not in the bytecode trace.

## What this session landed (16 commits)

1. **PC 47..60 cascade fully threaded** through `WethTrace`. Each PC's
   trace disjunct carries `(slot, oldVal, x)` witnesses with the
   `x ≤ oldVal` bound from PC 51's LT + PC 55's JUMPI not-taken.
2. **Strong shape lemmas** in `EVMYulLean` framework: DUP1/2/3, SWAP1,
   PUSH (generic), JUMPI — each with `accountMap` preservation.
3. **`pc60_cascade` discharged as theorem** via `WethAccountAtC`.
4. **`pc72_cascade` discharged as theorem** via `WethCallNoWrapAt72`
   + `WethCallSlackAt72`.
5. **`pc40_cascade` discharged as theorem** via
   `WethDepositCascadeStruct` + `WethDepositPreCredit`.

## Net effect

Before this session: `WethAssumptions` had three opaque
`Weth*CascadeFacts` predicates encoding broad per-PC structural
data. Discharging required full bytecode threading.

After this session: zero opaque `Weth*CascadeFacts` predicates in
`WethAssumptions`. Five narrower structural facts replace them.
Three of these five are bytecode-derivable in principle (with
mechanical threading work). Two are genuinely irreducible
real-world / framework facts.

The headline `weth_solvency_invariant` theorem is unchanged — it
still proves `storageSum σ_post C ≤ balanceOf σ_post C` after any
single Ethereum transaction, conditional on `WethAssumptions`.
