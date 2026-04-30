# Weth solvency proof — closure roadmap

**State (2026-04-30, post-session)**: `weth_solvency_invariant` is
typed and proved as a Lean theorem. Build green, 2 axioms (T2 + T5), 0
sorries. The theorem is conditional on `WethAssumptions` (7 fields).

The PC 60 withdraw-cascade is now **fully threaded end-to-end** PCs
47→60 in `WethTrace`. The cascade carries the LT/JUMPI bound `x ≤
oldVal` and the SLOAD-derived storage equation. Build green at every
intermediate step.

## `WethAssumptions` final shape

```lean
structure WethAssumptions
    (σ : AccountMap .EVM) (fuel H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks)
    (tx : Transaction) (S_T C : AccountAddress) : Prop where
  -- Register-shape (4): direct mirrors of register_balance_mono's hypotheses.
  deployed         : DeployedAtC C
  sd_excl          : WethSDExclusion σ fuel H_f H H_gen blocks tx S_T C
  dead_at_σP       : WethDeadAtσP    σ fuel H_f H H_gen blocks tx S_T C
  inv_at_σP        : WethInvAtσP     σ fuel H_f H H_gen blocks tx S_T C
  -- Bytecode-cascade (3): per-PC structural facts about Weth's withdraw + deposit flows.
  pc40_cascade     : WethPC40CascadeFacts C   -- deposit SSTORE
  pc60_cascade     : WethPC60CascadeFacts C   -- withdraw SSTORE
  pc72_cascade     : WethPC72CascadeFacts C   -- withdraw CALL
```

## What landed this session

PC-by-PC cascade threading PCs 47→60 (12 commits):

1. PC 48: DUP1 invariant `stack[0]? = stack[1]?` carried in disjunct.
2. PC 49: post-SLOAD-strong cascade `(slot, oldVal, x)` with `oldVal = SLOAD(slot at C)`.
3. PC 50: post-DUP3 cascade.
4. PC 51: post-DUP2 cascade — both LT inputs (oldVal, x) materialized.
5. PC 52: post-LT cascade carrying `UInt256.lt oldVal x`.
6. PC 55: JUMPI not-taken extracts bound `x ≤ oldVal` from `lt(oldVal,x) = ⟨0⟩`.
7. PC 56: post-JUMPI-not-taken cascade with bound.
8. PC 57: post-DUP3 cascade.
9. PC 58: post-SWAP1 cascade.
10. PC 59: post-SUB cascade (`UInt256.sub oldVal x`).
11. PC 60: post-SWAP1 cascade — pre-SSTORE [slot, oldVal-x, x].

All 5 rcases lemmas (`WethTrace_decodeSome`, `WethReachable_op_in_allowed`,
`WethReachable_sstore_pc`, `WethReachable_call_pc`, `weth_step_closure`)
updated for each PC.

Framework infrastructure added (committed to `leonardoalt/EVMYulLean`):

* **Strong shape lemmas** (with `accountMap` preservation): DUP1,
  DUP2, DUP3, SWAP1, PUSH (generic n≥1), JUMPI. Plus their PcWalk
  wrappers (`step_*_at_pc_strong`).

The PC 60 disjunct now reads:

```lean
(s.pc.toNat = 60 ∧ s.stack.length = 3 ∧
  ∃ slot oldVal x : UInt256,
    s.stack = slot :: UInt256.sub oldVal x :: x :: [] ∧
    oldVal = (s.accountMap.find? C).option ⟨0⟩
               (Account.lookupStorage (k := slot)) ∧
    x.toNat ≤ oldVal.toNat)
```

## What's left for `pc60_cascade` discharge

The cascade form uses `oldVal = (σ.find? C).option ⟨0⟩ (...)`.
Discharging `WethPC60CascadeFacts` requires `σ.find? C = some acc`
because the framework's `step_SSTORE_accountMap` lemma needs it.

Three paths to close this:

1. **Thread σ-has-C as a `WethReachable` conjunct.** Add `∃ acc,
   s.accountMap.find? C = some acc` to `WethReachable`. Update
   `WethReachable_Z_preserves` (trivial — Z preserves accountMap) and
   `weth_step_closure`. The latter has 64 case branches; for each:
   - Stack-only ops (DUP/SWAP/PUSH/POP/ADD/LT/EQ/etc.):
     `s'.accountMap = s.accountMap` (from strong-shape if used; else
     inline `EVM.step` unfolding).
   - SSTORE (PCs 40, 60): `s'.accountMap = s.accountMap.insert C
     (acc.updateStorage slot newVal)` ⇒ σ' has C.
   - CALL (PC 72): σ' is post-Θ; need framework
     `Θ_preserves_account_at_C` (likely already exists via
     `Λ_invariant_preserved`'s family but not yet exposed).

2. **Weaken `WethPC60CascadeFacts`** to use the option form, and
   add a parallel SSTORE-preservation lemma for the no-C case
   (where `oldVal = ⟨0⟩` ⇒ `x = 0` ⇒ `newVal = sub(0,0) = 0` ⇒
   invariant `0 ≤ 0` holds vacuously). Requires upstream framework
   support for `step_SSTORE_accountMap_general`.

3. **Lift σ-has-C from Ξ entry** as a small, narrow hypothesis at the
   top level (`WethAssumptions.account_at_σ_initial`), then derive
   preservation through the X-loop. This still needs preservation
   threading through `weth_step_closure` but with cleaner top-level
   hypothesis.

Path 1 is most idiomatic. Path 3 is the smallest delta to land. All
three preserve the user's "no opaque axioms" preference while admitting
σ-has-C as either a derived property (paths 1, 2) or a minimal
top-level structural assumption (path 3).

## What's untouched

* **`pc40_cascade`** (deposit SSTORE at PC 40):
  - Cascade through PCs 33–40 (~7 PCs). Pattern identical to the
    PC 47–60 threading; ~600 LoC mechanical.
  - **Additional**: requires the **Θ-pre-credit slack** lifted from
    outside Ξ — the σ_in entry state must carry `β(C) ≥ S(C) +
    msg.value` from Θ's value transfer that occurred before Ξ ran.
    This is a Υ-side fact requiring framework or trace extension; not
    derivable from the per-PC bytecode walk alone.

* **`pc72_cascade`** (CALL at PC 72):
  - Continue cascade through PCs 60–72 (~12 PCs). PCs 61–71 are
    non-storage-touching; cascade preserves trivially.
  - PC 72 disjunct gains the slack `μ₂ + storageSum ≤ balanceOf`
    (post-PC-60 SSTORE-decrement slack) and the call-source/
    call-recipient no-wrap.
  - Combine with `weth_caller_ne_C` for the recipient-≠-C disjunct.

## Total volume estimate

Including σ-has-C threading + pc40 + pc72:
- σ-has-C (path 1 or 3): ~300 LoC.
- pc60 discharge (after σ-has-C): ~50 LoC.
- pc40 cascade threading: ~500 LoC + Θ-pre-credit lift (framework
  extension, hard to estimate).
- pc72 cascade threading: ~600 LoC.

Total: ~1500 LoC + the Θ-pre-credit framework gap.

## Progress this session

12 commits landed. Framework extended with 6 new strong shape
lemmas + 6 PcWalk wrappers. The `pc60_cascade` is structurally
complete in `WethTrace`; only the σ-has-C plumbing separates it from
being a pure theorem.
