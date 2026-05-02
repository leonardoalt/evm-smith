# Infrastructure landed for the WETH solvency proof

This report documents the infrastructure built to support the WETH
solvency proof. After an architectural cleanup, the work splits
cleanly into two halves:

1. **Framework additions** — contract-agnostic, landed inside
   `leonardoalt/EVMYulLean@main` under `EvmYul/Frame/`. Reusable by
   any future single-contract invariant proof.
2. **Consumer-side closure** — the relational-solvency invariant
   chain (`storageSum ≤ balanceOf` plus the full mutual closure that
   preserves it across Υ). Lives at
   `EvmSmith/Demos/Weth/InvariantClosure.lean` in this repository
   (~5400 LoC).

The framework half is the amortizable investment. The consumer-side
half is **not** WETH-specific in shape — the predicate and its
preservation chain don't reference WETH's bytecode at all; only the
*location* is consumer-side, because we currently have one
consumer. Once a second consumer demonstrates the same relational
shape, this content is the natural candidate for lifting back into
the frame library as a parametric module over `I : AccountMap →
AccountAddress → Prop`. For now, future relational-shape proofs
either copy and specialise it, or trigger the lift.

## Repository

- Framework submodule: `EVMYulLean/` (the `EvmYul/Frame/` subtree
  is where the framework additions live).
- Pinned to `leonardoalt/EVMYulLean@main`.
- Consumer-side closure: `EvmSmith/Demos/Weth/InvariantClosure.lean`
  (this repo).

---

# Part 1 — Framework additions

All paths in this section are relative to the `EVMYulLean/` submodule.

## Headline addition: universal `Ξ`-preservation theorem

**`Ξ_preserves_account_at_a_universal : ∀ a, ΞPreservesAccountAt a`**

(In `EvmYul/Frame/MutualFrame.lean`.)

Says: every successful Ξ invocation preserves account presence at any
address. Equivalently: if σ has account at `a` before Ξ runs, then σ' has
it after, regardless of what code Ξ executes.

This is **unconditionally true** because every operation in the EVM
modifies σ only via `insert` (which preserves presence at any address).
SELFDESTRUCT zeroes the executing-frame's balance via `insert` — actual
account deletion happens in Υ's post-tx selfDestructSet processing,
which is *outside* Ξ.

Discharged via mutual fuel induction over Ξ ↔ Θ ↔ Λ ↔ X ↔ EVM.step.

This is the load-bearing addition. It made many downstream theorems
discharge-able.

---

## §I — Θ-side account-presence preservation

Layer 1: leaf lemmas about account-presence under specific σ
manipulations.

| Theorem | What it says |
|---|---|
| `accountPresentAt σ a` | `∃ acc, σ.find? a = some acc` |
| `accountPresentAt_insert` | `insert k v` preserves presence at any address. |
| `theta_σ'₁_preserves_present` | Θ's value-credit prefix preserves presence. |
| `theta_σ₁_preserves_present` | Θ's value-debit prefix preserves presence. |
| `theta_σ'_clamp_preserves_present` | Θ's σ'-clamp preserves presence. |
| `Θ_preserves_account_at_a` | **Full Θ** preserves presence (witness-driven). |
| `EVM_call_preserves_account_at_a` | `EVM.call` wrapper of Θ preservation. |

---

## §J — Universal mutual-induction discharge

Layer 2: per-step preservation, then X-loop induction, then Ξ wrapper.

### §J.1–J.4: per-step preservation

| Theorem | What it says |
|---|---|
| `evmYul_step_SSTORE_preserves_present` | SSTORE step preserves presence. |
| `evmYul_step_TSTORE_preserves_present` | Same for TSTORE. |
| `selfDestruct_preserves_present` | SELFDESTRUCT step (within Θ frame). |
| `binaryStateOp_preserves_present` | Generic binary state-op preservation. |
| `evmYul_step_preserves_present` | **Master** per-op lemma for `EvmYul.step`. |
| `EVM_step_handled_preserves_present` | `EVM.step` for "handled" (non-CALL) ops. |
| `EVM_step_CALL_preserves_present` | CALL step (and CALLCODE / DELEGATECALL / STATICCALL). |
| `EVM_step_preserves_present_no_create` | Universal `EVM.step` dispatcher (CREATE excluded). |

### §J.5: bounded variants for fuel induction

The mutual induction needs predicates parameterized by fuel:

| Predicate | What it says |
|---|---|
| `ΞPreservesAccountAtBdd a f` | Ξ preserves presence at `a` for fuels `≤ f`. |

Plus matching bounded variants of all the per-step / Θ / X / EVM.call
preservation theorems.

### §J.5b: CREATE/CREATE2 preservation (Λ-side)

The hardest single piece. Requires unfolding `EVM.Lambda`'s nested
do-block (which has `MonadLift Option (Except _)` complications and a
`Id.run` for the F-condition).

| Theorem | What it says |
|---|---|
| `Λ_preserves_account_at_a` | Λ preserves presence (witness-driven). |
| `EVM_step_CREATE_preserves_present` | Λ-using EVM.step CREATE arm. |
| `EVM_step_CREATE2_preserves_present` | Same for CREATE2. |
| `EVM_step_preserves_present` | Universal EVM.step (no no-create constraint). |

### §J.5c–J.6: universal closures

| Theorem | What it says |
|---|---|
| `X_preserves_account_at_a_bdd_universal` | X-loop preservation handling `decode = none` via STOP arm. |
| `Ξ_preserves_account_at_a_universal` | The fully universal Ξ preservation. |

### §J.7: Reachable-closure wrappers

Convenience entries for consumers using a `Reachable` predicate:

| Theorem | What it says |
|---|---|
| `Θ_preserves_account_at_a_of_Reachable` | Wraps Θ preservation with Reachable closure. |
| `EVM_call_preserves_account_at_a_of_Reachable` | Same for EVM.call. |
| `Ξ_preserves_account_at_a_of_Reachable_for_C` | Restricted to `I.codeOwner = C`. |

### §J.6.6/.6.7 — `_inv_aware` pres-step variants

These pres-step variants thread the post-step σ-presence through the
`hReach_step` callback. They are parameterised over the consumer's
`Reachable` and don't reference any specific invariant predicate, so
they live framework-side; the consumer-side relational closure (Part
2 below) pairs them with `StorageSumLeBalance` to build its own
slack-dispatch wrapper.

| Theorem | What it says |
|---|---|
| `X_preserves_account_at_a_bdd_op_conditional_with_pres_step` | X-loop variant with σ-presence in step closure. |
| `Ξ_preserves_account_at_a_of_Reachable_for_C_with_pres_step` | Same at Ξ-level. |

---

## Strong shape lemmas

Per-opcode shape lemmas in `EvmYul/Frame/StepShapes.lean` (and `_at_pc`
wrappers in `PcWalk.lean`) that additionally expose `accountMap`
preservation. Used by the WETH-side cascade-threading work to propagate
storage-equality facts through non-storage ops.

| Opcode | Strong shape lemma |
|---|---|
| `SLOAD` | `step_SLOAD_shape_strong` (with codeOwner-storage lookup) |
| `LT` | `step_LT_shape_strong` |
| `SUB` | `step_SUB_shape_strong` |
| `DUP1` | `step_DUP1_shape_strong` |
| `DUP2` | `step_DUP2_shape_strong` |
| `DUP3` | `step_DUP3_shape_strong` |
| `DUP5` | `step_DUP5_shape_strong` |
| `SWAP1` | `step_SWAP1_shape_strong` |
| `PUSH` (generic n≥1) | `step_PUSH_shape_strong` |
| `PUSH1` | `step_PUSH1_shape_strong` |
| `JUMPI` | `step_JUMPI_shape_strong` |
| `JUMPDEST` | `step_JUMPDEST_shape_strong` |
| `POP` | `step_POP_shape_strong` |
| `CALLER` | `step_CALLER_shape_strong` |
| `CALLVALUE` | `step_CALLVALUE_shape_strong` |
| `ADD` | `step_ADD_shape_strong` |
| `GAS` | `step_GAS_shape_strong` |

Each ships with a `_at_pc_strong` wrapper (in `PcWalk.lean`) that
combines the strong shape with PC equality.

---

## StorageSum helpers

In `EvmYul/Frame/StorageSum.lean`:

| Theorem | What it says |
|---|---|
| `storageSum_sstore_replace_eq_findD` | findD-flavored bridge: SSTORE-replace inequality on storageSum. |
| `storageSum_storage_insert_absent_eq` | Inserting into an absent slot. |
| Exposed `storageSum_storage_erase_eq_of_find?_none` | Public visibility of erase-of-absent. |

---

## Generic Υ-tail helpers (storage-sum side)

In `EvmYul/Frame/UpsilonFrame.lean` (parallel to the existing
balance-mono helpers):

| Theorem | What it says |
|---|---|
| `storageSum_tail_generic` | `storageSum` invariant under the post-dispatch Υ tail (gas refund + SD/dead sweeps + tstorage wipe) at any C in the tail's exclusion set. |
| `Υ_tail_storageSum_eq` | Specialisation tying that to the boundary hypotheses (`*SDExclusion`, `*DeadAtσP`). |
| `storageSum_increaseBalance_ne` | `storageSum σ C` invariant under `increaseBalance σ a v` when `a ≠ C`. |

These were promoted to public visibility (alongside the existing
balance-side helpers `balanceOf_tail_generic`,
`Υ_tail_balanceOf_ge`, `dead_increaseBalance_ne`,
`balanceOf_increaseBalance_ne`) so consumer-side relational closures
can compose them directly.

---

## Visibility changes

Seven framework helpers in `UpsilonFrame.lean` flipped from `private`
to public so the consumer-side closure can invoke them:
`storageSum_tail_generic`, `Υ_tail_storageSum_eq`,
`Υ_tail_balanceOf_ge`, `balanceOf_increaseBalance_ne`,
`storageSum_increaseBalance_ne`, `balanceOf_tail_generic`,
`dead_increaseBalance_ne`.

Five in `MutualFrame.lean` likewise: `applyPrecompile_bundled`,
`stateWF_theta_σ₁`, `stateWF_lambda_σStar_some`,
`opIsSystemCallOrCreate`, `op_classification`.

---

## Framework-side volume

- ~17 commits to `MutualFrame.lean`.
- ~5 commits to `StepShapes.lean` / `PcWalk.lean` / `StorageSum.lean`.
- A handful of commits to `UpsilonFrame.lean`.
- ~5000 LoC total framework infrastructure added.

## Framework-side reusability

All framework additions are contract-agnostic. The
`Ξ_preserves_account_at_a_universal` theorem in particular is the kind
of result that's true for any EVM execution and would be needed by any
contract proof that reasons about cross-call account presence.

The pres-step `_inv_aware` variants in §J.6.6/.6.7 are the framework
half of the canonical pattern for any contract proof whose `Reachable`
predicate carries an X-loop invariant — they expose the post-step
σ-presence to the reachability-preservation callback, eliminating the
chicken-and-egg circularity that previously forced consumers to admit
a per-step preservation predicate.

---

# Part 2 — Consumer-side closure (`InvariantClosure.lean`)

In `EvmSmith/Demos/Weth/InvariantClosure.lean`, ~5400 LoC. This file
hosts the **relational-solvency invariant chain** — the
`StorageSumLeBalance` predicate and the full mutual-induction
closure that preserves it across Υ. The closure is generic in
*shape* (no theorem here references WETH's bytecode); it lives
outside the generic framework because we currently have one
consumer. Once a second consumer demonstrates the same shape, this
file is the natural candidate for lifting into `EvmYul/Frame/` as a
parametric module over the invariant `I` — the lift is essentially
a rename + an extra `(I : AccountMap → AccountAddress → Prop)`
parameter on each theorem signature. Brief overview here;
per-theorem details and the proof flow live in `REPORT_WETH.md`.

## What's in it

- **The predicate.**
  `StorageSumLeBalance σ C := storageSum σ C ≤ balanceOf σ C`.
- **§H invariant predicates.** `ΞPreservesInvariantAtC`,
  `ΞInvariantAtCFrame`, `ΞInvariantFrameAtC` — analogues of the
  framework's `ΞPreservesAtC` / `ΞAtCFrame` / `ΞFrameAtC` whose
  success-branch conjunct is `StorageSumLeBalance σ' C` instead of
  `β` monotonicity.
- **§H.2 mutual closure.** `Θ_invariant_preserved_bdd`,
  `Λ_invariant_preserved_bdd`, `Ξ_invariant_preserved_bundled_bdd`,
  `call_invariant_preserved`,
  `ΞPreservesInvariantAtC_of_Reachable_general*` (including the
  `_inv_aware` slack-dispatch variant
  `ΞPreservesInvariantAtC_of_Reachable_general_call_slack_dispatch_inv_aware`,
  which exposes `StorageSumLeBalance s'.accountMap C` to
  `hReach_step`). Joint fuel-induction parallel to the framework's
  balance-mono `Ξ_balanceOf_ge_bundled_bdd` chain.
- **Transaction-level entry.** `Υ_invariant_preserved` — the
  consumer-facing top-level theorem (parametric in the relational
  invariant), plus its Υ-tail wrappers `Υ_tail_invariant_preserves`,
  `Υ_output_invariant_preserves`, and the `ΥBodyFactorsInvariant`
  predicate.
- **Θ-pre-credit slack.** `theta_σ'₁_pre_credit_slack_at_C` — given
  `StorageSumLeBalance σ C` and balance no-wrap, post-credit state
  σ'₁ satisfies `v + storageSum σ'₁ C ≤ balanceOf σ'₁ C` (backs
  WETH's `deposit` slack). Composes
  `theta_σ'₁_storageSum_eq` with balance-delta arithmetic.
- **§H per-step `StorageSumLeBalance` preservation** at non-`C`
  codeOwner — the relational-shape per-step lemmas used by §H.2.

## What it sits on top of (framework-side)

§I/§J (account-presence preservation), the universal Ξ-preservation
result, the strong shape lemmas, and the generic Υ-tail helpers
(both balance-side and storage-sum-side).

## Entry-point simplification

The `Υ_invariant_preserved` entry point was simplified during the
extraction: it previously took a `ΞPreservesInvariantAtC C`
parameter that was structurally unused (passed through to
`Υ_output_invariant_preserves` as `_hWitness`, never consumed).
Dropping the parameter simplified the consumer interface and
eliminated the chain that required `account_at_initial` as a
structural assumption in WETH's proof.

---

## Axioms unchanged

These additions introduce zero new axioms. The framework still has
exactly the two axioms documented in
`EVMYulLean/FRAME_LIBRARY.md`'s audit
(`precompile_preserves_accountMap`, `lambda_derived_address_ne_C`).
The consumer-side closure adds none.
