# Framework infrastructure landed in EVMYulLean

This report documents the additions to the upstream EVMYulLean
framework (`leonardoalt/EVMYulLean`) needed to support the WETH
solvency proof.

## Repository

- Submodule: `EVMYulLean/` (the `EvmYul/Frame/` subtree is where the
  framework additions live).
- Pinned to `leonardoalt/EVMYulLean@main`.

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

### §J.6.6/.6.7 — `_inv_aware` variants

The framework's `hReach_step` callback didn't expose `StorageSumLeBalance s'.accountMap C`
to consumers, even though the X-loop's induction has it locally. This
caused a chicken-and-egg circularity for any contract whose Reachable
predicate depends on the invariant.

The `_inv_aware` variants thread the post-step invariant through:

| Theorem | What it says |
|---|---|
| `X_preserves_account_at_a_bdd_op_conditional_with_pres_step` | X-loop variant with σ-presence in step closure. |
| `Ξ_preserves_account_at_a_of_Reachable_for_C_with_pres_step` | Same at Ξ-level. |
| `ΞPreservesInvariantAtC_of_Reachable_general_call_slack_dispatch_inv_aware` | Slack-dispatch variant exposing `StorageSumLeBalance s'.accountMap C` to `hReach_step`. |

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

## UpsilonFrame simplification

`Υ_invariant_preserved` previously took a `ΞPreservesInvariantAtC C`
parameter that was structurally unused (passed through to
`Υ_output_invariant_preserves` as `_hWitness`, never consumed). Drop
the parameter to simplify the consumer interface.

This eliminated the chain that required `account_at_initial` as a
structural assumption in WETH's proof.

---

## Θ-pre-credit framework lemma

| Theorem | What it says |
|---|---|
| `theta_σ'₁_pre_credit_slack_at_C` | Given `StorageSumLeBalance σ C` and balance no-wrap, post-credit state σ'₁ satisfies `v + storageSum σ'₁ C ≤ balanceOf σ'₁ C`. |

Composes the existing `theta_σ'₁_storageSum_eq` (storage unchanged at
C through credit) with balance-delta arithmetic
(`balanceOf σ'₁ C = balanceOf σ C + v` at recipient = C). Backs the
Θ-pre-credit fact for any consumer that needs it.

---

## Total volume

- ~17 commits to `MutualFrame.lean`.
- ~5 commits to `StepShapes.lean` / `PcWalk.lean` / `StorageSum.lean`.
- 1 commit to `UpsilonFrame.lean`.
- ~5000 LoC total framework infrastructure added.

## Reusability

All framework additions are contract-agnostic. The
`Ξ_preserves_account_at_a_universal` theorem in particular is the kind
of result that's true for any EVM execution and would be needed by any
contract proof that reasons about cross-call account presence.

The `_inv_aware` variants are the canonical pattern for any contract
proof whose `Reachable` predicate carries an X-loop invariant: the
framework now exposes the post-step invariant directly to the
reachability-preservation callback, breaking the chicken-and-egg
circularity that previously forced consumers to admit a per-step
invariant-preservation predicate.
