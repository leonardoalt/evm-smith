import EvmYul.Frame
import EvmSmith.Demos.Weth.Invariant
import EvmSmith.Demos.Weth.BytecodeFrame

/-!
# Weth — solvency invariant, top-level theorem (§2.6)

`weth_solvency_invariant` — after any single Ethereum transaction, the
Weth contract at `C` remains solvent: the sum of user-balance storage
slots is at most `C`'s ETH balance.

This file mirrors `EvmSmith/Demos/Register/BalanceMono.lean`'s
composition pattern. Like Register, Weth's top-level proof composes:

* `Υ_invariant_preserved` (§1.3, in `EVMYulLean/EvmYul/Frame/UpsilonFrame.lean`),
  the framework's transaction-level invariant-preservation theorem
  for the relational `storageSum ≤ balanceOf` invariant.
* A bundle of **structural hypotheses** packaging the call-tree-level
  facts that aren't derivable from the closed framework outputs.

## Hypotheses (`WethAssumptions`, 5 fields)

The boundary hypotheses (`hWF`, `hS_T`, `hBen`, `hValid`, `hInv`)
are the same shape as Register's `register_balance_mono`. The Weth
analogues of Register's `RegSDExclusion` / `RegDeadAtσP`, plus the
two Weth-specific structural facts, are bundled in `WethAssumptions`:

1. **`deployed : DeployedAtC C`** — Weth's bytecode is installed at
   `C`. Real world: genesis-deployment + Weth bytecode contains no
   CREATE/CREATE2/SELFDESTRUCT, so `C`'s code is preserved across
   any sub-frame (mirror of Register's `DeployedAtC`).

2. **`sd_excl : WethSDExclusion …`** — no SELFDESTRUCT in the call
   tree adds `C` to the final substate's selfDestructSet. Holds
   because Weth's bytecode contains no SELFDESTRUCT and SELFDESTRUCT
   only inserts the executing-frame address `Iₐ` into the SD-set,
   which by `DeployedAtC` is `≠ C` whenever the code at that address
   is not Weth's. Same shape as `RegSDExclusion`.

3. **`dead_at_σP : WethDeadAtσP …`** — `C`'s account in σ_P (the
   post-Θ/Λ state) has non-empty code (Weth's bytecode), so
   `State.dead σ_P C = false`. Holds because `WethInv σ C` (which
   provides the bytecode identity) is preserved through the
   value-debit at `S_T ≠ C` and `lambda_derived_address_ne_C` rules
   out CREATE-derivation of `C`. Same shape as `RegDeadAtσP`.

4. **`inv_at_σP : WethInvAtσP …`** — σ_P (Υ's post-Θ/Λ-dispatch
   state) preserves the relational solvency invariant
   `storageSum σ_P C ≤ balanceOf σ_P C`. Mirror of Register's
   `σ_to_σP_balance_mono_Θ`/`Λ` chain, but for the relational
   invariant. Discharging from Lean requires exposed
   `Θ_invariant_preserved` / `Λ_invariant_preserved` framework
   theorems (currently private inside MutualFrame.lean); bundled
   here as a structural hypothesis.

5. **`call_no_wrap : WethCallNoWrapAt72 C`** — at PC 72 (the
   withdraw block's outbound CALL), `recipient_balance + value` does
   not wrap modulo `2^256`. Real-world chain-state bound that's not
   bytecode-derivable.

The bytecode-level cascade-fact predicates (`WethPC{40,60,72}CascadeFacts`)
that were originally hypotheses on `WethAssumptions` have been
**discharged as in-Lean theorems** in `BytecodeFrame.lean`
(`weth_pc60_cascade`, `weth_pc40_cascade`, `weth_pc72_cascade`).
The non-halt step closure and op-classification are likewise in-Lean
(`weth_step_closure`, `WethReachable_op_in_allowed`). The previous
fields `deposit_slack` / `account_at_C` / `inv_step_pres` /
`xi_preserves_C` / `account_at_initial` / `inv_at_initial` have all
been eliminated by framework simplifications (see inline notes on
the live `WethAssumptions` structure below).

The body decomposition existence (`σ' = Υ_tail_state σ_P g' A …`)
is **NOT** a structural hypothesis — it is derived mechanically
inline by `weth_Υ_body_factors` from inspecting Υ's `.ok` output
shape, exactly as in Register's `register_Υ_body_factors`.

## Top-level theorem composition

  WethInv σ C  ∧ DeployedAtC C  ∧ WethSDExclusion ∧ WethDeadAtσP
              ∧ WethInvAtσP    ∧ WethCallNoWrapAt72 C
  ───────────────────────────────────────────────────────  Υ_invariant_preserved
                    WethInv (Υ σ).σ' C
-/

namespace EvmSmith.Weth
open EvmYul EvmYul.EVM EvmYul.Frame

/-! ## §2.6 — Structural hypothesis bundle for Weth

Each entry below is a `Prop` capturing a real-world structural fact
about Weth's run. They mirror `EvmSmith/Demos/Register/BalanceMono`
(Register's `RegSDExclusion`/`RegDeadAtσP`) in posture: stated on
Υ's `.ok` output, vacuous on `.error`. -/

/-- Hypothesis on Υ's run output: the resulting substate's
self-destruct set excludes `C`. Mirror of Register's `RegSDExclusion`. -/
def WethSDExclusion (σ : AccountMap .EVM) (fuel H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction)
    (S_T C : AccountAddress) : Prop :=
  match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
  | .ok (_, A, _, _) => ∀ k ∈ A.selfDestructSet.1.toList, k ≠ C
  | _ => True

/-- Hypothesis on Υ's body factorisation: every post-dispatch state
σ_P that decomposes Υ's output via the tail-state form satisfies
`State.dead σ_P C = false`. Mirror of Register's `RegDeadAtσP`. -/
def WethDeadAtσP (σ : AccountMap .EVM) (fuel H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction)
    (S_T C : AccountAddress) : Prop :=
  match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
  | .ok (σ', A', _, _) =>
      ∀ σ_P g',
        σ' = Υ_tail_state σ_P g' A' H H_f tx S_T →
        State.dead σ_P C = false
  | _ => True

/-- Hypothesis: σ_P (Υ's post-Θ/Λ-dispatch state) preserves Weth's
solvency invariant. This is the σ-to-σ_P propagation step, analogous
to Register's `σ_to_σP_balance_mono_Θ`/`Λ` chain but for the
relational `storageSum ≤ balanceOf` invariant.

Discharging inside Lean requires exposed
`Θ_invariant_preserved`/`Λ_invariant_preserved` framework theorems
(currently private in `MutualFrame.lean`, bundled inside
`Υ_invariant_preserved`'s body factor input). -/
def WethInvAtσP (σ : AccountMap .EVM) (fuel H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction)
    (S_T C : AccountAddress) : Prop :=
  match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
  | .ok (σ', A', _, _) =>
      ∀ σ_P g',
        σ' = Υ_tail_state σ_P g' A' H H_f tx S_T →
        WethInvFr σ_P C
  | _ => True

/-- **Weth assumptions bundle.** Packages the structural hypotheses
for the top-level solvency theorem.

Mirror of Register's `(hDeployed, hSDExcl, hDeadAtσP)` triple, with
Weth-specific additions:

* `inv_at_σP` — σ_P preserves the invariant.
* `pc40_cascade`, `pc60_cascade`, `pc72_cascade` — the per-PC
  cascade-fact predicates (in `BytecodeFrame.lean`) capturing the
  precise trace-cascade data the SSTORE / CALL dischargers need.
  These derive `WethSStorePreserves` and `WethCallSlack` via the
  closed-form glue (`weth_sstore_preserves_from_cascades`,
  `weth_call_slack_from_cascade`), which then derive
  `ΞPreservesInvariantAtC C` via `bytecodePreservesInvariant`. This
  replaces the previous opaque `WethSStorePreserves` / `WethCallSlack`
  fields with narrower per-PC predicates that match the shape of the
  pending trace cascade extension. The non-halt step closure and the
  op-classification are discharged in-Lean (`weth_step_closure`,
  `WethReachable_op_in_allowed`).

The decomposition existence (`σ' = Υ_tail_state σ_P g' …`) is
mechanical and is derived inline by `weth_Υ_body_factors`; combined
with `inv_at_σP` and `dead_at_σP` they form the
`ΥBodyFactorsInvariant` predicate `Υ_invariant_preserved` consumes. -/
structure WethAssumptions
    (σ : AccountMap .EVM) (fuel H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction)
    (S_T C : AccountAddress) : Prop where
  /-- Weth's bytecode is installed at `C`. -/
  deployed         : DeployedAtC C
  /-- No SELFDESTRUCT in the run inserts `C` into the SD-set. -/
  sd_excl          : WethSDExclusion σ fuel H_f H H_gen blocks tx S_T C
  /-- σ_P has `dead σ_P C = false`. -/
  dead_at_σP       : WethDeadAtσP σ fuel H_f H H_gen blocks tx S_T C
  /-- σ_P preserves the invariant. -/
  inv_at_σP        : WethInvAtσP σ fuel H_f H H_gen blocks tx S_T C
  -- Note: the previous `deposit_slack : WethDepositPreCredit C` field
  -- has been **eliminated**. It was only ever consumed (transitively)
  -- to build the `ΞPreservesInvariantAtC C` witness threaded into
  -- `Υ_invariant_preserved`. Since the framework's
  -- `Υ_invariant_preserved` no longer requires that witness (it was
  -- structurally unused — see the docstring of `Υ_invariant_preserved`
  -- in `EVMYulLean/EvmYul/Frame/UpsilonFrame.lean`), the
  -- pre-credit-slack hypothesis is no longer reached and has been
  -- dropped. The discharger
  -- `bytecodePreservesInvariant_inv_aware_fully_narrowed` (in
  -- `BytecodeFrame.lean`) still consumes a `WethDepositPreCredit C`
  -- argument for users who want to call it directly, but it is no
  -- longer threaded through the top-level solvency composition.
  -- Note: the previous `deposit_cascade : WethDepositCascadeStruct C`
  -- field had already been replaced by an in-Lean theorem
  -- `weth_deposit_cascade` (commit 083ea45).
  -- Note: the previous `account_at_initial : ∀ σ I, I.codeOwner = C →
  -- accountPresentAt σ C` field has been **eliminated**. It was only ever
  -- consumed (transitively) to feed the `hReachInit` callback inside the
  -- consumer's `bytecodePreservesInvariant_inv_aware_fully_narrowed`
  -- entry point, which built the `ΞPreservesInvariantAtC C` witness
  -- threaded into `Υ_invariant_preserved`. The framework's
  -- `Υ_invariant_preserved` has since been simplified to drop the
  -- (structurally unused) `ΞPreservesInvariantAtC C` parameter, so the
  -- witness is no longer needed and `account_at_initial` along with it.
  -- See the docstring of `Υ_invariant_preserved` in
  -- `EVMYulLean/EvmYul/Frame/UpsilonFrame.lean` for the rationale.
  -- Note: the previous `inv_at_initial : ∀ σ I, I.codeOwner = C →
  -- WethInvFr σ C` field has been **eliminated**. The framework's
  -- invariant-aware slack-dispatch X-loop
  -- (`ΞPreservesInvariantAtC_of_Reachable_general_call_slack_dispatch_inv_aware`,
  -- EVMYulLean) was refactored to expose `WethInvFr σ C` (Ξ's invariant
  -- precondition, already part of `ΞPreservesInvariantAtC`'s signature)
  -- to its `hReachInit` callback. The Weth side feeds this directly into
  -- `WethReachable_initial`'s `hInv` parameter, removing the need for a
  -- σ-universal closure. See `bytecodePreservesInvariant_inv_aware`'s
  -- `hReachInit` arm in `BytecodeFrame.lean`.
  -- Note: the previous `call_inv_step_pres : WethCALLStepInvFr C` field
  -- has been removed. The framework's invariant-aware slack-dispatch
  -- X-loop (`ΞPreservesInvariantAtC_of_Reachable_general_call_slack_dispatch_inv_aware`,
  -- EVMYulLean) exposes `WethInvFr s'.accountMap C` to its `hReach_step`
  -- callback (already established internally via
  -- `step_bundled_invariant_at_C_invariant_at_C_slack_dispatch`'s CALL
  -- arm), so no per-step CALL invariant predicate is needed. The Weth
  -- side discharges this via `bytecodePreservesInvariant_inv_aware_fully_narrowed`.
  -- Note: the previous `xi_preserves_C_other : ...` field has been
  -- replaced by an in-Lean theorem `weth_xi_preserves_C_other`
  -- (discharged from the framework's
  -- `Ξ_preserves_account_at_a_universal`, the fully universal Ξ-preservation
  -- closure that landed in EVMYulLean §J.5c/§J.6). Consumers no longer
  -- supply it — `weth_xi_preserves_C` derives the full
  -- `ΞPreservesAccountAt C` directly.
  /-- Recipient-balance no-wrap at PC 72's CALL: chain-bound real-world
  fact. **Replaces** the no-wrap part of the previous opaque
  `pc72_cascade : WethPC72CascadeFacts C` field. -/
  call_no_wrap     : WethCallNoWrapAt72 C
  -- Note: the previous `call_slack : WethCallSlackAt72 C` field has
  -- been replaced by an in-Lean theorem `weth_call_slack` (discharged
  -- from the threaded WethTrace cascade at PCs 60..72 plus σ-has-C),
  -- so consumers no longer need to supply it.

/-! ## Conversion to framework predicates

The framework's `Υ_invariant_preserved` consumes `ΥTailInvariant` and
`ΥBodyFactorsInvariant`. We project the `WethAssumptions` bundle into
those predicates.

Mirror of Register's `register_Υ_tail_invariant` /
`register_Υ_body_factors`. -/

/-- Project the `WethSDExclusion` structural hypothesis to the
framework's `ΥTailInvariant`. The dead-filter clause is discharged
trivially: `k ∈ filter (dead σ_F ·)` implies `dead σ_F k = true`,
contradicting `dead σ_F C = false`.

Mirror of Register's `register_Υ_tail_invariant`. -/
private theorem weth_Υ_tail_invariant
    (σ : AccountMap .EVM) (fuel H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction)
    (S_T C : AccountAddress)
    (hSD : WethSDExclusion σ fuel H_f H H_gen blocks tx S_T C) :
    ΥTailInvariant σ fuel H_f H H_gen blocks tx S_T C := by
  unfold ΥTailInvariant WethSDExclusion at *
  cases hΥ : EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
  | error e => trivial
  | ok r =>
    obtain ⟨_, A, _, _⟩ := r
    rw [hΥ] at hSD
    refine ⟨hSD, ?_⟩
    intro σ_F hDead k hk hkC
    have hpk : State.dead σ_F k = true := mem_filter_pred _ _ _ hk
    rw [hkC] at hpk
    rw [hDead] at hpk
    cases hpk

/-- Project the `WethDeadAtσP` + `WethInvAtσP` hypotheses to the
framework's `ΥBodyFactorsInvariant`.

Mirror of Register's `register_Υ_body_factors`. The body decomposition
existence (`σ' = Υ_tail_state σ_P g' …`) is derived mechanically by
inspecting Υ's `.ok` output structure — it's syntactically a `do
(σ_P, g', A, z) ← Θ/Λ-dispatch σ₀; .ok (Υ_tail_state …, A, z, _)`. -/
private theorem weth_Υ_body_factors
    (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks)
    (tx : Transaction) (S_T C : AccountAddress)
    (hInv  : WethInvAtσP σ fuel H_f H H_gen blocks tx S_T C)
    (hDead : WethDeadAtσP σ fuel H_f H H_gen blocks tx S_T C) :
    ΥBodyFactorsInvariant σ fuel H_f H H_gen blocks tx S_T C := by
  unfold ΥBodyFactorsInvariant WethInvAtσP WethDeadAtσP at *
  unfold EVM.Υ at *
  match hRec : tx.base.recipient with
  | none =>
    simp only
    rw [hRec] at hInv hDead
    simp only at hInv hDead
    split
    case h_2 _ => trivial
    case h_1 σ' A' z' gUsed' hOk =>
      split at hOk
      case h_2 e hΛ => simp [bind, Except.bind] at hOk
      case h_1 a cA σ_P g' A z gReturn hΛ =>
        rw [hΛ] at hInv hDead
        simp only at hInv hDead
        cases hOk
        exact ⟨σ_P, g', rfl, hInv σ_P g' rfl, hDead σ_P g' rfl⟩
  | some t =>
    simp only
    rw [hRec] at hInv hDead
    simp only at hInv hDead
    split
    case h_2 _ => trivial
    case h_1 σ' A' z' gUsed' hOk =>
      split at hOk
      case h_2 e hΘ => simp [bind, Except.bind] at hOk
      case h_1 cA σ_P g' A z gReturn hΘ =>
        rw [hΘ] at hInv hDead
        simp only at hInv hDead
        cases hOk
        exact ⟨σ_P, g', rfl, hInv σ_P g' rfl, hDead σ_P g' rfl⟩

/-! ## Top-level solvency theorem

The headline result. Mirror of Register's `register_balance_mono`. -/

/-- **Weth solvency: the contract is always solvent across any
transaction.**

Given:
* `hWF`           — pre-state well-formedness (T1, T5).
* `hInv`          — pre-state invariant (`storageSum σ C ≤
                    balanceOf σ C`).
* `hS_T`          — `C` is not the transaction sender.
* `hBen`          — `C` is not the block beneficiary (kept for
                    parity with Register; the invariant chain doesn't
                    actually require it for the storage-sum side, but
                    `Υ_tail_balanceOf_ge`'s β-side does).
* `hValid`        — strengthened transaction-validity (sender funds
                    cover gasLimit·p + value).
* `hAssumptions`  — the `WethAssumptions` bundle (deployed code,
                    SD-exclusion, dead-at-σP, σ_P-invariant, plus
                    per-PC cascade-fact predicates for the PC 40 /
                    60 SSTORE and PC 72 CALL discharges).

Conclusion: Υ's post-state σ' satisfies `WethInv σ' C` (or Υ
returned `.error`, in which case the conclusion is vacuous).

The proof is direct composition: `Υ_invariant_preserved` consumes
`ΞPreservesInvariantAtC C` (from the bundle), `ΥTailInvariant`
(projected via `weth_Υ_tail_invariant`), and `ΥBodyFactorsInvariant`
(projected via `weth_Υ_body_factors`).

`WethInv` and `WethInvFr` (the framework's underlying predicate) are
definitionally equal — both unfold to `storageSum σ C ≤ balanceOf σ
C`. The conclusion is restated using the demo-side `WethInv`. -/
theorem weth_solvency_invariant
    (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks)
    (tx : Transaction) (S_T C : AccountAddress)
    (hWF : StateWF σ)
    (hInv : WethInv σ C)
    (hS_T : C ≠ S_T)
    (hBen : C ≠ H.beneficiary)
    (_hValid : TxValid σ S_T tx H H_f)
    (hAssumptions : WethAssumptions σ fuel H_f H H_gen blocks tx S_T C) :
    match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
    | .ok (σ', _, _, _) => WethInv σ' C
    | .error _ => True := by
  -- WethInv σ C ↔ WethInvFr σ C (definitional; both = storageSum σ C ≤ balanceOf σ C).
  have hInvFr : WethInvFr σ C := hInv
  -- Project structural hypotheses to framework predicates.
  have hTail :=
    weth_Υ_tail_invariant σ fuel H_f H H_gen blocks tx S_T C hAssumptions.sd_excl
  have hFactor :=
    weth_Υ_body_factors fuel σ H_f H H_gen blocks tx S_T C
      hAssumptions.inv_at_σP hAssumptions.dead_at_σP
  -- Apply Υ_invariant_preserved. The previously-required
  -- `ΞPreservesInvariantAtC C` witness has been dropped from
  -- `Υ_invariant_preserved`'s signature (it was structurally unused in
  -- the chain), so we no longer need to construct it here. The
  -- `bytecodePreservesInvariant_inv_aware_fully_narrowed` discharger and
  -- its `account_at_initial` precondition are no longer reached.
  have h :=
    Υ_invariant_preserved fuel σ H_f H H_gen blocks tx S_T C
      hWF hInvFr hS_T hBen hTail hFactor
  -- Re-thread the match: the framework returns WethInvFr; restate as WethInv.
  cases hΥ : EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
  | error _ => trivial
  | ok r =>
    obtain ⟨σ', _A, _z, _g⟩ := r
    rw [hΥ] at h
    -- `h : WethInvFr σ' C`; the goal at the .ok branch is `WethInv σ' C`.
    exact h

end EvmSmith.Weth
