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

## Hypotheses (from `SOLVENCY_PLAN.md` and `ASSUMPTIONS.md`)

The boundary hypotheses (`hWF`, `hS_T`, `hBen`, `hValid`, `hInv`)
are the same shape as Register's `register_balance_mono`. The Weth
analogues of Register's `RegSDExclusion` / `RegDeadAtσP` are bundled
in `WethAssumptions`:

1. **`DeployedAtC C`** — Weth's bytecode is installed at `C`. Real
   world: genesis-deployment + Weth bytecode contains no
   CREATE/CREATE2/SELFDESTRUCT, so `C`'s code is preserved across
   any sub-frame (mirror of Register's `DeployedAtC`).

2. **`WethSDExclusion`** — no SELFDESTRUCT in the call tree adds `C`
   to the final substate's selfDestructSet. Holds because Weth's
   bytecode contains no SELFDESTRUCT and SELFDESTRUCT only inserts
   the executing-frame address `Iₐ` into the SD-set, which by
   `DeployedAtC` is `≠ C` whenever the code at that address is not
   Weth's. Same shape as `RegSDExclusion`.

3. **`WethDeadAtσP`** — `C`'s account in σ_P (the post-Θ/Λ state)
   has non-empty code (Weth's bytecode), so `State.dead σ_P C =
   false`. Holds because `WethInv σ C` (which provides the bytecode
   identity) is preserved through the value-debit at `S_T ≠ C` and
   `lambda_derived_address_ne_C` rules out CREATE-derivation of `C`.
   Same shape as `RegDeadAtσP`.

4. **Bytecode-level cascade-fact hypotheses** (`pc40_cascade`,
   `pc60_cascade`, `pc72_cascade`) — the `ΞPreservesInvariantAtC C`
   witness is derived inline by `bytecodePreservesInvariant` (in
   `BytecodeFrame.lean`) from these structural facts via the
   `weth_sstore_preserves_from_cascades` and
   `weth_call_slack_from_cascade` glue lemmas. The non-halt step
   closure (formerly the `step_closure` field) is derived in-Lean by
   `weth_step_closure` (aggregating the 61 per-PC walks); the
   op-classification (formerly `op_reach`) is also in-Lean
   (`WethReachable_op_in_allowed`). The cascade-fact predicates
   `WethPC{40,60,72}CascadeFacts` capture exactly the per-PC
   trace-cascade data needed for the SSTORE / CALL discharge — this
   refines the previous opaque `WethSStorePreserves` / `WethCallSlack`
   fields to the precise narrower predicates the trace cascade
   extension would establish (PC 48 SLOAD → PC 60 SSTORE → PC 72 CALL
   propagation; see `BytecodeFrame.lean`'s `WethPC60CascadeFacts`
   docstring for the cascade roadmap).

5. **`WethInvAtσP`** — σ_P (Υ's post-Θ/Λ-dispatch state) preserves
   the relational solvency invariant `storageSum σ_P C ≤ balanceOf
   σ_P C`. Mirror of Register's `σ_to_σP_balance_mono_Θ`/`Λ` chain
   for the relational invariant. Discharging from Lean requires
   exposed `Θ_invariant_preserved` / `Λ_invariant_preserved`
   framework theorems (currently private inside MutualFrame.lean);
   bundled here as a structural hypothesis.

The body decomposition existence (`σ' = Υ_tail_state σ_P g' A …`)
is **NOT** a structural hypothesis — it is derived mechanically
inline by `weth_Υ_body_factors` from inspecting Υ's `.ok` output
shape, exactly as in Register's `register_Υ_body_factors`.

The remaining decomposition into structural hypotheses follows
Register's posture: real-world facts captured precisely, with
discharge deferred to the relevant framework strengthening pass.

## Top-level theorem composition

  WethInv σ C  ∧ DeployedAtC C  ∧ WethSDExclusion ∧ WethDeadAtσP
              ∧ WethInvAtσP    ∧ ΞPreservesInvariantAtC C
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
  /-- Bytecode-derivable cascade structure at PC 40 (deposit SSTORE):
  stack[0] = sender, stack[1] = newBal, σ has C with the sender's
  storage slot present. **Bytecode-derivable in principle** via
  cascade threading PCs 32..40 (same pattern as PCs 47..60 already
  done for pc60). Pending that threading, kept as a structural
  assumption. -/
  deposit_cascade  : WethDepositCascadeStruct C
  /-- Θ-pre-credit slack at PC 40: `storageSum - oldVal + newVal ≤
  balanceOf` at PC 40. This is the **Υ-side** fact: `msg.value` was
  added to C's balance by Θ before Ξ entered, so the post-SSTORE
  storageSum (= storageSum + msg.value) is bounded by the post-Θ
  balance. **Cannot be derived from bytecode walks alone** — it
  lives in the framework's outer Θ/Λ layer. -/
  deposit_slack    : WethDepositPreCredit C
  /-- σ-has-C invariant: every Weth-reachable state has σ.find? C = some _.

  This **replaces** the previous opaque `pc60_cascade : WethPC60CascadeFacts C`
  field. The PC 60 cascade-fact predicate is now a **theorem**
  (`weth_pc60_cascade`), discharged from the threaded `WethTrace`
  cascade (PCs 47..60) plus this narrower σ-has-C fact.

  Why σ-has-C is true: Weth's bytecode has no SELFDESTRUCT, and Ξ
  enters at C with σ[C] = some _ (framework guarantee from Λ's
  account-at-codeOwner setup). Across the X loop, only SSTORE
  (modifies storage but preserves account presence) and CALL (Θ
  preserves σ at the source address) touch σ at C, neither removes
  it.

  Discharging this from Lean requires extending `WethReachable`'s
  preservation across `weth_step_closure` cases (or exposing a
  framework-level "Reachable preserves σ-at-codeOwner" helper). For
  now it remains a structural fact bundled with the assumption set;
  it is **strictly narrower** than the prior opaque cascade-fact
  field, since it asserts only account presence (one bit), not the
  full per-PC cascade data. -/
  account_at_C     : WethAccountAtC C
  /-- Recipient-balance no-wrap at PC 72's CALL: chain-bound real-world
  fact. **Replaces** the no-wrap part of the previous opaque
  `pc72_cascade : WethPC72CascadeFacts C` field. -/
  call_no_wrap     : WethCallNoWrapAt72 C
  /-- Post-SSTORE slack at PC 72: μ₂ + storageSum ≤ balanceOf, plus
  caller-account-found-with-balance-≥-μ₂ in the cumbersome
  `AccountAddress.ofUInt256 (.ofNat codeOwner)` form. **Replaces** the
  slack/funds parts of the previous opaque `pc72_cascade` field.
  Derivable from threading the post-PC-60-SSTORE invariant through
  PCs 61..72 (pending `WethReachable`/WethInvFr extension). -/
  call_slack       : WethCallSlackAt72 C

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
  -- Derive ΞPreservesInvariantAtC C directly from the per-PC
  -- cascade-fact predicates via `bytecodePreservesInvariant_from_cascades`,
  -- which composes the closed-form glue lemmas
  -- (`weth_sstore_preserves_from_cascades`,
  -- `weth_call_slack_from_cascade`) with `bytecodePreservesInvariant`.
  -- The non-halt step closure is derived in-Lean by `weth_step_closure C`
  -- inside the discharger, so consumers no longer supply it.
  have hXi : ΞPreservesInvariantAtC C :=
    bytecodePreservesInvariant_fully_narrowed C
      hAssumptions.deployed hAssumptions.account_at_C
      hAssumptions.call_no_wrap hAssumptions.call_slack
      hAssumptions.deposit_cascade hAssumptions.deposit_slack
  -- Apply Υ_invariant_preserved.
  have h :=
    Υ_invariant_preserved fuel σ H_f H H_gen blocks tx S_T C
      hWF hInvFr hS_T hBen hXi hTail hFactor
  -- Re-thread the match: the framework returns WethInvFr; restate as WethInv.
  cases hΥ : EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
  | error _ => trivial
  | ok r =>
    obtain ⟨σ', _A, _z, _g⟩ := r
    rw [hΥ] at h
    -- `h : WethInvFr σ' C`; the goal at the .ok branch is `WethInv σ' C`.
    exact h

end EvmSmith.Weth
