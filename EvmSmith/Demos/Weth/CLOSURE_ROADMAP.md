# Weth solvency proof — closure roadmap

**State**: `weth_solvency_invariant` is typed and proved as a Lean
theorem. Build green, 2 axioms (T2 + T5), 0 sorries. The theorem is
conditional on `WethAssumptions` (7 fields).

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

## What each cascade-fact says (in plain English)

* **`pc60_cascade`**: at any reachable state about to execute the
  SSTORE at PC 60, the EVM stack and storage are in the form expected
  by the withdraw flow: `slot = sender_uint`, `oldVal = current
  storage at slot`, `newVal ≤ oldVal` (verified by the LT/JUMPI gate
  at PCs 51/55 + the SUB at PC 58).
* **`pc40_cascade`**: at any reachable state about to execute the
  SSTORE at PC 40, the deposit flow's pre-credit slack `storageSum -
  oldVal + newVal ≤ balanceOf` holds, courtesy of Θ's value transfer
  before Ξ entered.
* **`pc72_cascade`**: at any reachable state about to execute the
  CALL at PC 72, the framework's slack-callback preconditions hold —
  specifically `μ₂ + storageSum ≤ balanceOf` (post-PC-60
  SSTORE-decrement slack) and the call-source/call-recipient
  no-wrap.

## Framework infrastructure already in place (reusable)

All landed and pushed to `leonardoalt/EVMYulLean@main`:

* **Strong shape lemmas** in `StepShapes.lean`: `step_SLOAD_shape_strong`,
  `step_LT_shape_strong`, `step_SUB_shape_strong` (expose the
  pushed value's semantic identity, not just its existence).
* **Strong PcWalk wrappers**: `step_SLOAD_at_pc_strong`,
  `step_LT_at_pc_strong`, `step_SUB_at_pc_strong`.
* **Storage-sum primitives** in `StorageSum.lean`:
  `storageSum_sstore_replace_eq`, `storageSum_sstore_erase_eq`,
  `storageSum_old_le`, `storageSum_sstore_replace_eq_findD` (the
  findD-flavored bridge that matches SLOAD's actual semantics).
* **MutualFrame parallel mutual closure**: `Θ_invariant_preserved_bdd`,
  `Λ_invariant_preserved_bdd`, `Ξ_invariant_preserved_bundled_bdd`,
  `call_invariant_preserved` (handles at-C CALL with `value ≠ 0`).
* **Slack-dispatch consumer entry**:
  `ΞPreservesInvariantAtC_of_Reachable_general_call_slack_dispatch`
  (takes per-state slack-callback instead of `v=0`).

## Weth-side infrastructure already in place

* **`WethTrace`** (line 94 of BytecodeFrame.lean): 64-disjunct
  enumeration of reachable PCs + stack lengths.
* **61 per-PC `WethTrace_step_at_*` walks**: cover the entire 86-byte
  bytecode.
* **Narrowing lemmas**: `WethReachable_sstore_pc` (narrows reachable
  SSTORE states to PCs {40, 60}), `WethReachable_call_pc` (narrows to
  PC 72).
* **`WithdrawCascadeAt`**: helper predicate (line 416) capturing the
  cascade invariant.
* **EVM-step→cascade bridges**: `WethInvFr_step_SSTORE_at_C_replace_decr`,
  `WethInvFr_step_SSTORE_at_C_erase`,
  `WethInvFr_step_SSTORE_at_C_replace_with_slack`.
* **Closed-form glue**: `weth_sstore_preserves_pc60_from_cascade`,
  `weth_sstore_preserves_pc40_from_cascade`,
  `weth_sstore_preserves_from_cascades`,
  `weth_call_slack_from_cascade`.
* **`bytecodePreservesInvariant_from_cascades`**: convenience entry
  taking the three cascade-fact predicates directly.

## What's left — the cascade threading

For each cascade-fact predicate, the discharge requires extending
the `WethTrace` predicate's per-PC disjuncts to carry cascade
witnesses, then threading them through the per-PC walks. Each PC
extension touches:

* the disjunct in `WethTrace` (~5 lines),
* the disjunct in `mk_wethTrace_aux` smart constructor (~5 lines),
* 5 rcases lemmas (`WethTrace_decodeSome`, `WethReachable_op_in_allowed`,
  `WethReachable_sstore_pc`, `WethReachable_call_pc`,
  `weth_step_closure`) — typically just `_` to absorb the new
  conjunct (~3 lines × 5 = 15 lines),
* the per-PC walk that produces the disjunct (~30-50 lines),
* the per-PC walk that consumes it (~5-10 lines).

### Concrete pieces

**`pc60_cascade` discharge** (~1500 LoC):
* Strengthen `WethTrace` PC 49-60 disjuncts with `WithdrawCascadeAt s C
  slot oldVal x` (storage-fact established at PC 49 via SLOAD-strong;
  bound `x ≤ oldVal` established at PC 56 from JUMPI not-taken; SUB
  semantic at PC 58 gives `newVal = oldVal - x`).
* Update walks 48→49, 49→50, ..., 59→60 (~12 walks).
* Discharge `weth_pc60_cascade` from the strengthened PC 60 disjunct.
* Drop `pc60_cascade` from `WethAssumptions`.

**`pc72_cascade` discharge** (~600 LoC):
* Continue the cascade through PCs 61-72 (CALL setup chain).
* PCs 61-71 are non-storage-touching; cascade preserves trivially.
* PC 72 disjunct gains the slack `μ₂ + storageSum ≤ balanceOf`.
* Combine with `weth_caller_ne_C` for the recipient-≠-C disjunct.

**`pc40_cascade` discharge** (~600 LoC):
* Threading through PCs 33-40 (deposit prefix).
* Additionally requires **Θ-pre-credit slack** lifted from outside Ξ
  — the σ_in entry state must carry `β(C) ≥ S(C) + msg.value` from
  Θ's value transfer that occurred before Ξ ran. This is a Υ-side
  fact requiring further framework or trace extension.

**Pre-cascade lemma**: a separate `WethReachable_account_at_C`
lemma proving `σ[C] = some acc` for any Weth-reachable state.
Required by SLOAD-strong's conclusion (which falls back to ⟨0⟩ if
`σ[C] = none`). Threading through the X loop's CALL arm requires the
framework's `Θ_invariant_preserved` to confirm σ[C] survives the
spawned Θ frame — but Θ may modify σ, so the lemma must be carefully
stated as "Weth-reachable AND no nested CREATE produces C" or similar.

## Total volume

Approximately **2500-3000 LoC** of bounded but careful per-PC
threading + the σ[C]-existence lemma + the Θ-pre-credit lift. Genuine
multi-day proof-engineering work.

## Why it hasn't landed in single sessions

Each per-PC disjunct extension requires coordinated changes across
~7 sites in the file. Lean's elaborator processes these
non-incrementally: a partial change leaves the build broken. So
mid-session bail = lost work. Sub-agents have consistently identified
this and stopped before the build-broken zone.

The clean approach is dedicated proof-engineering sessions where the
full PC-by-PC threading is done in one push: extend disjunct N, all
five rcases at N, walk producing N, walk consuming N, build, commit.
Then PC N+1, etc. ~12 such cycles for `pc60_cascade` alone.

## Status posture

The current 7-field `WethAssumptions` is honest about what's still
trust vs. what's proved. The 4 Register-shape fields exactly mirror
Register's own posture (which the user accepted). The 3 cascade-fact
fields are narrower-than-original-`xi_inv` per-state structural
facts, all derivable in principle from the existing infrastructure
once the threading lands.

Real-world consumers of `weth_solvency_invariant` can verify the
cascade facts by inspection of Weth's bytecode + the per-PC trace —
the same epistemic posture as `I_code_at_C_is_Register_bytecode`
in Register's proof.
