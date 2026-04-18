import EvmSmith.Demos.Weth.Theta

/-!
# Layer 3 — transaction-level preservation (`Υ`)

`Υ` is one transaction: gas/nonce bookkeeping, a `Θ`/`Lambda` dispatch,
gas refund, beneficiary fee, selfdestruct sweep, dead-account sweep,
tstorage wipe, return. Each step either doesn't touch `σ[C]` or does so
in a way covered by Layer 2.

## The case breakdown

- **Sender prep** — subtract gas × price + blob fee from sender, bump
  nonce, checkpoint into `σ₀`. Sender ≠ C (hypothesis).
- **Θ / Lambda** — Layer 2 handles this.
- **Gas refund** — `increaseBalance S_T (gStar * p)`. S_T ≠ C, frame.
- **Beneficiary fee** — `increaseBalance H.beneficiary ((gasLimit - gStar) * f)`.
  `H.beneficiary ≠ C` (hypothesis), frame.
- **Selfdestruct sweep** — `A.selfDestructSet.foldl erase`. Weth's
  bytecode contains no `SELFDESTRUCT` opcode, so `C ∉ selfDestructSet`;
  this can be shown from `Weth_Ξ_preserves_I` extended to also
  preserve "C ∉ substate.selfDestructSet". Or, simpler: we add that
  conjunct into `I` / the combined invariant.
- **Dead-account sweep** — erase every dead account (code empty ∧
  nonce 0 ∧ balance 0) from `touchedAccounts`. Weth has non-empty
  code (maintained by `codeAt`), so `C` is not dead, survives the
  sweep.
- **Tstorage wipe** — `σ.map (fun (_, acc) => {acc with tstorage := ∅})`.
  Weth doesn't use TSTORE so its slot-level invariant is blind to
  `tstorage`; wipe is a no-op on `I`.

## Lemmas

- `Υ_preserves_I` — the top-level result, consumed by
  `weth_always_safe` in `Proofs.lean`.
- Sub-lemmas for each case as needed.

**Status:** all `sorry` — Layer 3 skeleton.
-/

namespace EvmSmith.WethProofs.Layer3

open EvmSmith.WethInvariant EvmSmith.WethProofs.Layer2
     EvmYul EvmYul.EVM EvmSmith EvmSmith.Weth Batteries

/-! ### Frame lemmas for the post-Θ operations -/

/-- `increaseBalance` at `A ≠ C` does not affect `σ[C]`. -/
theorem increaseBalance_frame
    (σ : AccountMap .EVM) (A C : AccountAddress) (v : UInt256)
    (hAC : A ≠ C) :
    True := by
  sorry  -- placeholder; refactor inline when Υ_preserves_I wires it

/-- Erasing addresses other than `C` doesn't affect `σ[C]`. -/
theorem erase_frame
    (σ : AccountMap .EVM) (addrs : Batteries.RBSet AccountAddress compare)
    (C : AccountAddress) (hCNotIn : C ∉ addrs) :
    True := by
  sorry

/-- `C` is never dead when `codeAt σ C` holds (non-empty code). -/
theorem C_not_dead_of_codeAt
    (σ : AccountMap .EVM) (C : AccountAddress) (hCode : codeAt σ C) :
    True := by
  sorry

/-- Wiping `tstorage` across `σ` doesn't change any account's
    `storage` or `balance`, so `I` and `codeAt` are preserved. -/
theorem tstorage_wipe_frame
    (σ : AccountMap .EVM) (C : AccountAddress) (hI : I σ C) (hCode : codeAt σ C) :
    True := by
  sorry

/-! ### `Υ` preserves `I` -/

/-- **Main Layer 3 result.** -/
theorem Υ_preserves_I
    (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ)
    (H H_genesis : BlockHeader) (blocks : ProcessedBlocks)
    (tx : Transaction) (S_T C : AccountAddress)
    (hI : I σ C) (hCode : codeAt σ C)
    (hCNotBeneficiary : C ≠ H.beneficiary)
    (hCNotSender     : C ≠ S_T) :
    match Υ fuel σ H_f H H_genesis blocks tx S_T with
    | .ok (σ', _, _, _) => I σ' C ∧ codeAt σ' C
    | .error _          => True := by
  sorry

end EvmSmith.WethProofs.Layer3
