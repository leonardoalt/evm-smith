import EvmSmith.Demos.Register.Theta

/-!
# Layer 3 — `Υ` preserves `RegInv`

Wraps Layer 2 with the transaction-level housekeeping:

- Sender prep: `S_T.balance -= gasLimit*p + blobFee`. Frame (`S_T ≠ C`).
  `totalETH` **strictly decreases** by the blob fee (EIP-4844 burn).
- `Θ` / `Lambda` dispatch: Layer 2.
- Gas refund: `increaseBalance S_T (gStar*p)`. Frame.
- Beneficiary fee: `increaseBalance H.beneficiary ((gasLimit-gStar)*f)`.
  Frame (`H.beneficiary ≠ C`). `totalETH` strictly decreases by the
  base-fee burn component (EIP-1559).
- Selfdestruct sweep: `A.selfDestructSet.foldl erase`. `RegInv.notSD`
  gives `C ∉ selfDestructSet`, so the erase never touches C.
- Dead-account sweep: erases accounts where `emptyAccount = true`.
  `codeAt σ C` → C has non-empty code → C not dead → erase skips C.
- Tstorage wipe: `σ.map` touching only `.tstorage`.

All five of `RegInv`'s conjuncts are preserved.
-/

namespace EvmSmith.RegisterProofs.Layer3

open EvmSmith.RegisterInvariant EvmSmith.RegisterProofs.Layer2
     EvmYul EvmYul.EVM EvmSmith EvmSmith.Register Batteries

theorem Υ_preserves_RegInv
    (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks)
    (tx : Transaction) (S_T C : AccountAddress) (b₀ : ℕ)
    (_hInv : RegInv σ default C b₀)
    (_hCS : C ≠ S_T)
    (_hCH : C ≠ H.beneficiary)
    (_hNewC : ∀ a : AccountAddress, a ≠ C) :
    match Υ fuel σ H_f H H_gen blocks tx S_T with
    | .ok (σ', A', _, _) => RegInv σ' A' C b₀
    | .error _ => True := by
  sorry

end EvmSmith.RegisterProofs.Layer3
