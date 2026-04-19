import EvmSmith.Demos.Register.Invariant

/-!
# Layer 2 — `Θ` / `Lambda` / `Ξ` preserve `RegInv`

Joint fuel induction. Each of these preserves `RegInv` at lower fuel
given the IH.

The statements are **generic on code** wherever possible — we do not
inspect what other contracts compute, only that they (a) can't reduce
`balanceOf σ C` via any opcode, and (b) can't add `C` to
`selfDestructSet` (because `SELFDESTRUCT` adds `Iₐ`, not the
recipient). The one place we need program-specific content is the
`I_env.codeOwner = C` branch of `Ξ`, which must invoke Register's
bytecode analysis.

## Threaded preconditions

Every frame carries:
- `sInSigmaOrZero : s ∈ σ ∨ v = ⟨0⟩` (rules out fresh-recipient ETH
  inflation in Θ's σ'₁ construction).
- `hNewC : ∀ a, a = C → a ∉ createdAccounts` (rules out CREATE
  spawning at C's address — would overwrite Register's bytecode).

Also global: `C ≠ H.beneficiary` is a caller-supplied boundary
hypothesis that's *not* used inside Θ/Ξ (only Υ uses it), so it does
not appear in the Layer 2 signatures.
-/

namespace EvmSmith.RegisterProofs.Layer2

open EvmSmith.RegisterInvariant EvmYul EvmYul.EVM EvmSmith EvmSmith.Register Batteries

/-! ## `Θ` preserves `RegInv` -/

theorem Θ_preserves_RegInv
    (fuel : ℕ) (blobVersionedHashes : List ByteArray)
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (c : ToExecute .EVM)
    (g p v v' : UInt256) (d : ByteArray) (e : Nat)
    (H : BlockHeader) (w : Bool)
    (C : AccountAddress) (b₀ : ℕ)
    (_hInv : RegInv σ A C b₀)
    (_hsC : s ≠ C)
    (_sInσOrZero : (σ.find? s).isSome ∨ v = ⟨0⟩)
    (_hNewC : ∀ a ∈ createdAccounts, a ≠ C) :
    match Θ fuel blobVersionedHashes createdAccounts genesisBlockHeader blocks
           σ σ₀ A s o r c g p v v' d e H w with
    | .ok (createdAccs', σ', _, A', _, _) =>
        RegInv σ' A' C b₀ ∧ (∀ a ∈ createdAccs', a ≠ C)
    | .error _ => True := by
  sorry

/-! ## `Ξ` preserves `RegInv`

Two sub-cases inside:
- `I_env.codeOwner = C`: must also have `I_env.code = bytecode`
  (enforced by the `hOwnerCode` hypothesis; holds because `Θ` derives
  `I_env.code` from the callee's actual code via `toExecute`, which
  combined with `RegInv.code` gives us Register's bytecode).
- `I_env.codeOwner ≠ C`: generic frame — any opcode either leaves
  `balanceOf C` alone, adds to it (CALL incoming, SELFDESTRUCT with
  `r = C`), or routes through `Θ` / `Lambda` at lower fuel (the
  mutual-induction IH). -/
theorem Ξ_preserves_RegInv
    (fuel : ℕ) (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate) (I_env : ExecutionEnv .EVM)
    (C : AccountAddress) (b₀ : ℕ)
    (_hInv : RegInv σ A C b₀)
    (_hOwnerCode : I_env.codeOwner = C → I_env.code = bytecode)
    (_hNewC : ∀ a ∈ createdAccounts, a ≠ C) :
    match Ξ fuel createdAccounts genesisBlockHeader blocks σ σ₀ g A I_env with
    | .ok (.success (createdAccs', σ', _, A') _) =>
        RegInv σ' A' C b₀ ∧ (∀ a ∈ createdAccs', a ≠ C)
    | .ok (.revert _ _) => True
    | .error _ => True := by
  sorry

end EvmSmith.RegisterProofs.Layer2
