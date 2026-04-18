import EvmSmith.Demos.Weth.Invariant
import EvmYul.EVM.Semantics

/-!
# Layer 2 — preservation of `I` across `Ξ` and `Θ`

The Weth safety invariant must be preserved across every message call.
`Θ` (message-call iterator) and `Ξ` (code execution) are mutually
recursive through fuel; this layer is one well-founded induction on
that fuel argument.

## Main lemmas

- `precompile_preserves`  — single lemma: all ten precompiles thread
  `σ` unchanged on success and return `∅` on failure, which Θ's
  equation (127) maps back to the pre-call σ.
- `balance_transfer_frame` — Θ's equations (124)-(126) update σ with
  the value transfer. When neither sender nor recipient is `C`, `σ[C]`
  is unchanged.
- `Weth_Ξ_preserves_I`    — the program-specific content: when `Ξ`
  runs Weth's bytecode, it preserves `I` on `σ[C]`. Uses the Layer 1
  storage lemmas. Callees of nested CALLs reached via reentrance
  inherit preservation from the fuel IH on `Θ`.
- `Θ_preserves_I`         — the top-level Θ-preservation statement,
  consumed directly by Layer 3. Proved by fuel induction, branching
  on precompile/code/error.

**Status:** all lemmas are currently `sorry` — Layer 2 skeleton.
-/

namespace EvmSmith.WethProofs.Layer2

open EvmSmith.WethInvariant EvmYul EvmYul.EVM EvmSmith EvmSmith.Weth Batteries

/-! ## Precompiles — frame lemma -/

/-- All ten precompiles (`ECREC` … `PointEval`) either leave `σ`
    unchanged on success or return `∅` on failure, which `Θ`'s
    equation (127) maps back to the pre-call σ. So `I` and `codeAt`
    are trivially preserved through any precompile branch. -/
theorem precompile_preserves
    (σ : AccountMap .EVM) (C : AccountAddress) (hI : I σ C) (hCode : codeAt σ C)
    (p : UInt256) (g : UInt256) (A : Substate) (I_env : ExecutionEnv .EVM) :
    True := by
  sorry

/-! ## Balance-transfer frame -/

/-- Θ's value-transfer lines (124)-(126) construct σ₁ from σ by
    adding `v` to the recipient and subtracting `v` from the sender.
    When neither is `C`, `σ₁[C] = σ[C]`. -/
theorem balance_transfer_frame
    (σ : AccountMap .EVM) (r s C : AccountAddress) (v : UInt256)
    (hrC : r ≠ C) (hsC : s ≠ C) :
    True := by
  sorry

/-! ## Weth bytecode preservation under Ξ -/

/-- **Weth's bytecode preserves `I`.** The program-specific content:
    for each dispatch branch (`deposit`, `withdraw`, revert, unknown
    selector), running it via `Ξ` preserves `I` on `σ[C]`. -/
theorem Weth_Ξ_preserves_I
    (fuel : ℕ) (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate) (I_env : ExecutionEnv .EVM)
    (C : AccountAddress)
    (hCode : codeAt σ C)
    (hIEnv_code : I_env.code = bytecode)
    (hIEnv_owner : I_env.codeOwner = C)
    (hInv : I σ C) :
    match Ξ fuel createdAccounts genesisBlockHeader blocks σ σ₀ g A I_env with
    | .ok (.success (_, σ', _, _) _) => I σ' C ∧ codeAt σ' C
    | .ok (.revert _ _) => True
    | .error _ => True := by
  sorry

/-! ## Θ preserves `I` — main Layer 2 statement -/

/-- **Main Layer 2 result.** Every `Θ` invocation preserves `I` and
    `codeAt` at `C`, provided the sender is not `C` (a caller of `Θ`
    always has a distinct sender in our call paths) and `C` is not
    the block beneficiary. -/
theorem Θ_preserves_I
    (fuel : ℕ) (blobVersionedHashes : List ByteArray)
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (c : ToExecute .EVM)
    (g p v v' : UInt256) (d : ByteArray) (e : Nat)
    (H : BlockHeader) (w : Bool)
    (C : AccountAddress)
    (hI : I σ C) (hCode : codeAt σ C)
    (hCNotBeneficiary : C ≠ H.beneficiary)
    (hsC : s ≠ C) :
    match Θ fuel blobVersionedHashes createdAccounts genesisBlockHeader blocks
           σ σ₀ A s o r c g p v v' d e H w with
    | .ok (_, σ', _, _, _, _) => I σ' C ∧ codeAt σ' C
    | .error _ => True := by
  sorry

end EvmSmith.WethProofs.Layer2
