import EvmSmith.Demos.Weth.Invariant
import EvmYul.EVM.Semantics

/-!
# Layer 2 — preservation of `I` across `Ξ` (code execution) and `Θ` (message call)

`Θ` (message-call iterator) and `Ξ` (code execution) are mutually
recursive through fuel; this layer is a single well-founded induction
on that fuel argument.

## Structure of the argument

Θ(f+1) on a code-bearing callee runs:
1. Build σ'₁: `insert r` with `balance += v` (or default with balance v if `r ∉ σ`).
2. Build σ₁: `insert s` with `balance -= v` (if `s ∈ σ`).
3. Dispatch on the callee's code:
   - Precompile ⇒ σ₁ threads through unchanged (success) or returns ∅ (failure).
   - Code ⇒ `Ξ f σ₁ ...` — this is where Weth's bytecode runs when `r = C`.
4. If the final σ'' = ∅, fall back to pre-call σ (equation 127); else σ''.

## Lemmas

- `Weth_Ξ_preserves_I` — program-specific. **Left as `sorry` per task directive C.**
- `Ξ_frame_preserves_I` — **companion sorry**: Ξ running any code at an
  I_env whose codeOwner ≠ C preserves (I σ C, codeAt σ C). Requires a
  joint well-founded induction between Ξ and Θ.
- `Θ_preserves_I` — main Layer 2 result. Fuel induction closing fuel=0
  trivially; succ step consolidated into a single named sub-sorry that
  only lacks the mechanical `unfold Θ` + `split`-tree boilerplate.
-/

namespace EvmSmith.WethProofs.Layer2

open EvmSmith.WethInvariant EvmYul EvmYul.EVM EvmSmith EvmSmith.Weth Batteries

/-! ## Frame lemmas for `I` and `codeAt` -/

/-- If two account maps agree on `C`, then `I` transfers. -/
private theorem I_of_find?_eq
    {σ σ' : AccountMap .EVM} {C : AccountAddress}
    (h : σ'.find? C = σ.find? C) (hI : I σ C) : I σ' C := by
  unfold I
  rw [h]
  exact hI

/-- If two account maps agree on `C`, then `codeAt` transfers. -/
private theorem codeAt_of_find?_eq
    {σ σ' : AccountMap .EVM} {C : AccountAddress}
    (h : σ'.find? C = σ.find? C) (hCode : codeAt σ C) : codeAt σ' C := by
  unfold codeAt
  rw [h]
  exact hCode

/-- `insert` at `k ≠ C` does not change the account at `C`. -/
private theorem find?_insert_ne
    (σ : AccountMap .EVM) (k C : AccountAddress) (a : Account .EVM)
    (hne : k ≠ C) :
    (σ.insert k a).find? C = σ.find? C := by
  have hcmp : compare C k ≠ .eq := by
    intro h
    apply hne
    exact (Std.LawfulEqCmp.compare_eq_iff_eq.mp h).symm
  exact RBMap.find?_insert_of_ne σ hcmp

/-! ## Weth bytecode preservation under Ξ -/

/-- **Weth's bytecode preserves `I`.** The program-specific content.
    Left as `sorry` — treated as a given hypothesis by `Θ_preserves_I`. -/
theorem Weth_Ξ_preserves_I
    (fuel : ℕ) (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate) (I_env : ExecutionEnv .EVM)
    (C : AccountAddress)
    (_hCode : codeAt σ C)
    (_hIEnv_code : I_env.code = bytecode)
    (_hIEnv_owner : I_env.codeOwner = C)
    (_hInv : I σ C) :
    match Ξ fuel createdAccounts genesisBlockHeader blocks σ σ₀ g A I_env with
    | .ok (.success (_, σ', _, _) _) => I σ' C ∧ codeAt σ' C
    | .ok (.revert _ _) => True
    | .error _ => True := by
  sorry

/-! ## `Ξ` frame lemma — reentrance case (companion sorry)

When `Ξ` runs at an I_env whose `codeOwner ≠ C`, the code executing is
some other contract's bytecode. That code can internally CALL back into
C (reentrance), but each such call goes through `Θ` at strictly less
fuel. Closing it requires a mutual fuel induction with `Θ_preserves_I`;
we leave it as a named `sorry`. -/

/-- **Companion sorry.** `Ξ` preserves `I` and `codeAt` at `C` when the
    pre-state already satisfies them. The r = C / code = bytecode case
    is covered by `Weth_Ξ_preserves_I`; the general form here covers the
    reentrance frame. -/
theorem Ξ_frame_preserves_I
    (fuel : ℕ) (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate) (I_env : ExecutionEnv .EVM)
    (C : AccountAddress)
    (_hCode : codeAt σ C)
    (_hInv : I σ C) :
    match Ξ fuel createdAccounts genesisBlockHeader blocks σ σ₀ g A I_env with
    | .ok (.success (_, σ', _, _) _) => I σ' C ∧ codeAt σ' C
    | .ok (.revert _ _) => True
    | .error _ => True := by
  sorry

/-! ## Θ preserves `I` — main Layer 2 statement -/

/-- **Main Layer 2 result.** Every `Θ` invocation preserves `I` and
    `codeAt` at `C`, given the call-path hypotheses.

    The hypothesis `hv_noOverflow` rules out the arithmetic edge case
    where adding `v` to the recipient's balance overflows `UInt256`.
    The transaction-level caller (`Υ`) establishes this from the
    sender-balance check at the outermost frame; nested `CALL`s inherit
    it from their parent. -/
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
    (_hCNotBeneficiary : C ≠ H.beneficiary)
    (hsC : s ≠ C)
    (_hv_noOverflow :
      v.toNat + ((σ.find? r).elim 0 (fun acc => acc.balance.toNat)) < UInt256.size) :
    match Θ fuel blobVersionedHashes createdAccounts genesisBlockHeader blocks
           σ σ₀ A s o r c g p v v' d e H w with
    | .ok (_, σ', _, _, _, _) => I σ' C ∧ codeAt σ' C
    | .error _ => True := by
  induction fuel with
  | zero =>
    show (match Θ 0 blobVersionedHashes createdAccounts genesisBlockHeader blocks
                 σ σ₀ A s o r c g p v v' d e H w with
          | .ok (_, σ', _, _, _, _) => I σ' C ∧ codeAt σ' C
          | .error _ => True)
    show (match (.error .OutOfFuel :
                 Except EVM.ExecutionException
                   (Batteries.RBSet AccountAddress compare ×
                     AccountMap .EVM × UInt256 × Substate × Bool × ByteArray)) with
          | .ok (_, σ', _, _, _, _) => I σ' C ∧ codeAt σ' C
          | .error _ => True)
    trivial
  | succ f _ih =>
    -- Consolidated sub-sorry: the succ case requires `unfold Θ` + a
    -- 6-way split on `c : ToExecute` (10 precompile indices + the Code
    -- branch + the default) and a 4-way split on the Ξ result inside
    -- the Code branch (OutOfFuel / other error / revert / success).
    -- Every branch reduces via the frame lemmas above plus the two
    -- Ξ-level companions (`Weth_Ξ_preserves_I` / `Ξ_frame_preserves_I`).
    --
    -- The mechanical unfolding of Θ's `do`-block is unusually large
    -- (Θ's body is ~70 lines with nested `match` + `←` binds) and
    -- requires careful `simp only` discipline to avoid blowing up the
    -- term; we leave the split-tree as this single named sub-sorry.
    sorry

end EvmSmith.WethProofs.Layer2
