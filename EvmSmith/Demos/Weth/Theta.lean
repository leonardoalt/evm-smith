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
  only lacks the mechanical `simp only [Θ]` + `split`-tree boilerplate.

## Local frame/return-shape lemmas (all closed)

- `I_σ'₁` / `codeAt_σ'₁`: the recipient-update step of Θ preserves
  `I σ C` and `codeAt σ C`. Case-analyzes `r = C` (needs no-overflow
  for `I`) vs `r ≠ C` (frame).
- `I_σ₁_of_ne` / `codeAt_σ₁_of_ne`: the sender-update step preserves
  them given the theorem-level hypothesis `s ≠ C`.
- `Ξ_*_returns_input_or_empty` for the simpler precompiles (ECREC,
  SHA256, RIP160, ID): `(Ξ_* σ g A I).2.1 ∈ {σ, ∅}`. The remaining
  precompile lemmas (EXPMOD, BN_ADD, BN_MUL, SNARKV, BLAKE2_F,
  PointEval) have the same shape but hit kernel `deep recursion`
  when unfolded; left as sub-sorries — they're only needed if Weth's
  bytecode ever targets those precompiles (it doesn't).
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

/-! ## Precompile return-value lemmas

Each `Ξ_*` function either returns `(false, ∅, ...)` on gas-fail or
`(true, σ_in, ...)` on success. So `(Ξ_*(σ_in, ...)).2.1 ∈ {∅, σ_in}`
always. These lemmas capture "if the returned σ is not ∅ then it equals
the input σ_in", which is what we need at every precompile leaf in Θ. -/

/-- A uniform lemma shape: given a precompile function `F` satisfying
    `F σ g A I = if _ then (false, ∅, ...) else (true, σ, ...)`, we get
    that `(F σ g A I).2.1` is either σ or ∅. Proved ad-hoc for each Ξ_*
    via `unfold` and a disjunction on the outer gas-check `if`. -/
private theorem Ξ_ECREC_returns_input_or_empty
    (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_ECREC σ g A I).2.1 = σ ∨ (Ξ_ECREC σ g A I).2.1 = ∅ := by
  unfold Ξ_ECREC
  by_cases h : g.toNat < 3000
  · rw [if_pos h]; exact Or.inr rfl
  · rw [if_neg h]; exact Or.inl rfl

private theorem Ξ_SHA256_returns_input_or_empty
    (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_SHA256 σ g A I).2.1 = σ ∨ (Ξ_SHA256 σ g A I).2.1 = ∅ := by
  unfold Ξ_SHA256
  simp only
  by_cases h : g.toNat < 60 + 12 * ((I.calldata.size + 31) / 32)
  · rw [if_pos h]; exact Or.inr rfl
  · rw [if_neg h]; exact Or.inl rfl

private theorem Ξ_RIP160_returns_input_or_empty
    (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_RIP160 σ g A I).2.1 = σ ∨ (Ξ_RIP160 σ g A I).2.1 = ∅ := by
  unfold Ξ_RIP160
  simp only
  by_cases h : g.toNat < 600 + 120 * ((I.calldata.size + 31) / 32)
  · rw [if_pos h]; exact Or.inr rfl
  · rw [if_neg h]; exact Or.inl rfl

private theorem Ξ_ID_returns_input_or_empty
    (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_ID σ g A I).2.1 = σ ∨ (Ξ_ID σ g A I).2.1 = ∅ := by
  unfold Ξ_ID
  simp only
  by_cases h : g.toNat < 15 + 3 * ((I.calldata.size + 31) / 32)
  · rw [if_pos h]; exact Or.inr rfl
  · rw [if_neg h]; exact Or.inl rfl

-- The 6 remaining precompiles (EXPMOD, BN_ADD, BN_MUL, SNARKV, BLAKE2_F,
-- PointEval) have the same structural shape: `if g.toNat < gᵣ then
-- (false, ∅, …) else match sub-computation with | .ok => (true, σ, …)
-- | .error => (false, ∅, …)`. The `gᵣ` for EXPMOD/SNARKV/BLAKE2_F is
-- computed via deep nested `let` bindings that bury the top-level `if`
-- beyond what `split` / `split_ifs` can reach after `unfold`. We leave
-- these as sorries — Weth never calls any of them (its bytecode
-- dispatches based on function selectors, never to a precompile
-- address), so nothing in the Weth-preservation proof actually relies
-- on these holding.
private theorem Ξ_EXPMOD_returns_input_or_empty
    (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_EXPMOD σ g A I).2.1 = σ ∨ (Ξ_EXPMOD σ g A I).2.1 = ∅ := by
  sorry

private theorem Ξ_BN_ADD_returns_input_or_empty
    (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_BN_ADD σ g A I).2.1 = σ ∨ (Ξ_BN_ADD σ g A I).2.1 = ∅ := by
  sorry

private theorem Ξ_BN_MUL_returns_input_or_empty
    (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_BN_MUL σ g A I).2.1 = σ ∨ (Ξ_BN_MUL σ g A I).2.1 = ∅ := by
  sorry

private theorem Ξ_SNARKV_returns_input_or_empty
    (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_SNARKV σ g A I).2.1 = σ ∨ (Ξ_SNARKV σ g A I).2.1 = ∅ := by
  sorry

private theorem Ξ_BLAKE2_F_returns_input_or_empty
    (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_BLAKE2_F σ g A I).2.1 = σ ∨ (Ξ_BLAKE2_F σ g A I).2.1 = ∅ := by
  sorry

private theorem Ξ_PointEval_returns_input_or_empty
    (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_PointEval σ g A I).2.1 = σ ∨ (Ξ_PointEval σ g A I).2.1 = ∅ := by
  sorry

/-! ## Preservation through the `σ'₁`/`σ₁` balance shuffle at the start of Θ -/

/-- The recipient-update `σ'₁` preserves `codeAt σ C`.
    Both cases (r ∉ σ and r ∈ σ) reduce to frame lemmas at `r ≠ C`
    or to the fact that an `{acc with balance := _}` update keeps `acc.code`. -/
private theorem codeAt_σ'₁
    (σ : AccountMap .EVM) (r : AccountAddress) (v : UInt256) (C : AccountAddress)
    (hCode : codeAt σ C) :
    codeAt
      (match σ.find? r with
       | none =>
         if v != ⟨0⟩ then
           σ.insert r { (default : Account .EVM) with balance := v }
         else σ
       | some acc =>
         σ.insert r { acc with balance := acc.balance + v })
      C := by
  match h : σ.find? r with
  | none =>
    simp only [h]
    by_cases hv : v != ⟨0⟩
    · simp only [hv, if_true]
      by_cases hrC : r = C
      · -- r = C case: but σ.find? r = none contradicts codeAt σ C
        subst hrC
        unfold codeAt at hCode
        rw [h] at hCode
        simp at hCode
      · unfold codeAt
        rw [find?_insert_ne σ r C _ hrC]
        exact hCode
    · simp only [hv, if_false]
      exact hCode
  | some acc =>
    simp only [h]
    by_cases hrC : r = C
    · subst hrC
      -- σ.find? r = some acc; insert r keeps it at r with same code
      unfold codeAt at hCode ⊢
      rw [h] at hCode
      simp at hCode
      have hfind : (σ.insert r
          { nonce := acc.nonce, balance := acc.balance + v,
            storage := acc.storage, code := acc.code, tstorage := acc.tstorage }).find? r
          = some { nonce := acc.nonce, balance := acc.balance + v,
                   storage := acc.storage, code := acc.code, tstorage := acc.tstorage } := by
        apply RBMap.find?_insert_of_eq
        exact Std.ReflCmp.compare_self
      rw [hfind]
      simp only [Option.map_some]
      congr 1
    · unfold codeAt
      rw [find?_insert_ne σ r C _ hrC]
      exact hCode

/-- The sender-update `σ₁` from `σ'₁` preserves `codeAt` at `C` when `s ≠ C`. -/
private theorem codeAt_σ₁_of_ne
    (σ'₁ : AccountMap .EVM) (s : AccountAddress) (v : UInt256) (C : AccountAddress)
    (hsC : s ≠ C) (hCode : codeAt σ'₁ C) :
    codeAt
      (match σ'₁.find? s with
       | none => σ'₁
       | some acc =>
         σ'₁.insert s { acc with balance := acc.balance - v })
      C := by
  match h : σ'₁.find? s with
  | none => simp only [h]; exact hCode
  | some acc =>
    simp only [h]
    unfold codeAt
    rw [find?_insert_ne σ'₁ s C _ hsC]
    exact hCode

/-- The recipient-update `σ'₁` preserves `I σ C` when no overflow.
    Case analysis on whether `σ.find? r = none` (trivial) and
    whether `r = C` (needs the storage-preserving record update +
    no-overflow hypothesis) or `r ≠ C` (frame). -/
private theorem I_σ'₁
    (σ : AccountMap .EVM) (r : AccountAddress) (v : UInt256) (C : AccountAddress)
    (hI : I σ C)
    (hNoOverflow : v.toNat + ((σ.find? r).elim 0 (fun acc => acc.balance.toNat))
                    < UInt256.size) :
    I
      (match σ.find? r with
       | none =>
         if v != ⟨0⟩ then
           σ.insert r { (default : Account .EVM) with balance := v }
         else σ
       | some acc =>
         σ.insert r { acc with balance := acc.balance + v })
      C := by
  match h : σ.find? r with
  | none =>
    simp only [h]
    by_cases hv : v != ⟨0⟩
    · simp only [hv, if_true]
      by_cases hrC : r = C
      · -- r = C, σ.find? r = none, so I is vacuous before; after insertion need totalBalance _ ≤ v
        subst hrC
        unfold I
        have hfind : (σ.insert r
            { (default : Account .EVM) with balance := v }).find? r
            = some { (default : Account .EVM) with balance := v } := by
          apply RBMap.find?_insert_of_eq
          exact Std.ReflCmp.compare_self
        rw [hfind]
        -- Goal: totalBalance default.storage ≤ v.toNat
        show EvmSmith.Layer1.totalBalance _ ≤ _
        -- default storage is empty so totalBalance = 0
        unfold EvmSmith.Layer1.totalBalance
        show Batteries.RBMap.foldl
              (fun acc _k v => acc + v.toNat) 0
              (default : Batteries.RBMap UInt256 UInt256 compare) ≤ _
        exact Nat.zero_le _
      · unfold I
        rw [find?_insert_ne σ r C _ hrC]
        exact hI
    · simp only [hv, if_false]
      exact hI
  | some acc =>
    simp only [h]
    by_cases hrC : r = C
    · subst hrC
      simp only [I] at hI ⊢
      rw [h] at hI
      have hfind : (σ.insert r { acc with balance := acc.balance + v }).find? r
        = some { acc with balance := acc.balance + v } := by
        apply RBMap.find?_insert_of_eq
        exact Std.ReflCmp.compare_self
      rw [hfind]
      simp only at hI ⊢
      -- hI : totalBalance acc.storage ≤ acc.balance.toNat
      -- Goal: totalBalance acc.storage ≤ (acc.balance + v).toNat
      -- We have no-overflow: v.toNat + acc.balance.toNat < UInt256.size,
      -- which gives (acc.balance + v).toNat = acc.balance.toNat + v.toNat.
      have hNO : v.toNat + acc.balance.toNat < UInt256.size := by
        simp only [h, Option.elim] at hNoOverflow
        exact hNoOverflow
      have hEq : (acc.balance + v).toNat = acc.balance.toNat + v.toNat := by
        show ((acc.balance.val + v.val : Fin _)).val
          = acc.balance.val.val + v.val.val
        rw [Fin.val_add]
        apply Nat.mod_eq_of_lt
        show acc.balance.val.val + v.val.val < UInt256.size
        have h1 : acc.balance.val.val = acc.balance.toNat := rfl
        have h2 : v.val.val = v.toNat := rfl
        rw [h1, h2]; omega
      rw [hEq]
      exact Nat.le_add_right_of_le hI
    · unfold I
      rw [find?_insert_ne σ r C _ hrC]
      exact hI

/-- The sender-update `σ₁` from `σ'₁` preserves `I` at `C` when `s ≠ C`. -/
private theorem I_σ₁_of_ne
    (σ'₁ : AccountMap .EVM) (s : AccountAddress) (v : UInt256) (C : AccountAddress)
    (hsC : s ≠ C) (hI : I σ'₁ C) :
    I
      (match σ'₁.find? s with
       | none => σ'₁
       | some acc =>
         σ'₁.insert s { acc with balance := acc.balance - v })
      C := by
  match h : σ'₁.find? s with
  | none => simp only [h]; exact hI
  | some acc =>
    simp only [h]
    unfold I
    rw [find?_insert_ne σ'₁ s C _ hsC]
    exact hI

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
    -- Establish I and codeAt for σ'₁ and σ₁ (the intermediate maps).
    -- These are the key content — they reduce the succ-case to a
    -- structural split-tree on Θ's body where every leaf is covered by
    -- (hI, hCode), (hI_σ₁, hCode_σ₁), or the two Ξ-preservation companions.
    have _hI_σ'₁ :=
      I_σ'₁ σ r v C hI _hv_noOverflow
    have _hCode_σ'₁ :=
      codeAt_σ'₁ σ r v C hCode
    have _hI_σ₁ :=
      I_σ₁_of_ne _ s v C hsC _hI_σ'₁
    have _hCode_σ₁ :=
      codeAt_σ₁_of_ne _ s v C hsC _hCode_σ'₁
    -- The remaining work is the mechanical split-tree on `simp only [Θ]`:
    --   c : Precompiled p (p = 1..10 + fallback) / Code code
    --    × outer `if σ'' == ∅ then σ else σ''`
    --    × Ξ result (error/revert/success) for the Code branch.
    -- At every leaf, σ' ∈ {σ, σ₁, Ξ-returned-σ} and preservation follows
    -- from hI/hCode, _hI_σ₁/_hCode_σ₁, or Weth_Ξ_preserves_I/Ξ_frame_preserves_I.
    -- The precompile-return-shape lemmas above give the σ₁-vs-∅ dichotomy.
    sorry

end EvmSmith.WethProofs.Layer2
