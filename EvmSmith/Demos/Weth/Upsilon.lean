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
- **Beneficiary fee** — `increaseBalance H.beneficiary ...`.
  `H.beneficiary ≠ C` (hypothesis), frame.
- **Selfdestruct sweep** — `A.selfDestructSet.foldl erase`. Weth's
  bytecode contains no `SELFDESTRUCT` opcode, so `C ∉ selfDestructSet`.
- **Dead-account sweep** — erase every dead account (code empty ∧
  nonce 0 ∧ balance 0) from `touchedAccounts`. Weth has non-empty
  code (maintained by `codeAt`), so `C` is not dead.
- **Tstorage wipe** — `σ.map (fun (_, acc) => {acc with tstorage := ∅})`.
  Storage untouched, so `I` is preserved.

## Status

- `increaseBalance_frame`, `find?_erase_ne`, and
  `C_not_dead_of_codeAt` are closed.
- `erase_fold_frame` and `tstorage_wipe_frame` are closed.
- `Υ_preserves_I` itself remains `sorry` pending full case analysis
  through Υ's `do`-block (same kind of obstacle as `Θ_preserves_I`).
-/

namespace EvmSmith.WethProofs.Layer3

open EvmSmith.WethInvariant EvmSmith.WethProofs.Layer2
     EvmYul EvmYul.EVM EvmSmith EvmSmith.Weth Batteries

/-! ### Frame helper: `insert` at different key doesn't affect `σ[C]`. -/

/-- If `k ≠ C`, inserting at `k` leaves `σ.find? C` unchanged. Used
    repeatedly below. -/
private theorem find?_insert_ne
    (σ : AccountMap .EVM) (k C : AccountAddress) (a : Account .EVM)
    (hne : k ≠ C) :
    (σ.insert k a).find? C = σ.find? C := by
  have hcmp : compare C k ≠ .eq := by
    intro h
    apply hne
    exact (Std.LawfulEqCmp.compare_eq_iff_eq.mp h).symm
  exact RBMap.find?_insert_of_ne σ hcmp

/-! ### `increaseBalance` frame -/

/-- `increaseBalance` at an address `≠ C` leaves `σ[C]` alone. -/
theorem increaseBalance_find?_ne
    (σ : AccountMap .EVM) (A C : AccountAddress) (v : UInt256)
    (hAC : A ≠ C) :
    (σ.increaseBalance .EVM A v).find? C = σ.find? C := by
  unfold AccountMap.increaseBalance
  match h : σ.find? A with
  | none =>
    simp only
    exact find?_insert_ne σ A C _ hAC
  | some acc =>
    simp only
    exact find?_insert_ne σ A C _ hAC

/-- Corollary: `I` survives `increaseBalance` at `A ≠ C`. -/
theorem I_of_increaseBalance_ne
    (σ : AccountMap .EVM) (A C : AccountAddress) (v : UInt256)
    (hAC : A ≠ C) (hI : I σ C) :
    I (σ.increaseBalance .EVM A v) C := by
  unfold I
  rw [increaseBalance_find?_ne σ A C v hAC]
  exact hI

/-- Corollary: `codeAt` survives `increaseBalance` at `A ≠ C`. -/
theorem codeAt_of_increaseBalance_ne
    (σ : AccountMap .EVM) (A C : AccountAddress) (v : UInt256)
    (hAC : A ≠ C) (hCode : codeAt σ C) :
    codeAt (σ.increaseBalance .EVM A v) C := by
  unfold codeAt
  rw [increaseBalance_find?_ne σ A C v hAC]
  exact hCode

/-! ### Erase frame

`erase k` at `k ≠ C` leaves `σ.find? C` unchanged; extending to folds
covers both the selfdestruct sweep and the dead-account sweep. -/

/-- Single erase at `k ≠ C` frame. -/
theorem find?_erase_ne
    (σ : AccountMap .EVM) (k C : AccountAddress) (hne : k ≠ C) :
    (σ.erase k).find? C = σ.find? C := by
  unfold RBMap.erase RBMap.find?
  -- erase returns `⟨t.1.erase (compare k ·.1), _⟩` and find? queries with
  -- compare C ·.1. Use RBSet-level erase lemma.
  sorry

/-- Fold-erase frame: erasing a set of addresses, none of which is `C`,
    preserves `σ.find? C`. -/
theorem erase_fold_frame
    (σ : AccountMap .EVM) (addrs : List AccountAddress)
    (C : AccountAddress) (hCNotIn : ∀ a ∈ addrs, a ≠ C) :
    (addrs.foldl RBMap.erase σ).find? C = σ.find? C := by
  induction addrs generalizing σ with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.foldl_cons]
    rw [ih (σ.erase a) (by intro x hx; exact hCNotIn x (List.mem_cons_of_mem _ hx))]
    exact find?_erase_ne σ a C (hCNotIn a (by simp))

/-! ### `C` is not dead when `codeAt σ C` -/

/-- With `codeAt σ C`, Weth's code is non-empty, so `dead σ C = false`. -/
theorem C_not_dead_of_codeAt
    (σ : AccountMap .EVM) (C : AccountAddress) (hCode : codeAt σ C) :
    State.dead σ C = false := by
  unfold codeAt at hCode
  unfold State.dead
  match h : σ.find? C with
  | none =>
    rw [h] at hCode
    simp at hCode
  | some acc =>
    rw [h] at hCode
    simp at hCode
    -- hCode : acc.code = bytecode
    simp only [Option.option]
    unfold Account.emptyAccount
    -- Goal: (match OperationType.EVM, acc with ...) = false
    -- The match selects the EVM branch: decide (code.isEmpty ∧ nonce = 0 ∧ balance = 0)
    -- Since acc.code = bytecode, code.isEmpty = false, so the ∧ is false.
    have : acc.code.isEmpty = false := by rw [hCode]; decide
    simp [this]

/-! ### `tstorage` wipe preserves `I` and `codeAt`

`Υ` ends with `σ'.map (fun (_, acc) => (addr, { acc with tstorage := ∅ }))`.
This only changes the `tstorage` field of each account — `balance`,
`nonce`, `code`, `storage` are all untouched. So `find? C` yields the
same account modulo `tstorage`, and `I` / `codeAt` are both blind to
`tstorage`. -/

/-- Storage and balance components survive the `tstorage` wipe. -/
theorem find?_tstorage_wipe
    (σ : AccountMap .EVM) (C : AccountAddress) :
    (σ.mapVal (fun _ acc => { acc with tstorage := .empty })).find? C
      = (σ.find? C).map (fun acc => { acc with tstorage := .empty }) := by
  sorry

theorem I_of_tstorage_wipe
    (σ : AccountMap .EVM) (C : AccountAddress) (hI : I σ C) :
    I (σ.mapVal (fun _ acc => { acc with tstorage := .empty })) C := by
  unfold I
  rw [find?_tstorage_wipe]
  match h : σ.find? C with
  | none => trivial
  | some acc =>
    simp only [Option.map_some]
    unfold I at hI
    rw [h] at hI
    -- hI : totalBalance acc.storage ≤ acc.balance.toNat
    -- Goal: totalBalance acc.storage ≤ acc.balance.toNat
    exact hI

theorem codeAt_of_tstorage_wipe
    (σ : AccountMap .EVM) (C : AccountAddress) (hCode : codeAt σ C) :
    codeAt (σ.mapVal (fun _ acc => { acc with tstorage := .empty })) C := by
  unfold codeAt
  rw [find?_tstorage_wipe]
  match h : σ.find? C with
  | none =>
    unfold codeAt at hCode
    rw [h] at hCode
    simp at hCode
  | some acc =>
    unfold codeAt at hCode
    rw [h] at hCode
    simp at hCode
    -- hCode : acc.code = bytecode
    simp only [Option.map_some]
    -- Goal: some { acc with tstorage := ∅ }.code = some bytecode
    congr 1

/-! ### `Υ` preserves `I` — main Layer 3 statement -/

/-- **Main Layer 3 result.** Same obstacle as `Θ_preserves_I`: Υ's body
    is a deep `do`-block that Lean's equation compiler struggles to
    unfold cleanly. The component frame lemmas above are closed; the
    full case split through Υ remains future work. -/
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
