import EvmSmith.Lemmas.RBMapSum
import EvmSmith.Demos.Weth.Program

/-!
# Weth invariant definitions

Shared definitions used by all four layers of the main proof:

- `totalBalance` — already defined generically in
  `EvmSmith/Lemmas/RBMapSum.lean` as `EvmSmith.Layer1.totalBalance`.
  Re-exported here for ergonomics.
- `I` — the main safety invariant, `ℕ`-valued so `UInt256` modular
  wraparound cannot masquerade as an overflowed sum satisfying `≤`.
- `codeAt` — auxiliary invariant that must be preserved alongside
  `I`: `σ[C].code = Weth.bytecode`. Needed because the Weth-specific
  preservation argument inside `Ξ` depends on the callee running
  Weth's bytecode.
- `initial_state` — freshly-deployed state: bytecode installed at
  `C`, balance 0, empty storage. Base case of the `I` induction.
-/

namespace EvmSmith.WethInvariant

open EvmYul EvmYul.EVM EvmSmith EvmSmith.Weth Batteries

/-- Sum of token balances stored in `C`'s storage map, taken in `ℕ`. -/
def totalBalance (storage : RBMap UInt256 UInt256 compare) : ℕ :=
  EvmSmith.Layer1.totalBalance storage

/-- Main safety invariant. -/
def I (σ : AccountMap .EVM) (C : AccountAddress) : Prop :=
  match σ.find? C with
  | none     => True
  | some acc => totalBalance acc.storage ≤ acc.balance.toNat

/-- Auxiliary code-preservation invariant. -/
def codeAt (σ : AccountMap .EVM) (C : AccountAddress) : Prop :=
  (σ.find? C).map (·.code) = some bytecode

/-- Freshly-deployed state with Weth bytecode at `C`. -/
def initial_state (C : AccountAddress) : EVM.State :=
  let acc : Account .EVM := { (default : Account .EVM) with code := bytecode }
  { (default : EVM.State) with
    toSharedState :=
      { (default : EvmYul.SharedState .EVM) with
        toState :=
          { (default : EvmYul.State .EVM) with
            accountMap := (default : AccountMap .EVM).insert C acc } } }

/-! ## Base case: the initial state satisfies `I` and `codeAt` -/

/-- The initial-state lookup returns the freshly-deployed account. -/
private theorem find?_initial (C : AccountAddress) :
    (initial_state C).accountMap.find? C
      = some { (default : Account .EVM) with code := bytecode } := by
  unfold initial_state
  simp only
  apply RBMap.find?_insert_of_eq
  exact Std.ReflCmp.compare_self

theorem I_initial (C : AccountAddress) :
    I (initial_state C).accountMap C := by
  unfold I
  rw [find?_initial]
  -- Goal: totalBalance ∅ ≤ (⟨0⟩ : UInt256).toNat
  show EvmSmith.Layer1.totalBalance default ≤ _
  -- default storage is ∅; totalBalance ∅ = 0 via the foldl definition.
  unfold EvmSmith.Layer1.totalBalance
  show (default : RBMap UInt256 UInt256 compare).foldl (fun acc _k v => acc + v.toNat) 0
       ≤ _
  rfl

theorem codeAt_initial (C : AccountAddress) :
    codeAt (initial_state C).accountMap C := by
  unfold codeAt
  rw [find?_initial]
  rfl

end EvmSmith.WethInvariant
