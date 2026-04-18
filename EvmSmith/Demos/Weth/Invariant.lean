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

theorem I_initial (C : AccountAddress) :
    I (initial_state C).accountMap C := by
  sorry

theorem codeAt_initial (C : AccountAddress) :
    codeAt (initial_state C).accountMap C := by
  sorry

end EvmSmith.WethInvariant
