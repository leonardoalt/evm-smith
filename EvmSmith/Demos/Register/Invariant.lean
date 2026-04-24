import EvmYul.Frame
import EvmSmith.Demos.Register.Program

/-!
# Register — inductive invariant bundle

`RegInv` packages together the two load-bearing conjuncts for the
balance-monotonicity theorem:

1. `codeAt σ C` — the runtime at `C` is Register's 20-byte bytecode.
   This is inductive: no step in the transaction deposits new code
   at `C` (ruled out by the `noCreatesC` boundary hypothesis, which
   forbids `CREATE`/`CREATE2` from deriving address `C`).
2. `b₀ ≤ balanceOf σ C` — the monotone lower bound we're proving.

The SELFDESTRUCT exclusion `C ∉ A.selfDestructSet` is kept as a separate
hypothesis rather than a `RegInv` conjunct, because we can prove it
holds throughout a Register-run by observing that only frames with
`Iₐ = C` add to the SD-set, and those run Register's code which
contains no SELFDESTRUCT.
-/

namespace EvmSmith.Register
open EvmYul EvmYul.Frame

/-- The runtime code at address `C` is Register's bytecode. -/
def codeAt (σ : AccountMap .EVM) (C : AccountAddress) : Prop :=
  (σ.find? C).map (·.code) = some bytecode

/-- The inductive invariant. -/
structure RegInv (σ : AccountMap .EVM) (C : AccountAddress) (b₀ : ℕ) : Prop where
  code : codeAt σ C
  bal  : b₀ ≤ balanceOf σ C

end EvmSmith.Register
