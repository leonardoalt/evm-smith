import EvmSmith.Demos.ERC20.Equivalence

/-!
# Axiom checks for the ERC-20 equivalence proofs

`#print axioms` on each headline theorem. The expected output is the
two pre-existing evm-smith axioms (T2: precompile purity; T5: keccak
collision resistance), Lean's `propext` / `Classical.choice` /
`Quot.sound` foundations, and nothing else.
-/

namespace EvmSmith.ERC20.AxiomCheck

#print axioms keccakPrefix_value
#print axioms balanceLoadOrig_value
#print axioms balanceLoadOpt_value
#print axioms balanceLoad_observable_equiv
#print axioms balanceStoreOrig_value
#print axioms balanceStoreOpt_value
#print axioms balanceStore_observable_equiv

end EvmSmith.ERC20.AxiomCheck
