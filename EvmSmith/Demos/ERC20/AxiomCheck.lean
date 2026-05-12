import EvmSmith.Demos.ERC20.Equivalence
import EvmSmith.Demos.ERC20.EquivalenceVyper
import EvmSmith.Demos.ERC20.Spec

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

#print axioms EvmSmith.ERC20Vyper.vyperOptPrefix_value
#print axioms EvmSmith.ERC20Vyper.vyperBalanceLoadOpt_value
#print axioms EvmSmith.ERC20Vyper.vyperBalanceLoad_relational_equiv

#print axioms EvmYul.UInt256.lnot_injective
#print axioms EvmYul.UInt256.lnot_toNat
#print axioms EvmSmith.ERC20.distinct_addresses_distinct_opt_slots
#print axioms EvmSmith.ERC20Vyper.distinct_addresses_distinct_opt_slots

#print axioms EvmSmith.ERC20.Spec.mint_refines
#print axioms EvmSmith.ERC20.Spec.burn_refines
#print axioms EvmSmith.ERC20.Spec.transfer_refines
#print axioms EvmSmith.ERC20.Spec.lnotSlotAbstraction

end EvmSmith.ERC20.AxiomCheck
