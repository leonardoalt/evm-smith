import EvmSmith.Framework
import EvmSmith.Demos.ERC20.Program

/-!
# Hand-rolled ERC-20 bytecode programs — address-as-slot layout

The optimized counterpart to `Program.lean`. Balances are stored at
`uint256(uint160(addr))` directly: no `MSTORE`, no `KECCAK256`. Allowances
and totalSupply would (in a full implementation) keep Solady's keccak
layout — but they aren't touched by the affected functions we prove
equivalent here.

Pairs with `Program.lean`'s `balanceLoadOrigBlock` /
`balanceStoreOrigBlock`. Equivalence theorems live in
`Equivalence.lean`.
-/

namespace EvmSmith.ERC20
open EvmYul EvmYul.EVM EvmSmith

/-- The optimized "balance-slot derivation": just the address itself.
This is trivially injective in the address (it's the identity, on
canonical 160-bit-clean addresses). -/
def balanceSlotOfOpt (addr : UInt256) : UInt256 := addr

/-- Optimized balance-load block: just `SLOAD` on the address.
Entry stack `[addr, ...]`, exit stack `[sload addr, ...]`. -/
def balanceLoadOptBlock : EvmSmith.Program :=
  [ (.SLOAD, none) ]

/-- Optimized balance-store block: `SSTORE` directly on the address.
Entry stack `[addr, val, ...]`, exit stack `[...]`. -/
def balanceStoreOptBlock : EvmSmith.Program :=
  [ (.SSTORE, none) ]

end EvmSmith.ERC20
