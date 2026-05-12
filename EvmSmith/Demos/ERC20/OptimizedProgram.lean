import EvmSmith.Framework
import EvmSmith.Demos.ERC20.Program

/-!
# Hand-rolled ERC-20 bytecode programs — NOT(addr)-as-slot layout

The optimized counterpart to `Program.lean`. Balances are stored at
`UInt256.lnot addr` (the bitwise complement of the address) — *not*
at `addr` itself. The reason is the same one that surfaced on the
Vyper side: using `addr` directly collides with Solidity-assigned
low slots, where the mock contract's `_name`, `_symbol`, and
`_decimals` live.

`UInt256.lnot addr` for any 160-bit address has the high 96 bits all
one, so the slot is always `>= 2^160`. Solidity's named slots in the
mock (0, 1, 2) and the Solady-base constants (the high
`_TOTAL_SUPPLY_SLOT`, the keccak'd allowance / nonce slots) sit
well clear. Allowances and totalSupply stay on Solady's keccak
layout, untouched.

Pairs with `Program.lean`'s `balanceLoadOrigBlock` /
`balanceStoreOrigBlock`. Equivalence theorems live in
`Equivalence.lean`.
-/

namespace EvmSmith.ERC20
open EvmYul EvmYul.EVM EvmSmith

/-- The optimized balance-slot derivation: `~addr`. Trivially
injective (bitwise NOT is a bijection on `UInt256`); maps any
160-bit address to a slot `>= 2^160`, avoiding every Solidity-
assigned low slot and the constants in the Solady base layer. -/
def balanceSlotOfOpt (addr : UInt256) : UInt256 := UInt256.lnot addr

/-- Optimized balance-load block: `NOT; SLOAD`. Entry stack
`[addr, ...]`, exit stack `[sload (~addr), ...]`. -/
def balanceLoadOptBlock : EvmSmith.Program :=
  [ (.NOT,   none)
  , (.SLOAD, none) ]

/-- Optimized balance-store block: `NOT` the address, then `SSTORE`.
Entry stack `[addr, val, ...]`, exit stack `[...]`. After the `NOT`,
the stack is `[~addr, val, ...]` — exactly what SSTORE pops. -/
def balanceStoreOptBlock : EvmSmith.Program :=
  [ (.NOT,    none)
  , (.SSTORE, none) ]

end EvmSmith.ERC20
