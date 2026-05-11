import EvmSmith.Framework
import EvmSmith.Demos.ERC20.ProgramVyper

/-!
# Vyper / Snekmate balance-access — optimized (patched) layout

The length-preserving peephole the bytecode patcher emits. Replaces
the 14-byte keccak prefix + 1-byte SLOAD/SSTORE with:

```
JUMPDEST × 10        ; no-op padding
PUSH1 <P>            ; memory offset for the address
MLOAD                ; load address from mem[P]
NOT                  ; ~addr — avoids collision with Vyper's named slots
SLOAD / SSTORE
```

Same 15-byte width as the original (length-preserving so JUMPDEST
absolute addresses elsewhere in the runtime stay valid).

`NOT(addr)` is the trick: low-address users would otherwise collide
with Vyper's named state vars (owner at slot 1, totalSupply at 4,
etc.). Bitwise NOT maps any 160-bit address to a 256-bit slot with
the high 96 bits all-one, so the slot is always > 2^160 — above every
named slot and above every concrete keccak-derived slot in practical
range. Bijective on addresses, so still injective.
-/

namespace EvmSmith.ERC20Vyper
open EvmYul EvmYul.EVM EvmSmith

/-- Optimized balance-slot derivation: just `NOT(addr)`. Trivially
injective in the address (bitwise NOT is a bijection on `UInt256`). -/
def vyperBalanceSlotOpt (addr : UInt256) : UInt256 := UInt256.lnot addr

/-- 14-op optimized prefix (10 no-op JUMPDESTs, PUSH1 P, MLOAD, NOT).
Pairs 1-for-1 with the 9-op keccak prefix. -/
def vyperOptPrefix (keyMemOffset : UInt256) : EvmSmith.Program :=
  [ (.JUMPDEST, none), (.JUMPDEST, none), (.JUMPDEST, none)
  , (.JUMPDEST, none), (.JUMPDEST, none), (.JUMPDEST, none)
  , (.JUMPDEST, none), (.JUMPDEST, none), (.JUMPDEST, none)
  , (.JUMPDEST, none)
  , (.Push .PUSH1, some (keyMemOffset, 1))
  , (.MLOAD,       none)
  , (.NOT,         none)
  ]

def vyperBalanceLoadOptBlock (keyMemOffset : UInt256) : EvmSmith.Program :=
  vyperOptPrefix keyMemOffset ++ [ (.SLOAD, none) ]

def vyperBalanceStoreOptBlock (keyMemOffset : UInt256) : EvmSmith.Program :=
  vyperOptPrefix keyMemOffset ++ [ (.SSTORE, none) ]

end EvmSmith.ERC20Vyper
