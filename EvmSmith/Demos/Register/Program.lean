import EvmSmith.Framework

/-!
# The `Register` program (with reentrance-exposure)

Reads one 256-bit word from calldata at offset 0, stores it at
`storage[msg.sender]`, then issues a `CALL` to `msg.sender` with
value 0 and all remaining gas forwarded. The CALL's return data is
discarded.

The value forwarded on the CALL is hard-coded to 0 — this is the
structural fact behind the balance-monotonicity invariant proved
in `BalanceMono.lean`: no execution path in Register's bytecode can
move ETH *out* of the contract. External callers can force ETH *in*
(via `SELFDESTRUCT` or coinbase reward), and they can reenter during
the CALL — but the reentry itself runs Register's bytecode, which
again only issues a `CALL` with value 0.

Assembly (20 bytes):

```
  pc  bytes    mnemonic            effect
  0   60 00    PUSH1 0x00          storage-value calldata offset
  2   35       CALLDATALOAD        x = cd[0:32]
  3   33       CALLER              sender
  4   55       SSTORE              storage[sender] = x
  5   60 00    PUSH1 0             retSize
  7   60 00    PUSH1 0             retOffset
  9   60 00    PUSH1 0             argsSize
  11  60 00    PUSH1 0             argsOffset
  13  60 00    PUSH1 0             value = 0
  15  33       CALLER              address = sender
  16  5a       GAS                 gas = remaining
  17  f1       CALL                invoke; reentrance possible here
  18  50       POP                 discard success flag
  19  00       STOP
```

Stack-top ordering: CALL's `pop7` pops head-first; `push v s = v :: s`
puts values on top. So the last-pushed `GAS` is popped first as
`gas`, and the first-pushed `retSize` is popped last — matches the
EVM spec `gas, to, value, inOff, inSize, outOff, outSize`.

Total runtime: 20 bytes. The raw `bytecode : ByteArray` value is
defined below; `lake exe register-dump-bytecode` writes the hex
form to `foundry/test/Register.bytecode.hex` for the Foundry suite.
-/

namespace EvmSmith.Register
open EvmYul EvmYul.EVM

/-- The program as an opcode sequence. -/
def program : EvmSmith.Program :=
  [ (.Push .PUSH1,  some (UInt256.ofNat 0, 1))   -- 0  storage offset
  , (.CALLDATALOAD, none)                         -- 2
  , (.CALLER,       none)                         -- 3
  , (.SSTORE,       none)                         -- 4
  , (.Push .PUSH1,  some (UInt256.ofNat 0, 1))   -- 5  retSize
  , (.Push .PUSH1,  some (UInt256.ofNat 0, 1))   -- 7  retOffset
  , (.Push .PUSH1,  some (UInt256.ofNat 0, 1))   -- 9  argsSize
  , (.Push .PUSH1,  some (UInt256.ofNat 0, 1))   -- 11 argsOffset
  , (.Push .PUSH1,  some (UInt256.ofNat 0, 1))   -- 13 value = 0
  , (.CALLER,       none)                         -- 15 addr
  , (.GAS,          none)                         -- 16 gas
  , (.CALL,         none)                         -- 17
  , (.POP,          none)                         -- 18
  , (.STOP,         none)                         -- 19
  ]

/-- Runtime bytecode matching the assembly listing. -/
def bytecode : ByteArray := ⟨#[
  0x60, 0x00,   -- PUSH1 0   (storage offset)
  0x35,         -- CALLDATALOAD
  0x33,         -- CALLER
  0x55,         -- SSTORE
  0x60, 0x00,   -- PUSH1 0   (retSize)
  0x60, 0x00,   -- PUSH1 0   (retOffset)
  0x60, 0x00,   -- PUSH1 0   (argsSize)
  0x60, 0x00,   -- PUSH1 0   (argsOffset)
  0x60, 0x00,   -- PUSH1 0   (value = 0)
  0x33,         -- CALLER    (addr)
  0x5a,         -- GAS       (gas)
  0xf1,         -- CALL
  0x50,         -- POP
  0x00          -- STOP
]⟩

end EvmSmith.Register
