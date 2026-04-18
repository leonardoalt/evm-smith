import EvmSmith.Framework

/-!
# The `Register` program

Reads one 256-bit word from calldata at offset 0 and stores it at
`storage[msg.sender]` in the calling contract's own storage. Six
bytes of runtime. Exercises `CALLER` + `SSTORE` — the EVM primitives
behind Solidity's `mapping(address => uint256)`.

Assembly:

```
  pc  bytes    mnemonic            effect
  0   60 00    PUSH1 0x00          -- stack: [0]
  2   35       CALLDATALOAD        -- stack: [x]           (x = cd[0:32])
  3   33       CALLER              -- stack: [sender, x]   (UInt256 of source)
  4   55       SSTORE              -- storage[sender] = x; stack: []
  5   00       STOP                -- halt
```

Six bytes: `0x600035335500`.

Correctness theorems (functional, slot-frame, account-frame) are in
`Proofs.lean`. See the docstring there for the `hacct` precondition
and the reason Invariant 3 is `accountMap`-only.
-/

namespace EvmSmith.Register
open EvmYul EvmYul.EVM

/-- The program as an opcode sequence. -/
def program : EvmSmith.Program :=
  [ (.Push .PUSH1,  some (UInt256.ofNat 0, 1))
  , (.CALLDATALOAD, none)
  , (.CALLER,       none)
  , (.SSTORE,       none)
  , (.STOP,         none)
  ]

/-- Runtime bytecode matching the assembly listing. -/
def bytecode : ByteArray := ⟨#[
  0x60, 0x00,   -- PUSH1 0
  0x35,         -- CALLDATALOAD
  0x33,         -- CALLER
  0x55,         -- SSTORE
  0x00          -- STOP
]⟩

end EvmSmith.Register
