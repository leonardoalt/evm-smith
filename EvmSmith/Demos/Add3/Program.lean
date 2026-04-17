import EvmSmith.Framework

/-!
# The `add3` program

A small EVM contract that reads three 256-bit words from calldata at offsets
0, 32, 64, sums them, writes the sum to `memory[0:32]`, and returns those
32 bytes.

This is the worked example the repository ships with. Use it as a template
for defining your own programs: give a `Program` value (the symbolic
opcode sequence), optionally the raw `ByteArray` bytecode, and then write
a correctness proof in a companion `Proofs.lean` file.

Assembly (with PCs):
```
  pc  bytes              mnemonic
  0   60 00              PUSH1 0x00      -- stack: [0]
  2   35                 CALLDATALOAD    -- stack: [a]
  3   60 20              PUSH1 0x20      -- stack: [32, a]
  5   35                 CALLDATALOAD    -- stack: [b, a]
  6   01                 ADD             -- stack: [a+b]
  7   60 40              PUSH1 0x40      -- stack: [64, a+b]
  9   35                 CALLDATALOAD    -- stack: [c, a+b]
  10  01                 ADD             -- stack: [a+b+c]
  11  60 00              PUSH1 0x00      -- stack: [0, a+b+c]
  13  52                 MSTORE          -- mem[0:32] := a+b+c; stack: []
  14  60 20              PUSH1 0x20      -- stack: [32]
  16  60 00              PUSH1 0x00      -- stack: [0, 32]
  18  f3                 RETURN          -- return mem[0:32]
```
-/

namespace EvmSmith.Add3
open EvmYul EvmYul.EVM

/-- The compute prefix: reads calldata and sums, stops before `MSTORE`.
    After running this on a state whose calldata reads as `a`, `b`, `c` at
    offsets 0, 32, 64, the top of the stack is `a + b + c`. -/
def compute : EvmSmith.Program :=
  [ (.Push .PUSH1,    some (UInt256.ofNat 0, 1))
  , (.CALLDATALOAD,   none)
  , (.Push .PUSH1,    some (UInt256.ofNat 32, 1))
  , (.CALLDATALOAD,   none)
  , (.ADD,            none)
  , (.Push .PUSH1,    some (UInt256.ofNat 64, 1))
  , (.CALLDATALOAD,   none)
  , (.ADD,            none)
  ]

/-- The full program: compute + store-and-return. -/
def program : EvmSmith.Program :=
  compute ++
  [ (.Push .PUSH1,    some (UInt256.ofNat 0, 1))
  , (.MSTORE,         none)
  , (.Push .PUSH1,    some (UInt256.ofNat 32, 1))
  , (.Push .PUSH1,    some (UInt256.ofNat 0, 1))
  , (.RETURN,         none)
  ]

/-- Raw bytecode for the full program, useful if you want to feed it to a real
    EVM interpreter or decode it back via the upstream `EVM.decode`. Matches
    the assembly listing in this file's docstring. -/
def bytecode : ByteArray := ⟨#[
  0x60, 0x00,   -- PUSH1 0
  0x35,         -- CALLDATALOAD
  0x60, 0x20,   -- PUSH1 32
  0x35,         -- CALLDATALOAD
  0x01,         -- ADD
  0x60, 0x40,   -- PUSH1 64
  0x35,         -- CALLDATALOAD
  0x01,         -- ADD
  0x60, 0x00,   -- PUSH1 0
  0x52,         -- MSTORE
  0x60, 0x20,   -- PUSH1 32
  0x60, 0x00,   -- PUSH1 0
  0xf3          -- RETURN
]⟩

end EvmSmith.Add3
