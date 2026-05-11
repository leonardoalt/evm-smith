import EvmSmith.Framework

/-!
# Hand-rolled ERC-20 balance-access blocks — keccak-balance layout

A minimal slice of Solady's ERC-20 in raw EVM bytecode, just covering
the **balance-access prefix** that the optimization targets. The rest
of an ERC-20 (selector dispatch, allowance accounting, log emission,
totalSupply tracking) is byte-identical between layouts and doesn't
need to be proved equivalent.

## Solady's balance-access pattern, in bytecode

```
PUSH4 0x87a211a2       ; seed
PUSH1 0x0c             ; offset for seed mstore
MSTORE                 ; mem[0x0c..0x2c] = seed (consumes [0x0c, seed])
PUSH1 0x00             ; offset for addr mstore (addr is already on stack)
MSTORE                 ; mem[0x00..0x20] = addr (consumes [0x00, addr])
PUSH1 0x20             ; size
PUSH1 0x0c             ; offset
KECCAK256              ; pushes keccak256(mem[0x0c..0x2c])
```

EVM convention: `MSTORE` pops `[offset, value]` with `offset` on top.
That's why the immediate offset is pushed *after* the value already on
stack.

## What this file gives you

- `balanceSlotSeed` — Solady's `_BALANCE_SLOT_SEED = 0x87a211a2`.
- `balanceSlotOf addr` — the slot derivation Solady uses. Defined
  *concretely* as the expression the prefix produces (via opaque
  `ffi.KEC`), so the equivalence proof never reduces Keccak.
- `keccakPrefix` — the 8-op balance-slot-derivation block, taking
  `[addr, ...]` on entry and leaving `[balanceSlotOf addr, ...]`.
- `balanceLoadOrigBlock` — `keccakPrefix ++ [SLOAD]`.
- `balanceStoreOrigBlock` — same prefix + a separate SSTORE wrapper.

## What "balanceSlotOf addr" means

`balanceSlotOf` is defined as the *exact* `UInt256` term that
`MSTORE seed; MSTORE addr; KECCAK256(0x0c, 0x20)` produces. The
underlying `ffi.KEC` is `opaque` in EVMYulLean, so this term is
irreducible — perfect for our equivalence proofs, which never need
to know what Keccak computes, only that the bytecode-side prefix
produces *exactly* the same Lean term.
-/

namespace EvmSmith.ERC20
open EvmYul EvmYul.EVM EvmSmith

/-! ## Constants -/

/-- Solady's `_BALANCE_SLOT_SEED = 0x87a211a2`. -/
def balanceSlotSeed : UInt256 := UInt256.ofNat 0x87a211a2

/-- Memory offset where the seed is mstored: 0x0c. -/
def seedOffset : UInt256 := UInt256.ofNat 0x0c

/-- Memory offset where the address is mstored: 0x00. -/
def addrOffset : UInt256 := UInt256.ofNat 0

/-- Size of the keccak preimage: 32 bytes. -/
def keccakSize : UInt256 := UInt256.ofNat 0x20

/-! ## Balance-slot derivation

`balanceSlotOf addr` is *defined* to be exactly what the keccak prefix
computes, when started from any `MachineState`. The starting
`MachineState` matters: the keccak reads bytes from memory, which the
two MSTOREs just wrote. We parameterize the definition on the *base*
`MachineState`, then prove the prefix produces this exact term in
`Equivalence.lean`. -/

/-- The memory bytes that Solady's prefix keccak's, computed from a
base `MachineState`. Run two `mstore`s (seed at 0x0c, addr at 0x00),
then read 32 bytes from offset 0x0c. -/
private abbrev balancePreimage (m : MachineState) (addr : UInt256) : ByteArray :=
  let m1 := EvmYul.MachineState.mstore m seedOffset balanceSlotSeed
  let m2 := EvmYul.MachineState.mstore m1 addrOffset addr
  m2.memory.readWithPadding seedOffset.toNat keccakSize.toNat

/-- The slot-derivation function: `Address → UInt256`, computed
relative to a base `MachineState`. In practice the only thing that
matters is the address (the memory writes overwrite their footprint),
but we keep the dependency explicit so the characterization theorem
applies to *any* starting `MachineState`. -/
def balanceSlotOf (m : MachineState) (addr : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (balancePreimage m addr)))

/-! ## The keccak balance-slot prefix

8-op block: two `(seed/addr, offset, MSTORE)` pairs then `PUSH; PUSH;
KECCAK256`. Entry stack: `[addr, ...]`. Exit stack:
`[balanceSlotOf <postMState> addr, ...]`. -/

def keccakPrefix : EvmSmith.Program :=
  [ -- PUSH4 seed
    (.Push .PUSH4,  some (balanceSlotSeed, 4))
    -- PUSH1 0x0c
  , (.Push .PUSH1,  some (seedOffset, 1))
    -- MSTORE  -- pops [0x0c, seed]
  , (.MSTORE,       none)
    -- PUSH1 0x00
  , (.Push .PUSH1,  some (addrOffset, 1))
    -- MSTORE  -- pops [0x00, addr]
  , (.MSTORE,       none)
    -- PUSH1 0x20
  , (.Push .PUSH1,  some (keccakSize, 1))
    -- PUSH1 0x0c
  , (.Push .PUSH1,  some (seedOffset, 1))
    -- KECCAK256
  , (.KECCAK256,    none)
  ]

/-- Balance load (Solady-style): keccak prefix + SLOAD. Entry
`[addr, ...]`, exit `[sload <slot>, ...]`. -/
def balanceLoadOrigBlock : EvmSmith.Program :=
  keccakPrefix ++ [ (.SLOAD, none) ]

/-- Balance store (Solady-style): the value to store is below the
address on entry (`[addr, value, ...]`). After the prefix we have
`[slot, value, ...]` which is exactly the SSTORE pop order. -/
def balanceStoreOrigBlock : EvmSmith.Program :=
  keccakPrefix ++ [ (.SSTORE, none) ]

end EvmSmith.ERC20
