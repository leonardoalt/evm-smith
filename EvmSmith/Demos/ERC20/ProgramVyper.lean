import EvmSmith.Framework

/-!
# Hand-rolled ERC-20 balance-access blocks — Vyper / Snekmate layout

A minimal slice of Vyper's `self.balanceOf[addr]` access pattern,
exactly as Vyper 0.5.0a1 compiles Snekmate's `HashMap[address,
uint256]`. We hand-roll only the 14-op balance-slot computation
prefix (no surrounding logic); the equivalence proofs in
`EquivalenceVyper.lean` compare this against the optimized version
in `OptimizedProgramVyper.lean`.

## Vyper's balance-access pattern, in bytecode

```
PUSH1 0x02           ; slot id (vyper-internal; not the "slot" reported
                     ;  by `vyper -f layout` — that's off by +1)
PUSH1 <P>            ; memory offset where the address argument lives
MLOAD                ; load address from mem[P]
PUSH1 0x20           ; offset for second mstore
MSTORE               ; mem[0x20] = address
PUSH0                ; offset for first mstore
MSTORE               ; mem[0x00] = slot id (overwrites)
PUSH1 0x40           ; size
PUSH0                ; offset
KECCAK256            ; keccak256(mem[0..0x40]) = keccak256(slot ++ addr)
SLOAD / SSTORE
```

Memory layout after both MSTOREs: `mem[0x00..0x20]` = slot id padded
to 32 bytes; `mem[0x20..0x40]` = address padded to 32 bytes. Vyper
keccaks 64 bytes total: `slot ++ addr` in big-endian.

This is **different from Solady**:
- Solady packs into a single 32-byte preimage (seed at 0x0c, addr at
  0x00, hash bytes 0x0c..0x2c).
- Vyper uses a clean 64-byte preimage (slot at 0x00, addr at 0x20).

## What this file provides

- `vyperBalanceSlot` — the slot derivation. Concrete, irreducible
  (depends on opaque `ffi.KEC`).
- `vyperKeccakPrefix` — the 9-op block (the bytecode minus the
  final SLOAD/SSTORE). Entry: arbitrary stack; memory has the address
  at offset `keyMemOffset`. Exit: `[slot_value :: rest]`.
- `vyperBalanceLoadOrigBlock` — `vyperKeccakPrefix ++ [SLOAD]`.
- `vyperBalanceStoreOrigBlock` — same prefix + `SSTORE`. SSTORE pops
  `[key, value]` so the value must be below the keccak-output on the
  stack going in.
-/

namespace EvmSmith.ERC20Vyper
open EvmYul EvmYul.EVM EvmSmith

/-! ## Constants -/

/-- Vyper's emitted slot id for `balanceOf` (= layout-JSON's
`balanceOf.slot` + 1 due to Vyper's +1 internal offset). -/
def balanceSlotId : UInt256 := UInt256.ofNat 0x02

/-- Memory offset for the second mstore (where the address is
written). Solady-style 0x20. -/
def addrMemOffset : UInt256 := UInt256.ofNat 0x20

/-- Memory offset for the first mstore (where the slot id is
written). -/
def slotIdMemOffset : UInt256 := UInt256.ofNat 0x00

/-- Size of the keccak preimage (64 bytes: slot at 0x00..0x20, addr at
0x20..0x40). -/
def vyperKeccakSize : UInt256 := UInt256.ofNat 0x40

/-- Memory offset for the keccak input. -/
def vyperKeccakStart : UInt256 := UInt256.ofNat 0x00

/-! ## Balance-slot derivation

Computed by mstoring the slot id at 0x00, the address at 0x20, then
keccak'ing the 64-byte window at 0x00..0x40. Same opacity story as
the Solidity variant: `ffi.KEC` is opaque, so the term carries through
proofs symbolically. -/

private abbrev vyperBalancePreimage
    (m : MachineState) (addr : UInt256) : ByteArray :=
  let m1 := EvmYul.MachineState.mstore m addrMemOffset addr
  let m2 := EvmYul.MachineState.mstore m1 slotIdMemOffset balanceSlotId
  m2.memory.readWithPadding vyperKeccakStart.toNat vyperKeccakSize.toNat

def vyperBalanceSlot (m : MachineState) (addr : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC (vyperBalancePreimage m addr)))

/-! ## The 9-op keccak prefix

Sub-program over the 9 ops between `<key-load>` and `<sload/sstore>`:

```
PUSH1 slotId; PUSH1 <P>; MLOAD; PUSH1 0x20; MSTORE;
PUSH0; MSTORE; PUSH1 0x40; PUSH0; KECCAK256
```

— this is what Vyper emits as the balance-slot derivation, identical
at every access site (the only thing that varies is `<P>`).

Entry stack: any (the prefix doesn't consume stack inputs — the address
comes from memory).
Exit stack: `[vyperBalanceSlot ?, rest]` (where `?` is the post-mstores
machine state). -/

def vyperKeccakPrefix (keyMemOffset : UInt256) : EvmSmith.Program :=
  [ (.Push .PUSH1,  some (balanceSlotId, 1))
  , (.Push .PUSH1,  some (keyMemOffset, 1))
  , (.MLOAD,        none)
  , (.Push .PUSH1,  some (addrMemOffset, 1))
  , (.MSTORE,       none)
  , (.Push .PUSH0,  none)
  , (.MSTORE,       none)
  , (.Push .PUSH1,  some (vyperKeccakSize, 1))
  , (.Push .PUSH0,  none)
  , (.KECCAK256,    none)
  ]

def vyperBalanceLoadOrigBlock (keyMemOffset : UInt256) : EvmSmith.Program :=
  vyperKeccakPrefix keyMemOffset ++ [ (.SLOAD, none) ]

def vyperBalanceStoreOrigBlock (keyMemOffset : UInt256) : EvmSmith.Program :=
  vyperKeccakPrefix keyMemOffset ++ [ (.SSTORE, none) ]

end EvmSmith.ERC20Vyper
