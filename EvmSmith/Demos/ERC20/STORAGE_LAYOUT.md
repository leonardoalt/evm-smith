# ERC-20 Storage Layout — Investigation

A walk-through of where Solady's ERC-20 puts its data, why that costs
gas every transfer, and what we change to make balances cheaper.

## Solady's layout (the original)

Solady's [`ERC20.sol`](./foundry/lib/solady/src/tokens/ERC20.sol)
abandons Solidity's `mapping(address => uint256)` storage layout
entirely and writes the storage assembly itself. Storage is keyed by
keccak hashes of `(address, seed)` packings, but in a more compact way
than the Solidity compiler emits.

Four kinds of state live in the contract:

| Bucket            | Slot derivation                                                                          | Comment                                                                                                                  |
|-------------------|------------------------------------------------------------------------------------------|--------------------------------------------------------------------------------------------------------------------------|
| `totalSupply`     | Constant slot `0x05345cdf77eb68f44c`                                                     | Fixed, dispatches via `sload(_TOTAL_SUPPLY_SLOT)`.                                                                       |
| `balances[a]`     | `keccak256(addr_padded ++ seed)` where `seed = 0x87a211a2` (4 bytes) and preimage is 32B | Address mstored at `0x00`; seed mstored at `0x0c`; hash spans `0x0c..0x2c`.                                              |
| `allowances[o][s]`| `keccak256(addr_o ++ seed ++ addr_s)` where `seed = 0x7f5e9f20`; preimage is 52B         | Spender at `0x20`, then `(owner<<32) | seed` at `0x0c`; hash spans `0x0c..0x40`.                                         |
| `nonces[a]`       | `keccak256(addr ++ seed)` where `seed = 0x38377508`                                      | Used for EIP-2612 permit. Same pattern as balances.                                                                      |

(See Solady source comments around lines 73–98 for the canonical
specification.)

### What the balance read looks like (in EVM)

The Solidity compiler emits the following five-instruction prefix
every time it needs to compute `balances[owner]`:

```
mstore(0x0c, 0x87a211a2)     ; memory[0x0c..0x2c] = seed (32-byte BE)
mstore(0x00, owner)          ; memory[0x00..0x20] = padded(owner)
push 0x20                    ; size = 32 bytes
push 0x0c                    ; offset = 0x0c
keccak256                    ; -> top = keccak256(memory[0x0c..0x2c])
```

After two `mstore`s, memory `0x0c..0x2c` contains
`[20 bytes of address][8 zero bytes][4 bytes of seed 0x87a211a2]` —
exactly the 32-byte preimage hashed.

Then `SLOAD` is called on the resulting hash, producing the user's
balance.

For `transfer`, this five-instruction prefix appears **twice**
(`fromBalance` and `toBalance`), and the corresponding `SSTORE`
prefix is the same prefix repeated (the slot is computed once and
held on stack, but `_transfer` still recomputes for `to`).

### What the cost is

Each balance access pays for:

- One `KECCAK256` of 32 bytes:
  - Base 30 gas, plus 6 gas per 32-byte word: **36 gas**
- Two `MSTORE`s into the scratch region:
  - 3 gas each, plus memory expansion when the contract first touches
    memory: **at least 6 gas**, plus expansion the first time
- Bytecode: ~12-16 extra bytes per balance access site (5 ops + 2
  pushes), each contributing to deployment cost and to the per-call
  `PUSH/DUP/SWAP` housekeeping needed to stage operands.

A successful `transfer(to, amount)` in Solady touches the balance of
`from` (load + store) and the balance of `to` (load + store) — 4
balance accesses, so ~4 × 42 = ~168 gas paid just for the keccak slot
computation, plus the bytecode cost.

## The optimization: address-as-slot

Solidity (and Solady) need keccak because **multiple maps share the
same storage**. The keccak hash of `(key, slot)` is what prevents
`balances[A]` and `allowances[A][B]` from colliding when both `A` and
`B` are small addresses near zero.

But that's only a constraint if all those maps live in the same contract.
An ERC-20 contract has *one* contract storage, and we can lay it out
however we like — as long as the layout is **injective** for each
quantity we care about.

The optimization stores `balances[addr]` at slot `uint256(uint160(addr))`
directly. Allowances stay keccak-derived. The two layouts can't
collide:

- A balance slot is at most `2^160 - 1` (any address).
- An allowance slot is the keccak of a 52-byte preimage. The chance of
  this colliding with any 160-bit-or-less value is `2^-96` per slot —
  this is the same collision-resistance the original layout relies on
  for *all* its slots, so we're not making the trust assumption worse.

Same argument for `_TOTAL_SUPPLY_SLOT = 0x05345cdf77eb68f44c` and nonce
slots: they're all keccak-derived, so colliding with any address-slot
takes a 160-bit preimage hit.

### What the balance read looks like now

```
sload(uint256(uint160(owner)))
```

No memory write, no hash. The address is already in low-160 bits of a
stack word; a `SHL 96 / SHR 96` pair cleans the high bits if the caller
didn't (3 gas total), then `SLOAD` runs on it directly.

Per-access savings on warm slots:

- `KECCAK256` removed: **-36 gas**
- Two `MSTORE`s removed (modulo memory expansion): **-6 gas** if memory
  was already paid for (and it might not be — see below).
- `PUSH 0x20; PUSH 0x0c` removed: **-6 gas**.

That's ~48 gas per balance access. A `transfer` has 4 balance accesses,
~192 gas of savings — but in practice the savings are less than that
because the optimizer reuses the keccak'd slot value across the
matched load/store, and because some of the mstores get amortized
across access sites that share the scratch memory.

### What we measured

From `forge test --match-contract ERC20GasCompareTest` against the two
Solady-based mocks compiled at the same optimizer settings:

| Operation              | Keccak layout (gas) | Address-as-slot (gas) | Delta  |
|------------------------|---------------------|-----------------------|--------|
| `balanceOf` (warm)     |              1,117  |                1,064  |  -53   |
| `mint` (fresh recipient)|            49,665  |               49,616  |  -49   |
| `mint` (warm recipient)|             3,365  |                3,316  |  -49   |
| `burn`                 |             3,304  |                3,244  |  -60   |
| `transfer` (fresh-to)  |            25,377  |               25,285  |  -92   |
| `transfer` (warm-to)   |             3,477  |                3,385  |  -92   |
| `transferFrom`         |            25,906  |               25,826  |  -80   |

Plus a constant 60 bytes of runtime savings (2,510 → 2,450 bytes
deployed), because the keccak prefix is compiled in fewer times.

(Numbers reproducible via `forge test --match-contract
ERC20GasCompareTest -vv` from the
`EvmSmith/Demos/ERC20/foundry/` directory.)

## Why this is safe

The risk on any storage-layout change is **slot collisions**: two
distinct logical states ending up at the same storage slot, so writing
one corrupts the other.

The orig layout's collision-resistance comes from keccak; the opt
layout's collision-resistance for balances vs allowances/nonces/total
supply also comes from keccak (since the other slots are still
keccak-derived). We're not relaxing any cryptographic assumption — we
just shorten the path for the balance bucket because it only needs to
be injective in the address.

The proofs in `Equivalence.lean` formalize this argument at the
bytecode level: under a storage-translation relation, the affected
functions in both layouts produce identical observable behavior.

## Why allowances stay keccak-derived

Allowances are keyed by *two* addresses `(owner, spender)`. Their
combined preimage is 52 bytes, so we can't fit the joint key in a
single 256-bit slot without further packing — and the moment we pack,
we lose the strong injectivity property the proof relies on. Keccak
is the right tool for the two-key case.

`nonces` is per-owner, so in principle could use the same address-as-
slot trick. We don't change it because (a) nonces collide trivially
with balances when both use raw addresses — and balances and nonces
would then live at *the same* slot, a real bug. To keep nonces direct
we'd need a different injective embedding (e.g., `(uint256(addr) | tag)`
with a high-bit tag), but the gain is small relative to the proof
complexity. Out of scope for this pass.

## Bytecode-level diff: `transfer`

A side-by-side at the relevant sites in the two compiled MockERC20
contracts. Annotations show the differing prefix; everything else is
byte-identical.

### Original (keccak balance load)

```
; ... function prelude, msg.sender on stack ...
mstore(0x0c, 0x87a211a2)        ; PUSH4 0x87a211a2; PUSH1 0x0c; MSTORE
mstore(0x00, caller())          ; CALLER; PUSH1 0x00; MSTORE
push 0x20                       ; PUSH1 0x20
push 0x0c                       ; PUSH1 0x0c
keccak256                       ; KECCAK256  → fromSlot
dup1                            ; DUP1
sload                           ; SLOAD      → fromBal
; check, sstore, ...
```

### Optimized (address-as-slot)

```
; ... function prelude, msg.sender on stack ...
caller()                        ; CALLER     → fromAddr (already clean low-160)
dup1                            ; DUP1
sload                           ; SLOAD      → fromBal
; check, sstore, ...
```

We save the four-byte `0x87a211a2` push, two `MSTORE`s, two `PUSH1`s,
and the `KECCAK256` op. Plus we avoid touching memory at all, which
side-steps memory expansion on the very first call within a transaction.
