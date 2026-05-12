# Vyper / Snekmate ERC-20: Storage Layout & Optimization

Companion to [`STORAGE_LAYOUT.md`](./STORAGE_LAYOUT.md) (Solidity /
Solady variant). Same optimization idea, balance slot from the
address directly. But applied at the **bytecode level** to Vyper's
compiled output, with one extra twist.

## How Vyper lays out storage

Snekmate's [`erc20.vy`](https://github.com/pcaversaccio/snekmate/blob/main/src/snekmate/tokens/erc20.vy)
uses idiomatic Vyper storage:

```vyper
balanceOf: public(HashMap[address, uint256])
allowance: public(HashMap[address, HashMap[address, uint256]])
totalSupply: public(uint256)
is_minter: public(HashMap[address, bool])
nonces: public(HashMap[address, uint256])
```

Vyper assigns each module-level state variable a sequential slot id at
compile time. For our [`mock.vy`](./foundry-vyper/src/mock.vy)
(snekmate erc20 + ownable):

| Slot (runtime emission) | Variable          | Layout-JSON's "slot" field |
|-------------------------|-------------------|----------------------------|
| `0x01`                  | `ownable.owner`   | `0`                        |
| `0x02`                  | `erc20.balanceOf` | `1`                        |
| `0x03`                  | `erc20.allowance` | `2`                        |
| `0x04`                  | `totalSupply`     | `3`                        |
| `0x05`                  | `is_minter`       | `4`                        |
| `0x06`                  | `nonces`          | `5`                        |

There's a known **+1 offset** between Vyper's `-f layout` output and
the actual bytecode emission. The patcher disambiguates by reading the
slot id directly out of the `balanceOf` public getter's bytecode.

## What Vyper emits for `self.balanceOf[addr]`

Across every balance access, read or write. Vyper emits the
identical 14-byte prefix (variable: `<P>`, the memory offset where the
caller has parked the address argument):

```
60 02            PUSH1 0x02       ; slot id
60 <P>           PUSH1 <P>        ; memory offset for the address arg
51               MLOAD            ; addr := mem[P]
60 20            PUSH1 0x20
52               MSTORE           ; mem[0x20] = addr (zero-padded to 32B)
5f               PUSH0
52               MSTORE           ; mem[0x00] = 0x02 (slot)
60 40            PUSH1 0x40
5f               PUSH0
20               KECCAK256        ; keccak(mem[0x00..0x40])
                                  ;   = keccak(slot ++ addr)
```

Total: 15 bytes including the trailing `SLOAD` (`54`) or `SSTORE`
(`55`).

This differs from Solady's prefix in two ways:

1. **64-byte preimage vs 32-byte preimage.** Vyper uses
   `keccak256(slot ++ addr)` over a clean 64-byte window. Solady packs
   `addr ++ seed` into 32 bytes with a 4-byte seed embedded at offset
   `0x0c`, exploiting the way `mstore` overlaps. The Vyper layout is
   cleaner; the Solady layout is slightly more compact.

2. **Address from memory vs from stack.** Vyper mloads the address
   from `mem[P]` (the function-argument staging area). Solady has the
   address already on the stack and uses `mstore(0x00, caller())` /
   `mstore(0x00, owner)` directly.

The keccak hash itself uses the same `KECCAK256` opcode, with the
same opaque `ffi.KEC` in EVMYulLean. So the proof story (Keccak
vanishes from the equivalence argument) carries over identically.

## The optimization

Same idea as the Solady variant: skip the keccak, use the address as
the slot. But Vyper raises a wrinkle:

### Wrinkle: Vyper's named slots are at the bottom

In the Solady setup, named slots like `_TOTAL_SUPPLY_SLOT =
0x05345cdf77eb68f44c` (~`2^46`) sit far above any realistic deployed
address (max `2^160 - 1`). Using `uint256(addr)` directly as a balance
slot was safe.

In Vyper, named slots live at `0x01..0x06`. Real users in tests have
small addresses (`address(0xAA)`, `address(0x01)`, …). Using `addr`
directly would put `balance[0x01]` at slot `1`, **overwriting**
`ownable.owner`. A fuzz test caught exactly this: `mint(0x01, value)`
on the naive optimized version corrupted the owner field.

### Fix: `NOT(addr)` as the slot

The patched prefix uses bitwise NOT to map any 160-bit address into
the high half of slot space:

```
JUMPDEST × 10       ; no-op padding (length-preserving)
60 <P>              PUSH1 <P>
51                  MLOAD             ; addr := mem[P]
19                  NOT               ; slot := ~addr
54 or 55            SLOAD or SSTORE
```

`NOT(addr)` for any 160-bit address is `2^256 - 1 - addr ∈
[2^256 - 2^160, 2^256 - 1)`. Every value in that range has its top 96
bits all-one. **No** named slot lives there (Vyper's are `0..16`),
and **no** keccak-derived slot lands there unless someone breaks
Keccak's preimage resistance for 256-bit outputs (the same trust
assumption Vyper, Solady, and every Solidity mapping already rely on).

`NOT` is a one-byte EVM opcode. Total patched prefix: 15 bytes,
length-preserving with the original. JUMPDESTs at the front are pure
no-ops (1 gas each, no state changes); the real work happens last so
the SLOAD/SSTORE consumes the freshly-computed slot.

### Why length-preserving

Vyper's deploy code embeds the runtime size as a literal immediate
(passed to CODECOPY during construction). Every `PUSH2 <jumpdest>` is
an absolute byte offset. If the patched runtime were shorter or
longer than the original, the deploy code would copy the wrong number
of bytes, or every jumpdest would land at the wrong target. The
patcher therefore pads with JUMPDESTs to keep every offset stable.

This is the reason we don't just "delete" the keccak prefix and
slide everything up by 11 bytes. Even if every consumer of jumpdest
addresses recomputed them, the runtime-length immediate inside the
deploy bytecode would still be wrong.

## The patcher

[`script/patch.py`](./foundry-vyper/script/patch.py) is the offline
Python patcher used to dump runtime hex files for inspection.
[`test/BytecodePatcher.sol`](./foundry-vyper/test/BytecodePatcher.sol)
is the in-place Solidity patcher used by the tests via `vm.etch` (so
the immutables initialized by the real Vyper constructor stay valid).

Both implement the same logic:

1. Walk the runtime bytecode, treating PUSH-immediates as opaque data.
2. At each PUSH1 boundary, check whether the next 15 bytes match the
   Vyper balance-keccak pattern (`60 02 60 <P> 51 60 20 52 5f 52 60
   40 5f 20 <54|55>`).
3. If yes, replace with `(JUMPDEST × 10) 60 <P> 51 19 <54|55>`.
4. Cross-check: the count of patched sites must match the count of
   `self.balanceOf[...]` accesses in the source AST (9 sites in our
   mock). Fail closed otherwise.

The Python patcher's AST-source counter walks the import graph
(Snekmate's modules), so changes upstream in Snekmate that add more
balance accesses get caught.

## Test results

| Suite                          | Result      |
|--------------------------------|-------------|
| `OriginalVyperERC20Test`       | 21/21 pass  |
| `OptimizedVyperERC20Test`      | 21/21 pass  |
| `ERC20VyperGasCompareTest`     | 8/8 pass    |

Identical public behaviour across both backends.

## Gas table

From `forge test --match-contract ERC20VyperGasCompareTest -vv`:

| Operation              | Original (gas) | Patched (gas) | Δ      |
|------------------------|----------------|---------------|--------|
| `balanceOf` (warm)     |            920 |           872 | -48    |
| `mint` (fresh)         |         51,810 |        51,714 | -96    |
| `mint` (warm)          |          3,510 |         3,414 | -96    |
| `burn`                 |          3,216 |         3,114 | -102   |
| `transfer` (fresh)     |         25,506 |        25,314 | -192   |
| `transfer` (warm)      |          3,606 |         3,414 | -192   |
| `transferFrom`         |         28,137 |        27,945 | -192   |
| runtime size           |    6,602 bytes |   6,602 bytes |  0     |

The per-keccak-saved overhead is roughly 50 gas (KECCAK256 36 +
2×MSTORE 6 + 3×PUSH 9 - 10×JUMPDEST 10 - PUSH 3 - MLOAD 3 - NOT 3 ≈
48). Vyper does 1 keccak per balanceOf access, 2 per mint/burn, 4 per
transfer/transferFrom, hence the proportional deltas.

Solady-via-`solc` saves fewer keccaks per function because the
compiler reuses the slot value across the read/write of the same
mapping access. Vyper's HashMap pattern recomputes every time. That's
why Vyper-side deltas are bigger.

## Why this only works because of `NOT`

Without the `NOT` substitution, the optimization is unsafe in Vyper:
any user with an address in `[0x01, max-named-slot]` collides with
named state. With `NOT`, we get the bijectivity (`NOT` is bijective on
`UInt256`) and the high-bit guarantee, every balance lives strictly
above `2^160`, in a region neither named slots nor keccak slots can
practically reach.

This is the kind of subtlety that's easy to miss when hand-writing an
optimized contract. The fuzz test caught it before any real funds
were involved; the patched version with `NOT` then passes the same
fuzz suite cleanly. The proof in `EquivalenceVyper.lean` formalizes
the soundness of the `NOT`-as-slot mapping under the per-address
storage relation.
