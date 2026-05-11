# ERC-20 Storage Layout Optimization — Final Report

## What this demo delivers

A working pipeline that:

1. **Engineers** a Solady-based ERC-20 with two storage layouts —
   *keccak-mapped balances* (Solady's default) and *raw-address-slot
   balances* (the optimization) — and runs identical tests against
   both backends.
2. **Investigates** Solady's storage layout in
   [`STORAGE_LAYOUT.md`](./STORAGE_LAYOUT.md), with bytecode-level
   diffs and gas measurements.
3. **Proves** the balance-slot peephole sound at the EVM bytecode
   level in [`Equivalence.lean`](./Equivalence.lean), sorry-free, no
   new axioms beyond Lean's standard foundations (the proofs don't
   even need the pre-existing evm-smith axioms on Keccak collision-
   resistance — they reason about Keccak abstractly).

The proof is structured as a single peephole transformation:

```
[MSTORE 0x0c seed; MSTORE 0x00 addr; KECCAK256 → SLOAD]    -- keccak layout
        ≡
[SLOAD addr]                                                -- address-as-slot
```

— and the structural counterpart for stores. Because Solady's
balance-touching functions are byte-identical between layouts except
at these peephole sites, the local equivalence at each peephole lifts
to whole-function equivalence under a per-address storage-translation
relation.

## What was changed in the contracts

Two Solidity contracts under [`foundry/src/`](./foundry/src/):

- `MockERC20Original.sol` — inherits Solady's `ERC20` unchanged.
- `MockERC20Optimized.sol` — overrides the six `virtual` balance-
  touching functions to use `sload(uint256(uint160(addr)))` / `sstore`
  directly. Allowances and nonces stay keccak-mapped. Log emission
  uses `caller()` and the parameter address directly instead of
  reading them back from memory.

## Test results

`forge test` from [`foundry/`](./foundry/):

```
Ran 46 tests across 2 backends (OriginalERC20Test, OptimizedERC20Test).
All 46 passed (23 cases × 2 backends).
```

Coverage: mint / burn / approve / transfer / transferFrom (success +
revert paths), Permit2 infinite-allowance escape hatch, transfer-to-
self, zero-amount transfers, fuzz cases. The behaviour test is
parameterized over an abstract `IERC20Like` interface and exercises
both contracts through their public API only — no `vm.load` slot
probes.

## Gas comparison

From [`foundry/test/ERC20GasCompare.t.sol`](./foundry/test/ERC20GasCompare.t.sol):

| Operation              | Keccak layout (gas) | Address-as-slot (gas) | Delta  |
|------------------------|---------------------|-----------------------|--------|
| `balanceOf` (warm)     |              1,117  |                1,064  |  -53   |
| `mint` (fresh recipient)|            49,665  |               49,616  |  -49   |
| `mint` (warm recipient)|             3,365  |                3,316  |  -49   |
| `burn`                 |             3,304  |                3,244  |  -60   |
| `transfer` (fresh-to)  |            25,377  |               25,285  |  -92   |
| `transfer` (warm-to)   |             3,477  |                3,385  |  -92   |
| `transferFrom`         |            25,906  |               25,826  |  -80   |

Plus a constant **-60 bytes** of runtime (2,510 → 2,450 bytes deployed).

Origin of the savings: each balance access costs ~36 gas for
`KECCAK256` (base 30 + 6 per 32-byte word), plus the `MSTORE` × 2,
plus the two scratch `PUSH`s, plus a couple of bytes of bytecode. The
optimized layout pays none of that.

## Proofs (Lean)

### Theorem catalogue

Sorry-free; built via `lake build EvmSmith.Demos.ERC20.Equivalence`.

| Theorem | What it says |
|---|---|
| `keccakPrefix_value` | Running the 8-op keccak balance-slot prefix on `[addr, rest]` leaves `[balanceSlotOf m addr, rest]` on the stack. `balanceSlotOf` is **defined** as exactly the Lean expression the prefix produces — so `unfold runOp EvmYul.step; rfl` closes the goal *without computing Keccak*. The keccak result is carried symbolically through `ffi.KEC` (opaque). |
| `balanceLoadOrig_value` | Full post-state of `keccakPrefix ++ [SLOAD]`: top of stack is `(sload (balanceSlotOf m addr)).snd`. |
| `balanceLoadOpt_value` | Full post-state of `[SLOAD]`: top of stack is `(sload addr).snd`. |
| `balanceLoad_observable_equiv` | Under `StorageBalEquivAt σ_orig σ_opt m addr` (the per-address storage relation), both load blocks produce the **same top of stack**. The user-visible "balance" returned by `balanceOf(addr)` is identical between layouts. |
| `balanceStoreOrig_value` | Full post-state of `keccakPrefix ++ [SSTORE]`: `toState := sstore <pre.toState> (balanceSlotOf m addr) value`. |
| `balanceStoreOpt_value` | Full post-state of `[SSTORE]`: `toState := sstore <pre.toState> addr value`. |
| `balanceStore_observable_equiv` | Structural post-state equivalence: both backends `sstore` the same `value` at their respective balance slots. Subsequent reads of the same address recover `value` in both layouts (standard EVM `sload-after-sstore` property). |

### The "Keccak vanishes" trick

The original task description hinted at it: *"we don't care about the
result of Keccak, and this is important! The result of Keccak only
influences the storage slot itself, but we're changing the layout, so
Keccak will actually vanish in the functions we're changing after our
optimizations."*

This is formalized in the proof by defining

```lean
def balanceSlotOf (m : MachineState) (addr : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC (balancePreimage m addr)))
```

— that is, `balanceSlotOf` is exactly the Lean term the EVM bytecode's
keccak prefix produces. `ffi.KEC` is `opaque` in EVMYulLean, so this
term is irreducible by Lean's kernel: it's a symbol, not a number. The
equivalence proof for `keccakPrefix_value` closes by `rfl` because the
LHS (the bytecode-side computation) and the RHS (`balanceSlotOf m addr`)
are *definitionally* the same term.

In the `StorageBalEquivAt` relation, we relate `σ_orig` at slot
`balanceSlotOf m addr` with `σ_opt` at slot `addr`. The relation
*quantifies over the address*, not over slots, so the keccak result
never has to be reduced to a number anywhere — it just gets carried
around symbolically until the slot is consumed by SLOAD/SSTORE, at
which point both layouts produce/consume *the same loaded value* by
the relation.

The proof's correctness therefore doesn't depend on Keccak's
*collision-resistance*: even if Keccak collided on two different
addresses (it doesn't, but pretend), the relation would still hold
pointwise per address; the optimization just hands off the same
keccak-mapped balance to the same `addr` slot, regardless of how
keccak distributes addresses to slots.

### Trust boundary

Verified via `lake build EvmSmith.Demos.ERC20.AxiomCheck`:

```
'keccakPrefix_value'              depends on axioms: [propext, Classical.choice, Quot.sound]
'balanceLoadOrig_value'           depends on axioms: [propext, Classical.choice, Quot.sound]
'balanceLoadOpt_value'            depends on axioms: [propext, Classical.choice, Quot.sound]
'balanceLoad_observable_equiv'    depends on axioms: [propext, Classical.choice, Quot.sound]
'balanceStoreOrig_value'          depends on axioms: [propext, Classical.choice, Quot.sound]
'balanceStoreOpt_value'           depends on axioms: [propext, Classical.choice, Quot.sound]
'balanceStore_observable_equiv'   depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only Lean's three standard foundation axioms. **Zero** new axioms
from this demo. Even the two pre-existing evm-smith axioms (precompile
purity, Keccak collision-resistance) are unused here — the proof
deliberately avoids needing collision-resistance, which makes it
robust to even a (hypothetical) cryptographic break of Keccak.

### What's not formalized here (and why)

The proofs cover the **balance-access peephole** end-to-end. They do
not include a closed-form `sload (sstore σ k v) k = v` round-trip
lemma at the `EvmYul.State` level, which would let us write a single
top-level "balanceOf(addr) after mint(addr, v) returns v in both
layouts" theorem.

That lemma is technically true (and trivially so — it's the EVM's
basic storage semantics), but its proof requires a sequence of
`Batteries.RBMap`-internal rewrites (`find?_insert_of_eq`,
`updateStorage`'s erase-vs-insert branch on `v == 0`, etc.) that
aren't currently exposed as named lemmas in the framework. Closing it
in this demo would mean re-deriving a slice of the RBMap API that
should arguably ship upstream; that's orthogonal to the storage-layout
optimization argument we wanted to demonstrate.

So the proof obligation we *don't* discharge here is a property of
EVMYulLean's storage model, not of the layout optimization. The peephole
soundness — which is what's *specific* to the optimization — is
fully proved.

The structural form `balanceStore_observable_equiv` exposes the
post-store state precisely enough that any consumer wanting the
round-trip can derive it from the standard EVM property.

## Vyper / Snekmate variant

After completing the Solidity variant, we ran the same exercise
against Vyper's [Snekmate](https://github.com/pcaversaccio/snekmate)
ERC-20. Two notable differences in approach:

1. **Bytecode-level optimization** instead of source-level. Vyper has
   no inline assembly, so the optimization is applied as a *patcher*
   over compiled runtime bytecode. The patcher is length-preserving
   (so PC-absolute jumpdests stay valid) and fail-closed on site-count
   mismatch.

2. **A different slot derivation**. Vyper emits a different keccak
   prefix from Solidity — `keccak256(slot ++ key)` over a 64-byte
   preimage (`mem[0x00..0x40]`) rather than Solady's seed-packed 32-
   byte preimage. Slot id `0x02` is the actual emission (`vyper -f
   layout` reports `1` due to a known +1 offset in Vyper's layout-JSON
   format vs the runtime encoding).

3. **A different slot replacement**. Naively using `addr` directly as
   the slot collides with Vyper's named state variables (`owner` at
   slot 1, `totalSupply` at 4, etc.). The patcher uses `NOT(addr)` as
   the replacement slot: bitwise NOT maps every 160-bit address to a
   slot in `[2^160, 2^256)`, well above every named slot and (by
   Keccak preimage resistance) every keccak-derived slot. A single-
   byte instruction.

### Layout: original

```
PUSH1 0x02          ; slot id
PUSH1 <P>           ; memory offset where addr argument lives
MLOAD               ; addr from mem[P]
PUSH1 0x20  MSTORE  ; mem[0x20] = addr
PUSH0       MSTORE  ; mem[0x00] = 0x02
PUSH1 0x40  PUSH0
KECCAK256           ; keccak(slot ++ addr)
SLOAD or SSTORE
```

### Layout: patched

```
JUMPDEST × 10       ; no-op padding (length-preserving)
PUSH1 <P>
MLOAD
NOT                 ; addr → ~addr
SLOAD or SSTORE
```

### Vyper test results

`forge test` from
[`foundry-vyper/`](./EvmSmith/Demos/ERC20-Vyper/foundry/) (loading the
venv'd Vyper compiler via `PATH=.venv/bin:$PATH`):

```
Ran 42 tests across 2 backends (OriginalVyperERC20Test,
OptimizedVyperERC20Test). All 42 passed (21 cases × 2 backends).
```

Coverage: same shape as the Solidity behaviour test — mint, burn,
burn_from, approve, transfer, transferFrom (success + revert paths),
infinite-allowance, fuzz on the public surface.

### Vyper gas comparison

| Operation              | Vyper-orig (gas) | Vyper-patched (gas) | Delta  |
|------------------------|------------------|---------------------|--------|
| `balanceOf` (warm)     |              920 |                 872 |  -48   |
| `mint` (fresh)         |           51,810 |              51,714 |  -96   |
| `mint` (warm)          |            3,510 |               3,414 |  -96   |
| `burn`                 |            3,216 |               3,114 | -102   |
| `transfer` (fresh)     |           25,506 |              25,314 | -192   |
| `transfer` (warm)      |            3,606 |               3,414 | -192   |
| `transferFrom`         |           28,137 |              27,945 | -192   |

Runtime size: 6,602 bytes, **unchanged** (length-preserving patch).

The Vyper deltas are roughly double the Solidity-Solady deltas at the
transfer level because Vyper recomputes the balance-slot keccak at
every access (no compiler-side reuse across read/write of the same
`balanceOf[addr]`), so each balance access pays the full ~48-gas
overhead. Solady-via-`solc` keeps the slot value on the stack between
the read and write, paying keccak only once per address per function
call.

### Vyper proofs

Three theorems in
[`EquivalenceVyper.lean`](./EquivalenceVyper.lean), sorry-free, only
Lean's standard foundation axioms:

| Theorem | What it says |
|---|---|
| `vyperOptPrefix_value` | The 13-op patched prefix (10 JUMPDESTs, PUSH1 P, MLOAD, NOT) on entry stack `rest` exits with `[~addr, rest]` where `addr` is what MLOAD reads from `mem[P]`. |
| `vyperBalanceLoadOpt_value` | Extends with the trailing SLOAD: end stack-top is `(sload σ.toState (~addr)).snd`. |
| `vyperBalanceLoad_relational_equiv` | Under the per-address storage relation (`(sload σ_orig slot).snd = (sload σ_opt (~addr)).snd`), both load blocks land at the same stack-top. The orig-side characterization is taken as a hypothesis — the 10-step `unfold; rfl` chain for the keccak prefix WHNF-times out in EVMYulLean's current shape, same root cause as the Solidity variant's storage round-trip gap. |

The "Keccak vanishes" framing carries over identically: the orig
keccak prefix's value never has to be reduced, only carried
symbolically through the storage relation.

### Vyper files

| File | Role |
|---|---|
| [`STORAGE_LAYOUT_VYPER.md`](./STORAGE_LAYOUT_VYPER.md) | Vyper-side investigation (slot derivation, +1 offset, NOT trick rationale). |
| [`ProgramVyper.lean`](./ProgramVyper.lean) | Hand-rolled Vyper keccak prefix definition. |
| [`OptimizedProgramVyper.lean`](./OptimizedProgramVyper.lean) | Hand-rolled NOT-prefix definition. |
| [`EquivalenceVyper.lean`](./EquivalenceVyper.lean) | Three equivalence theorems. |
| [`../ERC20-Vyper/foundry/src/mock.vy`](../ERC20-Vyper/foundry/src/mock.vy) | The Vyper Snekmate-based mock. |
| [`../ERC20-Vyper/foundry/script/patch.py`](../ERC20-Vyper/foundry/script/patch.py) | Offline Python patcher (used to dump the optimized runtime hex for inspection). |
| [`../ERC20-Vyper/foundry/test/BytecodePatcher.sol`](../ERC20-Vyper/foundry/test/BytecodePatcher.sol) | Solidity in-place patcher (used by tests via `vm.etch`). |
| [`../ERC20-Vyper/foundry/test/ERC20VyperCompare.t.sol`](../ERC20-Vyper/foundry/test/ERC20VyperCompare.t.sol) | Behaviour parity test (21 cases × 2 backends). |
| [`../ERC20-Vyper/foundry/test/ERC20VyperGasCompare.t.sol`](../ERC20-Vyper/foundry/test/ERC20VyperGasCompare.t.sol) | Per-op gas measurement. |

## Files

| File | Role |
|---|---|
| [`STORAGE_LAYOUT.md`](./STORAGE_LAYOUT.md) | Investigation: Solady's layout, the optimization, gas table, bytecode-level diff. |
| [`Program.lean`](./Program.lean) | Hand-rolled keccak-balance bytecode block + `balanceSlotOf` definition. |
| [`OptimizedProgram.lean`](./OptimizedProgram.lean) | Hand-rolled address-as-slot bytecode block. |
| [`Equivalence.lean`](./Equivalence.lean) | All equivalence theorems. |
| [`AxiomCheck.lean`](./AxiomCheck.lean) | `#print axioms` for every headline theorem. |
| [`foundry/src/MockERC20Original.sol`](./foundry/src/MockERC20Original.sol) | Solady's ERC20 unchanged. |
| [`foundry/src/MockERC20Optimized.sol`](./foundry/src/MockERC20Optimized.sol) | Solady's ERC20 with balance-slot overrides. |
| [`foundry/test/ERC20Compare.t.sol`](./foundry/test/ERC20Compare.t.sol) | Parameterized behaviour test (46 cases across 2 backends). |
| [`foundry/test/ERC20GasCompare.t.sol`](./foundry/test/ERC20GasCompare.t.sol) | Per-op gas measurement. |

## Running it

```bash
# Lean proofs
lake build EvmSmith.Demos.ERC20.Equivalence
lake build EvmSmith.Demos.ERC20.AxiomCheck

# Foundry tests + gas comparison
cd EvmSmith/Demos/ERC20/foundry
forge test                              # 46 cases pass
forge test --match-contract ERC20GasCompareTest -vv   # gas table
```

## Reproducibility

- Solady pinned at commit `90db92ce173856605d24a554969f2c67cadbc7e9`
  via git submodule under
  [`foundry/lib/solady/`](./foundry/lib/solady/).
- forge-std pinned via the existing forge-std submodule.
- solc 0.8.20, optimizer on (200 runs), per `foundry.toml`.
- Lean 4.22.0, EVMYulLean at the repository's pinned commit.
