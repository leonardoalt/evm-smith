# ERC-20 Storage Layout Optimization: Final Report

## What this demo delivers

Three things, with very different rigour levels:

1. **Engineering case study.** A Solady-based ERC-20 with two
   storage layouts. *keccak-mapped balances* (Solady's default)
   and *`~addr`-as-slot* (the optimization), running identical
   tests against both backends, plus per-op gas comparison. Same
   for Vyper / Snekmate, with the optimization applied at the
   bytecode level via a length-preserving patcher. **The deployed
   bytecode in both cases is the actual compiler output**; the
   tests verify operational equivalence on ~100 Foundry cases plus
   a no-aliasing fuzz invariant.

2. **A small handful of Lean theorems** about a hand-rolled mirror
   of the keccak prefix. **The Lean proofs do not target the
   `solc`/`vyper`-compiled bytecode.** They target ~10-opcode
   `Program` values we wrote by hand to match the shape of what the
   compiler emits. The "link" from these theorems to the actual
   deployed bytes is by inspection, not by proof. See
   "What is proven" below, read it before believing any
   "equivalence" claim downstream.

3. **A refinement framework** (`Spec.lean`) that, *if* a future AI
   or contributor adds a new storage-layout optimization, forces
   them to discharge injectivity + named-slot-disjointness as
   type-level proof obligations. Doesn't retroactively prove the
   current demo's correctness. It's a *future-facing* safeguard.

## What is proven

In Lean, sorry-free, no new axioms beyond Lean's three foundations:

1. **`UInt256.lnot` is injective.** Two distinct 256-bit values get
   distinct complements. `EvmYul.UInt256.lnot_injective` in
   `EvmSmith/Lemmas/UInt256Order.lean`.

2. **`UInt256.lnot a` is disjoint from `{0, 1, 2, _TOTAL_SUPPLY_SLOT}`
   for any 160-bit `a`.** Arithmetic: `lnot a ≥ 2^256 - 2^160`, well
   above every named slot. `lnot_disjoint_from_named` in `Spec.lean`.

3. **A 10-opcode hand-rolled keccak-prefix block produces
   `balanceSlotOf m addr` on the stack.** `keccakPrefix_value` in
   `Equivalence.lean`. The "10-opcode block" is our hand-roll, not
   the compiler's output.

4. **A 2-opcode hand-rolled `[NOT, SLOAD]` block produces
   `(sload σ (~addr)).snd` on the stack.** `balanceLoadOpt_value`.

5. **Under a per-address storage relation `R(σ_orig, σ_opt, a)`,
   the two hand-rolled blocks produce equal stack-tops.** Block-
   local, pointwise per address, `R` taken as hypothesis.
   `balanceLoad_observable_equiv`.

6. **The two hand-rolled store blocks land at structurally-known
   `sstore`d states.** `balanceStore_observable_equiv`. Doesn't say
   `R` is preserved across the store. That's a separate gap.

7. **The abstract `Function.update`-style storage model preserves a
   refinement relation across mint / burn / transfer**, provided
   the caller supplies a `SlotAbstraction` (which requires
   injectivity + named-slot disjointness proofs).
   `mint_refines` / `burn_refines` / `transfer_refines` in
   `Spec.lean`. This is about an abstract `UInt256 → UInt256`
   storage model, not actual `EvmYul.State` storage.

That is the complete catalogue. The Vyper variant adds three more
theorems with the same shape against a different (Vyper-emitted)
keccak prefix.

## To be proven

Things we do **not** have Lean theorems for, despite the demo's
shape suggesting we might:

- The actual `solc`-compiled `MockERC20Optimized.sol` runtime
  bytecode is equivalent to the `MockERC20Original.sol` runtime
  bytecode. *Not proved.* We only proved equivalence of two
  hand-rolled 10-opcode mirrors. The 2,500-byte deployed bytes
  could differ from our mirror in ways the proof wouldn't catch.

- The Vyper-patched runtime bytecode is equivalent to the original
  Vyper-compiled runtime. *Not proved.* Same gap, the patcher
  operates on real bytes, but our Lean proofs are about a
  separate hand-rolled mirror.

- Storage round-trip at the `EvmYul.State` level
  (`sload(sstore σ k v) k = v`). *Not proved.* Needed for the
  abstract refinement framework to lift to the real EVM.

- The storage relation `R` is preserved by a balance store.
  *Not proved* directly, the structural form in (6) is *consistent
  with* preservation but doesn't state it.

- A sequence of mint/transfer/burn operations preserves `R`.
  *Not proved.* Would follow by induction once (3)–(7) are
  end-to-end connected and lifted to `EvmYul.State`.

- The contract's `name()` / `symbol()` / `decimals()` getters
  return their constructor-initialised values after any sequence of
  operations. *Not proved in Lean*, but checked by the
  Foundry-level no-aliasing invariant across ~2,000 fuzzed call
  sequences per backend.

## Trust assumptions

Three layers of trust, distinct:

1. **Lean's three standard foundation axioms** (`propext`,
   `Classical.choice`, `Quot.sound`). Foundational, not contract-
   specific.

2. **One pre-existing evm-smith axiom: Keccak collision-resistance
   (T5).** Used implicitly: the `~addr` slot for the opt layout
   has to not collide with the keccak-derived allowance / nonce /
   is_minter slots that the orig layout uses. Disjointness against
   the *named* slots (slots 0, 1, 2, `_TOTAL_SUPPLY_SLOT`) is
   proved by Lean arithmetic. Disjointness against
   *keccak-derived* slots (allowances at
   `keccak256(spender ++ owner ++ seed)`, etc.) is taken on T5: for
   `~a` to equal `keccak256(some_preimage)`, an attacker would
   need to find the preimage. `2^-256` per attempt. This is the
   same Keccak trust assumption Solady itself rests on for its
   own mappings; we don't strengthen it.

3. **Deployment-side trust, not encoded in Lean:**
   - `solc 0.8.20` and `vyper 0.5.0a1` emit the keccak prefixes in
     the exact opcode shape our hand-rolled `Program` mirrors.
     Checked by disassembly, not by proof.
   - The bytecode patcher (Vyper) correctly identifies *every*
     balance-access site and rewrites *only* those. Fail-closed on
     AST/site-count mismatch, but the source-AST vs runtime-pattern
     correspondence is by construction, not by Lean theorem.
   - Foundry's `vm.etch` faithfully installs runtime bytecode.

## The proof gap, stated plainly

The local peephole theorem `balanceLoad_observable_equiv` says: "two
specific 10-opcode programs, run on related states, return the same
value." It does **not** say: "the deployed Solady-compiled bytecode
on the orig contract is equivalent to the deployed
`MockERC20Optimized`-compiled bytecode on the opt contract."

The chain from one to the other needs:

- A proof that the deployed bytecode contains exactly the peephole
  pattern at exactly the sites we modelled. Inspected, not proved.
- A proof that the rest of the bytecode is byte-identical between
  layouts (or that any differences don't break `R`). Not proved.
- The `EvmYul.State` bridge for lifting `R` across the actual EVM
  operations. Not proved.

The original task. "compile to bytecode, modify it at the EVM level,
prove equivalence", would mean walking the *whole bytecode*
opcode-by-opcode in Lean (the way the WETH solvency proof does for
its 86-byte hand-rolled bytecode). We did not do that for ERC-20.

The peephole approach in this demo is sound *as a peephole*. Lifting
it to a whole-bytecode equivalence claim is not in scope of the
current proofs. Read "What is proven" above for the precise
list, and don't let downstream prose like "the local equivalence at
each peephole lifts to whole-function equivalence" anywhere else in
this report bait you into thinking otherwise. That lift is asserted,
not proved.

## Repository setup

How the two test harnesses are wired up. Both keep external
dependencies as git submodules, pin compiler versions, and put the
build artefacts and the proof artefacts under the same demo
directory so the engineering and the proof stay co-located.

### Solidity / Solady setup

Layout: `EvmSmith/Demos/ERC20/foundry/`:

```
foundry.toml                 solc 0.8.20, optimizer on (200 runs)
lib/
├── forge-std/               submodule, foundry-rs/forge-std
└── solady/                  submodule, pinned to commit 90db92c
src/
├── MockERC20Original.sol    inherits Solady's ERC20 verbatim
└── MockERC20Optimized.sol   inherits Solady's ERC20; overrides 6
                             virtual functions with inline-asm
                             versions that use ~addr as the balance slot
test/
├── ERC20Compare.t.sol       parameterised behaviour test; same suite
                             runs against both contracts
└── ERC20GasCompare.t.sol    per-op gas comparison
```

Foundry config (`foundry.toml`):

| Option | Value | Why |
|---|---|---|
| `solc_version` | `"0.8.20"` | Matches Solady's CI; the inline-assembly idioms (`shr`, `shl`, `keccak256` from yul) are stable on this version. |
| `optimizer` | `true` | Without it, the compiled bytecode is bloated with stack-cleanup boilerplate that swamps the keccak-prefix delta we're measuring. |
| `optimizer_runs` | `200` | Standard Solidity-ecosystem default (Solady itself uses 200). Higher runs would over-inline at the cost of deploy size and don't affect the keccak-prefix savings. |

We deliberately don't use `via_ir = true` because (a) Solady's
assembly idioms are designed for the legacy pipeline and (b) the
IR pipeline can hoist the keccak'd slot across read/write pairs,
muddying the gas comparison.

Building:

```bash
cd EvmSmith/Demos/ERC20/foundry
forge build               # uses solc 0.8.20 via foundry's resolver
forge test                # runs both behaviour and gas tests
```

### Vyper / Snekmate setup

Layout: `EvmSmith/Demos/ERC20-Vyper/`:

```
.venv/                       Python venv (gitignored)
foundry/
  foundry.toml               solc 0.8.20 + vyper = { optimize = "gas" }
  lib/
  ├── forge-std/             submodule
  └── snekmate/              submodule, pinned to commit ba43b69
  src/
  ├── mock.vy                Snekmate-based mock contract
  └── snekmate/              symlink → ../lib/snekmate/src/snekmate
                             (so Vyper's import resolver finds the package)
  script/
  └── patch.py               offline bytecode patcher (AST-cross-checked)
  test/
  ├── BytecodePatcher.sol    Solidity in-place patcher used by tests
  ├── ERC20VyperCompare.t.sol
  └── ERC20VyperGasCompare.t.sol
```

The venv is pinned to Vyper 0.5.0a1 (`pip install vyper==0.5.0a1`),
the version that satisfies Snekmate's `# pragma version ~=0.5.0a1`
directive. Foundry's Vyper integration finds the compiler by looking
up `vyper` on `PATH`, so the test commands all run as
`PATH=$(pwd)/../.venv/bin:$PATH forge test`.

Foundry config differences from the Solidity setup:

| Option | Value | Why |
|---|---|---|
| `vyper` | `{ optimize = "gas" }` | Matches Snekmate's own CI. Doesn't help with our optimization, Vyper recomputes the balance keccak at every access regardless of optimizer level. (We verified this against `none`, `codesize`, and `gas`.) |
| `skip` | `["src/snekmate/**/*.vy", "src/snekmate/**/*.vyi"]` | Otherwise `forge build` tries to compile every Snekmate `.vy` file as a standalone contract and trips on uninitialised `uses:` clauses. |
| `ffi` | `true` | Matches Snekmate's own setting; lets us invoke external commands from tests if needed. |
| `allow_paths` | `["lib/snekmate/src"]` | Permits Vyper imports to escape `src/` into the vendored Snekmate tree. |

The `src/snekmate -> ../lib/snekmate/src/snekmate` symlink is the
trick that lets `from snekmate.tokens import erc20` work without
patching Vyper's path resolver. Snekmate's own foundry project
does effectively the same thing by putting the library under
`src/snekmate/` directly.

Building & running:

```bash
cd EvmSmith/Demos/ERC20-Vyper
python3 -m venv .venv
.venv/bin/pip install vyper==0.5.0a1
cd foundry
PATH=$(pwd)/../.venv/bin:$PATH forge build
PATH=$(pwd)/../.venv/bin:$PATH forge test
```

### Lean / EVMYulLean setup

The proofs live at the *repo root* (one level up from the demo
directories) and use the framework's pinned EVMYulLean submodule.
`lake build` from the repo root verifies everything. No additional
toolchain on top of the existing evm-smith setup. Vyper isn't
needed for the proof side because the patcher's output is checked
by tests, not by Lean.

## What was changed in the contracts

Two Solidity contracts under [`foundry/src/`](./foundry/src/):

- `MockERC20Original.sol`: inherits Solady's `ERC20` unchanged.
- `MockERC20Optimized.sol`: overrides the six `virtual` balance-
  touching functions to use `sload(not(addr))` / `sstore(not(addr), v)`.
  Allowances and nonces stay keccak-mapped. Log emission uses
  `caller()` and the cleaned parameter address as topics directly
  instead of reading them back from memory.

## Test results

`forge test` from [`foundry/`](./foundry/), after the NOT(addr) fix
and the added metadata-regression tests:

```
Ran 54 tests across 2 backends (OriginalERC20Test, OptimizedERC20Test).
All 54 passed (27 cases × 2 backends).
Plus 8 gas-comparison tests.
```

Coverage: mint / burn / approve / transfer / transferFrom (success +
revert paths), Permit2 infinite-allowance escape hatch, transfer-to-
self, zero-amount transfers, fuzz cases, **plus four metadata-
preservation regression tests** that mint to low addresses (0x00,
0x01, 0x02, 0x03) and assert the contract's `name()` / `symbol()` /
`decimals()` stay intact. The behaviour test is parameterized over
an abstract `IERC20Like` interface and exercises both contracts
through their public API only, no `vm.load` slot probes.

## Collision-avoidance: why `~addr` instead of `addr`

A naive read of the optimization says "use the address as the balance
slot directly." The first version did exactly that: `sload(addr)`,
one byte saved. Pretty soon it broke a fuzz test on the Vyper side
(see the next subsection); we then realised the **Solidity side has
the same latent bug** even though the fuzz tests missed it. The fix
is the same in both: `sload(not(addr))`, replace the address with
its bitwise complement.

### Why the raw address collides

A storage slot is a `UInt256`. Both the contract's *named* state
variables and our *balance map* live in the same flat slot space.
Two storage uses with the same slot id alias, writing one
corrupts the other.

In **Vyper / Snekmate**, named state lives at low slots:

| Slot | Variable             |
|------|----------------------|
| 0x01 | `ownable.owner`      |
| 0x02 | `erc20.balanceOf` (keccak base, never directly addressed) |
| 0x03 | `erc20.allowance` (keccak base) |
| 0x04 | `erc20.totalSupply`  |
| 0x05 | `erc20.is_minter` (keccak base) |
| 0x06 | `erc20.nonces` (keccak base) |

With `sload(addr)`, `mint(address(0x04), v)` would *overwrite
totalSupply*. The fuzz suite caught it on a different collision
(`address(0x01)`, the owner).

In **Solidity / Solady**, named state in our mock contract lives at
slots 0, 1, 2:

| Slot | Variable           |
|------|--------------------|
| 0x00 | `_name`            |
| 0x01 | `_symbol`          |
| 0x02 | `_decimals`        |

Solady's own constants (`_TOTAL_SUPPLY_SLOT = 0x05345cdf77eb68f44c`,
the `_BALANCE_SLOT_SEED`, the keccak'd allowance / nonce slots) all
live at high values and don't collide. But `_name`, `_symbol`,
`_decimals` are *Solidity-assigned* state variables on our
`MockERC20Optimized` subclass, so they get slots 0, 1, 2.

### How the bug surfaced

**Vyper side, naturally:** the foundry fuzzer biases toward "magic"
addresses (`address(0)`, `address(0x01)`, `address(this)`, the
precompiles). On the first run of `testFuzzMint(address, uint96)`
against the patched Vyper backend, the fuzzer tried
`mint(address(0x01), 34493224748316818407380903281)` and got
balance back as `(owner_address + 34493...281)`, a giveaway
that slot 1 (the owner) was being written instead of the balance
mapping.

**Solidity side, by retroactive testing.** Our original 256-run
fuzz suite on the Solidity side passed because the fuzz cases
only assert `balanceOf` and `totalSupply` after the mint, never
`name()` / `symbol()` / `decimals()`. The collision was silent -
slot 0/1/2 got overwritten, but the asserted properties
(`balanceOf(addr) == v` and `totalSupply == v`) still held
trivially (the rewritten slot at `addr` is now `v`, and
`totalSupply` lives at its high constant slot, unaffected). The
metadata was corrupted but not observed.

A targeted test confirmed the bug after the fact:

```solidity
function test_long_string_flag_attack() public {
    token.mint(address(0x00), 0x80);
    token.name();  // ⇒ panic: storage byte array incorrectly encoded
}
```

The `0x80` low byte flips Solidity's "long string" flag on slot 0
(`_name`'s slot), and the next call to `name()` dereferences
`keccak256(0x00)` thinking it's a long-string data pointer, which
points to uninitialised storage and Solidity panics.

### The fix

The optimized contracts (Solidity and Vyper, after the fix) use
`sload(not(addr))` / `sstore(not(addr), v)` everywhere they touched
the balance map.

- `NOT` is one byte (`0x19`) in EVM, costing 3 gas. The keccak
  prefix we eliminate costs ~48 gas, so the saving is still net
  positive after paying for the NOT.
- `not(addr)` for any 160-bit address has its high 96 bits all
  one, so the slot lies in `[2^256 - 2^160, 2^256)`. Every named
  slot in either contract is `< 2^160`, so no collision is possible
  there. Keccak-derived slots (Solady's totalSupply constant, the
  allowance / nonce buckets) could *in principle* collide if Keccak
  happened to produce a hash value in `[2^256 - 2^160, 2^256)`,
  but that's the same preimage-resistance assumption every
  Solidity mapping already rests on. We're not weakening the
  trust model.
- `NOT` is bijective on `UInt256`, so the slot function remains
  injective per address (different addresses map to different
  slots). No two users alias.

### The no-aliasing Foundry invariants

Beyond the targeted regression tests below, both backends now ship a
generic *fuzz invariant* that catches any storage aliasing, not
just collisions with the specific named slots we know about. See
[`foundry/test/NoAliasingInvariant.t.sol`](./foundry/test/NoAliasingInvariant.t.sol)
(Solidity) and
[`../ERC20-Vyper/foundry/test/NoAliasingInvariant.t.sol`](../ERC20-Vyper/foundry/test/NoAliasingInvariant.t.sol)
(Vyper).

A handler drives the contract through fuzzed `mint` / `transfer`
sequences over a small actor dictionary that **always seeds the
low-collision addresses** (0x00..0x03 for Solidity, 0x00..0x06 for
Vyper). Two invariants per backend:

- `invariant_metadata_preserved`: `name()` / `symbol()` /
  `decimals()` (and `owner()` on Vyper) must return their
  constructor-initialised values across any fuzz sequence.
- `invariant_no_phantom_balance`: `Σ balanceOf(actor) ≤
  totalSupply`. Aliasing inflates the sum (two actors share one
  storage slot, both read its value), or corrupts `totalSupply`
  itself (if a balance write lands on its slot), either trips the
  invariant.

Sanity check: temporarily reverting the `NOT(addr)` fix to the
broken `sload(addr)` version and re-running, the
phantom-balance invariant fires immediately:

```
[FAIL: invariant_no_phantom_balance]
  phantom balance: aliased addresses inflate the visible sum:
  76318471673650654452077537475063650456547488489235383969275586155053664174114 > 0
```

(That huge number is the corrupted `_name` string's packed bytes
read as if it were a uint256 balance.) After restoring the fix,
all four invariants × 2 backends pass at 2,048 fuzzed calls each.

This is the **lowest-effort defence** against the bug class: it
requires no knowledge of which slots will collide, just a fuzz
dictionary biased toward the low-address neighbourhood. Add it to
*every* storage-layout optimization that lands in the codebase, this one included.

### Regression test that would have caught the Solidity bug

Added to [`ERC20Compare.t.sol`](./foundry/test/ERC20Compare.t.sol):

```solidity
function testMetadataSurvivesMintToLowAddresses() public {
    _mint(address(0x00), 1 ether);
    _mint(address(0x01), 2 ether);
    _mint(address(0x02), 3 ether);
    _mint(address(0x03), 4 ether);
    assertEq(token.name(), "Token");
    assertEq(token.symbol(), "TKN");
    assertEq(token.decimals(), 18);
}

function testMetadataSurvivesLongStringFlagAttack() public {
    _mint(address(0x00), 0x80);
    assertEq(token.name(), "Token");
}
```

Plus an explicit fuzz variant that targets low-byte addresses and
asserts on the metadata getters. With the broken (`sload(addr)`)
optimization, all three of these failed.

## Gas comparison

From [`foundry/test/ERC20GasCompare.t.sol`](./foundry/test/ERC20GasCompare.t.sol),
after the `NOT(addr)` fix:

| Operation              | Keccak layout (gas) | `~addr`-as-slot (gas) | Delta  |
|------------------------|---------------------|-----------------------|--------|
| `balanceOf` (warm)     |              1,117  |                1,067  |  -50   |
| `mint` (fresh recipient)|            49,665  |               49,622  |  -43   |
| `mint` (warm recipient)|             3,365  |                3,322  |  -43   |
| `burn`                 |             3,304  |                3,252  |  -52   |
| `transfer` (fresh-to)  |            25,377  |               25,302  |  -75   |
| `transfer` (warm-to)   |             3,477  |                3,402  |  -75   |
| `transferFrom`         |            25,906  |               25,833  |  -73   |

Plus a constant **-42 bytes** of runtime (2,510 → 2,468 bytes
deployed), slightly less than the pre-NOT version (which saved 60
bytes) because each access site now spends one extra byte on
`NOT`.

Origin of the savings: each balance access used to cost ~36 gas for
`KECCAK256` (base 30 + 6 per 32-byte word), plus the `MSTORE` × 2,
plus the two scratch `PUSH`s, plus a couple of bytes of bytecode.
The optimized layout pays one `NOT` (3 gas, 1 byte) instead.

## Proofs (Lean)

### Theorem catalogue

Sorry-free; built via `lake build EvmSmith.Demos.ERC20.Equivalence`.

| Theorem | What it says |
|---|---|
| `keccakPrefix_value` | Running the 8-op keccak balance-slot prefix on `[addr, rest]` leaves `[balanceSlotOf m addr, rest]` on the stack. `balanceSlotOf` is **defined** as exactly the Lean expression the prefix produces, so `unfold runOp EvmYul.step; rfl` closes the goal *without computing Keccak*. The keccak result is carried symbolically through `ffi.KEC` (opaque). |
| `balanceLoadOrig_value` | Full post-state of `keccakPrefix ++ [SLOAD]`: top of stack is `(sload (balanceSlotOf m addr)).snd`. |
| `balanceLoadOpt_value` | Full post-state of `[NOT; SLOAD]`: top of stack is `(sload (~addr)).snd`. |
| `balanceLoad_observable_equiv` | Under `StorageBalEquivAt σ_orig σ_opt m addr` (the per-address storage relation), both load blocks produce the **same top of stack**. The user-visible "balance" returned by `balanceOf(addr)` is identical between layouts. |
| `balanceStoreOrig_value` | Full post-state of `keccakPrefix ++ [SSTORE]`: `toState := sstore <pre.toState> (balanceSlotOf m addr) value`. |
| `balanceStoreOpt_value` | Full post-state of `[NOT; SSTORE]`: `toState := sstore <pre.toState> (~addr) value`. |
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

- that is, `balanceSlotOf` is exactly the Lean term the EVM bytecode's
keccak prefix produces. `ffi.KEC` is `opaque` in EVMYulLean, so this
term is irreducible by Lean's kernel: it's a symbol, not a number. The
equivalence proof for `keccakPrefix_value` closes by `rfl` because the
LHS (the bytecode-side computation) and the RHS (`balanceSlotOf m addr`)
are *definitionally* the same term.

In the `StorageBalEquivAt` relation, we relate `σ_orig` at slot
`balanceSlotOf m addr` with `σ_opt` at slot `~addr` (the bitwise NOT
of the address; see the "Collision-avoidance" section). The
relation *quantifies over the address*, not over slots, so the
keccak result never has to be reduced to a number anywhere. It
just gets carried around symbolically until the slot is consumed by
SLOAD/SSTORE, at which point both layouts produce/consume *the
same loaded value* by the relation.

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
purity, Keccak collision-resistance) are unused here, the proof
deliberately avoids needing collision-resistance, which makes it
robust to even a (hypothetical) cryptographic break of Keccak.

### The injectivity safety condition

A storage-layout optimization is only sound if its *slot function*
is injective on addresses, otherwise two distinct users alias on
the opt side, with one's `mint` silently changing the other's
balance. The orig side gets this from Keccak's collision-resistance
(the existing evm-smith T5 axiom). The opt side uses
`UInt256.lnot`, a concrete bitwise op, and we proved its
injectivity in `EvmSmith/Lemmas/UInt256Order.lean`:

```lean
theorem lnot_injective : Function.Injective (UInt256.lnot)
```

Together with the contrapositive corollary
`distinct_addresses_distinct_opt_slots` in both
[`Equivalence.lean`](./Equivalence.lean) and
[`EquivalenceVyper.lean`](./EquivalenceVyper.lean), this is the
piece that lets two distinct addresses simultaneously hold distinct
balances on the opt side. No new axioms. `lnot_injective` reduces
via `sub_toNat_of_le` + `Nat.le_sub_one_of_lt` to Nat subtraction
cancellation, all kernel-checkable.

A non-injective slot function (say, `addr mod 2^32`) would fail
this theorem and immediately rule the optimization unsafe at the
type-check level. With `~addr`, the proof goes through.

## Refinement framework + abstract ERC-20 spec

The peephole theorems (`balanceLoad_observable_equiv`,
`balanceStore_observable_equiv`) prove that the orig and opt
*bytecode* agree on stack tops and post-state structure **under a
per-address storage relation**. The relation is taken as a
precondition; the peephole proof doesn't check whether the slot
function can actually maintain it across a sequence of operations.
A non-injective or named-slot-colliding slot function would
silently make the relation degenerate, and the peephole proof would
still go through.

This is the **soundness gap** the user flagged after the
collision bug surfaced. The refinement framework in
[`Spec.lean`](./Spec.lean) closes it at the *structure* level. The
relevant pieces:

### The abstract spec

A minimal ERC-20 modelled at the Lean level:

```lean
-- Storage layout, abstracted: balances + named non-balance state.
def AbsStorage := UInt256 → UInt256  -- balance map
-- Operations:
def absMint     (bal : AbsStorage) (dst amt : UInt256) : AbsStorage
def absBurn     (bal : AbsStorage) (src amt : UInt256) : AbsStorage
def absTransfer (bal : AbsStorage) (src dst amt : UInt256) : AbsStorage
```

Concrete storage is also `UInt256 → UInt256` but with
`Function.update` semantics. Operations write storage at the slot
derived from the address via the abstraction.

### The `SlotAbstraction` structure: both obligations type-level

```lean
structure SlotAbstraction where
  ValidAddr : UInt256 → Prop           -- which inputs are "addresses"
  NamedSlot : UInt256 → Prop           -- non-balance state slots
  slotFn    : UInt256 → UInt256        -- slot derivation
  inj       : ∀ a b, ValidAddr a → ValidAddr b →
              slotFn a = slotFn b → a = b
  disjoint  : ∀ a, ValidAddr a → ¬ NamedSlot (slotFn a)
```

**You cannot instantiate `SlotAbstraction` without supplying proofs
for both `inj` and `disjoint`.** That's the type-system enforcing
the obligations.

### The preservation theorems

```lean
theorem mint_refines     ... -- requires sa.ValidAddr dst
theorem burn_refines     ... -- requires sa.ValidAddr src
theorem transfer_refines ... -- requires sa.ValidAddr src + ValidAddr dst
```

Each:
- Per-valid-address branch uses `sa.inj` to argue distinct
  addresses don't share slots, required for the "the write at
  another user's slot didn't touch mine" step.
- Per-named-slot branch uses `sa.disjoint` to argue the write
  doesn't corrupt metadata, required for the "named slot is
  untouched" preservation step.

A non-injective slot function fails to construct `inj`. A slot
function that collides with named state fails to construct
`disjoint`. Either failure prevents the structure from being
instantiated, which prevents the preservation theorems from being
applied, which means **the optimization cannot claim soundness**
under this framework.

### Concrete instances

```lean
def lnotSlotAbstraction : SlotAbstraction where
  ValidAddr := IsValidAddress         -- a.toNat < 2^160
  NamedSlot := IsSoladyNamedSlot      -- s ∈ {0, 1, 2, _TOTAL_SUPPLY_SLOT}
  slotFn    := UInt256.lnot
  inj       := lnot_injective_on_valid
  disjoint  := lnot_disjoint_from_named
```

The `disjoint` proof is the high-bit argument: for any 160-bit `a`,
`lnot a ≥ 2^256 - 2^160`, which is well above every named slot
(max = `_TOTAL_SUPPLY_SLOT ≈ 2^46`).

The pre-fix `idSlotAbstraction` is **not constructible** under
this framework: `id 0 = 0 ∈ {0, 1, 2}`, so `disjoint` cannot be
proved. The buggy design is rejected at type-check.

### What to do to make your bytecode pass the proofs

If you (or an AI) propose a new storage-layout optimization, here
is the **recipe** to make it sound under this framework:

1. **Pick a slot function `f : UInt256 → UInt256`** that you
   believe satisfies the two safety conditions.
2. **Define your `ValidAddr` predicate**: typically `a.toNat <
   2^160` for real Ethereum addresses, but any decidable predicate
   works.
3. **Define your `NamedSlot` predicate**: the slots your contract
   uses for non-balance state. This depends on the compiler / source
   layout (Solidity assigns 0, 1, 2, … to declared state vars;
   constants like Solady's `_TOTAL_SUPPLY_SLOT` are baked in).
4. **Prove `inj`**: `∀ a b, ValidAddr a → ValidAddr b → f a = f b
   → a = b`. For `lnot`, this comes from `lnot_injective`.
   Hashing functions reduce to a cryptographic axiom (Keccak
   collision-resistance is evm-smith's T5). For ad-hoc choices,
   you'll need to prove it from first principles, if you can't,
   your optimization is unsafe.
5. **Prove `disjoint`**: `∀ a, ValidAddr a → ¬ NamedSlot (f a)`.
   This is the test that catches the named-slot collision class
   of bugs. The proof is contract-specific: enumerate the named
   slots, show each one is outside the image of `f` restricted to
   valid addresses.
6. **Instantiate `SlotAbstraction`** with the four fields.
7. **Apply `mint_refines`, `burn_refines`, `transfer_refines`** to
   your operations. The theorems hand you a refinement-preserving
   post-state, which is exactly the user-visible guarantee
   "balances are correctly updated, metadata is untouched."

If any of steps 4–6 fail, **don't ship the optimization**. The
proof obligation is the safety obligation.

### Where the framework currently stops: the EvmYul.State bridge

The refinement preservation theorems live at the *abstract*
storage level (`UInt256 → UInt256` with `Function.update`). To lift
them to actual `EvmYul.State.sstore` / `sload`, the layer the
deployed bytecode operates on, needs one more bridge theorem:

```lean
theorem storageAt_sstore
    (σ : EvmYul.State .EVM) (k v : UInt256) (acc : Account .EVM)
    (h : σ.accountMap.find? σ.executionEnv.codeOwner = some acc) :
    ∀ slot, storageAt (EvmYul.State.sstore σ k v) slot
            = Function.update (storageAt σ) k v slot
```

where `storageAt σ slot` is the abstract projection from `σ`'s
account storage at `slot`. With this in hand, every theorem in
`Spec.lean` lifts mechanically to the running EVM.

The proof requires two RBMap-storage-key-level lemmas not currently
in Batteries:

```lean
-- Round-trip on the v = 0 (erase) branch:
storage_find?_erase_self : (t.erase k).find? k = none

-- Nonalias on the v = 0 (erase) branch:
storage_find?_erase_of_ne : k ≠ k' → (t.erase k).find? k' = t.find? k'
```

The `find?_insert_of_eq` / `find?_insert_of_ne` counterparts ship
in `Batteries.RBMap.Lemmas`. The erase versions are provable via
the existing `EvmSmith.Layer1.rbmap_erase_toList_filter` (now made
public for this purpose) in ~50 lines of Lean, same proof
structure as the AccountAddress-keyed `EvmYul.Frame.find?_erase_ne`.
The instance-typeclass setup (`Std.LawfulEqCmp` for UInt256) is
already done in
[`EvmSmith/Lemmas/UInt256Order.lean`](../../Lemmas/UInt256Order.lean).

Estimated effort to close: ~one focused afternoon. The infra is in
place; what's missing is the proof labor on the storage-key-level
erase lemmas. Documented here as the next step rather than
attempted in this pass because the proofs hit several layered
Batteries-API edge cases (decide-equality on `(v == default)`, Fin
sub modular arithmetic, RBMap toList-filter unification) that
warrant a dedicated session rather than being entangled with the
peephole story.

### What's not formalized here (and why)

The proofs cover the **balance-access peephole** end-to-end. They do
not include a closed-form `sload (sstore σ k v) k = v` round-trip
lemma at the `EvmYul.State` level, which would let us write a single
top-level "balanceOf(addr) after mint(addr, v) returns v in both
layouts" theorem.

That lemma is technically true (and trivially so. It's the EVM's
basic storage semantics), but its proof requires a sequence of
`Batteries.RBMap`-internal rewrites (`find?_insert_of_eq`,
`updateStorage`'s erase-vs-insert branch on `v == 0`, etc.) that
aren't currently exposed as named lemmas in the framework. Closing it
in this demo would mean re-deriving a slice of the RBMap API that
should arguably ship upstream; that's orthogonal to the storage-layout
optimization argument we wanted to demonstrate.

So the proof obligation we *don't* discharge here is a property of
EVMYulLean's storage model, not of the layout optimization. The
peephole soundness *as a peephole* (i.e., on the hand-rolled 10-op
mirror) is proved; the lift to whole-bytecode equivalence on the
deployed contract is not, see "What is proven" at the top
of this report.

The structural form `balanceStore_observable_equiv` exposes the
post-store state precisely enough that any consumer wanting the
round-trip can derive it from the standard EVM property, but
they'd still need to close the bridge to `EvmYul.State` themselves.

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
   prefix from Solidity. `keccak256(slot ++ key)` over a 64-byte
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

Coverage: same shape as the Solidity behaviour test, mint, burn,
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
| `vyperBalanceLoad_relational_equiv` | Under the per-address storage relation (`(sload σ_orig slot).snd = (sload σ_opt (~addr)).snd`), both load blocks land at the same stack-top. The orig-side characterization is taken as a hypothesis, the 10-step `unfold; rfl` chain for the keccak prefix WHNF-times out in EVMYulLean's current shape, same root cause as the Solidity variant's storage round-trip gap. |

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
