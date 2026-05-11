# Plan — ERC-20 Storage Layout Optimization (revised)

Source task: `storage_layout_opt.md`. Reviewed and revised after sub-agent
review (key findings: KECCAK256 in EVMYulLean is *concrete* via opaque
`ffi.KEC`, not abstract; memory divergence between layouts in `log3`
needs design-level resolution; transferFrom must be in scope; Solady's
test uses no `vm.load`/`stdStore` probes against balance slots so the
test suite *can* be reused unchanged).

## Goal

Take Solady's ERC-20, change the storage layout so balances live at
`uint256(addr)` directly (no Keccak), prove the affected functions
produce equivalent user-visible behavior, run Solady's tests against
both, compare gas, write a report + blog draft.

## Constraints from the task

- Use evm-smith for proofs, in the style of `OptimizedProgram.lean` /
  `OptimizedProgramV2.lean` (block-level equivalence theorems).
- No new sorries, no new axioms, no new style hypotheses (only the 2
  pre-existing evm-smith axioms — keccak collision resistance and
  precompile purity — are allowed).
- Allowances and totalSupply stay as-is; only balances are relayouted.
- The task hint: storage-layout injectivity per user address is enough;
  don't try to compute Keccak.

## Tooling check (per task md:91-94)

- foundry 1.5.1 ✅
- lean / lake (Lean 4.22.0) ✅
- git ✅
- solc — not installed standalone, but foundry's solc resolver handles
  it via foundry.toml. Confirmed by reading WETH foundry.toml. No
  additional install needed.

## Workspace

All new code under `EvmSmith/Demos/ERC20/`. Mirrors WETH/Register layout.
Namespace convention: `EvmSmith.ERC20`, proofs in
`EvmSmith.ERC20Proofs`-or-`.Equivalence`.

```
EvmSmith/Demos/ERC20/
├── Program.lean             # hand-rolled ERC-20 bytecode, keccak-balance layout
├── OptimizedProgram.lean    # hand-rolled ERC-20 bytecode, address-as-slot layout
├── Equivalence.lean         # equivalence theorems between the two
├── DumpBytecodeOrig.lean    # hex dump for foundry tests
├── DumpBytecodeOpt.lean
├── STORAGE_LAYOUT.md        # investigation: Solady's layout, our hand-rolled mirror
├── REPORT_ERC20.md          # final report
├── BLOG_DRAFT.md            # blog post draft
└── foundry/
    ├── foundry.toml
    ├── src/
    │   ├── MockERC20Original.sol  # Solady-based, unchanged
    │   └── MockERC20Optimized.sol # Solady-based, with balance-slot overrides
    ├── test/
    │   ├── ERC20Compare.t.sol    # adapted Solady tests against both backends
    │   └── ERC20GasCompare.t.sol # per-op gas comparison
    └── lib/  (submodules: forge-std + solady)
```

## Proof strategy (revised)

KECCAK256 in EVMYulLean is concrete: it dispatches to `ffi.KEC`
(`opaque`, no kernel reduction). So Keccak's result is an irreducible
term in proofs — we *don't* need to invent an "abstract step lemma" and
we *can't* (the semantics is fully specified).

The right framing is:

1. **Define `balanceSlot : UInt256 → UInt256`** as a Lean function
   computing exactly what the original keccak prefix produces, using the
   real `ffi.KEC`. This is concrete but unreducible (Keccak is opaque).
   We name it for clarity.

2. **Prove a balance-slot characterization lemma**:
   ```lean
   lemma balance_slot_prefix_value
       (s : EVM.State) (addr : UInt256) (rest : Stack UInt256) (pc : UInt256) :
     runSeq balanceSlotPrefix
       { s with stack := addr :: rest, pc := pc }
       = .ok { ... with stack := balanceSlot addr :: rest ... }
   ```
   Where `balanceSlotPrefix` is the 5-op sequence
   `[MSTORE 0x0c; MSTORE 0x00; PUSH1 0x20; PUSH1 0x0c; KECCAK256]`
   (and stack inputs are arranged correctly). Both sides reduce to
   the same expression involving `ffi.KEC` applied to memory bytes,
   so `unfold runOp EvmYul.step; rfl` should close — verify
   experimentally early in phase 3.

   If `rfl` doesn't close because memory writes don't reduce nicely,
   fall back to a series of small lemmas — but try `rfl` first.

3. **Storage-relation predicate** between original-layout and
   optimized-layout states. Range over the *underlying storage map*,
   not `sload`'s return tuple (review fix). E.g.:
   ```lean
   def StorageBalEquiv (σ_orig σ_opt : AccountMap .EVM) (C : Address) : Prop :=
     -- For every address, the orig's balance slot has the same value as
     -- the opt's `uint256(addr)` slot.
     ∀ addr : UInt256,
       getStorage σ_orig C (balanceSlot addr) = getStorage σ_opt C addr
     ∧
     -- All non-balance slots match exactly.
     (∀ s : UInt256,
        (¬ ∃ addr, balanceSlot addr = s) ∧ (¬ ∃ addr, UInt256.ofNat (Address.toNat addr) = s)
        → getStorage σ_orig C s = getStorage σ_opt C s)
   ```
   (Exact form decided during phase 3 once the storage model is read
   in detail; the conceptual relation is "balances live in different
   slots, everything else identical".)

4. **Per-function functional correctness, then equivalence by
   composition.**

   For each affected function (`transfer`, `transferFrom`, `_mint`,
   `_burn`, `balanceOf`), state a *functional-correctness* theorem:
   "given balances `bFrom`, `bTo` at the relevant slots before, after
   the call the new balances are `bFrom - amount`, `bTo + amount` at
   the same relevant slots."

   Prove this *separately* for each version (original keccak-layout,
   optimized addr-layout). The two theorems have identical statements
   modulo the slot function (`balanceSlot addr` vs `addr`).

   Then equivalence is a *corollary*: from `StorageBalEquiv` before to
   `StorageBalEquiv` after, given the same calldata. No giant
   relational state-shape proof needed.

5. **Memory divergence in `log3` topics — design-level fix.**

   In the hand-rolled bytecode we *control*, the optimized version
   never mstores the address — instead it uses `CALLER` (or `DUP1`
   from stack) as the topic source for `log3`. So both versions emit
   bit-for-bit identical `Transfer(from, to, amount)` events. No
   "memory unread / different memory" concern downstream.

   This is a *cleaner* design than Solady's Keccak-prefix-side-effect
   trick of reading the address back from memory, and gets called out
   in the report as an additional win.

## Phase 1 — Engineering (Solidity)

### 1.1 Vendor Solady
- Add Solady as a git submodule under
  `EvmSmith/Demos/ERC20/foundry/lib/solady/`. Pin to a known-good
  commit. Update `.gitmodules`.

### 1.2 Two Mock contracts
- `MockERC20Original.sol`: inherits Solady's `ERC20`, no overrides
  (just `name`/`symbol`/`decimals` + `mint`/`burn` for testing).

- `MockERC20Optimized.sol`: inherits Solady's `ERC20`, overrides the
  affected `virtual` functions. All five are `virtual` in Solady's
  source (`balanceOf` line 155, `transfer` line 217, `transferFrom` line
  257, `_mint` line 496, `_burn` line 529, `_transfer` line 559). We
  override each with assembly that uses `caller()` (or the parameter
  address) directly as the storage slot for balances. Allowances,
  nonces, totalSupply stay as-is.

  Verify override compatibility by reading the parent functions'
  visibility/virtual modifiers up front in 1.1.

### 1.3 Foundry config
- `foundry.toml`: solc 0.8.20, optimizer on, fs_permissions for hex files.
- Use Solady's own `ERC20.t.sol` adapted (or duplicated) to run against
  both contracts.

### 1.4 Tests
- Both contracts must pass identical test suites.
- Per-op gas comparison reported.

## Phase 2 — Investigation

In `STORAGE_LAYOUT.md`:
- Solady's storage layout (slots from Solady source comments).
- The optimization (balance slot = raw address).
- Why it's safe (injectivity).
- Bytecode-level diff at the relevant sites.

## Phase 3 — Proof scaffolding (hand-rolled bytecode + proofs)

### 3.1 `Program.lean` — keccak-balance hand-rolled ERC-20

Functions, selector-dispatched (just the affected ones):
- `mint(address,uint256)`       — `0x40c10f19`
- `burn(address,uint256)`       — `0x9dc29fac`
- `balanceOf(address)`          — `0x70a08231`
- `transfer(address,uint256)`   — `0xa9059cbb`
- `transferFrom(address,address,uint256)` — `0x23b872dd`

(Skip `totalSupply`, `name`, `symbol`, `decimals` from the proof — they
don't touch balance storage. Skip `approve`, `allowance`, `permit` — also
not affected.)

Each function block uses Solady's exact balance-slot computation:
```
mstore(0x0c, 0x87a211a2)
mstore(0x00, addr)
let slot := keccak256(0x0c, 0x20)
sload(slot)  // or sstore(slot, val)
```

Estimated total bytecode: ~250-400 bytes.

### 3.2 `OptimizedProgram.lean` — address-as-slot hand-rolled ERC-20

Same dispatcher + same function shapes, but each balance access uses
the address directly (no MSTORE+KECCAK256). Log emission topics use
`CALLER` or a DUP'd address instead of `mload(0x0c)`.

### 3.3 `Equivalence.lean` — proofs

A. **Concrete `balanceSlot` definition.**
   ```lean
   def balanceSlot (addr : UInt256) : UInt256 := ...
   ```
   Matches what `MSTORE; MSTORE; KECCAK256` actually computes in EVMYulLean.

B. **Balance-slot-prefix characterization lemma.**
   ```lean
   lemma balance_slot_prefix
       (s : EVM.State) (addr : UInt256) ... :
     runSeq balanceSlotPrefix { s with stack := addr :: rest, pc := pc }
       = .ok { ... with stack := balanceSlot addr :: rest ... }
   ```
   Try `unfold runOp EvmYul.step; rfl` first; fall back to per-opcode lemma chain if needed.

C. **Per-function functional-correctness theorems.**

   For each of `mint`, `burn`, `transfer`, `transferFrom`, `balanceOf`:
   - One theorem about the *original* layout, parameterized by
     pre-balances at `balanceSlot from`, `balanceSlot to`.
   - One theorem about the *optimized* layout, parameterized by
     pre-balances at `from`, `to` directly.
   - Both theorems state the same post-conditions on the relevant
     balance values.

D. **Storage-relation predicate and per-function equivalence
   corollaries.**

   ```lean
   def StorageBalEquiv (σ_orig σ_opt : ...) (C : Address) : Prop := ...
   theorem transfer_observable_equiv ... : ...
   theorem transferFrom_observable_equiv ... : ...
   theorem mint_observable_equiv ... : ...
   theorem burn_observable_equiv ... : ...
   theorem balanceOf_observable_equiv ... : ...
   ```

E. **Top-level wrapper theorem** (optional, time permitting):
   "Under StorageBalEquiv, the two whole-bytecode programs yield
   observably equivalent traces on any of the supported function
   calls."

### 3.4 Missing opcode lemmas
Expected to need:
- `runOp_mstore`
- `runOp_keccak256`
- `runOp_log3`
- `runOp_push1` for various values (already there)
- `runOp_push2` (already there)
- `runOp_eq`, `runOp_shr` for selector dispatch (probably new).

Add to `EvmSmith/Lemmas.lean` as encountered. Proof template: `unfold
runOp EvmYul.step; rfl`.

## Phase 4 — Tests & Gas

Covered by phase 1.4; just record outputs into `REPORT_ERC20.md`.

## Phase 5 — Report & Blog

- `REPORT_ERC20.md`: what was done end-to-end, theorems summary, gas
  numbers, trust boundary (same axioms as evm-smith elsewhere).
- `BLOG_DRAFT.md`: motivation, why/what/how, examples, theorems in
  human terms, conclusion.

## Workflow (per task md:60-69)

- **This plan**: reviewed in a loop until sub-agent approves. After
  this revision, request another review; iterate until approved.
- **Commit before spawning impl sub-agents.**
- **Sub-agent review after each implementation step.**
- **Commit on each completed step.** Don't push.
- **No human feedback request.** Keep grinding.
- **Sub-agents must not perform destructive ops.**

## Step-by-step execution order

1. (current) Revise plan; sub-agent re-review until approved.
2. Commit plan.
3. Phase 1.1 — vendor Solady, set up foundry skeleton. Commit.
4. Phase 1.2-1.4 — write contracts, write tests, run. Commit.
5. Phase 2 — `STORAGE_LAYOUT.md`. Commit.
6. Phase 3.1 — `Program.lean`. Commit. Sub-agent review.
7. Phase 3.2 — `OptimizedProgram.lean`. Commit. Sub-agent review.
8. Phase 3.3 — `Equivalence.lean` (step A first, characterization).
   Commit. Sub-agent review.
9. Phase 3.3 — steps B-D, per-function equivs. Iterative commits.
10. Phase 3.4 — opcode lemmas as needed during 3.3 (in-line commits).
11. Phase 5 — report + blog. Commit.
12. Final verification: `lake build` is sorry-free; `forge test` passes
    on both backends; `#print axioms <top-level theorem>` shows only
    the 2 evm-smith axioms.

## Risks (after revision)

1. **`unfold; rfl` may not close the balance-slot characterization
   lemma** because memory writes go through `ByteArray.write` which is
   defined operationally. Mitigation: try `rfl` first; if it fails, use
   per-opcode lemma chain with explicit memory-state reasoning. Last
   resort: introduce a helper `mstore_mstore_keccak256_value` lemma
   proved by reducing the byte expression manually (no axioms).
2. **Bytecode size**: 250-400 bytes of hand-rolled ERC-20 is ~3-5x WETH.
   Proof effort scales. If running out of session budget, scope down to
   `transfer`+`mint`+`balanceOf` and explicitly note in the report that
   `burn`/`transferFrom` are left as identical-pattern follow-up.
3. **`runOp_log3` lemma** may need careful proof of memory-read
   behavior. Bypass by designing the optimized bytecode so `log3`
   topics come from stack (CALLER + parameter address), not memory.
4. **Solady `_givePermit2InfiniteAllowance` branch** affects `approve`
   and `transferFrom` allowance handling. Allowances aren't touched by
   our optimization, so we don't override `_givePermit2InfiniteAllowance`
   and the Solady default branch runs identically on both backends.
5. **Test adaptation surface**: Solady's tests reference `MockERC20` —
   we instantiate it twice (`Original` and `Optimized` subclasses) and
   parameterize. Confirmed by reading `ERC20.t.sol`: tests use the
   public interface only, no `vm.load(token, specificSlot)`.

## Trust boundary

Identical to existing evm-smith demos:
1. Lean's type checker.
2. EVMYulLean's faithfulness to the EVM (`#print axioms` should show
   only the 2 pre-existing axioms).
3. Any per-demo structural hypotheses we explicitly declare (e.g.,
   "the deployed bytecode at C is the original/optimized hand-roll").
   No new axioms.
