# Plan — ERC-20 Storage Layout Optimization (Vyper / Snekmate)

The Solidity variant was done at the source level (rewriting Solady's
inline-asm balance accesses with `MockERC20Optimized.sol`). The user
pointed out that the optimization should ideally be applied at the EVM
*bytecode* level, not the language level. For Vyper, that's the path
we'll take from the start: Vyper has no inline assembly, so source-
level rewriting isn't an option anyway.

## Spec

Same as the Solidity variant: take a standard Vyper ERC-20 (Snekmate),
identify the balance-storage layout, optimize so balances live at
`uint256(addr)` directly, run tests against both backends, compare gas,
prove equivalence in Lean, modify the report and blog draft to fold
in the Vyper findings.

## Strategy

1. **Compile Snekmate's `erc20.vy`** to runtime bytecode.
2. **Investigate** Vyper's storage layout (sequential slot assignment +
   `keccak256(slot, key)` for `HashMap[address, uint256]`). Confirm by
   inspecting the compiled bytecode and Vyper's storage-layout JSON.
3. **Bytecode-level peephole transformation**: identify every site
   where Vyper emits the keccak-prefix balance access pattern and
   replace it with a direct address push. Skip allowance sites (two-
   key, can't be safely flattened). The replacement is mechanical and
   local.
4. **Both bytecodes deployed** via Foundry `vm.etch` at distinct
   addresses; the existing Snekmate test suite (or an adapted version
   of it) runs against both.
5. **Gas comparison**: per-op deltas, runtime size delta.
6. **Lean proofs**: a per-peephole equivalence at the bytecode level.
   The proof structure mirrors the Solidity case — it's the same
   keccak-prefix-vs-direct-load equivalence — but the *prefix shape*
   may differ between Vyper's compiler output and Solidity's, so we
   prove the Vyper-specific shape too.

## Workspace

```
EvmSmith/Demos/ERC20/foundry-vyper/  (new — separate Foundry project so
                                       solc / vyper configs don't fight)
├── foundry.toml          (vyper.optimize, allow_paths to snekmate)
├── lib/forge-std/        (submodule)
├── lib/snekmate/         (submodule — full Snekmate, pinned)
├── src/
│   ├── MockERC20.vy            # Snekmate-based mock (or just use Snekmate's directly)
│   └── BytecodePatcher.sol     # helper that applies the peephole patch to the runtime
├── script/
│   └── patch.py                # offline patcher: reads compiled bytecode, emits patched
└── test/
    ├── ERC20CompareVyper.t.sol
    └── ERC20GasCompareVyper.t.sol

EvmSmith/Demos/ERC20/
├── ProgramVyper.lean           # Vyper's exact keccak-prefix shape
├── OptimizedProgramVyper.lean  # the peephole-replacement
├── EquivalenceVyper.lean       # peephole soundness
└── REPORT_ERC20.md             # extended with Vyper section
└── BLOG_DRAFT.md               # extended with Vyper section
```

## Tooling

- `python3 -m venv` → install `vyper` in the venv.
- Foundry already supports Vyper compilation (`vyper = { ... }` in
  foundry.toml), provided `vyper` is on `PATH`. We activate the venv
  in the test command.
- No other new tooling.

## Phases

### Phase 1: venv + Vyper toolchain (#9)
- Create venv under `EvmSmith/Demos/ERC20/foundry-vyper/.venv/`.
- Install `vyper` (latest 0.5.x).
- Verify `forge build` picks it up.

### Phase 2: vendor Snekmate (#9 cont.)
- Add Snekmate as a git submodule (pinned).
- Configure remappings.

### Phase 3: investigation (#10)
- Compile Snekmate's `erc20.vy`. Generate the storage-layout JSON via
  `vyper -f layout`. Confirm balanceOf is at the expected sequential
  slot; allowance/nonces/totalSupply slot ids documented.
- Inspect the compiled runtime: find the balance-access peephole(s).
- Document in `STORAGE_LAYOUT_VYPER.md` (or fold into the existing
  STORAGE_LAYOUT.md).

### Phase 4: bytecode patcher (#11)

**Hard constraint — length-preserving patches.** The patcher must not
change the runtime size. Vyper embeds the runtime length in the deploy
code, and every `PUSH2 <jumpdest>` immediate uses absolute addresses;
shifting bytes is a cascade of breakage. Mitigation: pad the
replacement sequence with dead opcodes (`JUMPDEST` for safety on top-
of-stack-cleared paths, or `PUSH0; POP` as a no-op pair) to match the
original site length byte-for-byte. The patched bytes only contain
the replaced slot computation; immediates and jump destinations are
untouched.

**Site discrimination — fail-closed on mismatch.** The keccak-prefix
pattern appears in non-balance contexts (allowance preimage, EIP-712
domain separator, role hashes, nonce derivation). The discriminator
will be the **slot-id immediate** baked into the keccak preimage. We
get the balanceOf slot id from `vyper -f layout` and only patch sites
whose preimage includes exactly that slot id. The patcher then:

1. Reads the storage-layout JSON, extracts `balanceOf` slot id.
2. Disassembles the runtime; collects all keccak-prefix sites.
3. Filters to sites whose preimage matches `(slot=balanceOf_slot_id,
   key=<address-shaped-value>)`.
4. Cross-checks the count against an expected count derived from the
   AST/source walk (`self.balanceOf[...]` accesses in `erc20.vy`,
   including all module-imported paths).
5. **Fails closed** (aborts patching, prints diagnostic) if the
   counts don't match.

Output: two runtime hex files committed to the repo
(`erc20.runtime.hex` + `erc20.optimized.runtime.hex`), refreshed by
a `make patch` rule. Constructor bytecode (and the embedded runtime
length immediate) is *unchanged* because we patch only the runtime.

### Phase 5: tests (#12)

Constructor handling: Vyper's `__init__` initialises immutables
(name, symbol, decimals, EIP-712 nameHash + versionHash) which live
inside the runtime bytecode region. `vm.etch` bypasses the
constructor entirely, so we *can't* just etch the optimized runtime
on top of a fresh address — immutables would be zero.

The right pattern (option (b) from review):

1. Deploy the **original** Vyper contract normally (`new MockERC20(...)`).
   This runs the real constructor, initialises the immutables in the
   runtime region, and leaves a properly-set-up contract at the
   deployed address.
2. Capture the deployed runtime via `address.code` (now contains the
   initialised immutables baked in).
3. For the optimized backend: deploy *another* instance of the same
   original contract normally (constructor → initialised immutables),
   then `vm.etch` the optimized runtime onto it. Because the
   length-preserving constraint above keeps immutable offsets stable,
   the immutables stay in place.
4. Both contracts now have correctly-initialised storage and code.
5. Run an abstract behaviour test against both, plus gas comparison.

Re-use Snekmate's `test/tokens/ERC20.t.sol` as inspiration or write a
focused parameterised suite (same shape as the Solidity variant's
`ERC20Compare.t.sol`).

### Phase 6: Lean (#13)

**Hard gate**: phase 3 must produce the exact Vyper keccak preimage
layout (key-then-slot vs slot-then-key, padding direction, preimage
size) before phase 6 starts. No speculative drafting.

- `ProgramVyper.lean`: hand-rolled Vyper-style keccak prefix matching
  whatever phase 3 discovered.
- `OptimizedProgramVyper.lean`: the addr-as-slot version.
- `EquivalenceVyper.lean`: theorems analogous to the Solidity case.
  Specifically:
  - `vyperKeccakPrefix_value` — characterises the Vyper-style keccak
    prefix.
  - `balanceLoadVyperOrig_value` / `balanceLoadVyperOpt_value`.
  - `balanceLoadVyper_observable_equiv` — under per-address relation.
  - `balanceStoreVyper_observable_equiv` — structural.
- AxiomCheck addition.

### Phase 7: docs (#14)
- Extend `REPORT_ERC20.md` with a "Vyper / Snekmate" section.
- Extend `BLOG_DRAFT.md` with a "Same trick, different compiler" angle.

## Risk register

1. **Vyper-compiled bytecode is large.** Snekmate's ERC-20 has permit,
   EIP-712 domain, ownable, minter role — likely thousands of bytes.
   The peephole patcher must find balance-access sites reliably.
   Mitigation: write a precise regex/byte-pattern matcher; verify by
   running the original tests against the original bytecode (sanity);
   then verify the patched bytecode passes the same tests.

2. **Vyper's keccak prefix shape may differ from what we expect.**
   Vyper's bytecode includes calldata-padding, dirty-bits clearing,
   `keccak256(slot, key)` vs `keccak256(key, slot)`. We need to look at
   actual compiler output, not assume. Mitigation: do the
   investigation phase carefully; document the exact shape.

3. **Snekmate's tests may use cheatcodes that probe specific slots.**
   Check `ERC20.t.sol`. If yes, fork the tests; if no, reuse as-is.

4. **Vyper / Foundry integration friction**. Foundry's Vyper support
   is via the `vyper` binary on `PATH`; we'll need `forge build` to see
   the venv'd one. Mitigation: scripting wrapper, or a `Makefile`
   that activates the venv before invoking forge.

5. **Address representation differences.** Vyper may pad the address
   in memory differently for the keccak preimage (e.g., right-aligned
   in a 32-byte word vs left-aligned). The peephole pattern needs to
   match Vyper's exact emission.

## Workflow rules (same as Solidity variant)

- Plan reviewed by sub-agent until approved.
- Commit before spawning impl sub-agents.
- Sub-agent reviews after each phase.
- Commit each completed phase. Don't push.
- No new sorries, no new axioms.
- Don't ask for human feedback; keep grinding.

## Out of scope

- Optimizing allowances/nonces (two-key maps, no safe single-slot embed).
- Optimizing the storage layout of the EIP-712 domain or ownable's
  fields (negligible gas, not part of the spec).
- Full per-function block walks of the Vyper-compiled ERC-20 in Lean
  (intractable for ~thousands of bytes). Same as Solidity variant: we
  prove peephole soundness and argue compositionally for whole-
  function equivalence.
- Cross-Vyper-version optimization: we pin a specific Vyper version
  and a specific Snekmate commit. The patcher is brittle to compiler
  upgrades; the contract is "compile once, patch once, ship". A
  Vyper version bump would require re-running the investigation +
  re-deriving the keccak-prefix byte pattern.

## Constraints written into the plan (from review)

- Patches are length-preserving (pad with `PUSH0 POP` no-ops or similar).
- Site discrimination uses the slot-id immediate to filter only
  balance-access sites; cross-checks against an expected site count
  from the AST; fails closed on mismatch.
- The test harness runs the real Vyper constructor first, then
  `vm.etch`-es the optimized runtime on top of an already-initialised
  instance — keeping immutables intact.
- Phase 3 is a hard gate before phase 6 (no speculative `ProgramVyper.lean`).
- Vyper version pinned in the venv; Snekmate version pinned via
  submodule; `foundry.toml` mirrors Snekmate's relevant settings
  (`vyper = { optimize = "gas" }`, `ffi = true`).
