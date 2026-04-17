# Review 2 — Foundry tests for `add3` plan (v2)

Round-2 spot-check against the five round-1 fixes.

## Fix-by-fix

**1. Bytecode sync (file-based).** Present and complete. Dumper exe + `vm.readFile` + `vm.parseBytes` + `_trim` + committed hex file is the right shape, matches review-1 option (a), and the residual `#guard bytecode.size == 19` is now correctly framed as a structural backstop, not as the sync mechanism.

**2. `foundry.toml` `src` conflict.** Fixed by dropping `src = "src"`. Fallback "keep `src/` as empty with `.gitkeep` if forge complains" is pragmatic; safer concrete instruction is "leave an empty `src/.gitkeep` in from the start." Minor.

**3. `.gitmodules` location.** Correctly placed at repo root with path `EvmSmith/Demos/Add3/foundry/lib/forge-std`.

**4. Short-calldata test.** `test_Add3_shortCalldata` present plus bonus `test_Add3_longCalldata`.

**5. Caveats / forge version / `forge init` edge cases.** All three present: nonce/EXTCODEHASH/no-CODECOPY-of-self caveats; minimum forge ≥ 1.0.0; pre-check `test ! -e …` before `forge init`.

## Specific verification points

- **`EvmYul.toHex` exists** — confirmed at `EVMYulLean/EvmYul/Wheels.lean:47` with signature `ByteArray → String` (no `0x` prefix; no newline). Plan should drop the pseudocode and commit: `let hex := "0x" ++ EvmYul.toHex Add3.bytecode ++ "\n"`. Loose end — an implementer could waste time reinventing `hexOfByte`.

- **`_trim` whitespace coverage.** Strips only `\n` and space. Misses `\r` (CRLF on Windows) and `\t`. Generator output is controlled, but add `0x0d` to `_trim` defensively for Windows checkouts where git autocrlf may rewrite line endings.

- **`vm.parseBytes` / `0x` prefix.** Generator writes `"0x" ++ …` — matches requirement.

- **`fs_permissions` path resolution.** Per Foundry docs, paths are relative to the project root (where `foundry.toml` lives). `./test/Add3.bytecode.hex` is correct.

- **Work-order ordering.** Steps 3 → 4 → 5 → 8 sound; 9 (`lake build`) independent of 8 (`forge test`).

- **`refresh-bytecode` skill.** Correctly marked optional. A sentence noting overlap with existing `add-program` / `debug-proof` skills would help the implementer decide.

## Verdict

The five round-1 issues are addressed. Two small residual items: (a) commit to `EvmYul.toHex` in the dumper snippet, (b) add `\r` to `_trim`. Both line-level edits, not structural.

VERDICT: accept
