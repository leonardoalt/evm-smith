import EvmYul.Frame
import EvmSmith.Demos.Groth16.SpecDSL

/-!
# Groth16 verifier — entry-point / dispatcher facts (bytecode-level)

The "structural" half of the spec story, in the style of
`Demos/Weth/EntryPoints.lean`: facts that are *decidable* over the actual
`bytecode` bytes, discharged by `native_decide`, so they break the instant
the bytecode changes. No precompile-correctness assumption is needed for any
of these — they are facts about *this contract's own* control flow and
memory wiring, true regardless of what `BN_MUL`/`BN_ADD`/`SNARKV` answer.

The headline fact is `program_has_no_sstore`: this contract is a `view`
function from its first byte to its last — the strongest, and cheapest,
guarantee this demo offers, and the one that needs no axiom at all.
-/

namespace EvmSmith.Groth16

open EvmYul EvmYul.EVM

/-- The opcode decoded at byte offset `pc` of this contract's runtime
bytecode (without its immediate argument), or `none` past the end. -/
def opAt (pc : Nat) : Option (Operation .EVM) :=
  (decode bytecode (UInt256.ofNat pc)).map (fun instr => instr.1)

/-- **A genuine, push-width-respecting disassembly**, walking sequentially
from `pc = 0` and skipping over each `PUSH*`'s immediate bytes — unlike
`opAt`, which decodes whatever instruction *would* start at a given raw
byte offset, with no regard for whether that offset is ever actually a
real instruction boundary. The two coincide on `Demos/Weth` (whose only
immediates are 1/2/4-byte selectors/offsets), which is why `opAt`-at-every-
offset facts were safe to state directly there. They do *not* coincide
here: this contract's nineteen 32-byte constants (eighteen verifying-key
words plus the scalar-field modulus `r`) are effectively random bytes, and
`0x55` (`SSTORE`) — or byte sequences that decode as `CALL` — reliably turn
up *inside* some `PUSH32` immediate at some raw offset. `opAt`-at-every-
offset claims over the whole 904-byte range are therefore false (and were
caught failing exactly this way once
the placeholder constants were replaced with real ones); `linearScan`
is the fix, and is what `program_has_no_sstore` / `does_three_external_calls`
below actually use. `fuel` only bounds the recursion (904 steps suffice;
called with headroom). -/
def linearScan : Nat → Nat → List (Nat × Operation .EVM)
  | 0, _ => []
  | fuel + 1, pc =>
    if pc ≥ bytecode.size then []
    else
      match decode bytecode (UInt256.ofNat pc) with
      | none => []
      | some (op, some (_, w)) => (pc, op) :: linearScan fuel (pc + 1 + w)
      | some (op, none) => (pc, op) :: linearScan fuel (pc + 1)

/-! ## (1) Only one entry point -/

/-- The dispatch prefix extracts the ABI selector in the standard way:
`calldataload(0) >> 0xe0`. -/
theorem dispatch_extracts_selector :
    decode bytecode (UInt256.ofNat 0) = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) ∧
    decode bytecode (UInt256.ofNat 2) = some (.CALLDATALOAD, none) ∧
    decode bytecode (UInt256.ofNat 3) = some (.Push .PUSH1, some (UInt256.ofNat 0xe0, 1)) ∧
    decode bytecode (UInt256.ofNat 5) = some (.SHR, none) := by
  native_decide

/-- The dispatcher compares the selector against exactly the one entry-point
constant (`verifyProof`, at PC 6/11). -/
theorem dispatch_compares_one_selector :
    decode bytecode (UInt256.ofNat 6) = some (.Push .PUSH4, some (verifySelector, 4)) ∧
    decode bytecode (UInt256.ofNat 11) = some (.EQ, none) := by
  native_decide

/-- **There is no second selector comparison.** Across the whole dispatch
region (PCs 0–20), the only `EQ` is the one at PC 11. So the bytecode can
route to at most one function — there is no hidden second entry point. -/
theorem dispatch_has_exactly_one_selector_check :
    (List.range' 0 21).filter (fun pc => decide (opAt pc = some .EQ)) = [11] := by
  native_decide

/-- A selector that doesn't match `verifyProof` falls through to `REVERT`
(PC 20): there is no fallback / `receive` handler. -/
theorem dispatch_fallthrough_reverts :
    decode bytecode (UInt256.ofNat 20) = some (.REVERT, none) := by
  native_decide

/-! ## (2) This is a `view` function: no `SSTORE`, ever -/

/-- **No instruction in this entire 904-byte program is `SSTORE`.** Storage
cannot change no matter which branch executes or what the precompiles
return — the strongest guarantee here, and the only one that needs no
`SnarkvCorrect`/`BnMulSucceeds`/`BnAddSucceeds` assumption. Stated over
`linearScan`, not over every raw byte offset — see its docstring. -/
theorem program_has_no_sstore :
    ∀ p ∈ linearScan 900 0, p.2 ≠ .SSTORE := by
  native_decide

/-! ## (3) ABI decode: the nine proof/input words -/

/-- `verifyProof` decodes its single public input from calldata offset 260
(`PUSH2 260; CALLDATALOAD` at PCs 137/140) — i.e. the tenth word of calldata
(selector + 9 preceding proof words), as the one-public-input ABI layout
demands. (This is the *second* decode of the same offset — the first is
`checkField`'s read at PCs 55/58, validated separately by
`checkfield_validates_input`.) -/
theorem decodes_public_input :
    decode bytecode (UInt256.ofNat 137) = some (.Push .PUSH2, some (UInt256.ofNat 260, 2)) ∧
    decode bytecode (UInt256.ofNat 140) = some (.CALLDATALOAD, none) := by
  native_decide

/-- `verifyProof` decodes `proof.A` from calldata offsets 4 and 36. -/
theorem decodes_proof_a :
    decode bytecode (UInt256.ofNat 255) = some (.Push .PUSH1, some (UInt256.ofNat 4, 1)) ∧
    decode bytecode (UInt256.ofNat 257) = some (.CALLDATALOAD, none) ∧
    decode bytecode (UInt256.ofNat 262) = some (.Push .PUSH1, some (UInt256.ofNat 36, 1)) ∧
    decode bytecode (UInt256.ofNat 264) = some (.CALLDATALOAD, none) := by
  native_decide

/-- `verifyProof` decodes `proof.B`'s `x` words (`x.c1` at calldata offset
68, `x.c0` at offset 100) — the EIP-197 `(c1, c0)` ordering. -/
theorem decodes_proof_b_x :
    decode bytecode (UInt256.ofNat 310) = some (.Push .PUSH1, some (UInt256.ofNat 68, 1)) ∧
    decode bytecode (UInt256.ofNat 312) = some (.CALLDATALOAD, none) ∧
    decode bytecode (UInt256.ofNat 317) = some (.Push .PUSH1, some (UInt256.ofNat 100, 1)) ∧
    decode bytecode (UInt256.ofNat 319) = some (.CALLDATALOAD, none) := by
  native_decide

/-- `verifyProof` decodes `proof.B`'s `y` words (`y.c1` at calldata offset
132, `y.c0` at offset 164). -/
theorem decodes_proof_b_y :
    decode bytecode (UInt256.ofNat 324) = some (.Push .PUSH1, some (UInt256.ofNat 132, 1)) ∧
    decode bytecode (UInt256.ofNat 326) = some (.CALLDATALOAD, none) ∧
    decode bytecode (UInt256.ofNat 331) = some (.Push .PUSH1, some (UInt256.ofNat 164, 1)) ∧
    decode bytecode (UInt256.ofNat 333) = some (.CALLDATALOAD, none) := by
  native_decide

/-- `verifyProof` decodes `proof.C` from calldata offsets 196 and 228. -/
theorem decodes_proof_c :
    decode bytecode (UInt256.ofNat 708) = some (.Push .PUSH1, some (UInt256.ofNat 196, 1)) ∧
    decode bytecode (UInt256.ofNat 710) = some (.CALLDATALOAD, none) ∧
    decode bytecode (UInt256.ofNat 715) = some (.Push .PUSH1, some (UInt256.ofNat 228, 1)) ∧
    decode bytecode (UInt256.ofNat 717) = some (.CALLDATALOAD, none) := by
  native_decide

/-! ## (3b) `checkField`: the public input is read once more, before everything else -/

/-- `verifyProof` reads `input` from calldata offset 260 a *second* time
(see `decodes_public_input`), right after `JUMPDEST verifyLbl`, before any
other computation: `PUSH32 r; PUSH2 260; CALLDATALOAD` at PCs 22/55/58. This
is the start of the `checkField` guard — see `Program.lean`'s docstring on
why a non-canonical `input ≥ r` must be rejected before it ever reaches
`BN_MUL`. (Split from `checkfield_compares_and_branches` below: an 7-conjunct
`native_decide` here failed to synthesize `Decidable`, the same issue
`decodes_proof_b` hit — see its split into `_x`/`_y`.) -/
theorem checkfield_reads_input_and_r :
    decode bytecode (UInt256.ofNat 22) = some (.Push .PUSH32, some (r, 32)) ∧
    decode bytecode (UInt256.ofNat 55) = some (.Push .PUSH2, some (UInt256.ofNat 260, 2)) ∧
    decode bytecode (UInt256.ofNat 58) = some (.CALLDATALOAD, none) := by
  native_decide

/-- ... then compares (`LT; ISZERO`) and branches to `revertLbl` on failure:
`LT; ISZERO; PUSH2 revertLbl; JUMPI` at PCs 59/60/61/64. -/
theorem checkfield_compares_and_branches :
    decode bytecode (UInt256.ofNat 59) = some (.LT, none) ∧
    decode bytecode (UInt256.ofNat 60) = some (.ISZERO, none) ∧
    decode bytecode (UInt256.ofNat 61) = some (.Push .PUSH2, some (revertLbl, 2)) ∧
    decode bytecode (UInt256.ofNat 64) = some (.JUMPI, none) := by
  native_decide

/-! ## (4) Exactly three external calls, to the three precompiles claimed -/

/-- There are exactly three `CALL`s in the program, at PCs 157, 249, 886.
Stated over `linearScan` — see its docstring for why a raw-offset scan
(safe for `Demos/Weth`, false here) won't do. -/
theorem does_three_external_calls :
    (linearScan 900 0).filterMap (fun p => match p.2 with | .CALL => some p.1 | _ => none)
      = [157, 249, 886] := by
  native_decide

/-- The first `CALL` (PC 157) targets address `7` (`BN_MUL`) — the
immediately preceding `PUSH1` (PC 154) supplies the `to` argument. -/
theorem first_call_targets_bn_mul :
    decode bytecode (UInt256.ofNat 154) = some (.Push .PUSH1, some (UInt256.ofNat 7, 1)) ∧
    decode bytecode (UInt256.ofNat 157) = some (.CALL, none) := by
  native_decide

/-- The second `CALL` (PC 249) targets address `6` (`BN_ADD`). -/
theorem second_call_targets_bn_add :
    decode bytecode (UInt256.ofNat 246) = some (.Push .PUSH1, some (UInt256.ofNat 6, 1)) ∧
    decode bytecode (UInt256.ofNat 249) = some (.CALL, none) := by
  native_decide

/-- The third `CALL` (PC 886) targets address `8` (`SNARKV`). -/
theorem third_call_targets_snarkv :
    decode bytecode (UInt256.ofNat 883) = some (.Push .PUSH1, some (UInt256.ofNat 8, 1)) ∧
    decode bytecode (UInt256.ofNat 886) = some (.CALL, none) := by
  native_decide

end EvmSmith.Groth16
