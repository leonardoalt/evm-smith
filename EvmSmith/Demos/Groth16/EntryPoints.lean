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

/-- **No instruction in this entire 861-byte program is `SSTORE`.** Storage
cannot change no matter which branch executes or what the precompiles
return — the strongest guarantee here, and the only one that needs no
`SnarkvCorrect`/`BnMulSucceeds`/`BnAddSucceeds` assumption. -/
theorem program_has_no_sstore :
    ∀ pc ∈ List.range' 0 861, opAt pc ≠ some .SSTORE := by
  native_decide

/-! ## (3) ABI decode: the nine proof/input words -/

/-- `verifyProof` decodes its single public input from calldata offset 260
(`PUSH2 260; CALLDATALOAD` at PCs 94/97) — i.e. the tenth word of calldata
(selector + 9 preceding proof words), as the one-public-input ABI layout
demands. -/
theorem decodes_public_input :
    decode bytecode (UInt256.ofNat 94) = some (.Push .PUSH2, some (UInt256.ofNat 260, 2)) ∧
    decode bytecode (UInt256.ofNat 97) = some (.CALLDATALOAD, none) := by
  native_decide

/-- `verifyProof` decodes `proof.A` from calldata offsets 4 and 36. -/
theorem decodes_proof_a :
    decode bytecode (UInt256.ofNat 212) = some (.Push .PUSH1, some (UInt256.ofNat 4, 1)) ∧
    decode bytecode (UInt256.ofNat 214) = some (.CALLDATALOAD, none) ∧
    decode bytecode (UInt256.ofNat 219) = some (.Push .PUSH1, some (UInt256.ofNat 36, 1)) ∧
    decode bytecode (UInt256.ofNat 221) = some (.CALLDATALOAD, none) := by
  native_decide

/-- `verifyProof` decodes `proof.B`'s `x` words (`x.c1` at calldata offset
68, `x.c0` at offset 100) — the EIP-197 `(c1, c0)` ordering. -/
theorem decodes_proof_b_x :
    decode bytecode (UInt256.ofNat 267) = some (.Push .PUSH1, some (UInt256.ofNat 68, 1)) ∧
    decode bytecode (UInt256.ofNat 269) = some (.CALLDATALOAD, none) ∧
    decode bytecode (UInt256.ofNat 274) = some (.Push .PUSH1, some (UInt256.ofNat 100, 1)) ∧
    decode bytecode (UInt256.ofNat 276) = some (.CALLDATALOAD, none) := by
  native_decide

/-- `verifyProof` decodes `proof.B`'s `y` words (`y.c1` at calldata offset
132, `y.c0` at offset 164). -/
theorem decodes_proof_b_y :
    decode bytecode (UInt256.ofNat 281) = some (.Push .PUSH1, some (UInt256.ofNat 132, 1)) ∧
    decode bytecode (UInt256.ofNat 283) = some (.CALLDATALOAD, none) ∧
    decode bytecode (UInt256.ofNat 288) = some (.Push .PUSH1, some (UInt256.ofNat 164, 1)) ∧
    decode bytecode (UInt256.ofNat 290) = some (.CALLDATALOAD, none) := by
  native_decide

/-- `verifyProof` decodes `proof.C` from calldata offsets 196 and 228. -/
theorem decodes_proof_c :
    decode bytecode (UInt256.ofNat 665) = some (.Push .PUSH1, some (UInt256.ofNat 196, 1)) ∧
    decode bytecode (UInt256.ofNat 667) = some (.CALLDATALOAD, none) ∧
    decode bytecode (UInt256.ofNat 672) = some (.Push .PUSH1, some (UInt256.ofNat 228, 1)) ∧
    decode bytecode (UInt256.ofNat 674) = some (.CALLDATALOAD, none) := by
  native_decide

/-! ## (4) Exactly three external calls, to the three precompiles claimed -/

/-- There are exactly three `CALL`s in the program, at PCs 114, 206, 843. -/
theorem does_three_external_calls :
    (List.range' 0 861).filter (fun pc => decide (opAt pc = some .CALL)) = [114, 206, 843] := by
  native_decide

/-- The first `CALL` (PC 114) targets address `7` (`BN_MUL`) — the
immediately preceding `PUSH1` (PC 111) supplies the `to` argument. -/
theorem first_call_targets_bn_mul :
    decode bytecode (UInt256.ofNat 111) = some (.Push .PUSH1, some (UInt256.ofNat 7, 1)) ∧
    decode bytecode (UInt256.ofNat 114) = some (.CALL, none) := by
  native_decide

/-- The second `CALL` (PC 206) targets address `6` (`BN_ADD`). -/
theorem second_call_targets_bn_add :
    decode bytecode (UInt256.ofNat 203) = some (.Push .PUSH1, some (UInt256.ofNat 6, 1)) ∧
    decode bytecode (UInt256.ofNat 206) = some (.CALL, none) := by
  native_decide

/-- The third `CALL` (PC 843) targets address `8` (`SNARKV`). -/
theorem third_call_targets_snarkv :
    decode bytecode (UInt256.ofNat 840) = some (.Push .PUSH1, some (UInt256.ofNat 8, 1)) ∧
    decode bytecode (UInt256.ofNat 843) = some (.CALL, none) := by
  native_decide

end EvmSmith.Groth16
