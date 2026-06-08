import EvmYul.Frame
import EvmSmith.Demos.Weth.Program

/-!
# WETH — entry-point / dispatcher facts (bytecode-level)

This module proves *decidable* facts about WETH's actual decoded
bytecode that characterise its entry points (the function dispatcher),
its payability, and its ABI decode/encode shape. Each theorem is
discharged by `native_decide` over the real `bytecode` from
`Program.lean`, so it is a tight binding to the bytes: change any byte
and the proof breaks.

These are the "structural" half of the entry-point story — they say
*what instructions are where*. The complementary "behavioural" half
(running the dispatcher and pinning which branch a given selector
takes) is the functional router, which executes `EVM.step`.

The human-readable restatements live in `Spec.lean`.

## What the dispatcher looks like (PCs 0–31)

```
PUSH1 0; CALLDATALOAD; PUSH1 0xe0; SHR   -- selector = calldata[0:4]
DUP1; PUSH4 depositSelector;  EQ; PUSH2 32; JUMPI   -- → deposit
      PUSH4 withdrawSelector; EQ; PUSH2 42; JUMPI   -- → withdraw
PUSH1 0; PUSH1 0; REVERT                  -- no match → revert
```
-/

namespace EvmSmith.Weth

open EvmYul EvmYul.EVM

/-! ## Decoded-instruction accessor -/

/-- The opcode decoded at byte offset `pc` of WETH's runtime bytecode
(without its immediate argument), or `none` if `pc` is past the end. -/
def opAt (pc : Nat) : Option (Operation .EVM) :=
  (decode bytecode (UInt256.ofNat pc)).map (fun instr => instr.1)

/-- The 4-byte ABI function selector carried by `calldata`: the high 4
bytes of the first calldata word, i.e. `calldataload(0) >> 224`. This is
exactly what WETH's dispatcher computes at PCs 0–5
(`PUSH1 0; CALLDATALOAD; PUSH1 0xe0; SHR`). -/
def selectorOf (calldata : ByteArray) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (calldata.readBytes 0 32)) (UInt256.ofNat 0xe0)

/-! ## (1) Only two entry points -/

/-- The two entry-point selectors are distinct, so the dispatcher's two
branches are mutually exclusive. -/
theorem selectors_distinct : depositSelector ≠ withdrawSelector := by
  native_decide

/-- The dispatch prefix extracts the ABI selector in the standard way:
load `calldata[0:32]`, then shift right by `0xe0` (224 bits) to keep the
top 4 bytes. -/
theorem dispatch_extracts_selector :
    decode bytecode (UInt256.ofNat 0) = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) ∧
    decode bytecode (UInt256.ofNat 2) = some (.CALLDATALOAD, none) ∧
    decode bytecode (UInt256.ofNat 3) = some (.Push .PUSH1, some (UInt256.ofNat 0xe0, 1)) ∧
    decode bytecode (UInt256.ofNat 5) = some (.SHR, none) := by
  native_decide

/-- The dispatcher compares the selector against exactly the two
entry-point constants (deposit at PC 7/12, withdraw at PC 17/22). -/
theorem dispatch_compares_two_selectors :
    decode bytecode (UInt256.ofNat 7) = some (.Push .PUSH4, some (depositSelector, 4)) ∧
    decode bytecode (UInt256.ofNat 12) = some (.EQ, none) ∧
    decode bytecode (UInt256.ofNat 17) = some (.Push .PUSH4, some (withdrawSelector, 4)) ∧
    decode bytecode (UInt256.ofNat 22) = some (.EQ, none) := by
  native_decide

/-- **There is no third selector comparison.** Across the whole dispatch
region (PCs 0–30), the only `EQ` instructions are the two at PC 12 and
PC 22. Hence the bytecode can route to at most two functions. -/
theorem dispatch_has_exactly_two_selector_checks :
    (List.range' 0 31).filter (fun pc => decide (opAt pc = some .EQ)) = [12, 22] := by
  native_decide

/-- A selector matching neither entry point falls through to `REVERT`
(PC 31): there is no fallback / receive handler. -/
theorem dispatch_fallthrough_reverts :
    decode bytecode (UInt256.ofNat 31) = some (.REVERT, none) := by
  native_decide

/-! ## (2) Payability: deposit uses `msg.value`, withdraw ignores it -/

/-- `deposit` reads `msg.value` (`CALLVALUE` at PC 37) — it is payable
and credits the sent ETH. -/
theorem deposit_reads_callvalue : opAt 37 = some .CALLVALUE := by
  native_decide

/-- **`withdraw` never inspects `msg.value`.** No `CALLVALUE` instruction
appears anywhere in the withdraw region (PCs 42–79). The Solidity
`nonpayable` guard (`if (msg.value != 0) revert;`) is *absent*: a
`withdraw` call carrying ETH does not revert on that account — the ETH
is added to the contract's balance but credited to no one. -/
theorem withdraw_never_reads_callvalue :
    ∀ pc ∈ List.range' 42 38, opAt pc ≠ some .CALLVALUE := by
  native_decide

/-! ## (4) deposit is total (never reverts internally) -/

/-- The deposit block (PCs 32–41) contains no `REVERT` and no branch
(`JUMP`/`JUMPI`): it is straight-line code to `STOP`, so `deposit` never
reverts on its own (only out-of-gas or a failed entry value-transfer
could stop it). -/
theorem deposit_has_no_revert_or_branch :
    ∀ pc ∈ List.range' 32 10,
      opAt pc ≠ some .REVERT ∧ opAt pc ≠ some .JUMP ∧ opAt pc ≠ some .JUMPI := by
  native_decide

/-! ## (3) ABI decode / encode -/

/-- `withdraw` decodes its single `uint256` argument from calldata
offset 4 (`PUSH1 4; CALLDATALOAD` at PCs 43/45) — the standard ABI
layout `calldata[4:36]` for the first argument. -/
theorem withdraw_decodes_uint256_arg :
    decode bytecode (UInt256.ofNat 43) = some (.Push .PUSH1, some (UInt256.ofNat 4, 1)) ∧
    decode bytecode (UInt256.ofNat 45) = some (.CALLDATALOAD, none) := by
  native_decide

/-- `withdraw`'s outbound transfer is a **plain ETH send**: the four CALL
memory arguments (retSize, retOff, argsSize, argsOff) are all pushed as
`0` (PCs 61/63/65/67), so the call carries empty calldata and ignores
return data. -/
theorem withdraw_call_args_are_zero :
    ∀ pc ∈ [61, 63, 65, 67],
      decode bytecode (UInt256.ofNat pc) = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
  native_decide

/-- The outbound `CALL` of the withdraw block is at PC 72. -/
theorem withdraw_does_external_call :
    decode bytecode (UInt256.ofNat 72) = some (.CALL, none) := by
  native_decide

end EvmSmith.Weth
