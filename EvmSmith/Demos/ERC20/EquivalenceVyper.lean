import EvmSmith.Lemmas
import EvmSmith.Demos.ERC20.ProgramVyper
import EvmSmith.Demos.ERC20.OptimizedProgramVyper

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

/-!
# Equivalence theorems for the Vyper / Snekmate balance-slot peephole

The patcher replaces every Vyper-emitted balance-slot computation:

    PUSH1 0x02; PUSH1 P; MLOAD; PUSH1 0x20; MSTORE;
    PUSH0; MSTORE; PUSH1 0x40; PUSH0; KECCAK256

with

    JUMPDEST × 10; PUSH1 P; MLOAD; NOT

(length-preserving, 15 bytes both ways). After the prefix, an `SLOAD`
or `SSTORE` consumes the slot value.

We prove:

* `vyperOptPrefix_value` — the 13-op opt prefix exits with
  `[UInt256.lnot addr :: rest]` where `addr` is what `MLOAD` reads
  from `mem[keyMemOffset]`. All 13 ops are simple (no memory writes,
  no keccak), so the proof is mechanical.

* `vyperBalanceLoadOpt_value` — extends the above with SLOAD: the
  loaded value is `(sload σ (~addr)).snd`.

* `vyperBalanceLoad_relational_equiv` — under the per-address storage
  relation, the orig keccak block and the opt NOT block produce the
  same loaded value, *modulo a closure providing the orig-side
  characterization*. (We don't prove the orig-side characterization
  here — the 10-step keccak prefix's `rfl` chains time out on
  `whnf`/`isDefEq` in EVMYulLean's current shape; same issue as the
  "no closed-form sload-after-sstore round-trip" gap in the Solidity
  variant. The equivalence statement is parameterized so a consumer
  who has that orig-side characterization can plug it in.)

The `NOT(addr)` slot is what makes the optimization safe in the
Vyper setting: Vyper places its named state at low slots (owner at
1, totalSupply at 4, etc.), so using the raw address would collide
with these for small-address users. `NOT(addr)` maps every 160-bit
address to a slot with the high 96 bits all-one, avoiding every
named slot and (with overwhelming probability) every keccak slot too.
-/

namespace EvmSmith.ERC20Vyper
open EvmYul EvmYul.EVM EvmSmith

/-! ## Storage relation -/

/-- Per-address storage relation: the value stored at orig's `slot`
(whatever it is) equals the value stored at opt's `NOT(addr)`. -/
def VyperStorageBalEquivAtRel
    (σ_orig σ_opt : EvmYul.State .EVM) (slot addr : UInt256) : Prop :=
  (EvmYul.State.sload σ_orig slot).2 =
  (EvmYul.State.sload σ_opt (UInt256.lnot addr)).2

/-! ## Opt-prefix characterization

The 10 JUMPDESTs are pure no-ops (each just bumps PC by 1, no stack/
memory/storage effect). After them, `PUSH1 P; MLOAD` reads the address
from `mem[P]`; `NOT` complements it. End state: stack-top is
`UInt256.lnot (mload mem[P]).snd` (the bitwise complement of the
address). -/

private abbrev keyAddr (s : EVM.State) (keyMemOffset : UInt256) : UInt256 :=
  (EvmYul.MachineState.mload s.toMachineState keyMemOffset).1

private abbrev mAfterMLoad (s : EVM.State) (keyMemOffset : UInt256) : MachineState :=
  (EvmYul.MachineState.mload s.toMachineState keyMemOffset).2

theorem vyperOptPrefix_value
    (s : EVM.State) (keyMemOffset : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    runSeq (vyperOptPrefix keyMemOffset)
        { s with stack := rest, pc := pc }
      = .ok { s with
          stack := UInt256.lnot (keyAddr s keyMemOffset) :: rest
          pc := pc + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                UInt256.ofNat 1
          toMachineState := mAfterMLoad s keyMemOffset } := by
  let pc1 := pc + UInt256.ofNat 1
  let pc2 := pc1 + UInt256.ofNat 1
  let pc3 := pc2 + UInt256.ofNat 1
  let pc4 := pc3 + UInt256.ofNat 1
  let pc5 := pc4 + UInt256.ofNat 1
  let pc6 := pc5 + UInt256.ofNat 1
  let pc7 := pc6 + UInt256.ofNat 1
  let pc8 := pc7 + UInt256.ofNat 1
  let pc9 := pc8 + UInt256.ofNat 1
  let pc10 := pc9 + UInt256.ofNat 1
  have j1 := runOp_jumpdest { s with stack := rest, pc := pc }
  have j2 := runOp_jumpdest { s with stack := rest, pc := pc1 }
  have j3 := runOp_jumpdest { s with stack := rest, pc := pc2 }
  have j4 := runOp_jumpdest { s with stack := rest, pc := pc3 }
  have j5 := runOp_jumpdest { s with stack := rest, pc := pc4 }
  have j6 := runOp_jumpdest { s with stack := rest, pc := pc5 }
  have j7 := runOp_jumpdest { s with stack := rest, pc := pc6 }
  have j8 := runOp_jumpdest { s with stack := rest, pc := pc7 }
  have j9 := runOp_jumpdest { s with stack := rest, pc := pc8 }
  have j10 := runOp_jumpdest { s with stack := rest, pc := pc9 }
  have h11 := runOp_push1 s keyMemOffset rest pc10
  have h12 := runOp_mload s keyMemOffset rest (pc10 + UInt256.ofNat 2)
  have h13 := runOp_not
                { s with toMachineState := mAfterMLoad s keyMemOffset }
                (keyAddr s keyMemOffset) rest
                (pc10 + UInt256.ofNat 2 + UInt256.ofNat 1)
  conv_lhs =>
    unfold vyperOptPrefix
    rw [runSeq_cons_ok _ _ _ _ _ j1, runSeq_cons_ok _ _ _ _ _ j2,
        runSeq_cons_ok _ _ _ _ _ j3, runSeq_cons_ok _ _ _ _ _ j4,
        runSeq_cons_ok _ _ _ _ _ j5, runSeq_cons_ok _ _ _ _ _ j6,
        runSeq_cons_ok _ _ _ _ _ j7, runSeq_cons_ok _ _ _ _ _ j8,
        runSeq_cons_ok _ _ _ _ _ j9, runSeq_cons_ok _ _ _ _ _ j10,
        runSeq_cons_ok _ _ _ _ _ h11, runSeq_cons_ok _ _ _ _ _ h12,
        runSeq_cons_ok _ _ _ _ _ h13]
    unfold runSeq

/-! ## Opt balance-load -/

theorem vyperBalanceLoadOpt_value
    (s : EVM.State) (keyMemOffset : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    runSeq (vyperBalanceLoadOptBlock keyMemOffset)
        { s with stack := rest, pc := pc }
      = .ok { s with
          stack := (EvmYul.State.sload s.toState
                      (UInt256.lnot (keyAddr s keyMemOffset))).2 :: rest
          pc := pc + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                UInt256.ofNat 1 + UInt256.ofNat 1
          toMachineState := mAfterMLoad s keyMemOffset
          toState := (EvmYul.State.sload s.toState
                        (UInt256.lnot (keyAddr s keyMemOffset))).1 } := by
  set slotOpt := UInt256.lnot (keyAddr s keyMemOffset) with hSlotOpt
  have hSload :=
    runOp_sload
      { s with toMachineState := mAfterMLoad s keyMemOffset }
      slotOpt rest
      (pc + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
       UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
       UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
       UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
       UInt256.ofNat 1)
  show runSeq (vyperBalanceLoadOptBlock keyMemOffset) _ = _
  unfold vyperBalanceLoadOptBlock vyperOptPrefix
  conv_lhs =>
    rw [List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.nil_append]
  let pc1 := pc + UInt256.ofNat 1
  let pc2 := pc1 + UInt256.ofNat 1
  let pc3 := pc2 + UInt256.ofNat 1
  let pc4 := pc3 + UInt256.ofNat 1
  let pc5 := pc4 + UInt256.ofNat 1
  let pc6 := pc5 + UInt256.ofNat 1
  let pc7 := pc6 + UInt256.ofNat 1
  let pc8 := pc7 + UInt256.ofNat 1
  let pc9 := pc8 + UInt256.ofNat 1
  let pc10 := pc9 + UInt256.ofNat 1
  have j1 := runOp_jumpdest { s with stack := rest, pc := pc }
  have j2 := runOp_jumpdest { s with stack := rest, pc := pc1 }
  have j3 := runOp_jumpdest { s with stack := rest, pc := pc2 }
  have j4 := runOp_jumpdest { s with stack := rest, pc := pc3 }
  have j5 := runOp_jumpdest { s with stack := rest, pc := pc4 }
  have j6 := runOp_jumpdest { s with stack := rest, pc := pc5 }
  have j7 := runOp_jumpdest { s with stack := rest, pc := pc6 }
  have j8 := runOp_jumpdest { s with stack := rest, pc := pc7 }
  have j9 := runOp_jumpdest { s with stack := rest, pc := pc8 }
  have j10 := runOp_jumpdest { s with stack := rest, pc := pc9 }
  have h11 := runOp_push1 s keyMemOffset rest pc10
  have h12 := runOp_mload s keyMemOffset rest (pc10 + UInt256.ofNat 2)
  have h13 := runOp_not
                { s with toMachineState := mAfterMLoad s keyMemOffset }
                (keyAddr s keyMemOffset) rest
                (pc10 + UInt256.ofNat 2 + UInt256.ofNat 1)
  conv_lhs =>
    rw [runSeq_cons_ok _ _ _ _ _ j1, runSeq_cons_ok _ _ _ _ _ j2,
        runSeq_cons_ok _ _ _ _ _ j3, runSeq_cons_ok _ _ _ _ _ j4,
        runSeq_cons_ok _ _ _ _ _ j5, runSeq_cons_ok _ _ _ _ _ j6,
        runSeq_cons_ok _ _ _ _ _ j7, runSeq_cons_ok _ _ _ _ _ j8,
        runSeq_cons_ok _ _ _ _ _ j9, runSeq_cons_ok _ _ _ _ _ j10,
        runSeq_cons_ok _ _ _ _ _ h11, runSeq_cons_ok _ _ _ _ _ h12,
        runSeq_cons_ok _ _ _ _ _ h13, runSeq_cons_ok _ _ _ _ _ hSload]
    unfold runSeq

/-! ## Relational equivalence

Under the relation that the orig contract's `slot` for the address
holds the same balance as `~addr` on the opt side, *and* the orig
load-block ends with `slot` on top of the stack, the two loaded
values agree.

We don't unfold the orig keccak prefix in Lean (its 10-step proof
WHNF-times out in EVMYulLean — same root cause as the Solidity
variant's `sload(sstore σ k v) k = v` gap). The equivalence theorem
takes the orig-side characterization as a hypothesis so a consumer
who proves it (or simply assumes it) can derive the equivalence. -/

theorem vyperBalanceLoad_relational_equiv
    (s_orig s_opt : EVM.State) (keyMemOffset : UInt256) (rest : Stack UInt256) (pc : UInt256)
    (slot : UInt256)
    (hMemAgree :
      (EvmYul.MachineState.mload s_orig.toMachineState keyMemOffset).1 =
      (EvmYul.MachineState.mload s_opt.toMachineState  keyMemOffset).1)
    (hEquiv :
      VyperStorageBalEquivAtRel s_orig.toState s_opt.toState slot
        (keyAddr s_orig keyMemOffset))
    (hOrig :
      ∃ rO, runSeq (vyperBalanceLoadOrigBlock keyMemOffset)
              { s_orig with stack := rest, pc := pc } = .ok rO
        ∧ rO.stack.head? = some (EvmYul.State.sload s_orig.toState slot).2) :
    ∃ rO rP,
      runSeq (vyperBalanceLoadOrigBlock keyMemOffset)
        { s_orig with stack := rest, pc := pc } = .ok rO ∧
      runSeq (vyperBalanceLoadOptBlock keyMemOffset)
        { s_opt  with stack := rest, pc := pc } = .ok rP ∧
      rO.stack.head? = rP.stack.head? := by
  obtain ⟨rO, hO, hOtop⟩ := hOrig
  have hP := vyperBalanceLoadOpt_value s_opt keyMemOffset rest pc
  refine ⟨rO, _, hO, hP, ?_⟩
  -- Compute the opt-side head from `vyperBalanceLoadOpt_value`'s
  -- structural form. Then use hOtop and hEquiv to chain to the orig
  -- side via the storage relation.
  rw [hOtop]
  -- Goal: some (sload σ_orig slot).2 = head? (post-state with sload at NOT-slot)
  -- The post-state's stack-top from `vyperBalanceLoadOpt_value` is
  -- `(sload s_opt.toState (~keyAddr s_opt P)).2`.
  have hKey : keyAddr s_opt keyMemOffset = keyAddr s_orig keyMemOffset := hMemAgree.symm
  rw [show (EvmYul.State.sload s_orig.toState slot).2
        = (EvmYul.State.sload s_opt.toState
              (UInt256.lnot (keyAddr s_opt keyMemOffset))).2 from by
            rw [hKey]; exact hEquiv]
  rfl

end EvmSmith.ERC20Vyper
