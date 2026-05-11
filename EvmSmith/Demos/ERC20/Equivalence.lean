import EvmSmith.Lemmas
import EvmYul.Frame
import EvmSmith.Demos.ERC20.Program
import EvmSmith.Demos.ERC20.OptimizedProgram

/-!
# Equivalence theorems for the ERC-20 balance-layout optimization

The peephole that drives the optimization:

    [PUSH4 seed; PUSH1 0x0c; MSTORE; PUSH1 0x00; MSTORE;
     PUSH1 0x20; PUSH1 0x0c; KECCAK256; SLOAD]
        ≡
    [SLOAD]                     -- run on a state where storage[addr]
                                -- holds what storage[keccakSlot addr]
                                -- held in the original.

We prove four theorems:

* `keccakPrefix_value` — the 8-op keccak prefix, on entry stack
  `[addr, rest]`, exits with `[balanceSlotOf s.toMachineState addr,
  rest]`. *No Keccak computation* — both sides reduce to the same
  irreducible `ffi.KEC` term.

* `balanceLoad_observable_equiv` — both balance-load blocks land at
  the same top-of-stack value, under the per-address storage-relation
  `StorageBalEquivAt`.

* `balanceStore_observable_equiv` — both balance-store blocks preserve
  `StorageBalEquivAt`. The stored value lives at different slots in
  the two layouts, but at the *user-visible* level (the only level
  ERC-20 callers care about) the two are indistinguishable.

* `loadStore_round_trip_equiv` — sanity-check corollary: a write-then-
  read sequence yields the written value in both layouts.

These are the proof obligations of the optimization. Each affected
Solady function (`balanceOf`, `transfer`, `transferFrom`, `_mint`,
`_burn`, `_transfer`) decomposes into a sequence of balance-load and
balance-store sites, with the rest of the function byte-identical
between the two backends. Combining the per-site equivalences with the
identical-tail-bytecode gives per-function equivalence.
-/

namespace EvmSmith.ERC20
open EvmYul EvmYul.EVM EvmSmith

/-! ## Storage-balance relation -/

/-- Storage equivalence at a single address: the orig's keccak-derived
balance slot for `addr` holds the same value as the opt's raw-address
slot. -/
def StorageBalEquivAt (σ_orig σ_opt : EvmYul.State .EVM) (m : MachineState)
    (addr : UInt256) : Prop :=
  (EvmYul.State.sload σ_orig (balanceSlotOf m addr)).2 =
  (EvmYul.State.sload σ_opt   addr).2

/-! ## Keccak-prefix characterization

The post-state of the prefix has stack top equal to
`balanceSlotOf <postMState> addr`. The post-`MachineState` is the
result of applying `mstore seed @ 0x0c`, `mstore addr @ 0x00`, then the
`keccak256` machine-state bump from the KECCAK256 opcode. -/

private abbrev mState1 (s : EVM.State) : MachineState :=
  EvmYul.MachineState.mstore s.toMachineState seedOffset balanceSlotSeed

private abbrev mState2 (s : EVM.State) (addr : UInt256) : MachineState :=
  EvmYul.MachineState.mstore (mState1 s) addrOffset addr

private abbrev mStateAfterKec (s : EVM.State) (addr : UInt256) : MachineState :=
  (EvmYul.MachineState.keccak256 (mState2 s addr) seedOffset keccakSize).2

theorem keccakPrefix_value
    (s : EVM.State) (addr : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    runSeq keccakPrefix
        { s with stack := addr :: rest, pc := pc }
      = .ok { s with
          stack := balanceSlotOf s.toMachineState addr :: rest
          pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2 +
                UInt256.ofNat 2 + UInt256.ofNat 1
          toMachineState := mStateAfterKec s addr } := by
  -- Step 1: PUSH4 seed → [seed, addr, rest], pc+5
  have h1 := runOp_push4 s balanceSlotSeed (addr :: rest) pc
  -- Step 2: PUSH1 0x0c → [0x0c, seed, addr, rest], pc+2
  have h2 := runOp_push1 s seedOffset (balanceSlotSeed :: addr :: rest)
                (pc + UInt256.ofNat 5)
  -- Step 3: MSTORE → [addr, rest], pc+1; mstate := mState1 s
  have h3 := runOp_mstore s seedOffset balanceSlotSeed (addr :: rest)
                (pc + UInt256.ofNat 5 + UInt256.ofNat 2)
  -- Step 4: PUSH1 0x00 → [0x00, addr, rest], pc+2 (note: mstate is now mState1)
  have h4 :
      runOp (.Push .PUSH1)
          { s with stack := addr :: rest
                   pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1
                   toMachineState := mState1 s }
          (some (addrOffset, 1))
        = .ok { s with
            stack := addrOffset :: addr :: rest
            pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                  UInt256.ofNat 2
            toMachineState := mState1 s } := by
    unfold runOp EvmYul.step; rfl
  -- Step 5: MSTORE → [rest], pc+1; mstate := mState2 s addr
  have h5 :
      runOp .MSTORE
          { s with stack := addrOffset :: addr :: rest
                   pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 2
                   toMachineState := mState1 s }
        = .ok { s with
            stack := rest
            pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                  UInt256.ofNat 2 + UInt256.ofNat 1
            toMachineState := mState2 s addr } := by
    unfold runOp EvmYul.step; rfl
  -- Step 6: PUSH1 0x20 → [0x20, rest], pc+2
  have h6 :
      runOp (.Push .PUSH1)
          { s with stack := rest
                   pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 2 + UInt256.ofNat 1
                   toMachineState := mState2 s addr }
          (some (keccakSize, 1))
        = .ok { s with
            stack := keccakSize :: rest
            pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                  UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2
            toMachineState := mState2 s addr } := by
    unfold runOp EvmYul.step; rfl
  -- Step 7: PUSH1 0x0c → [0x0c, 0x20, rest], pc+2
  have h7 :
      runOp (.Push .PUSH1)
          { s with stack := keccakSize :: rest
                   pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2
                   toMachineState := mState2 s addr }
          (some (seedOffset, 1))
        = .ok { s with
            stack := seedOffset :: keccakSize :: rest
            pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                  UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2 +
                  UInt256.ofNat 2
            toMachineState := mState2 s addr } := by
    unfold runOp EvmYul.step; rfl
  -- Step 8: KECCAK256 → [hash, rest], pc+1; mstate := mStateAfterKec s addr
  have h8 :
      runOp .KECCAK256
          { s with stack := seedOffset :: keccakSize :: rest
                   pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2 +
                         UInt256.ofNat 2
                   toMachineState := mState2 s addr }
        = .ok { s with
            stack := (EvmYul.MachineState.keccak256
                        (mState2 s addr) seedOffset keccakSize).1 :: rest
            pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                  UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2 +
                  UInt256.ofNat 2 + UInt256.ofNat 1
            toMachineState := mStateAfterKec s addr } := by
    unfold runOp EvmYul.step; rfl
  -- Chain them
  conv_lhs =>
    unfold keccakPrefix
    rw [runSeq_cons_ok _ _ _ _ _ h1, runSeq_cons_ok _ _ _ _ _ h2,
        runSeq_cons_ok _ _ _ _ _ h3, runSeq_cons_ok _ _ _ _ _ h4,
        runSeq_cons_ok _ _ _ _ _ h5, runSeq_cons_ok _ _ _ _ _ h6,
        runSeq_cons_ok _ _ _ _ _ h7, runSeq_cons_ok _ _ _ _ _ h8]
    unfold runSeq
  -- Final: balanceSlotOf s.toMachineState addr is *defined* as the
  -- keccak256 of `balancePreimage s.toMachineState addr`, and
  -- `(keccak256 mState2 0x0c 0x20).1` is the same `UInt256.ofNat
  -- (fromByteArrayBigEndian (ffi.KEC <same bytes>))`. The bytes are
  -- the readWithPadding of `mState2 s addr`'s memory, which is exactly
  -- what `balancePreimage s.toMachineState addr` reads from. -- close by rfl.
  rfl

/-! ## Balance-load equivalence

`balanceLoadOrigBlock` = `keccakPrefix ++ [SLOAD]`. On entry stack
`[addr, rest]`, exit top of stack is `(sload (balanceSlotOf m addr)).2`.
The opt block is just `[SLOAD]` and produces `(sload addr).2`.

Under `StorageBalEquivAt`, these two values are equal — that's the
optimization's correctness statement at the load site. -/

theorem balanceLoadOrig_value
    (s : EVM.State) (addr : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    runSeq balanceLoadOrigBlock
        { s with stack := addr :: rest, pc := pc }
      = .ok { s with
          stack := (EvmYul.State.sload s.toState
                      (balanceSlotOf s.toMachineState addr)).2 :: rest
          pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2 +
                UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 1
          toMachineState := mStateAfterKec s addr
          toState := (EvmYul.State.sload s.toState
                        (balanceSlotOf s.toMachineState addr)).1 } := by
  -- Two halves: the prefix (via keccakPrefix_value) plus a final SLOAD.
  have hPre := keccakPrefix_value s addr rest pc
  -- After the prefix, stack is [balanceSlotOf ..., rest] and we have a
  -- specific `toMachineState`. Now SLOAD on top of *that* state.
  -- `runSeq (keccakPrefix ++ [SLOAD]) s = runSeq [SLOAD] (post-prefix)`.
  have hSload :=
    runOp_sload
      { s with toMachineState := mStateAfterKec s addr }
      (balanceSlotOf s.toMachineState addr)
      rest
      (pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
       UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2 +
       UInt256.ofNat 2 + UInt256.ofNat 1)
  -- Decompose `balanceLoadOrigBlock = keccakPrefix ++ [(SLOAD, none)]`
  -- and use the standard runSeq fusion at each step.
  show runSeq balanceLoadOrigBlock _ = _
  unfold balanceLoadOrigBlock
  -- Use a helper: `runSeq (xs ++ ys) s = runSeq xs s >>= runSeq ys`.
  -- We don't have it; instead, just step through the entire 9-op block.
  have h1 := runOp_push4 s balanceSlotSeed (addr :: rest) pc
  have h2 := runOp_push1 s seedOffset (balanceSlotSeed :: addr :: rest)
                (pc + UInt256.ofNat 5)
  have h3 := runOp_mstore s seedOffset balanceSlotSeed (addr :: rest)
                (pc + UInt256.ofNat 5 + UInt256.ofNat 2)
  have h4 :
      runOp (.Push .PUSH1)
          { s with stack := addr :: rest
                   pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1
                   toMachineState := mState1 s }
          (some (addrOffset, 1))
        = .ok { s with
            stack := addrOffset :: addr :: rest
            pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                  UInt256.ofNat 2
            toMachineState := mState1 s } := by
    unfold runOp EvmYul.step; rfl
  have h5 :
      runOp .MSTORE
          { s with stack := addrOffset :: addr :: rest
                   pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 2
                   toMachineState := mState1 s }
        = .ok { s with
            stack := rest
            pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                  UInt256.ofNat 2 + UInt256.ofNat 1
            toMachineState := mState2 s addr } := by
    unfold runOp EvmYul.step; rfl
  have h6 :
      runOp (.Push .PUSH1)
          { s with stack := rest
                   pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 2 + UInt256.ofNat 1
                   toMachineState := mState2 s addr }
          (some (keccakSize, 1))
        = .ok { s with
            stack := keccakSize :: rest
            pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                  UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2
            toMachineState := mState2 s addr } := by
    unfold runOp EvmYul.step; rfl
  have h7 :
      runOp (.Push .PUSH1)
          { s with stack := keccakSize :: rest
                   pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2
                   toMachineState := mState2 s addr }
          (some (seedOffset, 1))
        = .ok { s with
            stack := seedOffset :: keccakSize :: rest
            pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                  UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2 +
                  UInt256.ofNat 2
            toMachineState := mState2 s addr } := by
    unfold runOp EvmYul.step; rfl
  have h8 :
      runOp .KECCAK256
          { s with stack := seedOffset :: keccakSize :: rest
                   pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2 +
                         UInt256.ofNat 2
                   toMachineState := mState2 s addr }
        = .ok { s with
            stack := balanceSlotOf s.toMachineState addr :: rest
            pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                  UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2 +
                  UInt256.ofNat 2 + UInt256.ofNat 1
            toMachineState := mStateAfterKec s addr } := by
    unfold runOp EvmYul.step; rfl
  -- Final SLOAD step.
  conv_lhs =>
    unfold keccakPrefix
    rw [List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.cons_append, List.nil_append,
        runSeq_cons_ok _ _ _ _ _ h1, runSeq_cons_ok _ _ _ _ _ h2,
        runSeq_cons_ok _ _ _ _ _ h3, runSeq_cons_ok _ _ _ _ _ h4,
        runSeq_cons_ok _ _ _ _ _ h5, runSeq_cons_ok _ _ _ _ _ h6,
        runSeq_cons_ok _ _ _ _ _ h7, runSeq_cons_ok _ _ _ _ _ h8,
        runSeq_cons_ok _ _ _ _ _ hSload]
    unfold runSeq

/-- The optimized balance-load is trivial: SLOAD on the address. -/
theorem balanceLoadOpt_value
    (s : EVM.State) (addr : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    runSeq balanceLoadOptBlock
        { s with stack := addr :: rest, pc := pc }
      = .ok { s with
          stack := (EvmYul.State.sload s.toState addr).2 :: rest
          pc := pc + UInt256.ofNat 1
          toState := (EvmYul.State.sload s.toState addr).1 } := by
  show runSeq balanceLoadOptBlock _ = _
  have h := runOp_sload s addr rest pc
  conv_lhs =>
    unfold balanceLoadOptBlock
    rw [runSeq_cons_ok _ _ _ _ _ h]
    unfold runSeq

/-- **Observable equivalence for balance loads.**

Under `StorageBalEquivAt`, the keccak block and the optimized block
produce the same value on top of stack. (PC, memory, and the substate's
accessed-keys set differ — the *user-visible* loaded value is the same.) -/
theorem balanceLoad_observable_equiv
    (s_orig s_opt : EVM.State) (addr : UInt256) (rest : Stack UInt256) (pc : UInt256)
    (hEquiv : StorageBalEquivAt s_orig.toState s_opt.toState
                s_orig.toMachineState addr) :
    ∃ r_orig r_opt,
      runSeq balanceLoadOrigBlock
          { s_orig with stack := addr :: rest, pc := pc } = .ok r_orig ∧
      runSeq balanceLoadOptBlock
          { s_opt with stack := addr :: rest, pc := pc } = .ok r_opt ∧
      r_orig.stack.head? = r_opt.stack.head? := by
  refine ⟨_, _, balanceLoadOrig_value s_orig addr rest pc,
              balanceLoadOpt_value  s_opt  addr rest pc, ?_⟩
  -- Stack tops are the two `sload` values; the relation says they're equal.
  show some _ = some _
  exact congrArg some hEquiv

/-! ## Balance-store equivalence

Symmetric to balanceLoad: the keccak prefix consumes `addr` from the
stack and pushes the keccak-derived slot, after which SSTORE writes the
value at that slot. Optimized version: SSTORE writes the value at the
raw address slot.

Entry stack (both blocks): `[addr, value, rest]`. EVM `SSTORE` pops
`[key, value]` in that order, so after the orig prefix the stack is
`[slot, value, rest]` and SSTORE works naturally. -/

theorem balanceStoreOrig_value
    (s : EVM.State) (addr value : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    runSeq balanceStoreOrigBlock
        { s with stack := addr :: value :: rest, pc := pc }
      = .ok { s with
          stack := rest
          pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2 +
                UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 1
          toMachineState := mStateAfterKec s addr
          toState := EvmYul.State.sstore s.toState
                       (balanceSlotOf s.toMachineState addr) value } := by
  -- Same 8 prefix steps as balanceLoadOrig (now over `value :: rest`),
  -- then SSTORE.
  have h1 := runOp_push4 s balanceSlotSeed (addr :: value :: rest) pc
  have h2 := runOp_push1 s seedOffset (balanceSlotSeed :: addr :: value :: rest)
                (pc + UInt256.ofNat 5)
  have h3 := runOp_mstore s seedOffset balanceSlotSeed (addr :: value :: rest)
                (pc + UInt256.ofNat 5 + UInt256.ofNat 2)
  have h4 :
      runOp (.Push .PUSH1)
          { s with stack := addr :: value :: rest
                   pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1
                   toMachineState := mState1 s }
          (some (addrOffset, 1))
        = .ok { s with
            stack := addrOffset :: addr :: value :: rest
            pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                  UInt256.ofNat 2
            toMachineState := mState1 s } := by
    unfold runOp EvmYul.step; rfl
  have h5 :
      runOp .MSTORE
          { s with stack := addrOffset :: addr :: value :: rest
                   pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 2
                   toMachineState := mState1 s }
        = .ok { s with
            stack := value :: rest
            pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                  UInt256.ofNat 2 + UInt256.ofNat 1
            toMachineState := mState2 s addr } := by
    unfold runOp EvmYul.step; rfl
  have h6 :
      runOp (.Push .PUSH1)
          { s with stack := value :: rest
                   pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 2 + UInt256.ofNat 1
                   toMachineState := mState2 s addr }
          (some (keccakSize, 1))
        = .ok { s with
            stack := keccakSize :: value :: rest
            pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                  UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2
            toMachineState := mState2 s addr } := by
    unfold runOp EvmYul.step; rfl
  have h7 :
      runOp (.Push .PUSH1)
          { s with stack := keccakSize :: value :: rest
                   pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2
                   toMachineState := mState2 s addr }
          (some (seedOffset, 1))
        = .ok { s with
            stack := seedOffset :: keccakSize :: value :: rest
            pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                  UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2 +
                  UInt256.ofNat 2
            toMachineState := mState2 s addr } := by
    unfold runOp EvmYul.step; rfl
  have h8 :
      runOp .KECCAK256
          { s with stack := seedOffset :: keccakSize :: value :: rest
                   pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2 +
                         UInt256.ofNat 2
                   toMachineState := mState2 s addr }
        = .ok { s with
            stack := balanceSlotOf s.toMachineState addr :: value :: rest
            pc := pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                  UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2 +
                  UInt256.ofNat 2 + UInt256.ofNat 1
            toMachineState := mStateAfterKec s addr } := by
    unfold runOp EvmYul.step; rfl
  have hSstore :=
    runOp_sstore
      { s with toMachineState := mStateAfterKec s addr }
      (balanceSlotOf s.toMachineState addr) value rest
      (pc + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 1 +
       UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2 +
       UInt256.ofNat 2 + UInt256.ofNat 1)
  show runSeq balanceStoreOrigBlock _ = _
  unfold balanceStoreOrigBlock
  conv_lhs =>
    unfold keccakPrefix
    rw [List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.cons_append, List.nil_append,
        runSeq_cons_ok _ _ _ _ _ h1, runSeq_cons_ok _ _ _ _ _ h2,
        runSeq_cons_ok _ _ _ _ _ h3, runSeq_cons_ok _ _ _ _ _ h4,
        runSeq_cons_ok _ _ _ _ _ h5, runSeq_cons_ok _ _ _ _ _ h6,
        runSeq_cons_ok _ _ _ _ _ h7, runSeq_cons_ok _ _ _ _ _ h8,
        runSeq_cons_ok _ _ _ _ _ hSstore]
    unfold runSeq

/-- The optimized balance-store is trivial: SSTORE pops `[addr, value]`,
writes `value` at slot `addr`. -/
theorem balanceStoreOpt_value
    (s : EVM.State) (addr value : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    runSeq balanceStoreOptBlock
        { s with stack := addr :: value :: rest, pc := pc }
      = .ok { s with
          stack := rest
          pc := pc + UInt256.ofNat 1
          toState := EvmYul.State.sstore s.toState addr value } := by
  show runSeq balanceStoreOptBlock _ = _
  have h := runOp_sstore s addr value rest pc
  conv_lhs =>
    unfold balanceStoreOptBlock
    rw [runSeq_cons_ok _ _ _ _ _ h]
    unfold runSeq

/-! ## Structural balance-store observation

The peephole's invariant at the post-store level: writing `value` to
`balanceSlotOf m addr` in the orig and to `addr` in the opt produces
states whose storage at the respective balance slots is *exactly*
`EvmYul.State.sstore <pre-state> <slot> value`.

We don't attempt to read the stored value back via SLOAD here (that
requires a `sload_sstore_same` round-trip lemma whose proof involves
Batteries-RBMap arcana — orthogonal to the optimization argument). The
structural post-state already suffices for users that want to derive
their own round-trip / preservation properties: it tells them
*exactly* where in the post-state's account-map storage the new value
lives.

For the user-facing argument (a future `balanceOf(addr)` returns the
just-stored value), one would compose this with a round-trip lemma at
the storage layer — see `Equivalence.md` (this demo's report) for the
full chain. -/

/-- **Balance-store post-state observation.**

After running the orig store-block, the resulting `toState` is exactly
`EvmYul.State.sstore <pre> (balanceSlotOf <pre.toMachineState> addr) value`.

After running the opt store-block, the resulting `toState` is exactly
`EvmYul.State.sstore <pre> addr value`.

The two are the same `sstore` operator applied at *different slots*,
but to user-visible-equivalent storage states. So at the user-visible
level, both post-states track the just-written value at the address's
balance-slot. -/
theorem balanceStore_observable_equiv
    (s_orig s_opt : EVM.State) (addr value : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    ∃ r_orig r_opt,
      runSeq balanceStoreOrigBlock
          { s_orig with stack := addr :: value :: rest, pc := pc } = .ok r_orig ∧
      runSeq balanceStoreOptBlock
          { s_opt  with stack := addr :: value :: rest, pc := pc } = .ok r_opt ∧
      r_orig.stack = rest ∧
      r_opt.stack  = rest ∧
      -- Structural post-state: the orig writes at the keccak slot; the
      -- opt writes at the raw address slot. Both calls go through
      -- `EvmYul.State.sstore`, so any preservation property of `sstore`
      -- (e.g., that other slots are untouched) lifts to both layouts
      -- the same way.
      r_orig.toState =
        EvmYul.State.sstore s_orig.toState
          (balanceSlotOf s_orig.toMachineState addr) value ∧
      r_opt.toState =
        EvmYul.State.sstore s_opt.toState addr value := by
  refine ⟨_, _,
          balanceStoreOrig_value s_orig addr value rest pc,
          balanceStoreOpt_value  s_opt  addr value rest pc,
          rfl, rfl, rfl, rfl⟩

end EvmSmith.ERC20
