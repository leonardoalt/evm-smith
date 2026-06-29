import EvmSmith.Demos.Groth16.Dispatch

/-!
# Groth16 — `checkField` actually rejects non-canonical public input

The one theorem in this module, `groth16_checkfield_rejects`, is a direct
answer to a question raised in review: does `checkField` *do* what its
docstring claims, or is that only checked empirically (the Foundry test
`test_Groth16_non_canonical_input_reverts`)? This proves it in Lean,
**no `sorry`** — unlike `groth16_verifies`, this doesn't need to reason
about the byte-encoding of any abstract `MSTORE`d value (`checkField` is
pure `PUSH`/`CALLDATALOAD`/`LT`/`ISZERO`/`JUMPI`, no memory access at all),
so it sits entirely on the provable side of the wall documented in
`SpecProofs.lean`.
-/

namespace EvmSmith.Groth16

open EvmYul EvmYul.EVM EvmYul.Frame Batteries EvmSmith.Spec

/-- **`checkField` rejects a non-canonical public input by reverting.**
From the call entry, if the public input is `≥ r` (the precondition
`groth16_verifies` excludes), then running to a halt always *reverts*
(`Reverts s s' o`) — not `RETURN`, not `STOP`. This is the complement of
`groth16_verifies`'s `publicInput < r` hypothesis: together they account for
both branches of `checkField`'s `JUMPI`. -/
theorem groth16_checkfield_rejects
    (s : EVM.State) (call : Calls .verifyProof s) (hge : r.toNat ≤ UInt256.toNat publicInput) :
    ensures Reverts s s' o := by
  obtain ⟨hcode, hpc0, hstk0, hsel⟩ := call
  intro s' o hHalt
  obtain ⟨callFuel, N, hrun⟩ := id hHalt
  -- step 0: PUSH1 0 @ 0
  have hd0 : decode s.executionEnv.code s.pc = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
    rw [hcode, hpc0]; exact dispatch_extracts_selector.1
  obtain _ | N := N
  · simp [evmRun] at hrun
  obtain ⟨s1, hst0, hrun⟩ := evmRun_succ_step callFuel N s _ _ _ hd0 (by decide) hrun
  have h0 : EVM.step (callFuel + 1) 0 (decode s.executionEnv.code s.pc) s = .ok s1 := by
    rw [hd0]; exact hst0
  obtain ⟨hp1, hs1, he1⟩ := step_PUSH1_shape s s1 callFuel 0 (UInt256.ofNat 0) hst0
  rw [hstk0] at hs1
  have hc1 : s1.executionEnv.code = bytecode := by rw [he1]; exact hcode
  have hpc1 : s1.pc = UInt256.ofNat 2 := by rw [hp1, hpc0]; decide
  -- step 1: CALLDATALOAD @ 2
  have hd1 : decode s1.executionEnv.code s1.pc = some (.CALLDATALOAD, none) := by
    rw [hc1, hpc1]; exact dispatch_extracts_selector.2.1
  obtain _ | N := N
  · simp [evmRun] at hrun
  obtain ⟨s2, hst1, hrun⟩ := evmRun_succ_step callFuel N s1 _ _ _ hd1 (by decide) hrun
  have h1 : EVM.step (callFuel + 1) 0 (decode s1.executionEnv.code s1.pc) s1 = .ok s2 := by
    rw [hd1]; exact hst1
  obtain ⟨hp2, hs2, he2⟩ := step_CALLDATALOAD_value s1 s2 callFuel 0 none (UInt256.ofNat 0) [] hs1 hst1
  have hc2 : s2.executionEnv.code = bytecode := by rw [he2]; exact hc1
  have hpc2 : s2.pc = UInt256.ofNat 3 := by rw [hp2, hpc1]; decide
  -- step 2: PUSH1 0xe0 @ 3
  have hd2 : decode s2.executionEnv.code s2.pc = some (.Push .PUSH1, some (UInt256.ofNat 0xe0, 1)) := by
    rw [hc2, hpc2]; exact dispatch_extracts_selector.2.2.1
  obtain _ | N := N
  · simp [evmRun] at hrun
  obtain ⟨s3, hst2, hrun⟩ := evmRun_succ_step callFuel N s2 _ _ _ hd2 (by decide) hrun
  have h2 : EVM.step (callFuel + 1) 0 (decode s2.executionEnv.code s2.pc) s2 = .ok s3 := by
    rw [hd2]; exact hst2
  obtain ⟨hp3, hs3, he3⟩ := step_PUSH1_shape s2 s3 callFuel 0 (UInt256.ofNat 0xe0) hst2
  rw [hs2] at hs3
  have hc3 : s3.executionEnv.code = bytecode := by rw [he3]; exact hc2
  have hpc3 : s3.pc = UInt256.ofNat 5 := by rw [hp3, hpc2]; decide
  -- step 3: SHR @ 5
  have hd3 : decode s3.executionEnv.code s3.pc = some (.SHR, none) := by
    rw [hc3, hpc3]; exact dispatch_extracts_selector.2.2.2
  obtain _ | N := N
  · simp [evmRun] at hrun
  obtain ⟨s4, hst3, hrun⟩ := evmRun_succ_step callFuel N s3 _ _ _ hd3 (by decide) hrun
  have h3 : EVM.step (callFuel + 1) 0 (decode s3.executionEnv.code s3.pc) s3 = .ok s4 := by
    rw [hd3]; exact hst3
  obtain ⟨hp4, hs4, he4⟩ :=
    step_SHR_value s3 s4 callFuel 0 none (UInt256.ofNat 0xe0)
      (EvmYul.State.calldataload s1.toState (UInt256.ofNat 0)) [] hs3 hst3
  have hc4 : s4.executionEnv.code = bytecode := by rw [he4]; exact hc3
  have hpc4 : s4.pc = UInt256.ofNat 6 := by rw [hp4, hpc3]; decide
  -- step 4: PUSH4 verifySelector @ 6
  have hd4 : decode s4.executionEnv.code s4.pc = some (.Push .PUSH4, some (verifySelector, 4)) := by
    rw [hc4, hpc4]; exact dispatch_compares_one_selector.1
  obtain _ | N := N
  · simp [evmRun] at hrun
  obtain ⟨s5, hst4, hrun⟩ := evmRun_succ_step callFuel N s4 _ _ _ hd4 (by decide) hrun
  have h4 : EVM.step (callFuel + 1) 0 (decode s4.executionEnv.code s4.pc) s4 = .ok s5 := by
    rw [hd4]; exact hst4
  obtain ⟨hp5, hs5, he5⟩ := step_PUSH_shape s4 s5 callFuel 0 .PUSH4 (by decide) verifySelector 4 hst4
  rw [hs4] at hs5
  have hc5 : s5.executionEnv.code = bytecode := by rw [he5]; exact hc4
  have hpc5 : s5.pc = UInt256.ofNat 11 := by rw [hp5, hpc4]; decide
  -- step 5: EQ @ 11
  have hd5 : decode s5.executionEnv.code s5.pc = some (.EQ, none) := by
    rw [hc5, hpc5]; exact dispatch_compares_one_selector.2
  obtain _ | N := N
  · simp [evmRun] at hrun
  obtain ⟨s6, hst5, hrun⟩ := evmRun_succ_step callFuel N s5 _ _ _ hd5 (by decide) hrun
  have h5 : EVM.step (callFuel + 1) 0 (decode s5.executionEnv.code s5.pc) s5 = .ok s6 := by
    rw [hd5]; exact hst5
  obtain ⟨hp6, hs6, he6⟩ :=
    step_EQ_value s5 s6 callFuel 0 none verifySelector
      (UInt256.shiftRight (EvmYul.State.calldataload s1.toState (UInt256.ofNat 0)) (UInt256.ofNat 0xe0))
      [] hs5 hst5
  have hc6 : s6.executionEnv.code = bytecode := by rw [he6]; exact hc5
  have hpc6 : s6.pc = UInt256.ofNat 12 := by rw [hp6, hpc5]; decide
  -- step 6: PUSH2 verifyLbl @ 12
  have hd6 : decode s6.executionEnv.code s6.pc = some (.Push .PUSH2, some (verifyLbl, 2)) := by
    rw [hc6, hpc6]; native_decide
  obtain _ | N := N
  · simp [evmRun] at hrun
  obtain ⟨s7, hst6, hrun⟩ := evmRun_succ_step callFuel N s6 _ _ _ hd6 (by decide) hrun
  have h6 : EVM.step (callFuel + 1) 0 (decode s6.executionEnv.code s6.pc) s6 = .ok s7 := by
    rw [hd6]; exact hst6
  obtain ⟨hp7, hs7, he7⟩ := step_PUSH_shape s6 s7 callFuel 0 .PUSH2 (by decide) verifyLbl 2 hst6
  rw [hs6] at hs7
  have hc7 : s7.executionEnv.code = bytecode := by rw [he7]; exact hc6
  have hpc7 : s7.pc = UInt256.ofNat 15 := by rw [hp7, hpc6]; decide
  -- step 7: JUMPI @ 15 — taken (selector matches `verifySelector`)
  have hd7 : decode s7.executionEnv.code s7.pc = some (.JUMPI, none) := by
    rw [hc7, hpc7]; native_decide
  obtain _ | N := N
  · simp [evmRun] at hrun
  obtain ⟨s8, hst7, hrun⟩ := evmRun_succ_step callFuel N s7 _ _ _ hd7 (by decide) hrun
  have h7 : EVM.step (callFuel + 1) 0 (decode s7.executionEnv.code s7.pc) s7 = .ok s8 := by
    rw [hd7]; exact hst7
  -- The combined dispatch fact, reusing `groth16_routes_verify` (which
  -- internally re-derives the value algebra from `h0`–`h7` alone, so it
  -- doesn't matter that the above only tracked pc/stack-shape, not values).
  obtain ⟨hs8pc, hs8stk, hs8ee⟩ :=
    groth16_routes_verify s s1 s2 s3 s4 s5 s6 s7 s8 callFuel 0 0 0 0 0 0 0 0
      hcode hpc0 hstk0 hsel h0 h1 h2 h3 h4 h5 h6 h7
  have hc8 : s8.executionEnv.code = bytecode := by rw [hs8ee]; exact hcode
  -- step 8: JUMPDEST @ 21 (verifyLbl)
  have hd8 : decode s8.executionEnv.code s8.pc = some (.JUMPDEST, none) := by
    rw [hc8, hs8pc]; native_decide
  obtain _ | N := N
  · simp [evmRun] at hrun
  obtain ⟨s9, hst8, hrun⟩ := evmRun_succ_step callFuel N s8 _ _ _ hd8 (by decide) hrun
  have h8 : EVM.step (callFuel + 1) 0 (decode s8.executionEnv.code s8.pc) s8 = .ok s9 := by
    rw [hd8]; exact hst8
  obtain ⟨hp9, hs9, he9⟩ := step_JUMPDEST_shape s8 s9 callFuel 0 none hst8
  rw [hs8stk] at hs9
  have hc9 : s9.executionEnv.code = bytecode := by rw [he9]; exact hc8
  have hpc9 : s9.pc = UInt256.ofNat 22 := by rw [hp9, hs8pc]; decide
  -- step 9: PUSH32 r @ 22 (checkField start)
  have hd9 : decode s9.executionEnv.code s9.pc = some (.Push .PUSH32, some (r, 32)) := by
    rw [hc9, hpc9]; exact checkfield_reads_input_and_r.1
  obtain _ | N := N
  · simp [evmRun] at hrun
  obtain ⟨s10, hst9, hrun⟩ := evmRun_succ_step callFuel N s9 _ _ _ hd9 (by decide) hrun
  have h9 : EVM.step (callFuel + 1) 0 (decode s9.executionEnv.code s9.pc) s9 = .ok s10 := by
    rw [hd9]; exact hst9
  obtain ⟨hp10, hs10, he10⟩ := step_PUSH_shape s9 s10 callFuel 0 .PUSH32 (by decide) r 32 hst9
  rw [hs9] at hs10
  have hc10 : s10.executionEnv.code = bytecode := by rw [he10]; exact hc9
  have hpc10 : s10.pc = UInt256.ofNat 55 := by rw [hp10, hpc9]; decide
  -- step 10: PUSH2 260 @ 55
  have hd10 : decode s10.executionEnv.code s10.pc = some (.Push .PUSH2, some (UInt256.ofNat 260, 2)) := by
    rw [hc10, hpc10]; exact checkfield_reads_input_and_r.2.1
  obtain _ | N := N
  · simp [evmRun] at hrun
  obtain ⟨s11, hst10, hrun⟩ := evmRun_succ_step callFuel N s10 _ _ _ hd10 (by decide) hrun
  have h10 : EVM.step (callFuel + 1) 0 (decode s10.executionEnv.code s10.pc) s10 = .ok s11 := by
    rw [hd10]; exact hst10
  obtain ⟨hp11, hs11, he11⟩ :=
    step_PUSH_shape s10 s11 callFuel 0 .PUSH2 (by decide) (UInt256.ofNat 260) 2 hst10
  rw [hs10] at hs11
  have hc11 : s11.executionEnv.code = bytecode := by rw [he11]; exact hc10
  have hpc11 : s11.pc = UInt256.ofNat 58 := by rw [hp11, hpc10]; decide
  -- step 11: CALLDATALOAD @ 58 — loads `publicInput`
  have hd11 : decode s11.executionEnv.code s11.pc = some (.CALLDATALOAD, none) := by
    rw [hc11, hpc11]; exact checkfield_reads_input_and_r.2.2
  obtain _ | N := N
  · simp [evmRun] at hrun
  obtain ⟨s12, hst11, hrun⟩ := evmRun_succ_step callFuel N s11 _ _ _ hd11 (by decide) hrun
  have h11 : EVM.step (callFuel + 1) 0 (decode s11.executionEnv.code s11.pc) s11 = .ok s12 := by
    rw [hd11]; exact hst11
  obtain ⟨hp12, hs12, he12⟩ :=
    step_CALLDATALOAD_value s11 s12 callFuel 0 none (UInt256.ofNat 260) [r] hs11 hst11
  have hc12 : s12.executionEnv.code = bytecode := by rw [he12]; exact hc11
  have hpc12 : s12.pc = UInt256.ofNat 59 := by rw [hp12, hpc11]; decide
  -- The loaded value is exactly `publicInput`: `s11.toState`'s calldata is
  -- `s`'s (chained through the ee-preservation facts above).
  have hcalldata11 : s11.executionEnv.calldata = s.executionEnv.calldata := by
    have : s11.executionEnv = s.executionEnv := by rw [he11, he10, he9, hs8ee]
    exact congrArg EvmYul.ExecutionEnv.calldata this
  have hs12' : s12.stack = publicInput :: [r] := by
    rw [hs12]
    unfold EvmYul.State.calldataload
    rw [hcalldata11]
  -- step 12: LT @ 59 — `LT publicInput r = 0` since `r ≤ publicInput`
  have hd12 : decode s12.executionEnv.code s12.pc = some (.LT, none) := by
    rw [hc12, hpc12]; exact checkfield_compares_and_branches.1
  obtain _ | N := N
  · simp [evmRun] at hrun
  obtain ⟨s13, hst12, hrun⟩ := evmRun_succ_step callFuel N s12 _ _ _ hd12 (by decide) hrun
  have h12 : EVM.step (callFuel + 1) 0 (decode s12.executionEnv.code s12.pc) s12 = .ok s13 := by
    rw [hd12]; exact hst12
  obtain ⟨hp13, hs13, he13, _⟩ :=
    step_LT_shape_strong s12 s13 callFuel 0 none publicInput r [] hs12' hst12
  have hc13 : s13.executionEnv.code = bytecode := by rw [he13]; exact hc12
  have hpc13 : s13.pc = UInt256.ofNat 60 := by rw [hp13, hpc12]; decide
  have hltZero : UInt256.lt publicInput r = UInt256.ofNat 0 := lt_eq_zero_of_ge hge
  rw [hltZero] at hs13
  -- step 13: ISZERO @ 60 — `ISZERO 0 = 1`
  have hd13 : decode s13.executionEnv.code s13.pc = some (.ISZERO, none) := by
    rw [hc13, hpc13]; exact checkfield_compares_and_branches.2.1
  obtain _ | N := N
  · simp [evmRun] at hrun
  obtain ⟨s14, hst13, hrun⟩ := evmRun_succ_step callFuel N s13 _ _ _ hd13 (by decide) hrun
  have h13 : EVM.step (callFuel + 1) 0 (decode s13.executionEnv.code s13.pc) s13 = .ok s14 := by
    rw [hd13]; exact hst13
  obtain ⟨hp14, hs14, he14⟩ :=
    step_ISZERO_value s13 s14 callFuel 0 none (UInt256.ofNat 0) [] hs13 hst13
  rw [iszero_zero_eq_one] at hs14
  have hc14 : s14.executionEnv.code = bytecode := by rw [he14]; exact hc13
  have hpc14 : s14.pc = UInt256.ofNat 61 := by rw [hp14, hpc13]; decide
  -- step 14: PUSH2 revertLbl @ 61
  have hd14 : decode s14.executionEnv.code s14.pc = some (.Push .PUSH2, some (revertLbl, 2)) := by
    rw [hc14, hpc14]; exact checkfield_compares_and_branches.2.2.1
  obtain _ | N := N
  · simp [evmRun] at hrun
  obtain ⟨s15, hst14, hrun⟩ := evmRun_succ_step callFuel N s14 _ _ _ hd14 (by decide) hrun
  have h14 : EVM.step (callFuel + 1) 0 (decode s14.executionEnv.code s14.pc) s14 = .ok s15 := by
    rw [hd14]; exact hst14
  obtain ⟨hp15, hs15, he15⟩ := step_PUSH_shape s14 s15 callFuel 0 .PUSH2 (by decide) revertLbl 2 hst14
  rw [hs14] at hs15
  have hc15 : s15.executionEnv.code = bytecode := by rw [he15]; exact hc14
  have hpc15 : s15.pc = UInt256.ofNat 64 := by rw [hp15, hpc14]; decide
  -- step 15: JUMPI @ 64 — taken (`ISZERO`'s `1` ≠ 0), lands at `revertLbl`
  have hd15 : decode s15.executionEnv.code s15.pc = some (.JUMPI, none) := by
    rw [hc15, hpc15]; exact checkfield_compares_and_branches.2.2.2
  obtain _ | N := N
  · simp [evmRun] at hrun
  obtain ⟨s16, hst15, hrun⟩ := evmRun_succ_step callFuel N s15 _ _ _ hd15 (by decide) hrun
  have h15 : EVM.step (callFuel + 1) 0 (decode s15.executionEnv.code s15.pc) s15 = .ok s16 := by
    rw [hd15]; exact hst15
  obtain ⟨hp16, hs16, he16, _⟩ :=
    step_JUMPI_shape_strong s15 s16 callFuel 0 none revertLbl (UInt256.ofNat 1) [] hs15 hst15
  have hc16 : s16.executionEnv.code = bytecode := by rw [he16]; exact hc15
  have hpc16 : s16.pc = UInt256.ofNat 898 := by
    rw [hp16, if_pos (by decide)]; rfl
  -- step 16: JUMPDEST @ 898 (revertLbl)
  have hd16 : decode s16.executionEnv.code s16.pc = some (.JUMPDEST, none) := by
    rw [hc16, hpc16]; native_decide
  obtain _ | N := N
  · simp [evmRun] at hrun
  obtain ⟨s17, hst16, hrun⟩ := evmRun_succ_step callFuel N s16 _ _ _ hd16 (by decide) hrun
  have h16 : EVM.step (callFuel + 1) 0 (decode s16.executionEnv.code s16.pc) s16 = .ok s17 := by
    rw [hd16]; exact hst16
  obtain ⟨hp17, hs17, he17⟩ := step_JUMPDEST_shape s16 s17 callFuel 0 none hst16
  rw [hs16] at hs17
  have hc17 : s17.executionEnv.code = bytecode := by rw [he17]; exact hc16
  have hpc17 : s17.pc = UInt256.ofNat 899 := by rw [hp17, hpc16]; decide
  -- step 17: PUSH1 0 @ 899
  have hd17 : decode s17.executionEnv.code s17.pc = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
    rw [hc17, hpc17]; native_decide
  obtain _ | N := N
  · simp [evmRun] at hrun
  obtain ⟨s18, hst17, hrun⟩ := evmRun_succ_step callFuel N s17 _ _ _ hd17 (by decide) hrun
  have h17 : EVM.step (callFuel + 1) 0 (decode s17.executionEnv.code s17.pc) s17 = .ok s18 := by
    rw [hd17]; exact hst17
  obtain ⟨hp18, hs18, he18⟩ := step_PUSH1_shape s17 s18 callFuel 0 (UInt256.ofNat 0) hst17
  rw [hs17] at hs18
  have hc18 : s18.executionEnv.code = bytecode := by rw [he18]; exact hc17
  have hpc18 : s18.pc = UInt256.ofNat 901 := by rw [hp18, hpc17]; decide
  -- step 18: PUSH1 0 @ 901
  have hd18 : decode s18.executionEnv.code s18.pc = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
    rw [hc18, hpc18]; native_decide
  obtain _ | N := N
  · simp [evmRun] at hrun
  obtain ⟨s19, hst18, hrun⟩ := evmRun_succ_step callFuel N s18 _ _ _ hd18 (by decide) hrun
  have h18 : EVM.step (callFuel + 1) 0 (decode s18.executionEnv.code s18.pc) s18 = .ok s19 := by
    rw [hd18]; exact hst18
  obtain ⟨hp19, _, he19⟩ := step_PUSH1_shape s18 s19 callFuel 0 (UInt256.ofNat 0) hst18
  have hc19 : s19.executionEnv.code = bytecode := by rw [he19]; exact hc18
  have hpc19 : s19.pc = UInt256.ofNat 903 := by rw [hp19, hpc18]; decide
  -- halt: REVERT @ 903
  have hd19 : decode s19.executionEnv.code s19.pc = some (.REVERT, none) := by
    rw [hc19, hpc19]; native_decide
  obtain _ | N := N
  · simp [evmRun] at hrun
  have hres := evmRun_halt_step callFuel N s19 _ _ _ hd19 (by decide) hrun
  have hres1 : s' = s19 := congrArg Prod.fst hres
  exact ⟨hHalt, by rw [hres1]; exact hd19⟩

end EvmSmith.Groth16
