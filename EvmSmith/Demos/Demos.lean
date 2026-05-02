import EvmSmith.Framework
import EvmSmith.Demos.Add3.Program
import EvmSmith.Demos.Register.Program
import EvmSmith.Demos.Weth.Program

/-!
# IO demos — shows the framework in action

Each `demo*` prints an expected result to stdout. `EvmSmith/Demos/Main.lean`
calls them all from `main`, so `lake exe evm-smith` is the one-command
smoke test.
-/

namespace EvmSmith
open EvmYul EvmYul.EVM

/-- ADD: 3 + 4 = 7 on top of stack. -/
def demoAdd : IO Unit := do
  let pre  := mkState (stack := [UInt256.ofNat 3, UInt256.ofNat 4])
  let post := runOp .ADD pre
  IO.println s!"ADD: top = {topOf post}"

/-- PUSH1 42 onto empty stack. -/
def demoPush : IO Unit := do
  let pre  := mkState (stack := [])
  let post := runOp (.Push .PUSH1) pre (arg := some (UInt256.ofNat 42, 1))
  IO.println s!"PUSH1 42: top = {topOf post}"

/-- DUP1 duplicates the top. -/
def demoDup : IO Unit := do
  let pre  := mkState (stack := [UInt256.ofNat 7, UInt256.ofNat 8])
  let post := runOp .DUP1 pre
  let printedStack :=
    match stackOf post with
    | some s => toString (s.map UInt256.toNat)
    | none   => "<error>"
  IO.println s!"DUP1: stack = {printedStack}"

/-- Parity between the pure `runOp` (via `EvmYul.step`) and the full
    `runOpFull` (via `EVM.step`). They must agree on `.stack`. -/
def demoParity : IO Unit := do
  let pre := mkState (stack := [UInt256.ofNat 3, UInt256.ofNat 4])
  let a := (runOp .ADD pre).toOption.map (·.stack.map UInt256.toNat)
  let b := (runOpFull .ADD pre).toOption.map (·.stack.map UInt256.toNat)
  IO.println s!"parity: runOp stack = {a}"
  IO.println s!"parity: runOpFull stack = {b}"
  IO.println s!"parity stacks match? {a == b}"

/-- End-to-end demo of the `add3` bytecode: construct 96-byte calldata
    from three UInt256 values, run the full program (ADD prefix + MSTORE +
    RETURN), and check the returned 32 bytes decode to `a + b + c`. -/
def demoAdd3 : IO Unit := do
  let run (a b c : Nat) : IO Unit := do
    let av := UInt256.ofNat a
    let bv := UInt256.ofNat b
    let cv := UInt256.ofNat c
    let cd := av.toByteArray ++ bv.toByteArray ++ cv.toByteArray
    let s0 := withCalldata (mkState []) cd
    match runSeq Add3.program s0 with
    | .ok s =>
        let returned := (uInt256OfByteArray s.H_return).toNat
        let ok := returned == a + b + c
        IO.println s!"add3({a}, {b}, {c}) → {returned} (expected {a + b + c}, ok? {ok})"
    | .error e =>
        IO.println s!"add3({a}, {b}, {c}) → error {repr e}"
  run 1 2 3
  run 10 20 30
  run 100 200 300
  run 0 0 0

/-- Register: run the storage-write prefix (`PUSH1 0; CALLDATALOAD;
    CALLER; SSTORE`) — the first 4 ops of `Register.program` — and
    show that `storage[sender]` ends up holding the calldata word. The
    suffix (`CALL; POP; STOP`) is intentionally skipped because pure
    `runSeq` doesn't drive the frame-aware Θ machinery; the on-chain
    behavior of the CALL is exercised by the Foundry tests. -/
def demoRegister : IO Unit := do
  let storePrefix : EvmSmith.Program :=
    [ (.Push .PUSH1, some (UInt256.ofNat 0, 1))
    , (.CALLDATALOAD, none)
    , (.CALLER,       none)
    , (.SSTORE,       none)
    ]
  let run (sender : AccountAddress) (v : UInt256) : IO Unit := do
    let owner : AccountAddress := 0xC0DE
    let s0 := withCalldata (mkState []) v.toByteArray
    let env := { s0.executionEnv with codeOwner := owner, source := sender }
    let s1 := ({ s0 with executionEnv := env }) |> withSelfAccount
    match runSeq storePrefix s1 with
    | .ok s =>
        let stored := storageAt s owner (addressSlot sender)
        IO.println s!"register: SSTORE storage[sender={sender.val}] = {v.toNat}; read back {stored.toNat} (ok? {stored == v})"
    | .error e =>
        IO.println s!"register: error {repr e}"
  run 0xCAFE   (UInt256.ofNat 0xdeadbeef)
  run 0xBEEF   (UInt256.ofNat 12345)
  run 0xC0FFEE (UInt256.ofNat 0)

/-- Weth: run the **deposit block** twice on chained state and show
    `storage[sender]` accumulates `msg.value` across calls. The block
    runs end-to-end (no CALL inside it), so pure `runSeq` is enough. -/
def demoWethDeposit : IO Unit := do
  let owner  : AccountAddress := 0xCAFE
  let sender : AccountAddress := 0xBEEF
  -- Deposit's entry stack from the dispatcher is `[selector]`; the
  -- block's first op is POP, which throws it away.
  let entryStack : Stack UInt256 := [Weth.depositSelector]
  let setEnv (s : EVM.State) (v : UInt256) : EVM.State :=
    let env' := { s.executionEnv with
                    codeOwner := owner, source := sender, weiValue := v }
    { s with stack := entryStack, executionEnv := env' }
  -- mkState [] needs an account at codeOwner so SSTORE has a target.
  let s0 := (setEnv (mkState []) (UInt256.ofNat 10)) |> withSelfAccount
  match runSeq Weth.depositBlock s0 with
  | .error e => IO.println s!"weth deposit 1: error {repr e}"
  | .ok s1 =>
    let bal1 := storageAt s1 owner (addressSlot sender)
    IO.println s!"weth deposit 1: +10 wei → storage[sender] = {bal1.toNat} (expected 10, ok? {bal1.toNat == 10})"
    let s2 := setEnv s1 (UInt256.ofNat 25)
    match runSeq Weth.depositBlock s2 with
    | .error e => IO.println s!"weth deposit 2: error {repr e}"
    | .ok s3 =>
      let bal2 := storageAt s3 owner (addressSlot sender)
      IO.println s!"weth deposit 2: +25 wei → storage[sender] = {bal2.toNat} (expected 35, ok? {bal2.toNat == 35})"

/-- Weth: deposit 100 wei, then run `withdrawPreCallBlock` (the
    state-update prefix of withdraw, up to but not including CALL) for
    amount=30, and show `storage[sender]` decreases to 70. Skipping the
    actual CALL is the same trick as in `demoRegister`: pure `runSeq`
    isn't frame-aware. -/
def demoWethWithdraw : IO Unit := do
  let owner  : AccountAddress := 0xCAFE
  let sender : AccountAddress := 0xBEEF
  -- Step 1: deposit 100 wei to set up storage[sender] = 100.
  let init := mkState []
  let env0 := { init.executionEnv with
                  codeOwner := owner, source := sender,
                  weiValue := UInt256.ofNat 100 }
  let s0 := ({ init with stack := [Weth.depositSelector], executionEnv := env0 }) |> withSelfAccount
  match runSeq Weth.depositBlock s0 with
  | .error e => IO.println s!"weth withdraw setup: error {repr e}"
  | .ok s1 =>
    let bal := storageAt s1 owner (addressSlot sender)
    IO.println s!"weth withdraw setup: deposited 100 wei → storage[sender] = {bal.toNat}"
    -- Step 2: run withdraw prefix with calldata = withdrawSelector ++ amount(30).
    let cd : ByteArray :=
      ⟨#[0x2e, 0x1a, 0x7d, 0x4d]⟩ ++ (UInt256.ofNat 30).toByteArray
    let env1 := { s1.executionEnv with calldata := cd, weiValue := UInt256.ofNat 0 }
    let s2 := { s1 with stack := [], executionEnv := env1 }
    match runSeq Weth.withdrawPreCallBlock s2 with
    | .error e => IO.println s!"weth withdraw: error {repr e}"
    | .ok s3 =>
      let bal' := storageAt s3 owner (addressSlot sender)
      IO.println s!"weth withdraw: -30 wei → storage[sender] = {bal'.toNat} (expected 70, ok? {bal'.toNat == 70})"

end EvmSmith
