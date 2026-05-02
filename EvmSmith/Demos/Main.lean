import EvmSmith.Demos.Demos

open EvmSmith

def main : IO Unit := do
  demoAdd
  demoPush
  demoDup
  demoParity
  IO.println ""
  IO.println "-- add3 program (reads 3 u256 from calldata, returns sum) --"
  demoAdd3
  IO.println ""
  IO.println "-- register storage prefix (PUSH1 0; CALLDATALOAD; CALLER; SSTORE) --"
  demoRegister
  IO.println ""
  IO.println "-- weth deposit block (chained: 10 then 25) --"
  demoWethDeposit
  IO.println ""
  IO.println "-- weth withdraw pre-call block (deposit 100, then withdraw 30) --"
  demoWethWithdraw
