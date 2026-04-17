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
