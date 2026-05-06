import EvmYul.Wheels
import EvmSmith.Demos.Weth.OptimizedProgram

/-!
# Dump `Weth.bytecodeOpt` as hex for the Foundry gas-comparison test

Writes the PUSH0-optimized runtime bytecode into
`EvmSmith/Demos/Weth/foundry/test/Weth.optimized.bytecode.hex`.

Run from the repo root: `lake exe weth-opt-dump-bytecode`.
-/

open EvmSmith

def main : IO Unit :=
  IO.FS.writeFile
    "EvmSmith/Demos/Weth/foundry/test/Weth.optimized.bytecode.hex"
    ("0x" ++ EvmYul.toHex Weth.bytecodeOpt ++ "\n")
