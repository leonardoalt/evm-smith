import EvmYul.Wheels
import EvmSmith.Demos.Weth.OptimizedProgramV2

/-!
# Dump `Weth.bytecodeV2` as hex for the Foundry gas-comparison test

Writes the V2-optimized runtime bytecode (CALLER-twice + dropped POP)
into `EvmSmith/Demos/Weth/foundry/test/Weth.optimizedV2.bytecode.hex`.

Run from the repo root: `lake exe weth-opt-v2-dump-bytecode`.
-/

open EvmSmith

def main : IO Unit :=
  IO.FS.writeFile
    "EvmSmith/Demos/Weth/foundry/test/Weth.optimizedV2.bytecode.hex"
    ("0x" ++ EvmYul.toHex Weth.bytecodeV2 ++ "\n")
