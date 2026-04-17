import EvmYul.Wheels
import EvmSmith.Demos.Add3.Program

/-!
# Dump `Add3.bytecode` as hex for the Foundry tests

Writes the runtime bytecode from `Program.lean` as a `0x`-prefixed hex
string into `EvmSmith/Demos/Add3/foundry/test/Add3.bytecode.hex`. The
Foundry test reads this file at `setUp` via `vm.readFile` +
`vm.parseBytes` and installs it with `vm.etch`.

Run from the repo root: `lake exe add3-dump-bytecode`.
-/

open EvmSmith

def main : IO Unit :=
  IO.FS.writeFile
    "EvmSmith/Demos/Add3/foundry/test/Add3.bytecode.hex"
    ("0x" ++ EvmYul.toHex Add3.bytecode ++ "\n")
