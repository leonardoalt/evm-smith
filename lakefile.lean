import Lake
open Lake DSL

package «evmSmith» where
  moreLeanArgs := #["-DautoImplicit=false"]
  moreServerOptions := #[⟨`autoImplicit, false⟩]

require evmyul from "EVMYulLean"

@[default_target]
lean_lib «EvmSmith»

lean_exe «evm-smith» where
  root := `EvmSmith.Demos.Main

lean_exe «add3-dump-bytecode» where
  root := `EvmSmith.Demos.Add3.DumpBytecode

lean_exe «register-dump-bytecode» where
  root := `EvmSmith.Demos.Register.DumpBytecode

lean_exe «weth-dump-bytecode» where
  root := `EvmSmith.Demos.Weth.DumpBytecode

lean_exe «weth-call-graph» where
  root := `EvmSmith.Demos.Weth.CallGraph
  supportInterpreter := true
