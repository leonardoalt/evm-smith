import EvmSmith.Demos.Register.Program

/-!
# `Register` program — structural theorems

The original structural theorems for Register's first (6-byte)
incarnation have been retired: the bytecode now contains a CALL
after the SSTORE, which takes the state off into `Θ` and beyond the
reach of `runSeq`-based reasoning. The meaningful invariant now lives
in `BalanceMono.lean`, which reasons about `Υ` / `Θ` / `Ξ` directly.

This file is kept as a placeholder so existing imports continue to
resolve. Any future structural lemma about the dispatch prefix (bytes
0-4, ending in SSTORE before the CALL) can be added here.
-/

namespace EvmSmith.RegisterProofs

end EvmSmith.RegisterProofs
