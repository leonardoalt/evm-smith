# weth spec

Let's take our weth demo here with a weth-like contract and write a readable formal spec for it.                                                                        
Read the old commits and weth dir for context on what it does and how.                                                                                                  
We managed to prove inductive invariants over reentrancy for it.                                                                                                        
                                                                                                                                                                        
Now we want to make the spec more readable.                                                                                                                             
The spec is now defined in Lean theorems.                                                                                                                               
                                                                                                                                                                        
## separate spec                                                                                                               
                                                                                                                                                                        
I don't know if the spec is already a separate file, but let's extract the                                                                                              
formal spec, i.e., what the contract should do/not do, into a separate file.                               

## human-readable spec                                                                                                                                                  
                                                                                                                                                                        
Let's design a very simple v1 human-readable spec format/language for our weth properties.                                                                              
We want any Solidity dev to be able to read these properties without knowing the internals of EVMYulLean, evm-smith or Lean.                                            
Some Lean-reading skills is okay to be assumed/required.                                                                                                                
This v1 may use functions to abstract odd symbols/math/syntax, named types etc.                                                                                         
The spec must be what the theorems use.
Our goal is for auditors/devs/etc to have to read ONLY the spec and what connects the spec and the bytecode to be convinced that e2e works.
We'll later proceed with a Solidity-subset-like eDSL.                                                                                                                   

## workflow

- Keep things simple.
- Do not overcomplicate.
- Make a work branch.
- Push progress as it happens in sensible commits.
- Spec should be as simple and readable as possible.
- Do not change existing proofs and functionalities.
- All proofs should still work.
- Write a succinct md report for my review after.
