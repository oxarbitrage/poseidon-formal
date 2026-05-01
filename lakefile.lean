import Lake
open Lake DSL

package PoseidonFormal where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib Poseidon where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

require pasta_formal from git
  "https://github.com/oxarbitrage/pasta-formal"
