import Lake
open Lake DSL

package «Spectra» where
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Spectra» where
  -- add any library configuration options here

-- Compile-time axiom gate (root module `AxiomCheck.lean`): `assert_no_sorry` on every
-- headline result. As a default target, `lake build` fails if a `sorry` reaches any of them.
@[default_target]
lean_lib «AxiomCheck» where
  globs := #[.one `AxiomCheck]
