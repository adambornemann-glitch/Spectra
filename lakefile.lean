import Lake
open Lake DSL

package «Spectra» where
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Spectra» where
  leanOptions := #[
    /- check that `mathlib` style is followed -/
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    /- check that `def` is used for propositions, not `theorem`/`lemma` -/
    ⟨`weak.linter.defProp, true⟩,
    /- check that all implicit arguments are explicitly marked with `{}` or `[]` -/
    ⟨`relaxedAutoImplicit, false⟩,
    /- check that all universe levels are explicitly marked with `{}` or `[]` -/
    ⟨`weak.linter.checkUnivs, true⟩,
    /- check that all implicit arguments are explicitly marked with `{}` or `[]` -/
    ⟨`autoImplicit, false⟩,
    /- check that all tactic variables are used -/
    ⟨`weak.linter.unusedVariables.analyzeTactics, true⟩,
    /- check that `simp`/`rw`/`dsimp` are not called with the same argument multiple times -/
    ⟨`weak.linter.loopingSimpArgs, true⟩,
    /- check that the number of pending goals in `synthInstance` does not exceed 3 -/
    ⟨`maxSynthPendingDepth, 3⟩
    ]

-- Compile-time axiom gate (root module `AxiomCheck.lean`): `assert_no_sorry` on every
-- headline result. As a default target, `lake build` fails if a `sorry` reaches any of them.
@[default_target]
lean_lib «AxiomCheck» where
  globs := #[.one `AxiomCheck]

-- Forensic index engine (`Forensic.lean`): reusable meta-programming to audit theorem
-- *statements* — unused hypotheses and transitive assumption cones. No side effects; built
-- as a dependency of the gate/report modules below.
lean_lib «Forensic» where
  globs := #[.one `Forensic]

-- Compile-time hypothesis-hygiene gate (`ForensicCheck.lean`): as a default target,
-- `lake build` fails if any theorem carries a normally-named but unused hypothesis
-- (an over-strong or vacuous statement). Intentionally-unused hypotheses are exempt by
-- the `_`-prefix convention.
@[default_target]
lean_lib «ForensicCheck» where
  globs := #[.one `ForensicCheck]
