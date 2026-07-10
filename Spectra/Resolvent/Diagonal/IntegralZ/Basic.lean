/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Diagonal.IntegralZ.GeneratorLim
import Spectra.Resolvent.Integral.Domain

/-!
# The Laplace-Integral Resolvent Equals the Abstract Resolvent

This file identifies the explicit Laplace-integral solution `resolventIntegralZ` with the
abstract `resolvent` built purely from formal self-adjointness and `(A ± i)`-surjectivity.

## Main statements

* `resolventIntegralZ_eq_resolvent` — for `z.im < 0`, `resolventIntegralZ U_grp z φ` equals
  `resolvent z … φ`.

## Implementation notes

Only `z.im < 0` is covered here: this is the honest domain where `resolventIntegralZ`
(the Laplace transform `-i ∫₀^∞ e^{-izt} U(t)φ dt`) is even defined and integrable. The
`z.im > 0` half is obtained elsewhere via the sibling `resolventIntegralMinus` construction
on the time-reversed group, not by generalizing this file's argument.

## References

* [Reed–Simon, *Methods of Modern Mathematical Physics I*][reedsimon1980], Theorem VIII.8
-/

open Spectra.OneParameterUnitaryGroup
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.Resolvent
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- **The Laplace-integral resolvent is the abstract resolvent**: for `z.im < 0`,
`resolventIntegralZ U_grp z φ = -i ∫₀^∞ e^{-izt} U(t)φ dt` coincides with `resolvent z … φ`,
the solution to `(A - z)ψ = φ` built abstractly from formal self-adjointness and
`(A ± i)`-surjectivity. The proof shows `J := resolventIntegralZ U_grp z φ` also solves
`(A - z)J = φ` and invokes uniqueness of solutions to identify the two. This is the fact that
`resolvent_diag_laplace` (`Resolvent/Diagonal/Basic.lean`) uses to derive the Nevanlinna/Herglotz
identity feeding Stone's formula. -/
theorem resolventIntegralZ_eq_resolvent {z : ℂ} (hz : z.im < 0) (φ : H) :
    resolventIntegralZ U_grp z φ
      = resolvent z (ne_of_lt hz)
          (generator_isFormalAdjoint U_grp)
          (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) φ := by
  -- `J := resolventIntegralZ U_grp z φ` solves `(A - z) J = φ`,
  -- exactly the `range_plus_i_eq_top` move applied to the `z`-limit:
  have hlim := generator_limit_resolventIntegralZ U_grp hz φ
  have hmem : resolventIntegralZ U_grp z φ ∈ (generator U_grp).domain := ⟨_, hlim⟩
  have hval : generator U_grp ⟨resolventIntegralZ U_grp z φ, hmem⟩
            = z • resolventIntegralZ U_grp z φ + φ :=
    tendsto_nhds_unique
      (generator_tendsto U_grp ⟨resolventIntegralZ U_grp z φ, hmem⟩) hlim
  have hJ : generator U_grp ⟨resolventIntegralZ U_grp z φ, hmem⟩
              - z • resolventIntegralZ U_grp z φ = φ := by
    rw [hval]; abel
  let J : (generator U_grp).domain :=
    Classical.choose
      (self_adjoint_range_all_z (generator_isFormalAdjoint U_grp)
        (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) z (ne_of_lt hz) φ).exists
  have hR_eq : generator U_grp J - z • (J : H) = φ :=
    Classical.choose_spec
      (self_adjoint_range_all_z (generator_isFormalAdjoint U_grp)
        (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) z (ne_of_lt hz) φ).exists
  have hR_res :
      resolvent z (ne_of_lt hz) (generator_isFormalAdjoint U_grp)
        (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) φ = (J : H) := rfl
  -- uniqueness of solutions to `(A - z)· = φ`:
  have huniq : (⟨resolventIntegralZ U_grp z φ, hmem⟩ : (generator U_grp).domain) = J :=
      solution_unique (generator_isFormalAdjoint U_grp) z (ne_of_lt hz) φ
        ⟨resolventIntegralZ U_grp z φ, hmem⟩ J hJ hR_eq
  rw [hR_res]
  exact congrArg Subtype.val huniq

end Spectra.Resolvent
