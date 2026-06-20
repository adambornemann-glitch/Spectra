/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Diagonal.IntegralZ.GeneratorLim
import Spectra.Resolvent.Integral.Domain

open Complex
open Spectra.OneParameterUnitaryGroup
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.Resolvent
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- Hence `(A - z)` sends the integral to `φ`, so it IS the resolvent. -/
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
  let R_sub : (generator U_grp).domain :=
    Classical.choose
      (self_adjoint_range_all_z (generator_isFormalAdjoint U_grp)
        (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) z (ne_of_lt hz) φ).exists
  have hR_eq : generator U_grp R_sub - z • (R_sub : H) = φ :=
    Classical.choose_spec
      (self_adjoint_range_all_z (generator_isFormalAdjoint U_grp)
        (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) z (ne_of_lt hz) φ).exists
  have hR_res :
      resolvent z (ne_of_lt hz) (generator_isFormalAdjoint U_grp)
        (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) φ = (R_sub : H) := rfl
  -- uniqueness of solutions to `(A - z)· = φ`:
  have huniq : (⟨resolventIntegralZ U_grp z φ, hmem⟩ : (generator U_grp).domain) = R_sub :=
      solution_unique (generator_isFormalAdjoint U_grp) z (ne_of_lt hz) φ
        ⟨resolventIntegralZ U_grp z φ, hmem⟩ R_sub hJ hR_eq
  rw [hR_res]
  exact congrArg Subtype.val huniq

end Spectra.Resolvent
