/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Diagonal.IntegralZ.Tendsto
import Spectra.Resolvent.Integral.Limits

/-!
# The head/tail shift split of the general-`z` resolvent integral

This file proves the algebraic core of the general-`z` resolvent generator argument: how the
shift `U(h)R(z)φ − R(z)φ` of the resolvent integral `R(z)φ = (−i)∫₀^∞ e^{−izt}U(t)φ dt` splits
into head/tail pieces, for both `h > 0` and `h < 0`, plus two small algebraic facts repackaging
the generator target and a scalar identity used in the difference quotient. These results feed
`DiffQuotient.lean` and `GeneratorLim.lean` directly.

## Main statements

* `unitary_shift_resolventIntegralZ` / `_neg` — the head/tail split of `U(h)R(z)φ - R(z)φ` for
  `h > 0` / `h < 0`.
* `genZ_target_eq` — the generator target `z·R(z)φ + φ` rewritten via the resolvent integral.
* `genZ_scalar` — the scalar identity `(ih)⁻¹·(-i) = -h⁻¹` used in the difference quotient.
-/

open Complex
open Spectra.OneParameterUnitaryGroup
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.Resolvent

variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- For `Im z < 0` and `a ≤ b`, the orbit integral over `Ici a` splits as `Ioc a b` plus `Ici b`. -/
private lemma integral_Ici_orbit_split_Z {z : ℂ} (hz : z.im < 0) (φ : H) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in Set.Ici a, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ =
    (∫ t in Set.Ioc a b, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) +
    ∫ t in Set.Ici b, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ :=
  integral_Ici_split_of (expZ_orbit_continuous U_grp (z := z) φ)
    (integrable_expZ_unitary U_grp hz φ) hab

/-- For `Im z < 0` and `h > 0`, the **shift** `U(h)R(z)φ - R(z)φ` of the resolvent integral splits
into a tail term over `Ici h` and a head term over `Ioc 0 h`. -/
lemma unitary_shift_resolventIntegralZ {z : ℂ} (hz : z.im < 0) (φ : H) (h : ℝ) (hh : h > 0) :
    U_grp.U h (resolventIntegralZ U_grp z φ) - resolventIntegralZ U_grp z φ =
    (-I) • ((cexp (I * z * (h : ℂ)) - 1) •
        ∫ t in Set.Ici h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) -
    (-I) • ∫ t in Set.Ioc 0 h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ := by
  unfold resolventIntegralZ
  rw [ContinuousLinearMap.map_smul, unitary_apply_expZ_integral U_grp hz φ h,
      integral_Ici_orbit_split_Z U_grp hz φ (le_of_lt hh)]
  set X := ∫ s in Set.Ici h, cexp (-(I * z * (s : ℂ))) • U_grp.U s φ
  set Y := ∫ t in Set.Ioc 0 h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ
  rw [smul_add]
  module

/-- For `Im z < 0` and `h < 0`, the **shift** `U(h)R(z)φ - R(z)φ` of the resolvent integral splits
into a term over `Ioc h 0` and a term over `Ici 0`. -/
lemma unitary_shift_resolventIntegralZ_neg {z : ℂ} (hz : z.im < 0) (φ : H) (h : ℝ) (hh : h < 0) :
    U_grp.U h (resolventIntegralZ U_grp z φ) - resolventIntegralZ U_grp z φ =
    (-I) • (cexp (I * z * (h : ℂ)) •
        ∫ t in Set.Ioc h 0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) +
    (-I) • ((cexp (I * z * (h : ℂ)) - 1) •
        ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) := by
  unfold resolventIntegralZ
  rw [ContinuousLinearMap.map_smul, unitary_apply_expZ_integral U_grp hz φ h,
      integral_Ici_orbit_split_Z U_grp hz φ (le_of_lt hh)]
  set X := ∫ t in Set.Ioc h 0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ
  set Y := ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ
  rw [smul_add]
  module

/-- The **generator target** `z·R(z)φ + φ` equals `-(iz)∫₀^∞ e^{-izt}U(t)φ dt + φ`. -/
lemma genZ_target_eq {z : ℂ} (φ : H) :
    z • resolventIntegralZ U_grp z φ + φ =
      -((I * z) • ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) + φ := by
  unfold resolventIntegralZ
  rw [smul_smul, mul_neg, neg_smul, mul_comm z I]

/-- The **scalar identity** `(ih)⁻¹·(-i) = -h⁻¹` used in the generator difference quotient. -/
lemma genZ_scalar (h : ℝ) : ((I * (h : ℂ))⁻¹ * (-I) : ℂ) = -(h : ℂ)⁻¹ := by
  rw [mul_inv_rev, mul_assoc, mul_neg, inv_mul_cancel₀ I_ne_zero, mul_neg_one]

end Spectra.Resolvent
