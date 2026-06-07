/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: UnitaryEvolution/Resolvent/IntegralZ.lean
-/
import Spectra.UnitaryEvolution.Resolvent.Diagonal.IntegralZ.Tendsto

namespace QuantumMechanics.Resolvent

open Complex Bochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U_grp : OneParameterUnitaryGroup (H := H))

lemma expZ_orbit_continuous {z : ℂ} (φ : H) :
    Continuous (fun t : ℝ => cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) :=
  (Complex.continuous_exp.comp ((Complex.continuous_ofReal.const_mul (I * z)).neg)).smul
    (U_grp.strong_continuous φ)

lemma integral_Ici_orbit_split_Z {z : ℂ} (hz : z.im < 0) (φ : H) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in Set.Ici a, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ =
    (∫ t in Set.Ioc a b, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) +
    ∫ t in Set.Ici b, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ :=
  integral_Ici_split_of (expZ_orbit_continuous U_grp (z := z) φ)
    (integrable_expZ_unitary U_grp hz φ) hab

lemma unitary_shift_resolventIntegralZ {z : ℂ} (hz : z.im < 0) (φ : H) (h : ℝ) (hh : h > 0) :
    U_grp.U h (resolventIntegralZ U_grp z φ) - resolventIntegralZ U_grp z φ =
    (-I) • ((cexp (I * z * (h : ℂ)) - 1) •
        ∫ t in Set.Ici h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) -
    (-I) • ∫ t in Set.Ioc 0 h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ := by
  unfold resolventIntegralZ
  rw [ContinuousLinearMap.map_smul, unitary_apply_expZ_integral U_grp hz φ h,
      integral_Ici_orbit_split_Z U_grp hz φ (le_of_lt hh)]
  set X := ∫ s in Set.Ici h, cexp (-(I * z * (s : ℂ))) • U_grp.U s φ with hX_def
  set Y := ∫ t in Set.Ioc 0 h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ with hY_def
  rw [smul_add]
  calc -I • cexp (I * z * (h : ℂ)) • X - (-I • Y + -I • X)
      = -I • cexp (I * z * (h : ℂ)) • X - -I • X - -I • Y := by abel
    _ = -I • (cexp (I * z * (h : ℂ)) • X - X) - -I • Y := by rw [← smul_sub]
    _ = -I • ((cexp (I * z * (h : ℂ)) - 1) • X) - -I • Y := by rw [sub_smul, one_smul]

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
  calc -I • (cexp (I * z * (h : ℂ)) • X + cexp (I * z * (h : ℂ)) • Y) - -I • Y
      = -I • cexp (I * z * (h : ℂ)) • X + -I • cexp (I * z * (h : ℂ)) • Y - -I • Y := by rw [smul_add]
    _ = -I • cexp (I * z * (h : ℂ)) • X + (-I • cexp (I * z * (h : ℂ)) • Y - -I • Y) := by abel
    _ = -I • cexp (I * z * (h : ℂ)) • X + -I • (cexp (I * z * (h : ℂ)) • Y - Y) := by rw [← smul_sub]
    _ = -I • cexp (I * z * (h : ℂ)) • X + -I • ((cexp (I * z * (h : ℂ)) - 1) • Y) := by
        rw [sub_smul, one_smul]

lemma genZ_target_eq {z : ℂ} (φ : H) :
    z • resolventIntegralZ U_grp z φ + φ =
      -((I * z) • ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) + φ := by
  unfold resolventIntegralZ
  rw [smul_smul, mul_neg, neg_smul, mul_comm z I]

lemma genZ_scalar (h : ℝ) : ((I * (h : ℂ))⁻¹ * (-I) : ℂ) = -(h : ℂ)⁻¹ := by
  rw [mul_inv_rev, mul_assoc, mul_neg, inv_mul_cancel₀ I_ne_zero, mul_neg_one]

end Resolvent
