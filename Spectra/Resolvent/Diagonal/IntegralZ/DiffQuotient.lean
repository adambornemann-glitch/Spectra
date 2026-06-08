/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: UnitaryEvolution/Resolvent/IntegralZ/DiffQuotient.lean
-/
import Spectra.Resolvent.Diagonal.IntegralZ.Shift
open Complex
open Spectra.QuantumMechanics
open OneParameterUnitaryGroup
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U_grp : OneParameterUnitaryGroup (H := H))

namespace Spectra.Resolvent

lemma genZ_diffQuotient_pos {z : ℂ} (hz : z.im < 0) (φ : H) (h : ℝ) (hh : h > 0) :
    ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralZ U_grp z φ) -
        resolventIntegralZ U_grp z φ) =
      -((h : ℂ)⁻¹ • (cexp (I * z * (h : ℂ)) - 1) •
          ∫ t in Set.Ici h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) +
      ((h : ℂ)⁻¹ • ∫ t in Set.Ioc 0 h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) := by
  have key : ∀ w : H, (I * (h : ℂ))⁻¹ • (-I) • w = -((h : ℂ)⁻¹ • w) := fun w => by
    rw [smul_smul, genZ_scalar h, neg_smul]
  rw [unitary_shift_resolventIntegralZ U_grp hz φ h hh, smul_sub,
      key ((cexp (I * z * (h : ℂ)) - 1) • ∫ t in Set.Ici h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ),
      key (∫ t in Set.Ioc 0 h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ),
      sub_neg_eq_add]

lemma genZ_diffQuotient_neg {z : ℂ} (hz : z.im < 0) (φ : H) (h : ℝ) (hh : h < 0) :
    ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralZ U_grp z φ) -
        resolventIntegralZ U_grp z φ) =
      (-(h : ℂ)⁻¹ • cexp (I * z * (h : ℂ)) •
          ∫ t in Set.Ioc h 0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) +
      (-(h : ℂ)⁻¹ • (cexp (I * z * (h : ℂ)) - 1) •
          ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) := by
  have key : ∀ w : H, (I * (h : ℂ))⁻¹ • (-I) • w = -(h : ℂ)⁻¹ • w := fun w => by
    rw [smul_smul, genZ_scalar h]
  rw [unitary_shift_resolventIntegralZ_neg U_grp hz φ h hh, smul_add,
      key (cexp (I * z * (h : ℂ)) • ∫ t in Set.Ioc h 0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ),
      key ((cexp (I * z * (h : ℂ)) - 1) • ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)]

end Spectra.Resolvent
