/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: UnitaryEvolution/Resolvent/IntegralZ/Bulk.lean
-/
import Spectra.UnitaryEvolution.Resolvent.Diagonal.IntegralZ.Tendsto

namespace QuantumMechanics.Resolvent

open Complex Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U_grp : OneParameterUnitaryGroup (H := H))

lemma genZ_bulk_pos {z : ℂ} (hz : z.im < 0) (φ : H) :
    Tendsto (fun h : ℝ => -((h : ℂ)⁻¹ • (cexp (I * z * (h : ℂ)) - 1) •
        ∫ t in Set.Ici h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ))
      (𝓝[>] 0)
      (𝓝 (-((I * z) • ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ))) := by
  apply Tendsto.neg
  have he_cplx : Tendsto (fun h : ℝ => (cexp (I * z * (h : ℂ)) - 1) / (h : ℂ))
      (𝓝[>] 0) (𝓝 (I * z)) :=
    tendsto_cexp_mul_sub_one_div.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))
  have hi : Tendsto (fun h : ℝ => ∫ t in Set.Ici h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)
      (𝓝[>] 0) (𝓝 (∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)) :=
    (tendsto_integral_Ici_expZ_unitary U_grp hz φ).mono_left nhdsWithin_le_nhds
  have h_prod : Tendsto (fun h : ℝ => ((cexp (I * z * (h : ℂ)) - 1) / (h : ℂ)) •
      ∫ t in Set.Ici h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)
      (𝓝[>] 0)
      (𝓝 ((I * z) • ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)) :=
    Tendsto.smul he_cplx hi
  apply Tendsto.congr' _ h_prod
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [div_eq_inv_mul, ← smul_smul]

lemma genZ_bulk_neg {z : ℂ} (φ : H) :
    Tendsto (fun h : ℝ => -(h : ℂ)⁻¹ • (cexp (I * z * (h : ℂ)) - 1) •
        ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)
      (𝓝[<] 0)
      (𝓝 (-((I * z) • ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ))) := by
  have he_cplx : Tendsto (fun h : ℝ => (cexp (I * z * (h : ℂ)) - 1) / (h : ℂ))
      (𝓝[<] 0) (𝓝 (I * z)) :=
    tendsto_cexp_mul_sub_one_div.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_lt hx))
  have h_prod : Tendsto (fun h : ℝ => ((cexp (I * z * (h : ℂ)) - 1) / (h : ℂ)) •
      ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)
      (𝓝[<] 0)
      (𝓝 ((I * z) • ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)) :=
    Tendsto.smul he_cplx tendsto_const_nhds
  have h_inner : Tendsto (fun h : ℝ => (h : ℂ)⁻¹ • (cexp (I * z * (h : ℂ)) - 1) •
      ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)
      (𝓝[<] 0)
      (𝓝 ((I * z) • ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)) := by
    apply Tendsto.congr' _ h_prod
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [div_eq_inv_mul, ← smul_smul]
  apply Tendsto.congr' _ h_inner.neg
  filter_upwards with h
  rw [neg_smul]

end QuantumMechanics.Resolvent
