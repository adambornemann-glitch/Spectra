/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: UnitaryEvolution/Resolvent/IntegralZ/DiffQuotient.lean
-/
import Spectra.Resolvent.Diagonal.IntegralZ.DiffQuotient
import Spectra.Resolvent.Diagonal.IntegralZ.Bulk

open Complex Filter Topology
open Spectra.OneParameterUnitaryGroup
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Resolvent
variable (U_grp : OneParameterUnitaryGroup (H := H))

lemma genZ_boundary_neg {z : ℂ} (φ : H) :
    Tendsto (fun h : ℝ => -(h : ℂ)⁻¹ • cexp (I * z * (h : ℂ)) •
        ∫ t in Set.Ioc h 0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) (𝓝[<] 0) (𝓝 φ) := by
  have h_avg := tendsto_average_integral_expZ_unitary_neg U_grp (z := z) φ
  have he' : Tendsto (fun h : ℝ => cexp (I * z * (h : ℂ))) (𝓝[<] 0) (𝓝 (1 : ℂ)) := by
    have hc : Continuous (fun h : ℝ => cexp (I * z * (h : ℂ))) :=
      Complex.continuous_exp.comp (Complex.continuous_ofReal.const_mul (I * z))
    have hval : cexp (I * z * ((0 : ℝ) : ℂ)) = 1 := by
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [← hval]
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have h_comb : Tendsto (fun h : ℝ => cexp (I * z * (h : ℂ)) • (((-h)⁻¹ : ℂ) •
      ∫ t in Set.Ioc h 0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)) (𝓝[<] 0) (𝓝 ((1 : ℂ) • φ)) :=
    Tendsto.smul he' h_avg
  simp only [one_smul] at h_comb
  apply Tendsto.congr' _ h_comb
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [smul_comm, @inv_neg]

/-- The difference-quotient limit lands on `z • R(z)φ + φ`. -/
lemma generator_limit_resolventIntegralZ {z : ℂ} (hz : z.im < 0) (φ : H) :
    Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) •
        (U_grp.U h (resolventIntegralZ U_grp z φ) - resolventIntegralZ U_grp z φ))
      (𝓝[≠] 0) (𝓝 (z • resolventIntegralZ U_grp z φ + φ)) := by
  have h_compl : ({0} : Set ℝ)ᶜ = Set.Ioi 0 ∪ Set.Iio 0 := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_Ioi, Set.mem_Iio]
    constructor
    · intro hx; rcases lt_or_gt_of_ne hx with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rintro (h | h)
      · exact ne_of_gt h
      · exact ne_of_lt h
  rw [genZ_target_eq U_grp φ,
      show (𝓝[≠] (0 : ℝ)) = 𝓝[Set.Ioi 0 ∪ Set.Iio 0] 0 by rw [← h_compl], nhdsWithin_union]
  refine Tendsto.sup ?_ ?_
  · refine Tendsto.congr' ?_
      ((genZ_bulk_pos U_grp hz φ).add (tendsto_average_integral_expZ_unitary U_grp (z := z) φ))
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (genZ_diffQuotient_pos U_grp hz φ h hh).symm
  · rw [show -((I * z) • ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) + φ =
          φ + -((I * z) • ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) by abel]
    refine Tendsto.congr' ?_
      ((genZ_boundary_neg U_grp (z := z) φ).add (genZ_bulk_neg U_grp (z := z) φ))
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (genZ_diffQuotient_neg U_grp hz φ h hh).symm

end Spectra.Resolvent
