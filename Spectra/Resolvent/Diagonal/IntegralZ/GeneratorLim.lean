/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Diagonal.IntegralZ.DiffQuotient
import Spectra.Resolvent.Diagonal.IntegralZ.Bulk

/-!
# The generator-recovery limit for the general-`z` resolvent integral

This file assembles the boundary and bulk limits from `DiffQuotient.lean` and `Bulk.lean` into the
headline generator identity for the general-`z` resolvent integral `resolventIntegralZ`: the
two-sided limit of its difference quotient at `h = 0` lands on `z • R(z)φ + φ`, i.e.
`resolventIntegralZ` really is (an integral representation of) the resolvent `R(z) = (A - z)⁻¹` of
the generator `A` of `U_grp`.

The `𝓝[≠] 0`-splits-into-`Ioi 0 ∪ Iio 0` architecture in `generator_limit_resolventIntegralZ`
mirrors the standard two-sided-derivative pattern used throughout the Stone/Hille–Yosida
generator-recovery arguments elsewhere in `Resolvent/`: a genuine two-sided limit is established by
proving the right- and left-sided limits separately and gluing them with `Tendsto.sup`.

## Main statements

* `generator_limit_resolventIntegralZ` — the difference-quotient limit
  `((Ih)⁻¹ • (U(h)R(z)φ − R(z)φ)) → z • R(z)φ + φ` as `h → 0` through `𝓝[≠] 0`.
-/

open Complex Filter Topology
open Spectra.OneParameterUnitaryGroup
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.Resolvent

variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- As `h → 0⁻`, the boundary term
`-(h)⁻¹ • cexp(I*z*h) • ∫_{(h,0]} cexp(-(I*z*t)) • U(t)φ dt` tends to `φ`. Used only in
`generator_limit_resolventIntegralZ`'s left-sided branch. -/
private lemma genZ_boundary_neg {z : ℂ} (φ : H) :
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
  filter_upwards [self_mem_nhdsWithin] with h _hh
  rw [smul_comm, @inv_neg]

/-- The **generator-recovery limit**: the difference-quotient limit of `resolventIntegralZ` lands
on `z • R(z)φ + φ`. -/
lemma generator_limit_resolventIntegralZ {z : ℂ} (hz : z.im < 0) (φ : H) :
    Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) •
        (U_grp.U h (resolventIntegralZ U_grp z φ) - resolventIntegralZ U_grp z φ))
      (𝓝[≠] 0) (𝓝 (z • resolventIntegralZ U_grp z φ + φ)) := by
  have h_compl : ({0} : Set ℝ)ᶜ = Set.Ioi 0 ∪ Set.Iio 0 := by
    rw [Set.union_comm, Set.Iio_union_Ioi]
  rw [genZ_target_eq U_grp φ,
      show (𝓝[≠] (0 : ℝ)) = 𝓝[Set.Ioi 0 ∪ Set.Iio 0] 0 by rw [← h_compl], nhdsWithin_union]
  refine Tendsto.sup ?_ ?_
  · refine Tendsto.congr' ?_
      ((genZ_bulk_pos U_grp hz φ).add (tendsto_average_integral_expZ_unitary U_grp (z := z) φ))
    filter_upwards [self_mem_nhdsWithin] with h hmem
    exact (genZ_diffQuotient_pos U_grp hz φ h hmem).symm
  · rw [show -((I * z) • ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) + φ =
          φ + -((I * z) • ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) by abel]
    refine Tendsto.congr' ?_
      ((genZ_boundary_neg U_grp (z := z) φ).add (genZ_bulk_neg U_grp (z := z) φ))
    filter_upwards [self_mem_nhdsWithin] with h hne
    exact (genZ_diffQuotient_neg U_grp hz φ h hne).symm

end Spectra.Resolvent
