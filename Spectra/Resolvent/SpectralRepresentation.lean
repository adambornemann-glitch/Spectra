/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Kernel.Resolvent
import Spectra.Resolvent.Diagonal.IntegralZ.Basic
import Spectra.SpectralTheory.Measure.GeneratorLink
/-!
# Resolvent Spectral Representation (rebuilt on the constructed calculus)

This file establishes `R(z) = Φ((· − z)⁻¹)` for `Im z ≠ 0` — the bridge between the
resolvent (constructed via surjectivity of `A − z` and `solution_unique`) and the
bounded functional calculus (constructed via polarization and Riesz).  The old
Logos-Library version of this file took a spectral measure as a *hypothesis*
(`IsSpectralMeasureFor E gen`) and spent ~90 lines on domain bookkeeping; every input
is now a theorem, and the bookkeeping is absorbed by `generator_spectralCalculus`:

| old (hypothesis-driven)                  | new (constructed)                          |
| ---------------------------------------- | ------------------------------------------ |
| `resolvent_eq_boundedFunctionalCalculus` | `resolvent_eq_spectralCalculus`             |
| `resolvent_spectral_bilinear`            | `inner_resolvent_diag_eq_integral`          |
| `resolvent_im_spectral`                  | `im_inner_resolvent_diag`                   |
| `resolvent_spectral_integrable`          | subsumed by `integrable_of_bounded`         |
| `generator_domain_subset_id_domain` route| subsumed by `generator_spectralCalculus`    |

## Proof shape

The symbol `f_z(s) = (s − z)⁻¹` is **spectrally bounded**: both `f_z` and
`s·f_z(s) = s/(s − z)` are bounded (`id_mul_kernel_bdd`, via the pointwise identity
`s·f_z = 1 + z·f_z`).  So `generator_spectralCalculus` applies directly:

  `A (Φ(f_z)φ) = Φ(s·f_z)φ = Φ(1 + z·f_z)φ = φ + z • Φ(f_z)φ`,

i.e. `(A − z)(Φ(f_z)φ) = φ`, and `solution_unique` identifies `Φ(f_z)φ` with `R(z)φ`.

## Downstream (Stone's formula)

`im_inner_resolvent_diag` is the Poisson-kernel input consumed by Stone's formula: with
`Kernel.Lorentzian`/`Kernel.Arctan` (`Spectra.Kernels`) providing the arctan-averaged symbol,
one scalar Fubini on `[a,b] × μ_ξ` turns this pointwise identity into the averaged spectral
measure of `[a,b]`, and `tendsto_spectralCalculus_apply` along `𝓝[>] 0` closes the limit.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII
* [Schmüdgen, *Unbounded Self-adjoint Operators*][schmudgen2012], Chapter 5
-/
open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace
open Spectra.Borel Spectra.OneParameterUnitaryGroup
open SpectralMeasure
open Spectra.QuantumMechanics.SpectralTheory
open Spectra.Fourier  -- `integrable_of_bounded`
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Resolvent
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-! ## The resolvent symbol `f_z(s) = (s − z)⁻¹` -/

/-- `(s : ℂ) - z ≠ 0` for real `s` and `z` off the real axis. -/
lemma sub_ne_zero_of_im_ne_zero (z : ℂ) (hz : z.im ≠ 0) (s : ℝ) :
    (s : ℂ) - z ≠ 0 := by
  intro h
  have : ((s : ℂ) - z).im = -z.im := by simp
  simp only [h, zero_im, zero_eq_neg] at this
  exact hz this

/-- Measurability of the resolvent symbol. -/
lemma kernel_measurable (z : ℂ) (hz : z.im ≠ 0) :
    Measurable fun s : ℝ => ((s : ℂ) - z)⁻¹ :=
  ((Complex.continuous_ofReal.sub continuous_const).inv₀
    (fun s => sub_ne_zero_of_im_ne_zero z hz s)).measurable

/-- Canonical boundedness package for the resolvent symbol, from the shared kernel bound
`Spectra.Kernels.resolvent_integrand_bound`. -/
lemma kernel_bdd (z : ℂ) (hz : z.im ≠ 0) :
    ∃ C, ∀ s : ℝ, ‖((s : ℂ) - z)⁻¹‖ ≤ C :=
  ⟨1 / |z.im|, Spectra.Kernels.resolvent_integrand_bound z hz⟩

/-- Pointwise decomposition: `s · (s − z)⁻¹ = 1 + z · (s − z)⁻¹`. -/
lemma id_mul_kernel_decomp (z : ℂ) (hz : z.im ≠ 0) (s : ℝ) :
    (s : ℂ) * ((s : ℂ) - z)⁻¹ = 1 + z * ((s : ℂ) - z)⁻¹ := by
  have h_ne := sub_ne_zero_of_im_ne_zero z hz s
  field_simp; ring

/-- Measurability of `s ↦ s · (s − z)⁻¹`. -/
lemma id_mul_kernel_measurable (z : ℂ) (hz : z.im ≠ 0) :
    Measurable fun s : ℝ => (s : ℂ) * ((s : ℂ) - z)⁻¹ :=
  Complex.measurable_ofReal.mul (kernel_measurable z hz)

/-- The resolvent symbol is **spectrally bounded**:
`‖s · (s − z)⁻¹‖ ≤ 1 + ‖z‖/|Im z|`, via the decomposition. -/
lemma id_mul_kernel_bdd (z : ℂ) (hz : z.im ≠ 0) :
    ∃ C, ∀ s : ℝ, ‖(s : ℂ) * ((s : ℂ) - z)⁻¹‖ ≤ C := by
  refine ⟨1 + ‖z‖ / |z.im|, fun s => ?_⟩
  rw [id_mul_kernel_decomp z hz s]
  calc ‖1 + z * ((s : ℂ) - z)⁻¹‖
      ≤ ‖(1 : ℂ)‖ + ‖z * ((s : ℂ) - z)⁻¹‖ := norm_add_le _ _
    _ = 1 + ‖z‖ * ‖((s : ℂ) - z)⁻¹‖ := by simp only [NormOneClass.norm_one,
      Complex.norm_mul, norm_inv];
    _ ≤ 1 + ‖z‖ * (1 / |z.im|) := by
        gcongr
        exact Spectra.Kernels.resolvent_integrand_bound z hz s
    _ = 1 + ‖z‖ / |z.im| := by ring

/-! ## The bridge -/

/-- **The resolvent through the calculus**: `R(z) = Φ((· − z)⁻¹)` for `Im z ≠ 0`.

`J := Φ(f_z)φ` lies in the generator's domain (the symbol is spectrally bounded), and
`A J = Φ(s·f_z)φ = Φ(1 + z·f_z)φ = φ + z • J`, so `(A − z)J = φ`; `solution_unique`
identifies `J` with `R(z)φ` — the `resolventIntegralZ_eq_resolvent` idiom, with the
calculus in place of the Laplace integral. -/
theorem resolvent_eq_spectralCalculus (z : ℂ) (hz : z.im ≠ 0) :
    resolvent z hz (generator_isFormalAdjoint U_grp)
        (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp)
      = spectralCalculus U_grp (fun s : ℝ => ((s : ℂ) - z)⁻¹)
          (kernel_measurable z hz) (kernel_bdd z hz) := by
  refine ContinuousLinearMap.ext fun φ => ?_
  set J : H := spectralCalculus U_grp (fun s : ℝ => ((s : ℂ) - z)⁻¹)
    (kernel_measurable z hz) (kernel_bdd z hz) φ with hJ_def
  -- `J ∈ D(A)`: the symbol is spectrally bounded.
  have hmem : J ∈ (generator U_grp).domain :=
    spectralCalculus_mem_generatorDomain U_grp _ (kernel_measurable z hz) (kernel_bdd z hz)
      (id_mul_kernel_measurable z hz) (id_mul_kernel_bdd z hz) φ
  -- `A J = Φ(s·f_z)φ`.
  have hval : generator U_grp ⟨J, hmem⟩
      = spectralCalculus U_grp (fun s : ℝ => (s : ℂ) * ((s : ℂ) - z)⁻¹)
          (id_mul_kernel_measurable z hz) (id_mul_kernel_bdd z hz) φ :=
    generator_spectralCalculus U_grp _ (kernel_measurable z hz) (kernel_bdd z hz)
      (id_mul_kernel_measurable z hz) (id_mul_kernel_bdd z hz) φ
  -- Symbol bookkeeping for the split `s·f_z = 1 + z·f_z`.
  have hzm : Measurable fun s : ℝ => z * ((s : ℂ) - z)⁻¹ :=
    measurable_const.mul (kernel_measurable z hz)
  have hzb : ∃ C, ∀ s : ℝ, ‖z * ((s : ℂ) - z)⁻¹‖ ≤ C :=
    bounded_mul (g₁ := fun _ => z) ⟨‖z‖, fun _ => le_rfl⟩ (kernel_bdd z hz)
  have hsm : Measurable fun s : ℝ => (1 : ℂ) + z * ((s : ℂ) - z)⁻¹ :=
    measurable_const.add hzm
  have hsb : ∃ C, ∀ s : ℝ, ‖(1 : ℂ) + z * ((s : ℂ) - z)⁻¹‖ ≤ C :=
    bounded_add ⟨1, fun _ => norm_one.le⟩ hzb
  have hfun : (fun s : ℝ => (s : ℂ) * ((s : ℂ) - z)⁻¹)
      = fun s : ℝ => (1 : ℂ) + z * ((s : ℂ) - z)⁻¹ :=
    funext fun s => id_mul_kernel_decomp z hz s
  -- `Φ(s·f_z) = 1 + z • Φ(f_z)`.
  have hsplit : spectralCalculus U_grp (fun s : ℝ => (s : ℂ) * ((s : ℂ) - z)⁻¹)
        (id_mul_kernel_measurable z hz) (id_mul_kernel_bdd z hz)
      = ContinuousLinearMap.id ℂ H
        + z • spectralCalculus U_grp (fun s : ℝ => ((s : ℂ) - z)⁻¹)
            (kernel_measurable z hz) (kernel_bdd z hz) := by
    rw [spectralCalculus_congr U_grp hfun (id_mul_kernel_measurable z hz)
        (id_mul_kernel_bdd z hz) hsm hsb,
      spectralCalculus_one_add_smul U_grp z _ (kernel_measurable z hz) (kernel_bdd z hz)
        hzm hzb hsm hsb]
  -- Hence `(A − z) J = φ`.
  have hAJ : generator U_grp ⟨J, hmem⟩ - z • J = φ := by
    have happ := congrArg (fun T : H →L[ℂ] H => T φ) hsplit
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply] at happ
    rw [hval, happ, ← hJ_def]
    abel
  -- Uniqueness of solutions to `(A − z)· = φ` — the `resolventIntegralZ` idiom.
  let R_sub : (generator U_grp).domain :=
    Classical.choose
      (self_adjoint_range_all_z (generator_isFormalAdjoint U_grp)
        (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) z hz φ).exists
  have hR_eq : generator U_grp R_sub - z • (R_sub : H) = φ :=
    Classical.choose_spec
      (self_adjoint_range_all_z (generator_isFormalAdjoint U_grp)
        (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) z hz φ).exists
  have hR_res :
      resolvent z hz (generator_isFormalAdjoint U_grp)
        (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) φ = (R_sub : H) := rfl
  have huniq : (⟨J, hmem⟩ : (generator U_grp).domain) = R_sub :=
    solution_unique (generator_isFormalAdjoint U_grp) z hz φ ⟨J, hmem⟩ R_sub hAJ hR_eq
  rw [hR_res]
  exact (congrArg Subtype.val huniq).symm

/-! ## The diagonal -/

/-- **Spectral representation of the resolvent diagonal**:
`⟪ξ, R(z)ξ⟫ = ∫ (s − z)⁻¹ dμ_ξ`.  The old conjugation gymnastics vanish because
`inner_spectralCalculus` already carries the operator in the second slot. -/
theorem inner_resolvent_diag_eq_integral (z : ℂ) (hz : z.im ≠ 0) (ξ : H) :
    ⟪ξ, resolvent z hz (generator_isFormalAdjoint U_grp)
        (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) ξ⟫_ℂ
      = ∫ s, ((s : ℂ) - z)⁻¹ ∂(borelMeasure U_grp ξ) := by
  rw [resolvent_eq_spectralCalculus U_grp z hz, inner_spectralCalculus,
    spectralForm_self U_grp ξ (kernel_measurable z hz) (kernel_bdd z hz)]

/-- **The Poisson/Lorentzian representation** — the input to Stone's formula:
`Im ⟪ξ, R(t + iε)ξ⟫ = ∫ ε/((s − t)² + ε²) dμ_ξ(s)` for `ε > 0`. -/
theorem im_inner_resolvent_diag (t : ℝ) {ε : ℝ} (hε : 0 < ε) (ξ : H) :
    (⟪ξ, resolvent (⟨t, ε⟩ : ℂ) hε.ne' (generator_isFormalAdjoint U_grp)
        (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) ξ⟫_ℂ).im
      = ∫ s, ε / ((s - t) ^ 2 + ε ^ 2) ∂(borelMeasure U_grp ξ) := by
  haveI : IsFiniteMeasure (borelMeasure U_grp ξ) := borelMeasure_isFiniteMeasure U_grp ξ
  have hint : Integrable (fun s : ℝ => ((s : ℂ) - ⟨t, ε⟩)⁻¹) (borelMeasure U_grp ξ) :=
    integrable_of_bounded (kernel_measurable _ hε.ne') (kernel_bdd _ hε.ne').choose_spec
  rw [inner_resolvent_diag_eq_integral U_grp (⟨t, ε⟩ : ℂ) hε.ne' ξ,
  ← Complex.imCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.imCLM hint]
  refine integral_congr_ae (.of_forall fun s => ?_)
  simp only [Complex.imCLM_apply, Complex.inv_im]
  -- Pointwise: `Im (s − (t + iε))⁻¹ = ε/((s − t)² + ε²)`.
  have h_im : ((s : ℂ) - ⟨t, ε⟩).im = -ε := by
    rw [Complex.sub_im, Complex.ofReal_im]
    change (0 : ℝ) - ε = -ε
    ring
  have h_sq : Complex.normSq ((s : ℂ) - ⟨t, ε⟩) = (s - t) ^ 2 + ε ^ 2 := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im]
    change (s - t) * (s - t) + ((0 : ℝ) - ε) * ((0 : ℝ) - ε) = (s - t) ^ 2 + ε ^ 2
    ring
  rw [h_im, h_sq, neg_neg]

end Spectra.Resolvent
