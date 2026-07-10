/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.CayleyTransform.Defs        -- cayleyTransform, *_isStarNormal, *_unitary
import Spectra.CayleyTransform.Mobius           -- inverseMobius, inverseMobius_real
import Spectra.CayleyTransform.RieszMarkov       -- Riesz.spectralMeasure + cfcHom bridge
import Spectra.ProjValMeasure.PdInterface       -- crossInner, crossInner_norm_le (generic Ω)
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed  -- finite-measure uniqueness on σ(U)
import Mathlib.Analysis.InnerProductSpace.Dual              -- continuousLinearMapOfBilin (Riesz)
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap  -- integral_withDensity_eq_integral_smul
/-!
# Bounded Borel functional calculus of a normal operator, and Stone's group in spectral order

This file builds `e^{itA}` for a self-adjoint `A` *from* the spectral theory of its
Cayley transform `V = (A - i)(A + i)⁻¹`, rather than from the Yosida exponential.
This is the construction in Stone's 1932 order: spectral resolution first, group as
its corollary.

## Why a *Borel* calculus is required

`e^{itA}` pulls back, through the inverse Cayley (Möbius) map, to the symbol
`w ↦ exp (i t · inverseMobius w)` on `spectrum ℂ V ⊆ circle`.  That symbol is
unimodular but **discontinuous at `w = 1`**, and `1 ∈ spectrum ℂ V` exactly when `A`
is unbounded.  Mathlib's continuous functional calculus (`cfcHom`) demands continuity
on the spectrum, so it cannot evaluate this symbol; the bounded Borel extension below
is what is needed.

## Construction

The Borel calculus is assembled from the pieces already in the library:

* the spectral measure of `V` is `Spectra.Riesz.spectralMeasure V hn ξ`
  (`Measure (spectrum ℂ V)`), finite, with mass `‖ξ‖ ^ 2`;
* `Spectra.Riesz.integral_spectralMeasure_complex` / `inner_cfcHom_polarized`
  pin its agreement with `cfcHom` on continuous symbols;
* `Spectra.Riesz.norm_inner_cfcHom_le` gives the contraction bound.

`borelForm` is the polarized sesquilinear form against this measure (the analogue of
`crossInner` for a `Measure (spectrum ℂ V)`); `borelCalculus` is the bounded operator
it represents.  The single lemma with analytic weight is `borelCalculus_mul`
(multiplicativity on bounded Borel functions); it is free on continuous symbols and
extends by simple-function approximation + bounded convergence (`tendsto_borelCalculus_apply`).

## References

* Stone, "Linear Transformations in Hilbert Space" (1932), Chapter V.
* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], §VII–VIII.
-/

open Complex MeasureTheory Filter Topology InnerProductSpace
open scoped InnerProductSpace ComplexConjugate ENNReal NNReal
open Spectra Spectra.Cayley Spectra.Riesz
open Spectra.Operator
open SelfAdjointOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.BorelCFC

/-! ## §1  The bounded Borel functional calculus of a normal operator -/

variable (U : H →L[ℂ] H) (hn : IsStarNormal U)

/-- The polarized sesquilinear form of a bounded Borel symbol `g` against the spectral
measure of `U`.  Mirrors `Spectra.Riesz.inner_cfcHom_polarized`, with the continuous
symbol replaced by an arbitrary measurable one. -/
noncomputable def borelForm (g : spectrum ℂ U → ℂ) (ξ η : H) : ℂ :=
  ( (∫ z, g z ∂(spectralMeasure U hn (ξ + η)))
    - (∫ z, g z ∂(spectralMeasure U hn (ξ - η)))
    - I * (∫ z, g z ∂(spectralMeasure U hn (ξ + I • η)))
    + I * (∫ z, g z ∂(spectralMeasure U hn (ξ - I • η))) ) / 4

/-! ### The separating engine on the (compact) spectrum

The Fourier separation used for measures on `ℝ` (`borel_combination_ext`) is replaced here
by Riesz uniqueness: continuous functions separate finite Borel measures on the *compact*
`spectrum ℂ U`.  These three lemmas are the exact analogue of `borel_combination_ext`. -/

variable {ι : Type*} [Fintype ι]

omit [CompleteSpace H] in
/-- A bounded measurable `ℂ`-valued symbol is integrable against a finite measure. -/
private lemma integrable_of_bdd {ν : Measure (spectrum ℂ U)} [IsFiniteMeasure ν]
    {g : spectrum ℂ U → ℂ} (hg : Measurable g) {C : ℝ} (hC : ∀ z, ‖g z‖ ≤ C) :
    Integrable g ν :=
  (integrable_const C).mono' hg.aestronglyMeasurable (.of_forall hC)

omit [CompleteSpace H] in
/-- A bounded measurable `ℝ`-valued symbol is integrable against a finite measure. -/
private lemma integrable_of_bdd_real {ν : Measure (spectrum ℂ U)} [IsFiniteMeasure ν]
    {g : spectrum ℂ U → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ z, ‖g z‖ ≤ C) :
    Integrable g ν :=
  (integrable_const C).mono' hg.aestronglyMeasurable (.of_forall hC)

omit [CompleteSpace H] in
/-- **Real separating engine.** A real combination of finite spectral measures that
integrates every continuous *real* test function to `0` integrates every bounded
measurable real function to `0`.  (Positive/negative parts + Riesz uniqueness.) -/
lemma combination_ext_zero_real
    (M : ι → Measure (spectrum ℂ U)) [∀ i, IsFiniteMeasure (M i)] (a : ι → ℝ)
    (hcont : ∀ f : C(spectrum ℂ U, ℝ), ∑ i, a i * ∫ z, f z ∂(M i) = 0)
    {g : spectrum ℂ U → ℝ} (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ z, ‖g z‖ ≤ C) :
    ∑ i, a i * ∫ z, g z ∂(M i) = 0 := by
  classical
  obtain ⟨C, hC⟩ := hg_bdd
  set P : Measure (spectrum ℂ U) := ∑ i, (Real.toNNReal (a i)) • M i with hP
  set N : Measure (spectrum ℂ U) := ∑ i, (Real.toNNReal (-(a i))) • M i with hN
  haveI hPfin : IsFiniteMeasure P := by
    refine ⟨?_⟩
    rw [hP, Measure.finsetSum_apply]
    refine ENNReal.sum_lt_top.mpr fun i _ => ?_
    rw [Measure.smul_apply]
    exact ENNReal.nnreal_smul_lt_top (measure_lt_top (M i) _)
  haveI hNfin : IsFiniteMeasure N := by
    refine ⟨?_⟩
    rw [hN, Measure.finsetSum_apply]
    refine ENNReal.sum_lt_top.mpr fun i _ => ?_
    rw [Measure.smul_apply]
    exact ENNReal.nnreal_smul_lt_top (measure_lt_top (M i) _)
  have hint : ∀ (h : spectrum ℂ U → ℝ), Measurable h → (∀ z, ‖h z‖ ≤ C) →
      ∀ (b : ι → ℝ),
        (∫ z, h z ∂(∑ i, (Real.toNNReal (b i)) • M i))
          = ∑ i, (max (b i) 0) * ∫ z, h z ∂(M i) := by
    intro h hh_meas hh_bdd b
    rw [integral_finsetSum_measure (fun i _ => by
      haveI : IsFiniteMeasure ((Real.toNNReal (b i)) • M i) := inferInstance
      exact integrable_of_bdd_real U hh_meas hh_bdd)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal']
  have hPN : P = N := by
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun φ => ?_
    obtain ⟨C', hC'⟩ : ∃ C', ∀ z, ‖φ z‖ ≤ C' := ⟨‖φ‖, fun z => φ.norm_coe_le_norm z⟩
    have hintφ : ∀ (b : ι → ℝ),
        (∫ z, φ z ∂(∑ i, (Real.toNNReal (b i)) • M i))
          = ∑ i, (max (b i) 0) * ∫ z, φ z ∂(M i) := by
      intro b
      rw [integral_finsetSum_measure (fun i _ => by
        haveI : IsFiniteMeasure ((Real.toNNReal (b i)) • M i) := inferInstance
        exact integrable_of_bdd_real U φ.continuous.measurable hC')]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal']
    rw [hP, hN, hintφ, hintφ]
    have hcontφ : ∑ i, a i * ∫ z, φ z ∂(M i) = 0 := by
      have := hcont ⟨fun z => φ z, φ.continuous⟩
      simpa using this
    have hsplit : ∀ i, max (a i) 0 * (∫ z, φ z ∂(M i))
        = a i * (∫ z, φ z ∂(M i)) + max (-(a i)) 0 * (∫ z, φ z ∂(M i)) := by
      intro i
      have : max (a i) 0 = a i + max (-(a i)) 0 := by
        rcases le_total 0 (a i) with h | h
        · rw [max_eq_left h, max_eq_right (by linarith)]; ring
        · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      rw [this]; ring
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib, hcontφ, zero_add]
  have key : (∫ z, g z ∂P) = (∫ z, g z ∂N) := by rw [hPN]
  rw [hP, hN, hint g hg_meas hC a, hint g hg_meas hC (fun i => -(a i))] at key
  have hcancel : ∑ i, max (a i) 0 * ∫ z, g z ∂(M i)
       = ∑ i, max (-(a i)) 0 * ∫ z, g z ∂(M i) := key
  have hgoal : ∑ i, a i * ∫ z, g z ∂(M i)
      = ∑ i, max (a i) 0 * ∫ z, g z ∂(M i) - ∑ i, max (-(a i)) 0 * ∫ z, g z ∂(M i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hmax : a i = max (a i) 0 - max (-(a i)) 0 := by
      rcases le_total 0 (a i) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    linear_combination (∫ z, g z ∂(M i)) * hmax
  rw [hgoal, hcancel, sub_self]

omit [CompleteSpace H] in
/-- **Complex separating engine.** A complex combination of finite spectral measures that
integrates every continuous symbol to `0` integrates every bounded measurable symbol to `0`. -/
lemma combination_ext_zero
    (M : ι → Measure (spectrum ℂ U)) [∀ i, IsFiniteMeasure (M i)] (e : ι → ℂ)
    (hcont : ∀ f : C(spectrum ℂ U, ℂ), ∑ i, e i * ∫ z, f z ∂(M i) = 0)
    {g : spectrum ℂ U → ℂ} (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ z, ‖g z‖ ≤ C) :
    ∑ i, e i * ∫ z, g z ∂(M i) = 0 := by
  obtain ⟨C, hC⟩ := hg_bdd
  have hcont_real : ∀ (f : C(spectrum ℂ U, ℝ)),
      ∑ i, e i * ((∫ z, f z ∂(M i) : ℝ) : ℂ) = 0 := by
    intro f
    have h := hcont ⟨fun z => (f z : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
    simpa only [ContinuousMap.coe_mk, integral_complex_ofReal] using h
  have hRe : ∀ f : C(spectrum ℂ U, ℝ), ∑ i, (e i).re * ∫ z, f z ∂(M i) = 0 := by
    intro f
    have h := congrArg Complex.re (hcont_real f)
    simpa [Complex.re_sum, Complex.mul_re] using h
  have hIm : ∀ f : C(spectrum ℂ U, ℝ), ∑ i, (e i).im * ∫ z, f z ∂(M i) = 0 := by
    intro f
    have h := congrArg Complex.im (hcont_real f)
    simpa [Complex.im_sum, Complex.mul_im] using h
  have hgre_meas : Measurable fun z => (g z).re := Complex.measurable_re.comp hg_meas
  have hgim_meas : Measurable fun z => (g z).im := Complex.measurable_im.comp hg_meas
  have hgre_bdd : ∃ C', ∀ z, ‖(g z).re‖ ≤ C' :=
    ⟨C, fun z => (Real.norm_eq_abs _ ▸ (Complex.abs_re_le_norm (g z))).trans (hC z)⟩
  have hgim_bdd : ∃ C', ∀ z, ‖(g z).im‖ ≤ C' :=
    ⟨C, fun z => (Real.norm_eq_abs _ ▸ (Complex.abs_im_le_norm (g z))).trans (hC z)⟩
  have hRe_re := combination_ext_zero_real U M (fun i => (e i).re) hRe hgre_meas hgre_bdd
  have hRe_im := combination_ext_zero_real U M (fun i => (e i).re) hRe hgim_meas hgim_bdd
  have hIm_re := combination_ext_zero_real U M (fun i => (e i).im) hIm hgre_meas hgre_bdd
  have hIm_im := combination_ext_zero_real U M (fun i => (e i).im) hIm hgim_meas hgim_bdd
  have S1 : ∑ i, ((e i).re : ℂ) * ((∫ z, (g z).re ∂(M i) : ℝ) : ℂ) = 0 := by exact_mod_cast hRe_re
  have S2 : ∑ i, ((e i).im : ℂ) * ((∫ z, (g z).im ∂(M i) : ℝ) : ℂ) = 0 := by exact_mod_cast hIm_im
  have S3 : ∑ i, ((e i).re : ℂ) * ((∫ z, (g z).im ∂(M i) : ℝ) : ℂ) = 0 := by exact_mod_cast hRe_im
  have S4 : ∑ i, ((e i).im : ℂ) * ((∫ z, (g z).re ∂(M i) : ℝ) : ℂ) = 0 := by exact_mod_cast hIm_re
  have hgsplit : ∀ i, (∫ z, g z ∂(M i))
      = ((∫ z, (g z).re ∂(M i) : ℝ) : ℂ) + I * ((∫ z, (g z).im ∂(M i) : ℝ) : ℂ) := by
    intro i
    have hre_meas : Measurable fun z => ((g z).re : ℂ) := Complex.measurable_ofReal.comp hgre_meas
    have him_meas : Measurable fun z => ((g z).im : ℂ) := Complex.measurable_ofReal.comp hgim_meas
    have hre_bdd : ∀ z, ‖((g z).re : ℂ)‖ ≤ C := fun z => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact (Complex.abs_re_le_norm (g z)).trans (hC z)
    have him_bdd : ∀ z, ‖((g z).im : ℂ)‖ ≤ C := fun z => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact (Complex.abs_im_le_norm (g z)).trans (hC z)
    have hfun : (fun z => g z) = fun z => ((g z).re : ℂ) + I * ((g z).im : ℂ) := by
      funext z; rw [mul_comm]; exact (Complex.re_add_im (g z)).symm
    calc (∫ z, g z ∂(M i))
        = ∫ z, (((g z).re : ℂ) + I * ((g z).im : ℂ)) ∂(M i) := by rw [hfun]
      _ = (∫ z, ((g z).re : ℂ) ∂(M i)) + I * ∫ z, ((g z).im : ℂ) ∂(M i) := by
          rw [integral_add (integrable_of_bdd U hre_meas hre_bdd)
            ((integrable_of_bdd U him_meas him_bdd).const_mul I), integral_const_mul]
      _ = ((∫ z, (g z).re ∂(M i) : ℝ) : ℂ) + I * ((∫ z, (g z).im ∂(M i) : ℝ) : ℂ) := by
          rw [integral_complex_ofReal, integral_complex_ofReal]
  have hgoal : ∑ i, e i * ∫ z, g z ∂(M i)
      = ∑ i, (((e i).re : ℂ) * ((∫ z, (g z).re ∂(M i) : ℝ) : ℂ)
          - ((e i).im : ℂ) * ((∫ z, (g z).im ∂(M i) : ℝ) : ℂ)
          + I * (((e i).re : ℂ) * ((∫ z, (g z).im ∂(M i) : ℝ) : ℂ)
              + ((e i).im : ℂ) * ((∫ z, (g z).re ∂(M i) : ℝ) : ℂ))) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have he : e i = ((e i).re : ℂ) + I * ((e i).im : ℂ) := by
      rw [mul_comm]; exact (Complex.re_add_im (e i)).symm
    conv_lhs => rw [hgsplit i, he]
    linear_combination (((e i).im : ℂ) * ((∫ z, (g z).im ∂(M i) : ℝ) : ℂ)) * Complex.I_mul_I
  rw [hgoal, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_add_distrib, S1, S2, S3, S4]
  ring

/-- **Two-sided separating engine** in `cfcHom` form — the exact analogue of
`borel_combination_ext`: two complex combinations of diagonal spectral measures whose
`cfcHom`-matrix-element combinations agree on every continuous symbol have equal integrals
against every bounded measurable symbol. -/
lemma spectrum_combination_ext {n m : ℕ} (c : Fin n → ℂ) (v : Fin n → H)
    (d : Fin m → ℂ) (w : Fin m → H)
    (hcont : ∀ f : C(spectrum ℂ U, ℂ),
        ∑ i, c i * ⟪v i, cfcHom hn f (v i)⟫_ℂ = ∑ j, d j * ⟪w j, cfcHom hn f (w j)⟫_ℂ)
    {g : spectrum ℂ U → ℂ} (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ z, ‖g z‖ ≤ C) :
    ∑ i, c i * ∫ z, g z ∂(spectralMeasure U hn (v i))
      = ∑ j, d j * ∫ z, g z ∂(spectralMeasure U hn (w j)) := by
  haveI hfin : ∀ x : Fin n ⊕ Fin m,
      IsFiniteMeasure (Sum.elim (fun i => spectralMeasure U hn (v i))
        (fun j => spectralMeasure U hn (w j)) x) := by
    rintro (i | j)
    · exact instIsFiniteMeasure_spectralMeasure U hn (v i)
    · exact instIsFiniteMeasure_spectralMeasure U hn (w j)
  have key := combination_ext_zero U
    (Sum.elim (fun i => spectralMeasure U hn (v i)) (fun j => spectralMeasure U hn (w j)))
    (Sum.elim c (fun j => -(d j)))
    (fun f => by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      have hcf := hcont f
      simp only [← integral_spectralMeasure_complex] at hcf
      rw [← sub_eq_zero] at hcf
      rw [← hcf]
      simp only [neg_mul, Finset.sum_neg_distrib]
      ring)
    hg_meas hg_bdd
  rw [Fintype.sum_sum_type] at key
  simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at key
  linear_combination key

/-! ### Density engine

The engines above are extended to carry bounded-measurable densities, by absorbing the `±`
parts of each density into `Measure.withDensity` measures and reducing to the density-free
engines.  This is what the multiplicativity keystone (`borelForm_calculus_right`) consumes. -/

omit [CompleteSpace H] in
/-- Products of real bounded measurable functions are integrable against a finite measure. -/
private lemma integrable_mul_real {ν : Measure (spectrum ℂ U)} [IsFiniteMeasure ν]
    {a b : spectrum ℂ U → ℝ} (ha_meas : Measurable a) (ha_bdd : ∃ C, ∀ z, ‖a z‖ ≤ C)
    (hb_meas : Measurable b) (hb_bdd : ∃ C, ∀ z, ‖b z‖ ≤ C) :
    Integrable (fun z => a z * b z) ν := by
  obtain ⟨Ca, hCa⟩ := ha_bdd; obtain ⟨Cb, hCb⟩ := hb_bdd
  refine integrable_of_bdd_real U (ha_meas.mul hb_meas) (C := max Ca 0 * max Cb 0) fun z => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul ((Real.norm_eq_abs _ ▸ hCa z).trans (le_max_left _ _))
    ((Real.norm_eq_abs _ ▸ hCb z).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)

/-- **Real density engine.** A real family of bounded-measurable densities `w` against finite
spectral measures, integrating every continuous test function to `0`, integrates every bounded
measurable function to `0`. -/
lemma combination_ext_zero_real_density
    (M : ι → Measure (spectrum ℂ U)) [∀ i, IsFiniteMeasure (M i)]
    (w : ι → spectrum ℂ U → ℝ) (hw_meas : ∀ i, Measurable (w i))
    (hw_bdd : ∀ i, ∃ C, ∀ z, ‖w i z‖ ≤ C)
    (hcont : ∀ f : C(spectrum ℂ U, ℝ), ∑ i, ∫ z, f z * w i z ∂(M i) = 0)
    {g : spectrum ℂ U → ℝ} (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ z, ‖g z‖ ≤ C) :
    ∑ i, ∫ z, g z * w i z ∂(M i) = 0 := by
  classical
  set P : ι → Measure (spectrum ℂ U) :=
    fun i => (M i).withDensity (fun z => ((Real.toNNReal (w i z)) : ℝ≥0∞)) with hP
  set N : ι → Measure (spectrum ℂ U) :=
    fun i => (M i).withDensity (fun z => ((Real.toNNReal (-(w i z))) : ℝ≥0∞)) with hN
  have hfin : ∀ (v : ι → spectrum ℂ U → ℝ), (∀ i, ∃ C, ∀ z, ‖v i z‖ ≤ C) → ∀ i,
      IsFiniteMeasure ((M i).withDensity (fun z => ((Real.toNNReal (v i z)) : ℝ≥0∞))) := by
    intro v hv_bdd i
    obtain ⟨C, hC⟩ := hv_bdd i
    refine isFiniteMeasure_withDensity (ne_of_lt ?_)
    calc ∫⁻ z, ((Real.toNNReal (v i z)) : ℝ≥0∞) ∂(M i)
        ≤ ∫⁻ _, ((Real.toNNReal C) : ℝ≥0∞) ∂(M i) := by
          refine lintegral_mono fun z => ?_
          exact ENNReal.coe_le_coe.mpr (Real.toNNReal_le_toNNReal ((le_abs_self _).trans (hC z)))
      _ = (Real.toNNReal C) * (M i) Set.univ := by rw [lintegral_const]
      _ < ⊤ := ENNReal.mul_lt_top (by simp) (measure_lt_top (M i) _)
  haveI hPfin : ∀ i, IsFiniteMeasure (P i) := hfin w hw_bdd
  haveI hNfin : ∀ i, IsFiniteMeasure (N i) :=
    hfin (fun i z => -(w i z))
      (fun i => by obtain ⟨C, hC⟩ := hw_bdd i; exact ⟨C, fun z => by rw [norm_neg]; exact hC z⟩)
  have hwint : ∀ (s : ℝ) (h : spectrum ℂ U → ℝ), Measurable h → (∃ C, ∀ z, ‖h z‖ ≤ C) → ∀ i,
      Integrable (fun z => (Real.toNNReal (s * w i z)) • h z) (M i) := by
    intro s h hh_meas hh_bdd i
    obtain ⟨Ch, hCh0⟩ := hh_bdd
    obtain ⟨Cw0, hCw0'⟩ := hw_bdd i
    set Cw : ℝ := max Cw0 0 with _hCwdef
    have hCw : ∀ z, ‖w i z‖ ≤ Cw := fun z => (hCw0' z).trans (le_max_left _ _)
    have _hCw0 : 0 ≤ Cw := le_max_right _ _
    set Ch' : ℝ := max Ch 0 with _hChdef
    have hCh : ∀ z, ‖h z‖ ≤ Ch' := fun z => (hCh0 z).trans (le_max_left _ _)
    have _hCh0 : 0 ≤ Ch' := le_max_right _ _
    refine integrable_of_bdd_real U
      ((continuous_real_toNNReal.measurable.comp (measurable_const.mul (hw_meas i))).smul hh_meas)
      (C := |s| * Cw * Ch') fun z => ?_
    have hbz : (Real.toNNReal (s * w i z) : ℝ) ≤ |s| * Cw := by
      rw [Real.coe_toNNReal']
      refine max_le ?_ (by positivity)
      calc s * w i z ≤ |s * w i z| := le_abs_self _
        _ = |s| * |w i z| := abs_mul s _
        _ ≤ |s| * Cw := mul_le_mul_of_nonneg_left (Real.norm_eq_abs _ ▸ hCw z) (abs_nonneg _)
    rw [NNReal.smul_def, smul_eq_mul, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (NNReal.coe_nonneg _)]
    exact mul_le_mul hbz (Real.norm_eq_abs _ ▸ hCh z) (abs_nonneg _) (by positivity)
  have hdiff : ∀ (h : spectrum ℂ U → ℝ), Measurable h → (∃ C, ∀ z, ‖h z‖ ≤ C) → ∀ i,
      (∫ z, h z ∂(P i)) - ∫ z, h z ∂(N i) = ∫ z, h z * w i z ∂(M i) := by
    intro h hh_meas hh_bdd i
    simp only [hP, hN]
    rw [integral_withDensity_eq_integral_smul
        (f := fun z => Real.toNNReal (w i z))
        (continuous_real_toNNReal.measurable.comp (hw_meas i)) h,
      integral_withDensity_eq_integral_smul
        (f := fun z => Real.toNNReal (-(w i z)))
        (continuous_real_toNNReal.measurable.comp (hw_meas i).neg) h, ← integral_sub]
    · refine integral_congr_ae (.of_forall fun z => ?_)
      simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal']
      rcases le_total 0 (w i z) with hz | hz
      · rw [max_eq_left hz, max_eq_right (by linarith)]; ring
      · rw [max_eq_right hz, max_eq_left (by linarith)]; ring
    · simpa using hwint 1 h hh_meas hh_bdd i
    · simpa using hwint (-1) h hh_meas hh_bdd i
  haveI : ∀ x : ι ⊕ ι, IsFiniteMeasure (Sum.elim P N x) := by
    rintro (i | i)
    · exact hPfin i
    · exact hNfin i
  have hfold : ∀ (h : spectrum ℂ U → ℝ), Measurable h → (∃ C, ∀ z, ‖h z‖ ≤ C) →
      (∑ i, ((∫ z, h z ∂(P i)) + -∫ z, h z ∂(N i))) = ∑ i, ∫ z, h z * w i z ∂(M i) := by
    intro h hh_meas hh_bdd
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hdiff h hh_meas hh_bdd i]; ring
  have hcont' : ∀ f : C(spectrum ℂ U, ℝ),
      ∑ x : ι ⊕ ι, Sum.elim (fun _ => (1 : ℝ)) (fun _ => (-1 : ℝ)) x
        * ∫ z, f z ∂(Sum.elim P N x) = 0 := by
    intro f
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, one_mul, neg_one_mul]
    rw [← Finset.sum_add_distrib,
      hfold f f.continuous.measurable ⟨‖f‖, fun z => f.norm_coe_le_norm z⟩]
    exact hcont f
  have expand : (∑ x : ι ⊕ ι, Sum.elim (fun _ => (1 : ℝ)) (fun _ => (-1 : ℝ)) x
        * ∫ z, g z ∂(Sum.elim P N x)) = ∑ i, ∫ z, g z * w i z ∂(M i) := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, one_mul, neg_one_mul]
    rw [← Finset.sum_add_distrib, hfold g hg_meas hg_bdd]
  rw [← expand]
  exact combination_ext_zero_real U (Sum.elim P N)
    (Sum.elim (fun _ => (1 : ℝ)) (fun _ => (-1 : ℝ))) hcont' hg_meas hg_bdd

/-- **Complex density engine.** A complex family of bounded-measurable densities `k` against
finite spectral measures, integrating every continuous symbol to `0`, integrates every bounded
measurable symbol to `0`. -/
lemma combination_ext_zero_density
    (M : ι → Measure (spectrum ℂ U)) [∀ i, IsFiniteMeasure (M i)]
    (k : ι → spectrum ℂ U → ℂ) (hk_meas : ∀ i, Measurable (k i))
    (hk_bdd : ∀ i, ∃ C, ∀ z, ‖k i z‖ ≤ C)
    (hcont : ∀ f : C(spectrum ℂ U, ℂ), ∑ i, ∫ z, f z * k i z ∂(M i) = 0)
    {g : spectrum ℂ U → ℂ} (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ z, ‖g z‖ ≤ C) :
    ∑ i, ∫ z, g z * k i z ∂(M i) = 0 := by
  have hkre_meas : ∀ i, Measurable fun z => (k i z).re :=
    fun i => Complex.measurable_re.comp (hk_meas i)
  have hkim_meas : ∀ i, Measurable fun z => (k i z).im :=
    fun i => Complex.measurable_im.comp (hk_meas i)
  have hkre_bdd : ∀ i, ∃ C, ∀ z, ‖(k i z).re‖ ≤ C := fun i => by
    obtain ⟨C, hC⟩ := hk_bdd i
    exact ⟨C, fun z => (Real.norm_eq_abs _ ▸ Complex.abs_re_le_norm (k i z)).trans (hC z)⟩
  have hkim_bdd : ∀ i, ∃ C, ∀ z, ‖(k i z).im‖ ≤ C := fun i => by
    obtain ⟨C, hC⟩ := hk_bdd i
    exact ⟨C, fun z => (Real.norm_eq_abs _ ▸ Complex.abs_im_le_norm (k i z)).trans (hC z)⟩
  -- integral split `∫ (a:ℂ)·kᵢ = (∫ a·kᵢ.re) + I (∫ a·kᵢ.im)` for real bounded measurable `a`
  have hsplit : ∀ (a : spectrum ℂ U → ℝ), Measurable a → (∃ C, ∀ z, ‖a z‖ ≤ C) → ∀ i,
      (∫ z, (a z : ℂ) * k i z ∂(M i))
        = ((∫ z, a z * (k i z).re ∂(M i) : ℝ) : ℂ)
          + I * ((∫ z, a z * (k i z).im ∂(M i) : ℝ) : ℂ) := by
    intro a ha_meas ha_bdd i
    have hre_int := integrable_mul_real U ha_meas ha_bdd (hkre_meas i) (hkre_bdd i)
      (ν := M i)
    have him_int := integrable_mul_real U ha_meas ha_bdd (hkim_meas i) (hkim_bdd i)
      (ν := M i)
    have hfun : (fun z => (a z : ℂ) * k i z)
        = fun z => ((a z * (k i z).re : ℝ) : ℂ) + I * ((a z * (k i z).im : ℝ) : ℂ) := by
      funext z
      conv_lhs => rw [show k i z = ((k i z).re : ℂ) + I * ((k i z).im : ℂ) from by
        rw [mul_comm]; exact (Complex.re_add_im (k i z)).symm]
      push_cast; ring
    rw [hfun, integral_add (f := fun z => ((a z * (k i z).re : ℝ) : ℂ))
        (g := fun z => I * ((a z * (k i z).im : ℝ) : ℂ))
        (hre_int.ofReal) (him_int.ofReal.const_mul I),
      integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]
  -- real-test hypotheses for the re/im density families
  have hReHyp : ∀ f : C(spectrum ℂ U, ℝ), ∑ i, ∫ z, f z * (k i z).re ∂(M i) = 0 := by
    intro f
    have hfc := hcont ⟨fun z => (f z : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
    simp only [ContinuousMap.coe_mk] at hfc
    have hsum : ∑ i, (((∫ z, f z * (k i z).re ∂(M i) : ℝ) : ℂ)
        + I * ((∫ z, f z * (k i z).im ∂(M i) : ℝ) : ℂ)) = 0 := by
      rw [← hfc]
      exact (Finset.sum_congr rfl fun i _ =>
        hsplit f f.continuous.measurable ⟨‖f‖, fun z => f.norm_coe_le_norm z⟩ i).symm
    have hre := congrArg Complex.re hsum
    simpa [Complex.re_sum, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im] using hre
  have hImHyp : ∀ f : C(spectrum ℂ U, ℝ), ∑ i, ∫ z, f z * (k i z).im ∂(M i) = 0 := by
    intro f
    have hfc := hcont ⟨fun z => (f z : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
    simp only [ContinuousMap.coe_mk] at hfc
    have hsum : ∑ i, (((∫ z, f z * (k i z).re ∂(M i) : ℝ) : ℂ)
        + I * ((∫ z, f z * (k i z).im ∂(M i) : ℝ) : ℂ)) = 0 := by
      rw [← hfc]
      exact (Finset.sum_congr rfl fun i _ =>
        hsplit f f.continuous.measurable ⟨‖f‖, fun z => f.norm_coe_le_norm z⟩ i).symm
    have him := congrArg Complex.im hsum
    simpa [Complex.im_sum, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im] using him
  -- the four real-engine conclusions
  have hgre_meas : Measurable fun z => (g z).re := Complex.measurable_re.comp hg_meas
  have hgim_meas : Measurable fun z => (g z).im := Complex.measurable_im.comp hg_meas
  obtain ⟨Cg, hCg⟩ := hg_bdd
  have hgre_bdd : ∃ C, ∀ z, ‖(g z).re‖ ≤ C :=
    ⟨Cg, fun z => (Real.norm_eq_abs _ ▸ Complex.abs_re_le_norm (g z)).trans (hCg z)⟩
  have hgim_bdd : ∃ C, ∀ z, ‖(g z).im‖ ≤ C :=
    ⟨Cg, fun z => (Real.norm_eq_abs _ ▸ Complex.abs_im_le_norm (g z)).trans (hCg z)⟩
  have hA := combination_ext_zero_real_density U M (fun i z => (k i z).re) hkre_meas hkre_bdd
    hReHyp hgre_meas hgre_bdd
  have hB := combination_ext_zero_real_density U M (fun i z => (k i z).im) hkim_meas hkim_bdd
    hImHyp hgim_meas hgim_bdd
  have hCc := combination_ext_zero_real_density U M (fun i z => (k i z).im) hkim_meas hkim_bdd
    hImHyp hgre_meas hgre_bdd
  have hDd := combination_ext_zero_real_density U M (fun i z => (k i z).re) hkre_meas hkre_bdd
    hReHyp hgim_meas hgim_bdd
  have S1 : ∑ i, ((∫ z, (g z).re * (k i z).re ∂(M i) : ℝ) : ℂ) = 0 := by exact_mod_cast hA
  have S2 : ∑ i, ((∫ z, (g z).im * (k i z).im ∂(M i) : ℝ) : ℂ) = 0 := by exact_mod_cast hB
  have S3 : ∑ i, ((∫ z, (g z).re * (k i z).im ∂(M i) : ℝ) : ℂ) = 0 := by exact_mod_cast hCc
  have S4 : ∑ i, ((∫ z, (g z).im * (k i z).re ∂(M i) : ℝ) : ℂ) = 0 := by exact_mod_cast hDd
  -- split the complex product `g·kᵢ` into the four real integrals
  have hgsplit : ∀ i, (∫ z, g z * k i z ∂(M i))
      = (((∫ z, (g z).re * (k i z).re ∂(M i) : ℝ) : ℂ)
          - ((∫ z, (g z).im * (k i z).im ∂(M i) : ℝ) : ℂ))
        + I * (((∫ z, (g z).re * (k i z).im ∂(M i) : ℝ) : ℂ)
          + ((∫ z, (g z).im * (k i z).re ∂(M i) : ℝ) : ℂ)) := by
    intro i
    -- decompose `g = g.re + I·g.im` and apply `hsplit` to each real part
    have hgre_int : Integrable (fun z => ((g z).re : ℂ) * k i z) (M i) := by
      obtain ⟨Ck, hCk⟩ := hk_bdd i
      refine integrable_of_bdd U ((Complex.measurable_ofReal.comp hgre_meas).mul (hk_meas i))
        (C := max Cg 0 * max Ck 0) fun z => ?_
      show ‖((g z).re : ℂ) * k i z‖ ≤ max Cg 0 * max Ck 0
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul ?_ ((hCk z).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
      exact ((Complex.abs_re_le_norm (g z)).trans (hCg z)).trans (le_max_left _ _)
    have hgim_int : Integrable (fun z => I * (((g z).im : ℂ) * k i z)) (M i) := by
      obtain ⟨Ck, hCk⟩ := hk_bdd i
      refine (integrable_of_bdd U ((Complex.measurable_ofReal.comp hgim_meas).mul (hk_meas i))
        (C := max Cg 0 * max Ck 0) fun z => ?_).const_mul I
      change ‖((g z).im : ℂ) * k i z‖ ≤ max Cg 0 * max Ck 0
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul ?_ ((hCk z).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
      exact ((Complex.abs_im_le_norm (g z)).trans (hCg z)).trans (le_max_left _ _)
    have hfun : (fun z => g z * k i z)
        = fun z => ((g z).re : ℂ) * k i z + I * (((g z).im : ℂ) * k i z) := by
      funext z
      conv_lhs => rw [show g z = ((g z).re : ℂ) + I * ((g z).im : ℂ) from by
        rw [mul_comm]; exact (Complex.re_add_im (g z)).symm]
      ring
    rw [hfun, integral_add hgre_int hgim_int, integral_const_mul,
      hsplit (fun z => (g z).re) hgre_meas hgre_bdd i,
      hsplit (fun z => (g z).im) hgim_meas hgim_bdd i]
    linear_combination ((∫ z, (g z).im * (k i z).im ∂(M i) : ℝ) : ℂ) * Complex.I_mul_I
  rw [Finset.sum_congr rfl (fun i _ => hgsplit i), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_add_distrib, S1, S2, S3, S4]
  ring

/-- **Two-sided density engine.** Two complex combinations of density-weighted diagonal spectral
measures agreeing (against `cfcHom`-style integrals) on every continuous symbol agree on every
bounded measurable symbol.  The weighted-measure keystone is an instance. -/
lemma spectrum_combination_ext_density {n m : ℕ}
    (c : Fin n → ℂ) (v : Fin n → H) (kc : Fin n → spectrum ℂ U → ℂ)
    (hkc_meas : ∀ i, Measurable (kc i)) (hkc_bdd : ∀ i, ∃ C, ∀ z, ‖kc i z‖ ≤ C)
    (d : Fin m → ℂ) (w : Fin m → H) (kd : Fin m → spectrum ℂ U → ℂ)
    (hkd_meas : ∀ j, Measurable (kd j)) (hkd_bdd : ∀ j, ∃ C, ∀ z, ‖kd j z‖ ≤ C)
    (hcont : ∀ f : C(spectrum ℂ U, ℂ),
        ∑ i, c i * ∫ z, f z * kc i z ∂(spectralMeasure U hn (v i))
          = ∑ j, d j * ∫ z, f z * kd j z ∂(spectralMeasure U hn (w j)))
    {g : spectrum ℂ U → ℂ} (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ z, ‖g z‖ ≤ C) :
    ∑ i, c i * ∫ z, g z * kc i z ∂(spectralMeasure U hn (v i))
      = ∑ j, d j * ∫ z, g z * kd j z ∂(spectralMeasure U hn (w j)) := by
  haveI hfin : ∀ x : Fin n ⊕ Fin m,
      IsFiniteMeasure (Sum.elim (fun i => spectralMeasure U hn (v i))
        (fun j => spectralMeasure U hn (w j)) x) := by
    rintro (i | j)
    · exact instIsFiniteMeasure_spectralMeasure U hn (v i)
    · exact instIsFiniteMeasure_spectralMeasure U hn (w j)
  -- pull constants out of each weighted integral
  have hL : ∀ (h : spectrum ℂ U → ℂ) i,
      (∫ z, h z * (c i * kc i z) ∂(spectralMeasure U hn (v i)))
        = c i * ∫ z, h z * kc i z ∂(spectralMeasure U hn (v i)) := by
    intro h i
    rw [← integral_const_mul]
    exact integral_congr_ae (.of_forall fun z => by ring)
  have hR : ∀ (h : spectrum ℂ U → ℂ) j,
      (∫ z, h z * (-(d j) * kd j z) ∂(spectralMeasure U hn (w j)))
        = -(d j * ∫ z, h z * kd j z ∂(spectralMeasure U hn (w j))) := by
    intro h j
    rw [show (∫ z, h z * (-(d j) * kd j z) ∂(spectralMeasure U hn (w j)))
          = ∫ z, -(d j * (h z * kd j z)) ∂(spectralMeasure U hn (w j)) from
        integral_congr_ae (.of_forall fun z => by ring), integral_neg, integral_const_mul]
  have key := combination_ext_zero_density U
    (Sum.elim (fun i => spectralMeasure U hn (v i)) (fun j => spectralMeasure U hn (w j)))
    (Sum.elim (fun i z => c i * kc i z) (fun j z => -(d j) * kd j z))
    (by
      rintro (i | j)
      · exact measurable_const.mul (hkc_meas i)
      · exact measurable_const.mul (hkd_meas j))
    (by
      rintro (i | j)
      · obtain ⟨C, hC⟩ := hkc_bdd i
        exact ⟨‖c i‖ * C, fun z => by
          rw [Sum.elim_inl, norm_mul]; exact mul_le_mul_of_nonneg_left (hC z) (norm_nonneg _)⟩
      · obtain ⟨C, hC⟩ := hkd_bdd j
        exact ⟨‖d j‖ * C, fun z => by
          rw [Sum.elim_inr, norm_mul, norm_neg]
          exact mul_le_mul_of_nonneg_left (hC z) (norm_nonneg _)⟩)
    (fun f => by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [Finset.sum_congr rfl (fun i _ => hL f i), Finset.sum_congr rfl (fun j _ => hR f j),
        Finset.sum_neg_distrib, hcont f]
      exact add_neg_cancel _)
    hg_meas hg_bdd
  rw [Fintype.sum_sum_type] at key
  simp only [Sum.elim_inl, Sum.elim_inr] at key
  rw [Finset.sum_congr rfl (fun i _ => hL g i), Finset.sum_congr rfl (fun j _ => hR g j),
    Finset.sum_neg_distrib] at key
  linear_combination key

/-- **Quadratic homogeneity of the spectral measure**: `μ_{c•ξ} = ‖c‖² • μ_ξ`.
Both sides integrate every continuous real test function to `‖c‖² · ∫ f dμ_ξ`; conclude by
Riesz uniqueness. -/
lemma spectralMeasure_smul (c : ℂ) (ξ : H) :
    spectralMeasure U hn (c • ξ) = (‖c‖₊ ^ 2) • spectralMeasure U hn ξ := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun φ => ?_
  set g : C(spectrum ℂ U, ℝ) := ⟨fun z => φ z, φ.continuous⟩ with _hg
  have hφg : ∀ ν : Measure (spectrum ℂ U), (∫ z, φ z ∂ν) = ∫ z, g z ∂ν := fun ν => rfl
  rw [hφg, hφg, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul,
    integral_spectralMeasure_continuous U hn (c • ξ) g,
    integral_spectralMeasure_continuous U hn ξ g]
  have hcc : (starRingEnd ℂ) c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by rw [RCLike.conj_mul]; norm_cast
  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, hcc, Complex.re_ofReal_mul]
  push_cast
  ring

/-- On the diagonal the form collapses to the spectral integral (uses the quadratic
homogeneity `μ (c • ξ) = ‖c‖ ^ 2 • μ ξ` of the spectral measure). -/
theorem borelForm_self (g : spectrum ℂ U → ℂ) (ξ : H) :
    borelForm U hn g ξ ξ = ∫ z, g z ∂(spectralMeasure U hn ξ) := by
  have key : ∀ c : ℂ, (∫ z, g z ∂(spectralMeasure U hn (c • ξ)))
      = (starRingEnd ℂ) c * c * ∫ z, g z ∂(spectralMeasure U hn ξ) := by
    intro c
    have hcc : (starRingEnd ℂ) c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by rw [RCLike.conj_mul]; norm_cast
    rw [spectralMeasure_smul, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul,
      hcc]
    norm_cast
  have e1 : ξ + ξ = (2 : ℂ) • ξ := (two_smul ℂ ξ).symm
  have e2 : ξ - ξ = (0 : ℂ) • ξ := by rw [zero_smul, sub_self]
  have e3 : ξ + I • ξ = ((1 : ℂ) + I) • ξ := by rw [add_smul, one_smul]
  have e4 : ξ - I • ξ = ((1 : ℂ) - I) • ξ := by rw [sub_smul, one_smul]
  simp only [borelForm]
  rw [e1, e2, e3, e4, key 2, key 0, key ((1 : ℂ) + I), key ((1 : ℂ) - I)]
  simp only [map_ofNat, map_zero, map_sub, map_add, map_one, Complex.conj_I]
  ring

/-- **Contraction bound for the form.** A one-line corollary of
`Spectra.ProjValMeasure.crossInner_norm_le`, instantiated at `Ω = spectrum ℂ U`: `borelForm` is
literally `crossInner (spectralMeasure U hn) g` up to the `(1/4)*(...)` vs `(...)/4` bracketing. -/
theorem norm_borelForm_le {g : spectrum ℂ U → ℂ} {C : ℝ}
    (hg : ∀ z, ‖g z‖ ≤ C) (ξ η : H) :
    ‖borelForm U hn g ξ η‖ ≤ C * (‖ξ‖ ^ 2 + ‖η‖ ^ 2) := by
  have hcross : borelForm U hn g ξ η
      = ProjValMeasure.crossInner (spectralMeasure U hn) g ξ η := by
    simp only [borelForm, ProjValMeasure.crossInner]; ring
  rw [hcross]
  exact ProjValMeasure.crossInner_norm_le (spectralMeasure U hn) hg (fun _ => inferInstance)
    (fun z => by rw [← measureReal_def]; exact spectralMeasure_real_univ U hn z) ξ η

/-- The form is sesquilinear: conjugate-linear in the left slot. -/
theorem borelForm_add_left (g : spectrum ℂ U → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ z, ‖g z‖ ≤ C) (ξ₁ ξ₂ η : H) :
    borelForm U hn g (ξ₁ + ξ₂) η = borelForm U hn g ξ₁ η + borelForm U hn g ξ₂ η := by
  have key := spectrum_combination_ext U hn
    (![1 / 4, -(1 / 4), -(I / 4), I / 4])
    (![ξ₁ + ξ₂ + η, ξ₁ + ξ₂ - η, ξ₁ + ξ₂ + I • η, ξ₁ + ξ₂ - I • η])
    (![1 / 4, -(1 / 4), -(I / 4), I / 4, 1 / 4, -(1 / 4), -(I / 4), I / 4])
    (![ξ₁ + η, ξ₁ - η, ξ₁ + I • η, ξ₁ - I • η, ξ₂ + η, ξ₂ - η, ξ₂ + I • η, ξ₂ - I • η])
    (fun f => by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, add_zero, map_add, map_sub, map_smul, inner_add_left,
        inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        Complex.conj_I]
      ring)
    hg_meas hg_bdd
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    add_zero] at key
  simp only [borelForm]
  linear_combination key

/-- Conjugate-homogeneity of the form in the left slot:
`borelForm g (c • ξ) η = c̄ · borelForm g ξ η`. -/
theorem borelForm_smul_left (g : spectrum ℂ U → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ z, ‖g z‖ ≤ C) (c : ℂ) (ξ η : H) :
    borelForm U hn g (c • ξ) η = conj c * borelForm U hn g ξ η := by
  have key := spectrum_combination_ext U hn
    (![1 / 4, -(1 / 4), -(I / 4), I / 4])
    (![c • ξ + η, c • ξ - η, c • ξ + I • η, c • ξ - I • η])
    (![(starRingEnd ℂ) c / 4, -((starRingEnd ℂ) c / 4),
        -((starRingEnd ℂ) c * I / 4), (starRingEnd ℂ) c * I / 4])
    (![ξ + η, ξ - η, ξ + I • η, ξ - I • η])
    (fun f => by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, add_zero, map_add, map_sub, map_smul, inner_add_left,
        inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        Complex.conj_I]
      linear_combination ((c - (starRingEnd ℂ) c) * ⟪η, cfcHom hn f ξ⟫_ℂ / 2)
        * Complex.I_mul_I)
    hg_meas hg_bdd
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    add_zero] at key
  simp only [borelForm]
  linear_combination key

/-- Additivity of the form in the right slot. -/
theorem borelForm_add_right (g : spectrum ℂ U → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ z, ‖g z‖ ≤ C) (ξ η₁ η₂ : H) :
    borelForm U hn g ξ (η₁ + η₂) = borelForm U hn g ξ η₁ + borelForm U hn g ξ η₂ := by
  have key := spectrum_combination_ext U hn
    (![1 / 4, -(1 / 4), -(I / 4), I / 4])
    (![ξ + (η₁ + η₂), ξ - (η₁ + η₂), ξ + I • (η₁ + η₂), ξ - I • (η₁ + η₂)])
    (![1 / 4, -(1 / 4), -(I / 4), I / 4, 1 / 4, -(1 / 4), -(I / 4), I / 4])
    (![ξ + η₁, ξ - η₁, ξ + I • η₁, ξ - I • η₁, ξ + η₂, ξ - η₂, ξ + I • η₂, ξ - I • η₂])
    (fun f => by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, add_zero, map_add, map_sub, map_smul, inner_add_left,
        inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        Complex.conj_I]
      ring)
    hg_meas hg_bdd
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    add_zero] at key
  simp only [borelForm]
  linear_combination key

/-- Homogeneity of the form in the right slot: `borelForm g ξ (c • η) = c · borelForm g ξ η`. -/
theorem borelForm_smul_right (g : spectrum ℂ U → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ z, ‖g z‖ ≤ C) (c : ℂ) (ξ η : H) :
    borelForm U hn g ξ (c • η) = c * borelForm U hn g ξ η := by
  have key := spectrum_combination_ext U hn
    (![1 / 4, -(1 / 4), -(I / 4), I / 4])
    (![ξ + c • η, ξ - c • η, ξ + I • (c • η), ξ - I • (c • η)])
    (![c / 4, -(c / 4), -(c * I / 4), c * I / 4])
    (![ξ + η, ξ - η, ξ + I • η, ξ - I • η])
    (fun f => by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, add_zero, map_add, map_sub, map_smul, inner_add_left,
        inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        Complex.conj_I]
      linear_combination (((starRingEnd ℂ) c - c) * ⟪η, cfcHom hn f ξ⟫_ℂ / 2)
        * Complex.I_mul_I)
    hg_meas hg_bdd
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    add_zero] at key
  simp only [borelForm]
  linear_combination key

/-- Homogenized (sesquilinear) form of the bound: `‖borelForm ξ η g‖ ≤ 2C‖ξ‖‖η‖`.
The crude `C(‖ξ‖²+‖η‖²)` is rescaled `η ↦ (‖ξ‖/‖η‖)•η` and optimized, exactly as in
`Spectra.QuantumMechanics.SpectralTheory.norm_spectralForm_le`. -/
theorem norm_borelForm_le' (g : spectrum ℂ U → ℂ)
    (hg_meas : Measurable g) {C : ℝ} (hg : ∀ z, ‖g z‖ ≤ C) (ξ η : H) :
    ‖borelForm U hn g ξ η‖ ≤ 2 * C * ‖ξ‖ * ‖η‖ := by
  have hmain : ∀ x y : H, ‖borelForm U hn g x y‖ ≤ C * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) := by
    intro x y
    have h := norm_borelForm_le U hn hg x y
    rwa [pow_two, pow_two] at h
  rcases eq_or_ne η 0 with rfl | hη
  · have h0 : borelForm U hn g ξ (0 : H) = 0 := by
      have h := borelForm_smul_right U hn g hg_meas ⟨C, hg⟩ (0 : ℂ) ξ (0 : H)
      simpa using h
    simp [h0]
  rcases eq_or_ne ξ 0 with rfl | hξ
  · have hneg : ∀ v : H, spectralMeasure U hn (-v) = spectralMeasure U hn v := by
      intro v
      have h := spectralMeasure_smul U hn (-1 : ℂ) v
      simpa using h
    have h0 : borelForm U hn g (0 : H) η = 0 := by
      simp only [borelForm, zero_add, zero_sub, hneg]
      ring
    simp [h0]
  have hξ0 : (0 : ℝ) < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hη0 : (0 : ℝ) < ‖η‖ := norm_pos_iff.mpr hη
  set t : ℝ := ‖ξ‖ / ‖η‖ with ht_def
  have ht : 0 < t := div_pos hξ0 hη0
  have hb := hmain ξ ((t : ℂ) • η)
  rw [borelForm_smul_right U hn g hg_meas ⟨C, hg⟩ (t : ℂ) ξ η, norm_mul, norm_smul,
    Complex.norm_of_nonneg ht.le] at hb
  have htη : t * ‖η‖ = ‖ξ‖ := by rw [ht_def]; exact div_mul_cancel₀ ‖ξ‖ hη0.ne'
  rw [htη] at hb
  have key : ‖borelForm U hn g ξ η‖ ≤ C * (‖ξ‖ * ‖ξ‖ + ‖ξ‖ * ‖ξ‖) / t :=
    (le_div_iff₀' ht).mpr hb
  refine key.trans (le_of_eq ?_)
  rw [ht_def, div_div_eq_mul_div, div_eq_iff hξ0.ne']
  ring

/-- The bounded sesquilinear form bundled, ready for Riesz representation
(the analogue of `spectralFormBilin`). -/
noncomputable def borelCalculusBilin (g : spectrum ℂ U → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ z, ‖g z‖ ≤ C) :
    H →L⋆[ℂ] H →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
      (fun ξ η => borelForm U hn g ξ η)
      (fun ξ₁ ξ₂ η => borelForm_add_left U hn g hg_meas hg_bdd ξ₁ ξ₂ η)
      (fun c ξ η => by
        rw [borelForm_smul_left U hn g hg_meas hg_bdd c ξ η, smul_eq_mul])
      (fun ξ η₁ η₂ => borelForm_add_right U hn g hg_meas hg_bdd ξ η₁ η₂)
      (fun c ξ η => by
        rw [borelForm_smul_right U hn g hg_meas hg_bdd c ξ η, RingHom.id_apply, smul_eq_mul]))
    (2 * hg_bdd.choose)
    (fun ξ η => norm_borelForm_le' U hn g hg_meas hg_bdd.choose_spec ξ η)

/-- The bundled form evaluates to the underlying `borelForm`. -/
@[simp] lemma borelCalculusBilin_apply (g : spectrum ℂ U → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ z, ‖g z‖ ≤ C) (ξ η : H) :
    borelCalculusBilin U hn g hg_meas hg_bdd ξ η = borelForm U hn g ξ η :=
  rfl

/-- **The bounded Borel functional calculus of `U`.**
`Φ_U(g) : H →L[ℂ] H` is the operator represented by `borelForm U hn g`.

`continuousLinearMapOfBilin` represents the form with the operator in the *first* slot
(`⟪B♯ ξ, η⟫ = B ξ η`); the adjoint flips it to the second, the orientation under which
`Φ(f) = cfcHom f` on continuous symbols (see `inner_borelCalculus`). -/
noncomputable def borelCalculus (g : spectrum ℂ U → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ z, ‖g z‖ ≤ C) : H →L[ℂ] H :=
  ContinuousLinearMap.adjoint
    (InnerProductSpace.continuousLinearMapOfBilin (borelCalculusBilin U hn g hg_meas hg_bdd))

/-- The characterizing property: matrix elements of `Φ_U(g)` are the polarized form. -/
theorem inner_borelCalculus (g : spectrum ℂ U → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ z, ‖g z‖ ≤ C) (ξ η : H) :
    ⟪ξ, borelCalculus U hn g hg_meas hg_bdd η⟫_ℂ = borelForm U hn g ξ η := by
  simp only [borelCalculus]
  rw [ContinuousLinearMap.adjoint_inner_right,
    InnerProductSpace.continuousLinearMapOfBilin_apply, borelCalculusBilin_apply]

/-- Diagonal form of the characterization. -/
theorem inner_borelCalculus_self (g : spectrum ℂ U → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ z, ‖g z‖ ≤ C) (ξ : H) :
    ⟪ξ, borelCalculus U hn g hg_meas hg_bdd ξ⟫_ℂ = ∫ z, g z ∂(spectralMeasure U hn ξ) := by
  rw [inner_borelCalculus, borelForm_self]

omit [CompleteSpace H] in
/-- Operators agreeing against all pairings are equal (left-slot separation). -/
private lemma borelCalculus_ext {A B : H →L[ℂ] H}
    (h : ∀ ξ η : H, ⟪ξ, A η⟫_ℂ = ⟪ξ, B η⟫_ℂ) : A = B :=
  ContinuousLinearMap.ext fun η => ext_inner_left ℂ fun ξ => h ξ η

/-- The Borel calculus depends only on the symbol (the measurability/boundedness proofs are
propositions). -/
theorem borelCalculus_congr {g₁ g₂ : spectrum ℂ U → ℂ} (h : g₁ = g₂)
    (hm₁ : Measurable g₁) (hb₁ : ∃ C, ∀ z, ‖g₁ z‖ ≤ C)
    (hm₂ : Measurable g₂) (hb₂ : ∃ C, ∀ z, ‖g₂ z‖ ≤ C) :
    borelCalculus U hn g₁ hm₁ hb₁ = borelCalculus U hn g₂ hm₂ hb₂ := by
  subst h; rfl

/-- Additivity of the form in the symbol slot (integrals split; needs integrability from
boundedness). -/
theorem borelForm_add_fun (g₁ g₂ : spectrum ℂ U → ℂ)
    (hg₁_meas : Measurable g₁) (hg₁_bdd : ∃ C, ∀ z, ‖g₁ z‖ ≤ C)
    (hg₂_meas : Measurable g₂) (hg₂_bdd : ∃ C, ∀ z, ‖g₂ z‖ ≤ C) (ξ η : H) :
    borelForm U hn (fun z => g₁ z + g₂ z) ξ η
      = borelForm U hn g₁ ξ η + borelForm U hn g₂ ξ η := by
  obtain ⟨C₁, hC₁⟩ := hg₁_bdd
  obtain ⟨C₂, hC₂⟩ := hg₂_bdd
  have hsplit : ∀ v : H, (∫ z, g₁ z + g₂ z ∂(spectralMeasure U hn v))
      = (∫ z, g₁ z ∂(spectralMeasure U hn v)) + ∫ z, g₂ z ∂(spectralMeasure U hn v) := fun v =>
    integral_add (integrable_of_bdd U hg₁_meas hC₁) (integrable_of_bdd U hg₂_meas hC₂)
  simp only [borelForm, hsplit]
  ring

/-- Scalars pull out of the symbol slot (`integral_const_mul`, no integrability needed). -/
theorem borelForm_smul_fun (c : ℂ) (g : spectrum ℂ U → ℂ) (ξ η : H) :
    borelForm U hn (fun z => c * g z) ξ η = c * borelForm U hn g ξ η := by
  simp only [borelForm, integral_const_mul]
  ring

/-- On continuous symbols the Borel calculus is the continuous calculus. -/
theorem borelCalculus_eq_cfcHom (f : C(spectrum ℂ U, ℂ)) :
    borelCalculus U hn (fun z => f z) f.continuous.measurable
        ⟨‖f‖, fun z => f.norm_coe_le_norm z⟩
      = cfcHom hn f := by
  refine borelCalculus_ext fun ξ η => ?_
  rw [inner_borelCalculus]
  exact (inner_cfcHom_polarized U hn ξ η f).symm

/-- `Φ_U(1) = id`  (uses `Spectra.Riesz.spectralMeasure_real_univ`). -/
theorem borelCalculus_one :
    borelCalculus U hn (fun _ => (1 : ℂ)) measurable_const ⟨1, fun _ => by simp⟩
      = ContinuousLinearMap.id ℂ H := by
  refine borelCalculus_ext fun ξ η => ?_
  rw [inner_borelCalculus, ContinuousLinearMap.id_apply]
  have h := inner_cfcHom_polarized U hn ξ η (1 : C(spectrum ℂ U, ℂ))
  rw [map_one, ContinuousLinearMap.one_apply] at h
  exact h.symm

/-- Additivity in the symbol: `Φ(g + h) = Φ(g) + Φ(h)`. -/
theorem borelCalculus_add (g h : spectrum ℂ U → ℂ)
    (hgm : Measurable g) (hgb : ∃ C, ∀ z, ‖g z‖ ≤ C)
    (hhm : Measurable h) (hhb : ∃ C, ∀ z, ‖h z‖ ≤ C)
    (hm : Measurable fun z => g z + h z) (hb : ∃ C, ∀ z, ‖g z + h z‖ ≤ C) :
    borelCalculus U hn (fun z => g z + h z) hm hb
      = borelCalculus U hn g hgm hgb + borelCalculus U hn h hhm hhb := by
  refine borelCalculus_ext fun ξ η => ?_
  rw [inner_borelCalculus U hn _ hm hb ξ η,
    borelForm_add_fun U hn g h hgm hgb hhm hhb ξ η, ContinuousLinearMap.add_apply,
    inner_add_right, inner_borelCalculus U hn g hgm hgb ξ η,
    inner_borelCalculus U hn h hhm hhb ξ η]

/-- Scalar-homogeneity in the symbol: `Φ(c · g) = c • Φ(g)`. -/
theorem borelCalculus_smul (c : ℂ) (g : spectrum ℂ U → ℂ)
    (hgm : Measurable g) (hgb : ∃ C, ∀ z, ‖g z‖ ≤ C)
    (hcm : Measurable fun z => c * g z) (hcb : ∃ C, ∀ z, ‖c * g z‖ ≤ C) :
    borelCalculus U hn (fun z => c * g z) hcm hcb = c • borelCalculus U hn g hgm hgb := by
  refine borelCalculus_ext fun ξ η => ?_
  rw [inner_borelCalculus U hn _ hcm hcb ξ η, borelForm_smul_fun,
    ContinuousLinearMap.smul_apply, inner_smul_right,
    inner_borelCalculus U hn g hgm hgb ξ η]

/-- Conjugate symmetry of the form (the measure-level `μ_{η,ξ} = conj μ_{ξ,η}`).
Pushing the outer conjugation through the four positive measures (`integral_conj`) flips
only the sign of the `I`-weighted pair. -/
theorem borelForm_conj_symm (g : spectrum ℂ U → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ z, ‖g z‖ ≤ C) (ξ η : H) :
    borelForm U hn g η ξ
      = starRingEnd ℂ (borelForm U hn (fun z => starRingEnd ℂ (g z)) ξ η) := by
  have key := spectrum_combination_ext U hn
    (![1 / 4, -(1 / 4), -(I / 4), I / 4])
    (![η + ξ, η - ξ, η + I • ξ, η - I • ξ])
    (![1 / 4, -(1 / 4), I / 4, -(I / 4)])
    (![ξ + η, ξ - η, ξ + I • η, ξ - I • η])
    (fun f => by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, add_zero, map_add, map_sub, map_smul, inner_add_left,
        inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        Complex.conj_I]
      ring)
    hg_meas hg_bdd
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    add_zero] at key
  simp only [borelForm, integral_conj, map_div₀, map_add, map_sub, map_mul, map_ofNat,
    Complex.conj_I, Complex.conj_conj]
  linear_combination key

/-- `Φ_U(ḡ) = Φ_U(g)*`. -/
theorem borelCalculus_adjoint (g : spectrum ℂ U → ℂ)
    (hgm : Measurable g) (hgb : ∃ C, ∀ z, ‖g z‖ ≤ C)
    (hcm : Measurable fun z => conj (g z)) (hcb : ∃ C, ∀ z, ‖conj (g z)‖ ≤ C) :
    ContinuousLinearMap.adjoint (borelCalculus U hn g hgm hgb)
      = borelCalculus U hn (fun z => conj (g z)) hcm hcb := by
  refine borelCalculus_ext fun ξ η => ?_
  calc ⟪ξ, ContinuousLinearMap.adjoint (borelCalculus U hn g hgm hgb) η⟫_ℂ
      = ⟪borelCalculus U hn g hgm hgb ξ, η⟫_ℂ :=
        ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = (starRingEnd ℂ) ⟪η, borelCalculus U hn g hgm hgb ξ⟫_ℂ := (inner_conj_symm _ _).symm
    _ = (starRingEnd ℂ) (borelForm U hn g η ξ) := by rw [inner_borelCalculus]
    _ = (starRingEnd ℂ) ((starRingEnd ℂ) (borelForm U hn (fun z => conj (g z)) ξ η)) := by
        rw [borelForm_conj_symm U hn g hgm hgb ξ η]
    _ = borelForm U hn (fun z => conj (g z)) ξ η := Complex.conj_conj _
    _ = ⟪ξ, borelCalculus U hn (fun z => conj (g z)) hcm hcb η⟫_ℂ :=
        (inner_borelCalculus U hn _ hcm hcb ξ η).symm

/-- **Left intertwining.** Moving a *continuous* `cfcHom f₁` from the left vector into the symbol:
`borelForm g (cfcHom f₁ ξ) η = borelForm (conj f₁ · g) ξ η`.  Holds on continuous `g` by `cfcHom`
multiplicativity; extends to bounded measurable `g` by the two-sided density engine. -/
theorem borelForm_cfcHom_left (f₁ : C(spectrum ℂ U, ℂ)) (g : spectrum ℂ U → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ z, ‖g z‖ ≤ C) (ξ η : H) :
    borelForm U hn g (cfcHom hn f₁ ξ) η
      = borelForm U hn (fun z => starRingEnd ℂ (f₁ z) * g z) ξ η := by
  -- `cfcHom hn f₁ ξ` recurs 7 times below; naming it once avoids repeatedly re-unifying the
  -- same `cfcHom`-coerced expression (see the compile-time case study).
  set cfcF1Xi : H := cfcHom hn f₁ ξ with hcfcF1Xi
  have hcf_meas : Measurable fun z => starRingEnd ℂ (f₁ z) :=
    (Complex.continuous_conj.comp f₁.continuous).measurable
  have hcf_bdd : ∃ C, ∀ z, ‖starRingEnd ℂ (f₁ z)‖ ≤ C :=
    ⟨‖f₁‖, fun z => by rw [RCLike.norm_conj]; exact f₁.norm_coe_le_norm z⟩
  -- (KL) on continuous symbols, via `cfcHom` multiplicativity
  have hcont_kl : ∀ f : C(spectrum ℂ U, ℂ),
      borelForm U hn (fun z => f z) cfcF1Xi η
        = borelForm U hn (fun z => starRingEnd ℂ (f₁ z) * f z) ξ η := by
    intro f
    have hadj : (cfcHom hn f₁).adjoint = cfcHom hn (star f₁) := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
    have e2 : ⟪cfcF1Xi, cfcHom hn f η⟫_ℂ = ⟪ξ, cfcHom hn (star f₁ * f) η⟫_ℂ := by
      rw [hcfcF1Xi, map_mul, ContinuousLinearMap.mul_apply, ← hadj,
        ContinuousLinearMap.adjoint_inner_right]
    rw [show borelForm U hn (fun z => f z) cfcF1Xi η
          = ⟪cfcF1Xi, cfcHom hn f η⟫_ℂ from
        (inner_cfcHom_polarized U hn cfcF1Xi η f).symm, e2]
    exact inner_cfcHom_polarized U hn ξ η (star f₁ * f)
  -- extend to bounded measurable `g` by the two-sided density engine
  have hcomm : ∀ (q : spectrum ℂ U → ℂ) (μ : Measure (spectrum ℂ U)),
      (∫ z, q z * starRingEnd ℂ (f₁ z) ∂μ) = ∫ z, starRingEnd ℂ (f₁ z) * q z ∂μ :=
    fun q μ => integral_congr_ae (.of_forall fun z => mul_comm _ _)
  have key := spectrum_combination_ext_density U hn
    (![1 / 4, -(1 / 4), -(I / 4), I / 4])
    (![cfcF1Xi + η, cfcF1Xi - η, cfcF1Xi + I • η, cfcF1Xi - I • η])
    (![fun _ => (1 : ℂ), fun _ => 1, fun _ => 1, fun _ => 1])
    (fun i => by fin_cases i <;> exact measurable_const)
    (fun i => by fin_cases i <;> exact ⟨1, fun _ => by simp⟩)
    (![1 / 4, -(1 / 4), -(I / 4), I / 4])
    (![ξ + η, ξ - η, ξ + I • η, ξ - I • η])
    (![fun z => starRingEnd ℂ (f₁ z), fun z => starRingEnd ℂ (f₁ z),
        fun z => starRingEnd ℂ (f₁ z), fun z => starRingEnd ℂ (f₁ z)])
    (fun j => by fin_cases j <;> exact hcf_meas)
    (fun j => by fin_cases j <;> exact hcf_bdd)
    (fun f => by
      have h := hcont_kl f
      simp only [borelForm] at h
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, add_zero, mul_one, hcomm]
      linear_combination h)
    hg_meas hg_bdd
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    add_zero, mul_one, hcomm] at key
  simp only [borelForm]
  linear_combination key

/-- **Weighted-measure theorem** (the keystone): pairing against `borelCalculus g η` twists the
symbol by `g`, `borelForm h ξ (borelCalculus g η) = borelForm ξ η (h·g)`.  Instance of the
two-sided density engine; on continuous symbols it is `borelForm_cfcHom_left` after moving the
`cfcHom` adjoint across the inner product. -/
theorem borelForm_calculus_right (g h : spectrum ℂ U → ℂ)
    (hgm : Measurable g) (hgb : ∃ C, ∀ z, ‖g z‖ ≤ C)
    (hhm : Measurable h) (hhb : ∃ C, ∀ z, ‖h z‖ ≤ C) (ξ η : H) :
    borelForm U hn h ξ (borelCalculus U hn g hgm hgb η)
      = borelForm U hn (fun z => h z * g z) ξ η := by
  -- `borelCalculus U hn g hgm hgb η` recurs 7 times below; naming it once avoids repeatedly
  -- re-unifying the same expression (see the compile-time case study).
  set uGη : H := borelCalculus U hn g hgm hgb η with huGη
  -- per-continuous-symbol identity, via the cfcHom adjoint + left intertwining
  have hcont_key : ∀ f : C(spectrum ℂ U, ℂ),
      borelForm U hn (fun z => f z) ξ uGη
        = borelForm U hn (fun z => f z * g z) ξ η := by
    intro f
    have hadj : (cfcHom hn f).adjoint = cfcHom hn (star f) := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
    rw [show borelForm U hn (fun z => f z) ξ uGη
          = ⟪ξ, cfcHom hn f uGη⟫_ℂ from
        (inner_cfcHom_polarized U hn ξ uGη f).symm,
      ← ContinuousLinearMap.adjoint_inner_left, hadj, huGη,
      inner_borelCalculus U hn g hgm hgb (cfcHom hn (star f) ξ) η,
      borelForm_cfcHom_left U hn (star f) g hgm hgb ξ η]
    congr 1
    funext z
    simp [ContinuousMap.star_apply]
  have key := spectrum_combination_ext_density U hn
    (![1 / 4, -(1 / 4), -(I / 4), I / 4])
    (![ξ + uGη, ξ - uGη, ξ + I • uGη, ξ - I • uGη])
    (![fun _ => (1 : ℂ), fun _ => 1, fun _ => 1, fun _ => 1])
    (fun i => by fin_cases i <;> exact measurable_const)
    (fun i => by fin_cases i <;> exact ⟨1, fun _ => by simp⟩)
    (![1 / 4, -(1 / 4), -(I / 4), I / 4])
    (![ξ + η, ξ - η, ξ + I • η, ξ - I • η])
    (![g, g, g, g])
    (fun j => by fin_cases j <;> exact hgm)
    (fun j => by fin_cases j <;> exact hgb)
    (fun f => by
      have hk := hcont_key f
      simp only [borelForm] at hk
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, add_zero, mul_one]
      linear_combination hk)
    hhm hhb
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    add_zero, mul_one] at key
  simp only [borelForm]
  linear_combination key

/-- **Multiplicativity**: `Φ(g) Φ(h) = Φ(g·h)`.  Bookkeeping on the weighted-measure theorem. -/
theorem borelCalculus_mul (g h : spectrum ℂ U → ℂ)
    (hgm : Measurable g) (hgb : ∃ C, ∀ z, ‖g z‖ ≤ C)
    (hhm : Measurable h) (hhb : ∃ C, ∀ z, ‖h z‖ ≤ C)
    (hghm : Measurable fun z => g z * h z) (hghb : ∃ C, ∀ z, ‖g z * h z‖ ≤ C) :
    (borelCalculus U hn g hgm hgb).comp (borelCalculus U hn h hhm hhb)
      = borelCalculus U hn (fun z => g z * h z) hghm hghb := by
  refine borelCalculus_ext fun ξ η => ?_
  rw [ContinuousLinearMap.comp_apply,
    inner_borelCalculus U hn g hgm hgb ξ (borelCalculus U hn h hhm hhb η),
    borelForm_calculus_right U hn h g hhm hhb hgm hgb ξ η,
    inner_borelCalculus U hn (fun z => g z * h z) hghm hghb ξ η]

/-- **The `L²` identity**: `‖Φ(g)ξ‖² = ∫ ‖g‖² dμ_ξ`.  Route: `‖Φ(g)ξ‖² = ⟪Φ(g)ξ, Φ(g)ξ⟫
= ⟪ξ, Φ(ḡ)(Φ(g)ξ)⟫ = borelForm ξ ξ (ḡ·g) = ∫ ‖g‖² dμ_ξ`, by the adjoint, the weighted-measure
theorem at `η = ξ`, and `borelForm_self`.  The engine for the dominated-convergence step. -/
theorem norm_sq_borelCalculus_apply (g : spectrum ℂ U → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ z, ‖g z‖ ≤ C) (ξ : H) :
    ‖borelCalculus U hn g hg_meas hg_bdd ξ‖ ^ 2
      = ∫ z, ‖g z‖ ^ 2 ∂(spectralMeasure U hn ξ) := by
  have hcg_meas : Measurable fun z => conj (g z) := Complex.continuous_conj.measurable.comp hg_meas
  have hcg_bdd : ∃ C, ∀ z, ‖conj (g z)‖ ≤ C := by
    obtain ⟨C, hC⟩ := hg_bdd; exact ⟨C, fun z => by rw [RCLike.norm_conj]; exact hC z⟩
  have h1 : ⟪borelCalculus U hn g hg_meas hg_bdd ξ, borelCalculus U hn g hg_meas hg_bdd ξ⟫_ℂ
      = ∫ z, conj (g z) * g z ∂(spectralMeasure U hn ξ) := by
    calc ⟪borelCalculus U hn g hg_meas hg_bdd ξ, borelCalculus U hn g hg_meas hg_bdd ξ⟫_ℂ
        = ⟪ξ, (borelCalculus U hn g hg_meas hg_bdd).adjoint
            (borelCalculus U hn g hg_meas hg_bdd ξ)⟫_ℂ :=
          (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
      _ = ⟪ξ, borelCalculus U hn (fun z => conj (g z)) hcg_meas hcg_bdd
            (borelCalculus U hn g hg_meas hg_bdd ξ)⟫_ℂ := by
          rw [borelCalculus_adjoint U hn g hg_meas hg_bdd hcg_meas hcg_bdd]
      _ = borelForm U hn (fun z => conj (g z)) ξ (borelCalculus U hn g hg_meas hg_bdd ξ) :=
          inner_borelCalculus U hn _ hcg_meas hcg_bdd ξ _
      _ = borelForm U hn (fun z => conj (g z) * g z) ξ ξ :=
          borelForm_calculus_right U hn g (fun z => conj (g z)) hg_meas hg_bdd hcg_meas hcg_bdd ξ ξ
      _ = ∫ z, conj (g z) * g z ∂(spectralMeasure U hn ξ) := borelForm_self U hn _ ξ
  have h2 : (∫ z, conj (g z) * g z ∂(spectralMeasure U hn ξ))
      = ((∫ z, ‖g z‖ ^ 2 ∂(spectralMeasure U hn ξ) : ℝ) : ℂ) := by
    have hcg : (∫ z, conj (g z) * g z ∂(spectralMeasure U hn ξ))
        = ∫ z, ((‖g z‖ ^ 2 : ℝ) : ℂ) ∂(spectralMeasure U hn ξ) := by
      refine integral_congr_ae (.of_forall fun z => ?_)
      change conj (g z) * g z = ((‖g z‖ ^ 2 : ℝ) : ℂ)
      rw [RCLike.conj_mul]; norm_cast
    rw [hcg, integral_complex_ofReal (f := fun z => ‖g z‖ ^ 2)]
  have h12 : ⟪borelCalculus U hn g hg_meas hg_bdd ξ, borelCalculus U hn g hg_meas hg_bdd ξ⟫_ℂ
      = ((∫ z, ‖g z‖ ^ 2 ∂(spectralMeasure U hn ξ) : ℝ) : ℂ) := h1.trans h2
  rw [inner_self_eq_norm_sq_to_K] at h12
  have h13 := congrArg Complex.re h12
  simpa [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] using h13

/-- **Operator-norm bound** `‖Φ(g)‖ ≤ C` (for `0 ≤ C`), via the `L²` identity. -/
theorem norm_borelCalculus_le (g : spectrum ℂ U → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ z, ‖g z‖ ≤ C) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ z, ‖g z‖ ≤ C) :
    ‖borelCalculus U hn g hg_meas hg_bdd‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun ξ => ?_
  have hint : (∫ z, ‖g z‖ ^ 2 ∂(spectralMeasure U hn ξ)) ≤ C ^ 2 * ‖ξ‖ ^ 2 := by
    calc (∫ z, ‖g z‖ ^ 2 ∂(spectralMeasure U hn ξ))
        ≤ ∫ _, C ^ 2 ∂(spectralMeasure U hn ξ) := by
          refine integral_mono_of_nonneg (.of_forall fun z => sq_nonneg _) (integrable_const _)
            (.of_forall fun z => ?_)
          nlinarith [hC z, norm_nonneg (g z)]
      _ = C ^ 2 * ‖ξ‖ ^ 2 := by
          rw [integral_const, smul_eq_mul, spectralMeasure_real_univ, mul_comm]
  have hsq : ‖borelCalculus U hn g hg_meas hg_bdd ξ‖ ^ 2 ≤ (C * ‖ξ‖) ^ 2 := by
    rw [norm_sq_borelCalculus_apply U hn g hg_meas hg_bdd ξ]
    calc (∫ z, ‖g z‖ ^ 2 ∂(spectralMeasure U hn ξ)) ≤ C ^ 2 * ‖ξ‖ ^ 2 := hint
      _ = (C * ‖ξ‖) ^ 2 := by ring
  calc ‖borelCalculus U hn g hg_meas hg_bdd ξ‖
      = Real.sqrt (‖borelCalculus U hn g hg_meas hg_bdd ξ‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((C * ‖ξ‖) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = C * ‖ξ‖ := Real.sqrt_sq (mul_nonneg hC0 (norm_nonneg _))

/-- Dominated-convergence engine: a uniformly bounded, pointwise-convergent net of
symbols converges in the strong operator topology.  (The driver for strong continuity
of the group, `stoneExp_strong_continuous`.)

Route: the `L²` identity `‖Φ(Gₙ)ξ − Φ(g)ξ‖² = ‖Φ(Gₙ − g)ξ‖² = ∫ ‖Gₙ − g‖² dμ_ξ`
(from `borelCalculus_add`/`_smul` and the `L²` identity behind `norm_borelCalculus_le`) lets
`MeasureTheory.tendstoInMeasure`/dominated convergence drive `∫ ‖Gₙ − g‖² dμ_ξ → 0` from the
uniform bound `2C` and pointwise `Gₙ → g`; then `‖Φ(Gₙ)ξ − Φ(g)ξ‖ → 0`.  Needs the keystone. -/
theorem tendsto_borelCalculus_apply {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {G : ι → spectrum ℂ U → ℂ} {g : spectrum ℂ U → ℂ}
    (hGm : ∀ n, Measurable (G n)) (hGb : ∀ n, ∃ C, ∀ z, ‖G n z‖ ≤ C)
    (hgm : Measurable g) (hgb : ∃ C, ∀ z, ‖g z‖ ≤ C)
    {C : ℝ} (hunif : ∀ n z, ‖G n z‖ ≤ C) (hlim : ∀ z, Tendsto (fun n => G n z) l (𝓝 (g z)))
    (ξ : H) :
    Tendsto (fun n => borelCalculus U hn (G n) (hGm n) (hGb n) ξ) l
      (𝓝 (borelCalculus U hn g hgm hgb ξ)) := by
  obtain ⟨Cg, hCg⟩ := id hgb
  have hDm : ∀ n, Measurable (fun z => G n z - g z) := fun n => (hGm n).sub hgm
  have hDb : ∀ n, ∃ C', ∀ z, ‖G n z - g z‖ ≤ C' :=
    fun n => ⟨C + Cg, fun z => (norm_sub_le _ _).trans (add_le_add (hunif n z) (hCg z))⟩
  -- `Φ(Gₙ)ξ − Φ(g)ξ = Φ(Gₙ − g)ξ`
  have hsumm : ∀ n, Measurable (fun z => (G n z - g z) + g z) := fun n => (hDm n).add hgm
  have hsumb : ∀ n, ∃ C', ∀ z, ‖(G n z - g z) + g z‖ ≤ C' :=
    fun n => ⟨C, fun z => by rw [sub_add_cancel]; exact hunif n z⟩
  have hsub : ∀ n, borelCalculus U hn (G n) (hGm n) (hGb n) ξ
        - borelCalculus U hn g hgm hgb ξ
      = borelCalculus U hn (fun z => G n z - g z) (hDm n) (hDb n) ξ := by
    intro n
    have hop : borelCalculus U hn (fun z => G n z - g z) (hDm n) (hDb n)
          + borelCalculus U hn g hgm hgb
        = borelCalculus U hn (G n) (hGm n) (hGb n) := by
      rw [← borelCalculus_add U hn (fun z => G n z - g z) g (hDm n) (hDb n) hgm hgb
        (hsumm n) (hsumb n)]
      exact borelCalculus_congr U hn (funext fun z => by ring) (hsumm n) (hsumb n)
        (hGm n) (hGb n)
    rw [← hop, ContinuousLinearMap.add_apply]; abel
  -- dominated convergence: `∫ ‖Gₙ − g‖² dμ_ξ → 0`
  have hdct : Tendsto (fun n => ∫ z, ‖G n z - g z‖ ^ 2 ∂(spectralMeasure U hn ξ)) l (𝓝 0) := by
    have hlim0 : ∀ z, Tendsto (fun n => ‖G n z - g z‖ ^ 2) l (𝓝 0) := by
      intro z
      have h := ((hlim z).sub tendsto_const_nhds (b := g z)).norm.pow 2
      simpa using h
    have := tendsto_integral_filter_of_dominated_convergence
      (μ := spectralMeasure U hn ξ) (bound := fun _ => (C + Cg) ^ 2)
      (F := fun n z => ‖G n z - g z‖ ^ 2) (f := fun _ => (0 : ℝ))
      (.of_forall fun n => ((hDm n).norm.pow_const 2).aestronglyMeasurable)
      (.of_forall fun n => .of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _)
          ((norm_sub_le _ _).trans (add_le_add (hunif n z) (hCg z))) 2)
      (integrable_const _)
      (.of_forall hlim0)
    simpa using this
  -- assemble via the `L²` identity
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have heq : ∀ n, ‖borelCalculus U hn (G n) (hGm n) (hGb n) ξ
        - borelCalculus U hn g hgm hgb ξ‖
      = Real.sqrt (∫ z, ‖G n z - g z‖ ^ 2 ∂(spectralMeasure U hn ξ)) := by
    intro n
    rw [hsub n, ← norm_sq_borelCalculus_apply U hn (fun z => G n z - g z) (hDm n) (hDb n) ξ,
      Real.sqrt_sq (norm_nonneg _)]
  simp only [heq]
  rw [show (0 : ℝ) = Real.sqrt 0 from Real.sqrt_zero.symm]
  exact (Real.continuous_sqrt.tendsto 0).comp hdct

end Spectra.BorelCFC
