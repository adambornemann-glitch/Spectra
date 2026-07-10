/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.TensorDecomp.Basic
import Spectra.QuantumMechanics.Hydrogen.Laplacian.Spherical
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The 3D spherical change-of-variables unitary

This file builds `chartRealization`, the unitary realizing the change of variables from
Cartesian to spherical coordinates on `L²(ℝ³)`:

  `chartRealization : Spectra.Sobolev.l2R3 ≃ₗᵢ[ℂ] Decomposition.l2R3`,

i.e. `Lp ℂ 2 (volume : Measure ℝ³) ≃ₗᵢ Lp ℂ 2 (radialMeasure.prod sphereMeasure)`, given
by precomposition with the spherical chart `(r, θ, φ) ↦ (r sinθ cosφ, r sinθ sinφ, r cosθ)`
(Jacobian `r² sinθ`).  Mathlib stops at the 2D `polarCoord`; this is the 3D analogue.

## Strategy

The Jacobian change of variables is performed on `Fin 3 → ℝ` (clean `Matrix.det_fin_three`
determinant `= r² sinθ` and per-coordinate `HasFDerivAt`), mirroring Mathlib's `polarCoord`
proof one dimension up via `lintegral_image_eq_lintegral_abs_det_fderiv_mul`.  The product
measure `radialMeasure.prod sphereMeasure` is collapsed to a single `withDensity (r² sinθ)`
(`prod_withDensity₀`), bridged to `Fin 3 → ℝ` by the volume-preserving `reshuffle`, and to the
Cartesian `EuclideanSpace ℝ (Fin 3)` by `PiLp.volume_preserving_toLp`.  This yields
`measurePreserving_sphereChart`, from which the unitary is assembled via
`Lp.compMeasurePreservingₗᵢ`; surjectivity is supplied by the explicit a.e. inverse chart.

## Main statements

* `measurePreserving_sphereChart` — the chart is measure-preserving (spherical → Cartesian).
* `measurePreserving_sphereChartInv` — the (a.e.) inverse chart is measure-preserving
  (Cartesian → spherical).
* `eLpNorm_chartRealizationFun` — the eLpNorm change-of-variables identity.
* `chartRealizationₗᵢ` — the forward isometry `Sobolev.l2R3 →ₗᵢ[ℂ] Decomposition.l2R3`.
* `chartRealization` — the unitary `Sobolev.l2R3 ≃ₗᵢ[ℂ] Decomposition.l2R3`.
* `chartRealization_coeFn` / `chartRealization_symm_coeFn` — the unitary and its inverse act,
  almost everywhere, as precomposition with the spherical chart / its (a.e.) inverse chart; this
  is what makes `chartRealization` usable pointwise in later intertwining arguments.
-/

open MeasureTheory Complex Filter Set Real Matrix ContinuousLinearMap
open scoped Topology NNReal ENNReal Real
open Spectra.SphericalHarmonics (sphereMeasure)
open Spectra.QuantumMechanics.Hydrogen (sphereChart)

namespace Spectra.QuantumMechanics.Hydrogen.Decomposition

noncomputable section

/-- The 3×3 spherical Jacobian matrix at `c = (r, θ, φ)` (columns: ∂r, ∂θ, ∂φ). -/
def sphereJac (c : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.sin (c 1) * Real.cos (c 2), c 0 * Real.cos (c 1) * Real.cos (c 2),
       -(c 0) * Real.sin (c 1) * Real.sin (c 2);
     Real.sin (c 1) * Real.sin (c 2), c 0 * Real.cos (c 1) * Real.sin (c 2),
       c 0 * Real.sin (c 1) * Real.cos (c 2);
     Real.cos (c 1), -(c 0) * Real.sin (c 1), 0]

/-- The determinant of the spherical Jacobian is `r² sin θ`. -/
theorem det_sphereJac (c : Fin 3 → ℝ) :
    (sphereJac c).det = (c 0) ^ 2 * Real.sin (c 1) := by
  have h1 : Real.sin (c 1) ^ 2 + Real.cos (c 1) ^ 2 = 1 := Real.sin_sq_add_cos_sq (c 1)
  have h2 : Real.sin (c 2) ^ 2 + Real.cos (c 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (c 2)
  simp only [sphereJac, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val',
    Matrix.cons_val]
  linear_combination ((c 0) ^ 2 * Real.sin (c 1) * (Real.sin (c 2) ^ 2 + Real.cos (c 2) ^ 2)) * h1 +
    ((c 0) ^ 2 * Real.sin (c 1)) * h2

/-- The spherical change of variables on `Fin 3 → ℝ`:
    `c ↦ (c₀ sin c₁ cos c₂, c₀ sin c₁ sin c₂, c₀ cos c₁)`. -/
def sphereCoordSymmF (c : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![c 0 * Real.sin (c 1) * Real.cos (c 2),
    c 0 * Real.sin (c 1) * Real.sin (c 2),
    c 0 * Real.cos (c 1)]

/-- The derivative of `sphereCoordSymmF` as a continuous linear map (from the Jacobian matrix). -/
def sphereCoordCLM (c : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (Matrix.toLin' (sphereJac c)).toContinuousLinearMap

/-- The determinant of `sphereCoordCLM c`, as a continuous linear map, is `r² sin θ` (same as
    the matrix determinant `det_sphereJac`). -/
theorem det_sphereCoordCLM (c : Fin 3 → ℝ) :
    (sphereCoordCLM c).det = (c 0) ^ 2 * Real.sin (c 1) := by
  simp only [sphereCoordCLM, ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap,
    LinearMap.det_toLin', det_sphereJac]

/-- Helper: evaluate `(proj i).comp (sphereCoordCLM c)` applied to `dc` as a dot product. -/
private theorem sphereCoordCLM_proj_apply (c dc : Fin 3 → ℝ) (i : Fin 3) :
    ((proj i).comp (sphereCoordCLM c)) dc
      = (sphereJac c i 0) * dc 0 + (sphereJac c i 1) * dc 1 + (sphereJac c i 2) * dc 2 := by
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, sphereCoordCLM,
    LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]

/-- `sphereCoordSymmF` is differentiable at every `c`, with derivative the continuous linear map
    `sphereCoordCLM c` induced by the Jacobian matrix `sphereJac c`. -/
theorem hasFDerivAt_sphereCoordSymmF (c : Fin 3 → ℝ) :
    HasFDerivAt sphereCoordSymmF (sphereCoordCLM c) c := by
  have hc0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) c
  have hc1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) c
  have hc2 := hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) c
  have hsin1 := (Real.hasDerivAt_sin (c 1)).comp_hasFDerivAt c hc1
  have hcos1 := (Real.hasDerivAt_cos (c 1)).comp_hasFDerivAt c hc1
  have hsin2 := (Real.hasDerivAt_sin (c 2)).comp_hasFDerivAt c hc2
  have hcos2 := (Real.hasDerivAt_cos (c 2)).comp_hasFDerivAt c hc2
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  -- component 0: c₀ sin c₁ cos c₂; component 1: c₀ sin c₁ sin c₂; component 2: c₀ cos c₁
  · exact (hc0.mul hsin1).mul hcos2 |>.congr_fderiv (by
      ext dc; rw [sphereCoordCLM_proj_apply]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul, sphereJac]
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
      ring)
  · exact (hc0.mul hsin1).mul hsin2 |>.congr_fderiv (by
      ext dc; rw [sphereCoordCLM_proj_apply]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul, sphereJac]
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
      ring)
  · exact hc0.mul hcos1 |>.congr_fderiv (by
      ext dc; rw [sphereCoordCLM_proj_apply]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul, sphereJac]
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
      ring)

/-- The open coordinate box `(0,∞) × (0,π) × (0,2π)` on which `sphereCoordSymmF` is a
    diffeomorphism. -/
def chartBox : Set (Fin 3 → ℝ) :=
  {c | 0 < c 0 ∧ c 1 ∈ Set.Ioo 0 Real.pi ∧ c 2 ∈ Set.Ioo 0 (2 * Real.pi)}

/-- Componentwise unfolding of `sphereCoordSymmF` (`simp` normal form for each coordinate). -/
@[simp] lemma sphereCoordSymmF_zero (c : Fin 3 → ℝ) :
    sphereCoordSymmF c 0 = c 0 * Real.sin (c 1) * Real.cos (c 2) := rfl
@[simp] lemma sphereCoordSymmF_one (c : Fin 3 → ℝ) :
    sphereCoordSymmF c 1 = c 0 * Real.sin (c 1) * Real.sin (c 2) := rfl
@[simp] lemma sphereCoordSymmF_two (c : Fin 3 → ℝ) :
    sphereCoordSymmF c 2 = c 0 * Real.cos (c 1) := rfl

/-- Sum of squares of the coordinates recovers `r²`. -/
lemma sphereCoordSymmF_sq (c : Fin 3 → ℝ) :
    (sphereCoordSymmF c 0) ^ 2 + (sphereCoordSymmF c 1) ^ 2 + (sphereCoordSymmF c 2) ^ 2
      = (c 0) ^ 2 := by
  simp only [sphereCoordSymmF_zero, sphereCoordSymmF_one, sphereCoordSymmF_two]
  have h1 : Real.sin (c 1) ^ 2 + Real.cos (c 1) ^ 2 = 1 := Real.sin_sq_add_cos_sq (c 1)
  have h2 : Real.sin (c 2) ^ 2 + Real.cos (c 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (c 2)
  linear_combination (c 0) ^ 2 * h1 + (c 0) ^ 2 * Real.sin (c 1) ^ 2 * h2

/-- `sphereCoordSymmF` is injective on `chartBox`: distinct `(r, θ, φ)` in the open box map to
    distinct Cartesian points. -/
theorem injOn_sphereCoordSymmF : Set.InjOn sphereCoordSymmF chartBox := by
  rintro c ⟨hc0, hc1, hc2⟩ c' ⟨hc0', hc1', hc2'⟩ hcc
  have e0 : c 0 * Real.sin (c 1) * Real.cos (c 2)
      = c' 0 * Real.sin (c' 1) * Real.cos (c' 2) := congrFun hcc 0
  have e1 : c 0 * Real.sin (c 1) * Real.sin (c 2)
      = c' 0 * Real.sin (c' 1) * Real.sin (c' 2) := congrFun hcc 1
  have e2 : c 0 * Real.cos (c 1) = c' 0 * Real.cos (c' 1) := congrFun hcc 2
  -- r = r' from the sum of squares
  have hr : c 0 = c' 0 := by
    have hsq := sphereCoordSymmF_sq c
    have hsq' := sphereCoordSymmF_sq c'
    have : (c 0) ^ 2 = (c' 0) ^ 2 := by
      rw [← hsq, ← hsq']; simp only [sphereCoordSymmF_zero, sphereCoordSymmF_one,
        sphereCoordSymmF_two]; rw [e0, e1, e2]
    nlinarith [this, hc0, hc0']
  -- θ = θ' via cos injective on [0,π]
  have hsinpos : 0 < Real.sin (c 1) := Real.sin_pos_of_pos_of_lt_pi hc1.1 hc1.2
  have hcosθ : Real.cos (c 1) = Real.cos (c' 1) := by
    have := e2; rw [hr] at this
    exact mul_left_cancel₀ (ne_of_gt (hr ▸ hc0)) this
  have hθ : c 1 = c' 1 :=
    Real.injOn_cos ⟨hc1.1.le, hc1.2.le⟩ ⟨hc1'.1.le, hc1'.2.le⟩ hcosθ
  -- φ = φ' via cos and sin both matching
  have hcc2 : Real.cos (c 2) = Real.cos (c' 2) := by
    rw [hr, hθ] at e0
    have hne : c' 0 * Real.sin (c' 1) ≠ 0 := by
      rw [← hr, ← hθ]; exact mul_ne_zero (ne_of_gt hc0) (ne_of_gt hsinpos)
    exact mul_left_cancel₀ hne (by linarith [e0] : c' 0 * Real.sin (c' 1) * Real.cos (c 2)
      = c' 0 * Real.sin (c' 1) * Real.cos (c' 2))
  have hsc2 : Real.sin (c 2) = Real.sin (c' 2) := by
    rw [hr, hθ] at e1
    have hne : c' 0 * Real.sin (c' 1) ≠ 0 := by
      rw [← hr, ← hθ]; exact mul_ne_zero (ne_of_gt hc0) (ne_of_gt hsinpos)
    exact mul_left_cancel₀ hne (by linarith [e1] : c' 0 * Real.sin (c' 1) * Real.sin (c 2)
      = c' 0 * Real.sin (c' 1) * Real.sin (c' 2))
  have hφ : c 2 = c' 2 := by
    have hcosdiff : Real.cos (c 2 - c' 2) = 1 := by
      rw [Real.cos_sub, hcc2, hsc2]; nlinarith [Real.sin_sq_add_cos_sq (c' 2)]
    have hlt : -(2 * Real.pi) < c 2 - c' 2 := by
      have := hc2.1; have := hc2'.2; linarith
    have hgt : c 2 - c' 2 < 2 * Real.pi := by
      have := hc2.2; have := hc2'.1; linarith
    have := (Real.cos_eq_one_iff_of_lt_of_lt hlt hgt).mp hcosdiff
    linarith
  funext i; fin_cases i <;> assumption

/-- Core construction shared by `sphereCoordSymmF_surj_of_ne` and `sphereCoordSymmInvF_spec`:
    given `y` with `y 1 ≠ 0`, the triple `(r, arccos(y 2 / r), φ)` — with
    `r = ‖(y 0, y 1, y 2)‖` and `φ` the (shifted, if needed) argument of `⟨y 0, y 1⟩` —
    lies in `chartBox` and reconstructs `y` under `sphereCoordSymmF`. -/
private theorem sphereCoordSymmInv_spec_aux (y : Fin 3 → ℝ) (hy : y 1 ≠ 0) :
    (![Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2),
        Real.arccos (y 2 / Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2)),
        if 0 < y 1 then Complex.arg ⟨y 0, y 1⟩ else Complex.arg ⟨y 0, y 1⟩ + 2 * Real.pi]
      ∈ chartBox) ∧
    sphereCoordSymmF ![Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2),
        Real.arccos (y 2 / Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2)),
        if 0 < y 1 then Complex.arg ⟨y 0, y 1⟩ else Complex.arg ⟨y 0, y 1⟩ + 2 * Real.pi] = y := by
  set z : ℂ := ⟨y 0, y 1⟩ with _hz_def
  have hzre : z.re = y 0 := rfl
  have hzim : z.im = y 1 := rfl
  have hz : z ≠ 0 := by
    intro h; apply hy; rw [← hzim, h]; rfl
  set ρ : ℝ := ‖z‖ with hρ_def
  have hρpos : 0 < ρ := norm_pos_iff.mpr hz
  have hρsq : ρ ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 := by
    rw [hρ_def, Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg z), Complex.normSq_apply,
      hzre, hzim]; ring
  set r : ℝ := Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2) with hr_def
  have hrnn : 0 ≤ (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 := by positivity
  have hrpos : 0 < r := by
    rw [hr_def]; apply Real.sqrt_pos.mpr; nlinarith [sq_nonneg (y 0), sq_nonneg (y 2),
      sq_pos_iff.mpr hy]
  have hrsq : r ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 := Real.sq_sqrt hrnn
  -- y 2 / r ∈ (-1, 1)
  have hr2lt : (y 2) ^ 2 < r ^ 2 := by rw [hrsq]; nlinarith [sq_pos_iff.mpr hy, sq_nonneg (y 0)]
  have hyrlt : (y 2 / r) < 1 := by
    rw [div_lt_one hrpos]; nlinarith [hr2lt, hrpos, abs_nonneg (y 2), sq_abs (y 2)]
  have hyrgt : -1 < (y 2 / r) := by
    rw [lt_div_iff₀ hrpos]; nlinarith [hr2lt, hrpos]
  -- φ
  set φ : ℝ := if 0 < y 1 then Complex.arg z else Complex.arg z + 2 * Real.pi with hφ_def
  have hcosφ : Real.cos φ = (y 0) / ρ := by
    rw [hφ_def]; split
    · rw [Complex.cos_arg hz, hzre]
    · rw [Real.cos_add_two_pi, Complex.cos_arg hz, hzre]
  have hsinφ : Real.sin φ = (y 1) / ρ := by
    rw [hφ_def]; split
    · rw [Complex.sin_arg, hzim]
    · rw [Real.sin_add_two_pi, Complex.sin_arg, hzim]
  have hφrange : φ ∈ Set.Ioo 0 (2 * Real.pi) := by
    rw [hφ_def]; split
    · rename_i hpos
      have h0 : 0 < Complex.arg z := by
        rcases (Complex.arg_nonneg_iff.mpr (show (0:ℝ) ≤ z.im by rw [hzim]; exact hpos.le)).lt_or_eq
          with h | h
        · exact h
        · exfalso
          rw [eq_comm, Complex.arg_eq_zero_iff] at h
          exact hy (by rw [← hzim]; exact h.2)
      exact ⟨h0, lt_of_le_of_lt (Complex.arg_le_pi z) (by linarith [Real.pi_pos])⟩
    · rename_i hpos
      have hyneg : y 1 < 0 := lt_of_le_of_ne (not_lt.mp hpos) hy
      have hargneg : Complex.arg z < 0 :=
        Complex.arg_neg_iff.mpr (show z.im < 0 by rw [hzim]; exact hyneg)
      have harggt : -Real.pi < Complex.arg z := Complex.neg_pi_lt_arg z
      exact ⟨by linarith [Real.pi_pos], by linarith⟩
  have hsa : Real.sin (Real.arccos (y 2 / r)) = ρ / r := by
    rw [Real.sin_arccos]
    have hsq : (1:ℝ) - (y 2 / r) ^ 2 = (ρ / r) ^ 2 := by
      field_simp
      nlinarith [hrsq, hρsq]
    rw [hsq, Real.sqrt_sq (by positivity)]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · change 0 < r
    exact hrpos
  · change Real.arccos (y 2 / r) ∈ Set.Ioo 0 Real.pi
    exact ⟨Real.arccos_pos.mpr hyrlt, Real.arccos_lt_pi.mpr hyrgt⟩
  · change φ ∈ Set.Ioo 0 (2 * Real.pi)
    exact hφrange
  · funext i
    fin_cases i
    · change r * Real.sin (Real.arccos (y 2 / r)) * Real.cos φ = y 0
      rw [hsa, hcosφ]; field_simp
    · change r * Real.sin (Real.arccos (y 2 / r)) * Real.sin φ = y 1
      rw [hsa, hsinφ]; field_simp
    · change r * Real.cos (Real.arccos (y 2 / r)) = y 2
      rw [Real.cos_arccos hyrgt.le hyrlt.le]; field_simp

/-- Surjectivity onto the non-slit set: every point with nonzero middle coordinate has a
    preimage in `chartBox`. -/
theorem sphereCoordSymmF_surj_of_ne (y : Fin 3 → ℝ) (hy : y 1 ≠ 0) :
    ∃ c ∈ chartBox, sphereCoordSymmF c = y :=
  ⟨_, sphereCoordSymmInv_spec_aux y hy⟩

/-- The image of the coordinate box is `volume`-a.e. all of `ℝ³`: its complement lies in the
    null hyperplane `{y | y 1 = 0}`. -/
theorem sphereCoordSymmF_image_ae_univ :
    sphereCoordSymmF '' chartBox =ᵐ[volume] (Set.univ : Set (Fin 3 → ℝ)) := by
  have hsub : (sphereCoordSymmF '' chartBox)ᶜ ⊆
      (LinearMap.ker (LinearMap.proj 1 : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) : Set (Fin 3 → ℝ)) := by
    intro y hy
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply]
    by_contra h
    exact hy (sphereCoordSymmF_surj_of_ne y h)
  have hnull : volume (LinearMap.ker (LinearMap.proj 1 : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) :
      Set (Fin 3 → ℝ)) = 0 := by
    apply Measure.addHaar_submodule
    rw [Ne, LinearMap.ker_eq_top]
    intro h
    have : (LinearMap.proj 1 : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) (Pi.single 1 1)
        = (0 : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) (Pi.single 1 1) := by rw [h]
    simp [LinearMap.proj_apply, Pi.single_eq_same] at this
  rw [ae_eq_univ]
  exact le_antisymm ((measure_mono hsub).trans hnull.le) bot_le

/-- `chartBox` is measurable (an intersection of coordinate half-spaces and slabs). -/
lemma measurableSet_chartBox : MeasurableSet chartBox := by
  rw [chartBox, Set.setOf_and, Set.setOf_and]
  exact (measurableSet_lt measurable_const (measurable_pi_apply 0)).inter
    (((measurable_pi_apply 1) measurableSet_Ioo).inter
      ((measurable_pi_apply 2) measurableSet_Ioo))

/-- **Change of variables (lintegral form) on `Fin 3 → ℝ`.** The Cartesian Lebesgue integral
    equals the box integral of `(r² sin θ) · g ∘ sphereCoordSymmF`. -/
theorem lintegral_sphereCoordSymmF (g : (Fin 3 → ℝ) → ℝ≥0∞) :
    ∫⁻ c in chartBox, ENNReal.ofReal ((c 0) ^ 2 * Real.sin (c 1)) * g (sphereCoordSymmF c)
      = ∫⁻ y, g y := by
  symm
  calc
    ∫⁻ y, g y = ∫⁻ y in sphereCoordSymmF '' chartBox, g y := by
        rw [← setLIntegral_univ, setLIntegral_congr sphereCoordSymmF_image_ae_univ.symm]
    _ = ∫⁻ c in chartBox,
          ENNReal.ofReal |(sphereCoordCLM c).det| * g (sphereCoordSymmF c) := by
        rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_chartBox
          (fun c _ => (hasFDerivAt_sphereCoordSymmF c).hasFDerivWithinAt) injOn_sphereCoordSymmF]
    _ = ∫⁻ c in chartBox,
          ENNReal.ofReal ((c 0) ^ 2 * Real.sin (c 1)) * g (sphereCoordSymmF c) := by
        apply setLIntegral_congr_fun measurableSet_chartBox
        intro c hc
        have hpos : 0 ≤ (c 0) ^ 2 * Real.sin (c 1) := by
          have := Real.sin_pos_of_pos_of_lt_pi hc.2.1.1 hc.2.1.2
          positivity
        change ENNReal.ofReal |(sphereCoordCLM c).det| * g (sphereCoordSymmF c)
          = ENNReal.ofReal ((c 0) ^ 2 * Real.sin (c 1)) * g (sphereCoordSymmF c)
        rw [det_sphereCoordCLM, abs_of_nonneg hpos]

/-! ## Bridge: `Fin 3 → ℝ` ↔ `ℝ × (ℝ × ℝ)` and to `EuclideanSpace` -/

/-- Volume-preserving reshuffle `(Fin 3 → ℝ) ≃ᵐ ℝ × (ℝ × ℝ)`. -/
def reshuffle : (Fin 3 → ℝ) ≃ᵐ ℝ × ℝ × ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow)

/-- `reshuffle` acts pointwise by reading off the three coordinates. -/
@[simp] lemma reshuffle_apply (c : Fin 3 → ℝ) : reshuffle c = (c 0, c 1, c 2) := by
  simp only [reshuffle, MeasurableEquiv.trans_apply, MeasurableEquiv.piFinSuccAbove_apply,
    MeasurableEquiv.prodCongr, MeasurableEquiv.coe_mk, Equiv.prodCongr_apply]
  rfl

/-- `reshuffle` is volume-preserving. -/
lemma measurePreserving_reshuffle :
    MeasurePreserving reshuffle (volume : Measure (Fin 3 → ℝ)) (volume : Measure (ℝ × ℝ × ℝ)) := by
  have h1 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)
      (volume : Measure (Fin 3 → ℝ)) volume :=
    volume_preserving_piFinSuccAbove (fun _ => ℝ) 0
  have h2 : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow)
      (volume : Measure (ℝ × (Fin 2 → ℝ))) (volume : Measure (ℝ × ℝ × ℝ)) :=
    (MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)
  exact h2.comp h1

/-- `toLp ∘ sphereCoordSymmF` is the repo's Cartesian `sphereChart`. -/
lemma toLp_sphereCoordSymmF (c : Fin 3 → ℝ) :
    (WithLp.toLp 2 (sphereCoordSymmF c) : Spectra.Sobolev.R3)
      = sphereChart (c 0) (c 1) (c 2) := rfl

/-- `radialMeasure.prod sphereMeasure` as a single `withDensity` over the OPEN box. -/
lemma radialMeasure_prod_sphereMeasure_eq :
    radialMeasure.prod sphereMeasure
      = (volume.restrict (Set.Ioi 0 ×ˢ (Set.Ioo 0 π ×ˢ Set.Ioo 0 (2 * π)))).withDensity
          (fun z : ℝ × ℝ × ℝ => ENNReal.ofReal ((z.1) ^ 2) * ENNReal.ofReal (Real.sin z.2.1)) := by
  have hf : AEMeasurable (fun r : ℝ => ENNReal.ofReal (r ^ 2))
      (volume.restrict (Set.Ioi (0:ℝ))) :=
    (measurable_id.pow_const 2).ennreal_ofReal.aemeasurable
  have hg : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Real.sin p.1))
      (volume.restrict (Set.Ioc 0 π ×ˢ Set.Ioc 0 (2 * π))) :=
    (Real.measurable_sin.comp measurable_fst).ennreal_ofReal.aemeasurable
  have hbox : (Set.Ioi (0:ℝ) ×ˢ (Set.Ioc 0 π ×ˢ Set.Ioc 0 (2 * π)))
      =ᵐ[volume] (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo 0 π ×ˢ Set.Ioo 0 (2 * π))) :=
    Measure.set_prod_ae_eq (Filter.EventuallyEq.refl _ _)
      (Measure.set_prod_ae_eq Ioo_ae_eq_Ioc Ioo_ae_eq_Ioc).symm
  simp only [radialMeasure, sphereMeasure]
  rw [prod_withDensity₀ hf hg, Measure.prod_restrict, ← Measure.volume_eq_prod ℝ (ℝ × ℝ),
    Measure.restrict_congr_set hbox]

/-- The spherical chart, uncurried to `ℝ × ℝ × ℝ`, is measurable. -/
lemma measurable_sphereChartProd :
    Measurable (fun p : ℝ × ℝ × ℝ => sphereChart p.1 p.2.1 p.2.2) := by
  have hc : Continuous (fun p : ℝ × ℝ × ℝ => sphereChart p.1 p.2.1 p.2.2) := by
    simp only [sphereChart]
    exact (PiLp.continuous_toLp 2 _).comp (by fun_prop)
  exact hc.measurable

/-- `WithLp.toLp 2` is volume-preserving onto `R3` (with the repo's `borel R3` instances). -/
lemma measurePreserving_toLp_R3 :
    MeasurePreserving (WithLp.toLp 2 : (Fin 3 → ℝ) → Spectra.Sobolev.R3)
      (volume : Measure (Fin 3 → ℝ)) (volume : Measure Spectra.Sobolev.R3) := by
  have h := PiLp.volume_preserving_toLp (Fin 3)
  convert h using 3
  exact BorelSpace.measurable_eq.symm

/-- **The change-of-variables identity for the spherical chart** (lintegral form), bridging the
    Cartesian Lebesgue integral on `ℝ³` to the spherical product measure. -/
theorem lintegral_sphereChart_prod (F : Spectra.Sobolev.R3 → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ p : ℝ × ℝ × ℝ, F (sphereChart p.1 p.2.1 p.2.2) ∂(radialMeasure.prod sphereMeasure)
      = ∫⁻ x, F x ∂(volume : Measure Spectra.Sobolev.R3) := by
  have hH : Measurable (fun p : ℝ × ℝ × ℝ =>
      ENNReal.ofReal (p.1 ^ 2) * ENNReal.ofReal (Real.sin p.2.1)
        * F (sphereChart p.1 p.2.1 p.2.2)) :=
    (by fun_prop : Measurable fun p : ℝ × ℝ × ℝ =>
        ENNReal.ofReal (p.1 ^ 2) * ENNReal.ofReal (Real.sin p.2.1)).mul
      (hF.comp measurable_sphereChartProd)
  have hlt : ∀ᵐ z ∂(volume.restrict
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo 0 π ×ˢ Set.Ioo 0 (2 * π)))),
      ENNReal.ofReal (z.1 ^ 2) * ENNReal.ofReal (Real.sin z.2.1) < ∞ :=
    ae_of_all _ fun _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hbox_meas : MeasurableSet (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo 0 π ×ˢ Set.Ioo 0 (2 * π))) :=
    measurableSet_Ioi.prod (measurableSet_Ioo.prod measurableSet_Ioo)
  have hpre : reshuffle ⁻¹' (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo 0 π ×ˢ Set.Ioo 0 (2 * π))) = chartBox := by
    ext c
    simp only [Set.mem_preimage, reshuffle_apply, Set.mem_prod, Set.mem_Ioi, chartBox,
      Set.mem_setOf_eq]
  calc
    ∫⁻ p, F (sphereChart p.1 p.2.1 p.2.2) ∂(radialMeasure.prod sphereMeasure)
      = ∫⁻ p in (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo 0 π ×ˢ Set.Ioo 0 (2 * π))),
          ENNReal.ofReal (p.1 ^ 2) * ENNReal.ofReal (Real.sin p.2.1)
            * F (sphereChart p.1 p.2.1 p.2.2) ∂volume := by
        rw [radialMeasure_prod_sphereMeasure_eq,
          lintegral_withDensity_eq_lintegral_mul_non_measurable _ (by fun_prop) hlt]
        simp only [Pi.mul_apply]
    _ = ∫⁻ c in chartBox,
          ENNReal.ofReal ((c 0) ^ 2) * ENNReal.ofReal (Real.sin (c 1))
            * F (sphereChart (c 0) (c 1) (c 2)) ∂volume := by
        rw [← measurePreserving_reshuffle.setLIntegral_comp_preimage hbox_meas hH, hpre]
        simp only [reshuffle_apply]
    _ = ∫⁻ c in chartBox,
          ENNReal.ofReal ((c 0) ^ 2 * Real.sin (c 1))
            * F (WithLp.toLp 2 (sphereCoordSymmF c)) ∂volume := by
        apply setLIntegral_congr_fun measurableSet_chartBox
        intro c _
        change ENNReal.ofReal ((c 0) ^ 2) * ENNReal.ofReal (Real.sin (c 1))
            * F (sphereChart (c 0) (c 1) (c 2))
          = ENNReal.ofReal ((c 0) ^ 2 * Real.sin (c 1)) * F (WithLp.toLp 2 (sphereCoordSymmF c))
        rw [← ENNReal.ofReal_mul (sq_nonneg _), ← toLp_sphereCoordSymmF]
    _ = ∫⁻ y, F (WithLp.toLp 2 y) ∂volume :=
        lintegral_sphereCoordSymmF (fun y => F (WithLp.toLp 2 y))
    _ = ∫⁻ x, F x ∂(volume : Measure Spectra.Sobolev.R3) :=
        measurePreserving_toLp_R3.lintegral_comp hF

/-- **The spherical chart is measure-preserving** from the spherical product measure to the
    Cartesian Lebesgue measure on `ℝ³`. -/
theorem measurePreserving_sphereChart :
    MeasurePreserving (fun p : ℝ × ℝ × ℝ => sphereChart p.1 p.2.1 p.2.2)
      (radialMeasure.prod sphereMeasure) (volume : Measure Spectra.Sobolev.R3) := by
  refine ⟨measurable_sphereChartProd, ?_⟩
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply measurable_sphereChartProd hs, ← lintegral_indicator_one
    (measurable_sphereChartProd hs), ← lintegral_indicator_one hs]
  exact lintegral_sphereChart_prod (s.indicator 1) (measurable_one.indicator hs)

/-- The eLpNorm change-of-variables identity for the chart (consumes `AEStronglyMeasurable`). -/
theorem eLpNorm_chartRealizationFun (g : Spectra.Sobolev.R3 → ℂ)
    (hg : AEStronglyMeasurable g (volume : Measure Spectra.Sobolev.R3)) :
    eLpNorm (fun p : ℝ × ℝ × ℝ => g (sphereChart p.1 p.2.1 p.2.2)) 2
        (radialMeasure.prod sphereMeasure)
      = eLpNorm g 2 (volume : Measure Spectra.Sobolev.R3) :=
  eLpNorm_comp_measurePreserving hg measurePreserving_sphereChart

/-- **The forward isometry** `L²(ℝ³, Cartesian) →ₗᵢ L²(ℝ³, spherical)`,
    `g ↦ g ∘ sphereChart`. -/
noncomputable def chartRealizationₗᵢ :
    Spectra.Sobolev.l2R3 →ₗᵢ[ℂ]
      Spectra.QuantumMechanics.Hydrogen.Decomposition.l2R3 :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) (E := ℂ)
    (fun p : ℝ × ℝ × ℝ => sphereChart p.1 p.2.1 p.2.2) measurePreserving_sphereChart

/-- Explicit inverse of `sphereCoordSymmF` on the non-slit set. -/
def sphereCoordSymmInvF (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2),
    Real.arccos (y 2 / Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2)),
    if 0 < y 1 then Complex.arg ⟨y 0, y 1⟩ else Complex.arg ⟨y 0, y 1⟩ + 2 * Real.pi]

/-- `sphereCoordSymmInvF y` lies in `chartBox` and is a right inverse of `sphereCoordSymmF`,
    for every `y` with nonzero middle coordinate. -/
lemma sphereCoordSymmInvF_spec (y : Fin 3 → ℝ) (hy : y 1 ≠ 0) :
    sphereCoordSymmInvF y ∈ chartBox ∧ sphereCoordSymmF (sphereCoordSymmInvF y) = y :=
  sphereCoordSymmInv_spec_aux y hy

/-- `sphereCoordSymmInvF` is a left inverse of `sphereCoordSymmF` on `chartBox`, provided the
    third coordinate does not lie in the (measure-zero) exceptional set `sin c 2 = 0`. -/
lemma sphereCoordSymmInvF_leftInv (c : Fin 3 → ℝ) (hc : c ∈ chartBox)
    (hs : Real.sin (c 2) ≠ 0) : sphereCoordSymmInvF (sphereCoordSymmF c) = c := by
  have hy1 : (sphereCoordSymmF c) 1 ≠ 0 := by
    rw [sphereCoordSymmF_one]
    exact mul_ne_zero (mul_ne_zero (ne_of_gt hc.1)
      (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hc.2.1.1 hc.2.1.2))) hs
  obtain ⟨hmem, heq⟩ := sphereCoordSymmInvF_spec (sphereCoordSymmF c) hy1
  exact injOn_sphereCoordSymmF hmem hc heq

/-- The (a.e.) inverse chart `ℝ³ → ℝ × ℝ × ℝ`. -/
def sphereChartInv (x : Spectra.Sobolev.R3) : ℝ × ℝ × ℝ :=
  reshuffle (sphereCoordSymmInvF (WithLp.ofLp x))

/-- `sphereCoordSymmInvF` is measurable. -/
lemma measurable_sphereCoordSymmInvF : Measurable sphereCoordSymmInvF := by
  have hmk : Measurable (fun y : Fin 3 → ℝ => (⟨y 0, y 1⟩ : ℂ)) := by
    have h : (fun y : Fin 3 → ℝ => (⟨y 0, y 1⟩ : ℂ))
        = Complex.measurableEquivRealProd.symm ∘ (fun y => (y 0, y 1)) := by funext y; rfl
    rw [h]; exact Complex.measurableEquivRealProd.symm.measurable.comp (by fun_prop)
  rw [measurable_pi_iff]
  intro i
  fin_cases i
  · change Measurable (fun y : Fin 3 → ℝ => Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2))
    fun_prop
  · change Measurable (fun y : Fin 3 → ℝ =>
      Real.arccos (y 2 / Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2)))
    exact Real.measurable_arccos.comp (by fun_prop)
  · change Measurable (fun y : Fin 3 → ℝ =>
      if 0 < y 1 then Complex.arg ⟨y 0, y 1⟩ else Complex.arg ⟨y 0, y 1⟩ + 2 * Real.pi)
    refine Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply 1)) ?_ ?_
    · exact Complex.measurable_arg.comp hmk
    · exact (Complex.measurable_arg.comp hmk).add_const _

/-- `sphereChartInv` is measurable. -/
lemma measurable_sphereChartInv : Measurable sphereChartInv :=
  reshuffle.measurable.comp
    (measurable_sphereCoordSymmInvF.comp (PiLp.continuous_ofLp 2 _).measurable)

/-- `sphereChartInv` is a left inverse of the spherical chart at any `p` whose coordinate triple
    lies in `chartBox` and avoids the exceptional set `sin p.2.2 = 0`. -/
lemma sphereChartInv_sphereChart (p : ℝ × ℝ × ℝ)
    (hp : ![p.1, p.2.1, p.2.2] ∈ chartBox) (hs : Real.sin p.2.2 ≠ 0) :
    sphereChartInv (sphereChart p.1 p.2.1 p.2.2) = p := by
  have h1 : (WithLp.ofLp (sphereChart p.1 p.2.1 p.2.2) : Fin 3 → ℝ)
      = sphereCoordSymmF ![p.1, p.2.1, p.2.2] := by
    rw [show sphereChart p.1 p.2.1 p.2.2
        = WithLp.toLp 2 (sphereCoordSymmF ![p.1, p.2.1, p.2.2])
      from (toLp_sphereCoordSymmF ![p.1, p.2.1, p.2.2]).symm, WithLp.ofLp_toLp]
  unfold sphereChartInv
  rw [h1, sphereCoordSymmInvF_leftInv ![p.1, p.2.1, p.2.2] hp hs, reshuffle_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]

/-- `sphereChartInv` is a left inverse of the spherical chart, `radialMeasure.prod sphereMeasure`-
    almost everywhere (the exceptional non-slit set is null). -/
lemma sphereChartInv_comp_ae :
    (fun p : ℝ × ℝ × ℝ => sphereChartInv (sphereChart p.1 p.2.1 p.2.2))
      =ᵐ[radialMeasure.prod sphereMeasure] id := by
  have hac : radialMeasure.prod sphereMeasure ≪ (volume : Measure (ℝ × ℝ × ℝ)) := by
    rw [radialMeasure_prod_sphereMeasure_eq]
    exact (withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hbox : ∀ᵐ p ∂(radialMeasure.prod sphereMeasure),
      p ∈ (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo 0 π ×ˢ Set.Ioo 0 (2 * π))) := by
    rw [radialMeasure_prod_sphereMeasure_eq]
    exact (ae_restrict_mem
      (measurableSet_Ioi.prod (measurableSet_Ioo.prod measurableSet_Ioo))).filter_mono
      (withDensity_absolutelyContinuous _ _).ae_le
  have hpi : ∀ᵐ p ∂(radialMeasure.prod sphereMeasure), p.2.2 ≠ π := by
    have hnull : (volume : Measure (ℝ × ℝ × ℝ)) {p | p.2.2 = π} = 0 := by
      have hset : {p : ℝ × ℝ × ℝ | p.2.2 = π} = Set.univ ×ˢ (Set.univ ×ˢ {π}) := by
        ext p; simp
      rw [hset, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod,
        Measure.prod_prod, Real.volume_singleton, mul_zero, mul_zero]
    refine (?_ : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ × ℝ)), p.2.2 ≠ π).filter_mono hac.ae_le
    rw [ae_iff]; simpa using hnull
  filter_upwards [hbox, hpi] with p hp hpi'
  have hmem : ![p.1, p.2.1, p.2.2] ∈ chartBox := ⟨hp.1, hp.2.1, hp.2.2⟩
  have hs : Real.sin p.2.2 ≠ 0 := by
    rcases lt_trichotomy p.2.2 π with h | h | h
    · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hp.2.2.1 h)
    · exact absurd h hpi'
    · have h2 : p.2.2 - 2 * π < 0 := by have := hp.2.2.2; linarith
      have h3 : -π < p.2.2 - 2 * π := by linarith
      have hneg := Real.sin_neg_of_neg_of_neg_pi_lt h2 h3
      rw [Real.sin_sub_two_pi] at hneg
      exact ne_of_lt hneg
  exact sphereChartInv_sphereChart p hmem hs

/-- **The (a.e.) inverse chart is measure-preserving**, in the reverse direction of
    `measurePreserving_sphereChart` (Cartesian → spherical). -/
theorem measurePreserving_sphereChartInv :
    MeasurePreserving sphereChartInv (volume : Measure Spectra.Sobolev.R3)
      (radialMeasure.prod sphereMeasure) := by
  refine ⟨measurable_sphereChartInv, ?_⟩
  rw [← measurePreserving_sphereChart.map_eq, Measure.map_map measurable_sphereChartInv
    measurable_sphereChartProd, show (sphereChartInv ∘ fun p : ℝ × ℝ × ℝ =>
      sphereChart p.1 p.2.1 p.2.2) = fun p => sphereChartInv (sphereChart p.1 p.2.1 p.2.2) from rfl,
    Measure.map_congr sphereChartInv_comp_ae, Measure.map_id]

/-- Shared surjectivity witness: precomposing `h` with the (a.e.) inverse chart and then with the
    forward chart returns `h`. Used both to build `chartRealization` (as the surjectivity proof
    of `chartRealizationₗᵢ`) and, once `chartRealization` exists, to identify
    `chartRealization.symm h` in `chartRealization_symm_coeFn`. -/
private theorem chartRealizationₗᵢ_comp_inv
    (h : Spectra.QuantumMechanics.Hydrogen.Decomposition.l2R3) :
    chartRealizationₗᵢ (MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) (E := ℂ) sphereChartInv
      measurePreserving_sphereChartInv h) = h := by
  have key : chartRealizationₗᵢ (MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) (E := ℂ)
      sphereChartInv measurePreserving_sphereChartInv h)
      = MeasureTheory.Lp.compMeasurePreserving
          (fun p : ℝ × ℝ × ℝ => sphereChart p.1 p.2.1 p.2.2) measurePreserving_sphereChart
          (MeasureTheory.Lp.compMeasurePreserving
            sphereChartInv measurePreserving_sphereChartInv h) :=
    rfl
  rw [key]
  refine Lp.ext ?_
  have e1 := MeasureTheory.Lp.coeFn_compMeasurePreserving
    (MeasureTheory.Lp.compMeasurePreserving sphereChartInv measurePreserving_sphereChartInv h)
    measurePreserving_sphereChart
  have e2 := MeasureTheory.Lp.coeFn_compMeasurePreserving h measurePreserving_sphereChartInv
  have e3 := measurePreserving_sphereChart.quasiMeasurePreserving.ae_eq_comp e2
  have e4 := sphereChartInv_comp_ae.fun_comp (⇑h)
  filter_upwards [e1, e3, e4] with p h1 h3 h4
  simp only [Function.comp_apply, id_eq] at h1 h3 h4 ⊢
  rw [h1, h3]; exact h4

/-- **The chart-realization unitary** `L²(ℝ³, Cartesian) ≃ₗᵢ L²(ℝ³, spherical)`. -/
noncomputable def chartRealization :
    Spectra.Sobolev.l2R3 ≃ₗᵢ[ℂ]
      Spectra.QuantumMechanics.Hydrogen.Decomposition.l2R3 :=
  LinearIsometryEquiv.ofSurjective chartRealizationₗᵢ (fun h =>
    ⟨MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) (E := ℂ) sphereChartInv
      measurePreserving_sphereChartInv h, chartRealizationₗᵢ_comp_inv h⟩)

/-- The forward unitary acts a.e. as precomposition with the spherical chart. -/
lemma chartRealization_coeFn (g : Spectra.Sobolev.l2R3) :
    ⇑(chartRealization g) =ᵐ[radialMeasure.prod sphereMeasure]
      fun p : ℝ × ℝ × ℝ => g (sphereChart p.1 p.2.1 p.2.2) :=
  MeasureTheory.Lp.coeFn_compMeasurePreserving g measurePreserving_sphereChart

/-- The inverse unitary acts a.e. as precomposition with the (a.e.) inverse chart. -/
lemma chartRealization_symm_coeFn
    (h : Spectra.QuantumMechanics.Hydrogen.Decomposition.l2R3) :
    ⇑(chartRealization.symm h) =ᵐ[volume] fun x : Spectra.Sobolev.R3 => h (sphereChartInv x) := by
  have hΨ : chartRealization.symm h
      = MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) (E := ℂ) sphereChartInv
          measurePreserving_sphereChartInv h := by
    apply chartRealization.injective
    rw [chartRealization.apply_symm_apply]
    exact (chartRealizationₗᵢ_comp_inv h).symm
  rw [hΨ]
  exact MeasureTheory.Lp.coeFn_compMeasurePreserving h measurePreserving_sphereChartInv

end

end Spectra.QuantumMechanics.Hydrogen.Decomposition
