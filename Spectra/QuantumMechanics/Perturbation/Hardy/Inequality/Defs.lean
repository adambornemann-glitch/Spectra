/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Sobolev.WeakDerivative
import Spectra.Spaces.Sobolev.IntegrationByParts
import Spectra.Spaces.Sobolev.DensityResults
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
/-!
# The Hardy Inequality in Three Dimensions — the smooth vanishing-near-origin case

The three-dimensional Hardy inequality:

  ∫_{ℝ³} |ψ(x)|²/|x|² dx ≤ 4 ∫_{ℝ³} |∇ψ(x)|² dx

for ψ ∈ H¹(ℝ³). The constant 4 = (d−2)⁻² · 4 for d = 3 is sharp.

## Role in the hydrogen atom

This inequality is the *analytic engine* of the Kato-Rellich argument.
It says that the Coulomb potential 1/|x| is controlled by the kinetic
energy −Δ in the sense of quadratic forms. Concretely, it gives:

  ‖(1/r)ψ‖² ≤ 4 ⟨−Δψ, ψ⟩

which, after applying Cauchy's inequality with ε, yields:

  ‖(1/r)ψ‖ ≤ ε‖Δψ‖ + C_ε‖ψ‖    for any ε > 0

This is the *relative boundedness with bound zero* of 1/r with respect
to −Δ, which is the hypothesis of Kato-Rellich.

## This file

This file builds the analytic core (`inverseRSq`, `inverseR`, the Hardy vector field
`hardyField`, and the Hardy integral `hardyIntegral`), then proves **Step 1** of the proof
strategy: Hardy's inequality for real, smooth, compactly supported functions that additionally
**vanish near the origin** (`hardy_inequality_smooth_of_vanishing`), by integration by parts in
spherical coordinates:

  ∫ |ψ|²/r² dx = −2 Re ∫ (ψ̄/r)(r̂ · ∇ψ) dx
                ≤ 2 (∫ |ψ|²/r²)^{1/2} (∫ |∇ψ|²)^{1/2}

Dividing both sides by (∫ |ψ|²/r²)^{1/2} gives the result. The integration by parts identity
comes from `div(r̂/r) = (d−2)/r²` in d dimensions (`= 1/r²` for d = 3) and the divergence
theorem on ℝ³ \ B(0,ε), then ε → 0.

`Hardy.Inequality.Basic` removes the vanishing-near-origin restriction (a second cutoff, this
time an *inner* one), extends from smooth functions to all of H¹ by density, and derives the
operator-theoretic corollaries consumed by `CoulombBound.lean` and `KatoRellich.lean`.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975], Theorem X.2.
* [Lieb, Loss, *Analysis*][lieb2001], Theorem 7.17.
* [Kato, *Perturbation Theory for Linear Operators*][kato1995], §V.5.
-/
open MeasureTheory Complex Filter ContinuousLinearMap
open MeasurableSet ContDiffBump Topology
open Spectra.Sobolev
open scoped Topology NNReal ENNReal TopologicalSpace ProbabilityTheory Pointwise ContDiff

namespace Spectra.QuantumMechanics.Hydrogen

/-! ## The inverse-square weight

We need the function x ↦ 1/|x|² as a measurable function on ℝ³,
and its interaction with L² functions.
-/

/-- The Euclidean norm on ℝ³. -/
noncomputable def euclideanNorm (x : R3) : ℝ := ‖x‖

/-- The inverse-square weight: x ↦ 1/|x|². -/
noncomputable def inverseRSq (x : R3) : ℝ :=
  if ‖x‖ = 0 then 0 else 1 / ‖x‖ ^ 2

/-- The inverse weight: x ↦ 1/|x|. -/
noncomputable def inverseR (x : R3) : ℝ :=
  if ‖x‖ = 0 then 0 else 1 / ‖x‖

/-- inverseRSq is measurable. -/
lemma inverseRSq_measurable : Measurable inverseRSq := by
  unfold inverseRSq
  exact Measurable.ite (measurableSet_eq_fun measurable_norm measurable_const)
    measurable_const (measurable_const.div (measurable_norm.pow_const 2))

/-- inverseR is measurable. -/
lemma inverseR_measurable : Measurable inverseR := by
  unfold inverseR
  exact Measurable.ite (measurableSet_eq_fun measurable_norm measurable_const)
    measurable_const (measurable_const.div measurable_norm)

/-- inverseRSq is non-negative. -/
lemma inverseRSq_nonneg (x : R3) : 0 ≤ inverseRSq x := by
  simp only [inverseRSq]
  split_ifs <;> positivity

/-- inverseR is non-negative. -/
lemma inverseR_nonneg (x : R3) : 0 ≤ inverseR x := by
  simp only [inverseR]
  split_ifs <;> positivity

/-- 1/|x| is locally L² on ℝ³ (integrable on any ball).

    **Discharge route:** In spherical coordinates,
    ∫_{B(0,R)} 1/|x|² dx = ∫_0^R ∫_{S²} (1/r²) r² dr dΩ
                           = 4π ∫_0^R dr = 4πR < ∞.
    The key is that the r² from the volume element cancels the 1/r². -/
theorem inverseRSq_integrableOn_ball (R : ℝ) :
    IntegrableOn inverseRSq (Metric.ball (0 : R3) R) volume := by
  haveI : (volume : Measure R3).IsAddHaarMeasure := by
    infer_instance
  have hfr : Module.finrank ℝ R3 = 3 := finrank_euclideanSpace_fin
  -- Almost every point of `R3` is nonzero (the origin is a null set).
  have hae : ∀ᵐ x ∂(volume : Measure R3), x ≠ 0 := by
    have hsing : (volume : Measure R3) {x : R3 | x = 0} = 0 := by
      have : {x : R3 | x = 0} = {(0 : R3)} := by ext x; simp
      rw [this]; exact measure_singleton 0
    rw [ae_iff]; simp only [ne_eq, not_not]; exact hsing
  -- Apply the `‖x‖^(-α)` integrability criterion with `α = 2 < 3 = dim ℝ³`.
  refine integrableOn_ball_of_norm_le_rpow (f := inverseRSq) (C := 1) (α := 2)
    ?_ ?_ ?_ inverseRSq_measurable.aestronglyMeasurable
  · rw [hfr]; norm_num
  · rw [hfr]; norm_num
  · filter_upwards [ae_restrict_of_ae hae] with x hx
    have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
    rw [inverseRSq, if_neg hnx, one_mul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), Real.rpow_neg hpos.le,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, ← one_div]

/-! ## The Hardy vector field

The vector field g(x) = x/‖x‖² on ℝ³ \ {0}. Its divergence is 1/‖x‖²,
which is what extracts the Hardy weight from the IBP identity.
-/

/-- The Hardy vector field: g(x) = x/‖x‖² for x ≠ 0, 0 at the origin.

    Used in the IBP proof of Hardy's inequality: ∫ ∇(|φ|²) · g = -∫ |φ|²/‖x‖²
    for φ smooth with compact support away from 0. -/
noncomputable def hardyField : R3 → R3 := fun x =>
  if x = 0 then 0 else (‖x‖^2)⁻¹ • x

/-- Off the origin, `hardyField x = x/‖x‖²`. -/
lemma hardyField_of_ne {x : R3} (hx : x ≠ 0) :
    hardyField x = (‖x‖^2)⁻¹ • x := by
  unfold hardyField
  exact if_neg hx

/-- `hardyField` vanishes at the origin (by convention). -/
@[simp] lemma hardyField_zero : hardyField (0 : R3) = 0 := by
  unfold hardyField
  exact if_pos rfl

/-- The norm of `hardyField` off the origin: `‖g(x)‖ = 1/‖x‖`. -/
lemma norm_hardyField_of_ne {x : R3} (hx : x ≠ 0) :
    ‖hardyField x‖ = ‖x‖⁻¹ := by
  rw [hardyField_of_ne hx, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _)), sq, mul_inv]
  field_simp

/-- `hardyField` is smooth on `ℝ³ \ {0}`.

    The proof: off the origin, `hardyField x = (‖x‖²)⁻¹ • x`. The norm-squared
    `‖·‖²` is smooth (bilinear inner product), nonzero away from 0, so its
    inverse is smooth there. Scalar-multiplying by the smooth identity preserves
    smoothness. -/
lemma hardyField_contDiffOn :
    ContDiffOn ℝ ∞ hardyField ({0}ᶜ : Set R3) := by
  -- Step 1: (‖x‖²)⁻¹ is smooth on the complement of {0}.
  have h_inv : ContDiffOn ℝ ∞ (fun x : R3 => (‖x‖^2)⁻¹) ({0}ᶜ : Set R3) := by
    refine ContDiffOn.inv (contDiff_norm_sq (𝕜 := ℝ)).contDiffOn ?_
    intro x hx
    have hx_ne : x ≠ 0 := by simpa using hx
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hx_ne)
  -- Step 2: smul of a smooth scalar field with the (smooth) identity.
  have h_smul : ContDiffOn ℝ ∞ (fun x : R3 => (‖x‖^2)⁻¹ • x) ({0}ᶜ : Set R3) :=
    h_inv.smul contDiff_id.contDiffOn
  -- Step 3: this agrees with `hardyField` off the origin.
  exact h_smul.congr (fun x hx => by
    have : x ≠ 0 := by simpa using hx
    exact hardyField_of_ne this)

/-- Diagonal Jacobian entry of the Hardy vector field.

    `∂ᵢ(xᵢ/‖x‖²)(x) = 1/‖x‖² − 2(xᵢ)²/‖x‖⁴` for `x ≠ 0` in ℝ³, where the
    `i`-th component of the directional derivative in direction `eᵢ` realises
    the `(i,i)` entry of the Jacobian. Quotient rule. -/
private lemma hardyField_diag_jacobian (x : R3) (hx : x ≠ 0) (i : Fin 3) :
    (fderiv ℝ hardyField x (EuclideanSpace.single i 1)) i
      = (‖x‖^2)⁻¹ - 2 * (x i)^2 / (‖x‖^2)^2 := by
  have hxsq_ne : ‖x‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  -- (1) HasFDerivAt for hardyField at x, via the smul expression.
  have h_norm_sq : HasFDerivAt (fun y : R3 => ‖y‖^2) (2 • innerSL ℝ x : R3 →L[ℝ] ℝ) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h_inv : HasFDerivAt (fun y : R3 => (‖y‖^2)⁻¹)
      ((toSpanSingleton ℝ (-((‖x‖^2)^2)⁻¹)).comp (2 • innerSL ℝ x : R3 →L[ℝ] ℝ)) x :=
    (hasFDerivAt_inv hxsq_ne).comp x h_norm_sq
  have h_smul := h_inv.smul (hasFDerivAt_id x)
  have h_evEq : hardyField =ᶠ[𝓝 x] (fun y : R3 => (‖y‖^2)⁻¹ • y) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds
      (Set.mem_compl_singleton_iff.mpr hx)] with y hy
    exact hardyField_of_ne (Set.mem_compl_singleton_iff.mp hy)
  have h_hardy := h_smul.congr_of_eventuallyEq h_evEq
  -- (2) Unfold the CLM application at e_i and take the i-th component.
  have h_inner : inner (𝕜 := ℝ) x (EuclideanSpace.single i (1:ℝ)) = x.ofLp i := by
    simpa using EuclideanSpace.inner_single_right (𝕜 := ℝ) i (1:ℝ) x
  simp [h_hardy.fderiv, h_inner]
  ring

/-- **Pointwise divergence** of the Hardy vector field on ℝ³ ∖ {0}:
    `∑ᵢ ∂ᵢ(xᵢ/‖x‖²) = 1/‖x‖²`.

    The dimension `d = 3` enters via the cardinality of `Fin 3`: in general
    dimension the formula is `(d−2)/‖x‖²`. Three is the minimum dimension where
    this divergence is positive — and it's what makes Hardy work in 3D. -/
lemma hardyField_div (x : R3) (hx : x ≠ 0) :
    ∑ i : Fin 3, (fderiv ℝ hardyField x (EuclideanSpace.single i 1)) i = (‖x‖^2)⁻¹ := by
  have _hxsq_ne : ‖x‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  -- Reduce each summand to the diagonal formula.
  simp_rw [hardyField_diag_jacobian x hx]
  -- ∑ᵢ ((‖x‖²)⁻¹ − 2(xᵢ)²/(‖x‖²)²) = 3·(‖x‖²)⁻¹ − 2·(∑ᵢ(xᵢ)²)/(‖x‖²)²
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  -- Factor out the constant 2/(‖x‖²)² from the remaining sum.
  conv_lhs =>
    rhs; arg 2; ext i;
    rw [show (2 : ℝ) * (x i)^2 / (‖x‖^2)^2 = (2 / (‖x‖^2)^2) * (x i)^2 from by ring]
  rw [← Finset.mul_sum]
  -- ∑ᵢ (xᵢ)² = ‖x‖² for x ∈ EuclideanSpace ℝ (Fin 3).
  have h_sum_sq : ∑ i : Fin 3, (x i)^2 = ‖x‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Real.norm_eq_abs, sq_abs]
  rw [h_sum_sq]
  -- 3·(‖x‖²)⁻¹ − 2·‖x‖²/(‖x‖²)² = (‖x‖²)⁻¹.
  rw [nsmul_eq_mul]
  push_cast
  field_simp
  ring

/-! ## The Hardy integral

The weighted L² norm ∫|ψ|²/|x|² that Hardy's inequality controls.
-/

/-- The Hardy integral: ∫ |ψ(x)|²/|x|² dx.

    Defined as the Lebesgue integral ∫ inverseRSq(x) · |ψ(x)|² dx.
    May be infinite if ψ is not in the Hardy domain. -/
noncomputable def hardyIntegral (ψ : l2R3) : ℝ :=
  ∫ x, inverseRSq x * ‖(ψ : R3 → ℂ) x‖ ^ 2

/-- The Hardy integral is non-negative. -/
lemma hardyIntegral_nonneg (ψ : l2R3) : 0 ≤ hardyIntegral ψ := by
  apply integral_nonneg
  intro x
  exact mul_nonneg (inverseRSq_nonneg x) (sq_nonneg _)

/-! ## Hardy's inequality: smooth case

The core estimate, proved for C_c^∞ functions where integration by parts
is classical.
-/
/-! ### Helpers for the IBP step -/

/-- Each component `x ↦ (hardyField x) i` is smooth on `ℝ³ \ {0}`. -/
private lemma hardyField_apply_contDiffOn (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun x : R3 => hardyField x i) ({0}ᶜ : Set R3) := by
  exact (EuclideanSpace.proj i).contDiff.comp_contDiffOn hardyField_contDiffOn

/-- If `u` vanishes on the open ball `B(0, r)` with `r > 0`, then the topological
    support of `u` avoids the origin.

    Used to discharge the differentiability hypothesis in the per-direction IBP
    step: we need `(hardyField · i)` to be differentiable on `tsupport u`, and
    `hardyField · i` is smooth precisely on `{0}ᶜ`. -/
private lemma tsupport_subset_compl_zero
    (u : R3 → ℝ) (r : ℝ) (hr_pos : 0 < r) (hu_zero : ∀ x, ‖x‖ < r → u x = 0) :
    tsupport u ⊆ ({0}ᶜ : Set R3) := by
  -- `support u ⊆ {x | r ≤ ‖x‖}` (a closed set not containing 0).
  have h_supp : Function.support u ⊆ {x : R3 | r ≤ ‖x‖} := fun y hy =>
    not_lt.mp fun h_lt => hy (hu_zero y h_lt)
  have h_closed : IsClosed {x : R3 | r ≤ ‖x‖} :=
    isClosed_le continuous_const continuous_norm
  have h_tsupp : tsupport u ⊆ {x : R3 | r ≤ ‖x‖} :=
    closure_minimal h_supp h_closed
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro heq
  have : r ≤ ‖x‖ := h_tsupp hx
  rw [heq, norm_zero] at this
  linarith

/-- If `u` vanishes on `B(0, r)`, then so does any directional derivative.
    No smoothness needed — only that `u = 0` on an open ball. -/
private lemma fderiv_apply_eq_zero_of_ball
    {u : R3 → ℝ}
    (r : ℝ) (_hr_pos : 0 < r) (hu_zero : ∀ x, ‖x‖ < r → u x = 0)
    (v : R3) {x : R3} (hx : ‖x‖ < r) :
    fderiv ℝ u x v = 0 := by
  have h_ball_x : Metric.ball (0 : R3) r ∈ 𝓝 x := by
    apply IsOpen.mem_nhds Metric.isOpen_ball
    rw [Metric.mem_ball, dist_zero_right]
    exact hx
  have h_eq : u =ᶠ[𝓝 x] (fun _ : R3 => (0 : ℝ)) := by
    filter_upwards [h_ball_x] with y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact hu_zero y hy
  rw [h_eq.fderiv_eq, fderiv_const_apply]
  rfl

/-- Integrability of a product where one factor is continuous + compactly supported
    + vanishes on `B(0, r)`, and the other factor is continuous on `ℝ³ \ {0}`.

    Continuity at `0` follows because the product is identically `0` on the open ball;
    continuity elsewhere is the standard product rule. -/
private lemma integrable_mul_singular
    {u : R3 → ℝ} (hu_cont : Continuous u) (hu_supp : HasCompactSupport u)
    (r : ℝ) (hr_pos : 0 < r) (hu_zero : ∀ x, ‖x‖ < r → u x = 0)
    {g : R3 → ℝ} (hg_cont : ContinuousOn g ({0}ᶜ : Set R3)) :
    Integrable (fun x => u x * g x) volume := by
  haveI : IsFiniteMeasureOnCompacts (volume : Measure R3) := by
    infer_instance
  refine Continuous.integrable_of_hasCompactSupport ?_ hu_supp.mul_right
  rw [continuous_iff_continuousAt]
  intro x₀
  by_cases hx₀ : x₀ = 0
  · subst hx₀
    have h_eq : (fun x : R3 => u x * g x) =ᶠ[𝓝 0] (fun _ => (0 : ℝ)) := by
      filter_upwards [Metric.ball_mem_nhds (0 : R3) hr_pos] with y hy
      rw [Metric.mem_ball, dist_zero_right] at hy
      rw [hu_zero y hy, zero_mul]
    exact continuous_const.continuousAt.congr_of_eventuallyEq h_eq
  · refine ContinuousAt.mul hu_cont.continuousAt ?_
    have hx₀_mem : x₀ ∈ ({0}ᶜ : Set R3) := by simpa using hx₀
    exact (hg_cont x₀ hx₀_mem).continuousAt
      (isOpen_compl_singleton.mem_nhds hx₀_mem)

/-- IBP integrand `(∂ᵢu) · gᵢ` is integrable. -/
private lemma integrable_fderiv_u_mul_hardyField
    {u : R3 → ℝ} (hu_smooth : ContDiff ℝ ∞ u) (hu_supp : HasCompactSupport u)
    (r : ℝ) (hr_pos : 0 < r) (hu_zero : ∀ x, ‖x‖ < r → u x = 0)
    (i : Fin 3) :
    Integrable (fun x =>
      fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ)) * hardyField x i) volume := by
  refine integrable_mul_singular
    (u := fun x => fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ)))
    (g := fun x => hardyField x i)
    ?_ (hu_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i (1 : ℝ))) r hr_pos ?_
    (hardyField_apply_contDiffOn i).continuousOn
  · exact (hu_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  · intro x hx
    exact fderiv_apply_eq_zero_of_ball r hr_pos hu_zero _ hx

/-- IBP integrand `u · (∂ᵢgᵢ)` is integrable. -/
private lemma integrable_u_mul_fderiv_hardyField
    {u : R3 → ℝ} (hu_cont : Continuous u) (hu_supp : HasCompactSupport u)
    (r : ℝ) (hr_pos : 0 < r) (hu_zero : ∀ x, ‖x‖ < r → u x = 0)
    (i : Fin 3) :
    Integrable (fun x => u x *
      fderiv ℝ (fun y => hardyField y i) x (EuclideanSpace.single i (1 : ℝ))) volume := by
  refine integrable_mul_singular hu_cont hu_supp r hr_pos hu_zero ?_
  refine ContinuousOn.clm_apply ?_ continuousOn_const
  exact (hardyField_apply_contDiffOn i).continuousOn_fderiv_of_isOpen
    isOpen_compl_singleton (by simp)

/-- IBP integrand `u · gᵢ` is integrable. -/
private lemma integrable_u_mul_hardyField
    {u : R3 → ℝ} (hu_cont : Continuous u) (hu_supp : HasCompactSupport u)
    (r : ℝ) (hr_pos : 0 < r) (hu_zero : ∀ x, ‖x‖ < r → u x = 0)
    (i : Fin 3) :
    Integrable (fun x => u x * hardyField x i) volume :=
  integrable_mul_singular hu_cont hu_supp r hr_pos hu_zero
    (hardyField_apply_contDiffOn i).continuousOn

/-- Per-direction integration by parts: for `u` smooth with compact support vanishing
    near `0`, integrate `u` against the `i`-th derivative of `hardyField · i` and move
    the derivative onto `u` (with a sign flip). -/
private lemma ibp_direction_hardyField
    {u : R3 → ℝ} (hu_smooth : ContDiff ℝ ∞ u) (hu_supp : HasCompactSupport u)
    (r : ℝ) (hr_pos : 0 < r) (hu_zero : ∀ x, ‖x‖ < r → u x = 0)
    (i : Fin 3) :
    ∫ x, u x * fderiv ℝ (fun y => hardyField y i) x (EuclideanSpace.single i (1 : ℝ)) ∂volume
      = - ∫ x, fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ)) * hardyField x i ∂volume := by
  haveI : (volume : Measure R3).IsAddHaarMeasure := by
    infer_instance
  -- tsupport u ⊆ {x : r ≤ ‖x‖}
  have h_tsupp : tsupport u ⊆ {x : R3 | r ≤ ‖x‖} := by
    refine closure_minimal ?_ (isClosed_le continuous_const continuous_norm)
    intro y hy
    exact not_lt.mp fun h_lt => hy (hu_zero y h_lt)
  -- Smooth cutoff: bump = 1 on B(0, r/3), 0 outside B(0, r/2); χ := 1 - bump.
  let bump : ContDiffBump (0 : R3) :=
    { rIn := r / 3, rOut := r / 2,
      rIn_pos := by linarith, rIn_lt_rOut := by linarith }
  let χ : R3 → ℝ := fun x => 1 - bump x
  have hχ_smooth : ContDiff ℝ ∞ χ := contDiff_const.sub bump.contDiff
  have hχ_eq_one_outside : ∀ {x : R3}, r/2 ≤ ‖x‖ → χ x = 1 := by
    intro x hx
    have h_dist : bump.rOut ≤ dist x 0 := by simpa [dist_zero_right] using hx
    simp [χ, bump.zero_of_le_dist h_dist]
  have hχ_eq_zero_in_ball : ∀ {x : R3}, ‖x‖ ≤ r/3 → χ x = 0 := by
    intro x hx
    have h_in : x ∈ Metric.closedBall (0 : R3) (r/3) := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hx
    simp [χ, bump.one_of_mem_closedBall h_in]
  -- Regularized gReg := χ · (hardyField · i). Globally C^∞.
  let gReg : R3 → ℝ :=
    fun x => χ x * hardyField x i
  have hgReg_smooth : ContDiff ℝ ∞ gReg := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · subst hx
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      have h_nhds : Metric.ball (0 : R3) (r/3) ∈ 𝓝 0 :=
        Metric.ball_mem_nhds _ (by linarith)
      filter_upwards [h_nhds] with y hy
      have hy_norm : ‖y‖ ≤ r/3 := by
        rw [Metric.mem_ball, dist_zero_right] at hy; linarith
      simp [gReg, hχ_eq_zero_in_ball hy_norm]
    · have h_in : x ∈ ({0}ᶜ : Set R3) := by simpa using hx
      exact hχ_smooth.contDiffAt.mul
        ((hardyField_apply_contDiffOn i).contDiffAt
          (isOpen_compl_singleton.mem_nhds h_in))
  -- On a neighborhood of any x ∈ tsupport u: χ = 1, so gReg = hardyField · i nearby.
  have h_gReg_eq_nbhd : ∀ x ∈ tsupport u, gReg =ᶠ[𝓝 x] (fun y => hardyField y i) := by
    intro x hx
    have h_strict : r/2 < ‖x‖ := lt_of_lt_of_le (by linarith) (h_tsupp hx)
    have h_open_nhds : {y : R3 | r/2 < ‖y‖} ∈ 𝓝 x :=
      IsOpen.mem_nhds (isOpen_lt continuous_const continuous_norm) h_strict
    filter_upwards [h_open_nhds] with y hy
    change gReg y = hardyField y i
    simp [gReg, hχ_eq_one_outside (le_of_lt hy)]
  have h_gReg_eq_at : ∀ x ∈ tsupport u, gReg x = hardyField x i :=
    fun x hx => (h_gReg_eq_nbhd x hx).eq_of_nhds
  have h_fgReg_eq_at : ∀ x ∈ tsupport u,
      fderiv ℝ gReg x = fderiv ℝ (fun y => hardyField y i) x :=
    fun x hx => (h_gReg_eq_nbhd x hx).fderiv_eq
  -- Integrability for the gReg versions (smooth · smooth-cs is integrable).
  have h_int_du_gReg : Integrable
      (fun x => fderiv ℝ u x (EuclideanSpace.single i (1:ℝ)) * gReg x) volume := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hu_smooth.continuous_fderiv (by simp)).clm_apply continuous_const).mul
        hgReg_smooth.continuous
    · exact (hu_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i (1:ℝ))).mul_right
  have h_int_u_dgReg : Integrable
      (fun x => u x * fderiv ℝ gReg x (EuclideanSpace.single i (1:ℝ))) volume := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hu_smooth.continuous.mul
        ((hgReg_smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
    · exact hu_supp.mul_right
  have h_int_u_gReg : Integrable (fun x => u x * gReg x) volume := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hu_smooth.continuous.mul hgReg_smooth.continuous
    · exact hu_supp.mul_right
  -- IBP on (u, gReg): both globally Differentiable.
  have h_ibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (𝕜 := ℝ) (f := u) (g := gReg)
    (v := EuclideanSpace.single i (1 : ℝ)) (μ := volume)
    h_int_du_gReg h_int_u_dgReg h_int_u_gReg
    (fun x _ => (hu_smooth.differentiable
      (by exact_mod_cast ENat.top_ne_zero)).differentiableAt)
    (fun x _ => (hgReg_smooth.differentiable
      (by exact_mod_cast ENat.top_ne_zero)).differentiableAt)
  -- Swap gReg → hardyField · i on each side via support agreement.
  have h_lhs : (∫ x, u x * fderiv ℝ gReg x (EuclideanSpace.single i (1:ℝ)) ∂volume) =
      (∫ x, u x * fderiv ℝ (fun y => hardyField y i) x
        (EuclideanSpace.single i (1:ℝ)) ∂volume) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport u
    · simp [h_fgReg_eq_at x hx]
    · have : u x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this]
  have h_rhs : (∫ x, fderiv ℝ u x (EuclideanSpace.single i (1:ℝ)) * gReg x ∂volume) =
      (∫ x, fderiv ℝ u x (EuclideanSpace.single i (1:ℝ)) * hardyField x i ∂volume) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport u
    · simp [h_gReg_eq_at x hx]
    · have : fderiv ℝ u x = 0 :=
        fderiv_of_notMem_tsupport ℝ hx
      simp [this]
  rw [h_lhs] at h_ibp
  rw [h_rhs] at h_ibp
  exact h_ibp


private lemma ibp_summed_hardyField
    {u : R3 → ℝ} (hu_smooth : ContDiff ℝ ∞ u) (hu_supp : HasCompactSupport u)
    (r : ℝ) (hr_pos : 0 < r) (hu_zero : ∀ x, ‖x‖ < r → u x = 0) :
    (∑ i : Fin 3, ∫ x, fderiv ℝ u x (EuclideanSpace.single i (1:ℝ)) * hardyField x i ∂volume)
      = - ∫ x, u x * inverseRSq x ∂volume := by
  haveI : (volume : Measure R3).IsAddHaarMeasure := by
    infer_instance
  -- tsupport bound from vanishing near 0
  have h_tsupp : tsupport u ⊆ {x : R3 | r ≤ ‖x‖} := by
    refine closure_minimal ?_ (isClosed_le continuous_const continuous_norm)
    intro y hy
    exact not_lt.mp fun h_lt => hy (hu_zero y h_lt)
  -- Step 1: Flip per-direction IBP for each i.
  have h_flip : ∀ i : Fin 3,
      ∫ x, fderiv ℝ u x (EuclideanSpace.single i (1:ℝ)) * hardyField x i ∂volume
        = - ∫ x, u x * fderiv ℝ (fun y => hardyField y i) x
            (EuclideanSpace.single i (1:ℝ)) ∂volume := by
    intro i
    have := ibp_direction_hardyField hu_smooth hu_supp r hr_pos hu_zero i
    linarith
  -- Step 2: Sum, factor out the negation.
  rw [Finset.sum_congr rfl (fun i _ => h_flip i), Finset.sum_neg_distrib]
  congr 1
  -- Goal: ∑ i, ∫ x, u·∂_i(hardyField·i) = ∫ x, u·inverseRSq
  rw [← integral_finsetSum _ (fun i _ =>
    integrable_u_mul_fderiv_hardyField hu_smooth.continuous hu_supp r hr_pos hu_zero i)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [← Finset.mul_sum, mul_eq_mul_left_iff]
  -- Goal: u x * (∑ i, fderiv (hardyField · i) x e_i) = u x * inverseRSq x
  by_cases hx_u : u x = 0
  · simp [hx_u]
  -- u x ≠ 0 ⟹ x ∈ tsupport u ⟹ r ≤ ‖x‖ ⟹ x ≠ 0
  have hx_in_supp : x ∈ Function.support u := hx_u
  have hx_norm : r ≤ ‖x‖ := h_tsupp (subset_tsupport _ hx_in_supp)
  have hx_ne : x ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hx_norm; linarith
  -- Goal: ∑ i, fderiv (hardyField · i) x e_i = inverseRSq x
  rw [show inverseRSq x = (‖x‖ ^ 2)⁻¹ by
    unfold inverseRSq
    rw [if_neg (norm_ne_zero_iff.mpr hx_ne), one_div]]
  -- Chain rule + hardyField_div
  have h_diff_hardy : DifferentiableAt ℝ hardyField x :=
    (hardyField_contDiffOn.differentiableOn (by simp)).differentiableAt
      (isOpen_compl_singleton.mem_nhds (by simpa using hx_ne))
  have h_chain : ∀ i : Fin 3,
      fderiv ℝ (fun y => hardyField y i) x (EuclideanSpace.single i (1:ℝ))
        = (fderiv ℝ hardyField x (EuclideanSpace.single i (1:ℝ))) i := by
    intro i
    have h_eq : (fun y : R3 => hardyField y i) = (EuclideanSpace.proj i) ∘ hardyField := rfl
    rw [h_eq, fderiv_comp x (EuclideanSpace.proj i).differentiableAt h_diff_hardy]
    simp only [ContinuousLinearMap.fderiv, coe_comp', Function.comp_apply, PiLp.proj_apply]
  simp_rw [h_chain]
  simp_all only [Function.mem_support, ne_eq, not_false_eq_true, or_false]
  exact hardyField_div x hx_ne

private lemma ibp_v_squared_hardyField
    {v : R3 → ℝ} (hv_smooth : ContDiff ℝ ∞ v) (hv_supp : HasCompactSupport v)
    (r : ℝ) (hr_pos : 0 < r) (hv_zero : ∀ x, ‖x‖ < r → v x = 0) :
    (∫ x, v x ^ 2 * inverseRSq x ∂volume)
      = - 2 * ∑ i : Fin 3,
          ∫ x, v x * fderiv ℝ v x (EuclideanSpace.single i (1:ℝ)) * hardyField x i ∂volume := by
  haveI : (volume : Measure R3).IsAddHaarMeasure := by
    infer_instance
  -- u = v²: smooth, compactly supported, vanishes near 0.
  have hu_smooth : ContDiff ℝ ∞ (fun x => v x ^ 2) := hv_smooth.pow 2
  have hu_supp : HasCompactSupport (fun x => v x ^ 2) := by
    have h_eq : (fun x => v x ^ 2) = v * v := by funext x; norm_num; ring
    rw [h_eq]; exact hv_supp.mul_right
  have hu_zero : ∀ x, ‖x‖ < r → (fun x => v x ^ 2) x = 0 := fun x hx => by
    change v x ^ 2 = 0; rw [hv_zero x hx]; ring
  -- Apply summed IBP to v².
  have h_ibp := ibp_summed_hardyField hu_smooth hu_supp r hr_pos hu_zero
  -- Chain rule per direction: fderiv (v²) x e_i = 2·v(x)·fderiv v x e_i.
  have h_v_diff : Differentiable ℝ v :=
    hv_smooth.differentiable (by exact_mod_cast ENat.top_ne_zero)
  have h_per : ∀ i : Fin 3,
      ∫ x, fderiv ℝ (fun y => v y ^ 2) x (EuclideanSpace.single i (1:ℝ)) * hardyField x i ∂volume
        = 2 * ∫ x, v x * fderiv ℝ v x (EuclideanSpace.single i (1:ℝ)) * hardyField x i ∂volume := by
    intro i
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have h_chain : fderiv ℝ (fun y => v y ^ 2) x (EuclideanSpace.single i (1:ℝ))
        = 2 * v x * fderiv ℝ v x (EuclideanSpace.single i (1:ℝ)) := by
      erw [fderiv_pow 2 (h_v_diff x)]
      simp [ContinuousLinearMap.smul_apply, pow_one, smul_eq_mul, nsmul_eq_mul]
    simp [h_chain]; ring
  -- Combine: sum, factor 2, conclude.
  rw [Finset.sum_congr rfl (fun i _ => h_per i), ← Finset.mul_sum] at h_ibp
  -- h_ibp : 2 * ∑ ... = -∫ x, v x^2 * inverseRSq x
  linarith

/-- If `A ≤ 2·√A·√B` with `A, B ≥ 0`, then `A ≤ 4·B`. The algebraic kernel of
    the Hardy inequality once IBP and Cauchy-Schwarz are in hand. -/
private lemma hardy_algebraic {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : A ≤ 2 * Real.sqrt A * Real.sqrt B) :
    A ≤ 4 * B := by
  by_cases hA0 : A = 0
  · rw [hA0]; linarith
  have _hA_pos : 0 < A := hA.lt_of_ne (Ne.symm hA0)
  nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB,
             Real.sqrt_nonneg A, Real.sqrt_nonneg B,
             mul_self_nonneg (Real.sqrt A - 2 * Real.sqrt B)]

/-- Pointwise Cauchy–Schwarz on the integrand `v(x) · (∇v · hardyField)(x)`. Holds
    for every `x`: at `x = 0` both sides vanish via `hardyField 0 = 0` and
    `inverseRSq 0 = 0`; otherwise `Real.sum_mul_le_sqrt_mul_sqrt` plus the identity
    `∑ i, (hardyField x i)² = (‖x‖²)⁻¹` (which equals `inverseRSq x` for `x ≠ 0`)
    deliver the bound. No regularity assumption on `v`. -/
private lemma cs_pointwise_v_grad_hardy (v : R3 → ℝ) (x : R3) :
    |v x * ∑ i : Fin 3, fderiv ℝ v x (EuclideanSpace.single i (1:ℝ)) * hardyField x i|
      ≤ Real.sqrt (v x ^ 2 * inverseRSq x)
        * Real.sqrt (∑ i : Fin 3,
            (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2) := by
  by_cases hx : x = 0
  · -- x = 0: every `hardyField` component is 0, so LHS = 0; RHS ≥ 0.
    have h_hf : ∀ i : Fin 3, hardyField x i = 0 := fun i => by simp [hardyField, hx]
    simp only [h_hf, mul_zero, Finset.sum_const_zero, abs_zero]
    positivity
  -- x ≠ 0
  have h_ne : (‖x‖ ^ 2 : ℝ) ≠ 0 := by positivity
  -- Cauchy–Schwarz on Fin 3 wrapped in absolute values.
  have h_cs :
      |∑ i : Fin 3, fderiv ℝ v x (EuclideanSpace.single i (1:ℝ)) * hardyField x i|
        ≤ Real.sqrt (∑ i, (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2)
          * Real.sqrt (∑ i, (hardyField x i) ^ 2) := by
    calc |∑ i : Fin 3,
              fderiv ℝ v x (EuclideanSpace.single i (1:ℝ)) * hardyField x i|
        ≤ ∑ i, |fderiv ℝ v x (EuclideanSpace.single i (1:ℝ)) * hardyField x i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))| * |hardyField x i| := by
          simp_rw [abs_mul]
      _ ≤ Real.sqrt (∑ i, |fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))| ^ 2)
            * Real.sqrt (∑ i, |hardyField x i| ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = Real.sqrt (∑ i, (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2)
            * Real.sqrt (∑ i, (hardyField x i) ^ 2) := by simp_rw [sq_abs]
  -- ∑_i (hardyField x i)² = (‖x‖²)⁻¹.  Use hardyField x i = (‖x‖²)⁻¹ · x i
  -- and ‖x‖² = ∑_i (x i)².
  have h_g_sumsq : ∑ i : Fin 3, (hardyField x i) ^ 2 = (‖x‖ ^ 2)⁻¹ := by
    have h_unfold : ∀ i : Fin 3, hardyField x i = (‖x‖ ^ 2)⁻¹ * x i := fun i => by
      simp [hardyField, hx]
    calc ∑ i : Fin 3, (hardyField x i) ^ 2
        = ∑ i, ((‖x‖^2)⁻¹ * x i)^2 := by simp_rw [h_unfold]
      _ = ((‖x‖^2)⁻¹)^2 * ∑ i, (x i)^2 := by
          simp_rw [mul_pow]; rw [← Finset.mul_sum]
      _ = ((‖x‖^2)⁻¹)^2 * ‖x‖^2 := by
          rw [@PiLp.norm_sq_eq_of_L2]
          simp only [Real.norm_eq_abs, sq_abs]
      _ = (‖x‖^2)⁻¹ := by
          rw [show ((‖x‖^2)⁻¹ : ℝ)^2 * ‖x‖^2
                = (‖x‖^2)⁻¹ * ((‖x‖^2)⁻¹ * ‖x‖^2) from by ring,
              inv_mul_cancel₀ h_ne, mul_one]
  -- inverseRSq x = (‖x‖²)⁻¹ for x ≠ 0
  have h_inv : inverseRSq x = (‖x‖ ^ 2)⁻¹ := by
    unfold inverseRSq
    rw [if_neg (norm_ne_zero_iff.mpr hx), one_div]
  -- Combine: |v x · ∑| = |v x| · |∑| ≤ |v x| · √(∑(∂_iv)²) · √(∑(hardyField)²),
  -- and the last sqrt equals √((‖x‖²)⁻¹) = √(inverseRSq), so absorb |v x| inside.
  rw [abs_mul]
  calc |v x| * |∑ i, fderiv ℝ v x (EuclideanSpace.single i (1:ℝ)) * hardyField x i|
      ≤ |v x| * (Real.sqrt (∑ i, (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2)
          * Real.sqrt (∑ i, (hardyField x i) ^ 2)) :=
        mul_le_mul_of_nonneg_left h_cs (abs_nonneg _)
    _ = Real.sqrt (v x ^ 2 * inverseRSq x)
        * Real.sqrt (∑ i, (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2) := by
        rw [h_g_sumsq, h_inv,
            show |v x| = Real.sqrt (v x ^ 2) from (Real.sqrt_sq_eq_abs _).symm,
            Real.sqrt_mul (sq_nonneg _)]
        ring

/-- Integral Cauchy–Schwarz for the Hardy integrand.  Bounds the summed integral
    `∑ᵢ ∫ v · ∂ᵢv · hardyFieldᵢ` (in absolute value) by `√A · √B`, where
    `A = ∫ v²·inverseRSq` and `B = ∫ ∑ᵢ (∂ᵢv)²`.

    Strategy: interchange sum and integral, bound by `∫ |·|` (triangle inequality
    for integrals), apply the pointwise CS lemma, then close with the integral
    Hölder inequality at the conjugate pair `(2,2)`.

    The two `MemLp _ 2` hypotheses are the L² memberships of the factors; they are
    discharged at the assembly site (continuity + compact support for the gradient
    factor, the singular-but-integrable estimate for the `inverseRSq` factor). -/
private lemma cs_bound_v_grad_hardy
    {v : R3 → ℝ}
    (hA_memLp : MemLp (fun x => Real.sqrt (v x ^ 2 * inverseRSq x)) 2 volume)
    (hB_memLp : MemLp (fun x => Real.sqrt
        (∑ i : Fin 3, (fderiv ℝ v x (EuclideanSpace.single i (1 : ℝ))) ^ 2)) 2 volume)
    (h_int_summand : ∀ i : Fin 3, Integrable (fun x =>
        v x * (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ)) * hardyField x i)) volume) :
    |∑ i : Fin 3, ∫ x,
        v x * (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ)) * hardyField x i) ∂volume|
      ≤ Real.sqrt (∫ x, v x ^ 2 * inverseRSq x ∂volume)
        * Real.sqrt (∫ x, ∑ i : Fin 3,
            (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2 ∂volume) := by
  -- Abbreviations for the two nonneg factors.
  set F := fun x => Real.sqrt (v x ^ 2 * inverseRSq x) with hF_def
  set G := fun x => Real.sqrt
      (∑ i : Fin 3, (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2) with hG_def
      -- the full product is the finite sum of the per-direction summands
  have h_int_prod : Integrable (fun x =>
      v x * ∑ i : Fin 3,
        fderiv ℝ v x (EuclideanSpace.single i (1:ℝ)) * hardyField x i) volume := by
    have h := integrable_finsetSum Finset.univ (fun i _ => h_int_summand i)
    exact h.congr (Filter.Eventually.of_forall fun x => by simp [Finset.mul_sum])
  -- STEP 1: pull the finite sum inside the integral.
  have h_sum_swap :
      ∑ i : Fin 3, ∫ x,
          v x * (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ)) * hardyField x i) ∂volume
        = ∫ x, v x * ∑ i : Fin 3,
            fderiv ℝ v x (EuclideanSpace.single i (1:ℝ)) * hardyField x i ∂volume := by
    rw [← integral_finsetSum]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [Finset.mul_sum]
    · intro i _
      exact h_int_summand i
      -- if this fails, see note (1) below — replace with the direct per-term lemma
  rw [h_sum_swap]
  -- STEP 2: |∫ φ| ≤ ∫ |φ| ≤ ∫ F·G  (triangle inequality, then pointwise CS).
  have h_abs_le :
      |∫ x, v x * ∑ i : Fin 3,
          fderiv ℝ v x (EuclideanSpace.single i (1:ℝ)) * hardyField x i ∂volume|
        ≤ ∫ x, F x * G x ∂volume := by
    calc |∫ x, v x * ∑ i : Fin 3,
              fderiv ℝ v x (EuclideanSpace.single i (1:ℝ)) * hardyField x i ∂volume|
        ≤ ∫ x, |v x * ∑ i : Fin 3,
              fderiv ℝ v x (EuclideanSpace.single i (1:ℝ)) * hardyField x i| ∂volume := by
          rw [← Real.norm_eq_abs]
          exact
            norm_integral_le_integral_norm fun a =>
              v a * ∑ i, (fderiv ℝ v a) (EuclideanSpace.single i 1) * (hardyField a).ofLp i
      _ ≤ ∫ x, F x * G x ∂volume := by
          refine integral_mono ?_ ?_ (fun x => cs_pointwise_v_grad_hardy v x)
          · exact h_int_prod.abs
          · -- F·G integrable: product of two L² functions
            exact (hA_memLp.integrable_mul hB_memLp)
  refine h_abs_le.trans ?_
  -- STEP 3: integral Hölder at (2,2): ∫ F·G ≤ (∫F²)^(1/2)·(∫G²)^(1/2).
  have h_holder :
      ∫ x, F x * G x ∂volume
        ≤ (∫ x, F x ^ (2:ℝ) ∂volume) ^ (1 / (2:ℝ))
          * (∫ x, G x ^ (2:ℝ) ∂volume) ^ (1 / (2:ℝ)) :=
    integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _)
      (Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _)
      (by simpa using hA_memLp) (by simpa using hB_memLp)
  refine h_holder.trans_eq ?_
  -- STEP 4: rewrite (∫ F²)^(1/2) = √(∫ v²·inverseRSq), likewise for G.
  have hF_sq : ∀ x, F x ^ (2:ℝ) = v x ^ 2 * inverseRSq x := fun x => by
    rw [hF_def]
    rw [Real.rpow_two, Real.sq_sqrt]
    unfold inverseRSq
    positivity
  have hG_sq : ∀ x, G x ^ (2:ℝ)
      = ∑ i : Fin 3, (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2 := fun x => by
    rw [hG_def, Real.rpow_two, Real.sq_sqrt]
    positivity
  rw [Real.sqrt_eq_rpow (∫ x, v x ^ 2 * inverseRSq x ∂volume),
      Real.sqrt_eq_rpow (∫ x, ∑ i : Fin 3,
        (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2 ∂volume)]
  congr 1
  · congr 1; exact integral_congr_ae (Filter.Eventually.of_forall hF_sq)
  · congr 1; exact integral_congr_ae (Filter.Eventually.of_forall hG_sq)

/-! ### Integrability prerequisites for the Cauchy–Schwarz bound

For `v` smooth, compactly supported, vanishing on `B(0, r)`, the two factors of the
Hardy integrand lie in `L²`. These discharge the `MemLp` hypotheses of
`cs_bound_v_grad_hardy`. -/

/-- `inverseRSq` is continuous on `ℝ³ \ {0}`: there it equals `1/‖x‖²` with
    `‖x‖² ≠ 0`. -/
private lemma inverseRSq_continuousOn :
    ContinuousOn inverseRSq ({0}ᶜ : Set R3) := by
  have h_eq : Set.EqOn inverseRSq (fun x => 1 / ‖x‖ ^ 2) ({0}ᶜ : Set R3) := by
    intro x hx
    have hx_ne : x ≠ 0 := by simpa using hx
    unfold inverseRSq
    rw [if_neg (norm_ne_zero_iff.mpr hx_ne)]
  refine ContinuousOn.congr ?_ h_eq
  refine ContinuousOn.div continuousOn_const ((continuous_norm.pow 2).continuousOn) ?_
  intro x hx
  have hx_ne : x ≠ 0 := by simpa using hx
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hx_ne)

/-- The gradient factor `√(∑ᵢ (∂ᵢv)²)` is in `L²`: its square is continuous with
    compact support (supported within `tsupport v`), hence the root is continuous-cs,
    hence in `L²`. -/
private lemma memLp_sqrt_sum_sq_fderiv
    {v : R3 → ℝ} (hv_smooth : ContDiff ℝ ∞ v) (hv_supp : HasCompactSupport v) :
    MemLp (fun x => Real.sqrt
        (∑ i : Fin 3, (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2)) 2 volume := by
  haveI : (volume : Measure R3).IsAddHaarMeasure := by
    infer_instance
  set S := fun x => ∑ i : Fin 3,
      (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2 with hS_def
  have h_cont : Continuous S := by
    refine continuous_finsetSum _ (fun i _ => ?_)
    exact ((hv_smooth.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2
  have h_supp : HasCompactSupport S := by
    refine HasCompactSupport.mono' hv_supp ?_
    intro x hx
    -- hx : x ∈ support S;  goal : x ∈ tsupport v
    by_contra hx_supp
    -- hx_supp : x ∉ tsupport v
    have h0 : fderiv ℝ v x = 0 := fderiv_of_notMem_tsupport ℝ hx_supp
    rw [Function.mem_support] at hx
    apply hx
    simp only [hS_def, h0, ContinuousLinearMap.zero_apply]
    simp
  have h_sqrt_cont : Continuous (fun x => Real.sqrt (S x)) :=
    Real.continuous_sqrt.comp h_cont
  have h_sqrt_supp : HasCompactSupport (fun x => Real.sqrt (S x)) :=
    h_supp.comp_left (g := Real.sqrt) Real.sqrt_zero
  exact h_sqrt_cont.memLp_of_hasCompactSupport h_sqrt_supp

/-- The singular factor `√(v²·inverseRSq)` is in `L²`: its square `v²·inverseRSq`
    is integrable via `integrable_mul_singular` (`u = v²` continuous-cs vanishing on
    `B(0,r)`, `g = inverseRSq` continuous on `{0}ᶜ`), then `memLp_two_iff_integrable_sq`. -/
private lemma memLp_sqrt_vsq_inverseRSq
    {v : R3 → ℝ} (hv_smooth : ContDiff ℝ ∞ v) (hv_supp : HasCompactSupport v)
    (r : ℝ) (hr_pos : 0 < r) (hv_zero : ∀ x, ‖x‖ < r → v x = 0) :
    MemLp (fun x => Real.sqrt (v x ^ 2 * inverseRSq x)) 2 volume := by
  have h_int : Integrable (fun x => v x ^ 2 * inverseRSq x) volume := by
    refine integrable_mul_singular
      (u := fun x => v x ^ 2) (g := inverseRSq)
      (hv_smooth.continuous.pow 2) (hv_supp.comp_left (g := (· ^ 2)) (by simp))
      r hr_pos ?_ inverseRSq_continuousOn
    · intro x hx; simp [hv_zero x hx]
  have h_meas : AEStronglyMeasurable
      (fun x => Real.sqrt (v x ^ 2 * inverseRSq x)) volume :=
    Real.continuous_sqrt.comp_aestronglyMeasurable h_int.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq h_meas]
  refine h_int.congr (Filter.Eventually.of_forall fun x => ?_)
  unfold inverseRSq; norm_num
  rw [Real.sq_sqrt]
  positivity

/-- **Hardy's inequality for real, smooth functions vanishing near the origin.**

    For `v ∈ C_c^∞(ℝ³, ℝ)` that vanishes on some ball `B(0, r)`:
      ∫ v(x)²/|x|² dx ≤ 4 ∫ ∑ᵢ (∂ᵢv(x))² dx

    This is the analytic core of Hardy's inequality. The "vanishing near the
    origin" hypothesis is what lets the integration-by-parts identity
    `ibp_v_squared_hardyField` run with no boundary term (the Hardy field is
    smooth away from `0`). The full smooth case removes this hypothesis via an
    `ε → 0` cutoff limit, and the `ℂ`-valued case follows by splitting into real
    and imaginary parts — both deferred to follow-up work.

    **Assembly:**
    - `ibp_v_squared_hardyField`: `A = −2·∑ᵢ ∫ v·∂ᵢv·gᵢ` where `A = ∫ v²·inverseRSq`.
    - `cs_bound_v_grad_hardy`: `|∑ᵢ ∫ v·∂ᵢv·gᵢ| ≤ √A·√B` where `B = ∫ ∑ᵢ (∂ᵢv)²`,
      discharged by the two `MemLp` lemmas and `h_int_summand`.
    - Hence `A = −2·S ≤ 2|S| ≤ 2·√A·√B`, and `hardy_algebraic` gives `A ≤ 4·B`. -/
theorem hardy_inequality_smooth_of_vanishing
    {v : R3 → ℝ} (hv_smooth : ContDiff ℝ ∞ v) (hv_supp : HasCompactSupport v)
    (r : ℝ) (hr_pos : 0 < r) (hv_zero : ∀ x, ‖x‖ < r → v x = 0) :
    ∫ x, v x ^ 2 * inverseRSq x ≤
      4 * ∫ x, ∑ i : Fin 3, (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2 := by
  -- Both integrals are nonnegative (their integrands are).
  have hA_nonneg : 0 ≤ ∫ x, v x ^ 2 * inverseRSq x ∂volume :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (inverseRSq_nonneg x))
  have hB_nonneg : 0 ≤ ∫ x, ∑ i : Fin 3,
      (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2 ∂volume :=
    integral_nonneg (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  -- The Cauchy–Schwarz summand `v·(∂ᵢv·gᵢ)` is integrable: `v·∂ᵢv` is continuous,
  -- compactly supported, vanishing near `0`, and `gᵢ` is continuous off `0`.
  have h_int_summand : ∀ i : Fin 3, Integrable (fun x =>
      v x * (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ)) * hardyField x i)) volume := by
    intro i
    have hcont : Continuous (fun x => v x * fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) :=
      hv_smooth.continuous.mul
        ((hv_smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
    have hsupp : HasCompactSupport
        (fun x => v x * fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) := hv_supp.mul_right
    have hzero : ∀ x, ‖x‖ < r →
        v x * fderiv ℝ v x (EuclideanSpace.single i (1:ℝ)) = 0 := by
      intro x hx; rw [hv_zero x hx, zero_mul]
    have h := integrable_mul_singular hcont hsupp r hr_pos hzero
      (g := fun x => hardyField x i) (hardyField_apply_contDiffOn i).continuousOn
    exact h.congr (Filter.Eventually.of_forall fun x => by ring)
  -- IBP identity, with the summand associativity normalised to `cs_bound`'s form.
  have h_ibp := ibp_v_squared_hardyField hv_smooth hv_supp r hr_pos hv_zero
  have hSeq : (∑ i : Fin 3, ∫ x,
        v x * fderiv ℝ v x (EuclideanSpace.single i (1:ℝ)) * hardyField x i ∂volume)
      = ∑ i : Fin 3, ∫ x,
        v x * (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ)) * hardyField x i) ∂volume := by
    refine Finset.sum_congr rfl (fun i _ =>
      integral_congr_ae (Filter.Eventually.of_forall fun x => ?_))
    ring
  rw [hSeq] at h_ibp
  -- Integral Cauchy–Schwarz on the IBP right-hand side.
  have h_cs := cs_bound_v_grad_hardy
    (memLp_sqrt_vsq_inverseRSq hv_smooth hv_supp r hr_pos hv_zero)
    (memLp_sqrt_sum_sq_fderiv hv_smooth hv_supp) h_int_summand
  -- Absorb: `A = −2·S`, `−S ≤ |S| ≤ √A·√B`, so `A ≤ 2·√A·√B`; then `hardy_algebraic`.
  refine hardy_algebraic hA_nonneg hB_nonneg ?_
  rw [mul_assoc]
  have hNegS := neg_le_abs (∑ i : Fin 3, ∫ x,
      v x * (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ)) * hardyField x i) ∂volume)
  linarith [h_cs, hNegS, h_ibp]


end Spectra.QuantumMechanics.Hydrogen
