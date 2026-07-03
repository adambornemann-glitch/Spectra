/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Sobolev.WeakDerivative
import Spectra.Spaces.Sobolev.IntegrationByParts
import Spectra.Spaces.Sobolev.DensityResults
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
/-!
# The Hardy Inequality in Three Dimensions

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

## Proof strategy

**Step 1 (Smooth functions):** Prove Hardy for ψ ∈ C_c^∞(ℝ³).
The proof uses integration by parts in spherical coordinates:

  ∫ |ψ|²/r² dx = −2 Re ∫ (ψ̄/r)(r̂ · ∇ψ) dx
                ≤ 2 (∫ |ψ|²/r²)^{1/2} (∫ |∇ψ|²)^{1/2}

Dividing both sides by (∫ |ψ|²/r²)^{1/2} gives the result.

The integration by parts identity comes from:
  div(r̂/r) = (d−2)/r²    in d dimensions (= 1/r² for d = 3)

and the divergence theorem on ℝ³ \ B(0,ε), then ε → 0.

**Step 2 (Density extension):** Extend from C_c^∞ to H¹ via
`smooth_compactly_supported_dense_H1` from Spaces/Sobolev/.
The ∫|ψ|²/|x|² functional is lower semicontinuous with respect to
H¹ convergence, so the bound passes to the closure.

## Main statements

* `hardy_inequality_smooth` — Hardy for smooth compactly supported functions.
* `hardy_inequality` — Hardy for all ψ ∈ H¹(ℝ³).
* `hardy_constant_sharp` — The constant 4 is optimal.
* `inverse_r_sq_integrable` — ∫|ψ|²/|x|² < ∞ for ψ ∈ H¹.

## Proof strategy

Each statement below is fully proved, by the following routes:
- `hardy_inequality_smooth`: IBP in spherical coordinates + Cauchy-Schwarz.
- `hardy_inequality`: density of C_c^∞ in H¹ + lower semicontinuity.
- `hardy_constant_sharp`: explicit optimising sequence ψ_n(r) = r^{−1/2+ε} χ(r).
- Inverse-r estimates: from Hardy + Cauchy inequality with ε.

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
  have hxsq_ne : ‖x‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
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
noncomputable def hardyIntegral (ψ : L2_R3) : ℝ :=
  ∫ x, inverseRSq x * ‖(ψ : R3 → ℂ) x‖ ^ 2

/-- The Hardy integral is non-negative. -/
lemma hardyIntegral_nonneg (ψ : L2_R3) : 0 ≤ hardyIntegral ψ := by
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
    show gReg y = hardyField y i
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
      (∫ x, u x * fderiv ℝ (fun y => hardyField y i) x (EuclideanSpace.single i (1:ℝ)) ∂volume) := by
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
  simp [← Finset.mul_sum]
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
    show v x ^ 2 = 0; rw [hv_zero x hx]; ring
  -- Apply summed IBP to v².
  have h_ibp := ibp_summed_hardyField hu_smooth hu_supp r hr_pos hu_zero
  -- Chain rule per direction: fderiv (v²) x e_i = 2·v(x)·fderiv v x e_i.
  have h_v_diff : Differentiable ℝ v := hv_smooth.differentiable (by exact_mod_cast ENat.top_ne_zero)
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
  have hA_pos : 0 < A := hA.lt_of_ne (Ne.symm hA0)
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
        (∑ i : Fin 3, (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2)) 2 volume)
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

/-! ### Removing the vanishing-near-origin hypothesis

To upgrade `hardy_inequality_smooth_of_vanishing` to general smooth compactly
supported functions, we multiply by a smooth **inner** cutoff `χ_ε` that vanishes
on `B(0, ε)` and equals `1` outside `B(0, 2ε)`, apply the vanishing case to
`v · χ_ε`, and let `ε → 0`. The key quantitative input is a gradient bound
`‖∇χ_ε‖ ≤ M/ε` with `M` independent of `ε`, exactly as for the outer cutoff in
`MeyersSerrin`. -/

/-- A scaled family of smooth **inner** cutoffs. There is a constant `M ≥ 0` such
    that for every `ε > 0` there is `χ : ℝ³ → ℝ` with: `χ` smooth; `χ = 0` on the
    closed ball `B(0, ε)`; `χ = 1` outside `B(0, 2ε)`; `0 ≤ χ ≤ 1`; the gradient
    bound `‖∇χ‖ ≤ M/ε`; and `∇χ = 0` outside `B(0, 2ε)`.

    Built from the unit `ContDiffBump` `ρ` (`= 1` on `B(0,1)`, `= 0` off `B(0,2)`)
    as `χ(x) = 1 − ρ(ε⁻¹ • x)`; the gradient bound comes from the scaling chain
    rule, `‖∇χ_ε(x)‖ = ε⁻¹‖∇ρ(ε⁻¹x)‖ ≤ M/ε`. -/
private lemma exists_hardy_cutoff :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ε : ℝ), 0 < ε →
      ∃ (χ : R3 → ℝ),
        ContDiff ℝ ∞ χ ∧
        (∀ x, ‖x‖ ≤ ε → χ x = 0) ∧
        (∀ x, 2 * ε ≤ ‖x‖ → χ x = 1) ∧
        (∀ x, χ x ∈ Set.Icc (0:ℝ) 1) ∧
        (∀ x, ‖fderiv ℝ χ x‖ ≤ M / ε) ∧
        (∀ x, 2 * ε < ‖x‖ → fderiv ℝ χ x = 0) := by
  -- Fixed unit-scale bump: `= 1` on `B(0,1)`, `= 0` off `B(0,2)`.
  let ρ : ContDiffBump (0 : R3) := ⟨1, 2, one_pos, by norm_num⟩
  have hρ_smooth : ContDiff ℝ ∞ (ρ : R3 → ℝ) := ρ.contDiff
  -- Its derivative is continuous with compact support, hence bounded.
  have hρ_d_cont : Continuous (fderiv ℝ (ρ : R3 → ℝ)) :=
    (contDiff_infty_iff_fderiv.mp hρ_smooth).2.continuous
  have hρ_d_supp : HasCompactSupport (fderiv ℝ (ρ : R3 → ℝ)) := ρ.hasCompactSupport.fderiv ℝ
  obtain ⟨M₀, hM₀⟩ := hρ_d_cont.bounded_above_of_compact_support hρ_d_supp
  refine ⟨max M₀ 0, le_max_right _ _, fun ε hε => ?_⟩
  -- HasFDerivAt of the scaling map and of `ρ ∘ scale`, available everywhere.
  have h_scale_hfd : ∀ x : R3, HasFDerivAt (fun y : R3 => ε⁻¹ • y)
      (ε⁻¹ • ContinuousLinearMap.id ℝ R3) x :=
    fun x => (ε⁻¹ • ContinuousLinearMap.id ℝ R3).hasFDerivAt
  have hρ_diff : ∀ x : R3, DifferentiableAt ℝ (ρ : R3 → ℝ) (ε⁻¹ • x) :=
    fun x => (hρ_smooth.differentiable (by exact_mod_cast ENat.top_ne_zero)).differentiableAt
  have h_comp_hfd : ∀ x : R3, HasFDerivAt (fun y : R3 => (ρ : R3 → ℝ) (ε⁻¹ • y))
      ((fderiv ℝ (ρ : R3 → ℝ) (ε⁻¹ • x)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ R3)) x :=
    fun x => (hρ_diff x).hasFDerivAt.comp x (h_scale_hfd x)
  have h_χ_hfd : ∀ x : R3, HasFDerivAt (fun y : R3 => 1 - (ρ : R3 → ℝ) (ε⁻¹ • y))
      (-((fderiv ℝ (ρ : R3 → ℝ) (ε⁻¹ • x)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ R3))) x :=
    fun x => (h_comp_hfd x).const_sub 1
  refine ⟨fun x => 1 - (ρ : R3 → ℝ) (ε⁻¹ • x), ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 1. Smooth.
  · exact contDiff_const.sub
      (hρ_smooth.comp (ε⁻¹ • ContinuousLinearMap.id ℝ R3).contDiff)
  -- 2. χ = 0 on closedBall ε.
  · intro x hx
    show 1 - (ρ : R3 → ℝ) (ε⁻¹ • x) = 0
    have : (ρ : R3 → ℝ) (ε⁻¹ • x) = 1 := by
      apply ρ.one_of_mem_closedBall
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv,
        Real.norm_eq_abs, abs_of_pos hε]
      show ε⁻¹ * ‖x‖ ≤ 1
      have hc : ε⁻¹ * ε = 1 := inv_mul_cancel₀ hε.ne'
      have h2 := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hε.le)
      linarith
    rw [this]; ring
  -- 3. χ = 1 off ball (2ε).
  · intro x hx
    show 1 - (ρ : R3 → ℝ) (ε⁻¹ • x) = 1
    have : (ρ : R3 → ℝ) (ε⁻¹ • x) = 0 := by
      apply ρ.zero_of_le_dist
      rw [dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hε]
      show (2 : ℝ) ≤ ε⁻¹ * ‖x‖
      have hc : ε⁻¹ * (2 * ε) = 2 := by
        rw [mul_comm 2 ε, ← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
      have h2 := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hε.le)
      linarith
    rw [this]; ring
  -- 4. χ ∈ [0,1].
  · intro x
    refine ⟨?_, ?_⟩
    · have h : (ρ : R3 → ℝ) (ε⁻¹ • x) ≤ 1 := ρ.le_one
      linarith
    · have h : 0 ≤ (ρ : R3 → ℝ) (ε⁻¹ • x) := ρ.nonneg' (ε⁻¹ • x)
      linarith
  -- 5. Gradient bound ‖∇χ‖ ≤ (max M₀ 0)/ε.
  · intro x
    rw [(h_χ_hfd x).fderiv, norm_neg]
    have h_op := ContinuousLinearMap.opNorm_comp_le
      (fderiv ℝ (ρ : R3 → ℝ) (ε⁻¹ • x)) (ε⁻¹ • ContinuousLinearMap.id ℝ R3)
    have h_σ : ‖ε⁻¹ • ContinuousLinearMap.id ℝ R3‖ = ε⁻¹ := by
      rw [norm_smul, ContinuousLinearMap.norm_id, norm_inv, Real.norm_eq_abs,
        abs_of_pos hε, mul_one]
    calc ‖(fderiv ℝ (ρ : R3 → ℝ) (ε⁻¹ • x)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ R3)‖
        ≤ ‖fderiv ℝ (ρ : R3 → ℝ) (ε⁻¹ • x)‖ * ‖ε⁻¹ • ContinuousLinearMap.id ℝ R3‖ := h_op
      _ = ‖fderiv ℝ (ρ : R3 → ℝ) (ε⁻¹ • x)‖ * ε⁻¹ := by rw [h_σ]
      _ ≤ max M₀ 0 * ε⁻¹ :=
          mul_le_mul_of_nonneg_right ((hM₀ (ε⁻¹ • x)).trans (le_max_left _ _))
            (inv_nonneg.mpr hε.le)
      _ = max M₀ 0 / ε := by rw [div_eq_mul_inv]
  -- 6. ∇χ = 0 off ball (2ε): there χ ≡ 1 locally.
  · intro x hx
    have hEq : (fun y : R3 => 1 - (ρ : R3 → ℝ) (ε⁻¹ • y)) =ᶠ[𝓝 x] (fun _ => (1:ℝ)) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
      show 1 - (ρ : R3 → ℝ) (ε⁻¹ • y) = 1
      have : (ρ : R3 → ℝ) (ε⁻¹ • y) = 0 := by
        apply ρ.zero_of_le_dist
        rw [dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hε]
        show (2 : ℝ) ≤ ε⁻¹ * ‖y‖
        have hc : ε⁻¹ * (2 * ε) = 2 := by
          rw [mul_comm 2 ε, ← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
        have h2 := mul_le_mul_of_nonneg_left (le_of_lt hy) (inv_nonneg.mpr hε.le)
        linarith
      rw [this]; ring
    rw [hEq.fderiv_eq]; simp

/-- For continuous, compactly supported real `v`, the Hardy integrand `v²·inverseRSq`
    is globally integrable: `v²` is bounded and supported in some ball `B(0, R)`, and
    `inverseRSq` is integrable on that ball (`inverseRSq_integrableOn_ball`). -/
private lemma vsq_inverseRSq_integrable
    {v : R3 → ℝ} (hv_cont : Continuous v) (hv_supp : HasCompactSupport v) :
    Integrable (fun x => v x ^ 2 * inverseRSq x) volume := by
  have hv2_cont : Continuous (fun x => v x ^ 2) := hv_cont.pow 2
  have hv2_supp : HasCompactSupport (fun x => v x ^ 2) :=
    hv_supp.comp_left (g := (· ^ 2)) (by simp)
  obtain ⟨M, hM⟩ := hv2_cont.bounded_above_of_compact_support hv2_supp
  have hM' : ∀ x, v x ^ 2 ≤ M := fun x =>
    (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hM x)
  -- tsupport of v² lies in some closed ball, hence in the open ball of radius R+1.
  obtain ⟨R, hR⟩ := hv2_supp.isCompact.isBounded.subset_closedBall (0 : R3)
  set R' := R + 1 with hR'_def
  have hsub : tsupport (fun x => v x ^ 2) ⊆ Metric.ball (0 : R3) R' := fun x hx => by
    have := hR hx
    rw [Metric.mem_closedBall, dist_zero_right] at this
    rw [Metric.mem_ball, dist_zero_right]; linarith
  -- Dominating function: `M` times `inverseRSq` restricted to `B(0, R')`.
  have hg_int : Integrable
      (fun x => M * (Metric.ball (0 : R3) R').indicator inverseRSq x) volume :=
    (((integrable_indicator_iff measurableSet_ball).mpr
      (inverseRSq_integrableOn_ball R')).const_mul M)
  refine Integrable.mono' hg_int
    (hv2_cont.measurable.mul inverseRSq_measurable).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Metric.ball (0 : R3) R'
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (inverseRSq_nonneg x)),
      Set.indicator_of_mem hx]
    exact mul_le_mul_of_nonneg_right (hM' x) (inverseRSq_nonneg x)
  · have hxt : x ∉ tsupport (fun x => v x ^ 2) := fun h => hx (hsub h)
    have hv0 : v x ^ 2 = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun x => v x ^ 2) hxt
    rw [hv0, zero_mul, Set.indicator_of_notMem hx, mul_zero, norm_zero]

/-- Young's inequality `(a+b)² ≤ (1+t)a² + (1+t⁻¹)b²` for `t > 0`. The slack is
    `t⁻¹·(t·a − b)² ≥ 0`. Used to split the gradient of `v·χ` into a `(1+t)`-multiple
    of `∇v` plus a vanishing cutoff-gradient error. -/
private lemma young_sq {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    (a + b) ^ 2 ≤ (1 + t) * a ^ 2 + (1 + t⁻¹) * b ^ 2 := by
  have hnn : 0 ≤ t⁻¹ * (t * a - b) ^ 2 := mul_nonneg (inv_nonneg.mpr ht.le) (sq_nonneg _)
  have hexp : t⁻¹ * (t * a - b) ^ 2 = (1 + t) * a ^ 2 + (1 + t⁻¹) * b ^ 2 - (a + b) ^ 2 := by
    field_simp
    ring
  linarith

/-- For `w` smooth with compact support, the squared-gradient `∑ᵢ (∂ᵢw)²` is
    integrable: it is continuous (derivatives of smooth functions are continuous)
    and supported within `tsupport w`. -/
private lemma sum_sq_fderiv_integrable
    {w : R3 → ℝ} (hw_smooth : ContDiff ℝ ∞ w) (hw_supp : HasCompactSupport w) :
    Integrable (fun x => ∑ i : Fin 3,
      (fderiv ℝ w x (EuclideanSpace.single i (1:ℝ))) ^ 2) volume := by
  haveI : IsFiniteMeasureOnCompacts (volume : Measure R3) := by
    infer_instance
  have h_cont : Continuous (fun x => ∑ i : Fin 3,
      (fderiv ℝ w x (EuclideanSpace.single i (1:ℝ))) ^ 2) := by
    refine continuous_finsetSum _ (fun i _ => ?_)
    exact ((hw_smooth.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2
  have h_supp : HasCompactSupport (fun x => ∑ i : Fin 3,
      (fderiv ℝ w x (EuclideanSpace.single i (1:ℝ))) ^ 2) := by
    refine HasCompactSupport.mono' hw_supp ?_
    intro x hx
    by_contra hx_supp
    have h0 : fderiv ℝ w x = 0 := fderiv_of_notMem_tsupport ℝ hx_supp
    rw [Function.mem_support] at hx
    apply hx
    simp [h0]
  exact h_cont.integrable_of_hasCompactSupport h_supp

/-- The per-cutoff estimate. With `w = v·χ` (which vanishes near `0`), the vanishing
    case gives `∫ w²·inverseRSq ≤ 4∫∑(∂ᵢw)²`. Young's inequality splits the gradient,
    `∑(∂ᵢw)² ≤ (1+t)∑(∂ᵢv)² + (1+t⁻¹)v²∑(∂ᵢχ)²` (using `χ² ≤ 1`), and integrating gives
    the stated bound. The second term is the cutoff-gradient error, shown to vanish
    as `ε → 0` in the assembly. -/
private lemma hardy_cutoff_step
    {v : R3 → ℝ} (hv_smooth : ContDiff ℝ ∞ v) (hv_supp : HasCompactSupport v)
    {χ : R3 → ℝ} (hχ_smooth : ContDiff ℝ ∞ χ)
    {ε : ℝ} (hε : 0 < ε) (hχ0 : ∀ x, ‖x‖ ≤ ε → χ x = 0)
    (hχ01 : ∀ x, χ x ∈ Set.Icc (0:ℝ) 1)
    {t : ℝ} (ht : 0 < t) :
    ∫ x, (v x * χ x) ^ 2 * inverseRSq x
      ≤ 4 * (1 + t) * (∫ x, ∑ i : Fin 3,
            (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2)
        + 4 * (1 + t⁻¹) * (∫ x, v x ^ 2 * ∑ i : Fin 3,
            (fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ))) ^ 2) := by
  have hv_diff : Differentiable ℝ v :=
    hv_smooth.differentiable (by exact_mod_cast ENat.top_ne_zero)
  have hχ_diff : Differentiable ℝ χ :=
    hχ_smooth.differentiable (by exact_mod_cast ENat.top_ne_zero)
  -- Vanishing case applied to `w = v·χ`.
  have hw_zero : ∀ x, ‖x‖ < ε → v x * χ x = 0 := fun x hx => by
    rw [hχ0 x (le_of_lt hx), mul_zero]
  have h_van := hardy_inequality_smooth_of_vanishing (v := fun x => v x * χ x)
    (hv_smooth.mul hχ_smooth) hv_supp.mul_right ε hε hw_zero
  -- Pointwise Young split of the gradient of `w`.
  have h_ptwise : ∀ x,
      (∑ i : Fin 3, (fderiv ℝ (fun y => v y * χ y) x (EuclideanSpace.single i (1:ℝ))) ^ 2)
        ≤ (1 + t) * (∑ i : Fin 3, (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2)
          + (1 + t⁻¹) * (v x ^ 2 * ∑ i : Fin 3,
              (fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ))) ^ 2) := by
    intro x
    have hχsq : χ x ^ 2 ≤ 1 := by obtain ⟨h0, h1⟩ := hχ01 x; nlinarith
    have per_i : ∀ i : Fin 3,
        (fderiv ℝ (fun y => v y * χ y) x (EuclideanSpace.single i (1:ℝ))) ^ 2
          ≤ (1 + t) * (χ x ^ 2 * (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2)
            + (1 + t⁻¹) * (v x ^ 2 * (fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ))) ^ 2) := by
      intro i
      have hleib : fderiv ℝ (fun y => v y * χ y) x (EuclideanSpace.single i (1:ℝ))
          = χ x * fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))
            + v x * fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ)) := by
        rw [fderiv_fun_mul (hv_diff x) (hχ_diff x)]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring
      rw [hleib]
      calc (χ x * fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))
              + v x * fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ))) ^ 2
          ≤ (1 + t) * (χ x * fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2
            + (1 + t⁻¹) * (v x * fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ))) ^ 2 :=
            young_sq ht _ _
        _ = (1 + t) * (χ x ^ 2 * (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2)
            + (1 + t⁻¹) * (v x ^ 2 * (fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ))) ^ 2) := by
            rw [mul_pow, mul_pow]
    calc ∑ i : Fin 3, (fderiv ℝ (fun y => v y * χ y) x (EuclideanSpace.single i (1:ℝ))) ^ 2
        ≤ ∑ i : Fin 3, ((1 + t) * (χ x ^ 2 * (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2)
            + (1 + t⁻¹) * (v x ^ 2 * (fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ))) ^ 2)) :=
          Finset.sum_le_sum (fun i _ => per_i i)
      _ = (1 + t) * (χ x ^ 2 * ∑ i : Fin 3, (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2)
          + (1 + t⁻¹) * (v x ^ 2 * ∑ i : Fin 3,
              (fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ))) ^ 2) := by
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [← Finset.mul_sum, ← Finset.mul_sum]
          · rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ (1 + t) * (∑ i : Fin 3, (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2)
          + (1 + t⁻¹) * (v x ^ 2 * ∑ i : Fin 3,
              (fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ))) ^ 2) := by
          have hSv : 0 ≤ ∑ i : Fin 3, (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2 :=
            Finset.sum_nonneg (fun i _ => sq_nonneg _)
          gcongr
          nlinarith [hχsq]
  -- Integrate the pointwise bound.
  have hB_int := sum_sq_fderiv_integrable hv_smooth hv_supp
  have hw_int := sum_sq_fderiv_integrable (hv_smooth.mul hχ_smooth) hv_supp.mul_right
  have hT3_int : Integrable (fun x => v x ^ 2 * ∑ i : Fin 3,
      (fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ))) ^ 2) volume := by
    haveI : IsFiniteMeasureOnCompacts (volume : Measure R3) := by
      infer_instance
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (hv_smooth.continuous.pow 2).mul
        (continuous_finsetSum _ (fun i _ =>
          ((hχ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2))
    · exact (hv_supp.comp_left (g := (· ^ 2)) (by simp)).mul_right
  have h_int_rhs : Integrable (fun x =>
      (1 + t) * (∑ i : Fin 3, (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2)
        + (1 + t⁻¹) * (v x ^ 2 * ∑ i : Fin 3,
            (fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ))) ^ 2)) volume :=
    (hB_int.const_mul _).add (hT3_int.const_mul _)
  have h_int_le := integral_mono hw_int h_int_rhs h_ptwise
  rw [integral_add (hB_int.const_mul _) (hT3_int.const_mul _),
    integral_const_mul, integral_const_mul] at h_int_le
  -- Combine with the vanishing-case bound.
  calc ∫ x, (v x * χ x) ^ 2 * inverseRSq x
      ≤ 4 * ∫ x, ∑ i : Fin 3,
          (fderiv ℝ (fun y => v y * χ y) x (EuclideanSpace.single i (1:ℝ))) ^ 2 := h_van
    _ ≤ 4 * ((1 + t) * (∫ x, ∑ i : Fin 3,
            (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2)
          + (1 + t⁻¹) * (∫ x, v x ^ 2 * ∑ i : Fin 3,
              (fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ))) ^ 2)) := by linarith [h_int_le]
    _ = 4 * (1 + t) * (∫ x, ∑ i : Fin 3,
            (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2)
        + 4 * (1 + t⁻¹) * (∫ x, v x ^ 2 * ∑ i : Fin 3,
            (fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ))) ^ 2) := by ring

/-- The cutoff-gradient error term vanishes linearly in `ε`. With `v² ≤ K`,
    `‖∇χ‖ ≤ M/ε`, and `∇χ = 0` outside `B(0, 2ε)`, the integrand `v²∑(∂ᵢχ)²` is
    bounded by `3K(M/ε)²` and supported in `B(0, 2ε)`, whose volume scales as
    `(2ε)³`. The `ε³/ε²` cancellation leaves a bound linear in `ε`. -/
private lemma cutoff_grad_sq_integral_le
    {v : R3 → ℝ} (hv_smooth : ContDiff ℝ ∞ v) (hv_supp : HasCompactSupport v)
    {K : ℝ} (hK : ∀ x, v x ^ 2 ≤ K) (hK0 : 0 ≤ K)
    {χ : R3 → ℝ} (hχ_smooth : ContDiff ℝ ∞ χ)
    {M ε : ℝ} (_hM : 0 ≤ M) (hε : 0 < ε)
    (hχd : ∀ x, ‖fderiv ℝ χ x‖ ≤ M / ε)
    (hχd0 : ∀ x, 2 * ε < ‖x‖ → fderiv ℝ χ x = 0) :
    ∫ x, v x ^ 2 * ∑ i : Fin 3, (fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ))) ^ 2
      ≤ 24 * K * M ^ 2 * (volume.real (Metric.ball (0:R3) 1)) * ε := by
  haveI : (volume : Measure R3).IsAddHaarMeasure := by
    infer_instance
  haveI : IsFiniteMeasureOnCompacts (volume : Measure R3) := by
    infer_instance
  -- Pointwise bound on the squared gradient of χ.
  have h_grad_sq : ∀ x, ∑ i : Fin 3,
      (fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ))) ^ 2 ≤ 3 * (M / ε) ^ 2 := by
    intro x
    have hb : ∀ i : Fin 3,
        (fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ))) ^ 2 ≤ (M / ε) ^ 2 := by
      intro i
      have h1 : |fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ))| ≤ M / ε := by
        calc |fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ))|
            = ‖fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ))‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖fderiv ℝ χ x‖ * ‖(EuclideanSpace.single i (1:ℝ) : R3)‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ = ‖fderiv ℝ χ x‖ := by
              rw [show ‖(EuclideanSpace.single i (1:ℝ) : R3)‖ = 1 by
                simp [PiLp.norm_single], mul_one]
          _ ≤ M / ε := hχd x
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    calc ∑ i : Fin 3, (fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ))) ^ 2
        ≤ ∑ _i : Fin 3, (M / ε) ^ 2 := Finset.sum_le_sum (fun i _ => hb i)
      _ = 3 * (M / ε) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num
  -- Integrability of the integrand (continuous with compact support).
  have hT3int : Integrable (fun x => v x ^ 2 * ∑ i : Fin 3,
      (fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ))) ^ 2) volume := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (hv_smooth.continuous.pow 2).mul
        (continuous_finsetSum _ (fun i _ =>
          ((hχ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2))
    · exact (hv_supp.comp_left (g := (· ^ 2)) (by simp)).mul_right
  -- Indicator dominator over the closed ball `B(0, 2ε)`.
  have hg_int : Integrable ((Metric.closedBall (0:R3) (2 * ε)).indicator
      (fun _ => 3 * K * (M / ε) ^ 2)) volume := by
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact integrableOn_const (hs := (isCompact_closedBall (0:R3) (2 * ε)).measure_lt_top.ne)
  have h_ptbound : ∀ x, v x ^ 2 * ∑ i : Fin 3,
      (fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ))) ^ 2
        ≤ (Metric.closedBall (0:R3) (2 * ε)).indicator (fun _ => 3 * K * (M / ε) ^ 2) x := by
    intro x
    by_cases hx : x ∈ Metric.closedBall (0:R3) (2 * ε)
    · rw [Set.indicator_of_mem hx]
      calc v x ^ 2 * ∑ i : Fin 3, (fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ))) ^ 2
          ≤ K * (3 * (M / ε) ^ 2) :=
            mul_le_mul (hK x) (h_grad_sq x)
              (Finset.sum_nonneg (fun i _ => sq_nonneg _)) hK0
        _ = 3 * K * (M / ε) ^ 2 := by ring
    · rw [Set.indicator_of_notMem hx]
      have hxn : 2 * ε < ‖x‖ := by
        rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx; exact hx
      simp [hχd0 x hxn]
  -- Integrate and apply ball-volume scaling.
  calc ∫ x, v x ^ 2 * ∑ i : Fin 3, (fderiv ℝ χ x (EuclideanSpace.single i (1:ℝ))) ^ 2
      ≤ ∫ x, (Metric.closedBall (0:R3) (2 * ε)).indicator
          (fun _ => 3 * K * (M / ε) ^ 2) x := integral_mono hT3int hg_int h_ptbound
    _ = volume.real (Metric.closedBall (0:R3) (2 * ε)) * (3 * K * (M / ε) ^ 2) := by
        rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul]
    _ = (2 * ε) ^ 3 * volume.real (Metric.ball (0:R3) 1) * (3 * K * (M / ε) ^ 2) := by
        rw [Measure.addHaar_real_closedBall _ _ (by positivity), finrank_euclideanSpace_fin]
    _ = 24 * K * M ^ 2 * (volume.real (Metric.ball (0:R3) 1)) * ε := by
        have hεne : ε ≠ 0 := hε.ne'
        field_simp
        ring

/-- **Hardy's inequality for real smooth compactly supported functions.**

    For `v ∈ C_c^∞(ℝ³, ℝ)`: `∫ v²/|x|² ≤ 4 ∫ ∑ᵢ (∂ᵢv)²`.

    Removes the vanishing-near-origin hypothesis from
    `hardy_inequality_smooth_of_vanishing` by the cutoff limit. Set `vₙ = v·χₙ`
    with `χₙ` vanishing on `B(0, 1/(n+1))`. The vanishing case + Young's inequality
    (`hardy_cutoff_step`) give, for every `t > 0`,
    `∫ vₙ²/|x|² ≤ 4(1+t)·∫∑(∂ᵢv)² + 4(1+t⁻¹)·O(1/(n+1))`.
    Dominated convergence sends `∫ vₙ²/|x|² → ∫ v²/|x|²` (dominated by the integrable
    `v²/|x|²`, with `χₙ → 1` off the origin); the error term vanishes
    (`cutoff_grad_sq_integral_le`). Hence `∫ v²/|x|² ≤ 4(1+t)·∫∑(∂ᵢv)²` for all
    `t > 0`, and `t → 0` gives the result. -/
theorem hardy_inequality_smooth_real
    {v : R3 → ℝ} (hv_smooth : ContDiff ℝ ∞ v) (hv_supp : HasCompactSupport v) :
    ∫ x, v x ^ 2 * inverseRSq x ≤
      4 * ∫ x, ∑ i : Fin 3, (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2 := by
  haveI : (volume : Measure R3).IsAddHaarMeasure := by
    infer_instance
  have hv_cont : Continuous v := hv_smooth.continuous
  -- `v²·inverseRSq` is the integrable dominator.
  have hvsq_int := vsq_inverseRSq_integrable hv_cont hv_supp
  -- A uniform bound `v² ≤ K`.
  obtain ⟨K, hK_norm⟩ := (hv_cont.pow 2).bounded_above_of_compact_support
    (hv_supp.comp_left (g := (· ^ 2)) (by simp))
  have hK : ∀ x, v x ^ 2 ≤ K := fun x =>
    (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hK_norm x)
  have hK0 : 0 ≤ K := (sq_nonneg (v 0)).trans (hK 0)
  -- The scaled inner-cutoff family and a sequence `εₙ = 1/(n+1) → 0`.
  obtain ⟨M, hM_nn, hcut⟩ := exists_hardy_cutoff
  have hseq_tend : Tendsto (fun n : ℕ => (1:ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  set e : ℕ → ℝ := fun n => 1 / (n + 1) with he_def
  have he_pos : ∀ n, 0 < e n := fun n => by positivity
  have hcut' : ∀ n : ℕ, ∃ χ : R3 → ℝ,
      ContDiff ℝ ∞ χ ∧ (∀ x, ‖x‖ ≤ e n → χ x = 0) ∧ (∀ x, 2 * e n ≤ ‖x‖ → χ x = 1) ∧
      (∀ x, χ x ∈ Set.Icc (0:ℝ) 1) ∧ (∀ x, ‖fderiv ℝ χ x‖ ≤ M / e n) ∧
      (∀ x, 2 * e n < ‖x‖ → fderiv ℝ χ x = 0) := fun n => hcut (e n) (he_pos n)
  choose χ hχs hχ0 hχ1 hχ01 hχd hχd0 using hcut'
  -- a.e. every point is nonzero (the origin is null).
  have hae : ∀ᵐ x ∂(volume : Measure R3), x ≠ 0 := by
    have hsing : (volume : Measure R3) {x : R3 | x = 0} = 0 := by
      rw [show {x : R3 | x = 0} = {(0 : R3)} from by ext x; simp]; exact measure_singleton 0
    rw [ae_iff]; simp only [ne_eq, not_not]; exact hsing
  -- Aₙ → A by dominated convergence.
  have hAn_tend : Tendsto (fun n => ∫ x, (v x * χ n x) ^ 2 * inverseRSq x) atTop
      (𝓝 (∫ x, v x ^ 2 * inverseRSq x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => v x ^ 2 * inverseRSq x)
      (fun n => ?_) hvsq_int (fun n => ?_) ?_
    · exact (((hv_cont.mul (hχs n).continuous).pow 2).measurable.mul
        inverseRSq_measurable).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (inverseRSq_nonneg x))]
      have hχsq : (χ n x) ^ 2 ≤ 1 := by obtain ⟨a, b⟩ := hχ01 n x; nlinarith
      calc (v x * χ n x) ^ 2 * inverseRSq x = v x ^ 2 * (χ n x) ^ 2 * inverseRSq x := by ring
        _ ≤ v x ^ 2 * 1 * inverseRSq x := by
            apply mul_le_mul_of_nonneg_right _ (inverseRSq_nonneg x)
            exact mul_le_mul_of_nonneg_left hχsq (sq_nonneg _)
        _ = v x ^ 2 * inverseRSq x := by ring
    · filter_upwards [hae] with x hx
      have hcong : ∀ᶠ n in atTop, v x ^ 2 * inverseRSq x = (v x * χ n x) ^ 2 * inverseRSq x := by
        have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
        have h2e : Tendsto (fun n => 2 * e n) atTop (𝓝 0) := by
          simpa using (hseq_tend.const_mul 2)
        filter_upwards [h2e.eventually (Iio_mem_nhds hxpos)] with n hn
        rw [hχ1 n x (le_of_lt hn), mul_one]
      exact Filter.Tendsto.congr' hcong tendsto_const_nhds
  -- The key bound `A ≤ 4(1+t)·B` for every `t > 0`.
  have key : ∀ t : ℝ, 0 < t → (∫ x, v x ^ 2 * inverseRSq x)
      ≤ 4 * (1 + t) * (∫ x, ∑ i : Fin 3,
          (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2) := by
    intro t ht
    have hAn_le : ∀ n, (∫ x, (v x * χ n x) ^ 2 * inverseRSq x)
        ≤ 4 * (1 + t) * (∫ x, ∑ i : Fin 3,
            (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2)
          + 4 * (1 + t⁻¹) * (24 * K * M ^ 2 * volume.real (Metric.ball (0:R3) 1) * e n) := by
      intro n
      have h1 := hardy_cutoff_step hv_smooth hv_supp (hχs n) (he_pos n) (hχ0 n) (hχ01 n) ht
      have h2 := cutoff_grad_sq_integral_le hv_smooth hv_supp hK hK0 (hχs n) hM_nn (he_pos n)
        (hχd n) (hχd0 n)
      have hcoef : (0:ℝ) ≤ 4 * (1 + t⁻¹) := by
        have : (0:ℝ) ≤ t⁻¹ := inv_nonneg.mpr ht.le; linarith
      have h3 := mul_le_mul_of_nonneg_left h2 hcoef
      linarith [h1, h3]
    have hR_tend : Tendsto (fun n => 4 * (1 + t) * (∫ x, ∑ i : Fin 3,
          (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2)
        + 4 * (1 + t⁻¹) * (24 * K * M ^ 2 * volume.real (Metric.ball (0:R3) 1) * e n)) atTop
        (𝓝 (4 * (1 + t) * (∫ x, ∑ i : Fin 3,
          (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2))) := by
      have : Tendsto (fun n => 4 * (1 + t⁻¹) *
          (24 * K * M ^ 2 * volume.real (Metric.ball (0:R3) 1) * e n)) atTop (𝓝 0) := by
        have h0 := (hseq_tend.const_mul
          (4 * (1 + t⁻¹) * (24 * K * M ^ 2 * volume.real (Metric.ball (0:R3) 1))))
        simpa [mul_assoc] using h0
      simpa using (tendsto_const_nhds.add this)
    exact le_of_tendsto_of_tendsto' hAn_tend hR_tend hAn_le
  -- `t → 0` along `tₘ = 1/(m+1)` gives `A ≤ 4·B`.
  have h1t : Tendsto (fun m : ℕ => (1:ℝ) + e m) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hseq_tend
  have hT_tend : Tendsto (fun m : ℕ => 4 * (1 + e m) * (∫ x, ∑ i : Fin 3,
        (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2)) atTop
      (𝓝 (4 * ∫ x, ∑ i : Fin 3,
        (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2)) := by
    simpa using (h1t.const_mul (4:ℝ)).mul_const
      (∫ x, ∑ i : Fin 3, (fderiv ℝ v x (EuclideanSpace.single i (1:ℝ))) ^ 2)
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hT_tend
    (fun m => key (e m) (he_pos m))

/-- **Hardy's inequality for smooth functions.**

    For ψ ∈ C_c^∞(ℝ³):
      ∫ |ψ(x)|²/|x|² dx ≤ 4 ∫ |∇ψ(x)|² dx

    **Discharge route (~150 lines):**

    1. **Divergence identity.** For d = 3:
         div(x̂/|x|) = (d−2)/|x|² = 1/|x|²
       More precisely, div(x/|x|²) = (d−2)/|x|² in the distributional sense.

    2. **Integration by parts.** For ψ ∈ C_c^∞, integrate on ℝ³ \ B(0,ε):
         ∫_{|x|>ε} |ψ|²/|x|² dx = ∫_{|x|>ε} |ψ|² div(x̂/|x|) dx
           = −∫_{|x|>ε} ∇(|ψ|²) · (x̂/|x|) dx + boundary term
           = −2 Re ∫_{|x|>ε} (ψ̄/|x|)(x̂ · ∇ψ) dx + boundary term

    3. **Boundary vanishes.** The boundary integral over ∂B(0,ε) is
       bounded by C·ε → 0 as ε → 0 (since ψ is smooth, hence bounded
       near the origin).

    4. **Cauchy-Schwarz.** Apply |⟨f, g⟩| ≤ ‖f‖ · ‖g‖ with
       f(x) = ψ̄(x)/|x| and g(x) = x̂ · ∇ψ(x):
         |2 Re ∫ (ψ̄/|x|)(x̂ · ∇ψ) dx| ≤ 2 (∫ |ψ|²/|x|²)^{1/2} (∫ |∇ψ|²)^{1/2}

    5. **Absorb.** Set A = (∫|ψ|²/|x|²)^{1/2}. From steps 2-4:
         A² ≤ 2A · (∫|∇ψ|²)^{1/2}
       Divide by A (if A = 0, the result is trivial):
         A ≤ 2 (∫|∇ψ|²)^{1/2}
       Square: ∫|ψ|²/|x|² ≤ 4 ∫|∇ψ|². -/
theorem hardy_inequality_smooth
    (ψ : R3 → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hsupp : HasCompactSupport ψ) :
    ∫ x, inverseRSq x * ‖ψ x‖ ^ 2 ≤
    4 * ∫ x, ∑ i : Fin 3, ‖fderiv ℝ ψ x (EuclideanSpace.single i 1)‖ ^ 2 := by
  have hψ_diff : Differentiable ℝ ψ := hψ.differentiable (by exact_mod_cast ENat.top_ne_zero)
  -- Real and imaginary parts: smooth, compactly supported.
  have hvr_smooth : ContDiff ℝ ∞ (fun x => Complex.reCLM (ψ x)) := Complex.reCLM.contDiff.comp hψ
  have hvi_smooth : ContDiff ℝ ∞ (fun x => Complex.imCLM (ψ x)) := Complex.imCLM.contDiff.comp hψ
  have hvr_supp : HasCompactSupport (fun x => Complex.reCLM (ψ x)) :=
    hsupp.comp_left (g := (Complex.reCLM : ℂ → ℝ)) (by simp)
  have hvi_supp : HasCompactSupport (fun x => Complex.imCLM (ψ x)) :=
    hsupp.comp_left (g := (Complex.imCLM : ℂ → ℝ)) (by simp)
  -- `Re`/`Im` commute with the derivative.
  have hvr_fd : ∀ x (e : R3),
      fderiv ℝ (fun y => Complex.reCLM (ψ y)) x e = Complex.reCLM (fderiv ℝ ψ x e) := by
    intro x e
    have h : HasFDerivAt (fun y => Complex.reCLM (ψ y))
        (Complex.reCLM.comp (fderiv ℝ ψ x)) x :=
      Complex.reCLM.hasFDerivAt.comp x (hψ_diff x).hasFDerivAt
    rw [h.fderiv, ContinuousLinearMap.comp_apply]
  have hvi_fd : ∀ x (e : R3),
      fderiv ℝ (fun y => Complex.imCLM (ψ y)) x e = Complex.imCLM (fderiv ℝ ψ x e) := by
    intro x e
    have h : HasFDerivAt (fun y => Complex.imCLM (ψ y))
        (Complex.imCLM.comp (fderiv ℝ ψ x)) x :=
      Complex.imCLM.hasFDerivAt.comp x (hψ_diff x).hasFDerivAt
    rw [h.fderiv, ContinuousLinearMap.comp_apply]
  -- `‖z‖² = (Re z)² + (Im z)²`.
  have hnormsq : ∀ z : ℂ, ‖z‖ ^ 2 = (Complex.reCLM z) ^ 2 + (Complex.imCLM z) ^ 2 := fun z => by
    rw [Complex.reCLM_apply, Complex.imCLM_apply, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  -- Hardy for each real part.
  have hr := hardy_inequality_smooth_real hvr_smooth hvr_supp
  have hi := hardy_inequality_smooth_real hvi_smooth hvi_supp
  -- Integrability facts (with reduced types so `integral_add` rewrites cleanly).
  have hfr_int : Integrable (fun x => (Complex.reCLM (ψ x)) ^ 2 * inverseRSq x) volume :=
    vsq_inverseRSq_integrable hvr_smooth.continuous hvr_supp
  have hfi_int : Integrable (fun x => (Complex.imCLM (ψ x)) ^ 2 * inverseRSq x) volume :=
    vsq_inverseRSq_integrable hvi_smooth.continuous hvi_supp
  have hgr_int : Integrable (fun x => ∑ i : Fin 3,
      (fderiv ℝ (fun y => Complex.reCLM (ψ y)) x (EuclideanSpace.single i (1:ℝ))) ^ 2) volume :=
    sum_sq_fderiv_integrable hvr_smooth hvr_supp
  have hgi_int : Integrable (fun x => ∑ i : Fin 3,
      (fderiv ℝ (fun y => Complex.imCLM (ψ y)) x (EuclideanSpace.single i (1:ℝ))) ^ 2) volume :=
    sum_sq_fderiv_integrable hvi_smooth hvi_supp
  -- Split the two integrals into real and imaginary contributions.
  have hLHS : (∫ x, inverseRSq x * ‖ψ x‖ ^ 2)
      = (∫ x, (Complex.reCLM (ψ x)) ^ 2 * inverseRSq x)
        + (∫ x, (Complex.imCLM (ψ x)) ^ 2 * inverseRSq x) := by
    rw [show (∫ x, inverseRSq x * ‖ψ x‖ ^ 2)
          = ∫ x, ((Complex.reCLM (ψ x)) ^ 2 * inverseRSq x
              + (Complex.imCLM (ψ x)) ^ 2 * inverseRSq x)
        from integral_congr_ae (Filter.Eventually.of_forall fun x => by
          simp only [hnormsq (ψ x)]; ring)]
    exact integral_add hfr_int hfi_int
  have hRHS : (∫ x, ∑ i : Fin 3, ‖fderiv ℝ ψ x (EuclideanSpace.single i 1)‖ ^ 2)
      = (∫ x, ∑ i : Fin 3,
          (fderiv ℝ (fun y => Complex.reCLM (ψ y)) x (EuclideanSpace.single i (1:ℝ))) ^ 2)
        + (∫ x, ∑ i : Fin 3,
          (fderiv ℝ (fun y => Complex.imCLM (ψ y)) x (EuclideanSpace.single i (1:ℝ))) ^ 2) := by
    rw [show (∫ x, ∑ i : Fin 3, ‖fderiv ℝ ψ x (EuclideanSpace.single i 1)‖ ^ 2)
          = ∫ x, ((∑ i : Fin 3,
                (fderiv ℝ (fun y => Complex.reCLM (ψ y)) x (EuclideanSpace.single i (1:ℝ))) ^ 2)
              + ∑ i : Fin 3,
                (fderiv ℝ (fun y => Complex.imCLM (ψ y)) x (EuclideanSpace.single i (1:ℝ))) ^ 2)
        from integral_congr_ae (Filter.Eventually.of_forall fun x => by
          simp only [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hvr_fd x _, hvi_fd x _, hnormsq (fderiv ℝ ψ x (EuclideanSpace.single i 1))])]
    exact integral_add hgr_int hgi_int
  rw [hLHS, hRHS]
  linarith [hr, hi]

/-! ## Hardy's inequality: H¹ extension

Extension from C_c^∞ to H¹ via density.
-/

/-- The squared `L²`-norm of an `L²` element is the integral of the squared
    pointwise norm: `‖f‖² = ∫ ‖f(x)‖²`. Via the `L²` inner product
    `‖f‖² = re⟪f,f⟫ = re ∫⟪f,f⟫ = ∫ ‖f(x)‖²`. -/
lemma norm_sq_eq_integral_norm_sq (f : L2_R3) :
    ‖f‖ ^ 2 = ∫ x, ‖(f : R3 → ℂ) x‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) f, MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner f f)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact inner_self_eq_norm_sq (𝕜 := ℂ) ((f : R3 → ℂ) x)

/-- **Bridge lemma (Hardy integral).** For smooth compactly supported `φ`, the
    Hardy integral of its `L²` class equals the integral over `φ` directly
    (the `L²` representative agrees with `φ` a.e.). -/
lemma hardyIntegral_toLp {φ : R3 → ℂ} (hφ : MemLp φ 2 volume) :
    hardyIntegral (hφ.toLp φ) = ∫ x, inverseRSq x * ‖φ x‖ ^ 2 := by
  unfold hardyIntegral
  refine integral_congr_ae ?_
  filter_upwards [hφ.coeFn_toLp] with x hx
  rw [hx]

/-- **Bridge lemma (gradient norm).** For smooth compactly supported `φ`, the
    Dirichlet form of its `H²` class equals the integral of `∑ᵢ |∂ᵢφ|²`. Each weak
    gradient component is `toLp(∂ᵢφ)` (weak-derivative uniqueness +
    `hasWeakDerivative_of_smooth_compactSupport`), whose squared `L²`-norm is
    `∫ |∂ᵢφ|²` (bridge `norm_sq_eq_integral_norm_sq`); summing and pulling the
    finite sum through the integral gives the claim. -/
lemma gradientNormSq_toLp {φ : R3 → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) (hmem : MemLp φ 2 volume) :
    gradientNormSq (hmem.toLp φ)
        (sobolevH2_le_H1 (smooth_compactSupport_memSobolevH2 φ hφ hsupp hmem))
      = ∫ x, ∑ i : Fin 3, ‖fderiv ℝ φ x (EuclideanSpace.single i 1)‖ ^ 2 := by
  haveI : IsFiniteMeasureOnCompacts (volume : Measure R3) := by
    infer_instance
  -- Each weak-gradient component is `toLp (∂ᵢφ)`, with squared norm `∫ |∂ᵢφ|²`.
  have step1 : ∀ i : Fin 3,
      ‖weakGradient (hmem.toLp φ)
          (sobolevH2_le_H1 (smooth_compactSupport_memSobolevH2 φ hφ hsupp hmem)) i‖ ^ 2
        = ∫ x, ‖fderiv ℝ φ x (EuclideanSpace.single i 1)‖ ^ 2 := by
    intro i
    have hwg : weakGradient (hmem.toLp φ)
        (sobolevH2_le_H1 (smooth_compactSupport_memSobolevH2 φ hφ hsupp hmem)) i
          = (memLp_partialDeriv φ i hφ hsupp).toLp
            (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
      apply hasWeakDerivative_unique (hmem.toLp φ) i
      · exact weakGradient_spec _ _ i
      · exact hasWeakDerivative_of_smooth_compactSupport hφ hsupp hmem
          (memLp_partialDeriv φ i hφ hsupp)
    rw [hwg, norm_sq_eq_integral_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_partialDeriv φ i hφ hsupp).coeFn_toLp] with x hx
    rw [hx]
  -- Integrability of each `|∂ᵢφ|²` (continuous with compact support).
  have hint : ∀ i : Fin 3, Integrable
      (fun x => ‖fderiv ℝ φ x (EuclideanSpace.single i 1)‖ ^ 2) volume := fun i =>
    ((contDiff_partialDeriv φ i hφ).continuous.norm.pow 2).integrable_of_hasCompactSupport
      ((hasCompactSupport_partialDeriv φ i hsupp).comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp))
  unfold gradientNormSq
  rw [Finset.sum_congr rfl (fun i _ => step1 i)]
  exact (integral_finsetSum Finset.univ (fun i _ => hint i)).symm

/-- The `i`-th weak gradient of `toLp φ` is `toLp (∂ᵢφ)` (weak-derivative uniqueness). -/
lemma weakGradient_toLp_eq {φ : R3 → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) (hmem : MemLp φ 2 volume) (i : Fin 3) :
    weakGradient (hmem.toLp φ)
        (sobolevH2_le_H1 (smooth_compactSupport_memSobolevH2 φ hφ hsupp hmem)) i
      = (memLp_partialDeriv φ i hφ hsupp).toLp
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
  apply hasWeakDerivative_unique (hmem.toLp φ) i
  · exact weakGradient_spec _ _ i
  · exact hasWeakDerivative_of_smooth_compactSupport hφ hsupp hmem (memLp_partialDeriv φ i hφ hsupp)

/-- **Per-approximant Hardy bound.** For smooth compactly supported `φ`, Hardy holds
    for its `L²` class: `hardyIntegral (toLp φ) ≤ 4 · gradientNormSq (toLp φ)`. Combines
    the two bridge lemmas with `hardy_inequality_smooth`. -/
lemma hardyIntegral_toLp_le {φ : R3 → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) (hmem : MemLp φ 2 volume) :
    hardyIntegral (hmem.toLp φ) ≤ 4 * gradientNormSq (hmem.toLp φ)
        (sobolevH2_le_H1 (smooth_compactSupport_memSobolevH2 φ hφ hsupp hmem)) := by
  rw [hardyIntegral_toLp hmem, gradientNormSq_toLp hφ hsupp hmem]
  exact hardy_inequality_smooth φ hφ hsupp

/-- **Fatou bound (lower semicontinuity).** For `ψ ∈ H¹`, the `ℝ≥0∞`-valued Hardy
    integral is bounded by `4·gradientNormSq ψ`. This is the heart of the H¹ Hardy
    inequality: smooth approximants `φₙ → ψ` (Meyers–Serrin), their gradient norms
    converge, an a.e.-convergent subsequence exists, and Fatou's lemma transfers the
    smooth bound to the limit. The real-valued Hardy inequality and integrability of
    the Hardy integrand are both corollaries. -/
private lemma hardy_lintegral_le (ψ : L2_R3) (hψ : MemSobolevH1 ψ) :
    ∫⁻ x, ENNReal.ofReal (inverseRSq x * ‖(ψ : R3 → ℂ) x‖ ^ 2) ∂volume
      ≤ ENNReal.ofReal (4 * gradientNormSq ψ hψ) := by
  haveI : (volume : Measure R3).IsAddHaarMeasure := by
    infer_instance
  -- Smooth compactly supported approximants `φₙ → ψ` in `H¹` (Meyers–Serrin), `εₙ = 1/(n+1)`.
  have happrox : ∀ n : ℕ, ∃ (φ : R3 → ℂ) (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ),
      ‖ψ - (memLp_of_smooth_compactSupport φ hφ hsupp).toLp φ‖ < 1 / (n + 1) ∧
      ∀ i, ‖weakGradient ψ hψ i - (memLp_partialDeriv φ i hφ hsupp).toLp
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))‖ < 1 / (n + 1) :=
    fun n => meyers_serrin_approx_multi ψ (weakGradient ψ hψ) (weakGradient_spec ψ hψ)
      (1 / (n + 1)) (by positivity)
  choose φ hφ hsupp hclose hgradclose using happrox
  let hmem : ∀ n, MemLp (φ n) 2 volume := fun n =>
    memLp_of_smooth_compactSupport (φ n) (hφ n) (hsupp n)
  -- (1) Gradient norms converge: `gradientNormSq (toLp φₙ) → gradientNormSq ψ`.
  have hwg_tend : ∀ i, Tendsto (fun n => (memLp_partialDeriv (φ n) i (hφ n) (hsupp n)).toLp
      (fun x => fderiv ℝ (φ n) x (EuclideanSpace.single i 1))) atTop
      (𝓝 (weakGradient ψ hψ i)) := by
    intro i
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [norm_sub_rev]; exact le_of_lt (hgradclose n i)
  have hB_eq : ∀ n, gradientNormSq ((hmem n).toLp (φ n))
      (sobolevH2_le_H1 (smooth_compactSupport_memSobolevH2 (φ n) (hφ n) (hsupp n) (hmem n)))
        = ∑ i : Fin 3, ‖(memLp_partialDeriv (φ n) i (hφ n) (hsupp n)).toLp
            (fun x => fderiv ℝ (φ n) x (EuclideanSpace.single i 1))‖ ^ 2 := by
    intro n
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [weakGradient_toLp_eq (hφ n) (hsupp n) (hmem n) i]
  have htend_B : Tendsto (fun n => gradientNormSq ((hmem n).toLp (φ n))
      (sobolevH2_le_H1 (smooth_compactSupport_memSobolevH2 (φ n) (hφ n) (hsupp n) (hmem n)))) atTop
      (𝓝 (gradientNormSq ψ hψ)) := by
    rw [show (fun n => gradientNormSq ((hmem n).toLp (φ n)) _)
          = (fun n => ∑ i : Fin 3, ‖(memLp_partialDeriv (φ n) i (hφ n) (hsupp n)).toLp
              (fun x => fderiv ℝ (φ n) x (EuclideanSpace.single i 1))‖ ^ 2) from funext hB_eq]
    exact tendsto_finsetSum _ (fun i _ => ((hwg_tend i).norm).pow 2)
  -- (2) `L²`-convergence ⟹ an a.e.-convergent subsequence.
  have hnorm_tend : Tendsto (fun n => ‖ψ - (hmem n).toLp (φ n)‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) (fun n => le_of_lt (hclose n))
      tendsto_one_div_add_atTop_nhds_zero_nat
  have heLp_tend : Tendsto (fun n => eLpNorm
      ((fun x => ((hmem n).toLp (φ n) : R3 → ℂ) x) - (ψ : R3 → ℂ)) 2 volume) atTop (𝓝 0) := by
    have heq : ∀ n, eLpNorm ((fun x => ((hmem n).toLp (φ n) : R3 → ℂ) x) - (ψ : R3 → ℂ)) 2 volume
        = ENNReal.ofReal ‖ψ - (hmem n).toLp (φ n)‖ := by
      intro n
      rw [eLpNorm_congr_ae (Lp.coeFn_sub ((hmem n).toLp (φ n)) ψ).symm,
        ← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top ((hmem n).toLp (φ n) - ψ)),
        ← Lp.norm_def, norm_sub_rev]
    rw [show (fun n => eLpNorm ((fun x => ((hmem n).toLp (φ n) : R3 → ℂ) x) - (ψ : R3 → ℂ)) 2 volume)
          = (fun n => ENNReal.ofReal ‖ψ - (hmem n).toLp (φ n)‖) from funext heq]
    rw [show (0 : ℝ≥0∞) = ENNReal.ofReal 0 from (ENNReal.ofReal_zero).symm]
    exact (ENNReal.continuous_ofReal.tendsto 0).comp hnorm_tend
  obtain ⟨ns, hns_mono, hns_ae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (μ := volume) (two_ne_zero)
      (fun n => Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable ψ) heLp_tend).exists_seq_tendsto_ae
  -- (3) Integrability of each approximant's Hardy integrand, and lintegral ↔ Bochner.
  have hInt : ∀ n, Integrable
      (fun x => inverseRSq x * ‖((hmem n).toLp (φ n) : R3 → ℂ) x‖ ^ 2) volume := by
    intro n
    refine (vsq_inverseRSq_integrable (hφ n).continuous.norm
      ((hsupp n).norm)).congr ?_
    filter_upwards [(hmem n).coeFn_toLp] with x hx
    rw [hx]; ring
  have hlin_eq : ∀ n, ∫⁻ x, ENNReal.ofReal
      (inverseRSq x * ‖((hmem n).toLp (φ n) : R3 → ℂ) x‖ ^ 2) ∂volume
        = ENNReal.ofReal (hardyIntegral ((hmem n).toLp (φ n))) :=
    fun n => (ofReal_integral_eq_lintegral_ofReal (hInt n)
      (Filter.Eventually.of_forall fun x => mul_nonneg (inverseRSq_nonneg x) (sq_nonneg _))).symm
  -- (4) Fatou: lower semicontinuity of the Hardy integral.
  have hpt : ∀ᵐ x ∂volume, ENNReal.ofReal (inverseRSq x * ‖(ψ : R3 → ℂ) x‖ ^ 2)
      = liminf (fun i => ENNReal.ofReal
          (inverseRSq x * ‖((hmem (ns i)).toLp (φ (ns i)) : R3 → ℂ) x‖ ^ 2)) atTop := by
    filter_upwards [hns_ae] with x hx
    refine (Filter.Tendsto.liminf_eq ?_).symm
    exact (ENNReal.continuous_ofReal.tendsto _).comp ((hx.norm.pow 2).const_mul (inverseRSq x))
  calc ∫⁻ x, ENNReal.ofReal (inverseRSq x * ‖(ψ : R3 → ℂ) x‖ ^ 2) ∂volume
      = ∫⁻ x, liminf (fun i => ENNReal.ofReal
          (inverseRSq x * ‖((hmem (ns i)).toLp (φ (ns i)) : R3 → ℂ) x‖ ^ 2)) atTop ∂volume :=
        lintegral_congr_ae hpt
    _ ≤ liminf (fun i => ∫⁻ x, ENNReal.ofReal
          (inverseRSq x * ‖((hmem (ns i)).toLp (φ (ns i)) : R3 → ℂ) x‖ ^ 2) ∂volume) atTop :=
        lintegral_liminf_le' (fun i =>
          (ENNReal.measurable_ofReal.comp_aemeasurable (inverseRSq_measurable.aemeasurable.mul
            ((Lp.aestronglyMeasurable _).aemeasurable.norm.pow_const 2))))
    _ ≤ liminf (fun i => ENNReal.ofReal (4 * gradientNormSq ((hmem (ns i)).toLp (φ (ns i)))
          (sobolevH2_le_H1 (smooth_compactSupport_memSobolevH2 (φ (ns i)) (hφ (ns i))
            (hsupp (ns i)) (hmem (ns i)))))) atTop := by
        refine Filter.liminf_le_liminf (Filter.Eventually.of_forall fun i => ?_)
        rw [hlin_eq (ns i)]
        exact ENNReal.ofReal_le_ofReal (hardyIntegral_toLp_le (hφ (ns i)) (hsupp (ns i)) (hmem (ns i)))
    _ = ENNReal.ofReal (4 * gradientNormSq ψ hψ) := by
        refine Filter.Tendsto.liminf_eq ?_
        exact (ENNReal.continuous_ofReal.tendsto _).comp
          ((htend_B.comp hns_mono.tendsto_atTop).const_mul 4)

/-- `∫ |ψ|²/|x|²` is integrable for `ψ ∈ H¹`: the integrand is nonnegative and
    measurable, and the Fatou bound `hardy_lintegral_le` makes its `∫⁻` finite. -/
lemma inverseRSq_mul_sq_integrable
    (ψ : L2_R3) (hψ : MemSobolevH1 ψ) :
    Integrable (fun x => inverseRSq x * ‖(ψ : R3 → ℂ) x‖ ^ 2) volume := by
  have hnn : ∀ x, (0 : ℝ) ≤ inverseRSq x * ‖(ψ : R3 → ℂ) x‖ ^ 2 :=
    fun x => mul_nonneg (inverseRSq_nonneg x) (sq_nonneg _)
  refine ⟨inverseRSq_measurable.aestronglyMeasurable.mul
    ((Lp.aestronglyMeasurable ψ).norm.pow 2), ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have heq : ∫⁻ x, ‖inverseRSq x * ‖(ψ : R3 → ℂ) x‖ ^ 2‖ₑ ∂volume
      = ∫⁻ x, ENNReal.ofReal (inverseRSq x * ‖(ψ : R3 → ℂ) x‖ ^ 2) ∂volume :=
    lintegral_congr_ae (Filter.Eventually.of_forall fun x => Real.enorm_of_nonneg (hnn x))
  rw [heq]
  exact lt_of_le_of_lt (hardy_lintegral_le ψ hψ) ENNReal.ofReal_lt_top

/-- **Hardy's inequality for H¹ functions.**

    For ψ ∈ H¹(ℝ³):
      ∫ |ψ(x)|²/|x|² dx ≤ 4 ∫ |∇ψ(x)|² dx = 4 · gradientNormSq ψ

    **Discharge route (~80 lines):**

    1. Approximate ψ by ψ_n ∈ C_c^∞ in H¹ norm
       (from `smooth_compactly_supported_dense_H1`).

    2. Hardy for ψ_n: ∫|ψ_n|²/|x|² ≤ 4 ∫|∇ψ_n|² for each n.

    3. **Lower semicontinuity:** Fatou's lemma gives
         ∫|ψ|²/|x|² ≤ liminf_n ∫|ψ_n|²/|x|²

       (since |ψ_n(x)|² → |ψ(x)|² a.e. along a subsequence,
       by the L² convergence ψ_n → ψ, and inverseRSq ≥ 0).

    4. **Gradient convergence:** ∫|∇ψ_n|² → ∫|∇ψ|² = gradientNormSq ψ
       by the H¹ approximation.

    5. Combine: ∫|ψ|²/|x|² ≤ liminf 4∫|∇ψ_n|² = 4 · gradientNormSq ψ. -/
theorem hardy_inequality
    (ψ : L2_R3) (hψ : MemSobolevH1 ψ) :
    hardyIntegral ψ ≤ 4 * gradientNormSq ψ hψ := by
  have hnn : ∀ x, (0 : ℝ) ≤ inverseRSq x * ‖(ψ : R3 → ℂ) x‖ ^ 2 :=
    fun x => mul_nonneg (inverseRSq_nonneg x) (sq_nonneg _)
  have hofReal : ENNReal.ofReal (hardyIntegral ψ) ≤ ENNReal.ofReal (4 * gradientNormSq ψ hψ) := by
    rw [hardyIntegral, ofReal_integral_eq_lintegral_ofReal
      (inverseRSq_mul_sq_integrable ψ hψ) (Filter.Eventually.of_forall hnn)]
    exact hardy_lintegral_le ψ hψ
  have h4nn : (0 : ℝ) ≤ 4 * gradientNormSq ψ hψ := by
    have := gradientNormSq_nonneg ψ hψ; linarith
  exact (ENNReal.ofReal_le_ofReal_iff h4nn).mp hofReal

/-- The Hardy integral is finite for H¹ functions. -/
lemma hardyIntegral_finite
    (ψ : L2_R3) (hψ : MemSobolevH1 ψ) :
    ∃ M : ℝ, hardyIntegral ψ ≤ M :=
  ⟨4 * gradientNormSq ψ hψ, hardy_inequality ψ hψ⟩

/-! ## Operator estimates for 1/r

These are the estimates consumed by `CoulombBound.lean` to establish
relative boundedness of the Coulomb potential.
-/

/-- **‖(1/r)ψ‖² ≤ 4⟨−Δψ, ψ⟩ for ψ ∈ H².**

    This is Hardy rephrased via integration by parts:
    ∫|∇ψ|² = ⟨−Δψ, ψ⟩ for ψ ∈ H² (from `gradient_norm_sq_eq_laplacian_inner`).

    This is the *quadratic form* version of relative boundedness. -/
theorem hardy_quadratic_form
    (ψ : L2_R3) (hψ : MemSobolevH2 ψ) :
    hardyIntegral ψ ≤
    4 * (inner (𝕜 := ℂ) (weakLaplacian ψ hψ) ψ).re := by
  calc hardyIntegral ψ
      ≤ 4 * gradientNormSq ψ (sobolevH2_le_H1 hψ) :=
        hardy_inequality ψ (sobolevH2_le_H1 hψ)
    _ = 4 * (inner (𝕜 := ℂ) (weakLaplacian ψ hψ) ψ).re := by
        congr 1
        rw [← gradient_norm_sq_eq_laplacian_inner ψ hψ, Complex.ofReal_re]

/-- **Cauchy inequality with ε**: ‖(1/r)ψ‖ ≤ ε‖Δψ‖ + C_ε‖ψ‖.

    For any ε > 0, there exists C_ε such that:
      ‖(1/r)ψ‖ ≤ ε ‖−Δψ‖ + C_ε ‖ψ‖

    **Discharge route:**
    From `hardy_quadratic_form`:
      ‖(1/r)ψ‖² ≤ 4 ⟨−Δψ, ψ⟩
                  ≤ 4 ‖−Δψ‖ · ‖ψ‖     (Cauchy-Schwarz)
    Then Young's inequality ab ≤ (ε/2)a² + (1/(2ε))b²:
      ‖(1/r)ψ‖² ≤ 4((ε²/2)‖−Δψ‖² + (1/(2ε²))‖ψ‖²)
                  = 2ε² ‖−Δψ‖² + (2/ε²) ‖ψ‖²
    Taking square roots (and relabelling ε):
      ‖(1/r)ψ‖ ≤ ε ‖−Δψ‖ + C_ε ‖ψ‖

    This is the *operator* version of relative boundedness with bound 0. -/
theorem hardy_operator_bound
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (ψ : L2_R3) (hψ : MemSobolevH2 ψ),
      Real.sqrt (hardyIntegral ψ) ≤
      ε * ‖weakLaplacian ψ hψ‖ + C * ‖ψ‖ := by
  refine ⟨ε⁻¹, le_of_lt (inv_pos.mpr hε), fun ψ hψ => ?_⟩
  set A := ‖weakLaplacian ψ hψ‖ with hA_def
  set B := ‖ψ‖ with hB_def
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ B := norm_nonneg _
  -- `‖(1/r)ψ‖² ≤ 4⟨−Δψ,ψ⟩ ≤ 4‖−Δψ‖‖ψ‖` (quadratic form + Cauchy–Schwarz).
  have hcs : (inner (𝕜 := ℂ) (weakLaplacian ψ hψ) ψ).re ≤ A * B :=
    (RCLike.re_le_norm (inner (𝕜 := ℂ) (weakLaplacian ψ hψ) ψ)).trans
      (norm_inner_le_norm (𝕜 := ℂ) (weakLaplacian ψ hψ) ψ)
  have hHI : hardyIntegral ψ ≤ 4 * (A * B) :=
    (hardy_quadratic_form ψ hψ).trans (by linarith [hcs])
  -- AM–GM: `√(4AB) ≤ εA + ε⁻¹B`.
  have hfin : Real.sqrt (4 * (A * B)) ≤ ε * A + ε⁻¹ * B := by
    have hnn : (0 : ℝ) ≤ ε * A + ε⁻¹ * B :=
      add_nonneg (mul_nonneg hε.le hA0) (mul_nonneg (inv_nonneg.mpr hε.le) hB0)
    rw [show ε * A + ε⁻¹ * B = Real.sqrt ((ε * A + ε⁻¹ * B) ^ 2) from (Real.sqrt_sq hnn).symm]
    apply Real.sqrt_le_sqrt
    have hcross : (ε * A) * (ε⁻¹ * B) = A * B := by
      rw [mul_mul_mul_comm, mul_inv_cancel₀ hε.ne', one_mul]
    nlinarith [sq_nonneg (ε * A - ε⁻¹ * B), hcross]
  calc Real.sqrt (hardyIntegral ψ)
      ≤ Real.sqrt (4 * (A * B)) := Real.sqrt_le_sqrt hHI
    _ ≤ ε * A + ε⁻¹ * B := hfin

/-- **Relative bound is zero**: 1/r is (−Δ)-bounded with relative bound 0.

    This means: for any a > 0, there exists b such that
      ‖(1/r)ψ‖ ≤ a ‖−Δψ‖ + b ‖ψ‖

    Equivalently: the infimum of valid a-constants is 0.

    This is the precise hypothesis needed for Kato-Rellich to conclude
    that −Δ − Z/r is self-adjoint on H²(ℝ³) for *any* Z > 0. -/
theorem coulomb_relative_bound_zero :
    ∀ a : ℝ, 0 < a →
    ∃ b : ℝ, 0 ≤ b ∧
    ∀ (ψ : L2_R3) (hψ : MemSobolevH2 ψ),
      Real.sqrt (hardyIntegral ψ) ≤
      a * ‖weakLaplacian ψ hψ‖ + b * ‖ψ‖ :=
  fun a ha => hardy_operator_bound a ha


/-! ## Interface summary

### Exports for `CoulombBound.lean`:
- `hardy_inequality` — the core estimate
- `hardy_operator_bound` — the ε-form for Kato-Rellich
- `coulomb_relative_bound_zero` — relative bound is 0
- `inverseRSq_mul_sq_integrable` — integrability of the weighted norm

### Exports for `KatoRellich.lean` (via CoulombBound):
- The relative boundedness of V = −Z/r with respect to A = −Δ
  with any a > 0, which is the hypothesis of the abstract theorem.
-/

end Spectra.QuantumMechanics.Hydrogen
