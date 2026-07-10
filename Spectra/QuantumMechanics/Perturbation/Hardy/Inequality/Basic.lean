/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Perturbation.Hardy.Inequality.Defs
/-!
# The Hardy Inequality in Three Dimensions — the general case and operator estimates

This file completes the three-dimensional Hardy inequality

  ∫_{ℝ³} |ψ(x)|²/|x|² dx ≤ 4 ∫_{ℝ³} |∇ψ(x)|² dx

for ψ ∈ H¹(ℝ³), building on the vanishing-near-origin case
(`hardy_inequality_smooth_of_vanishing`) proved in `Hardy.Inequality.Defs`.

## Proof strategy

**Removing the vanishing hypothesis:** multiply by a smooth **inner** cutoff `χ_ε` that
vanishes on `B(0, ε)` and equals `1` outside `B(0, 2ε)`, apply the vanishing case to `v · χ_ε`,
and let `ε → 0` (`hardy_inequality_smooth_real`, `hardy_inequality_smooth`).

**Density extension:** extend from `C_c^∞` to `H¹` via `smooth_compactly_supported_dense_H1`
from `Spaces/Sobolev/`. The `∫|ψ|²/|x|²` functional is lower semicontinuous with respect to
`H¹` convergence, so the bound passes to the closure (`hardy_inequality`).

## Main statements

* `hardy_inequality_smooth` — Hardy for smooth compactly supported functions.
* `hardy_inequality` — Hardy for all ψ ∈ H¹(ℝ³).
* `inverseRSq_mul_sq_integrable` — ∫|ψ|²/|x|² < ∞ for ψ ∈ H¹.
* `hardy_quadratic_form` — ‖(1/r)ψ‖² ≤ 4⟨−Δψ, ψ⟩ for ψ ∈ H².
* `hardy_operator_bound` — the Cauchy-inequality-with-ε form: ‖(1/r)ψ‖ ≤ ε‖Δψ‖ + C_ε‖ψ‖.
* `coulomb_relative_bound_zero` — 1/r is (−Δ)-bounded with relative bound 0, the hypothesis
  consumed by Kato-Rellich (`CoulombBound.lean`, `KatoRellich.lean`).

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
    change 1 - (ρ : R3 → ℝ) (ε⁻¹ • x) = 0
    have : (ρ : R3 → ℝ) (ε⁻¹ • x) = 1 := by
      apply ρ.one_of_mem_closedBall
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv,
        Real.norm_eq_abs, abs_of_pos hε]
      change ε⁻¹ * ‖x‖ ≤ 1
      have hc : ε⁻¹ * ε = 1 := inv_mul_cancel₀ hε.ne'
      have h2 := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hε.le)
      linarith
    rw [this]; ring
  -- 3. χ = 1 off ball (2ε).
  · intro x hx
    change 1 - (ρ : R3 → ℝ) (ε⁻¹ • x) = 1
    have : (ρ : R3 → ℝ) (ε⁻¹ • x) = 0 := by
      apply ρ.zero_of_le_dist
      rw [dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hε]
      change (2 : ℝ) ≤ ε⁻¹ * ‖x‖
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
        change (2 : ℝ) ≤ ε⁻¹ * ‖y‖
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
  set R' := R + 1 with _hR'_def
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
    (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
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
  set e : ℕ → ℝ := fun n => 1 / (n + 1) with _he_def
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
lemma norm_sq_eq_integral_norm_sq (f : l2R3) :
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
        (sobolevH2_le_sobolevH1 (smooth_compactSupport_memSobolevH2 φ hφ hsupp hmem))
      = ∫ x, ∑ i : Fin 3, ‖fderiv ℝ φ x (EuclideanSpace.single i 1)‖ ^ 2 := by
  haveI : IsFiniteMeasureOnCompacts (volume : Measure R3) := by
    infer_instance
  -- Each weak-gradient component is `toLp (∂ᵢφ)`, with squared norm `∫ |∂ᵢφ|²`.
  have step1 : ∀ i : Fin 3,
      ‖weakGradient (hmem.toLp φ)
          (sobolevH2_le_sobolevH1 (smooth_compactSupport_memSobolevH2 φ hφ hsupp hmem)) i‖ ^ 2
        = ∫ x, ‖fderiv ℝ φ x (EuclideanSpace.single i 1)‖ ^ 2 := by
    intro i
    have hwg : weakGradient (hmem.toLp φ)
        (sobolevH2_le_sobolevH1 (smooth_compactSupport_memSobolevH2 φ hφ hsupp hmem)) i
          = (memLp_partialDeriv φ i hφ hsupp).toLp
            (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
      apply hasWeakDerivative_unique (hmem.toLp φ) i
      · exact weakGradient_spec _ _ i
      · exact hasWeakDerivative_of_smooth_compactSupport φ hφ hsupp hmem
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
        (sobolevH2_le_sobolevH1 (smooth_compactSupport_memSobolevH2 φ hφ hsupp hmem)) i
      = (memLp_partialDeriv φ i hφ hsupp).toLp
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
  apply hasWeakDerivative_unique (hmem.toLp φ) i
  · exact weakGradient_spec _ _ i
  · exact hasWeakDerivative_of_smooth_compactSupport φ hφ hsupp hmem
      (memLp_partialDeriv φ i hφ hsupp)

/-- **Per-approximant Hardy bound.** For smooth compactly supported `φ`, Hardy holds
    for its `L²` class: `hardyIntegral (toLp φ) ≤ 4 · gradientNormSq (toLp φ)`. Combines
    the two bridge lemmas with `hardy_inequality_smooth`. -/
lemma hardyIntegral_toLp_le {φ : R3 → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) (hmem : MemLp φ 2 volume) :
    hardyIntegral (hmem.toLp φ) ≤ 4 * gradientNormSq (hmem.toLp φ)
        (sobolevH2_le_sobolevH1 (smooth_compactSupport_memSobolevH2 φ hφ hsupp hmem)) := by
  rw [hardyIntegral_toLp hmem, gradientNormSq_toLp hφ hsupp hmem]
  exact hardy_inequality_smooth φ hφ hsupp

/-- **Fatou bound (lower semicontinuity).** For `ψ ∈ H¹`, the `ℝ≥0∞`-valued Hardy
    integral is bounded by `4·gradientNormSq ψ`. This is the heart of the H¹ Hardy
    inequality: smooth approximants `φₙ → ψ` (Meyers–Serrin), their gradient norms
    converge, an a.e.-convergent subsequence exists, and Fatou's lemma transfers the
    smooth bound to the limit. The real-valued Hardy inequality and integrability of
    the Hardy integrand are both corollaries. -/
private lemma hardy_lintegral_le (ψ : l2R3) (hψ : MemSobolevH1 ψ) :
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
      (sobolevH2_le_sobolevH1 (smooth_compactSupport_memSobolevH2 (φ n) (hφ n) (hsupp n) (hmem n)))
        = ∑ i : Fin 3, ‖(memLp_partialDeriv (φ n) i (hφ n) (hsupp n)).toLp
            (fun x => fderiv ℝ (φ n) x (EuclideanSpace.single i 1))‖ ^ 2 := by
    intro n
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [weakGradient_toLp_eq (hφ n) (hsupp n) (hmem n) i]
  have htend_B : Tendsto (fun n => gradientNormSq ((hmem n).toLp (φ n))
      (sobolevH2_le_sobolevH1
        (smooth_compactSupport_memSobolevH2 (φ n) (hφ n) (hsupp n) (hmem n)))) atTop
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
    rw [show (fun n => eLpNorm
          ((fun x => ((hmem n).toLp (φ n) : R3 → ℂ) x) - (ψ : R3 → ℂ)) 2 volume)
          = (fun n => ENNReal.ofReal ‖ψ - (hmem n).toLp (φ n)‖) from funext heq]
    rw [show (0 : ℝ≥0∞) = ENNReal.ofReal 0 from (ENNReal.ofReal_zero).symm]
    exact (ENNReal.continuous_ofReal.tendsto 0).comp hnorm_tend
  obtain ⟨ns, hns_mono, hns_ae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (μ := volume) (two_ne_zero)
      (fun n => Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable ψ)
      heLp_tend).exists_seq_tendsto_ae
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
          (sobolevH2_le_sobolevH1 (smooth_compactSupport_memSobolevH2 (φ (ns i)) (hφ (ns i))
            (hsupp (ns i)) (hmem (ns i)))))) atTop := by
        refine Filter.liminf_le_liminf (Filter.Eventually.of_forall fun i => ?_)
        rw [hlin_eq (ns i)]
        exact ENNReal.ofReal_le_ofReal
          (hardyIntegral_toLp_le (hφ (ns i)) (hsupp (ns i)) (hmem (ns i)))
    _ = ENNReal.ofReal (4 * gradientNormSq ψ hψ) := by
        refine Filter.Tendsto.liminf_eq ?_
        exact (ENNReal.continuous_ofReal.tendsto _).comp
          ((htend_B.comp hns_mono.tendsto_atTop).const_mul 4)

/-- `∫ |ψ|²/|x|²` is integrable for `ψ ∈ H¹`: the integrand is nonnegative and
    measurable, and the Fatou bound `hardy_lintegral_le` makes its `∫⁻` finite. -/
lemma inverseRSq_mul_sq_integrable
    (ψ : l2R3) (hψ : MemSobolevH1 ψ) :
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
    (ψ : l2R3) (hψ : MemSobolevH1 ψ) :
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
    (ψ : l2R3) (hψ : MemSobolevH1 ψ) :
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
    (ψ : l2R3) (hψ : MemSobolevH2 ψ) :
    hardyIntegral ψ ≤
    4 * (inner (𝕜 := ℂ) (weakLaplacian ψ hψ) ψ).re := by
  calc hardyIntegral ψ
      ≤ 4 * gradientNormSq ψ (sobolevH2_le_sobolevH1 hψ) :=
        hardy_inequality ψ (sobolevH2_le_sobolevH1 hψ)
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
    ∀ (ψ : l2R3) (hψ : MemSobolevH2 ψ),
      Real.sqrt (hardyIntegral ψ) ≤
      ε * ‖weakLaplacian ψ hψ‖ + C * ‖ψ‖ := by
  refine ⟨ε⁻¹, le_of_lt (inv_pos.mpr hε), fun ψ hψ => ?_⟩
  set A := ‖weakLaplacian ψ hψ‖ with _hA_def
  set B := ‖ψ‖ with _hB_def
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
    ∀ (ψ : l2R3) (hψ : MemSobolevH2 ψ),
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
