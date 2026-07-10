/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Sobolev.Mollification

/-!
# Shared helpers for the Meyers-Serrin approximation

The single-direction (`MeyersSerrin`) and multi-direction (`MeyersMulti`) truncation arguments
share three cutoff/truncation helper lemmas, and — since both are really the same construction
run over a different index set — the truncation construction itself. They are collected here so
both files can import them rather than each carrying its own copy.

## Main results

* `L2_tail_small`: for `f : (l2Rn d)` and `ε > 0`, there is a radius `R` such that multiplying `f`
  by `1 - χ` for *any* cutoff `χ` that is `1` on `closedBall 0 R` and valued in `[0, 1]` leaves
  L² mass below `ε` — i.e. the tail of `f` outside a large enough ball is negligible.
* `hasWeakDerivative_smul_smooth`: the Leibniz rule for weak derivatives — if `g` has weak
  derivative `dg` in direction `i` and `χ` is smooth with compact support, then `χ · g` has weak
  derivative `χ · dg + g · ∂ᵢχ`.
* `exists_smooth_cutoff_scaled`: a family of smooth cutoffs `χ_R`, one for every `R > 0`, that
  are `1` on `closedBall 0 R`, supported in `closedBall 0 (2R)`, and whose derivative is bounded
  by `M / R` for a single constant `M` independent of `R`.
* `truncation_approx_family`: the shared cutoff-truncation construction itself, parametrized by
  an arbitrary nonempty `Finite` index `ι` of directions. Truncates `f` (once, shared across all
  directions) and, for every `j : ι`, a weak derivative `dg j` in direction `dir j`, using a
  single common cutoff. `MeyersSerrin.lean`'s `truncation_approx` (`ι := Unit`) and
  `MeyersMulti.lean`'s `truncation_approx_multi` (`ι := Fin d`, `dir := id`) are both thin
  wrappers around this one lemma, so the construction is proved exactly once.

## Implementation notes

The truncation strategy shared by `MeyersSerrin` and `MeyersMulti` is: given `f` (and its weak
derivative(s)), pick `R` large enough that (a) `L2_tail_small` makes the tails of `f` and its
derivatives negligible and (b) the cross-term `(M / R) · ‖f‖` coming from the cutoff's derivative
bound (`exists_smooth_cutoff_scaled`) is also negligible, then multiply by `χ_R` and apply
`hasWeakDerivative_smul_smooth` to get a compactly supported truncation with controlled weak
derivative. `truncation_approx_family` carries this out once, generically in the index set `ι`;
the single- and multi-direction call sites differ only in how many L²-tail radii need to be
gathered into the max defining `R` (via `Finset.sup'`), not in the underlying argument. This
truncation is the first of the two steps (truncate, then mollify) that make up the Meyers-Serrin
approximation; the second step lives in `Mollification.lean`.

## References

* [Meyers, Serrin, *H = W*][meyers1964]
* [Adams, Fournier, *Sobolev Spaces*][adams2003]
-/

open MeasureTheory
open scoped Pointwise ContDiff

namespace Spectra.Sobolev

variable {d : ℕ}

/-- L² mass on the complement of large balls vanishes.
    Proof avoids dominated convergence by using density of C_c in L². -/
lemma L2_tail_small (f : (l2Rn d)) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ (χ : Rn d → ℝ),
      (∀ x ∈ Metric.closedBall (0 : Rn d) R, χ x = 1) →
      (∀ x, χ x ∈ Set.Icc 0 1) →
      eLpNorm (fun x => (1 - (χ x : ℂ)) * (f : Rn d → ℂ) x) 2 volume
        < ENNReal.ofReal ε := by
  -- Approximate f by continuous compactly supported φ within ε
  obtain ⟨g₁, hg₁_dist, φ, _hcont, hsupp, hae⟩ :=
    Metric.dense_iff.mp dense_continuous_compactSupport_L2 f ε hε
  -- φ has compact support ⊆ some ball
  obtain ⟨R₀, hball⟩ := hsupp.isCompact.isBounded.subset_closedBall (0 : Rn d)
  refine ⟨max R₀ 1, lt_max_of_lt_right one_pos, fun χ hχ_one hχ_bound => ?_⟩
  have hball' : tsupport φ ⊆ Metric.closedBall (0 : Rn d) (max R₀ 1) :=
    hball.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  -- Key: (1-χ)φ = 0 everywhere (χ=1 in ball, φ=0 outside support)
  have hzero : ∀ x, (1 - (χ x : ℂ)) * φ x = 0 := by
    intro x
    by_cases hx : x ∈ Metric.closedBall (0 : Rn d) (max R₀ 1)
    · rw [hχ_one x hx, Complex.ofReal_one, sub_self, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hball' h)), mul_zero]
  -- (1-χ)f =ᵐ (1-χ)(f - g₁) since (1-χ)g₁ =ᵐ (1-χ)φ = 0
  have hae_eq : (fun x => (1 - (χ x : ℂ)) * (f : Rn d → ℂ) x) =ᵐ[volume]
      fun x => (1 - (χ x : ℂ)) * ((f : Rn d → ℂ) x - (g₁ : Rn d → ℂ) x) := by
    filter_upwards [hae] with x hx
    have hg₁x : (1 - (χ x : ℂ)) * (g₁ : Rn d → ℂ) x = 0 := by rw [hx]; exact hzero x
    rw [mul_sub, hg₁x, sub_zero]
  -- Pointwise: ‖(1-χ)(f-g₁)‖ ≤ ‖f-g₁‖ since ‖1-χ‖ ≤ 1
  have hbound : ∀ᵐ x ∂volume,
      ‖(fun x => (1 - (χ x : ℂ)) * ((f : Rn d → ℂ) x - (g₁ : Rn d → ℂ) x)) x‖ ≤
      ‖(f : Rn d → ℂ) x - (g₁ : Rn d → ℂ) x‖ :=
    ae_of_all _ fun x => by
      simp only; rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (by
        rw [show (1 : ℂ) - (χ x : ℂ) = ((1 - χ x : ℝ) : ℂ) from by push_cast; ring,
            Complex.norm_real, Real.norm_of_nonneg (by grind only [= Set.mem_Icc])]
        grind only [= Set.mem_Icc])
  -- Chain: eLpNorm((1-χ)f) = eLpNorm((1-χ)(f-g₁)) ≤ eLpNorm(f-g₁) < ε
  have h_ne_top : eLpNorm ((f - g₁ : (l2Rn d)) : Rn d → ℂ) 2 volume ≠ ⊤ :=
    (Lp.memLp (f - g₁)).eLpNorm_ne_top
  calc eLpNorm (fun x => (1 - (χ x : ℂ)) * (f : Rn d → ℂ) x) 2 volume
      = eLpNorm (fun x => (1 - (χ x : ℂ)) * ((f : Rn d → ℂ) x - (g₁ : Rn d → ℂ) x))
          2 volume := eLpNorm_congr_ae hae_eq
    _ ≤ eLpNorm (fun x => (f : Rn d → ℂ) x - (g₁ : Rn d → ℂ) x) 2 volume :=
        eLpNorm_mono_ae hbound
    _ = eLpNorm ((f - g₁ : (l2Rn d)) : Rn d → ℂ) 2 volume :=
        eLpNorm_congr_ae (Lp.coeFn_sub f g₁).symm
    _ < ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_toReal h_ne_top]
        exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by
          rw [← Lp.norm_def, ← dist_eq_norm]
          exact Metric.mem_ball'.mp hg₁_dist)

/-- Weak derivative product rule with smooth multiplier.
    If g has weak derivative dg and χ is smooth, then χ·g has weak
    derivative χ·dg + g·∂ᵢχ. Discharge: expand the test function
    integral, use Leibniz rule on χ·φ. -/
lemma hasWeakDerivative_smul_smooth
    (g : (l2Rn d)) (i : Fin d) (dg : (l2Rn d))
    (h_dg : HasWeakDerivative g i dg)
    (χ : Rn d → ℝ) (hχ_smooth : ContDiff ℝ ∞ χ) (hχ_supp : HasCompactSupport χ)
    (g_trunc dg_trunc : (l2Rn d))
    (hg_ae : (g_trunc : Rn d → ℂ) =ᵐ[volume] fun x => (χ x : ℂ) * (g : Rn d → ℂ) x)
    (hdg_ae : (dg_trunc : Rn d → ℂ) =ᵐ[volume] fun x =>
      (χ x : ℂ) * (dg : Rn d → ℂ) x +
      (g : Rn d → ℂ) x * fderiv ℝ (fun y => (χ y : ℂ)) x (EuclideanSpace.single i 1)) :
    HasWeakDerivative g_trunc i dg_trunc := by
  intro φ hφ hsupp_φ
  set eᵢ := EuclideanSpace.single i (1 : ℝ)
  set χC : Rn d → ℂ := fun y => (χ y : ℂ) with _hχC_def
  have hχC : ContDiff ℝ ∞ χC := Complex.ofRealCLM.contDiff.comp hχ_smooth
  have hχC_supp : HasCompactSupport χC := hχ_supp.comp_left Complex.ofReal_zero
  -- χ · φ is smooth compactly supported — a valid test function
  have hχφ_s : ContDiff ℝ ∞ (fun x => χC x * φ x) := hχC.mul hφ
  have hχφ_c : HasCompactSupport (fun x => χC x * φ x) := hχC_supp.mul_right
  -- Leibniz rule: ∂ᵢ(χ·φ) = (∂ᵢχ)·φ + χ·(∂ᵢφ)
  have leibniz : ∀ x, fderiv ℝ (fun y => χC y * φ y) x eᵢ =
      fderiv ℝ χC x eᵢ * φ x + χC x * fderiv ℝ φ x eᵢ := by
    intro x
    have h1 : DifferentiableAt ℝ χC x :=
      (hχC.differentiable (by exact_mod_cast ENat.top_ne_zero)).differentiableAt
    have h2 : DifferentiableAt ℝ φ x :=
      (hφ.differentiable (by exact_mod_cast ENat.top_ne_zero)).differentiableAt
    simp only [show (fun y => χC y * φ y) = χC * φ from funext fun _ => rfl]
    rw [fderiv_mul h1 h2, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]; ring_nf
  -- Apply the weak derivative of g to the test function χ · φ
  have h_test := h_dg (fun x => χC x * φ x) hχφ_s hχφ_c
  -- Integrability of all four integral terms (Hölder: L² × L² → L¹)
  have hint_lhs : Integrable (fun x => (g_trunc : Rn d → ℂ) x *
      fderiv ℝ φ x eᵢ) volume :=
    (Lp.memLp g_trunc).integrable_mul (memLp_partialDeriv φ i hφ hsupp_φ)
  have hint_rhs : Integrable (fun x => (dg_trunc : Rn d → ℂ) x * φ x) volume :=
    (Lp.memLp dg_trunc).integrable_mul (memLp_of_smooth_compactSupport φ hφ hsupp_φ)
  have hint_l : Integrable (fun x => (g : Rn d → ℂ) x *
      fderiv ℝ (fun y => χC y * φ y) x eᵢ) volume :=
    (Lp.memLp g).integrable_mul (memLp_of_smooth_compactSupport _
      (contDiff_partialDeriv _ i hχφ_s) (hasCompactSupport_partialDeriv _ i hχφ_c))
  have hint_r : Integrable (fun x => (dg : Rn d → ℂ) x * (χC x * φ x)) volume :=
    (Lp.memLp dg).integrable_mul (memLp_of_smooth_compactSupport _ hχφ_s hχφ_c)
  -- Reduce goal (A = -B) to (A + B = 0)
  apply eq_neg_of_add_eq_zero_left
  -- Strategy: merge into one integral, ae-rewrite integrands via
  -- hg_ae + hdg_ae + Leibniz (ring closes the pointwise identity),
  -- then split back and close with h_test.
  trans ∫ x, ((g : Rn d → ℂ) x * fderiv ℝ (fun y => χC y * φ y) x eᵢ +
              (dg : Rn d → ℂ) x * (χC x * φ x))
  · -- ∫(g_trunc·∂ᵢφ + dg_trunc·φ) =ᵃᵉ ∫(g·∂ᵢ(χφ) + dg·(χφ))
    rw [← integral_add hint_lhs hint_rhs]
    exact integral_congr_ae (by
      filter_upwards [hg_ae, hdg_ae] with x hx1 hx2
      rw [hx1, hx2, leibniz]; ring)
  · -- ∫ g·∂ᵢ(χφ) + ∫ dg·(χφ) = 0  by h_test
    rw [integral_add hint_l hint_r]
    linear_combination h_test

/-- A scaled smooth cutoff with explicit derivative bound `M/R`,
where `M ≥ 0` is a constant independent of `R`. Used in the truncation step
of Meyers-Serrin to control the Leibniz cross-term `g · ∂ᵢχ` uniformly as
`R → ∞`. The bound is achieved by taking `χ_R(x) := ρ(R⁻¹ • x)` for a fixed
unit-scale bump `ρ`; the chain rule then gives `‖fderiv χ_R‖ ≤ ‖fderiv ρ‖_∞ / R`. -/
lemma exists_smooth_cutoff_scaled :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (R : ℝ), 0 < R →
      ∃ (χ : Rn d → ℝ),
        ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        (∀ x ∈ Metric.closedBall (0 : Rn d) R, χ x = 1) ∧
        (∀ x, χ x ∈ Set.Icc 0 1) ∧
        tsupport χ ⊆ Metric.closedBall (0 : Rn d) (2 * R) ∧
        ∀ x, ‖fderiv ℝ χ x‖ ≤ M / R := by
  -- Fixed unit-scale bump: rIn = 1, rOut = 2 at the origin.
  let ρ : ContDiffBump (0 : Rn d) := ⟨1, 2, one_pos, by norm_num⟩
  have hρ_smooth : ContDiff ℝ ∞ (ρ : Rn d → ℝ) := ρ.contDiff
  have hρ_supp : HasCompactSupport (ρ : Rn d → ℝ) := ρ.hasCompactSupport
  have hρ_tsupp_eq : tsupport (ρ : Rn d → ℝ) = Metric.closedBall (0 : Rn d) 2 :=
    ρ.tsupport_eq
  -- Unit bump's derivative is c.s. and continuous, hence bounded.
  have hρ_d_smooth : ContDiff ℝ ∞ (fderiv ℝ (ρ : Rn d → ℝ)) :=
    (contDiff_infty_iff_fderiv.mp hρ_smooth).2
  have hρ_d_cont : Continuous (fderiv ℝ (ρ : Rn d → ℝ)) := hρ_d_smooth.continuous
  have hρ_d_supp : HasCompactSupport (fderiv ℝ (ρ : Rn d → ℝ)) := hρ_supp.fderiv ℝ
  obtain ⟨M₀, hM₀⟩ := hρ_d_cont.bounded_above_of_compact_support hρ_d_supp
  -- max M₀ 0 ensures nonnegativity unconditionally.
  refine ⟨max M₀ 0, le_max_right _ _, fun R hR => ?_⟩
  refine ⟨fun x => (ρ : Rn d → ℝ) (R⁻¹ • x), ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 1. Smooth (composition with scaling CLM).
  · have h_scale_smooth : ContDiff ℝ ∞ (fun y : (Rn d) => R⁻¹ • y) :=
      (R⁻¹ • ContinuousLinearMap.id ℝ (Rn d)).contDiff
    exact hρ_smooth.comp h_scale_smooth
  -- 2. Compact support.
  · refine HasCompactSupport.intro
      (K := (fun y : (Rn d) => R • y) '' Metric.closedBall (0 : Rn d) 2)
      ((isCompact_closedBall _ _).image (continuous_id.const_smul R)) ?_
    intro x hx
    show (ρ : Rn d → ℝ) (R⁻¹ • x) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    rw [hρ_tsupp_eq] at hmem
    exact hx ⟨R⁻¹ • x, hmem, by simp [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]⟩
  -- 3. χ ≡ 1 on closedBall 0 R.
  · intro x hx
    change (ρ : Rn d → ℝ) (R⁻¹ • x) = 1
    apply ρ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul]
    simp only [norm_inv, Real.norm_eq_abs, abs_of_pos hR]
    calc R⁻¹ * ‖x‖
        ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hR.le)
      _ = 1       := inv_mul_cancel₀ hR.ne'
  -- 4. χ ∈ [0, 1].
  · intro x; exact ⟨ρ.nonneg, ρ.le_one⟩
  -- 5. tsupport χ ⊆ closedBall 0 (2R).
  · apply closure_minimal _ Metric.isClosed_closedBall
    intro y hy
    rw [Function.mem_support] at hy
    have h_in : R⁻¹ • y ∈ tsupport (ρ : Rn d → ℝ) := subset_tsupport _ hy
    rw [hρ_tsupp_eq, Metric.mem_closedBall, dist_zero_right, norm_smul] at h_in
    simp only [norm_inv, Real.norm_eq_abs, abs_of_pos hR] at h_in
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖y‖
        = R * (R⁻¹ * ‖y‖) := by
            rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]
      _ ≤ R * 2 := mul_le_mul_of_nonneg_left h_in hR.le
      _ = 2 * R := by ring
  -- 6. Derivative bound: ‖fderiv χ x‖ ≤ (max M₀ 0) / R.
  · intro x
    -- Chain rule via HasFDerivAt of the scaling CLM.
    have h_scale_hfd : HasFDerivAt (fun y : (Rn d) => R⁻¹ • y)
        (R⁻¹ • ContinuousLinearMap.id ℝ (Rn d)) x :=
      (R⁻¹ • ContinuousLinearMap.id ℝ (Rn d)).hasFDerivAt
    have hρ_diff_at : DifferentiableAt ℝ (ρ : Rn d → ℝ) (R⁻¹ • x) :=
      (hρ_smooth.differentiable
        (by exact_mod_cast ENat.top_ne_zero)).differentiableAt
    have h_χ_hfd : HasFDerivAt (fun y : (Rn d) => (ρ : Rn d → ℝ) (R⁻¹ • y))
        ((fderiv ℝ (ρ : Rn d → ℝ) (R⁻¹ • x)).comp
          (R⁻¹ • ContinuousLinearMap.id ℝ (Rn d))) x :=
      hρ_diff_at.hasFDerivAt.comp x h_scale_hfd
    rw [h_χ_hfd.fderiv]
    have h_op_bound : ‖(fderiv ℝ (ρ : Rn d → ℝ) (R⁻¹ • x)).comp
        (R⁻¹ • ContinuousLinearMap.id ℝ (Rn d))‖ ≤
        ‖fderiv ℝ (ρ : Rn d → ℝ) (R⁻¹ • x)‖ *
          ‖R⁻¹ • ContinuousLinearMap.id ℝ (Rn d)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    have h_σ_norm : ‖R⁻¹ • ContinuousLinearMap.id ℝ (Rn d)‖ ≤ R⁻¹ := by
      rw [norm_smul]
      calc ‖R⁻¹‖ * ‖ContinuousLinearMap.id ℝ (Rn d)‖
          ≤ ‖R⁻¹‖ * 1 :=
            mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
        _ = R⁻¹ := by rw [mul_one, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    calc ‖(fderiv ℝ (ρ : Rn d → ℝ) (R⁻¹ • x)).comp
            (R⁻¹ • ContinuousLinearMap.id ℝ (Rn d))‖
        ≤ ‖fderiv ℝ (ρ : Rn d → ℝ) (R⁻¹ • x)‖ *
            ‖R⁻¹ • ContinuousLinearMap.id ℝ (Rn d)‖ := h_op_bound
      _ ≤ ‖fderiv ℝ (ρ : Rn d → ℝ) (R⁻¹ • x)‖ * R⁻¹ :=
          mul_le_mul_of_nonneg_left h_σ_norm (norm_nonneg _)
      _ ≤ M₀ * R⁻¹ :=
          mul_le_mul_of_nonneg_right (hM₀ _) (inv_nonneg.mpr hR.le)
      _ ≤ max M₀ 0 * R⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.mpr hR.le)
      _ = max M₀ 0 / R := by rw [← div_eq_mul_inv]

/-- **Shared cutoff-truncation construction**, parametrized by an arbitrary nonempty
    `Finite` index `ι` of directions to control simultaneously. Given `f` and, for
    every `j : ι`, a weak derivative `dg j` in direction `dir j`, produces a single
    truncation `h_R` of `f` (shared across all `j`) together with per-`j` truncated
    derivatives `dh_R j`, using one common cutoff `χ` whose radius `R` is chosen large
    enough to simultaneously control the L²-tail of `f`, the L²-tail of every `dg j`,
    and the Leibniz cross-term `(M / R) · ‖f‖` coming from `∂χ`.
    `truncation_approx` (`ι := Unit`) and `truncation_approx_multi` (`ι := Fin d`,
    `dir := id`) both specialize this lemma; it exists so the cutoff/budget argument
    is maintained in exactly one place. -/
lemma truncation_approx_family {ι : Type*} [Finite ι] [Nonempty ι]
    (dir : ι → Fin d) (f : (l2Rn d)) (dg : ι → (l2Rn d))
    (h_dg : ∀ j, HasWeakDerivative f (dir j) (dg j)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (h_R : Rn d → ℂ) (dh_R : ι → Rn d → ℂ)
      (hh : MemLp h_R 2 volume) (hdh : ∀ j, MemLp (dh_R j) 2 volume),
      HasCompactSupport h_R ∧ (∀ j, HasCompactSupport (dh_R j)) ∧
      (∀ j, HasWeakDerivative (hh.toLp h_R) (dir j) ((hdh j).toLp (dh_R j))) ∧
      ‖f - hh.toLp h_R‖ < ε ∧ ∀ j, ‖dg j - (hdh j).toLp (dh_R j)‖ < ε := by
  haveI : Fintype ι := Fintype.ofFinite ι
  have hε4 : 0 < ε / 4 := by linarith
  -- Universal derivative bound M for the cutoff.
  obtain ⟨M, hM_nn, h_cutoff⟩ := exists_smooth_cutoff_scaled
  -- L²-tail bounds: one for f, one for each dg j.
  obtain ⟨R₀, _hR₀_pos, hR₀_tail_f⟩ := L2_tail_small f (ε / 4) hε4
  choose R_dg _hR_dg_pos hR_dg_tail using
    fun j => L2_tail_small (dg j) (ε / 4) hε4
  -- R covers all tails AND makes (M/R)·‖f‖ < ε/4.
  set R := max (max R₀ (Finset.univ.sup' Finset.univ_nonempty R_dg))
                (4 * M * ‖f‖ / ε + 1)
  have hMf_nn : 0 ≤ 4 * M * ‖f‖ / ε :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM_nn) (norm_nonneg _)) hε.le
  have hR_pos : 0 < R := lt_max_of_lt_right (by linarith)
  have hR_ge_R₀ : R₀ ≤ R := le_max_of_le_left (le_max_left _ _)
  have hR_ge_R_dg : ∀ j, R_dg j ≤ R := fun j =>
    le_max_of_le_left (le_max_of_le_right
      (Finset.le_sup' R_dg (Finset.mem_univ j)))
  have hR_cross : (M / R) * ‖f‖ < ε / 4 := by
    have h_le : 4 * M * ‖f‖ / ε + 1 ≤ R := le_max_right _ _
    have h_lt : 4 * M * ‖f‖ / ε < R := by linarith
    have h_ε : 4 * M * ‖f‖ < R * ε := by
      have := (div_lt_iff₀ hε).mp h_lt; linarith
    rw [show (M / R) * ‖f‖ = M * ‖f‖ / R from by ring, div_lt_iff₀ hR_pos]
    linarith
  -- The cutoff (real-valued, single χ for all directions).
  obtain ⟨χ, hχ_smooth, hχ_supp, hχ_one, hχ_bound, _hχ_tsupp, hχ_deriv⟩ :=
    h_cutoff R hR_pos
  -- Complex-valued cutoff and sup bound.
  let χℂ : Rn d → ℂ := fun x => (χ x : ℂ)
  have hχℂ_smooth : ContDiff ℝ ∞ χℂ := Complex.ofRealCLM.contDiff.comp hχ_smooth
  have hχℂ_supp : HasCompactSupport χℂ := hχ_supp.comp_left Complex.ofReal_zero
  have hχℂ_le_one : ∀ x, ‖χℂ x‖ ≤ 1 := by
    intro x
    change ‖((χ x : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h := hχ_bound x
    rw [Set.mem_Icc] at h
    exact abs_le.mpr ⟨by linarith, h.2⟩
  -- Per-direction partial of χℂ: smooth, c.s., uniformly bounded by M/R.
  let dχℂ : ι → Rn d → ℂ :=
    fun j x => fderiv ℝ χℂ x (EuclideanSpace.single (dir j) 1)
  have hdχℂ_smooth : ∀ j, ContDiff ℝ ∞ (dχℂ j) :=
    fun j => contDiff_partialDeriv χℂ (dir j) hχℂ_smooth
  have hdχℂ_supp : ∀ j, HasCompactSupport (dχℂ j) :=
    fun j => hasCompactSupport_partialDeriv χℂ (dir j) hχℂ_supp
  have hdχℂ_bound : ∀ j x, ‖dχℂ j x‖ ≤ M / R := by
    intro j x
    change ‖fderiv ℝ χℂ x (EuclideanSpace.single (dir j) 1)‖ ≤ M / R
    have hχ_diff_at : DifferentiableAt ℝ χ x :=
      (hχ_smooth.differentiable
        (by exact_mod_cast ENat.top_ne_zero)).differentiableAt
    rw [show (χℂ : Rn d → ℂ) = Complex.ofRealCLM ∘ χ from rfl,
        fderiv_comp x Complex.ofRealCLM.differentiableAt hχ_diff_at]
    rw [ContinuousLinearMap.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    change ‖((fderiv ℝ χ x (EuclideanSpace.single (dir j) 1) : ℝ) : ℂ)‖ ≤ M / R
    rw [Complex.norm_real]
    calc ‖fderiv ℝ χ x (EuclideanSpace.single (dir j) 1)‖
        ≤ ‖fderiv ℝ χ x‖ * ‖EuclideanSpace.single (dir j) (1 : ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (M / R) * 1 := by
          gcongr
          · exact hχ_deriv x
          · simp [PiLp.norm_single]
      _ = M / R := mul_one _
  -- Truncated bare functions: h_R universal, dh_R j per direction.
  let h_R : Rn d → ℂ := fun x => χℂ x * (f : Rn d → ℂ) x
  let dh_R : ι → Rn d → ℂ :=
    fun j x => χℂ x * (dg j : Rn d → ℂ) x + (f : Rn d → ℂ) x * dχℂ j x
  have h_f_meas : AEStronglyMeasurable (f : Rn d → ℂ) volume :=
    (Lp.memLp f).aestronglyMeasurable
  have h_dg_meas : ∀ j, AEStronglyMeasurable (dg j : Rn d → ℂ) volume :=
    fun j => (Lp.memLp (dg j)).aestronglyMeasurable
  -- MemLp h_R via |h_R| ≤ |f|.
  have hh_R_MemLp : MemLp h_R 2 volume := by
    refine ⟨hχℂ_smooth.continuous.aestronglyMeasurable.mul h_f_meas, ?_⟩
    refine lt_of_le_of_lt (eLpNorm_mono_ae ?_) (Lp.memLp f).eLpNorm_lt_top
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχℂ_le_one x)
  -- Per-j MemLp for χ·(dg j).
  have h_χdg_MemLp : ∀ j, MemLp (fun x => χℂ x * (dg j : Rn d → ℂ) x) 2 volume := by
    intro j
    refine ⟨hχℂ_smooth.continuous.aestronglyMeasurable.mul (h_dg_meas j), ?_⟩
    refine lt_of_le_of_lt (eLpNorm_mono_ae ?_) (Lp.memLp (dg j)).eLpNorm_lt_top
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχℂ_le_one x)
  have hMR_nn : 0 ≤ M / R := div_nonneg hM_nn hR_pos.le
  -- Pointwise: ‖f · dχℂ j‖ ≤ ‖(M/R) • f‖, uniformly in j.
  have h_fdχ_ptw : ∀ j x, ‖(f : Rn d → ℂ) x * dχℂ j x‖ ≤
      ‖(M / R : ℝ) • (f : Rn d → ℂ) x‖ := by
    intro j x
    rw [Complex.real_smul, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hMR_nn,
        mul_comm ‖(f : Rn d → ℂ) x‖ ‖dχℂ j x‖]
    exact mul_le_mul_of_nonneg_right (hdχℂ_bound j x) (norm_nonneg _)
  -- Per-j MemLp for f · dχℂ j.
  have h_fdχ_MemLp : ∀ j, MemLp (fun x => (f : Rn d → ℂ) x * dχℂ j x) 2 volume := by
    intro j
    refine ⟨h_f_meas.mul (hdχℂ_smooth j).continuous.aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt
      (eLpNorm_mono_ae (Filter.Eventually.of_forall (h_fdχ_ptw j))) ?_
    rw [show (fun x => (M / R : ℝ) • (f : Rn d → ℂ) x)
          = (M / R : ℝ) • ((f : Rn d → ℂ)) from rfl]
    rw [eLpNorm_const_smul]
    exact ENNReal.mul_lt_top enorm_lt_top (Lp.memLp f).eLpNorm_lt_top
  have hdh_R_MemLp : ∀ j, MemLp (dh_R j) 2 volume :=
    fun j => (h_χdg_MemLp j).add (h_fdχ_MemLp j)
  -- Compact supports.
  have hh_R_supp : HasCompactSupport h_R := hχℂ_supp.mul_right
  have hdh_R_supp : ∀ j, HasCompactSupport (dh_R j) :=
    fun j => HasCompactSupport.add hχℂ_supp.mul_right (hdχℂ_supp j).mul_left
  -- Per-j weak derivative via hasWeakDerivative_smul_smooth.
  have h_wkd : ∀ j, HasWeakDerivative (hh_R_MemLp.toLp h_R) (dir j)
      ((hdh_R_MemLp j).toLp (dh_R j)) := fun j =>
    hasWeakDerivative_smul_smooth f (dir j) (dg j) (h_dg j)
      χ hχ_smooth hχ_supp
      (hh_R_MemLp.toLp h_R) ((hdh_R_MemLp j).toLp (dh_R j))
      hh_R_MemLp.coeFn_toLp (hdh_R_MemLp j).coeFn_toLp
  refine ⟨h_R, dh_R, hh_R_MemLp, hdh_R_MemLp,
    hh_R_supp, hdh_R_supp, h_wkd, ?_, ?_⟩
  -- Norm bound 1: ‖f - h_R_Lp‖ < ε.
  · rw [Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_sub _ _)]
    have hae : ((f : Rn d → ℂ) - (hh_R_MemLp.toLp h_R : Rn d → ℂ)) =ᵐ[volume]
        fun x => (1 - (χ x : ℂ)) * (f : Rn d → ℂ) x := by
      filter_upwards [hh_R_MemLp.coeFn_toLp] with x hx
      change (f : Rn d → ℂ) x - (hh_R_MemLp.toLp h_R : Rn d → ℂ) x = _
      rw [hx]
      change (f : Rn d → ℂ) x - χℂ x * (f : Rn d → ℂ) x =
        (1 - (χ x : ℂ)) * (f : Rn d → ℂ) x
      ring
    rw [eLpNorm_congr_ae hae]
    have h_bound :
        eLpNorm (fun x => (1 - (χ x : ℂ)) * (f : Rn d → ℂ) x) 2 volume
          < ENNReal.ofReal (ε / 4) :=
      hR₀_tail_f χ
        (fun x hx => hχ_one x (Metric.closedBall_subset_closedBall hR_ge_R₀ hx))
        hχ_bound
    have h_ne :
        eLpNorm (fun x => (1 - (χ x : ℂ)) * (f : Rn d → ℂ) x) 2 volume ≠ ⊤ :=
      ne_top_of_lt h_bound
    calc (eLpNorm (fun x => (1 - (χ x : ℂ)) * (f : Rn d → ℂ) x) 2 volume).toReal
        < (ENNReal.ofReal (ε / 4)).toReal :=
          (ENNReal.toReal_lt_toReal h_ne ENNReal.ofReal_ne_top).mpr h_bound
      _ = ε / 4 := ENNReal.toReal_ofReal hε4.le
      _ < ε := by linarith
  -- Norm bound 2: ∀ j, ‖dg j - dh_R_j_Lp‖ < ε.
  · intro j
    rw [Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_sub _ _)]
    have hae : ((dg j : Rn d → ℂ) - ((hdh_R_MemLp j).toLp (dh_R j) : Rn d → ℂ))
        =ᵐ[volume]
        fun x => (1 - (χ x : ℂ)) * (dg j : Rn d → ℂ) x -
          (f : Rn d → ℂ) x * dχℂ j x := by
      filter_upwards [(hdh_R_MemLp j).coeFn_toLp] with x hx
      change (dg j : Rn d → ℂ) x -
            ((hdh_R_MemLp j).toLp (dh_R j) : Rn d → ℂ) x = _
      rw [hx]
      change (dg j : Rn d → ℂ) x -
            (χℂ x * (dg j : Rn d → ℂ) x + (f : Rn d → ℂ) x * dχℂ j x) =
        (1 - (χ x : ℂ)) * (dg j : Rn d → ℂ) x - (f : Rn d → ℂ) x * dχℂ j x
      ring
    rw [eLpNorm_congr_ae hae]
    have h_meas1 : AEStronglyMeasurable
        (fun x => (1 - (χ x : ℂ)) * (dg j : Rn d → ℂ) x) volume :=
      (continuous_const.sub hχℂ_smooth.continuous).aestronglyMeasurable.mul
        (h_dg_meas j)
    have h_meas2 : AEStronglyMeasurable
        (fun x => (f : Rn d → ℂ) x * dχℂ j x) volume :=
      h_f_meas.mul (hdχℂ_smooth j).continuous.aestronglyMeasurable
    have hp_one_le_two : (1 : ENNReal) ≤ 2 := by norm_num
    have h_triangle : eLpNorm
        (fun x => (1 - (χ x : ℂ)) * (dg j : Rn d → ℂ) x -
          (f : Rn d → ℂ) x * dχℂ j x) 2 volume ≤
        eLpNorm (fun x => (1 - (χ x : ℂ)) * (dg j : Rn d → ℂ) x) 2 volume +
        eLpNorm (fun x => (f : Rn d → ℂ) x * dχℂ j x) 2 volume :=
      eLpNorm_sub_le h_meas1 h_meas2 hp_one_le_two
    have h_bound1 :
        eLpNorm (fun x => (1 - (χ x : ℂ)) * (dg j : Rn d → ℂ) x) 2 volume
          < ENNReal.ofReal (ε / 4) :=
      hR_dg_tail j χ
        (fun x hx => hχ_one x
          (Metric.closedBall_subset_closedBall (hR_ge_R_dg j) hx))
        hχ_bound
    have h_eLpNorm_f_eq :
        eLpNorm (f : Rn d → ℂ) 2 volume = ENNReal.ofReal ‖f‖ := by
      rw [Lp.norm_def]
      exact (ENNReal.ofReal_toReal (Lp.memLp f).eLpNorm_ne_top).symm
    have h_bound2 :
        eLpNorm (fun x => (f : Rn d → ℂ) x * dχℂ j x) 2 volume
          ≤ ENNReal.ofReal (ε / 4) := by
      have h_le :
          eLpNorm (fun x => (f : Rn d → ℂ) x * dχℂ j x) 2 volume ≤
          ENNReal.ofReal ((M / R) * ‖f‖) := by
        calc eLpNorm (fun x => (f : Rn d → ℂ) x * dχℂ j x) 2 volume
            ≤ eLpNorm (fun x => (M / R : ℝ) • (f : Rn d → ℂ) x) 2 volume :=
              eLpNorm_mono_ae (Filter.Eventually.of_forall (h_fdχ_ptw j))
          _ = ‖(M / R : ℝ)‖ₑ * eLpNorm (f : Rn d → ℂ) 2 volume := by
              rw [show (fun x => (M / R : ℝ) • (f : Rn d → ℂ) x)
                    = (M / R : ℝ) • ((f : Rn d → ℂ)) from rfl]
              rw [eLpNorm_const_smul]
          _ = ENNReal.ofReal (M / R) * ENNReal.ofReal ‖f‖ := by
              rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hMR_nn,
                  h_eLpNorm_f_eq]
          _ = ENNReal.ofReal ((M / R) * ‖f‖) :=
              (ENNReal.ofReal_mul hMR_nn).symm
      exact le_of_lt
        (lt_of_le_of_lt h_le ((ENNReal.ofReal_lt_ofReal_iff hε4).mpr hR_cross))
    have h_sum_bound : eLpNorm
        (fun x => (1 - (χ x : ℂ)) * (dg j : Rn d → ℂ) x -
          (f : Rn d → ℂ) x * dχℂ j x) 2 volume
          ≤ ENNReal.ofReal (ε / 2) := by
      calc eLpNorm
            (fun x => (1 - (χ x : ℂ)) * (dg j : Rn d → ℂ) x -
              (f : Rn d → ℂ) x * dχℂ j x) 2 volume
          ≤ eLpNorm (fun x => (1 - (χ x : ℂ)) * (dg j : Rn d → ℂ) x) 2 volume +
            eLpNorm (fun x => (f : Rn d → ℂ) x * dχℂ j x) 2 volume := h_triangle
        _ ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
              add_le_add h_bound1.le h_bound2
        _ = ENNReal.ofReal (ε / 2) := by
              rw [← ENNReal.ofReal_add hε4.le hε4.le]; congr 1; ring
    have h_ne : eLpNorm
        (fun x => (1 - (χ x : ℂ)) * (dg j : Rn d → ℂ) x -
          (f : Rn d → ℂ) x * dχℂ j x) 2 volume ≠ ⊤ :=
      (lt_of_le_of_lt h_sum_bound ENNReal.ofReal_lt_top).ne
    calc (eLpNorm
            (fun x => (1 - (χ x : ℂ)) * (dg j : Rn d → ℂ) x -
              (f : Rn d → ℂ) x * dχℂ j x) 2 volume).toReal
        ≤ (ENNReal.ofReal (ε / 2)).toReal :=
          (ENNReal.toReal_le_toReal h_ne ENNReal.ofReal_ne_top).mpr h_sum_bound
      _ = ε / 2 := ENNReal.toReal_ofReal (by linarith)
      _ < ε := by linarith

end Spectra.Sobolev
