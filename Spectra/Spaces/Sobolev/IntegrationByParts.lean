/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
File: Spectra/Spaces/Sobolev/IntegrationByParts.lean
-/
import Spectra.Spaces.Sobolev.MeyersSerrin

open MeasureTheory Complex
open scoped ContDiff

namespace Spectra.Sobolev

/-- Distribute inner product over a finite sum in the first argument. -/
private lemma inner_finset_sum_left {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → L2_R3) (y : L2_R3) :
    @inner ℂ L2_R3 _ (∑ i ∈ s, f i) y =
    ∑ i ∈ s, @inner ℂ L2_R3 _ (f i) y := by
  induction s using Finset.induction_on with
  | empty => simp [inner_zero_left]
  | insert _ _ ha ih =>
    rw [Finset.sum_insert ha, inner_add_left, ih, Finset.sum_insert ha]

/-- **Smooth IBP identity**: ⟨∂ᵢ(df), φ⟩ + ⟨df, ∂ᵢφ⟩ = 0 for smooth c.s. φ -/
private lemma ibp_smooth_test (i : Fin 3) (df ddf : L2_R3)
    (h_ddf : HasWeakDerivative df i ddf)
    (φ : R3 → ℂ) (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) :
    @inner ℂ L2_R3 _ ddf ((memLp_of_smooth_compactSupport φ hφ hsupp).toLp φ) +
    @inner ℂ L2_R3 _ df ((memLp_partialDeriv φ i hφ hsupp).toLp
      (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))) = 0 := by
  set eᵢ := EuclideanSpace.single i (1 : ℝ)
  -- (A) Chain rule: ∂ᵢ(conj ∘ φ) = conj ∘ ∂ᵢφ  (conjCLE is ℝ-linear)
  have h_fderiv_conj : ∀ x, fderiv ℝ (fun y => starRingEnd ℂ (φ y)) x eᵢ =
        starRingEnd ℂ (fderiv ℝ φ x eᵢ) := by
      intro x
      have hd : DifferentiableAt ℝ φ x :=
        (hφ.differentiable (by exact_mod_cast ENat.top_ne_zero)).differentiableAt
      have hrw : (fun y => starRingEnd ℂ (φ y)) = ⇑Complex.conjCLE ∘ φ := rfl
      rw [hrw]
      -- (fderiv ℝ (⇑conjCLE ∘ φ) x) eᵢ = (starRingEnd ℂ) ((fderiv ℝ φ x) eᵢ)
      exact congr_arg (· eᵢ) Complex.conjCLE.comp_fderiv ▸ by
        simp_all only [eᵢ]
  -- (B) Test h_ddf against conj(φ), then substitute ∂ᵢ(conj φ) = conj(∂ᵢφ)
  have h_wk := h_ddf (fun x => starRingEnd ℂ (φ x))
    (contDiff_starRingEnd_comp hφ) (hasCompactSupport_starRingEnd_comp hsupp)
  rw [show (fun x => (df : R3 → ℂ) x *
        fderiv ℝ (fun y => starRingEnd ℂ (φ y)) x eᵢ) =
      (fun x => (df : R3 → ℂ) x *
        starRingEnd ℂ (fderiv ℝ φ x eᵢ)) from
    funext fun x => by rw [h_fderiv_conj]] at h_wk
  -- h_wk : ∫ df · conj(∂ᵢφ) = −∫ ddf · conj(φ)
  -- (C) Integrability for the conjugated integrals
  have hint1 : Integrable (fun x => (ddf : R3 → ℂ) x * starRingEnd ℂ (φ x)) volume :=
    (Lp.memLp ddf).integrable_mul
      (memLp_of_smooth_compactSupport _ (contDiff_starRingEnd_comp hφ)
        (hasCompactSupport_starRingEnd_comp hsupp))
  have hint2 : Integrable (fun x => (df : R3 → ℂ) x *
      starRingEnd ℂ (fderiv ℝ φ x eᵢ)) volume :=
    (Lp.memLp df).integrable_mul
      (memLp_of_smooth_compactSupport _
        (contDiff_starRingEnd_comp (contDiff_partialDeriv φ i hφ))
        (hasCompactSupport_starRingEnd_comp (hasCompactSupport_partialDeriv φ i hsupp)))
  -- (D) Sum to zero — NOTE: each ∫ MUST be parenthesized (the binder is greedy)
  have h_sum_zero : (∫ x, (ddf : R3 → ℂ) x * starRingEnd ℂ (φ x)) +
      (∫ x, (df : R3 → ℂ) x * starRingEnd ℂ (fderiv ℝ φ x eᵢ)) = 0 := by
    linear_combination h_wk
  -- (E) Conjugate: (∫ conj(ddf)·φ) + (∫ conj(df)·∂ᵢφ) = 0
  --     Key identity: conj(a * conj(b)) = conj(a) * b
  have conj_swap : ∀ (a b : ℂ),
      starRingEnd ℂ (a * starRingEnd ℂ b) = starRingEnd ℂ a * b :=
    fun a b => by rw [map_mul, starRingEnd_self_apply]
  have conj_integral : ∀ (f : R3 → ℂ), Integrable f volume →
      (∫ x, starRingEnd ℂ (f x)) = starRingEnd ℂ (∫ x, f x) :=
    fun f hf => (Complex.conjCLE.toContinuousLinearMap.integral_comp_comm hf)
  have h_conj : (∫ x, starRingEnd ℂ ((ddf : R3 → ℂ) x) * φ x) +
      (∫ x, starRingEnd ℂ ((df : R3 → ℂ) x) * fderiv ℝ φ x eᵢ) = 0 := by
    simp_rw [← conj_swap]
    rw [conj_integral _ hint1, conj_integral _ hint2,
        ← map_add, h_sum_zero, map_zero]
  -- (F) Identify with L² inner products
  have h_inner1 : @inner ℂ L2_R3 _ ddf
      ((memLp_of_smooth_compactSupport φ hφ hsupp).toLp φ) =
      ∫ x, starRingEnd ℂ ((ddf : R3 → ℂ) x) * φ x := by
    rw [L2.inner_def]; simp only [RCLike.inner_apply]
    exact integral_congr_ae
      ((memLp_of_smooth_compactSupport φ hφ hsupp).coeFn_toLp.mono
        fun x hx => by simp only [hx]; ring)
  have h_inner2 : @inner ℂ L2_R3 _ df
      ((memLp_partialDeriv φ i hφ hsupp).toLp
        (fun x => fderiv ℝ φ x eᵢ)) =
      ∫ x, starRingEnd ℂ ((df : R3 → ℂ) x) * fderiv ℝ φ x eᵢ := by
    rw [L2.inner_def]; simp only [RCLike.inner_apply]
    exact integral_congr_ae
      ((memLp_partialDeriv φ i hφ hsupp).coeFn_toLp.mono
        fun x hx => by simp only; rw [hx]; ring)
  rw [h_inner1, h_inner2]
  exact h_conj

/-- **Per-component IBP**: ⟨∂ᵢ(df), g⟩ = −⟨df, ∂ᵢg⟩.

    Proof: Meyers-Serrin gives φ close to g in H¹. Smooth IBP gives the
    identity for φ. Cauchy-Schwarz controls the error. -/
private lemma ibp_component (i : Fin 3)
    (df ddf g dg : L2_R3)
    (h_ddf : HasWeakDerivative df i ddf)
    (h_dg : HasWeakDerivative g i dg) :
    @inner ℂ L2_R3 _ ddf g = -@inner ℂ L2_R3 _ df dg := by
  -- Suffices: ⟨ddf, g⟩ + ⟨df, dg⟩ = 0
  apply eq_neg_of_add_eq_zero_left
  by_contra h_ne
  -- The sum has positive norm
  set val := @inner ℂ L2_R3 _ ddf g + @inner ℂ L2_R3 _ df dg
  have h_pos : (0 : ℝ) < ‖val‖ := norm_pos_iff.mpr h_ne
  -- Choose approximation radius
  set C := ‖ddf‖ + ‖df‖ + 1 with hC_def
  have hC_pos : (0 : ℝ) < C := by positivity
  set δ := ‖val‖ / (2 * C) with hδ_def
  have hδ_pos : (0 : ℝ) < δ := div_pos h_pos (by positivity)
  -- Meyers-Serrin: get smooth c.s. φ with ‖g - φ‖ < δ and ‖dg - ∂ᵢφ‖ < δ
  obtain ⟨φ, hφ_s, hφ_c, h_g_close, h_dg_close⟩ :=
    meyers_serrin_approx i g dg h_dg δ hδ_pos
  set φ_L2 := (memLp_of_smooth_compactSupport φ hφ_s hφ_c).toLp φ
  set dφ_L2 := (memLp_partialDeriv φ i hφ_s hφ_c).toLp
    (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))
  -- Smooth IBP: ⟨ddf, φ⟩ + ⟨df, ∂ᵢφ⟩ = 0
  have h_ibp := ibp_smooth_test i df ddf h_ddf φ hφ_s hφ_c
  -- Decompose: val = ⟨ddf, g - φ⟩ + ⟨df, dg - ∂ᵢφ⟩ + 0
  have h_val : val = @inner ℂ L2_R3 _ ddf (g - φ_L2) +
      @inner ℂ L2_R3 _ df (dg - dφ_L2) := by
    show @inner ℂ L2_R3 _ ddf g + @inner ℂ L2_R3 _ df dg =
         @inner ℂ L2_R3 _ ddf (g - φ_L2) + @inner ℂ L2_R3 _ df (dg - dφ_L2)
    rw [inner_sub_right, inner_sub_right]
    linear_combination h_ibp
  -- Cauchy-Schwarz bound
  have h_bound : ‖val‖ ≤ ‖ddf‖ * δ + ‖df‖ * δ := by
    rw [h_val]
    calc ‖@inner ℂ L2_R3 _ ddf (g - φ_L2) +
            @inner ℂ L2_R3 _ df (dg - dφ_L2)‖
        ≤ ‖@inner ℂ L2_R3 _ ddf (g - φ_L2)‖ +
          ‖@inner ℂ L2_R3 _ df (dg - dφ_L2)‖ := norm_add_le _ _
      _ ≤ ‖ddf‖ * ‖g - φ_L2‖ + ‖df‖ * ‖dg - dφ_L2‖ := by
          gcongr <;> exact norm_inner_le_norm _ _
      _ ≤ ‖ddf‖ * δ + ‖df‖ * δ := by
          gcongr
  -- Contradiction: ‖val‖ ≤ (‖ddf‖ + ‖df‖) · δ < C · δ = ‖val‖/2 < ‖val‖
  have : ‖val‖ < ‖val‖ :=
    calc ‖val‖
        ≤ (‖ddf‖ + ‖df‖) * δ := by linarith
      _ < C * δ := by
          exact mul_lt_mul_of_pos_right (by linarith) hδ_pos
      _ = ‖val‖ / 2 := by
          rw [hδ_def, hC_def]; field_simp
      _ < ‖val‖ := half_lt_self h_pos
  exact absurd this (lt_irrefl _)

/-- ### Integration by parts: the fundamental identity -/
lemma integration_by_parts
    (f : L2_R3) (hf : MemSobolevH2 f)
    (g : L2_R3) (hg : MemSobolevH1 g) :
    inner (𝕜 := ℂ) (weakLaplacian f hf) g =
    ∑ i : Fin 3, inner (𝕜 := ℂ) (weakGradient f (sobolevH2_le_H1 hf) i)
                   (weakGradient g hg i) := by
  simp only [weakLaplacian]
  rw [inner_neg_left, inner_finset_sum_left, ← Finset.sum_neg_distrib]
  -- Goal: ∑ i, -(inner ((hf.2 i i).choose) g) = ∑ i, inner (weakGrad f i) (weakGrad g i)
  apply Finset.sum_congr rfl
  intro i _
  -- Extract the second derivative chain: ∃ mid, ∂ᵢf = mid ∧ ∂ᵢ(mid) = ∂ᵢᵢf
  obtain ⟨mid, hmid_first, hmid_second⟩ := (hf.2 i i).choose_spec
  -- By uniqueness: mid = weakGradient f i
  have h_eq : mid = weakGradient f (sobolevH2_le_H1 hf) i :=
    hasWeakDerivative_unique f i mid _ hmid_first
      (weakGradient_spec f (sobolevH2_le_H1 hf) i)
  rw [← h_eq]
  -- Goal: -(inner (∂ᵢᵢf) g) = inner mid (∂ᵢg)
  -- ibp_component gives: inner (∂ᵢᵢf) g = -(inner mid (∂ᵢg))
  exact neg_eq_iff_eq_neg.mpr
    (ibp_component i mid ((hf.2 i i).choose) g (weakGradient g hg i)
      hmid_second (weakGradient_spec g hg i))

/-- **Symmetry of -Δ**: ⟨-Δf, g⟩ = ⟨f, -Δg⟩ for f, g ∈ H². -/
lemma laplacian_symmetric
    (f g : L2_R3) (hf : MemSobolevH2 f) (hg : MemSobolevH2 g) :
    inner (𝕜 := ℂ) (weakLaplacian f hf) g =
    inner (𝕜 := ℂ) f (weakLaplacian g hg) := by
  rw [integration_by_parts f hf g (sobolevH2_le_H1 hg)]
  symm
  calc inner (𝕜 := ℂ) f (weakLaplacian g hg)
      = starRingEnd ℂ (inner (𝕜 := ℂ) (weakLaplacian g hg) f) :=
        (inner_conj_symm f _).symm
    _ = starRingEnd ℂ (∑ i, inner (𝕜 := ℂ) (weakGradient g (sobolevH2_le_H1 hg) i)
            (weakGradient f (sobolevH2_le_H1 hf) i)) := by
        rw [integration_by_parts g hg f (sobolevH2_le_H1 hf)]
    _ = ∑ i, starRingEnd ℂ (inner (𝕜 := ℂ) (weakGradient g (sobolevH2_le_H1 hg) i)
            (weakGradient f (sobolevH2_le_H1 hf) i)) :=
        map_sum _ _ _
    _ = ∑ i, inner (𝕜 := ℂ) (weakGradient f (sobolevH2_le_H1 hf) i)
            (weakGradient g (sobolevH2_le_H1 hg) i) := by
        congr 1; ext i; exact inner_conj_symm _ _

/-- The gradient norm squared equals the Laplacian inner product. -/
lemma gradient_norm_sq_eq_laplacian_inner
    (f : L2_R3) (hf : MemSobolevH2 f) :
    (gradientNormSq f (sobolevH2_le_H1 hf) : ℂ) =
    inner (𝕜 := ℂ) (weakLaplacian f hf) f := by
  rw [integration_by_parts f hf f (sobolevH2_le_H1 hf), gradientNormSq]
  push_cast
  congr 1; ext i
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
  apply ext
  · rfl
  · rfl

/-- **Non-negativity of -Δ**: ⟨-Δf, f⟩ = ‖∇f‖² ≥ 0. -/
lemma laplacian_nonneg (f : L2_R3) (hf : MemSobolevH2 f) :
    0 ≤ (inner (𝕜 := ℂ) (weakLaplacian f hf) f : ℂ).re := by
  rw [← gradient_norm_sq_eq_laplacian_inner]
  simp only [gradientNormSq, Complex.ofReal_re]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- **Skew-symmetry of the weak derivative**: `⟨∂ᵢf, g⟩ = −⟨f, ∂ᵢg⟩` for `f, g ∈ H¹(ℝ³)`.
This is the first-order integration-by-parts identity (no boundary term on `ℝ³`); it is the
reason the momentum operator `-i∂ᵢ` is symmetric. -/
lemma weakGradient_inner_skew (f g : L2_R3) (hf : MemSobolevH1 f) (hg : MemSobolevH1 g)
    (i : Fin 3) :
    inner (𝕜 := ℂ) (weakGradient f hf i) g = -inner (𝕜 := ℂ) f (weakGradient g hg i) :=
  ibp_component i f (weakGradient f hf i) g (weakGradient g hg i)
    (weakGradient_spec f hf i) (weakGradient_spec g hg i)

end Spectra.Sobolev
