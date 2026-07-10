/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Diagonal.IntegralZ.Basic

/-!
# The Resolvent Diagonal: Laplace Representation and Nevanlinna Identity

This file develops the Herglotz/Nevanlinna machinery for the resolvent diagonal
`⟪ξ, R(z)ξ⟫`: its representation as a one-sided Laplace transform of the group
`t ↦ ⟪ξ, U(t)ξ⟫`, the Nevanlinna sign identity `Im ⟪ξ, R(z)ξ⟫ = (Im z)·‖R(z)ξ‖²` that makes
`z ↦ ⟪ξ, R(z)ξ⟫` a Herglotz (Nevanlinna) function, continuity of the resolvent along a
horizontal strip, and the conjugate-symmetry pair relating `R(λ+iε)` to `R(λ-iε)`.

## Main statements

* `resolvent_diag_laplace` — `⟪ξ, R(z)ξ⟫ = (-i) ∫₀^∞ e^{-izt} ⟪ξ, U(t)ξ⟫ dt` for `Im z < 0`.
* `im_resolvent_diag` — the **Nevanlinna identity** `Im ⟪ξ, R(z)ξ⟫ = (Im z)·‖R(z)ξ‖²`.
* `laplace_exp`, `cauchy_kernel_laplace_neg_im` — the scalar Laplace transform of a character
  and its Cauchy-kernel corollary, the model case behind `resolvent_diag_laplace`.
* `resolvent_continuous_at_height` — `λ ↦ R(λ+iε)ξ` is continuous on a horizontal strip.
* `resolvent_diag_lower_laplace`, `resolvent_diag_upper_eq_conj` — the lower-half-plane Laplace
  form and the conjugate-symmetry identity `⟪ξ, R(λ+iε)ξ⟫ = conj ⟪ξ, R(λ-iε)ξ⟫`.

## Implementation notes

`resolvent_diag_laplace` and `resolvent_diag_lower_laplace` are stated for `Im z < 0` (resp.
`Im z = -ε < 0`) because the Laplace integral `∫₀^∞ e^{-izt} f(t) dt` only converges for `z` in
the lower half-plane (the integrand decays as `e^{(Im z)t}`). `im_resolvent_diag` and
`resolvent_continuous_at_height`, by contrast, hold for the general `hz : z.im ≠ 0` split
carried by `resolvent` itself, so they take the full `hsym`/`hplus`/`hminus` hypothesis triple
rather than the group-based `U_grp` package. The upper-half-plane case is recovered from the
lower one via `resolvent_diag_upper_eq_conj`'s conjugate symmetry rather than a second Laplace
computation.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII.4
* [Kato, *Perturbation Theory for Linear Operators*][kato1995], Section V.3
-/

open scoped InnerProductSpace
open Complex MeasureTheory
open Spectra.OneParameterUnitaryGroup
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Resolvent
variable (U_grp : OneParameterUnitaryGroup (H := H))
variable {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
  (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
  (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)

/-- The **resolvent diagonal Laplace representation**: `⟪ξ, R(z)ξ⟫` is `(-i)` times the
Laplace transform of `t ↦ ⟪ξ, U(t)ξ⟫` on `[0,∞)`, valid for `Im z < 0`. -/
lemma resolvent_diag_laplace (ξ : H) {z : ℂ} (hz : z.im < 0) :
    ⟪ξ, resolvent z (ne_of_lt hz)
          (generator_isFormalAdjoint U_grp)
          (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) ξ⟫_ℂ
      = (-I) * ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) * ⟪ξ, U_grp.U t ξ⟫_ℂ := by
  have hint := integrable_expZ_unitary U_grp hz ξ
  rw [← resolventIntegralZ_eq_resolvent U_grp hz ξ, resolventIntegralZ, inner_smul_right]
  congr 1
  rw [← innerSL_apply_apply, ← ContinuousLinearMap.integral_comp_comm (innerSL ℂ ξ) hint]
  refine setIntegral_congr_fun measurableSet_Ici (fun t _ => ?_)
  simp [innerSL_apply_apply]

/-- The **Nevanlinna identity** for the resolvent diagonal:
`Im ⟪ξ, R(z) ξ⟫ = (Im z) · ‖R(z) ξ‖²`. -/
lemma im_resolvent_diag (z : ℂ) (hz : z.im ≠ 0) (ξ : H) :
    (⟪ξ, resolvent z hz hsym hplus hminus ξ⟫_ℂ).im
      = z.im * ‖resolvent z hz hsym hplus hminus ξ‖ ^ 2 := by
  let ψ_sub : A.domain :=
    Classical.choose (self_adjoint_range_all_z hsym hplus hminus z hz ξ).exists
  have hψ_eq : A ψ_sub - z • (ψ_sub : H) = ξ :=
    Classical.choose_spec (self_adjoint_range_all_z hsym hplus hminus z hz ξ).exists
  have hres : resolvent z hz hsym hplus hminus ξ = (ψ_sub : H) := rfl
  rw [hres, ← hψ_eq, inner_sub_left, inner_smul_left]
  have h1 : (⟪A ψ_sub, (ψ_sub : H)⟫_ℂ).im = 0 :=
    inner_self_im_eq_zero_of_symmetric hsym ψ_sub
  have h2im : (⟪(ψ_sub : H), (ψ_sub : H)⟫_ℂ).im = 0 := by
    simpa using inner_self_im (𝕜 := ℂ) (ψ_sub : H)
  have h2re : (⟪(ψ_sub : H), (ψ_sub : H)⟫_ℂ).re = ‖(ψ_sub : H)‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (ψ_sub : H)
  simp only [Complex.sub_im, Complex.mul_im, Complex.conj_re, Complex.conj_im,
             h1, h2im, h2re]
  ring

/-- The **one-sided Laplace transform of a character**:
`∫₀^∞ e^{-izt} e^{iλt} dt = i/(λ - z)`, valid when
`Im(λ - z) > 0` so the integrand decays. -/
lemma laplace_exp {z lambda : ℂ} (h : (lambda - z).im > 0) :
    ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * t)) *
    cexp (I * lambda * t) = I / (lambda - z) := by
  -- (1) Fuse the exponentials: e^{-izt} · e^{iλt} = e^{i(λ-z)t}
  have h_combine : ∀ t : ℝ,
      cexp (-(I * z * (t : ℂ))) * cexp (I * lambda * (t : ℂ)) =
      cexp (I * (lambda - z) * (t : ℂ)) := fun t => by
    rw [← Complex.exp_add]; congr 1; ring
  -- (2) Re(i(λ−z)) = −Im(λ−z) < 0 from the hypothesis
  have ha : (I * (lambda - z)).re < 0 := by
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, zero_sub, neg_lt_zero]
    exact h
  -- (3) Rewrite under the integral, drop the endpoint, apply Mathlib's formula
  simp_rw [h_combine]
  rw [integral_Ici_eq_integral_Ioi, integral_exp_mul_complex_Ioi ha 0]
  -- (4) −1/(i(λ−z)) = i/(λ−z), via i⁻¹ = −i
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div,
    one_div, mul_inv, Complex.inv_I, neg_neg, ← div_eq_mul_inv]

/-- For `w` in the lower half-plane, the **Cauchy kernel's Laplace representation**
`(λ - w)⁻¹ = -i ∫₀^∞ e^{-iwt} e^{iλt} dt`. Direct corollary of `laplace_exp`. -/
lemma cauchy_kernel_laplace_neg_im {w : ℂ} (hw : w.im < 0) (lambda : ℝ) :
    ((lambda : ℂ) - w)⁻¹
      = -I * ∫ t in Set.Ici (0 : ℝ),
          Complex.exp (-(I * w * (t : ℂ))) * Complex.exp (I * (lambda : ℂ) * (t : ℂ)) := by
  have hpos : ((lambda : ℂ) - w).im > 0 := by
    simp only [Complex.sub_im, Complex.ofReal_im]; linarith
  rw [laplace_exp hpos, ← mul_div_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_div]

/-- On the strip `Im z = ε > 0`, `λ ↦ R(⟨λ,ε⟩)ξ` is **continuous** — the proof bounds
`‖R(λ+iε)ξ - R(λ₀+iε)ξ‖` by `|λ - λ₀| · (‖ξ‖/ε² + 1)` via the resolvent identity, which is
slightly weaker than a genuine `LipschitzWith (‖ξ‖/ε²)` bound. -/
lemma resolvent_continuous_at_height {ε : ℝ} (hε : 0 < ε) (ξ : H) :
    Continuous (fun lambda : ℝ =>
      resolvent (⟨lambda, ε⟩ : ℂ) hε.ne' hsym hplus hminus ξ) := by
  rw [Metric.continuous_iff]
  intro lambda₀ δ hδ
  set K : ℝ := ‖ξ‖ / ε^2 + 1 with hK_def
  have hK_pos : 0 < K := by positivity
  refine ⟨δ / K, by positivity, fun lambda hlambda => ?_⟩
  -- Resolvent identity, applied to ξ
  have hdiff :
      resolvent (⟨lambda, ε⟩ : ℂ) hε.ne' hsym hplus hminus ξ -
        resolvent (⟨lambda₀, ε⟩ : ℂ) hε.ne' hsym hplus hminus ξ =
      ((⟨lambda, ε⟩ : ℂ) - ⟨lambda₀, ε⟩) •
        (resolvent (⟨lambda, ε⟩ : ℂ) hε.ne' hsym hplus hminus)
          ((resolvent (⟨lambda₀, ε⟩ : ℂ) hε.ne' hsym hplus hminus) ξ) := by
    have h := congrArg (fun T : H →L[ℂ] H => T ξ)
      (resolvent_identity hsym hplus hminus
        (⟨lambda, ε⟩ : ℂ) (⟨lambda₀, ε⟩ : ℂ) hε.ne' hε.ne')
    simpa [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
           ContinuousLinearMap.comp_apply] using h
  -- ‖z - z₀‖ = |λ - λ₀|
  have hnorm_zd : ‖((⟨lambda, ε⟩ : ℂ) - ⟨lambda₀, ε⟩)‖ = |lambda - lambda₀| := by
    have hz_eq : ((⟨lambda, ε⟩ : ℂ) - ⟨lambda₀, ε⟩) = ((lambda - lambda₀ : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [hz_eq, Complex.norm_real]; rfl
  -- Both resolvents have operator norm ≤ 1/ε on the strip Im = ε.
  have hbnd_z  := resolvent_bound (⟨lambda, ε⟩  : ℂ) hε.ne' hsym hplus hminus
  have hbnd_z₀ := resolvent_bound (⟨lambda₀, ε⟩ : ℂ) hε.ne' hsym hplus hminus
  have him  : (⟨lambda, ε⟩  : ℂ).im = ε := rfl
  have him₀ : (⟨lambda₀, ε⟩ : ℂ).im = ε := rfl
  rw [him,  abs_of_pos hε] at hbnd_z
  rw [him₀, abs_of_pos hε] at hbnd_z₀
  -- Product bound:  ‖R(z) R(z₀) ξ‖ ≤ ‖ξ‖ / ε²
  have hop_bnd :
      ‖(resolvent (⟨lambda, ε⟩ : ℂ) hε.ne' hsym hplus hminus)
          ((resolvent (⟨lambda₀, ε⟩ : ℂ) hε.ne' hsym hplus hminus) ξ)‖
        ≤ ‖ξ‖ / ε^2 :=
    calc _ ≤ ‖resolvent (⟨lambda, ε⟩ : ℂ) hε.ne' hsym hplus hminus‖ *
              ‖(resolvent (⟨lambda₀, ε⟩ : ℂ) hε.ne' hsym hplus hminus) ξ‖ :=
                ContinuousLinearMap.le_opNorm _ _
      _ ≤ (1/ε) * (‖resolvent (⟨lambda₀, ε⟩ : ℂ) hε.ne' hsym hplus hminus‖ * ‖ξ‖) := by
              gcongr
              exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ (1/ε) * ((1/ε) * ‖ξ‖) := by gcongr
      _ = ‖ξ‖ / ε^2 := by ring
  -- Combine
  rw [dist_eq_norm, hdiff, norm_smul, hnorm_zd]
  rw [dist_eq_norm, Real.norm_eq_abs] at hlambda
  calc |lambda - lambda₀| * _
      ≤ |lambda - lambda₀| * (‖ξ‖ / ε^2) := by gcongr
    _ ≤ |lambda - lambda₀| * K := by
          have hKge : ‖ξ‖ / ε^2 ≤ K := by rw [hK_def]; linarith
          exact mul_le_mul_of_nonneg_left hKge (abs_nonneg _)
    _ < (δ / K) * K                        := by
          exact mul_lt_mul_of_pos_right hlambda hK_pos
    _ = δ                                   := by field_simp

/-- The **lower-half-plane Laplace representation** of the resolvent diagonal:
`⟨ξ, R(λ - iε)ξ⟩ = -i ∫₀^∞ e^{-iλt} e^{-εt} f(t) dt`. -/
lemma resolvent_diag_lower_laplace (ξ : H) {ε : ℝ} (hε : 0 < ε) (lambda : ℝ) :
    ⟪ξ, resolvent (⟨lambda, -ε⟩ : ℂ)
            (by change (-ε : ℝ) ≠ 0; exact neg_ne_zero.mpr hε.ne')
            (generator_isFormalAdjoint U_grp)
            (range_plus_i_eq_top U_grp)
            (range_minus_i_eq_top U_grp) ξ⟫_ℂ
      = -I * ∫ t in Set.Ici (0 : ℝ),
              cexp (-(I * (lambda : ℂ) * (t : ℂ))) *
              (Real.exp (-(ε * t)) : ℂ) *
              ⟪ξ, U_grp.U t ξ⟫_ℂ := by
  -- z = λ - iε, so z.im = -ε < 0
  set z : ℂ := ⟨lambda, -ε⟩ with _hz_def
  have hz_lt : z.im < 0 := by change (-ε : ℝ) < 0; linarith
  -- Step 1: replace R(z) ξ by its Laplace integral form.
  rw [← resolventIntegralZ_eq_resolvent (U_grp := U_grp) hz_lt]
  unfold resolventIntegralZ
  -- Step 2: pull -I out via linearity of inner in the second slot.
  rw [inner_smul_right]
  congr 1
  -- Step 3: pull ⟨ξ, ·⟩ through the Bochner integral as a continuous linear functional.
  rw [← integral_inner (integrable_expZ_unitary U_grp hz_lt ξ)]
  -- Step 4: ⟨ξ, cexp(…) • U(t)ξ⟩ = cexp(…) * ⟨ξ, U(t)ξ⟩,
  -- and split cexp(-(I*z*t)) = cexp(-(I*λ*t)) * Real.exp(-(ε*t)).
  refine setIntegral_congr_fun measurableSet_Ici (fun t _ => ?_)
  rw [inner_smul_right]
  -- Now show cexp(-(I*z*t)) = cexp(-(I*λ*t)) * Real.exp(-(ε*t)) as a complex number.
  have h_split :
      cexp (-(I * z * (t : ℂ)))
        = cexp (-(I * (lambda : ℂ) * (t : ℂ))) * (Real.exp (-(ε * t)) : ℂ) := by
    have hz_re : z.re = lambda := rfl
    have hz_im : z.im = -ε := rfl
    -- z = lambda - I * ε, so -(I*z*t) = -(I*λ*t) - ε*t
    rw [show (z : ℂ) = (lambda : ℂ) - I * (ε : ℂ) by
          apply Complex.ext <;> simp [hz_re, hz_im]]
    rw [show -(I * ((lambda : ℂ) - I * (ε : ℂ)) * (t : ℂ))
          = -(I * (lambda : ℂ) * (t : ℂ)) + (-(ε * t : ℝ) : ℂ) by
            push_cast; ring_nf; rw [Complex.I_sq]; ring]
    rw [Complex.exp_add, Complex.ofReal_exp]
    simp only [ofReal_mul, ofReal_neg]
  rw [h_split]

/-- The **upper/lower conjugate symmetry** of the resolvent diagonal:
`⟨ξ, R(λ+iε)ξ⟩ = conj ⟨ξ, R(λ-iε)ξ⟩`. -/
lemma resolvent_diag_upper_eq_conj (ξ : H) {ε : ℝ} (hε : 0 < ε) (lambda : ℝ) :
    ⟪ξ, resolvent (⟨lambda, ε⟩ : ℂ) hε.ne'
            (generator_isFormalAdjoint U_grp)
            (range_plus_i_eq_top U_grp)
            (range_minus_i_eq_top U_grp) ξ⟫_ℂ
      = starRingEnd ℂ ⟪ξ, resolvent (⟨lambda, -ε⟩ : ℂ)
              (neg_ne_zero.mpr hε.ne')
              (generator_isFormalAdjoint U_grp)
              (range_plus_i_eq_top U_grp)
              (range_minus_i_eq_top U_grp) ξ⟫_ℂ := by
  have hz_neg_ne : ((⟨lambda, -ε⟩ : ℂ)).im ≠ 0 := neg_ne_zero.mpr hε.ne'
  have h_adj := resolvent_adjoint
        (generator_isFormalAdjoint U_grp)
        (range_plus_i_eq_top U_grp)
        (range_minus_i_eq_top U_grp)
        (⟨lambda, -ε⟩ : ℂ) hz_neg_ne
  have h_eq : resolvent (⟨lambda, ε⟩ : ℂ) hε.ne'
        (generator_isFormalAdjoint U_grp)
        (range_plus_i_eq_top U_grp)
        (range_minus_i_eq_top U_grp)
      = (resolvent (⟨lambda, -ε⟩ : ℂ) hz_neg_ne
          (generator_isFormalAdjoint U_grp)
          (range_plus_i_eq_top U_grp)
          (range_minus_i_eq_top U_grp)).adjoint := by
    rw [h_adj]; congr 1; apply Complex.ext <;> simp
  conv_lhs => rw [h_eq]
  rw [ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]

end Spectra.Resolvent
