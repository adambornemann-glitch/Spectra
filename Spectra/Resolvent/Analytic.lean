/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Identities

/-!
# Analyticity of the Resolvent

This file proves the textbook fact that the resolvent `R(z) = (A - zI)⁻¹` is an analytic
operator-valued function off the real axis: near any `z₀` with `Im z₀ ≠ 0`, `R(z)` has the
convergent Neumann-type power-series expansion
`R(z) = ∑ₙ (z - z₀)ⁿ • R(z₀)ⁿ⁺¹` for `‖z - z₀‖ < |Im z₀|`.

## Main statements

* `resolventFun_hasSum` : the Neumann-series expansion of `R(z)` around `z₀`.

## Implementation notes

The proof composes the resolvent identity with the abstract Neumann series
(`neumannSeries`/`neumannSeries_hasSum` from `Defs.lean`): writing `R₀ = R(z₀)` and
`T = (z - z₀) • R₀`, the resolvent identity shows `R(z) = R₀ ∘ (1 - T)⁻¹`, and `(1 - T)⁻¹` is
exactly `neumannSeries T hT`, convergent because `‖T‖ < 1` follows from the standard resolvent
bound `‖R₀‖ ≤ 1 / |Im z₀|`. Composing `R₀` with the Neumann series term-by-term and matching
powers gives the stated `HasSum`.

This is an off-axis-only construction (it needs `‖z - z₀‖ < |Im z₀|` to make `T` small). The
later, general analyticity result on the whole resolvent set — including approach to the real
axis away from the spectrum — is proved independently in `Meromorphic.lean` via
`isResolvent_mul_neumann`/`Ring.inverse`, which does not go through this file.

## References

* [Kato, *Perturbation Theory for Linear Operators*][kato1995], Section IV.1
* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII
-/
open Complex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Resolvent

/-- The **resolvent has a convergent power series expansion** near any point `z₀` with
`Im z₀ ≠ 0`: for `z` within `|Im z₀|` of `z₀`, `R(z) = ∑ₙ (z - z₀)ⁿ • R(z₀)ⁿ⁺¹`. -/
lemma resolventFun_hasSum {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (z₀ : OffRealAxis) (z : ℂ) (hz : ‖z - z₀.val‖ < |z₀.val.im|) :
    HasSum (fun n => (z - z₀.val)^n • (resolventFun hsym hplus hminus z₀)^(n+1))
           (resolvent z (im_ne_zero_of_near hz) hsym hplus hminus) := by
  have hz' : z.im ≠ 0 := im_ne_zero_of_near hz
  set R₀ := resolventFun hsym hplus hminus z₀ with _hR₀_def
  set T := (z - z₀.val) • R₀ with hT_def
  have hT_norm : ‖T‖ < 1 := by
    have h_smul_bound : ‖T‖ ≤ ‖z - z₀.val‖ * ‖R₀‖ := by
      simp only [hT_def]
      exact norm_smul_le (z - z₀.val) R₀
    have h_R₀_bound : ‖R₀‖ ≤ 1 / |z₀.val.im| :=
      resolvent_bound z₀.val z₀.property hsym hplus hminus
    calc ‖T‖
        ≤ ‖z - z₀.val‖ * ‖R₀‖ := h_smul_bound
      _ ≤ ‖z - z₀.val‖ * (1 / |z₀.val.im|) := by
          apply mul_le_mul_of_nonneg_left h_R₀_bound (norm_nonneg _)
      _ = ‖z - z₀.val‖ / |z₀.val.im| := by ring
      _ < |z₀.val.im| / |z₀.val.im| := by
          apply div_lt_div_of_pos_right hz (abs_pos.mpr z₀.property)
      _ = 1 := div_self (ne_of_gt (abs_pos.mpr z₀.property))
  have h_neumann := neumannSeries_hasSum T hT_norm
  -- Resolvents at `z` and `z₀` commute, so `R₀` and `R(z)` can be freely reordered below.
  have h_comm : R₀.comp (resolvent z hz' hsym hplus hminus) =
              (resolvent z hz' hsym hplus hminus).comp R₀ :=
    resolvent_commute hsym hplus hminus z₀.val z z₀.property hz'
  -- Express R(z) in terms of R(z₀) and the Neumann series.
  have h_resolvent_eq : resolvent z hz' hsym hplus hminus =
    R₀.comp (neumannSeries T hT_norm) := by
    set Rz := resolvent z hz' hsym hplus hminus with _hRz_def
    have h_res_id := resolvent_identity hsym hplus hminus z₀.val z z₀.property hz'
    have h1 : Rz = R₀ + (z - z₀.val) • R₀.comp Rz := by
      have hsub : R₀ - Rz = (z₀.val - z) • R₀.comp Rz := h_res_id
      have hneg : (z₀.val - z) = -(z - z₀.val) := by ring
      rw [hneg, neg_smul] at hsub
      calc Rz = R₀ - (R₀ - Rz) := by abel
        _ = R₀ - (-((z - z₀.val) • R₀.comp Rz)) := by rw [hsub]
        _ = R₀ + (z - z₀.val) • R₀.comp Rz := by abel
    rw [h_comm] at h1
    have h2 : (z - z₀.val) • Rz.comp R₀ = Rz.comp T := by
      rw [hT_def, ContinuousLinearMap.comp_smul]
    rw [h2] at h1
    have h3 : Rz.comp (ContinuousLinearMap.id ℂ H - T) = R₀ := by
      have : Rz - Rz.comp T = R₀ := by exact sub_eq_iff_eq_add.mpr h1
      calc Rz.comp (ContinuousLinearMap.id ℂ H - T)
          = Rz.comp (ContinuousLinearMap.id ℂ H) - Rz.comp T := by
              rw [ContinuousLinearMap.comp_sub]
        _ = Rz - Rz.comp T := by rw [ContinuousLinearMap.comp_id]
        _ = R₀ := by exact this
    calc Rz = Rz.comp (ContinuousLinearMap.id ℂ H) := by rw [ContinuousLinearMap.comp_id]
      _ = Rz.comp ((ContinuousLinearMap.id ℂ H - T) * (neumannSeries T hT_norm)) := by
          rw [neumannSeries_mul_left T hT_norm]
      _ = Rz.comp ((ContinuousLinearMap.id ℂ H - T).comp (neumannSeries T hT_norm)) := rfl
      _ = (Rz.comp (ContinuousLinearMap.id ℂ H - T)).comp (neumannSeries T hT_norm) := by
          rw [ContinuousLinearMap.comp_assoc]
      _ = R₀.comp (neumannSeries T hT_norm) := by rw [h3]
  -- Show that each term matches.
  have h_term_eq : ∀ n, R₀.comp (T^n) = (z - z₀.val)^n • R₀^(n+1) := by
    intro n
    induction n with
    | zero =>
      simp only [pow_zero, one_smul, zero_add, pow_one]
      rfl
    | succ n ih =>
      calc R₀.comp (T^(n+1))
          = R₀.comp (T^n * T) := by rw [pow_succ]
        _ = (R₀.comp (T^n)).comp T := by rfl
        _ = ((z - z₀.val)^n • R₀^(n+1)).comp T := by rw [ih]
        _ = (z - z₀.val)^n • (R₀^(n+1)).comp ((z - z₀.val) • R₀) := by
            rw [ContinuousLinearMap.smul_comp]
        _ = (z - z₀.val)^n • ((z - z₀.val) • (R₀^(n+1)).comp R₀) := by
            rw [ContinuousLinearMap.comp_smul]
        _ = (z - z₀.val)^n • ((z - z₀.val) • R₀^(n+2)) := by
            have : (R₀^(n+1)).comp R₀ = R₀^(n+2) := by
              change R₀^(n+1) * R₀ = R₀^(n+2)
              rw [← pow_succ]
            rw [this]
        _ = (z - z₀.val)^(n+1) • R₀^(n+2) := by
            rw [smul_smul, ← pow_succ]
  rw [h_resolvent_eq]
  have h_comp_hasSum : HasSum (fun n => R₀.comp (T^n)) (R₀.comp (neumannSeries T hT_norm)) :=
    ((ContinuousLinearMap.compL ℂ H H H) R₀).hasSum h_neumann
  convert h_comp_hasSum using 1
  · ext n
    exact Eq.symm (DFunLike.congr (h_term_eq n) rfl)

end Spectra.Resolvent
