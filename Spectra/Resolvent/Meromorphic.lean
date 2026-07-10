/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Spectrum
import Spectra.Resolvent.Identities
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Ring.Units
/-!
# The resolvent on the whole resolvent set, and its analyticity (Tier C: C0 + C1)

The bespoke `Resolvent.resolvent` is only constructed for `Im z ≠ 0` (where `A − z` is surjective
by the basic self-adjointness machinery).  But the *poles* of the resolvent of a self-adjoint
operator are real, so to talk about meromorphy we need the resolvent on **all** of the resolvent
set — including real points in spectral gaps.

This file builds that general object and proves it is analytic on the (open) resolvent set.

## Main definitions

* `Spectra.Resolvent.IsResolvent A z R` — `R : H →L[ℂ] H` is a two-sided bounded inverse of
  `A − z` (a left inverse on `dom A`, a right inverse landing in `dom A`).  Membership in
  `resolventSet A` is exactly the existence of such an `R`.
* `Spectra.Resolvent.resolventOf A z` — the resolvent `(A − z)⁻¹` for `z` in the resolvent set
  (the chosen two-sided inverse), and junk `0` off it.  Total in `z : ℂ`.

## Main statements

* `IsResolvent.unique` — two two-sided inverses of `A − z` agree (operator-level uniqueness).
* `resolventOf_isResolvent` — `resolventOf A z` is a two-sided inverse when `z ∈ resolventSet A`.
* `resolventOf_eq_resolvent` — agrees with the bespoke `resolvent` for `Im z ≠ 0`.
* `resolventOf_identity` — the resolvent identity `R(z) − R(w) = (z − w) R(z) R(w)` on the
  resolvent set.
* `isResolvent_mul_neumann` / `mem_resolventSet_of_norm_mul_lt` / `resolventOf_eq_mul_inverse` —
  the Neumann perturbation: `A − z` stays invertible near a resolvent point, with the explicit
  inverse `R₀ · (1 − (z − z₀) R₀)⁻¹`.
* `resolventOf_eq_of_rightInverse` — identifies `resolventOf A z` with an explicitly-built
  operator by checking only the right-inverse equation, used downstream at
  `SpectralTheory/SimplePole.lean`.
* `isOpen_resolventSet` — the resolvent set is open.
* `resolventOf_analyticOnNhd` — `AnalyticOnNhd ℂ (resolventOf A) (resolventSet A)`.

## Implementation notes

This file's Neumann-perturbation argument (`isResolvent_mul_neumann`, via `Ring.inverse` on the
unit `1 − (z − z₀) R₀`) is a different, more general construction than the earlier one in
`Resolvent/Analytic.lean` (`resolventFun_hasSum`, via `HasSum`/`neumannSeries` directly). They are
not redundant: `Analytic.lean` only ever considers `Im z ≠ 0` and produces a convergent power
series, feeding `YosidaHille/Approximation/Helpers.lean`; this file works on the *whole* resolvent
set — including real points in spectral gaps — and only needs analyticity, not an explicit series,
so it goes through `Ring.inverse`/`DifferentiableAt.comp` instead.

## References

* [Kato, *Perturbation Theory for Linear Operators*][kato1995], Section IV.3 (resolvent set open,
  resolvent analytic).
* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VI.5.
-/
open Complex Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Resolvent

/-! ## Two-sided inverses and the general resolvent -/

/-- `R : H →L[ℂ] H` is a **two-sided bounded inverse** of `A − z`: a left inverse on `dom A`, and a
right inverse on all of `H` landing back in `dom A`.  By definition `z ∈ resolventSet A` iff such an
`R` exists. -/
def IsResolvent (A : H →ₗ.[ℂ] H) (z : ℂ) (R : H →L[ℂ] H) : Prop :=
  (∀ ψ : A.domain, R (A ψ - z • (ψ : H)) = (ψ : H)) ∧
  (∀ φ : H, ∃ h : R φ ∈ A.domain, A ⟨R φ, h⟩ - z • R φ = φ)

omit [CompleteSpace H] in
lemma mem_resolventSet_iff {A : H →ₗ.[ℂ] H} {z : ℂ} :
    z ∈ resolventSet A ↔ ∃ R : H →L[ℂ] H, IsResolvent A z R := Iff.rfl

omit [CompleteSpace H] in
/-- **Operator-level uniqueness**: any two two-sided inverses of `A − z` are equal.  If `R` is a
left inverse and `R'` a right inverse landing in the domain, then `R φ = R ((A − z)(R' φ)) = R' φ`.
-/
lemma IsResolvent.unique {A : H →ₗ.[ℂ] H} {z : ℂ} {R R' : H →L[ℂ] H}
    (h : IsResolvent A z R) (h' : IsResolvent A z R') : R = R' := by
  ext φ
  obtain ⟨hmem', heq'⟩ := h'.2 φ
  have hh : R (A ⟨R' φ, hmem'⟩ - z • R' φ) = R' φ := h.1 ⟨R' φ, hmem'⟩
  rwa [heq'] at hh

open scoped Classical in
/-- The resolvent `(A − z)⁻¹` as a total function of `z`: the chosen two-sided inverse on the
resolvent set, junk `0` off it.  Well-defined regardless of the choice by `IsResolvent.unique`. -/
noncomputable def resolventOf (A : H →ₗ.[ℂ] H) (z : ℂ) : H →L[ℂ] H :=
  if h : z ∈ resolventSet A then h.choose else 0

open scoped Classical in
omit [CompleteSpace H] in
/-- `resolventOf A z` is a two-sided inverse of `A − z` whenever `z` is in the resolvent set. -/
lemma resolventOf_isResolvent {A : H →ₗ.[ℂ] H} {z : ℂ} (hz : z ∈ resolventSet A) :
    IsResolvent A z (resolventOf A z) := by
  change IsResolvent A z (if h : z ∈ resolventSet A then h.choose else 0)
  rw [dif_pos hz]
  exact hz.choose_spec

omit [CompleteSpace H] in
/-- On the resolvent set, `resolventOf A z` is THE two-sided inverse: it equals any other. -/
lemma resolventOf_eq_of_isResolvent {A : H →ₗ.[ℂ] H} {z : ℂ} {R : H →L[ℂ] H}
    (hR : IsResolvent A z R) : resolventOf A z = R :=
  (resolventOf_isResolvent ⟨R, hR⟩).unique hR

omit [CompleteSpace H] in
/-- On the resolvent set, `resolventOf A z` equals **any right inverse landing in the domain**: the
left-inverse property of the (genuine two-sided) `resolventOf` pins it down, since
`resolventOf φ = resolventOf ((A − z)(R φ)) = R φ`.  This lets one identify the resolvent with an
explicitly-built operator by checking only the right-inverse equation `(A − z)(R φ) = φ`. -/
lemma resolventOf_eq_of_rightInverse {A : H →ₗ.[ℂ] H} {z : ℂ} (hz : z ∈ resolventSet A)
    {R : H →L[ℂ] H}
    (hR : ∀ φ : H, ∃ h : R φ ∈ A.domain, A ⟨R φ, h⟩ - z • R φ = φ) :
    resolventOf A z = R := by
  ext φ
  obtain ⟨hmem, heq⟩ := hR φ
  have hh : resolventOf A z (A ⟨R φ, hmem⟩ - z • R φ) = R φ :=
    (resolventOf_isResolvent hz).1 ⟨R φ, hmem⟩
  rwa [heq] at hh

/-! ## Agreement with the bespoke resolvent off the real axis -/

/-- For `Im z ≠ 0`, the bespoke `resolvent` is a two-sided inverse of `A − z`. -/
lemma isResolvent_resolvent {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    {z : ℂ} (hz : z.im ≠ 0) :
    IsResolvent A z (resolvent z hz hsym hplus hminus) := by
  refine ⟨?_, ?_⟩
  · intro ψ
    have heq := resolvent_sub_smul_apply z hz hsym hplus hminus (A ψ - z • (ψ : H))
    have huniq := (self_adjoint_range_all_z hsym hplus hminus z hz (A ψ - z • (ψ : H))).unique
      heq rfl
    exact congrArg Subtype.val huniq
  · intro φ
    exact ⟨resolvent_apply_mem_domain z hz hsym hplus hminus φ,
      resolvent_sub_smul_apply z hz hsym hplus hminus φ⟩

/-- The general resolvent agrees with the bespoke one for `Im z ≠ 0`. -/
lemma resolventOf_eq_resolvent {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    {z : ℂ} (hz : z.im ≠ 0) :
    resolventOf A z = resolvent z hz hsym hplus hminus :=
  resolventOf_eq_of_isResolvent (isResolvent_resolvent hsym hplus hminus hz)

/-! ## The resolvent identity on the resolvent set -/

omit [CompleteSpace H] in
/-- **The resolvent identity** `R(z) − R(w) = (z − w) R(z) R(w)`, on the resolvent set.  Pure
operator algebra from the two-sided inverse properties (no `Im z ≠ 0`). -/
lemma resolventOf_identity {A : H →ₗ.[ℂ] H} {z w : ℂ}
    (hz : z ∈ resolventSet A) (hw : w ∈ resolventSet A) :
    resolventOf A z - resolventOf A w
      = (z - w) • (resolventOf A z * resolventOf A w) := by
  obtain ⟨hLz, _⟩ := resolventOf_isResolvent hz
  obtain ⟨_, hRw⟩ := resolventOf_isResolvent hw
  ext φ
  obtain ⟨hmemw, heqw⟩ := hRw φ
  have hAz : A ⟨resolventOf A w φ, hmemw⟩ - z • resolventOf A w φ
      = φ + (w - z) • resolventOf A w φ := by
    have hstep : A ⟨resolventOf A w φ, hmemw⟩ - z • resolventOf A w φ
        = (A ⟨resolventOf A w φ, hmemw⟩ - w • resolventOf A w φ)
            + (w - z) • resolventOf A w φ := by
      rw [sub_smul]; abel
    rw [hstep, heqw]
  have hkey : resolventOf A z φ + (w - z) • resolventOf A z (resolventOf A w φ)
      = resolventOf A w φ := by
    have h0 : resolventOf A z (A ⟨resolventOf A w φ, hmemw⟩ - z • resolventOf A w φ)
        = resolventOf A w φ := hLz ⟨resolventOf A w φ, hmemw⟩
    rw [hAz, map_add, map_smul] at h0
    exact h0
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.mul_apply]
  set X := resolventOf A z (resolventOf A w φ)
  rw [← hkey, show (z - w) = -(w - z) by ring, neg_smul]
  abel

/-! ## Neumann perturbation: the resolvent set is open -/

/-- **Neumann construction.**  If `R₀` is a two-sided inverse of `A − z₀` and
`‖(z − z₀) R₀‖ < 1`, then `R₀ · (1 − (z − z₀) R₀)⁻¹` is a two-sided inverse of `A − z`. -/
lemma isResolvent_mul_neumann {A : H →ₗ.[ℂ] H} {z₀ : ℂ} {R₀ : H →L[ℂ] H}
    (h₀ : IsResolvent A z₀ R₀) {z : ℂ} (hT : ‖((z - z₀) • R₀)‖ < 1) :
    IsResolvent A z (R₀ * neumannSeries ((z - z₀) • R₀) hT) := by
  set T := (z - z₀) • R₀ with hTdef
  set S := neumannSeries T hT
  obtain ⟨hL₀, hR₀⟩ := h₀
  -- Injectivity of `A − z` on the domain.
  have hInj : ∀ χ : H, ∀ hχ : χ ∈ A.domain, A ⟨χ, hχ⟩ - z • χ = 0 → χ = 0 := by
    intro χ hχ hz0
    have e1 : A ⟨χ, hχ⟩ - z₀ • χ = (z - z₀) • χ := by
      have hsplit : A ⟨χ, hχ⟩ - z₀ • χ = (A ⟨χ, hχ⟩ - z • χ) + (z - z₀) • χ := by
        rw [sub_smul]; abel
      rw [hsplit, hz0, zero_add]
    have e2 : R₀ ((z - z₀) • χ) = χ := by
      have h : R₀ (A ⟨χ, hχ⟩ - z₀ • χ) = χ := hL₀ ⟨χ, hχ⟩
      rwa [e1] at h
    have e3 : T χ = χ := by
      have ht : T χ = (z - z₀) • R₀ χ := by rw [hTdef, ContinuousLinearMap.smul_apply]
      have hm : R₀ ((z - z₀) • χ) = (z - z₀) • R₀ χ := map_smul R₀ (z - z₀) χ
      rw [ht, ← hm]; exact e2
    have hmr := neumannSeries_mul_right T hT
    have happ := congrArg (fun L : H →L[ℂ] H => L χ) hmr
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply] at happ
    rw [e3, sub_self, map_zero] at happ
    exact happ.symm
  -- Right inverse: `(A − z)(R₀ S φ) = φ`.
  have hRight : ∀ φ : H, ∃ h : (R₀ * S) φ ∈ A.domain,
      A ⟨(R₀ * S) φ, h⟩ - z • ((R₀ * S) φ) = φ := by
    intro φ
    obtain ⟨hmem, heq⟩ := hR₀ (S φ)
    refine ⟨hmem, ?_⟩
    change A ⟨R₀ (S φ), hmem⟩ - z • (R₀ (S φ)) = φ
    have hzz : A ⟨R₀ (S φ), hmem⟩ - z • (R₀ (S φ))
        = (A ⟨R₀ (S φ), hmem⟩ - z₀ • R₀ (S φ)) - (z - z₀) • R₀ (S φ) := by
      rw [sub_smul]; abel
    rw [hzz, heq]
    have hT_app : (z - z₀) • R₀ (S φ) = T (S φ) := by
      rw [hTdef, ContinuousLinearMap.smul_apply]
    rw [hT_app]
    have hidT : S φ - T (S φ) = (ContinuousLinearMap.id ℂ H - T) (S φ) := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    rw [hidT]
    have hml := neumannSeries_mul_left T hT
    have happ := congrArg (fun L : H →L[ℂ] H => L φ) hml
    simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.id_apply] using happ
  -- Left inverse: from right inverse + injectivity.
  refine ⟨?_, hRight⟩
  intro ψ
  obtain ⟨hmem, heq⟩ := hRight (A ψ - z • (ψ : H))
  set χ := (R₀ * S) (A ψ - z • (ψ : H))
  have hsub_mem : χ - (ψ : H) ∈ A.domain := A.domain.sub_mem hmem ψ.2
  have hzero : A ⟨χ - (ψ : H), hsub_mem⟩ - z • (χ - (ψ : H)) = 0 := by
    have hmap : A ⟨χ - (ψ : H), hsub_mem⟩ = A ⟨χ, hmem⟩ - A ψ := by
      rw [← A.map_sub ⟨χ, hmem⟩ ψ]
      exact congrArg A (Subtype.ext rfl)
    rw [hmap, smul_sub,
      show A ⟨χ, hmem⟩ - A ψ - (z • χ - z • (ψ : H))
        = (A ⟨χ, hmem⟩ - z • χ) - (A ψ - z • (ψ : H)) by abel, heq, sub_self]
  have hχψ : χ - (ψ : H) = 0 := hInj (χ - (ψ : H)) hsub_mem hzero
  exact sub_eq_zero.mp hχψ

/-- If `‖(z − z₀) R₀‖ < 1` (with `R₀ = resolventOf A z₀`), then `z` is in the resolvent set. -/
lemma mem_resolventSet_of_norm_mul_lt {A : H →ₗ.[ℂ] H} {z₀ : ℂ} (hz₀ : z₀ ∈ resolventSet A)
    {z : ℂ} (hz : ‖z - z₀‖ * ‖resolventOf A z₀‖ < 1) : z ∈ resolventSet A := by
  have hTnorm : ‖(z - z₀) • resolventOf A z₀‖ < 1 := by rw [norm_smul]; exact hz
  exact ⟨_, isResolvent_mul_neumann (resolventOf_isResolvent hz₀) hTnorm⟩

/-- The explicit local formula for the perturbed resolvent:
`R(z) = R₀ · (1 − (z − z₀) R₀)⁻¹`. -/
lemma resolventOf_eq_mul_inverse {A : H →ₗ.[ℂ] H} {z₀ : ℂ} (hz₀ : z₀ ∈ resolventSet A)
    {z : ℂ} (hz : ‖z - z₀‖ * ‖resolventOf A z₀‖ < 1) :
    resolventOf A z
      = resolventOf A z₀ * Ring.inverse (1 - (z - z₀) • resolventOf A z₀) := by
  set R₀ := resolventOf A z₀ with _hR₀
  have hTnorm : ‖(z - z₀) • R₀‖ < 1 := by rw [norm_smul]; exact hz
  have huniq : resolventOf A z = R₀ * neumannSeries ((z - z₀) • R₀) hTnorm :=
    resolventOf_eq_of_isResolvent (isResolvent_mul_neumann (resolventOf_isResolvent hz₀) hTnorm)
  rw [huniq]
  congr 1
  rw [NormedRing.inverse_one_sub ((z - z₀) • R₀) hTnorm]
  rfl

/-- **The resolvent set is open.** -/
theorem isOpen_resolventSet (A : H →ₗ.[ℂ] H) : IsOpen (resolventSet A) := by
  rw [Metric.isOpen_iff]
  intro z₀ hz₀
  refine ⟨1 / (‖resolventOf A z₀‖ + 1), by positivity, ?_⟩
  intro z hz
  have hRpos : 0 < ‖resolventOf A z₀‖ + 1 := by positivity
  have hd : ‖z - z₀‖ < 1 / (‖resolventOf A z₀‖ + 1) := by
    rwa [Metric.mem_ball, dist_eq_norm] at hz
  have hlt : ‖z - z₀‖ * (‖resolventOf A z₀‖ + 1) < 1 := (lt_div_iff₀ hRpos).mp hd
  have hmul : ‖z - z₀‖ * ‖resolventOf A z₀‖ ≤ ‖z - z₀‖ * (‖resolventOf A z₀‖ + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
  exact mem_resolventSet_of_norm_mul_lt hz₀ (by linarith)

/-! ## Analyticity on the resolvent set -/

/-- The resolvent is complex-differentiable at every point of the resolvent set: locally it equals
`R₀ · (1 − (z − z₀) R₀)⁻¹`, a composition of an affine map with `Ring.inverse` at a unit. -/
lemma resolventOf_differentiableAt {A : H →ₗ.[ℂ] H} {z₀ : ℂ} (hz₀ : z₀ ∈ resolventSet A) :
    DifferentiableAt ℂ (resolventOf A) z₀ := by
  set R₀ := resolventOf A z₀ with _hR₀
  -- The local model `g z = R₀ · (1 − (z − z₀) R₀)⁻¹` is differentiable at `z₀`.
  have hg : DifferentiableAt ℂ (fun z => R₀ * Ring.inverse (1 - (z - z₀) • R₀)) z₀ := by
    have hc : DifferentiableAt ℂ (fun z => (1 : H →L[ℂ] H) - (z - z₀) • R₀) z₀ := by fun_prop
    have hu : IsUnit ((fun z => (1 : H →L[ℂ] H) - (z - z₀) • R₀) z₀) := by simp
    have hinv : DifferentiableAt ℂ
        (Ring.inverse ∘ fun z => (1 : H →L[ℂ] H) - (z - z₀) • R₀) z₀ :=
      DifferentiableAt.comp z₀ (differentiableAt_inverse (𝕜 := ℂ) hu) hc
    exact (differentiableAt_const R₀).mul hinv
  -- The resolvent agrees with `g` on a ball around `z₀`.
  have hEq : resolventOf A =ᶠ[𝓝 z₀] fun z => R₀ * Ring.inverse (1 - (z - z₀) • R₀) := by
    have hpos : (0 : ℝ) < 1 / (‖R₀‖ + 1) := by positivity
    filter_upwards [Metric.ball_mem_nhds z₀ hpos] with w hw
    have hRpos : 0 < ‖R₀‖ + 1 := by positivity
    have hd : ‖w - z₀‖ < 1 / (‖R₀‖ + 1) := by rwa [Metric.mem_ball, dist_eq_norm] at hw
    have hlt : ‖w - z₀‖ * (‖R₀‖ + 1) < 1 := (lt_div_iff₀ hRpos).mp hd
    have hmul : ‖w - z₀‖ * ‖R₀‖ ≤ ‖w - z₀‖ * (‖R₀‖ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    exact resolventOf_eq_mul_inverse hz₀ (by linarith)
  exact hg.congr_of_eventuallyEq hEq

/-- The resolvent is complex-differentiable on the resolvent set. -/
lemma resolventOf_differentiableOn (A : H →ₗ.[ℂ] H) :
    DifferentiableOn ℂ (resolventOf A) (resolventSet A) :=
  fun _ hz => (resolventOf_differentiableAt hz).differentiableWithinAt

/-- **C1 — the resolvent is analytic on the resolvent set.** -/
theorem resolventOf_analyticOnNhd (A : H →ₗ.[ℂ] H) :
    AnalyticOnNhd ℂ (resolventOf A) (resolventSet A) :=
  (resolventOf_differentiableOn A).analyticOnNhd (isOpen_resolventSet A)

/-- The resolvent is analytic at each individual resolvent point: the standard
`AnalyticOnNhd → AnalyticAt` specialization of `resolventOf_analyticOnNhd` at `z`, with no
additional content beyond evaluating the `AnalyticOnNhd` predicate at a single membership proof. -/
theorem resolventOf_analyticAt {A : H →ₗ.[ℂ] H} {z : ℂ} (hz : z ∈ resolventSet A) :
    AnalyticAt ℂ (resolventOf A) z :=
  resolventOf_analyticOnNhd A z hz

end Spectra.Resolvent
