/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.ProjValMeasure.Basic

/-!
# Projection-valued measures on an arbitrary measurable space

`ProjValMeasure' K ι` is the projection-valued measure of `ProjValMeasure/Basic.lean` with two
generalizations: the outcome space is an arbitrary `[MeasurableSpace ι]` (rather than the Borel
sets of `ℝ`), and the Hilbert space `K` is a **parameter** of the structure (rather than a
file-level `variable`).  The second is what lets a single `ProjValMeasure'` live on a *constructed*
space — e.g. the dilation space of Naimark's theorem.

## Design

It is exactly `Spectra.POVM` (the positive operator-valued measure of
`QuantumMechanics/BornRule/POVM.lean`) **plus** the multiplicativity field `proj_inter`
(`E(B₁)E(B₂) = E(B₁∩B₂)`).  So everything `POVM` proves ports verbatim — self-adjointness, finite
additivity, the mass `‖ξ‖²`, extensionality — and the two facts `POVM` had to drop (idempotence
`proj_idem` and the projective norm identity `norm_sq_proj_apply`) come back, exactly as in
`ProjValMeasure/Basic.lean`, now over a general `ι` and a parametric `K`.

`Spectra.ProjValMeasure H` (over `(ℝ, Borel)`) is the special case `K = H`, `ι = ℝ`; we keep it
separate to avoid disturbing the spectral stack built on it.
-/

open MeasureTheory Complex
open scoped InnerProductSpace ENNReal

namespace Spectra

/-- A **projection-valued measure** on the measurable space `(ι, 𝓜)`, acting on the complex
Hilbert space `K`.  The diagonal scalar measures `diag ξ` are carried as data and welded to the
projections by `inner_proj`; multiplicativity `proj_inter` makes the projections genuine
(idempotent, self-adjoint) projections, recovering the full PVM calculus. -/
structure ProjValMeasure' (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (ι : Type*) [MeasurableSpace ι] where
  /-- The projection assigned to each measurable set. -/
  proj : ∀ B : Set ι, MeasurableSet B → (K →L[ℂ] K)
  /-- The diagonal scalar measures, carried as data. -/
  diag : K → Measure ι
  /-- Each diagonal measure is finite (mass `‖ξ‖²`, by `diag_univ_toReal`). -/
  diag_finite : ∀ ξ : K, IsFiniteMeasure (diag ξ)
  /-- The weld: diagonal matrix elements of the projections are the diagonal measures. -/
  inner_proj : ∀ (B : Set ι) (hB : MeasurableSet B) (ξ : K),
    ⟪ξ, proj B hB ξ⟫_ℂ = (((diag ξ) B).toReal : ℂ)
  /-- Normalization: the whole space carries the identity, `P(ι) = I`. -/
  proj_univ : proj Set.univ MeasurableSet.univ = ContinuousLinearMap.id ℂ K
  /-- Multiplicativity: intersection of sets is composition of projections. -/
  proj_inter : ∀ (B₁ B₂ : Set ι) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂),
    proj B₁ hB₁ * proj B₂ hB₂ = proj (B₁ ∩ B₂) (hB₁.inter hB₂)

namespace ProjValMeasure'

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {ι : Type*} [MeasurableSpace ι]

instance instIsFiniteMeasureDiag (P : ProjValMeasure' K ι) (ξ : K) :
    IsFiniteMeasure (P.diag ξ) :=
  P.diag_finite ξ

/-- The projections do not depend on the measurability witness. -/
lemma proj_congr (P : ProjValMeasure' K ι) {B₁ B₂ : Set ι} (h : B₁ = B₂)
    (h₁ : MeasurableSet B₁) (h₂ : MeasurableSet B₂) :
    P.proj B₁ h₁ = P.proj B₂ h₂ := by subst h; rfl

@[simp] lemma proj_empty (P : ProjValMeasure' K ι) : P.proj ∅ MeasurableSet.empty = 0 :=
  op_ext_of_inner_self fun ξ => by
    rw [P.inner_proj, ContinuousLinearMap.zero_apply, inner_zero_right, measure_empty]
    simp

/-- Idempotence, from multiplicativity at `B ∩ B`. -/
lemma proj_idem (P : ProjValMeasure' K ι) (B : Set ι) (hB : MeasurableSet B) :
    P.proj B hB * P.proj B hB = P.proj B hB := by
  rw [P.proj_inter B B hB hB]
  exact P.proj_congr (Set.inter_self B) (hB.inter hB) hB

/-- Self-adjointness: the diagonal is a real coercion, hence conjugation-fixed. -/
lemma isSelfAdjoint_proj (P : ProjValMeasure' K ι) (B : Set ι) (hB : MeasurableSet B) :
    IsSelfAdjoint (P.proj B hB) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  refine op_ext_of_inner_self fun ξ => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm (P.proj B hB ξ) ξ,
    P.inner_proj, Complex.conj_ofReal]

/-- Finite additivity on disjoint sets. -/
lemma proj_union (P : ProjValMeasure' K ι) {B₁ B₂ : Set ι}
    (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂) (hd : Disjoint B₁ B₂) :
    P.proj (B₁ ∪ B₂) (hB₁.union hB₂) = P.proj B₁ hB₁ + P.proj B₂ hB₂ :=
  op_ext_of_inner_self fun ξ => by
    rw [ContinuousLinearMap.add_apply, inner_add_right, P.inner_proj, P.inner_proj,
      P.inner_proj, measure_union hd hB₂,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    push_cast
    ring

/-- The fundamental quadratic identity `‖proj B ξ‖² = diag ξ B` — idempotence and
self-adjointness, two birds with one Stone. -/
lemma norm_sq_proj_apply (P : ProjValMeasure' K ι) (B : Set ι) (hB : MeasurableSet B)
    (ξ : K) : ‖P.proj B hB ξ‖ ^ 2 = ((P.diag ξ) B).toReal := by
  have h1 : ⟪P.proj B hB ξ, P.proj B hB ξ⟫_ℂ = ⟪ξ, P.proj B hB ξ⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right,
      (P.isSelfAdjoint_proj B hB).adjoint_eq, ← ContinuousLinearMap.mul_apply, P.proj_idem]
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), h1, P.inner_proj, RCLike.re_eq_complex_re, Complex.ofReal_re]

/-- Total mass: `diag ξ ι = ‖ξ‖²`. -/
lemma diag_univ_toReal (P : ProjValMeasure' K ι) (ξ : K) :
    ((P.diag ξ) Set.univ).toReal = ‖ξ‖ ^ 2 := by
  have h := P.inner_proj Set.univ MeasurableSet.univ ξ
  rw [P.proj_univ, ContinuousLinearMap.id_apply, inner_self_eq_norm_sq_to_K, ← coe_algebraMap] at h
  exact_mod_cast h.symm

/-- **A PVM is determined by its diagonal measures.** -/
theorem ext_of_diag {P Q : ProjValMeasure' K ι} (h : ∀ ξ : K, P.diag ξ = Q.diag ξ) : P = Q := by
  have hproj : P.proj = Q.proj := by
    funext B hB
    exact op_ext_of_inner_self fun ξ => by rw [P.inner_proj, Q.inner_proj, h ξ]
  obtain ⟨p, d, _, _, _, _⟩ := P
  obtain ⟨q, e, _, _, _, _⟩ := Q
  obtain rfl : p = q := hproj
  obtain rfl : d = e := funext h
  rfl

end ProjValMeasure'

end Spectra
