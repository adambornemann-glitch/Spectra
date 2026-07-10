/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Projection-valued measures on the Borel sets of `ℝ`

The bundled structure `ProjValMeasure H`, designed as the carrier type for the
keystone spectral theorem
`∃! P : ProjValMeasure H, (resolvent formula for A against P.diag)`.

## Design

The diagonal scalar measures are carried as **data** (`diag : H → Measure ℝ`),
welded to the projections by the single axiom `inner_proj`.  This buys:

* σ-additivity for free — `diag ξ` is a `Measure`, so no "extends to a measure"
  existential ever appears;
* a two-field extensionality (`ext`), hence the two characterizations
  `ext_of_diag` and `ext_of_proj`, which are the uniqueness engine for the
  keystone;
* finite additivity (`proj_union`), idempotence (`proj_idem`), self-adjointness
  (`isSelfAdjoint_proj`), and the contraction property (`norm_proj_apply_le`)
  as *theorems*, not axioms.

The axiom list is deliberately minimal: `inner_proj`, `proj_univ`, `proj_inter`,
and finiteness.  Everything classical about resolutions of the identity is
derivable, and a weaker structure means a stronger uniqueness statement
downstream.

## Main results

* `ProjValMeasure.ext_of_diag` : a PVM is determined by its diagonal measures
  (complex polarization — two birds with one Stone).
* `ProjValMeasure.ext_of_proj` : conversely, the projections determine the
  diagonal measures (finiteness cancels `toReal`).

## References

* Stone, "Linear Transformations in Hilbert Space" (1932), Chapter V
  (resolutions of the identity).
* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], §VII–VIII.
-/

open MeasureTheory Complex
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra

/-! ## Polarization: the diagonal determines the operator -/

omit [CompleteSpace H] in
/-- On a **complex** Hilbert space, an operator is determined by its diagonal
matrix elements `⟪ξ, T ξ⟫`.  (False over `ℝ` — a rotation by `π/2` of the plane
has vanishing diagonal.)  Mathlib's `ext_inner_map` carries the polarization;
we merely flip slots by conjugation. -/
lemma op_ext_of_inner_self {S T : H →L[ℂ] H}
    (h : ∀ ξ : H, ⟪ξ, S ξ⟫_ℂ = ⟪ξ, T ξ⟫_ℂ) : S = T := by
  refine ContinuousLinearMap.coe_injective ((ext_inner_map _ _).mp fun ξ => ?_)
  change ⟪S ξ, ξ⟫_ℂ = ⟪T ξ, ξ⟫_ℂ
  rw [← inner_conj_symm (S ξ) ξ, ← inner_conj_symm (T ξ) ξ, h ξ]

/-! ## The structure -/

/-- A **projection-valued measure** on the Borel sets of `ℝ`, acting on a complex
Hilbert space `H`.

The diagonal scalar measures `diag ξ = ⟪ξ, proj · ξ⟫` are carried as data and
welded to the operator field by `inner_proj`; consequently countable additivity
never needs to be stated — it lives inside `Measure ℝ`.  Idempotence,
self-adjointness, positivity, finite additivity, and `‖proj B ξ‖ ≤ ‖ξ‖` are all
theorems below. -/
structure ProjValMeasure (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The projection assigned to each Borel set. -/
  proj : ∀ B : Set ℝ, MeasurableSet B → (H →L[ℂ] H)
  /-- The diagonal scalar measures, carried as data. -/
  diag : H → Measure ℝ
  /-- Each diagonal measure is finite (its mass is `‖ξ‖ ^ 2`, by `diag_univ_toReal`). -/
  diag_finite : ∀ ξ : H, IsFiniteMeasure (diag ξ)
  /-- The weld: diagonal matrix elements of the projections are the diagonal measures. -/
  inner_proj : ∀ (B : Set ℝ) (hB : MeasurableSet B) (ξ : H),
    ⟪ξ, proj B hB ξ⟫_ℂ = (((diag ξ) B).toReal : ℂ)
  /-- The whole line carries the identity. -/
  proj_univ : proj Set.univ MeasurableSet.univ = ContinuousLinearMap.id ℂ H
  /-- Multiplicativity: intersection of sets is composition of projections. -/
  proj_inter : ∀ (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂),
    proj B₁ hB₁ * proj B₂ hB₂ = proj (B₁ ∩ B₂) (hB₁.inter hB₂)

namespace ProjValMeasure

instance instIsFiniteMeasureDiag (P : ProjValMeasure H) (ξ : H) :
    IsFiniteMeasure (P.diag ξ) :=
  P.diag_finite ξ

/-! ## The classical axioms, recovered as theorems -/

/-- The projections do not depend on the measurability witness — proof
irrelevance: the witness is not set in stone, only the set is. -/
lemma proj_congr (P : ProjValMeasure H) {B₁ B₂ : Set ℝ} (h : B₁ = B₂)
    (h₁ : MeasurableSet B₁) (h₂ : MeasurableSet B₂) :
    P.proj B₁ h₁ = P.proj B₂ h₂ := by
  subst h; rfl

@[simp]
lemma proj_empty (P : ProjValMeasure H) : P.proj ∅ MeasurableSet.empty = 0 :=
  op_ext_of_inner_self fun ξ => by
    rw [P.inner_proj, ContinuousLinearMap.zero_apply, inner_zero_right, measure_empty]
    simp

/-- Idempotence, from multiplicativity at `B ∩ B`. -/
lemma proj_idem (P : ProjValMeasure H) (B : Set ℝ) (hB : MeasurableSet B) :
    P.proj B hB * P.proj B hB = P.proj B hB := by
  rw [P.proj_inter B B hB hB]
  exact P.proj_congr (Set.inter_self B) (hB.inter hB) hB

/-- Self-adjointness: the diagonal is a real coercion, hence conjugation-fixed,
hence the operator equals its adjoint by polarization. -/
lemma isSelfAdjoint_proj (P : ProjValMeasure H) (B : Set ℝ) (hB : MeasurableSet B) :
    IsSelfAdjoint (P.proj B hB) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  refine op_ext_of_inner_self fun ξ => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm (P.proj B hB ξ) ξ,
    P.inner_proj, Complex.conj_ofReal]

/-- Finite additivity is already a theorem: the diagonal measures are measures,
and polarization lifts their additivity to the operators. -/
lemma proj_union (P : ProjValMeasure H) {B₁ B₂ : Set ℝ}
    (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂) (hd : Disjoint B₁ B₂) :
    P.proj (B₁ ∪ B₂) (hB₁.union hB₂) = P.proj B₁ hB₁ + P.proj B₂ hB₂ :=
  op_ext_of_inner_self fun ξ => by
    rw [ContinuousLinearMap.add_apply, inner_add_right, P.inner_proj, P.inner_proj,
      P.inner_proj, measure_union hd hB₂,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    push_cast
    ring

/-- The fundamental quadratic identity `‖proj B ξ‖ ^ 2 = diag ξ B` — idempotence
and self-adjointness, two birds with one Stone. -/
lemma norm_sq_proj_apply (P : ProjValMeasure H) (B : Set ℝ) (hB : MeasurableSet B)
    (ξ : H) :
    ‖P.proj B hB ξ‖ ^ 2 = ((P.diag ξ) B).toReal := by
  have h1 : ⟪P.proj B hB ξ, P.proj B hB ξ⟫_ℂ = ⟪ξ, P.proj B hB ξ⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right,
      (P.isSelfAdjoint_proj B hB).adjoint_eq, ← ContinuousLinearMap.mul_apply,
      P.proj_idem]
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), h1, P.inner_proj, RCLike.re_eq_complex_re,
    Complex.ofReal_re]

/-- Total mass: `diag ξ ℝ = ‖ξ‖ ^ 2`. -/
lemma diag_univ_toReal (P : ProjValMeasure H) (ξ : H) :
    ((P.diag ξ) Set.univ).toReal = ‖ξ‖ ^ 2 := by
  have h := P.inner_proj Set.univ MeasurableSet.univ ξ
  rw [P.proj_univ, ContinuousLinearMap.id_apply, inner_self_eq_norm_sq_to_K,
    ← coe_algebraMap] at h
  exact_mod_cast h.symm

/-- Every projection of the measure is a contraction — monotonicity of the
diagonal measure does all the work. -/
lemma norm_proj_apply_le (P : ProjValMeasure H) (B : Set ℝ) (hB : MeasurableSet B)
    (ξ : H) :
    ‖P.proj B hB ξ‖ ≤ ‖ξ‖ := by
  have hsq : ‖P.proj B hB ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
    rw [norm_sq_proj_apply, ← P.diag_univ_toReal ξ]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ B))
  calc ‖P.proj B hB ξ‖
      = Real.sqrt (‖P.proj B hB ξ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖ξ‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖ξ‖ := Real.sqrt_sq (norm_nonneg _)

/-! ## Extensionality: the keystone's uniqueness engine

A `ProjValMeasure` is determined by either of its two data fields.  The
uniqueness half of the spectral theorem will run:

  resolvent formula ⟹ equal Cauchy transforms ⟹ (scalar injectivity)
  equal `diag` ⟹ `ext_of_diag` ⟹ equal PVMs.  Stone-cold. -/

/-- Two PVMs with the same data fields are equal; the remaining fields are
propositions. -/
lemma ext {P Q : ProjValMeasure H} (hproj : P.proj = Q.proj)
    (hdiag : P.diag = Q.diag) : P = Q := by
  obtain ⟨p, d, _, _, _, _⟩ := P
  obtain ⟨q, e, _, _, _, _⟩ := Q
  obtain rfl : p = q := hproj
  obtain rfl : d = e := hdiag
  rfl

/-- **A projection-valued measure is determined by its diagonal measures.**
The diagonal matrix elements agree by `inner_proj`, and complex polarization
recovers the operators. -/
theorem ext_of_diag {P Q : ProjValMeasure H}
    (h : ∀ ξ : H, P.diag ξ = Q.diag ξ) : P = Q := by
  refine ext ?_ (funext h)
  funext B hB
  exact op_ext_of_inner_self fun ξ => by rw [P.inner_proj, Q.inner_proj, h ξ]

/-- Conversely, **the projections determine the diagonal measures**: finiteness
lets `toReal` be cancelled on every Borel set. -/
theorem ext_of_proj {P Q : ProjValMeasure H}
    (h : ∀ (B : Set ℝ) (hB : MeasurableSet B), P.proj B hB = Q.proj B hB) :
    P = Q := by
  refine ext_of_diag fun ξ => Measure.ext fun B hB => ?_
  have hr : (((P.diag ξ) B).toReal : ℂ) = (((Q.diag ξ) B).toReal : ℂ) := by
    rw [← P.inner_proj B hB ξ, ← Q.inner_proj B hB ξ, h B hB]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    (by exact_mod_cast hr)

theorem ext_iff_diag {P Q : ProjValMeasure H} :
    P = Q ↔ ∀ ξ : H, P.diag ξ = Q.diag ξ :=
  ⟨fun h ξ => by rw [h], ext_of_diag⟩

theorem ext_iff_proj {P Q : ProjValMeasure H} :
    P = Q ↔ ∀ (B : Set ℝ) (hB : MeasurableSet B), P.proj B hB = Q.proj B hB :=
  ⟨fun h B hB => by rw [h], ext_of_proj⟩

end ProjValMeasure

end Spectra
