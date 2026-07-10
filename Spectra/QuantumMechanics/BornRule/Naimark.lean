/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.BornRule.POVM
import Spectra.ProjValMeasure.General
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Naimark's dilation theorem (discrete case)

**Every discrete POVM is the compression of a PVM.**  For a countable family of positive effects
`E : κ → (H →L[ℂ] H)` resolving the identity (`∑' k, E k = 1`) — i.e. the discrete POVMs built by
`POVM.ofEffects` — there is a larger Hilbert space `K`, a projection-valued measure `P` on `K`, and
an isometry `V : H → K` with

  `M(B) = V⋆ ∘ P(B) ∘ V`   for every measurable `B ⊆ κ`,

where `M = ofEffects E`.  This is the structural theorem justifying the phrase "generalized
measurement": a POVM is exactly what a sharp (projective) measurement on a larger space looks like
after restricting to `H`.

## The construction

The carrier is the ℓ²-direct-sum of `κ`-many copies of `H`,
`NaimarkSpace H κ := lp (fun _ : κ => H) 2`.

* **`P` (`naimarkPVM`).**  The *diagonal* projection-valued measure: `P(B)` is the
  coordinate-**restriction** `lpRestrict B` that zeroes every coordinate outside `B`.  (It is *not*
  a norm-convergent sum of the rank-`H` coordinate projections — those converge only strongly — so
  it is built directly via `LinearMap.mkContinuous`.)  Its diagonal measure is `∑' k, ‖η k‖² δ_k`,
  and `proj_inter`/`proj_univ` are `Set.indicator_indicator`/`Set.indicator_univ`.

* **`V` (`naimarkV`).**  `V ψ = (√Eₖ ψ)ₖ`, using the operator square root `CFC.sqrt` of each
  positive effect.  It lands in `ℓ²` because `∑ₖ ‖√Eₖ ψ‖² = ∑ₖ ⟪ψ, Eₖ ψ⟫ = ‖ψ‖²` (resolution of
  the identity), which is also exactly why `V` is an **isometry**.

* **The compression `naimark_effect_eq`.**  `⟪V ψ, P(B) (V ψ)⟫ = ∑_{k∈B} ⟪√Eₖ ψ, √Eₖ ψ⟫ =
  ∑_{k∈B} ⟪ψ, Eₖ ψ⟫ = ⟪ψ, M(B) ψ⟫` (using `CFC.sqrt_mul_sqrt_self` and `√Eₖ` self-adjoint), and
  `op_ext_of_inner_self` upgrades the diagonal-form equality to the operator identity.

## Scope

This is the **countable / discrete** Naimark theorem, which covers every `ofEffects`-style POVM
(state discrimination, informationally-complete measurements, the two-outcome `binaryPOVM`).  The
fully general σ-additive *operator-valued-measure* Naimark theorem (uncountable outcome space) needs
an operator-valued-measure topology the library deliberately avoids, and remains out of scope.

The dilating PVM is a `Spectra.ProjValMeasure'` (the projection-valued measure of
`ProjValMeasure/General.lean`, over an arbitrary Hilbert space and measurable outcome space).

## Implementation notes

The isometry ships as two declarations.  `naimarkV` is the bundled `LinearIsometry`
(`H →ₗᵢ[ℂ] NaimarkSpace H κ`), where the norm-preservation obligation is naturally discharged;
`naimarkVclm` is its `ContinuousLinearMap` coercion.  The `→L[ℂ]` bundle is the one the compression
statements need, because `naimark_effect_eq`/`inner_compression_eq` use the `.adjoint` API (`V⋆`),
which is available on continuous linear maps but not on the linear-isometry bundle.  The split is
therefore deliberate, not redundant.

## References

* M. Naimark, *On a representation of additive operator set functions* (1943).
* [Paulsen, *Completely Bounded Maps and Operator Algebras*], Ch. 4 (Stinespring/Naimark).
* [Heinosaari, Ziman, *The Mathematical Language of Quantum Theory*], §3.4.
-/

open MeasureTheory Complex
open scoped InnerProductSpace ENNReal
open Spectra

namespace Spectra.QuantumMechanics.BornRule

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {κ : Type v} [Countable κ]

/-- The Naimark dilation carrier: the ℓ²-direct-sum of `κ`-many copies of `H`. -/
abbrev NaimarkSpace (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (κ : Type*) := lp (fun _ : κ => H) 2

/-- Restriction of an `lp` element to the coordinates in `B`, as a linear map.  File-local
scaffolding for the continuous `lpRestrict`. -/
private noncomputable def lpRestrictₗ (B : Set κ) : NaimarkSpace H κ →ₗ[ℂ] NaimarkSpace H κ where
  toFun η := ⟨Set.indicator B (⇑η),
    (lp.memℓp η).mono' (f := Set.indicator B (⇑η)) (fun k => by
      classical
      rw [Set.indicator_apply]; split_ifs <;> simp)⟩
  map_add' η₁ η₂ := by
    classical
    apply lp.ext
    simp only [lp.coeFn_add]
    ext k
    simp only [Set.indicator_apply, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c η := by
    classical
    apply lp.ext
    simp only [lp.coeFn_smul, RingHom.id_apply]
    ext k
    simp only [Set.indicator_apply, Pi.smul_apply]
    split_ifs <;> simp

omit [Countable κ] in
@[simp] private lemma lpRestrictₗ_coeFn (B : Set κ) (η : NaimarkSpace H κ) :
    ⇑(lpRestrictₗ B η) = Set.indicator B (⇑η) := rfl

/-! ## §1  The coordinate-restriction projection -/

omit [Countable κ] in
private lemma lp_indicator_norm_le (B : Set κ) (η : NaimarkSpace H κ) (k : κ) :
    ‖Set.indicator B (⇑η) k‖ ≤ ‖η k‖ := by
  classical
  rw [Set.indicator_apply]; split_ifs <;> simp

/-- The coordinate-restriction operator `lpRestrict B` as a continuous linear contraction. -/
noncomputable def lpRestrict (B : Set κ) : NaimarkSpace H κ →L[ℂ] NaimarkSpace H κ :=
  LinearMap.mkContinuous (lpRestrictₗ B) 1 fun η => by
    rw [one_mul]
    refine lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg η) ?_
    rw [lp.norm_rpow_eq_tsum (by norm_num) η]
    refine Summable.tsum_le_tsum (fun k => ?_) ?_ ((lp.memℓp η).summable (by norm_num))
    · rw [lpRestrictₗ_coeFn]
      exact Real.rpow_le_rpow (norm_nonneg _) (lp_indicator_norm_le B η k) ENNReal.toReal_nonneg
    · have hmem := (lp.memℓp (lpRestrictₗ B η)).summable (p := 2) (by norm_num)
      simpa using hmem

omit [Countable κ] in
@[simp] lemma lpRestrict_coeFn (B : Set κ) (η : NaimarkSpace H κ) :
    ⇑(lpRestrict B η) = Set.indicator B (⇑η) := rfl

/-! ## §2  The dilating projection-valued measure on the carrier -/

variable [MeasurableSpace κ]

/-- The diagonal measure of `η` on the carrier: `∑' k, ‖η k‖² δ_k`. -/
noncomputable def naimarkDiag (η : NaimarkSpace H κ) : Measure κ :=
  Measure.sum (fun k => ENNReal.ofReal (‖η k‖ ^ 2) • Measure.dirac k)

omit [Countable κ] in
private lemma naimarkDiag_apply (η : NaimarkSpace H κ) {B : Set κ} (hB : MeasurableSet B) :
    (naimarkDiag η) B = ∑' k, Set.indicator B (fun k => ENNReal.ofReal (‖η k‖ ^ 2)) k := by
  rw [naimarkDiag, Measure.sum_apply _ hB]
  refine tsum_congr fun k => ?_
  rw [Measure.smul_apply, MeasureTheory.Measure.dirac_apply' k hB, smul_eq_mul]
  by_cases hk : k ∈ B
  · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk]; simp
  · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk]; simp

omit [Countable κ] [MeasurableSpace κ] in
private lemma naimarkDiag_summable (η : NaimarkSpace H κ) :
    Summable (fun k => ‖η k‖ ^ 2) := by
  have hmem := (lp.memℓp η).summable (p := 2) (by norm_num)
  simpa using hmem

omit [Countable κ] in
private lemma naimarkDiag_finite (η : NaimarkSpace H κ) : IsFiniteMeasure (naimarkDiag η) := by
  refine ⟨?_⟩
  rw [naimarkDiag_apply η MeasurableSet.univ]
  simp only [Set.indicator_univ]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) (naimarkDiag_summable η)]
  exact ENNReal.ofReal_lt_top

omit [Countable κ] in
/-- The weld: `⟪η, lpRestrict B η⟫ = ((naimarkDiag η B).toReal : ℂ)`. -/
private lemma naimark_inner_proj (B : Set κ) (hB : MeasurableSet B) (η : NaimarkSpace H κ) :
    ⟪η, lpRestrict B η⟫_ℂ = (((naimarkDiag η) B).toReal : ℂ) := by
  rw [lp.inner_eq_tsum]
  have hterm : ∀ k, ⟪η k, (lpRestrict B η) k⟫_ℂ
      = ((Set.indicator B (fun k => (‖η k‖ ^ 2 : ℝ)) k : ℝ) : ℂ) := fun k => by
    rw [lpRestrict_coeFn]
    by_cases hk : k ∈ B
    · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk, inner_zero_right,
        Complex.ofReal_zero]
  rw [tsum_congr hterm, ← Complex.ofReal_tsum, naimarkDiag_apply η hB]
  congr 1
  have hfin : ∀ k, Set.indicator B (fun k => ENNReal.ofReal (‖η k‖ ^ 2)) k ≠ ⊤ := fun k => by
    by_cases hk : k ∈ B
    · rw [Set.indicator_of_mem hk]; exact ENNReal.ofReal_ne_top
    · rw [Set.indicator_of_notMem hk]; exact ENNReal.zero_ne_top
  rw [ENNReal.tsum_toReal_eq hfin]
  refine tsum_congr fun k => ?_
  by_cases hk : k ∈ B
  · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk, ENNReal.toReal_ofReal (sq_nonneg _)]
  · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk, ENNReal.toReal_zero]

/-- The canonical **diagonal projection-valued measure** on the Naimark carrier: `P(B)` restricts
to the coordinates in `B`. -/
noncomputable def naimarkPVM : ProjValMeasure' (NaimarkSpace H κ) κ where
  proj B _ := lpRestrict B
  diag := naimarkDiag
  diag_finite := naimarkDiag_finite
  inner_proj := naimark_inner_proj
  proj_univ := by
    ext η : 1
    apply lp.ext
    simp [lpRestrict_coeFn, Set.indicator_univ]
  proj_inter := by
    intro B₁ B₂ _hB₁ _hB₂
    ext η : 1
    apply lp.ext
    simp only [ContinuousLinearMap.mul_apply, lpRestrict_coeFn, Set.indicator_indicator]

/-! ## §3  The isometry `V : ψ ↦ (√Eₖ ψ)ₖ` -/

omit [CompleteSpace H] [Countable κ] [MeasurableSpace κ] in
/-- `hpos k ⟹ 0 ≤ E k`. -/
private lemma nonneg_of_isPositive {E : κ → (H →L[ℂ] H)} (hpos : ∀ k, (E k).IsPositive)
    (k : κ) : (0 : H →L[ℂ] H) ≤ E k :=
  (ContinuousLinearMap.nonneg_iff_isPositive (E k)).mpr (hpos k)

omit [Countable κ] [MeasurableSpace κ] in
/-- The core coordinate identity: `⟪√Eₖ ψ, √Eₖ ψ⟫ = ⟪ψ, Eₖ ψ⟫`. -/
private lemma inner_sqrt_self {E : κ → (H →L[ℂ] H)} (hpos : ∀ k, (E k).IsPositive)
    (k : κ) (ψ : H) :
    ⟪CFC.sqrt (E k) ψ, CFC.sqrt (E k) ψ⟫_ℂ = ⟪ψ, E k ψ⟫_ℂ := by
  have hsa : IsSelfAdjoint (CFC.sqrt (E k)) :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (E k))
  rw [← ContinuousLinearMap.adjoint_inner_right, hsa.adjoint_eq,
    ← ContinuousLinearMap.mul_apply, CFC.sqrt_mul_sqrt_self (E k) (nonneg_of_isPositive hpos k)]

omit [Countable κ] [MeasurableSpace κ] in
/-- `‖√Eₖ ψ‖² = re ⟪ψ, Eₖ ψ⟫`. -/
private lemma norm_sq_sqrt {E : κ → (H →L[ℂ] H)} (hpos : ∀ k, (E k).IsPositive)
    (k : κ) (ψ : H) :
    ‖CFC.sqrt (E k) ψ‖ ^ 2 = (⟪ψ, E k ψ⟫_ℂ).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_sqrt_self hpos k ψ, RCLike.re_eq_complex_re]

omit [CompleteSpace H] [Countable κ] [MeasurableSpace κ] in
/-- The real series `k ↦ re ⟪ψ, Eₖ ψ⟫` is summable. -/
private lemma summable_re_quadForm {E : κ → (H →L[ℂ] H)} (hsum : ∑' k, E k = 1) (ψ : H) :
    Summable (fun k => (⟪ψ, E k ψ⟫_ℂ).re) := by
  have hSE : Summable E := POVM.summable_ofEffects hsum
  have h1 : Summable (fun k => (E k) ψ) := hSE.mapL (ContinuousLinearMap.apply ℂ H ψ)
  have h2 : Summable (fun k => ⟪ψ, (E k) ψ⟫_ℂ) := h1.mapL (innerSL ℂ ψ)
  exact h2.mapL Complex.reCLM

omit [Countable κ] [MeasurableSpace κ] in
/-- `fun k => √Eₖ ψ` is in `ℓ²`. -/
private lemma memℓp_sqrt {E : κ → (H →L[ℂ] H)} (hpos : ∀ k, (E k).IsPositive)
    (hsum : ∑' k, E k = 1) (ψ : H) :
    Memℓp (fun k => CFC.sqrt (E k) ψ) 2 := by
  apply memℓp_gen
  have hconv : (fun k => ‖CFC.sqrt (E k) ψ‖ ^ (2 : ℝ≥0∞).toReal)
      = (fun k => (⟪ψ, E k ψ⟫_ℂ).re) := by
    funext k
    rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num, Real.rpow_two, norm_sq_sqrt hpos k ψ]
  rw [hconv]
  exact summable_re_quadForm hsum ψ

omit [CompleteSpace H] [Countable κ] [MeasurableSpace κ] in
/-- Pushing `ψ` and the inner product through the operator tsum:
`∑' k, ⟪ψ, Eₖ ψ⟫ = ⟪ψ, (∑' k, Eₖ) ψ⟫`. -/
private lemma tsum_inner_quadForm {E : κ → (H →L[ℂ] H)} (hSE : Summable E) (ψ : H) :
    ∑' k, ⟪ψ, (E k) ψ⟫_ℂ = ⟪ψ, (∑' k, E k) ψ⟫_ℂ := by
  have happ : (∑' k, E k) ψ = ∑' k, (E k) ψ :=
    (hSE.hasSum.mapL (ContinuousLinearMap.apply ℂ H ψ)).tsum_eq.symm
  rw [happ]
  have hsumapp : Summable (fun k => (E k) ψ) := hSE.mapL (ContinuousLinearMap.apply ℂ H ψ)
  exact (hsumapp.hasSum.mapL (innerSL ℂ ψ)).tsum_eq

omit [CompleteSpace H] [Countable κ] [MeasurableSpace κ] in
/-- `∑' k, re ⟪ψ, Eₖ ψ⟫ = ‖ψ‖²` from `∑' k, Eₖ = 1`. -/
private lemma tsum_re_quadForm_eq {E : κ → (H →L[ℂ] H)} (hsum : ∑' k, E k = 1) (ψ : H) :
    ∑' k, (⟪ψ, E k ψ⟫_ℂ).re = ‖ψ‖ ^ 2 := by
  have hSE : Summable E := POVM.summable_ofEffects hsum
  have hsuminner : Summable (fun k => ⟪ψ, (E k) ψ⟫_ℂ) :=
    (hSE.mapL (ContinuousLinearMap.apply ℂ H ψ)).mapL (innerSL ℂ ψ)
  rw [← Complex.re_tsum hsuminner, tsum_inner_quadForm hSE ψ, hsum,
    ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The **Naimark isometry** `V : ψ ↦ (√Eₖ ψ)ₖ`. -/
noncomputable def naimarkV (E : κ → (H →L[ℂ] H)) (hpos : ∀ k, (E k).IsPositive)
    (hsum : ∑' k, E k = 1) : H →ₗᵢ[ℂ] NaimarkSpace H κ where
  toFun ψ := ⟨fun k => CFC.sqrt (E k) ψ, memℓp_sqrt hpos hsum ψ⟩
  map_add' ψ₁ ψ₂ := by
    apply lp.ext
    simp only [lp.coeFn_add]
    funext k
    simp [map_add]
  map_smul' c ψ := by
    apply lp.ext
    simp only [lp.coeFn_smul]
    funext k
    simp [map_smul]
  norm_map' ψ := by
    change ‖(⟨fun k => CFC.sqrt (E k) ψ, memℓp_sqrt hpos hsum ψ⟩ : NaimarkSpace H κ)‖ = ‖ψ‖
    have hnonneg : (0 : ℝ) ≤ ‖ψ‖ := norm_nonneg ψ
    set v : NaimarkSpace H κ := ⟨fun k => CFC.sqrt (E k) ψ, memℓp_sqrt hpos hsum ψ⟩ with _hv
    have hVnonneg : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
    have hsq : ‖v‖ ^ (2 : ℝ≥0∞).toReal = ‖ψ‖ ^ 2 := by
      rw [lp.norm_rpow_eq_tsum (by norm_num) v]
      have hcoord : ∀ k, ‖v k‖ ^ (2 : ℝ≥0∞).toReal = (⟪ψ, E k ψ⟫_ℂ).re := fun k => by
        rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num, Real.rpow_two]
        change ‖CFC.sqrt (E k) ψ‖ ^ 2 = (⟪ψ, E k ψ⟫_ℂ).re
        exact norm_sq_sqrt hpos k ψ
      rw [tsum_congr hcoord, tsum_re_quadForm_eq hsum ψ]
    rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num, Real.rpow_two] at hsq
    nlinarith [hsq, hVnonneg, hnonneg]

/-- The Naimark isometry as a continuous linear map. -/
noncomputable def naimarkVclm (E : κ → (H →L[ℂ] H)) (hpos : ∀ k, (E k).IsPositive)
    (hsum : ∑' k, E k = 1) : H →L[ℂ] NaimarkSpace H κ :=
  (naimarkV E hpos hsum).toContinuousLinearMap

omit [Countable κ] [MeasurableSpace κ] in
@[simp] lemma naimarkVclm_apply (E : κ → (H →L[ℂ] H)) (hpos : ∀ k, (E k).IsPositive)
    (hsum : ∑' k, E k = 1) (ψ : H) :
    (naimarkVclm E hpos hsum ψ : ∀ _ : κ, H) = fun k => CFC.sqrt (E k) ψ := rfl

omit [Countable κ] [MeasurableSpace κ] in
lemma naimarkVclm_isometry (E : κ → (H →L[ℂ] H)) (hpos : ∀ k, (E k).IsPositive)
    (hsum : ∑' k, E k = 1) : Isometry (naimarkVclm E hpos hsum) := by
  have h : ⇑(naimarkVclm E hpos hsum) = ⇑(naimarkV E hpos hsum) :=
    (naimarkV E hpos hsum).coe_toContinuousLinearMap
  rw [show Isometry (naimarkVclm E hpos hsum) ↔ Isometry ⇑(naimarkVclm E hpos hsum) from Iff.rfl,
    h]
  exact (naimarkV E hpos hsum).isometry

/-! ## §4  The compression identity and Naimark's theorem -/
omit [Countable κ] [MeasurableSpace κ] in
/-- The compression of the diagonal PVM along `V` recovers the POVM effect:
both `⟪V ψ, P(B) (V ψ)⟫` and `⟪ψ, M(B) ψ⟫` equal `∑' k, B.indicator (k ↦ ⟪ψ, Eₖ ψ⟫) k`. -/
private lemma inner_compression_eq (E : κ → (H →L[ℂ] H)) (hpos : ∀ k, (E k).IsPositive)
    (hsum : ∑' k, E k = 1) (B : Set κ) (ψ : H) :
    ⟪naimarkVclm E hpos hsum ψ, lpRestrict B (naimarkVclm E hpos hsum ψ)⟫_ℂ
      = ⟪ψ, (∑' k, Set.indicator B E k) ψ⟫_ℂ := by
  classical
  have hSE : Summable E := POVM.summable_ofEffects hsum
  -- RHS as a coordinate tsum
  have hRHS : ⟪ψ, (∑' k, Set.indicator B E k) ψ⟫_ℂ
      = ∑' k, Set.indicator B (fun k => ⟪ψ, E k ψ⟫_ℂ) k := by
    have hBsum : Summable (Set.indicator B E) := hSE.indicator B
    have happ : (∑' k, Set.indicator B E k) ψ = ∑' k, (Set.indicator B E k) ψ :=
      (hBsum.hasSum.mapL (ContinuousLinearMap.apply ℂ H ψ)).tsum_eq.symm
    rw [happ]
    have hSummApp : Summable (fun k => (Set.indicator B E k) ψ) :=
      hBsum.mapL (ContinuousLinearMap.apply ℂ H ψ)
    have hinner : ⟪ψ, ∑' k, (Set.indicator B E k) ψ⟫_ℂ
        = ∑' k, ⟪ψ, (Set.indicator B E k) ψ⟫_ℂ :=
      (hSummApp.hasSum.mapL (innerSL ℂ ψ)).tsum_eq.symm
    rw [hinner]
    refine tsum_congr fun k => ?_
    by_cases hk : k ∈ B
    · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk]
    · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk,
        ContinuousLinearMap.zero_apply, inner_zero_right]
  -- LHS as a coordinate tsum
  have hLHS : ⟪naimarkVclm E hpos hsum ψ, lpRestrict B (naimarkVclm E hpos hsum ψ)⟫_ℂ
      = ∑' k, Set.indicator B (fun k => ⟪ψ, E k ψ⟫_ℂ) k := by
    rw [lp.inner_eq_tsum]
    refine tsum_congr fun k => ?_
    rw [lpRestrict_coeFn]
    have hVk : (naimarkVclm E hpos hsum ψ) k = CFC.sqrt (E k) ψ := rfl
    by_cases hk : k ∈ B
    · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk, hVk, inner_sqrt_self hpos k ψ]
    · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk, inner_zero_right]
  rw [hLHS, hRHS]

omit [Countable κ] in
/-- **The compression identity** `M(B) = V⋆ P(B) V`: the POVM effect `M(B)` is the `V⋆`-compression
of the dilating PVM's projection `P(B)`. -/
theorem naimark_effect_eq (E : κ → (H →L[ℂ] H)) (hpos : ∀ k, (E k).IsPositive)
    (hsum : ∑' k, E k = 1) (B : Set κ) (hB : MeasurableSet B) :
    (POVM.ofEffects E hpos hsum).effect B hB
      = (naimarkVclm E hpos hsum).adjoint.comp
          (((naimarkPVM (κ := κ)).proj B hB).comp (naimarkVclm E hpos hsum)) := by
  refine op_ext_of_inner_self fun ψ => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  change ⟪ψ, (∑' k, Set.indicator B E k) ψ⟫_ℂ
    = ⟪naimarkVclm E hpos hsum ψ, lpRestrict B (naimarkVclm E hpos hsum ψ)⟫_ℂ
  rw [inner_compression_eq E hpos hsum B ψ]

omit [Countable κ] in
/-- **Naimark dilation (discrete case).** A resolution of the identity `∑' k, E k = 1` by positive
effects on `H` is the compression `V⋆ P(·) V` of a projection-valued measure `P` on the larger
Hilbert space `NaimarkSpace H κ`, along an isometry `V`. -/
theorem naimark_dilation (E : κ → (H →L[ℂ] H)) (hpos : ∀ k, (E k).IsPositive)
    (hsum : ∑' k, E k = 1) :
    ∃ (K : Type (max u v)) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
      (_ : CompleteSpace K) (V : H →L[ℂ] K) (P : ProjValMeasure' K κ),
      Isometry V ∧ ∀ (B : Set κ) (hB : MeasurableSet B),
        (POVM.ofEffects E hpos hsum).effect B hB = V.adjoint.comp ((P.proj B hB).comp V) :=
  ⟨NaimarkSpace H κ, inferInstance, inferInstance, inferInstance, naimarkVclm E hpos hsum,
    naimarkPVM, naimarkVclm_isometry E hpos hsum, naimark_effect_eq E hpos hsum⟩

end Spectra.QuantumMechanics.BornRule
