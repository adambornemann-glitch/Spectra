/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.BornRule.Mixed
import Mathlib.Analysis.InnerProductSpace.Positive
/-!
# Generalized measurements: POVMs and the Born rule

A **positive operator-valued measure** (POVM) on an outcome space `(ι, 𝓜)` assigns to each
measurable `B ⊆ ι` an **effect** `M(B)` — a positive operator with `0 ≤ M(B) ≤ I` — additively
and with `M(ι) = I`.  It is the model of a generalized (unsharp) measurement; the projective
measurements of `ProjValMeasure` are the special case where every effect is a projection.

## Design: a POVM is a `ProjValMeasure` minus multiplicativity

`ProjValMeasure` carried the diagonal scalar measures `diag : H → Measure ℝ` as data, welded to
the operators by `inner_proj`, and had two structural axioms beyond the weld: `proj_univ`
(normalization) and `proj_inter` (multiplicativity, `E(B₁)E(B₂) = E(B₁∩B₂)`).  **A POVM keeps the
weld and `_univ`, and drops `_inter`** — generalizing the outcome space from `(ℝ, Borel)` to an
arbitrary `[MeasurableSpace ι]`.

The data-carrying weld pays off exactly as before.  Because `inner_effect` welds `⟪ξ, M(B) ξ⟫` to
the value of a *measure*, which is nonnegative, each effect is **positive** with no extra axiom;
and `M(B) ≤ M(ι) = I` follows from additivity, giving the effect property `0 ≤ M(B) ≤ I` as a
theorem.  The only `ProjValMeasure` facts that *don't* survive are the ones that used `proj_inter`:
idempotence `E² = E` and the projective norm identity `‖E(B)ξ‖² = ⟪ξ, E(B)ξ⟫`.  Everything else —
self-adjointness, finite additivity, the mass `‖ξ‖²`, `ext_of_diag` — ports verbatim.

## The Born rule is unchanged

It never used multiplicativity.  For a POVM `M`:
* pure state `ψ`: the outcome law is `M.diag ψ` (mass `‖ψ‖²`); `(M.diag ψ) B = ⟪ψ, M(B) ψ⟫`;
* mixed state `ρ`: `bornMeasurePOVM M ρ = Measure.sum (fun i => ρ.weight i • M.diag (ρ.state i))`,
  exactly the mixture used for PVMs;
* trace form: `(ρ.toState M(B)) = Tr(ρ M(B))` via the same `toState` bridge of `Mixed.lean`.

This is why the Born-rule layer factors through the `diag` field alone (see the abstraction note
in §6): PVM and POVM share it.

## Mathlib used

`MeasureTheory.Measure(.sum/.smul_apply)`, `ContinuousLinearMap.IsPositive`
(`Mathlib.Analysis.InnerProductSpace.Positive`), and — for the order `0 ≤ M(B) ≤ 1` — the
`StarOrderedRing` structure on the C*-algebra `H →L[ℂ] H`.  No operator-valued-measure topology
and no Naimark dilation are needed for any of the above.

## References

* [Busch, Lahti, Mittelstaedt, *The Quantum Theory of Measurement*], §§II–III (effects, POVMs).
* [Heinosaari, Ziman, *The Mathematical Language of Quantum Theory*], Ch. 3.
* M. Naimark, *On a representation of additive operator set functions* (1943) — the dilation
  theorem (flagged, §6).

## Layout

§1 the structure and its effect calculus; §2–§3 the two constructors (`ofEffects` from a discrete
family of effects, `toPOVM` from a sharp `ProjValMeasure`); §4 the Born rule; §5 a capstone — the
two-outcome measurement — tying the three strands together; §6 flags for later work.
-/

open MeasureTheory Complex
open scoped InnerProductSpace ENNReal
open Spectra Spectra.ProjValMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [MeasurableSpace ι]

namespace Spectra

/-! ## §1  The POVM structure -/

/-- A **positive operator-valued measure** on the measurable space `(ι, 𝓜)`, acting on `H`.

Exactly `ProjValMeasure` with the outcome space generalized and the multiplicativity axiom
`proj_inter` removed.  The diagonal scalar measures `diag ξ` are carried as data and welded to the
effects by `inner_effect`; countable additivity therefore lives inside `Measure ι` and is never
restated, and positivity/self-adjointness/the effect bound are theorems (proved below in this
section). -/
structure POVM (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ι : Type*) [MeasurableSpace ι] where
  /-- The effect assigned to each measurable set. -/
  effect : ∀ B : Set ι, MeasurableSet B → (H →L[ℂ] H)
  /-- The diagonal scalar measures, carried as data. -/
  diag : H → Measure ι
  /-- Each diagonal measure is finite (mass `‖ξ‖²`, by `diag_univ_toReal`). -/
  diag_finite : ∀ ξ : H, IsFiniteMeasure (diag ξ)
  /-- The weld: diagonal matrix elements of the effects are the diagonal measures. -/
  inner_effect : ∀ (B : Set ι) (hB : MeasurableSet B) (ξ : H),
    ⟪ξ, effect B hB ξ⟫_ℂ = (((diag ξ) B).toReal : ℂ)
  /-- Normalization: the whole space carries the identity, `M(ι) = I`. -/
  effect_univ : effect Set.univ MeasurableSet.univ = ContinuousLinearMap.id ℂ H

namespace POVM

instance instIsFiniteMeasureDiag (M : POVM H ι) (ξ : H) : IsFiniteMeasure (M.diag ξ) :=
  M.diag_finite ξ

/-! ### Facts that port verbatim from `ProjValMeasure` (no `_inter` used) -/

/-- `[done — ports verbatim]` Effects do not depend on the measurability witness. -/
lemma effect_congr (M : POVM H ι) {B₁ B₂ : Set ι} (h : B₁ = B₂)
    (h₁ : MeasurableSet B₁) (h₂ : MeasurableSet B₂) :
    M.effect B₁ h₁ = M.effect B₂ h₂ := by subst h; rfl

/-- `[done — ports verbatim]` `M(∅) = 0`.  Proof: `op_ext_of_inner_self` + `measure_empty`. -/
@[simp] lemma effect_empty (M : POVM H ι) : M.effect ∅ MeasurableSet.empty = 0 :=
  op_ext_of_inner_self fun ξ => by
    rw [M.inner_effect, ContinuousLinearMap.zero_apply, inner_zero_right, measure_empty]
    simp

/-- `[done — ports verbatim from `isSelfAdjoint_proj`]` Each effect is self-adjoint: its diagonal
is a real coercion, hence conjugation-fixed, hence (polarization) the operator is self-adjoint. -/
lemma isSelfAdjoint_effect (M : POVM H ι) (B : Set ι) (hB : MeasurableSet B) :
    IsSelfAdjoint (M.effect B hB) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  refine op_ext_of_inner_self fun ξ => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm (M.effect B hB ξ) ξ,
    M.inner_effect, Complex.conj_ofReal]

/-- `[done — ports verbatim from `proj_union`]` Finite additivity on disjoint sets. -/
lemma effect_union (M : POVM H ι) {B₁ B₂ : Set ι}
    (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂) (hd : Disjoint B₁ B₂) :
    M.effect (B₁ ∪ B₂) (hB₁.union hB₂) = M.effect B₁ hB₁ + M.effect B₂ hB₂ :=
  op_ext_of_inner_self fun ξ => by
    rw [ContinuousLinearMap.add_apply, inner_add_right, M.inner_effect, M.inner_effect,
      M.inner_effect, measure_union hd hB₂,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    push_cast
    ring

/-- `[done — ports verbatim from `diag_univ_toReal`]` Total mass `diag ξ ι = ‖ξ‖²`. -/
lemma diag_univ_toReal (M : POVM H ι) (ξ : H) : ((M.diag ξ) Set.univ).toReal = ‖ξ‖ ^ 2 := by
  have h := M.inner_effect Set.univ MeasurableSet.univ ξ
  rw [M.effect_univ, ContinuousLinearMap.id_apply, inner_self_eq_norm_sq_to_K,
    ← coe_algebraMap] at h
  exact_mod_cast h.symm

/-! ### Facts new to POVMs (positivity and the effect bound)

These replace the projective facts (`proj_idem`, `norm_sq_proj_apply`) that `_inter` would have
given.  They are *weaker* but exactly what an effect needs. -/

/-- `[done — free from the weld]` Each effect is **positive**.  Because `inner_effect` welds the
diagonal to a measure value `(diag ξ B).toReal ≥ 0`, the quadratic form is nonnegative; with
`isSelfAdjoint_effect` this is `ContinuousLinearMap.IsPositive`.
SIGNATURE TO VERIFY: Mathlib's `IsPositive` uses `reApplyInnerSelf x = re ⟪T x, x⟫`; reconcile the
slot order with the `⟪ξ, T ξ⟫` of `inner_effect` (equal real parts by conjugation). -/
lemma isPositive_effect (M : POVM H ι) (B : Set ι) (hB : MeasurableSet B) :
    (M.effect B hB).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff']
  refine ⟨M.isSelfAdjoint_effect B hB, fun x => ?_⟩
  have h : ⟪M.effect B hB x, x⟫_ℂ = (((M.diag x) B).toReal : ℂ) := by
    rw [← inner_conj_symm (M.effect B hB x) x, M.inner_effect, Complex.conj_ofReal]
  rw [h]
  exact_mod_cast ENNReal.toReal_nonneg

/-- `[done]` **Monotonicity.**  `B₁ ⊆ B₂ ⟹ M(B₁) ≤ M(B₂)` in the C*-order: the difference is
`M(B₂ \ B₁)`, a positive effect, by `effect_union` and `isPositive_effect`. -/
lemma effect_mono (M : POVM H ι) {B₁ B₂ : Set ι}
    (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂) (h : B₁ ⊆ B₂) :
    M.effect B₁ hB₁ ≤ M.effect B₂ hB₂ := by
  rw [ContinuousLinearMap.le_def]
  have hsplit : M.effect B₂ hB₂ =
      M.effect B₁ hB₁ + M.effect (B₂ \ B₁) (hB₂.diff hB₁) := by
    have hu : B₁ ∪ (B₂ \ B₁) = B₂ := Set.union_diff_cancel h
    rw [← M.effect_congr hu (hB₁.union (hB₂.diff hB₁)) hB₂,
      M.effect_union hB₁ (hB₂.diff hB₁) disjoint_sdiff_self_right]
  rw [hsplit, add_sub_cancel_left]
  exact M.isPositive_effect (B₂ \ B₁) (hB₂.diff hB₁)

/-- `[done]` **The effect property** `0 ≤ M(B) ≤ I`.  Lower bound is `isPositive_effect`; upper
bound is `effect_mono` against `M(univ) = I` (`effect_univ`).
SIGNATURE TO VERIFY: the `StarOrderedRing (H →L[ℂ] H)` instance (from `CStarAlgebra`) supplying
`≤` and `1 = id`. -/
lemma effect_le_one (M : POVM H ι) (B : Set ι) (hB : MeasurableSet B) :
    M.effect B hB ≤ 1 := by
  have h1 : (1 : H →L[ℂ] H) = M.effect Set.univ MeasurableSet.univ := by
    rw [M.effect_univ]; rfl
  rw [h1]
  exact M.effect_mono hB MeasurableSet.univ (Set.subset_univ B)

/-! ### Extensionality (the diagonal still determines the POVM) -/

/-- `[done — ports verbatim from `ext_of_diag`]` A POVM is determined by its diagonal measures. -/
theorem ext_of_diag {M N : POVM H ι} (h : ∀ ξ : H, M.diag ξ = N.diag ξ) : M = N := by
  have heff : M.effect = N.effect := by
    funext B hB
    exact op_ext_of_inner_self fun ξ => by rw [M.inner_effect, N.inner_effect, h ξ]
  obtain ⟨e₁, d₁, _, _, _⟩ := M
  obtain ⟨e₂, d₂, _, _, _⟩ := N
  obtain rfl : e₁ = e₂ := heff
  obtain rfl : d₁ = d₂ := funext h
  rfl

/-! ## §2  The discrete-POVM constructor `ofEffects`

The first of the two constructors, and the form most applications take (state discrimination,
informationally-complete measurements): a countable family of effects `Eₖ ≥ 0` resolving the
identity, `∑' k, E k = 1`, *is* a POVM on `κ` with the discrete σ-algebra.  `ofEffects` assembles
it — `effect B = ∑' k, B.indicator E k` (an operator-valued tsum) and `diag ξ` the discrete measure
`k ↦ ⟪ξ, Eₖ ξ⟫.re`.  The only analytic input is convergence of `∑' k, Eₖ` in the strong operator
topology, isolated as `summable_ofEffects`; the weld `inner_effect` then follows by pushing `ξ` and
the inner product through the tsum (the same `mapL` idiom as `Mixed.toStateCLM`).  The helper lemmas
are `private`; the public surface is `ofEffects`, `summable_ofEffects`, `diagOfEffects`, and the
`@[simp]` projections `ofEffects_effect` / `ofEffects_diag`. -/

/-- Each positive effect's diagonal matrix element is a nonnegative real coercion:
`⟪ξ, Eₖ ξ⟫ = (⟪ξ, Eₖ ξ⟫).re` (self-adjointness from positivity). -/
private lemma inner_eq_re_of_isPositive {E : H →L[ℂ] H} (hE : E.IsPositive) (ξ : H) :
    ⟪ξ, E ξ⟫_ℂ = ((⟪ξ, E ξ⟫_ℂ).re : ℂ) := by
  have hsa : IsSelfAdjoint E := hE.isSelfAdjoint
  have heq : starRingEnd ℂ ⟪ξ, E ξ⟫_ℂ = ⟪ξ, E ξ⟫_ℂ := by
    rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.isSelfAdjoint_iff'.mp hsa]
  exact (Complex.conj_eq_iff_re.mp heq).symm

open scoped ComplexOrder in
/-- The diagonal matrix element of a positive effect has nonnegative real part. -/
private lemma re_nonneg_of_isPositive {E : H →L[ℂ] H} (hE : E.IsPositive) (ξ : H) :
    0 ≤ (⟪ξ, E ξ⟫_ℂ).re := by
  rw [ContinuousLinearMap.isPositive_iff'] at hE
  have h := (Complex.le_def.mp (hE.2 ξ)).1
  simp only [Complex.zero_re] at h
  rw [← inner_conj_symm (E ξ) ξ, Complex.conj_re] at h
  exact h

variable {κ : Type*}

omit [CompleteSpace H] in
/-- From `∑' k, E k = 1`, the family `E` is summable.  (If it were not, the tsum would be `0`,
forcing the identity to vanish, hence `H` trivial — in which case every operator is `0`, so `E` is
summable after all.) -/
lemma summable_ofEffects {E : κ → (H →L[ℂ] H)} (hsum : ∑' k, E k = 1) : Summable E := by
  by_cases hns : Summable E
  · exact hns
  · rw [tsum_eq_zero_of_not_summable hns] at hsum
    have h0 : (1 : H →L[ℂ] H) = 0 := hsum.symm
    have hsub : ∀ x : H, x = 0 := fun x => by
      have := congrArg (fun T => T x) h0; simpa using this
    have hE0 : E = (fun _ => 0) := funext fun k => by
      ext x; rw [hsub (E k x)]; simp
    rw [hE0]
    exact summable_zero

/-- Push `ξ` through the operator-valued tsum and the inner product through the scalar tsum:
`⟪ξ, (∑' k, B.indicator E k) ξ⟫ = ∑' k, B.indicator (k ↦ ⟪ξ, Eₖ ξ⟫) k`. -/
private lemma inner_effect_tsum {E : κ → (H →L[ℂ] H)} (hSE : Summable E) (B : Set κ) (ξ : H) :
    ⟪ξ, (∑' k, Set.indicator B E k) ξ⟫_ℂ
      = ∑' k, Set.indicator B (fun k => ⟪ξ, E k ξ⟫_ℂ) k := by
  have hBsum : Summable (Set.indicator B E) := hSE.indicator B
  have happ : (∑' k, Set.indicator B E k) ξ = ∑' k, (Set.indicator B E k) ξ :=
    (hBsum.hasSum.mapL (ContinuousLinearMap.apply ℂ H ξ)).tsum_eq.symm
  rw [happ]
  have hSummApp : Summable (fun k => (Set.indicator B E k) ξ) :=
    hBsum.mapL (ContinuousLinearMap.apply ℂ H ξ)
  have hinner : ⟪ξ, ∑' k, (Set.indicator B E k) ξ⟫_ℂ
      = ∑' k, ⟪ξ, (Set.indicator B E k) ξ⟫_ℂ :=
    (hSummApp.hasSum.mapL (innerSL ℂ ξ)).tsum_eq.symm
  rw [hinner]
  refine tsum_congr fun k => ?_
  by_cases hk : k ∈ B
  · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk]
  · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk,
      ContinuousLinearMap.zero_apply, inner_zero_right]

variable [MeasurableSpace κ]

/-- The discrete diagonal measure `diag ξ = ∑' k, ⟪ξ, Eₖ ξ⟫.re • δ_k`. -/
noncomputable def diagOfEffects (E : κ → (H →L[ℂ] H)) (ξ : H) : Measure κ :=
  Measure.sum (fun k => ENNReal.ofReal ((⟪ξ, E k ξ⟫_ℂ).re) • Measure.dirac k)

omit [CompleteSpace H] in
private lemma diagOfEffects_apply {E : κ → (H →L[ℂ] H)} (ξ : H) {B : Set κ}
    (hB : MeasurableSet B) :
    (diagOfEffects E ξ) B
      = ∑' k, Set.indicator B (fun k => ENNReal.ofReal ((⟪ξ, E k ξ⟫_ℂ).re)) k := by
  rw [diagOfEffects, Measure.sum_apply _ hB]
  refine tsum_congr fun k => ?_
  rw [Measure.smul_apply, MeasureTheory.Measure.dirac_apply' k hB, smul_eq_mul]
  by_cases hk : k ∈ B
  · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk]; simp
  · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk]; simp

/-- The weld for `ofEffects`: `⟪ξ, (∑' k, B.indicator E k) ξ⟫ = ((diag ξ B).toReal : ℂ)`. -/
private lemma inner_effect_eq_diag {E : κ → (H →L[ℂ] H)} (hSE : Summable E)
    (hpos : ∀ k, (E k).IsPositive) (B : Set κ) (hB : MeasurableSet B) (ξ : H) :
    ⟪ξ, (∑' k, Set.indicator B E k) ξ⟫_ℂ = (((diagOfEffects E ξ) B).toReal : ℂ) := by
  rw [inner_effect_tsum hSE B ξ, diagOfEffects_apply ξ hB]
  have hterm : ∀ k, Set.indicator B (fun k => ⟪ξ, E k ξ⟫_ℂ) k
      = ((Set.indicator B (fun k => ((⟪ξ, E k ξ⟫_ℂ).re : ℝ)) k : ℝ) : ℂ) := fun k => by
    by_cases hk : k ∈ B
    · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk]
      exact inner_eq_re_of_isPositive (hpos k) ξ
    · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk, Complex.ofReal_zero]
  rw [tsum_congr hterm, ← Complex.ofReal_tsum]
  congr 1
  have hfin : ∀ k, Set.indicator B (fun k => ENNReal.ofReal ((⟪ξ, E k ξ⟫_ℂ).re)) k ≠ ⊤ :=
    fun k => by
      by_cases hk : k ∈ B
      · rw [Set.indicator_of_mem hk]; exact ENNReal.ofReal_ne_top
      · rw [Set.indicator_of_notMem hk]; exact ENNReal.zero_ne_top
  rw [ENNReal.tsum_toReal_eq hfin]
  refine tsum_congr fun k => ?_
  by_cases hk : k ∈ B
  · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk,
      ENNReal.toReal_ofReal (re_nonneg_of_isPositive (hpos k) ξ)]
  · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk, ENNReal.toReal_zero]

set_option linter.unusedSectionVars false in
/-- The real quadratic-form series `k ↦ ⟪ξ, Eₖ ξ⟫.re` is summable. -/
private lemma summable_re_quadForm {E : κ → (H →L[ℂ] H)} (hSE : Summable E) (ξ : H) :
    Summable (fun k => (⟪ξ, E k ξ⟫_ℂ).re) := by
  have h1 : Summable (fun k => (E k) ξ) := hSE.mapL (ContinuousLinearMap.apply ℂ H ξ)
  have h2 : Summable (fun k => ⟪ξ, (E k) ξ⟫_ℂ) := h1.mapL (innerSL ℂ ξ)
  exact h2.mapL Complex.reCLM

private lemma diagOfEffects_finite {E : κ → (H →L[ℂ] H)} (hSE : Summable E)
    (hpos : ∀ k, (E k).IsPositive) (ξ : H) : IsFiniteMeasure (diagOfEffects E ξ) := by
  refine ⟨?_⟩
  rw [diagOfEffects_apply ξ MeasurableSet.univ]
  simp only [Set.indicator_univ]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => re_nonneg_of_isPositive (hpos k) ξ)
    (summable_re_quadForm hSE ξ)]
  exact ENNReal.ofReal_lt_top

/-- **Discrete-POVM constructor.**  A countable family of positive effects `Eₖ` resolving the
identity (`∑' k, E k = 1`) is a POVM on `κ` (with the discrete σ-algebra): the effect of `B` is the
operator-valued tsum `∑' k, B.indicator E k`, and `diag ξ` is the discrete measure
`k ↦ ⟪ξ, Eₖ ξ⟫.re`. -/
noncomputable def ofEffects (E : κ → (H →L[ℂ] H)) (hpos : ∀ k, (E k).IsPositive)
    (hsum : ∑' k, E k = 1) : POVM H κ where
  effect B _ := ∑' k, Set.indicator B E k
  diag ξ := diagOfEffects E ξ
  diag_finite ξ := diagOfEffects_finite (summable_ofEffects hsum) hpos ξ
  inner_effect B hB ξ := inner_effect_eq_diag (summable_ofEffects hsum) hpos B hB ξ
  effect_univ := by
    simp only [Set.indicator_univ]
    rw [hsum, ContinuousLinearMap.one_def]

@[simp] lemma ofEffects_effect (E : κ → (H →L[ℂ] H)) (hpos : ∀ k, (E k).IsPositive)
    (hsum : ∑' k, E k = 1) {B : Set κ} (hB : MeasurableSet B) :
    (ofEffects E hpos hsum).effect B hB = ∑' k, Set.indicator B E k := rfl

@[simp] lemma ofEffects_diag (E : κ → (H →L[ℂ] H)) (hpos : ∀ k, (E k).IsPositive)
    (hsum : ∑' k, E k = 1) (ξ : H) :
    (ofEffects E hpos hsum).diag ξ = diagOfEffects E ξ := rfl


end POVM

/-! ## §3  Every projection-valued measure is a POVM

The second constructor, in the opposite direction: a sharp `ProjValMeasure` is a POVM on
`(ℝ, Borel)` — keep `proj`, `diag`, the weld, and `proj_univ`; forget only the multiplicativity
`proj_inter`.  So every projective measurement is an (extremal) generalized one, and the Born layer
of §4 applies to it unchanged (`bornMeasurePOVM_toPOVM`). -/

/-- `[done]` The forgetful coercion: a `ProjValMeasure` is a POVM on `(ℝ, Borel)` — keep `proj`,
`diag`, the weld, and `proj_univ`; forget `proj_inter`.  (`effect_le_one` then holds with equality
of `M(B)` to a projection, the sharp case.) -/
noncomputable def _root_.Spectra.ProjValMeasure.toPOVM (P : ProjValMeasure H) : POVM H ℝ where
  effect := P.proj
  diag := P.diag
  diag_finite := P.diag_finite
  inner_effect := P.inner_proj
  effect_univ := P.proj_univ

@[simp] lemma ProjValMeasure.toPOVM_diag (P : ProjValMeasure H) (ξ : H) :
    P.toPOVM.diag ξ = P.diag ξ := rfl

@[simp] lemma ProjValMeasure.toPOVM_effect (P : ProjValMeasure H)
    (B : Set ℝ) (hB : MeasurableSet B) :
    P.toPOVM.effect B hB = P.proj B hB := rfl

end Spectra

/-! ## §4  The Born rule for POVMs

Identical in form to the PVM Born rule, because that layer only ever touched `diag`. -/

open Spectra

namespace Spectra.QuantumMechanics.BornRule

/-! ### Pure states -/

/-- The **POVM Born measure of a pure state** `ψ`: the carried diagonal measure, exactly as in
the projective case.  `(bornMeasurePOVMPure M ψ) B = ⟪ψ, M(B) ψ⟫` by `inner_effect`. -/
noncomputable def bornMeasurePOVMPure (M : POVM H ι) (ψ : H) : Measure ι :=
  M.diag ψ

/-- For a unit vector this is a probability measure (mass `‖ψ‖² = 1`, by `diag_univ_toReal`). -/
theorem isProbabilityMeasure_bornMeasurePOVMPure (M : POVM H ι) {ψ : H} (hψ : ‖ψ‖ = 1) :
    IsProbabilityMeasure (bornMeasurePOVMPure M ψ) := by
  refine ⟨(ENNReal.toReal_eq_one_iff _).mp ?_⟩
  change ((M.diag ψ) Set.univ).toReal = 1
  rw [M.diag_univ_toReal, hψ, one_pow]

/-- `[done]` **The Born rule, POVM pure form.**  `Prob(B) = ⟪ψ, M(B) ψ⟫`.  Proof:
`M.inner_effect`, with `.re`/`.toReal` bookkeeping (the value is real). -/
theorem bornMeasurePOVMPure_apply (M : POVM H ι) (ψ : H)
    {B : Set ι} (hB : MeasurableSet B) :
    ((bornMeasurePOVMPure M ψ) B).toReal = (⟪ψ, M.effect B hB ψ⟫_ℂ).re := by
  rw [show (bornMeasurePOVMPure M ψ) = M.diag ψ from rfl, M.inner_effect B hB ψ,
    Complex.ofReal_re]

/-! ### Mixed states -/

/-- The **POVM Born measure of a mixed state** `ρ`: the eigenvalue-weighted mixture of the pure
POVM measures — the same `Measure.sum` construction as for PVMs.  This is the `M : POVM H ι`,
`ρ : DensityOperator H ↦ Measure ι` map of the stub. -/
noncomputable def bornMeasurePOVM (M : POVM H ι) (ρ : DensityOperator H) : Measure ι :=
  Measure.sum (fun i => ρ.weight i • M.diag (ρ.state i))

/-- `[done]` A probability measure (mass `∑ pᵢ = 1`). -/
theorem isProbabilityMeasure_bornMeasurePOVM (M : POVM H ι) (ρ : DensityOperator H) :
    IsProbabilityMeasure (bornMeasurePOVM M ρ) := by
  refine ⟨?_⟩
  rw [bornMeasurePOVM, Measure.sum_apply _ MeasurableSet.univ]
  have hone : ∀ i, (ρ.weight i • M.diag (ρ.state i)) Set.univ = ρ.weight i := fun i => by
    rw [Measure.smul_apply, smul_eq_mul]
    have h := M.diag_univ_toReal (ρ.state i)
    rw [ρ.state_unit i, one_pow] at h
    rw [← ENNReal.ofReal_toReal (measure_ne_top (M.diag (ρ.state i)) Set.univ), h,
      ENNReal.ofReal_one, mul_one]
  simp only [hone]
  exact ρ.weight_sum

/-- `[done]` **The trace form as a spectral sum**, `Tr(ρ M(B)) = ∑' i, pᵢ ⟪eᵢ, M(B) eᵢ⟫`.
Via `Measure.sum_apply _ hB` and `Measure.smul_apply`. -/
theorem bornMeasurePOVM_apply (M : POVM H ι) (ρ : DensityOperator H)
    {B : Set ι} (hB : MeasurableSet B) :
    (bornMeasurePOVM M ρ) B = ∑' i, ρ.weight i * (M.diag (ρ.state i)) B := by
  rw [bornMeasurePOVM, Measure.sum_apply _ hB]
  simp only [Measure.smul_apply, smul_eq_mul]

/-- `[done]` The pure case reduces to `bornMeasurePOVMPure`. -/
theorem bornMeasurePOVM_pure (M : POVM H ι) {ψ : H} (hψ : ‖ψ‖ = 1) :
    bornMeasurePOVM M (DensityOperator.pure hψ) = bornMeasurePOVMPure M ψ := by
  refine Measure.ext fun B hB => ?_
  rw [bornMeasurePOVM_apply M _ hB]
  simp only [DensityOperator.pure, ite_mul, one_mul, zero_mul, tsum_ite_eq, bornMeasurePOVMPure]

/-- `[done]` **`Tr(ρ M(B))`, literal**, through the `toState` bridge of `Mixed.lean`: the normal
state evaluated on the effect equals the POVM Born probability.  Proof: `toStateCLM_apply`,
`M.inner_effect` termwise, then `bornMeasurePOVM_apply` — the exact analogue of `toState_proj_eq`
with `inner_effect` in place of `inner_proj`. -/
theorem toState_effect_eq (M : POVM H ι) (ρ : DensityOperator H)
    {B : Set ι} (hB : MeasurableSet B) :
    (ρ.toStateCLM (M.effect B hB)).re = ((bornMeasurePOVM M ρ) B).toReal := by
  have hrhs : ((bornMeasurePOVM M ρ) B).toReal
      = ∑' i, (ρ.weight i).toReal * ((M.diag (ρ.state i)) B).toReal := by
    rw [bornMeasurePOVM_apply M ρ hB]
    have hfin : ∀ i, ρ.weight i * (M.diag (ρ.state i)) B ≠ ⊤ := fun i =>
      ENNReal.mul_ne_top
        (lt_of_le_of_lt (ρ.weight_sum ▸ ENNReal.le_tsum i) ENNReal.one_lt_top).ne
        (measure_ne_top _ _)
    rw [ENNReal.tsum_toReal_eq hfin]
    exact tsum_congr fun i => ENNReal.toReal_mul
  rw [hrhs, DensityOperator.toStateCLM_apply]
  have key : ∀ i, (ρ.weight i).toReal • ⟪ρ.state i, M.effect B hB (ρ.state i)⟫_ℂ
      = ((ρ.weight i).toReal * ((M.diag (ρ.state i)) B).toReal : ℝ) := fun i => by
    rw [M.inner_effect B hB (ρ.state i), Complex.real_smul, ← Complex.ofReal_mul]
  simp_rw [key]
  rw [← Complex.ofReal_tsum]
  exact Complex.ofReal_re _

/-- `[done]` **Consistency with the projective Born rule.**  For a `ProjValMeasure`, its POVM
Born measure is its PVM Born measure: `toPOVM` only forgets `proj_inter`, which the measure never
used.  Proof: both are `Measure.sum` of the same `P.diag`s (`toPOVM_diag`). -/
theorem bornMeasurePOVM_toPOVM (P : ProjValMeasure H) (ρ : DensityOperator H) :
    bornMeasurePOVM P.toPOVM ρ = bornMeasureMixed P ρ := rfl

/-! ## §5  Capstone: the two-outcome measurement

The simplest non-trivial POVM, and the one every yes/no test and state-discrimination problem
reduces to: an effect `E` with `0 ≤ E ≤ 1` is precisely a binary measurement — `E` the "yes"
effect, its complement `1 - E` the "no" effect.  `binaryPOVM` builds it on `Bool`, and it ties the
three strands of the file together:

* the **effect calculus** of §1 — `1 - E` is again an effect *exactly because* `E ≤ 1` in the
  Loewner order (`ContinuousLinearMap.le_def`, which makes `E ≤ 1` definitionally
  `(1 - E).IsPositive`);
* the **constructor** `ofEffects` of §2, applied to the two-element family `{E, 1 - E}` whose sum
  is the identity;
* the **Born rule** of §4 — the outcome probabilities are `⟪ψ, E ψ⟫` and `⟪ψ, (1 - E) ψ⟫`, which
  for a unit vector sum to one (`isProbabilityMeasure_bornMeasurePOVMPure`).

So an effect is *literally* a yes-probability operator: `binaryPOVM_bornPure_true` reads
`P(yes) = ⟪ψ, E ψ⟫`. -/

/-- The two-element effect family of a binary measurement: `true` ("yes") carries `E`, `false`
("no") its complement `1 - E`.  Shared by `binaryPOVM` and its `@[simp]` effect lemmas. -/
private abbrev binaryEffect (E : H →L[ℂ] H) : Bool → (H →L[ℂ] H) := fun b => bif b then E else 1 - E

/-- The **two-outcome POVM** of an effect `0 ≤ E ≤ 1`: outcome `true` ("yes") carries the effect
`E`, outcome `false` ("no") its complement `1 - E`. -/
noncomputable def binaryPOVM (E : H →L[ℂ] H) (hE : E.IsPositive) (hE1 : E ≤ 1) :
    POVM H Bool :=
  POVM.ofEffects (binaryEffect E)
    (fun b => by cases b with
      | true => exact hE
      | false => exact (ContinuousLinearMap.le_def E 1).mp hE1)
    (by
      rw [(hasSum_fintype (binaryEffect E)).tsum_eq, Fintype.sum_bool]
      simp)

/-- The "yes" effect of `binaryPOVM` is `E` itself. -/
@[simp] lemma binaryPOVM_effect_true (E : H →L[ℂ] H) (hE : E.IsPositive) (hE1 : E ≤ 1) :
    (binaryPOVM E hE hE1).effect {true} (measurableSet_singleton true) = E := by
  rw [binaryPOVM, POVM.ofEffects_effect,
    (hasSum_fintype (fun b : Bool => Set.indicator {true} (binaryEffect E) b)).tsum_eq,
    Fintype.sum_bool]
  simp

/-- The "no" effect of `binaryPOVM` is the complement `1 - E`. -/
@[simp] lemma binaryPOVM_effect_false (E : H →L[ℂ] H) (hE : E.IsPositive) (hE1 : E ≤ 1) :
    (binaryPOVM E hE hE1).effect {false} (measurableSet_singleton false) = 1 - E := by
  rw [binaryPOVM, POVM.ofEffects_effect,
    (hasSum_fintype (fun b : Bool => Set.indicator {false} (binaryEffect E) b)).tsum_eq,
    Fintype.sum_bool]
  simp

/-- **The yes-probability is `⟪ψ, E ψ⟫`.**  The Born probability that `binaryPOVM E` returns `true`
in state `ψ` is exactly the diagonal matrix element of the effect — an effect *is* a yes-probability
operator.  (Effect order ⟹ constructor ⟹ Born rule, in one line.) -/
theorem binaryPOVM_bornPure_true (E : H →L[ℂ] H) (hE : E.IsPositive) (hE1 : E ≤ 1) (ψ : H) :
    ((bornMeasurePOVMPure (binaryPOVM E hE hE1) ψ) {true}).toReal = (⟪ψ, E ψ⟫_ℂ).re := by
  rw [bornMeasurePOVMPure_apply (binaryPOVM E hE hE1) ψ (measurableSet_singleton true),
    binaryPOVM_effect_true]

/-- The complementary "no" probability is `⟪ψ, (1 - E) ψ⟫`. -/
theorem binaryPOVM_bornPure_false (E : H →L[ℂ] H) (hE : E.IsPositive) (hE1 : E ≤ 1) (ψ : H) :
    ((bornMeasurePOVMPure (binaryPOVM E hE hE1) ψ) {false}).toReal = (⟪ψ, (1 - E) ψ⟫_ℂ).re := by
  rw [bornMeasurePOVMPure_apply (binaryPOVM E hE hE1) ψ (measurableSet_singleton false),
    binaryPOVM_effect_false]

/-! ## §6  Flags

`[optional refactor — no new infra]`  **Factor the Born layer through `diag`.**  Every Born-rule
declaration in `Mixed.lean` and here depends only on the `diag : H → Measure ·` field and the mass
lemma — never on `proj_inter`, `effect_univ`, or the operators.  A typeclass
```
class HasDiagonalMeasure (F : Type*) (H ι) where
  diag : F → H → Measure ι
  diag_finite : …
  diag_univ : ((diag f ξ) univ).toReal = ‖ξ‖²
```
with `ProjValMeasure` and `POVM` instances would let `bornMeasure`, `bornMeasureMixed`,
`isProbabilityMeasure_*`, and `*_apply` be stated and proved **once**.  Pure refactor; recommended
only if a third carrier appears.

`[done — discrete case, in `Naimark.lean`]`  **Naimark's theorem.**  Every POVM `M` on `H` is the
compression of a PVM `P` on a larger space `K`: `M.effect B = V⋆ ∘ P.proj B ∘ V` for an isometry
`V : H → K`.  This is the structural theorem justifying "generalized measurement," and the bridge by
which POVM results reduce to projective ones.

The **discrete / countable** case is proved sorry-free in
`QuantumMechanics/BornRule/Naimark.lean` as `naimark_dilation`: for a resolution of the identity
`E : κ → (H →L[ℂ] H)`, `∑' k, E k = 1` (i.e. an `ofEffects` POVM), with carrier
`NaimarkSpace H κ = lp (fun _ : κ => H) 2`, isometry `naimarkV : ψ ↦ (√Eₖ ψ)ₖ` (operator square
root `CFC.sqrt`), and the diagonal PVM `naimarkPVM : ProjValMeasure' (NaimarkSpace H κ) κ`.  This
covers every `ofEffects`/`binaryPOVM` measurement.  The dilating PVM lives in the general
`Spectra.ProjValMeasure'` (`ProjValMeasure/General.lean`) — a PVM over an arbitrary Hilbert space
and outcome space, i.e. `POVM` + the `proj_inter` field.

(Aside: there is **no** Stinespring/Naimark/CP-dilation existence theorem in Mathlib, and the
`Bochner.GNS` stack here is specialized to positive-definite functions `ℝ → ℂ` for Stone's theorem,
so neither shortcuts this — the discrete dilation is the bespoke ℓ²-direct-sum construction.)

`[needs infra: operator-valued-measure topology]`  The fully general σ-additive Naimark theorem,
for an *uncountable* outcome space `ι` with a non-atomic POVM, remains open: it needs a topology on
operator-valued measures that the library deliberately avoids.

`[needs InformationGeometry.StatisticalModel API]`  **The weld, quantum-estimation form.**  A POVM
`M` turns a state `ρ` into the classical model `bornMeasurePOVM M ρ`; ranging over `M` is the
*measurement-choice* in quantum estimation.  The quantum Cramér–Rao bound
(`CramerRao.Quantum`) is the optimization of the classical Fisher information of
`θ ↦ bornMeasurePOVM M ρ_θ` over all POVMs `M`, bounded by the quantum Fisher information.  The map
`(M, ρ) ↦ bornMeasurePOVM M ρ` is the object that optimization is taken over.
-/

end Spectra.QuantumMechanics.BornRule
