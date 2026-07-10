/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.ProjValMeasure.Basic
import Spectra.QuantumMechanics.BornRule.Observable
import Spectra.Modular.KMS.StateTopology
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
/-!
# The mixed-state Born rule

For a density operator `ρ` and a resolution of the identity `P`, the probability of an
outcome in a Borel set `B` is `Tr(ρ · E(B))`.  A density operator is carried here as a
normalized countable **ensemble** of unit vectors rather than a bundled trace-class operator,
and `Tr(ρ ·)` is realized as an honest normal state on the bounded operators.

## Main definitions

* `DensityOperator` — a mixed state as a normalized ensemble: `ℝ≥0∞` weights summing to `1`
  and a family of unit vectors.
* `DensityOperator.pure` — the one-point ensemble `|ψ⟩⟨ψ|`.
* `bornMeasureMixed` — the mixed-state Born measure, the weight-weighted mixture of the
  pure-state Born measures `P.diag (eᵢ)`.
* `DensityOperator.toStateCLM` / `DensityOperator.toState` — the normal-state functional
  `T ↦ ∑ᵢ pᵢ ⟪eᵢ, T eᵢ⟫` on `H →L[ℂ] H`, packaged as a continuous linear map and as an
  element of the weak-* dual.
* `DensityOperator.trace` — the trace `Tr ρ = ∑ pᵢ`, equal to `(toState ρ) 1`.

## Main statements

* `isProbabilityMeasure_bornMeasureMixed` — `bornMeasureMixed P ρ` is a probability measure.
* `bornMeasureMixed_apply` / `bornMeasureMixed_apply_norm` — the trace form as the spectral
  sum `∑' i, pᵢ · μ_{eᵢ}(B)`, in real/norm terms `∑' i, pᵢ · ‖E(B) eᵢ‖²`.
* `bornMeasureMixed_pure` — the pure case reduces to the pure-state `bornMeasure`.
* `DensityOperator.toState_mem_stateSet` — the ensemble is a state: `toState ρ ∈ stateSet`.
* `toState_proj_eq` — `Tr(ρ E(B))` is literal: evaluating the normal state on the spectral
  projection returns the Born probability, with no trace functional.
* `bornMeasureMixed_eq_of_toState_eq` — ensemble invariance: the Born measure depends only on
  the state, not on the ensemble realizing it.
* `bornExpectation_eq_toState` — the expectation `∫ s dμ` equals `Tr(ρ A)` when `A` is the
  observable of `P`.

## Implementation notes

Two structures are involved and they play different roles.

**The measure needs normality, not a trace.**  As of Mathlib 4.31 there is no
infinite-dimensional trace-class trace, so `Tr(ρ E(B))` is not available on a bundled
operator.  The deeper point is about additivity: for a *general* state
`φ ∈ stateSet (H →L[ℂ] H)` the set function `B ↦ φ(E(B))` is only **finitely** additive; it is
a genuine measure exactly when `φ` is **normal** (= a density operator).  `stateSet` does not
encode normality — its Krein–Milman pure states (`Spectra.KMS.pureStateSet`) include singular
states that are not vector states.  So `stateSet` is the wrong carrier for the Born *measure*.

**The ensemble is manifestly normal.**  A countable convex combination of vector states is
normal by construction, so its Born measure is countably additive for free — it is literally a
`Measure.sum` of the pure measures `P.diag` built in `Basic.lean`.  Hence `DensityOperator` is
carried as an **ensemble** (a normalized family of unit vectors), and `bornMeasureMixed` is the
mixture.  No trace functional, no normality side-condition.

**`stateSet` is the right *target*, via a bridge.**  `DensityOperator.toState` sends the
ensemble to the normal state `T ↦ ∑ᵢ pᵢ ⟪eᵢ, T eᵢ⟫` and lands it inside the convex, compact
`stateSet` of `StateTopology`.  This bridge:

* provides a genuine, Mathlib-native functional — `trace ρ = (toState ρ) 1` and
  `⟪eᵢ, ρ A eᵢ⟫`-style expectations are real definitions;
* makes **`Tr(ρ E(B))` literal**: `(toState ρ) (P.proj B hB) = Born probability`
  (`toState_proj_eq`), with no trace-class theory;
* makes **ensemble invariance** provable (`bornMeasureMixed_eq_of_toState_eq`): the Born
  measure depends only on the state `toState ρ`, not on the chosen ensemble — the physical
  fact that distinct preparations of the same `ρ` are indistinguishable.

It also hands `InformationGeometry` the convex state space (`stateSet_convex`,
`stateSet_isCompact`) as the manifold of mixed states, with pure states as extreme points.

Two scope facts are worth stating plainly:

* `toState` is a functional on **bounded** operators `H →L[ℂ] H`.  The Born *measure* handles
  unbounded observables (projections are bounded), but the operator expectation `Tr(ρ A)` via
  `toState` is only for bounded `A`; for unbounded `A` use the measure mean `∫ s dμ`.
* The embedding `DensityOperator ↪ stateSet` is **not** surjective: only normal states are hit.

The construction relies on the instance `CStarAlgebra (H →L[ℂ] H)` (via Mathlib's
`ContinuousLinearMap.instCStarRingId`) for `stateSet (H →L[ℂ] H)` to typecheck; it resolves,
as `DensityOperator.toState_mem_stateSet` is a proved theorem that uses it.

## References

* [Hall, *Quantum Theory for Mathematicians*][hall2013], §19.
* [Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics I*], §2.4
  (normal states ↔ density matrices; the finitely- vs countably-additive distinction).
* [Reed, Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*], §VI.6
  (trace-class operators and density matrices).

## Tags

density operator, mixed state, Born rule, normal state, ensemble, trace, projection-valued
measure, state space
-/

open MeasureTheory Complex
open scoped InnerProductSpace ENNReal ComplexOrder
open Spectra Spectra.ProjValMeasure Spectra.KMS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.QuantumMechanics.BornRule
open PVM

/-! ## §1  Density operators as ensembles -/

/-- A **density operator** (mixed state), presented as a normalized ensemble: `ℝ≥0∞` weights
summing to `1` and a family of unit vectors.  The minimal data from which the Born measure is a
mixture of pure measures; manifestly a normal state.  The unit vectors `state` need not be
orthonormal, and no spectral decomposition of any operator is assumed. -/
structure DensityOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The mixing weights (the ensemble probabilities). -/
  weight : ℕ → ℝ≥0∞
  /-- The ensemble's unit vectors. -/
  state : ℕ → H
  /-- Each ensemble member is a unit vector. -/
  state_unit : ∀ i, ‖state i‖ = 1
  /-- A probability distribution of weights: `∑ pᵢ = 1`. -/
  weight_sum : ∑' i, weight i = 1

namespace DensityOperator

/-- The **pure state** `|ψ⟩⟨ψ|` as the one-point ensemble. -/
noncomputable def pure {ψ : H} (hψ : ‖ψ‖ = 1) : DensityOperator H where
  weight := fun i => if i = 0 then 1 else 0
  state := fun _ => ψ
  state_unit := fun _ => hψ
  weight_sum := tsum_ite_eq 0 1

end DensityOperator

/-! ## §2  The mixed Born measure -/

/-- The **mixed-state Born measure** `Tr(ρ E(·))`, as the eigenvalue-weighted mixture of the
pure-state Born measures `P.diag (eᵢ)`. -/
noncomputable def bornMeasureMixed (P : ProjValMeasure H) (ρ : DensityOperator H) : Measure ℝ :=
  Measure.sum (fun i => ρ.weight i • P.diag (ρ.state i))

/-- `[done — Mathlib]` A probability measure (mass `∑ pᵢ = 1`).  Via `Measure.sum_apply` at
`univ`, `Measure.smul_apply`, `P.diag_univ_toReal`, and `ρ.weight_sum`. -/
theorem isProbabilityMeasure_bornMeasureMixed (P : ProjValMeasure H) (ρ : DensityOperator H) :
    IsProbabilityMeasure (bornMeasureMixed P ρ) := by
  refine ⟨?_⟩
  rw [bornMeasureMixed, Measure.sum_apply _ MeasurableSet.univ]
  have hone : ∀ i, (ρ.weight i • P.diag (ρ.state i)) Set.univ = ρ.weight i := fun i => by
    rw [Measure.smul_apply, smul_eq_mul]
    have h := P.diag_univ_toReal (ρ.state i)
    rw [ρ.state_unit i, one_pow] at h
    rw [← ENNReal.ofReal_toReal (measure_ne_top (P.diag (ρ.state i)) Set.univ), h,
      ENNReal.ofReal_one, mul_one]
  simp only [hone]
  exact ρ.weight_sum

/-- `[done — Mathlib]` The trace form as a spectral sum: `∑' i, pᵢ · μ_{eᵢ}(B)`, which is
`Tr(ρ E(B))` in `ρ`'s eigenbasis (each term is `⟪eᵢ, E(B) eᵢ⟫` by `inner_proj`).
Via `Measure.sum_apply _ hB` and `Measure.smul_apply`. -/
theorem bornMeasureMixed_apply (P : ProjValMeasure H) (ρ : DensityOperator H)
    {B : Set ℝ} (hB : MeasurableSet B) :
    (bornMeasureMixed P ρ) B = ∑' i, ρ.weight i * (P.diag (ρ.state i)) B := by
  rw [bornMeasureMixed, Measure.sum_apply _ hB]
  simp only [Measure.smul_apply, smul_eq_mul]

/-- `[done — Mathlib]` The Born rule, mixed form (real/norm): the eigenvalue-weighted sum of the
pure Born probabilities `‖E(B) eᵢ‖²`.  Via `bornMeasureMixed_apply`, `ENNReal.tsum_toReal`, and
`P.norm_sq_proj_apply`. -/
theorem bornMeasureMixed_apply_norm (P : ProjValMeasure H) (ρ : DensityOperator H)
    {B : Set ℝ} (hB : MeasurableSet B) :
    ((bornMeasureMixed P ρ) B).toReal
      = ∑' i, (ρ.weight i).toReal * ‖P.proj B hB (ρ.state i)‖ ^ 2 := by
  rw [bornMeasureMixed_apply P ρ hB]
  have hfin : ∀ i, ρ.weight i * (P.diag (ρ.state i)) B ≠ ⊤ := fun i =>
    ENNReal.mul_ne_top
      (lt_of_le_of_lt (ρ.weight_sum ▸ ENNReal.le_tsum i) ENNReal.one_lt_top).ne
      (measure_ne_top _ _)
  rw [ENNReal.tsum_toReal_eq hfin]
  exact tsum_congr fun i => by
    rw [ENNReal.toReal_mul, ← P.norm_sq_proj_apply B hB (ρ.state i)]

/-- `[done]` The pure case reduces to the pure-state `bornMeasure` of `Basic.lean`. -/
theorem bornMeasureMixed_pure (P : ProjValMeasure H) {ψ : H} (hψ : ‖ψ‖ = 1) :
    bornMeasureMixed P (DensityOperator.pure hψ) = bornMeasure P ψ := by
  refine Measure.ext fun B hB => ?_
  rw [bornMeasureMixed_apply P _ hB]
  simp only [DensityOperator.pure, ite_mul, one_mul, zero_mul, tsum_ite_eq, bornMeasure]

/-! ## §3  The normal state `toState`

The functional `T ↦ ∑ᵢ pᵢ ⟪eᵢ, T eᵢ⟫` on `H →L[ℂ] H`.  It is the trace `Tr(ρ ·)` computed
against the ensemble — a genuine normal state, built with only `tsum` of inner products and the
contraction bound `‖·‖ ≤ ‖T‖`.  No trace-class theory. -/

/-- The weights, as a summable real family (`weight_sum = 1 < ∞`). -/
lemma DensityOperator.summable_weight_toReal (ρ : DensityOperator H) :
    Summable (fun i => (ρ.weight i).toReal) :=
  ENNReal.summable_toReal (by rw [ρ.weight_sum]; exact ENNReal.one_ne_top)

/-- The real weights sum to `1`: `∑' pᵢ.toReal = (∑' pᵢ).toReal = 1`. -/
lemma DensityOperator.tsum_weight_toReal (ρ : DensityOperator H) :
    ∑' i, (ρ.weight i).toReal = 1 := by
  have hfin : ∀ i, ρ.weight i ≠ ⊤ := fun i =>
    (lt_of_le_of_lt (ρ.weight_sum ▸ ENNReal.le_tsum i) ENNReal.one_lt_top).ne
  rw [← ENNReal.tsum_toReal_eq hfin, ρ.weight_sum, ENNReal.toReal_one]

/-- The contraction bound on each ensemble term: `‖pᵢ ⟪eᵢ, T eᵢ⟫‖ ≤ pᵢ ‖T‖` (Cauchy–Schwarz
and `‖eᵢ‖ = 1`). -/
lemma DensityOperator.norm_term_le (ρ : DensityOperator H) (T : H →L[ℂ] H) (i : ℕ) :
    ‖(ρ.weight i).toReal • ⟪ρ.state i, T (ρ.state i)⟫_ℂ‖ ≤ (ρ.weight i).toReal * ‖T‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  gcongr
  calc ‖⟪ρ.state i, T (ρ.state i)⟫_ℂ‖
      ≤ ‖ρ.state i‖ * ‖T (ρ.state i)‖ := norm_inner_le_norm _ _
    _ ≤ ‖ρ.state i‖ * (‖T‖ * ‖ρ.state i‖) := by gcongr; exact T.le_opNorm _
    _ = ‖T‖ := by rw [ρ.state_unit i]; ring

/-- For each bounded `T`, the ensemble series `∑ᵢ pᵢ ⟪eᵢ, T eᵢ⟫` is absolutely summable. -/
lemma DensityOperator.summable_term (ρ : DensityOperator H) (T : H →L[ℂ] H) :
    Summable (fun i => (ρ.weight i).toReal • ⟪ρ.state i, T (ρ.state i)⟫_ℂ) :=
  Summable.of_norm_bounded (ρ.summable_weight_toReal.mul_right ‖T‖) (fun i => ρ.norm_term_le T i)

/-- The underlying ℂ-linear functional `T ↦ ∑ᵢ pᵢ ⟪eᵢ, T eᵢ⟫`, as a continuous linear map.
Boundedness: each term is `≤ pᵢ‖T‖`, and `∑ pᵢ = 1`, so `‖toStateCLM ρ T‖ ≤ ‖T‖`
(supply this `C = 1` bound to `LinearMap.mkContinuous`). -/
noncomputable def DensityOperator.toStateCLM (ρ : DensityOperator H) :
    (H →L[ℂ] H) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun T => ∑' i, (ρ.weight i).toReal • ⟪ρ.state i, T (ρ.state i)⟫_ℂ
      map_add' := fun T S => by
        simp only [ContinuousLinearMap.add_apply, inner_add_right, smul_add]
        exact Summable.tsum_add (ρ.summable_term T) (ρ.summable_term S)
      map_smul' := fun c T => by
        simp only [ContinuousLinearMap.smul_apply, inner_smul_right, RingHom.id_apply,
          ← smul_eq_mul]
        rw [← tsum_const_smul'' c]
        exact tsum_congr fun i => smul_comm _ c _ }
    1 fun T => by
      rw [one_mul]
      have hbnd : Summable fun i => ‖(ρ.weight i).toReal • ⟪ρ.state i, T (ρ.state i)⟫_ℂ‖ :=
        Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ρ.norm_term_le T i)
          (ρ.summable_weight_toReal.mul_right ‖T‖)
      calc ‖∑' i, (ρ.weight i).toReal • ⟪ρ.state i, T (ρ.state i)⟫_ℂ‖
          ≤ ∑' i, ‖(ρ.weight i).toReal • ⟪ρ.state i, T (ρ.state i)⟫_ℂ‖ :=
            norm_tsum_le_tsum_norm hbnd
        _ ≤ ∑' i, (ρ.weight i).toReal * ‖T‖ :=
            hbnd.tsum_le_tsum (fun i => ρ.norm_term_le T i)
              (ρ.summable_weight_toReal.mul_right ‖T‖)
        _ = (∑' i, (ρ.weight i).toReal) * ‖T‖ := tsum_mul_right
        _ = ‖T‖ := by rw [ρ.tsum_weight_toReal, one_mul]

@[simp] lemma DensityOperator.toStateCLM_apply (ρ : DensityOperator H) (T : H →L[ℂ] H) :
    ρ.toStateCLM T = ∑' i, (ρ.weight i).toReal • ⟪ρ.state i, T (ρ.state i)⟫_ℂ :=
  rfl

/-- `ρ` as an element of the weak-* dual, the home of the state geometry. -/
noncomputable def DensityOperator.toState (ρ : DensityOperator H) :
    WeakDual ℂ (H →L[ℂ] H) :=
  StrongDual.toWeakDual ρ.toStateCLM

/-- `[done — reuses StateTopology]` **The ensemble is a state.**  `toState ρ` lands in
`stateSet`: positivity is `⟪eᵢ, (T⋆T) eᵢ⟫ = ‖T eᵢ‖² ≥ 0` summed with `pᵢ ≥ 0`; normalization is
`∑ pᵢ ‖eᵢ‖² = ∑ pᵢ = 1` (`state_unit`, `weight_sum`).  Reuses `Spectra.KMS.mem_stateSet`. -/
theorem DensityOperator.toState_mem_stateSet (ρ : DensityOperator H) :
    ρ.toState ∈ stateSet (H →L[ℂ] H) := by
  rw [mem_stateSet]
  refine ⟨fun T => ?_, ?_⟩
  · -- positivity: `⟪eᵢ, (T⋆T) eᵢ⟫ = ‖T eᵢ‖² ≥ 0`, weighted by `pᵢ ≥ 0`
    change (0 : ℂ) ≤ ρ.toStateCLM (star T * T)
    rw [DensityOperator.toStateCLM_apply]
    have key : ∀ i, (ρ.weight i).toReal • ⟪ρ.state i, (star T * T) (ρ.state i)⟫_ℂ
        = ((ρ.weight i).toReal * ‖T (ρ.state i)‖ ^ 2 : ℝ) := fun i => by
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right]
      refine Complex.ext ?_ ?_
      · rw [Complex.smul_re, smul_eq_mul, Complex.ofReal_re, ← RCLike.re_eq_complex_re,
          inner_self_eq_norm_sq]
      · rw [Complex.ofReal_im, Complex.smul_im, ← RCLike.im_eq_complex_im, inner_self_im,
          smul_zero]
    simp_rw [key]
    rw [← Complex.ofReal_tsum]
    exact Complex.zero_le_real.mpr
      (tsum_nonneg fun i => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
  · -- normalization: `∑ pᵢ ‖eᵢ‖² = ∑ pᵢ = 1`
    change ρ.toStateCLM 1 = 1
    rw [DensityOperator.toStateCLM_apply]
    have key : ∀ i, (ρ.weight i).toReal • ⟪ρ.state i, (1 : H →L[ℂ] H) (ρ.state i)⟫_ℂ
        = ((ρ.weight i).toReal : ℝ) := fun i => by
      rw [ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, ρ.state_unit i]
      simp [Complex.real_smul]
    simp_rw [key]
    rw [← Complex.ofReal_tsum, ρ.tsum_weight_toReal, Complex.ofReal_one]

/-- The **trace** `Tr ρ = ∑ pᵢ`, now also `= (toState ρ) 1`. -/
noncomputable def DensityOperator.trace (ρ : DensityOperator H) : ℝ≥0∞ :=
  ∑' i, ρ.weight i

/-- `[done]` `Tr ρ = 1` (`weight_sum`), consistent with `(toState ρ) 1 = 1`
(`toState_mem_stateSet`). -/
theorem DensityOperator.trace_eq_one (ρ : DensityOperator H) : ρ.trace = 1 :=
  ρ.weight_sum

/-! ## §4  The bridge identities -/

/-- `[done]` **`Tr(ρ E(B))`, literal.**  Evaluating the normal state on the spectral projection
gives the Born probability — the trace form with no trace functional.
Proof: `toStateCLM_apply`, `P.inner_proj` on each `⟪eᵢ, E(B) eᵢ⟫`, then `bornMeasureMixed_apply`.
The value is real (each `⟪eᵢ, E(B) eᵢ⟫` is, by `inner_proj`). -/
theorem toState_proj_eq (P : ProjValMeasure H) (ρ : DensityOperator H)
    {B : Set ℝ} (hB : MeasurableSet B) :
    (ρ.toStateCLM (P.proj B hB)).re = ((bornMeasureMixed P ρ) B).toReal := by
  rw [bornMeasureMixed_apply_norm P ρ hB, DensityOperator.toStateCLM_apply]
  have key : ∀ i, (ρ.weight i).toReal • ⟪ρ.state i, P.proj B hB (ρ.state i)⟫_ℂ
      = ((ρ.weight i).toReal * ‖P.proj B hB (ρ.state i)‖ ^ 2 : ℝ) := fun i => by
    rw [P.inner_proj B hB (ρ.state i), ← P.norm_sq_proj_apply B hB (ρ.state i),
      Complex.real_smul, ← Complex.ofReal_mul]
  simp_rw [key]
  rw [← Complex.ofReal_tsum]
  exact Complex.ofReal_re _

/-- `[done]` **Ensemble invariance.**  The Born measure depends only on the state, not on the
ensemble realizing it: equal `toState`s give equal Born measures.  Proof: `ext` on Borel `B` via
`ext_of_diag`-style reasoning — `toState_proj_eq` rewrites each `μ B` as `(toState · ) (E B)`,
which agree by hypothesis; finiteness cancels `toReal`. -/
theorem bornMeasureMixed_eq_of_toState_eq (P : ProjValMeasure H) {ρ σ : DensityOperator H}
    (h : ρ.toStateCLM = σ.toStateCLM) :
    bornMeasureMixed P ρ = bornMeasureMixed P σ := by
  haveI := isProbabilityMeasure_bornMeasureMixed P ρ
  haveI := isProbabilityMeasure_bornMeasureMixed P σ
  refine Measure.ext fun B hB => ?_
  have hr : ((bornMeasureMixed P ρ) B).toReal = ((bornMeasureMixed P σ) B).toReal := by
    rw [← toState_proj_eq P ρ hB, ← toState_proj_eq P σ hB, h]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hr

/-- **Expectation as `Tr(ρ A)`** — *given that `A` is the observable of `P`*.
`hA` is the link that was missing: it says `A = ∫ s dP(s)` in quadratic-form terms.
Without it `P` and `A` are independent and the equation is false.
(For self-adjoint `A` the `.re` is lossless, since `⟪ξ, A ξ⟫` is then already real.) -/
theorem bornExpectation_eq_toState (P : ProjValMeasure H) (ρ : DensityOperator H)
    (A : H →L[ℂ] H)
    (hA : ∀ ξ : H, (⟪ξ, A ξ⟫_ℂ).re = ∫ s, s ∂(P.diag ξ))
    (hint : Integrable (fun s => s) (bornMeasureMixed P ρ)) :
    (∫ s, s ∂(bornMeasureMixed P ρ)) = (ρ.toStateCLM A).re := by
  rw [DensityOperator.toStateCLM_apply, Complex.re_tsum (ρ.summable_term A)]
  simp only [bornMeasureMixed] at hint ⊢
  rw [integral_sum_measure hint]
  refine tsum_congr fun i => ?_
  rw [integral_smul_measure, Complex.smul_re, hA]

/-! ## §5  Hooks into the convex state geometry (flagged)

These are the payoff of landing in `stateSet`; each is a short consequence once the relevant
`InformationGeometry` API is fixed.

`[done — reuses StateTopology]`  The image of `DensityOperator` sits in the convex, compact state
space: `toState ρ ∈ stateSet` (above), and `stateSet_convex` / `stateSet_isCompact` give the
mixed-state manifold its geometry.  A convex combination of density operators (as ensembles, by
concatenating weighted families) maps to the convex combination of states — affineness of `ρ ↦
toState ρ`.

`[needs InformationGeometry.StatisticalModel API]`  **The weld.**
```
noncomputable def toStatisticalModel (P : ProjValMeasure H) (A : H →L[ℂ] H)
    (ρ : DensityOperator H) : InformationGeometry.StatisticalModel ℝ
```
the classical model induced on `ρ` by an observable, with measure `bornMeasureMixed P ρ` and
score/Fisher data flowing from the convex structure of `stateSet`.  This is what
`CramerRao.Quantum` consumes; the quantum Fisher information is the pullback of the Fisher metric
along `ρ ↦ toStatisticalModel`.

Note (pure states): `DensityOperator.pure ψ` maps under `toState` to the vector state
`⟪ψ, · ψ⟫`, which is an extreme point of `stateSet`; but `pureStateSet` (the Krein–Milman
extreme points) is strictly larger — it contains singular pure states with no vector (hence no
`DensityOperator`) realization.  So `DensityOperator.pure` is a section of, not a bijection
onto, the *normal* pure states.
-/

end Spectra.QuantumMechanics.BornRule
