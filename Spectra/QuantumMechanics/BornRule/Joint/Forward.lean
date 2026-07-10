/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.BornRule.Joint.Measure
/-!
# Joint spectral measures — the forward construction (headline results)

This file completes the forward direction of the relational Born-rule layer (`Joint.Defs`,
sorry-free, easy/backward half): the operator field `jointEffect` recovered by polarizing the
quadratic form `ξ ↦ jointScalarMeasure ξ` (G2.3), the joint POVM `jointPOVM` and its cylinder
marginals (G2.5), and the multiplicativity that makes it a genuine PVM (G2.4, `IsProjective`).
All `sorry`-free and axiom-clean.

* `stronglyCommute_iff_jointPVM` — the corrected equivalence.  Its **backward** half is the proved
  `stronglyCommute_of_jointPVM` (`Joint.Defs`); the **forward** half — the genuine new construction
  (Goal 2) — produces a joint projective PVM on `ℝ²` from commuting PVMs by Carathéodory extension
  of the bimeasure content `μ_ξ(S×T) = ⟪ξ, E_A(S)E_B(T)ξ⟫` (`jointScalarMeasure`, `Joint.Measure`),
  with the operator field recovered by polarization (`jointEffect`).
* `jointBornMeasure_correlation` — the correlation identity `∫ xy dμ_ξ = ⟪ξ, A(Bξ)⟫.re` (Goal 3),
  the 2-D analogue of `weak_first_moment`: truncate `xy` to `[-N,N]²`, identify the truncated
  integral with the operator product `Φ_A(x·1_N)Φ_B(y·1_N)` (Step A, `joint_product_form`),
  collapse it to `E_A([-N,N])E_B([-N,N])(A(Bξ))` (Step C, `joint_truncated_vector`), and pass to the
  limit.  The bridge to Bell/CHSH.

## Main statements

* `stronglyCommute_iff_jointPVM` — the corrected equivalence between strong commutativity of a pair
  of self-adjoint operators and the existence of a projective joint POVM with the right cylinder
  marginals (the multivariate spectral theorem, headline result).
* `jointEffect`, `jointPOVM` — the operator field and its packaging as a `POVM H (ℝ × ℝ)`.
* `jointPOVM_isProjective`, `jointPOVM_isJointOf` — the joint POVM is a genuine PVM (G2.4) with the
  correct cylinder marginals `M(S × ℝ) = E_A(S)`, `M(ℝ × T) = E_B(T)` (G2.5).
* `jointBornMeasure_correlation` — the cross-moment identity `∫ xy dμ_ξ = ⟪ξ, A(Bξ)⟫.re`.

## Implementation notes

The per-state joint measure `μ_ξ` (built in `Joint.Measure`) is obtained by **Carathéodory
extension** of the bimeasure rectangle content `μ_ξ(S × T) = ⟪ξ, E_A(S)E_B(T)ξ⟫` along the rectangle
semiring, with ∅-continuity discharged by an Alexandrov compact-inner-regularity (Route T /
tightness) argument rather than the more standard product-measure construction — `μ_ξ` is genuinely
**not** a product measure, which is why Fubini is unavailable in the correlation proof and is
replaced by the operator product `Φ_A(f)Φ_B(g)`.

The operator field `jointEffect E` is recovered by **polarizing** the real quadratic form
`ξ ↦ μ_ξ(E)`: each sesquilinearity/multiplicativity identity is proved by Dynkin (π–λ) induction
over the rectangle π-system, working at the **sesquilinear-form** level (`crossMeasureForm`) where
σ-additivity is the clean scalar `crossMeasureForm_iUnion` and no operator-topology σ-additivity is
ever needed.  Riesz packaging (`continuousLinearMapOfBilin`, then adjoint) turns the bounded form
into the operator.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*][reedsimon1980],
  §VIII.3 (the spectral theorem and its multivariate/joint form for commuting families).
* [Halmos, *Introduction to Hilbert Space and the Theory of Spectral Multiplicity*][halmos1951]
  (product spectral measures for commuting normal operators).

## Tags

joint spectral measure, projection-valued measure, PVM, POVM, strong commutativity, multivariate
spectral theorem, Carathéodory extension, correlation, Bell, CHSH
-/

open MeasureTheory Complex Spectra Filter Topology
open scoped InnerProductSpace
open Spectra.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.QuantumMechanics.BornRule

open PVM Spectra.ProjValMeasure Spectra.AxisGrid

/-! ## G2.3 — `μ_ξ(E)` is a quadratic form in `ξ` (the operator-field foundation)

For the operator field `effect E` (built by polarizing `ξ ↦ μ_ξ(E)`) to exist, the real quadratic
form `q_E(ξ) = μ_ξ(E)` must satisfy the parallelogram law.  This holds for **every** measurable
`E ⊆ ℝ²` by a Dynkin (π–λ) induction over the rectangle π-system: on rectangles it is the diagonal
parallelogram of the projection `E_A(S)E_B(T)`; it passes to complements (`μ_ξ(Eᶜ) = ‖ξ‖² − μ_ξ(E)`,
with the norm's own parallelogram law) and to countable disjoint unions (σ-additivity of the genuine
measure `μ_ξ`). -/

/-- **`μ_ξ(E)` satisfies the parallelogram law in `ξ`, for every measurable `E`.**  Hence
`ξ ↦ μ_ξ(E)` is a bounded (`≤ ‖ξ‖²`) quadratic form, and polarizes to the sesquilinear form of the
operator `effect E` (G2.3).  Proved by Dynkin induction on the rectangle π-system. -/
theorem jointScalarMeasure_parallelogram (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (ψ φ : H) :
    (jointScalarMeasure A B hSC (ψ + φ) E).toReal
        + (jointScalarMeasure A B hSC (ψ - φ) E).toReal
      = 2 * (jointScalarMeasure A B hSC ψ E).toReal
        + 2 * (jointScalarMeasure A B hSC φ E).toReal := by
  classical
  set q : Set (ℝ × ℝ) → H → ℝ := fun E ξ => (jointScalarMeasure A B hSC ξ E).toReal with _hq
  have hqE : ∀ (E : Set (ℝ × ℝ)) (ξ : H),
      q E ξ = (jointScalarMeasure A B hSC ξ E).toReal := fun _ _ => rfl
  -- the diagonal of an operator obeys the parallelogram law (`ProjValMeasure.diag_parallelogram`)
  have hrepar : ∀ (P : H →L[ℂ] H) (ψ φ : H),
      (⟪ψ + φ, P (ψ + φ)⟫_ℂ).re + (⟪ψ - φ, P (ψ - φ)⟫_ℂ).re
        = 2 * (⟪ψ, P ψ⟫_ℂ).re + 2 * (⟪φ, P φ⟫_ℂ).re := by
    intro P ψ φ
    have h2 := congrArg Complex.re (ProjValMeasure.diag_parallelogram P ψ φ)
    simpa using h2
  -- total mass `q univ ξ = ‖ξ‖²`
  have hmass : ∀ ξ : H, q Set.univ ξ = ‖ξ‖ ^ 2 := by
    intro ξ
    have hu : jointScalarMeasure A B hSC ξ Set.univ = A.spectralPVM.diag ξ Set.univ := by
      rw [← Set.univ_prod_univ,
        jointScalarMeasure_prod A B hSC ξ MeasurableSet.univ MeasurableSet.univ,
        B.spectralPVM.proj_univ, ContinuousLinearMap.id_apply]
    rw [hqE, hu, A.spectralPVM.diag_univ_toReal]
  -- the property is closed under the Dynkin operations on the rectangle π-system
  refine MeasurableSpace.induction_on_inter
    (C := fun E _ => ∀ ψ φ : H, q E (ψ + φ) + q E (ψ - φ) = 2 * q E ψ + 2 * q E φ)
    generateFrom_jointRectangles isSetSemiring_jointRectangles.isPiSystem ?_ ?_ ?_ ?_ E hE ψ φ
  · -- empty
    intro ψ φ; simp only [hqE, measure_empty, ENNReal.toReal_zero, mul_zero, add_zero]
  · -- basic: rectangles, via the projection's diagonal parallelogram
    rintro _ ⟨S, T, hS, hT, rfl⟩ ψ φ
    have hbasic : ∀ ξ : H, q (S ×ˢ T) ξ
        = (⟪ξ, (A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ⟫_ℂ).re := by
      intro ξ
      rw [hqE, jointScalarMeasure_prod_norm_sq A B hSC ξ hS hT,
        norm_sq_apply_of_isStarProjection (jointRect_isStarProjection A B hSC hS hT) ξ]
    rw [hbasic, hbasic, hbasic, hbasic]
    exact hrepar _ ψ φ
  · -- complement: `q Eᶜ ξ = ‖ξ‖² − q E ξ`
    intro t htm ih ψ φ
    have hcompl : ∀ ξ : H, q tᶜ ξ = ‖ξ‖ ^ 2 - q t ξ := by
      intro ξ
      have hle : jointScalarMeasure A B hSC ξ t ≤ jointScalarMeasure A B hSC ξ Set.univ :=
        measure_mono (Set.subset_univ t)
      rw [hqE tᶜ ξ, measure_compl htm (measure_ne_top _ _),
        ENNReal.toReal_sub_of_le hle (measure_ne_top _ _), ← hqE t ξ, ← hqE Set.univ ξ, hmass]
    rw [hcompl, hcompl, hcompl, hcompl]
    have hpar := parallelogram_law_with_norm ℂ ψ φ
    have hih := ih ψ φ
    nlinarith [hpar, hih]
  · -- countable disjoint union: σ-additivity of `μ_ξ`
    intro f hfd hfm ih ψ φ
    have hsum : ∀ ξ : H, q (⋃ i, f i) ξ = ∑' i, q (f i) ξ := by
      intro ξ
      rw [hqE, measure_iUnion hfd hfm, ENNReal.tsum_toReal_eq (fun i => measure_ne_top _ _)]
    have hsummable : ∀ ξ : H, Summable (fun i => q (f i) ξ) := by
      intro ξ
      apply ENNReal.summable_toReal
      rw [← measure_iUnion hfd hfm]
      exact measure_ne_top _ _
    rw [hsum, hsum, hsum, hsum,
      ← (hsummable (ψ + φ)).tsum_add (hsummable (ψ - φ)),
      ← tsum_mul_left, ← tsum_mul_left,
      ← ((hsummable ψ).mul_left 2).tsum_add ((hsummable φ).mul_left 2)]
    exact tsum_congr fun i => ih i ψ φ

/-! ## G2.3 — the operator field `jointEffect E` (polarizing the quadratic form `μ_ξ(E)`)

The quadratic form `q_E(ξ) = μ_ξ(E)` polarizes to `crossMeasureForm E ψ φ =
¼(q_E(ψ+φ) − q_E(ψ−φ) − i·q_E(ψ+iφ) + i·q_E(ψ−iφ))`, a bounded sesquilinear form in `(ψ, φ)`.  Each
sesquilinear identity is proved by Dynkin induction over the rectangle π-system, reducing to the
rectangle case `crossMeasureForm (S ×ˢ T) ψ φ = ⟪ψ, E_A(S)E_B(T) φ⟫` where it is the (honest,
ℂ-linear) projection effect.  Riesz packaging (`continuousLinearMapOfBilin`, then adjoint) turns the
form into the operator `jointEffect E`, with `⟪ξ, jointEffect E ξ⟫ = μ_ξ(E)` (the diagonal collapse
`crossMeasureForm_diag`) and `jointEffect (S ×ˢ T) = E_A(S)E_B(T)`. -/

omit [CompleteSpace H] in
/-- **Polarization, right slot.**  The off-diagonal `⟪ψ, T φ⟫` is the fixed `ℂ`-combination of the
diagonal `z ↦ ⟪z, T z⟫` — the mirror of `inner_op_eq_polarization` (which polarizes `⟪T ψ, φ⟫`).
Holds for *any* `T` (no self-adjointness). -/
theorem inner_polarization_right (T : H →L[ℂ] H) (ψ φ : H) :
    ⟪ψ, T φ⟫_ℂ = (1 / 4 : ℂ) *
      ( ⟪ψ + φ, T (ψ + φ)⟫_ℂ - ⟪ψ - φ, T (ψ - φ)⟫_ℂ
        - I * ⟪ψ + I • φ, T (ψ + I • φ)⟫_ℂ + I * ⟪ψ - I • φ, T (ψ - I • φ)⟫_ℂ ) := by
  have hI : (starRingEnd ℂ) I = -I := by change star I = -I; simp [Complex.conj_I]
  simp only [map_add, map_sub, map_smul,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, hI]
  ring_nf; simp only [Complex.I_sq]; ring

/-- The **complex polarized form** of the joint scalar measure: `crossMeasureForm E ψ φ` is the
`ℂ`-combination of the four real masses `μ_{ψ±φ}(E)`, `μ_{ψ±iφ}(E)` whose diagonal is `μ_ξ(E)` and
whose rectangle value is `⟪ψ, E_A(S)E_B(T) φ⟫`.  It is the sesquilinear form of `jointEffect E`. -/
noncomputable def crossMeasureForm (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) (E : Set (ℝ × ℝ)) (ψ φ : H) : ℂ :=
  (1 / 4 : ℂ) *
    ( ((jointScalarMeasure A B hSC (ψ + φ) E).toReal : ℂ)
      - ((jointScalarMeasure A B hSC (ψ - φ) E).toReal : ℂ)
      - I * ((jointScalarMeasure A B hSC (ψ + I • φ) E).toReal : ℂ)
      + I * ((jointScalarMeasure A B hSC (ψ - I • φ) E).toReal : ℂ) )

omit [CompleteSpace H] in
/-- The diagonal `⟪ξ, ξ⟫` as a complex coercion of `‖ξ‖²` (a `Complex.ofReal`-headed restatement of
`inner_self_eq_norm_sq_to_K`, robust under the `RCLike`/`Complex` coercion split). -/
theorem inner_self_complex (ξ : H) : ⟪ξ, ξ⟫_ℂ = ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]; norm_cast

/-- **Complement mass.**  `μ_ξ(Eᶜ) = ‖ξ‖² − μ_ξ(E)`, since the total mass is `‖ξ‖²`. -/
theorem jointScalarMeasure_compl_toReal (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) (ξ : H) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) :
    (jointScalarMeasure A B hSC ξ Eᶜ).toReal
      = ‖ξ‖ ^ 2 - (jointScalarMeasure A B hSC ξ E).toReal := by
  have hle : jointScalarMeasure A B hSC ξ E ≤ jointScalarMeasure A B hSC ξ Set.univ :=
    measure_mono (Set.subset_univ E)
  have hmass : (jointScalarMeasure A B hSC ξ Set.univ).toReal = ‖ξ‖ ^ 2 := by
    have hu : jointScalarMeasure A B hSC ξ Set.univ = A.spectralPVM.diag ξ Set.univ := by
      rw [← Set.univ_prod_univ,
        jointScalarMeasure_prod A B hSC ξ MeasurableSet.univ MeasurableSet.univ,
        B.spectralPVM.proj_univ, ContinuousLinearMap.id_apply]
    rw [hu, A.spectralPVM.diag_univ_toReal]
  rw [measure_compl hE (measure_ne_top _ _),
    ENNReal.toReal_sub_of_le hle (measure_ne_top _ _), hmass]

/-- **Diagonal of the rectangle effect.**  `μ_ξ(S ×ˢ T) = ⟪ξ, E_A(S)E_B(T) ξ⟫`: the diagonal mass is
the diagonal of the (self-adjoint, idempotent) rectangle projection
(`norm_sq_apply_of_isStarProjection` for the real part; idempotence + self-adjointness for vanishing
imaginary part). -/
theorem jointRect_diag_complex (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (ξ : H) :
    ((jointScalarMeasure A B hSC ξ (S ×ˢ T)).toReal : ℂ)
      = ⟪ξ, (A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ⟫_ℂ := by
  have hsp := jointRect_isStarProjection A B hSC hS hT
  have h1 : ⟪(A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ,
      (A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ⟫_ℂ
      = ⟪ξ, (A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hsp.isSelfAdjoint.adjoint_eq,
      ← ContinuousLinearMap.mul_apply, hsp.isIdempotentElem.eq]
  refine Complex.ext ?_ ?_
  · rw [Complex.ofReal_re, jointScalarMeasure_prod_norm_sq A B hSC ξ hS hT,
      norm_sq_apply_of_isStarProjection hsp ξ]
  · rw [Complex.ofReal_im, ← h1]
    exact (inner_self_im (𝕜 := ℂ) _).symm

/-- **Base case.**  On a rectangle the form is the honest projection effect:
`crossMeasureForm (S ×ˢ T) ψ φ = ⟪ψ, E_A(S)E_B(T) φ⟫` — each diagonal mass is the star-projection
diagonal (`jointRect_diag_complex`) and polarization (`inner_polarization_right`) reassembles it. -/
theorem crossMeasureForm_rect (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (ψ φ : H) :
    crossMeasureForm A B hSC (S ×ˢ T) ψ φ
      = ⟪ψ, (A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) φ⟫_ℂ := by
  rw [crossMeasureForm, jointRect_diag_complex A B hSC hS hT (ψ + φ),
    jointRect_diag_complex A B hSC hS hT (ψ - φ), jointRect_diag_complex A B hSC hS hT (ψ + I • φ),
    jointRect_diag_complex A B hSC hS hT (ψ - I • φ),
    inner_polarization_right (A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ψ φ]

/-- **Complement closure.**  `crossMeasureForm Eᶜ ψ φ = ⟪ψ, φ⟫ − crossMeasureForm E ψ φ`: the four
masses split as `μ_z(Eᶜ) = ‖z‖² − μ_z(E)`, the `‖·‖²` part polarizes to the inner product `⟪ψ, φ⟫`
(`inner_polarization_right` at `id`), and the rest is `−crossMeasureForm E`. -/
theorem crossMeasureForm_compl (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (ψ φ : H) :
    crossMeasureForm A B hSC Eᶜ ψ φ = ⟪ψ, φ⟫_ℂ - crossMeasureForm A B hSC E ψ φ := by
  have hc : ∀ z : H, ((jointScalarMeasure A B hSC z Eᶜ).toReal : ℂ)
      = ((‖z‖ ^ 2 : ℝ) : ℂ) - ((jointScalarMeasure A B hSC z E).toReal : ℂ) := by
    intro z; rw [jointScalarMeasure_compl_toReal A B hSC z hE]; push_cast; ring
  have hnorm : ⟪ψ, φ⟫_ℂ = (1 / 4 : ℂ) *
      ( ((‖ψ + φ‖ ^ 2 : ℝ) : ℂ) - ((‖ψ - φ‖ ^ 2 : ℝ) : ℂ)
        - I * ((‖ψ + I • φ‖ ^ 2 : ℝ) : ℂ) + I * ((‖ψ - I • φ‖ ^ 2 : ℝ) : ℂ) ) := by
    have h := inner_polarization_right (ContinuousLinearMap.id ℂ H) ψ φ
    simp only [ContinuousLinearMap.id_apply] at h
    rw [h]; simp only [inner_self_complex]
  rw [crossMeasureForm, crossMeasureForm, hc (ψ + φ), hc (ψ - φ), hc (ψ + I • φ), hc (ψ - I • φ),
    hnorm]
  ring

/-- **Countable disjoint-union closure.**  `crossMeasureForm (⋃ i, f i) ψ φ = ∑' i, crossMeasureForm
(f i) ψ φ`: each mass is σ-additive (`measure_iUnion`), `Complex.ofReal_tsum` moves the coercion
through, and `tsum` linearity reassembles the four series into one. -/
theorem crossMeasureForm_iUnion (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B)
    {f : ℕ → Set (ℝ × ℝ)} (hd : Pairwise (Function.onFun Disjoint f))
    (hm : ∀ i, MeasurableSet (f i)) (ψ φ : H) :
    crossMeasureForm A B hSC (⋃ i, f i) ψ φ = ∑' i, crossMeasureForm A B hSC (f i) ψ φ := by
  have hsumm : ∀ z : H, Summable (fun i => (jointScalarMeasure A B hSC z (f i)).toReal) := by
    intro z; apply ENNReal.summable_toReal; rw [← measure_iUnion hd hm]; exact measure_ne_top _ _
  have hsummC : ∀ z : H, Summable (fun i => ((jointScalarMeasure A B hSC z (f i)).toReal : ℂ)) :=
    fun z => (Complex.summable_ofReal).mpr (hsumm z)
  have hz : ∀ z : H, ((jointScalarMeasure A B hSC z (⋃ i, f i)).toReal : ℂ)
      = ∑' i, ((jointScalarMeasure A B hSC z (f i)).toReal : ℂ) := by
    intro z
    rw [measure_iUnion hd hm, ENNReal.tsum_toReal_eq (fun i => measure_ne_top _ _),
      Complex.ofReal_tsum]
  have s1 := hsummC (ψ + φ); have s2 := hsummC (ψ - φ)
  have s3 := hsummC (ψ + I • φ); have s4 := hsummC (ψ - I • φ)
  symm
  calc ∑' i, crossMeasureForm A B hSC (f i) ψ φ
      = (1 / 4 : ℂ) * ∑' i,
          ( ((jointScalarMeasure A B hSC (ψ + φ) (f i)).toReal : ℂ)
            - ((jointScalarMeasure A B hSC (ψ - φ) (f i)).toReal : ℂ)
            - I * ((jointScalarMeasure A B hSC (ψ + I • φ) (f i)).toReal : ℂ)
            + I * ((jointScalarMeasure A B hSC (ψ - I • φ) (f i)).toReal : ℂ) ) := by
        rw [← tsum_mul_left]; exact tsum_congr fun i => by rw [crossMeasureForm]
    _ = (1 / 4 : ℂ) *
          ( (∑' i, ((jointScalarMeasure A B hSC (ψ + φ) (f i)).toReal : ℂ))
            - (∑' i, ((jointScalarMeasure A B hSC (ψ - φ) (f i)).toReal : ℂ))
            - I * (∑' i, ((jointScalarMeasure A B hSC (ψ + I • φ) (f i)).toReal : ℂ))
            + I * (∑' i, ((jointScalarMeasure A B hSC (ψ - I • φ) (f i)).toReal : ℂ)) ) := by
        congr 1
        rw [Summable.tsum_add ((s1.sub s2).sub (s3.mul_left I)) (s4.mul_left I),
          Summable.tsum_sub (s1.sub s2) (s3.mul_left I), Summable.tsum_sub s1 s2,
          tsum_mul_left, tsum_mul_left]
    _ = crossMeasureForm A B hSC (⋃ i, f i) ψ φ := by
        rw [crossMeasureForm, hz (ψ + φ), hz (ψ - φ), hz (ψ + I • φ), hz (ψ - I • φ)]

/-- **Summability** of the per-cell forms (each of the four masses is summable; the `ℂ`-combination
inherits it). -/
theorem crossMeasureForm_summable (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) {f : ℕ → Set (ℝ × ℝ)}
    (hd : Pairwise (Function.onFun Disjoint f)) (hm : ∀ i, MeasurableSet (f i)) (ψ φ : H) :
    Summable (fun i => crossMeasureForm A B hSC (f i) ψ φ) := by
  have hsumm : ∀ z : H, Summable (fun i => ((jointScalarMeasure A B hSC z (f i)).toReal : ℂ)) := by
    intro z
    refine (Complex.summable_ofReal).mpr (ENNReal.summable_toReal ?_)
    rw [← measure_iUnion hd hm]; exact measure_ne_top _ _
  simp only [crossMeasureForm]
  exact Summable.mul_left _
    ((((hsumm _).sub (hsumm _)).sub ((hsumm _).mul_left I)).add ((hsumm _).mul_left I))

/-! ### Sesquilinearity of `crossMeasureForm` (by Dynkin induction over the rectangle π-system)

Each identity reduces — on rectangles — to (conjugate-)linearity of the honest projection effect
`⟪ψ, E_A(S)E_B(T) φ⟫`, and passes to complements (via `crossMeasureForm_compl` + the matching inner
identity) and to countable disjoint unions (via `crossMeasureForm_iUnion` + `tsum` linearity). -/

/-- Additive in the (conjugate-linear) left slot. -/
theorem crossMeasureForm_add_left (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (ψ₁ ψ₂ φ : H) :
    crossMeasureForm A B hSC E (ψ₁ + ψ₂) φ
      = crossMeasureForm A B hSC E ψ₁ φ + crossMeasureForm A B hSC E ψ₂ φ := by
  refine MeasurableSpace.induction_on_inter
    (C := fun E _ => ∀ ψ₁ ψ₂ φ : H, crossMeasureForm A B hSC E (ψ₁ + ψ₂) φ
      = crossMeasureForm A B hSC E ψ₁ φ + crossMeasureForm A B hSC E ψ₂ φ)
    generateFrom_jointRectangles isSetSemiring_jointRectangles.isPiSystem ?_ ?_ ?_ ?_ E hE ψ₁ ψ₂ φ
  · intro ψ₁ ψ₂ φ; simp [crossMeasureForm]
  · rintro _ ⟨S, T, hS, hT, rfl⟩ ψ₁ ψ₂ φ
    rw [crossMeasureForm_rect A B hSC hS hT, crossMeasureForm_rect A B hSC hS hT,
      crossMeasureForm_rect A B hSC hS hT, inner_add_left]
  · intro t htm ih ψ₁ ψ₂ φ
    rw [crossMeasureForm_compl A B hSC htm, crossMeasureForm_compl A B hSC htm,
      crossMeasureForm_compl A B hSC htm, inner_add_left, ih ψ₁ ψ₂ φ]
    ring
  · intro g hgd hgm ih ψ₁ ψ₂ φ
    rw [crossMeasureForm_iUnion A B hSC hgd hgm, crossMeasureForm_iUnion A B hSC hgd hgm,
      crossMeasureForm_iUnion A B hSC hgd hgm,
      ← (crossMeasureForm_summable A B hSC hgd hgm ψ₁ φ).tsum_add
        (crossMeasureForm_summable A B hSC hgd hgm ψ₂ φ)]
    exact tsum_congr fun i => ih i ψ₁ ψ₂ φ

/-- Conjugate-homogeneous in the left slot. -/
theorem crossMeasureForm_smul_left (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (c : ℂ) (ψ φ : H) :
    crossMeasureForm A B hSC E (c • ψ) φ
      = (starRingEnd ℂ) c * crossMeasureForm A B hSC E ψ φ := by
  refine MeasurableSpace.induction_on_inter
    (C := fun E _ => ∀ ψ φ : H, crossMeasureForm A B hSC E (c • ψ) φ
      = (starRingEnd ℂ) c * crossMeasureForm A B hSC E ψ φ)
    generateFrom_jointRectangles isSetSemiring_jointRectangles.isPiSystem ?_ ?_ ?_ ?_ E hE ψ φ
  · intro ψ φ; simp [crossMeasureForm]
  · rintro _ ⟨S, T, hS, hT, rfl⟩ ψ φ
    rw [crossMeasureForm_rect A B hSC hS hT, crossMeasureForm_rect A B hSC hS hT, inner_smul_left]
  · intro t htm ih ψ φ
    rw [crossMeasureForm_compl A B hSC htm, crossMeasureForm_compl A B hSC htm,
      inner_smul_left, ih ψ φ]
    ring
  · intro g hgd hgm ih ψ φ
    rw [crossMeasureForm_iUnion A B hSC hgd hgm, crossMeasureForm_iUnion A B hSC hgd hgm,
      ← tsum_mul_left]
    exact tsum_congr fun i => ih i ψ φ

/-- Additive in the (linear) right slot. -/
theorem crossMeasureForm_add_right (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (ψ φ₁ φ₂ : H) :
    crossMeasureForm A B hSC E ψ (φ₁ + φ₂)
      = crossMeasureForm A B hSC E ψ φ₁ + crossMeasureForm A B hSC E ψ φ₂ := by
  refine MeasurableSpace.induction_on_inter
    (C := fun E _ => ∀ ψ φ₁ φ₂ : H, crossMeasureForm A B hSC E ψ (φ₁ + φ₂)
      = crossMeasureForm A B hSC E ψ φ₁ + crossMeasureForm A B hSC E ψ φ₂)
    generateFrom_jointRectangles isSetSemiring_jointRectangles.isPiSystem ?_ ?_ ?_ ?_ E hE ψ φ₁ φ₂
  · intro ψ φ₁ φ₂; simp [crossMeasureForm]
  · rintro _ ⟨S, T, hS, hT, rfl⟩ ψ φ₁ φ₂
    rw [crossMeasureForm_rect A B hSC hS hT, crossMeasureForm_rect A B hSC hS hT,
      crossMeasureForm_rect A B hSC hS hT, map_add, inner_add_right]
  · intro t htm ih ψ φ₁ φ₂
    rw [crossMeasureForm_compl A B hSC htm, crossMeasureForm_compl A B hSC htm,
      crossMeasureForm_compl A B hSC htm, inner_add_right, ih ψ φ₁ φ₂]
    ring
  · intro g hgd hgm ih ψ φ₁ φ₂
    rw [crossMeasureForm_iUnion A B hSC hgd hgm, crossMeasureForm_iUnion A B hSC hgd hgm,
      crossMeasureForm_iUnion A B hSC hgd hgm,
      ← (crossMeasureForm_summable A B hSC hgd hgm ψ φ₁).tsum_add
        (crossMeasureForm_summable A B hSC hgd hgm ψ φ₂)]
    exact tsum_congr fun i => ih i ψ φ₁ φ₂

/-- Homogeneous in the (linear) right slot. -/
theorem crossMeasureForm_smul_right (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (c : ℂ) (ψ φ : H) :
    crossMeasureForm A B hSC E ψ (c • φ) = c * crossMeasureForm A B hSC E ψ φ := by
  refine MeasurableSpace.induction_on_inter
    (C := fun E _ => ∀ ψ φ : H, crossMeasureForm A B hSC E ψ (c • φ)
      = c * crossMeasureForm A B hSC E ψ φ)
    generateFrom_jointRectangles isSetSemiring_jointRectangles.isPiSystem ?_ ?_ ?_ ?_ E hE ψ φ
  · intro ψ φ; simp [crossMeasureForm]
  · rintro _ ⟨S, T, hS, hT, rfl⟩ ψ φ
    rw [crossMeasureForm_rect A B hSC hS hT, crossMeasureForm_rect A B hSC hS hT, map_smul,
      inner_smul_right]
  · intro t htm ih ψ φ
    rw [crossMeasureForm_compl A B hSC htm, crossMeasureForm_compl A B hSC htm,
      inner_smul_right, ih ψ φ]
    ring
  · intro g hgd hgm ih ψ φ
    rw [crossMeasureForm_iUnion A B hSC hgd hgm, crossMeasureForm_iUnion A B hSC hgd hgm,
      ← tsum_mul_left]
    exact tsum_congr fun i => ih i ψ φ

/-- **Diagonal collapse.**  `crossMeasureForm E ξ ξ = μ_ξ(E)` for every measurable `E` — the
polarized form recovers the original quadratic form on the diagonal.  Dynkin induction: rectangles
(`jointRect_diag_complex`), complements (`jointScalarMeasure_compl_toReal` + `inner_self_complex`),
countable unions (σ-additivity). -/
theorem crossMeasureForm_diag (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (ξ : H) :
    crossMeasureForm A B hSC E ξ ξ = ((jointScalarMeasure A B hSC ξ E).toReal : ℂ) := by
  refine MeasurableSpace.induction_on_inter
    (C := fun E _ => ∀ ξ : H,
      crossMeasureForm A B hSC E ξ ξ = ((jointScalarMeasure A B hSC ξ E).toReal : ℂ))
    generateFrom_jointRectangles isSetSemiring_jointRectangles.isPiSystem ?_ ?_ ?_ ?_ E hE ξ
  · intro ξ; simp [crossMeasureForm]
  · rintro _ ⟨S, T, hS, hT, rfl⟩ ξ
    rw [crossMeasureForm_rect A B hSC hS hT, ← jointRect_diag_complex A B hSC hS hT ξ]
  · intro t htm ih ξ
    rw [crossMeasureForm_compl A B hSC htm, ih ξ, inner_self_complex,
      jointScalarMeasure_compl_toReal A B hSC ξ htm]
    push_cast; ring
  · intro g hgd hgm ih ξ
    rw [crossMeasureForm_iUnion A B hSC hgd hgm, measure_iUnion hgd hgm,
      ENNReal.tsum_toReal_eq (fun i => measure_ne_top _ _), Complex.ofReal_tsum]
    exact tsum_congr fun i => ih i ξ

/-! ### Riesz packaging: the operator field `jointEffect E`

The bounded sesquilinear `crossMeasureForm E` is represented (`continuousLinearMapOfBilin`, adjoint)
by the operator `jointEffect E`, with `⟪ξ, jointEffect E ξ⟫ = μ_ξ(E)` (the POVM weld) and
`jointEffect (S ×ˢ T) = E_A(S)E_B(T)` (rectangle agreement). -/

/-- **Operator-norm bound** for the form, `‖crossMeasureForm E ψ φ‖ ≤ 2‖ψ‖‖φ‖`: a crude
`‖ψ‖²+‖φ‖²` bound (mass bound + the two parallelogram laws), homogenized by rescaling `φ ↦ t•φ`. -/
theorem crossMeasureForm_norm_le (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (ψ φ : H) :
    ‖crossMeasureForm A B hSC E ψ φ‖ ≤ 2 * ‖ψ‖ * ‖φ‖ := by
  -- each mass `μ_z(E) ≤ μ_z(univ) = ‖z‖²`
  have hm_le : ∀ z : H, ‖((jointScalarMeasure A B hSC z E).toReal : ℂ)‖ ≤ ‖z‖ ^ 2 := by
    intro z
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    have hu : jointScalarMeasure A B hSC z Set.univ = A.spectralPVM.diag z Set.univ := by
      rw [← Set.univ_prod_univ,
        jointScalarMeasure_prod A B hSC z MeasurableSet.univ MeasurableSet.univ,
        B.spectralPVM.proj_univ, ContinuousLinearMap.id_apply]
    calc (jointScalarMeasure A B hSC z E).toReal
        ≤ (jointScalarMeasure A B hSC z Set.univ).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ E))
      _ = (A.spectralPVM.diag z Set.univ).toReal := by rw [hu]
      _ = ‖z‖ ^ 2 := A.spectralPVM.diag_univ_toReal z
  -- crude bound `‖crossMeasureForm E x y‖ ≤ ‖x‖² + ‖y‖²`
  have hmain : ∀ x y : H, ‖crossMeasureForm A B hSC E x y‖ ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    intro x y
    have htri : ‖((jointScalarMeasure A B hSC (x + y) E).toReal : ℂ)
          - ((jointScalarMeasure A B hSC (x - y) E).toReal : ℂ)
          - I * ((jointScalarMeasure A B hSC (x + I • y) E).toReal : ℂ)
          + I * ((jointScalarMeasure A B hSC (x - I • y) E).toReal : ℂ)‖
        ≤ ‖((jointScalarMeasure A B hSC (x + y) E).toReal : ℂ)‖
          + ‖((jointScalarMeasure A B hSC (x - y) E).toReal : ℂ)‖
          + ‖((jointScalarMeasure A B hSC (x + I • y) E).toReal : ℂ)‖
          + ‖((jointScalarMeasure A B hSC (x - I • y) E).toReal : ℂ)‖ := by
      have eI3 : ‖I * ((jointScalarMeasure A B hSC (x + I • y) E).toReal : ℂ)‖
          = ‖((jointScalarMeasure A B hSC (x + I • y) E).toReal : ℂ)‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
      have eI4 : ‖I * ((jointScalarMeasure A B hSC (x - I • y) E).toReal : ℂ)‖
          = ‖((jointScalarMeasure A B hSC (x - I • y) E).toReal : ℂ)‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
      calc ‖_ - _ - I * _ + I * _‖
          ≤ ‖((jointScalarMeasure A B hSC (x + y) E).toReal : ℂ)
              - ((jointScalarMeasure A B hSC (x - y) E).toReal : ℂ)
              - I * ((jointScalarMeasure A B hSC (x + I • y) E).toReal : ℂ)‖
            + ‖I * ((jointScalarMeasure A B hSC (x - I • y) E).toReal : ℂ)‖ := norm_add_le _ _
        _ ≤ (‖((jointScalarMeasure A B hSC (x + y) E).toReal : ℂ)
              - ((jointScalarMeasure A B hSC (x - y) E).toReal : ℂ)‖
            + ‖I * ((jointScalarMeasure A B hSC (x + I • y) E).toReal : ℂ)‖)
            + ‖I * ((jointScalarMeasure A B hSC (x - I • y) E).toReal : ℂ)‖ := by
              gcongr; exact norm_sub_le _ _
        _ ≤ ((‖((jointScalarMeasure A B hSC (x + y) E).toReal : ℂ)‖
              + ‖((jointScalarMeasure A B hSC (x - y) E).toReal : ℂ)‖)
            + ‖I * ((jointScalarMeasure A B hSC (x + I • y) E).toReal : ℂ)‖)
            + ‖I * ((jointScalarMeasure A B hSC (x - I • y) E).toReal : ℂ)‖ := by
              gcongr; exact norm_sub_le _ _
        _ = _ := by rw [eI3, eI4]
    have hpar1 : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
      parallelogram_law_with_norm ℂ x y
    have hpar2 : ‖x + I • y‖ ^ 2 + ‖x - I • y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
      have h := parallelogram_law_with_norm ℂ x (I • y)
      rwa [norm_smul, Complex.norm_I, one_mul] at h
    rw [crossMeasureForm, norm_mul,
      show ‖(1 / 4 : ℂ)‖ = 1 / 4 by rw [norm_div, norm_one, Complex.norm_ofNat]]
    have hb := htri.trans (by
      gcongr <;> exact hm_le _ :
      _ ≤ ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 + ‖x + I • y‖ ^ 2 + ‖x - I • y‖ ^ 2)
    nlinarith [hb, hpar1, hpar2, norm_nonneg (crossMeasureForm A B hSC E x y)]
  -- homogenize: handle the zero slots, then rescale `φ ↦ (‖ψ‖/‖φ‖)•φ`
  rcases eq_or_ne φ 0 with rfl | hφ
  · have h0 : crossMeasureForm A B hSC E ψ 0 = 0 := by
      have := crossMeasureForm_smul_right A B hSC hE (0 : ℂ) ψ 0; simpa using this
    simp [h0]
  rcases eq_or_ne ψ 0 with rfl | hψ
  · have h0 : crossMeasureForm A B hSC E 0 φ = 0 := by
      have := crossMeasureForm_smul_left A B hSC hE (0 : ℂ) 0 φ; simpa using this
    simp [h0]
  have hψ0 : (0 : ℝ) < ‖ψ‖ := norm_pos_iff.mpr hψ
  have hφ0 : (0 : ℝ) < ‖φ‖ := norm_pos_iff.mpr hφ
  set t : ℝ := ‖ψ‖ / ‖φ‖ with ht_def
  have ht : 0 < t := div_pos hψ0 hφ0
  have hb := hmain ψ ((t : ℂ) • φ)
  rw [crossMeasureForm_smul_right A B hSC hE (t : ℂ) ψ φ, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.le, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ht.le] at hb
  have htφ : t * ‖φ‖ = ‖ψ‖ := by rw [ht_def]; field_simp
  have key : t * ‖crossMeasureForm A B hSC E ψ φ‖ ≤ ‖ψ‖ ^ 2 + (t * ‖φ‖) ^ 2 := hb
  rw [htφ] at key
  have hfinal : ‖crossMeasureForm A B hSC E ψ φ‖ ≤ (‖ψ‖ ^ 2 + ‖ψ‖ ^ 2) / t :=
    (le_div_iff₀' ht).mpr (by linarith [key])
  refine hfinal.trans (le_of_eq ?_)
  rw [ht_def, div_div_eq_mul_div, div_eq_iff hψ0.ne']
  ring

/-- The polarized pairing `(ψ, φ) ↦ crossMeasureForm E ψ φ`, bundled as a continuous sesquilinear
map (`mk₂'ₛₗ` with conjugation on the left slot; the bound is `crossMeasureForm_norm_le`). -/
noncomputable def crossMeasureFormBilin (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) : H →L⋆[ℂ] H →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
      (fun ψ φ => crossMeasureForm A B hSC E ψ φ)
      (fun ψ₁ ψ₂ φ => crossMeasureForm_add_left A B hSC hE ψ₁ ψ₂ φ)
      (fun c ψ φ => by rw [crossMeasureForm_smul_left A B hSC hE c ψ φ, smul_eq_mul])
      (fun ψ φ₁ φ₂ => crossMeasureForm_add_right A B hSC hE ψ φ₁ φ₂)
      (fun c ψ φ => by
        rw [crossMeasureForm_smul_right A B hSC hE c ψ φ, RingHom.id_apply, smul_eq_mul]))
    2
    (fun ψ φ => crossMeasureForm_norm_le A B hSC hE ψ φ)

@[simp] theorem crossMeasureFormBilin_apply (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (ψ φ : H) :
    crossMeasureFormBilin A B hSC hE ψ φ = crossMeasureForm A B hSC E ψ φ := rfl

/-- **The joint effect** `jointEffect E`: the operator whose sesquilinear form is
`crossMeasureForm E` (`continuousLinearMapOfBilin`, adjointed to put the operator in the second
inner-product slot, as in `spectralCalculus`). -/
noncomputable def jointEffect (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) : H →L[ℂ] H :=
  ContinuousLinearMap.adjoint
    (InnerProductSpace.continuousLinearMapOfBilin (crossMeasureFormBilin A B hSC hE))

/-- The defining identity: `⟪ξ, jointEffect E η⟫ = crossMeasureForm E ξ η`. -/
theorem jointEffect_inner (A B : Spectra.Operator.SelfAdjointOperator H) (hSC : StronglyCommute A B)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (ξ η : H) :
    ⟪ξ, jointEffect A B hSC hE η⟫_ℂ = crossMeasureForm A B hSC E ξ η := by
  simp only [jointEffect]
  rw [ContinuousLinearMap.adjoint_inner_right,
    InnerProductSpace.continuousLinearMapOfBilin_apply, crossMeasureFormBilin_apply]

/-- **The POVM weld.**  `⟪ξ, jointEffect E ξ⟫ = μ_ξ(E)` — the diagonal of the joint effect is the
joint scalar measure. -/
theorem jointEffect_diag (A B : Spectra.Operator.SelfAdjointOperator H) (hSC : StronglyCommute A B)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (ξ : H) :
    ⟪ξ, jointEffect A B hSC hE ξ⟫_ℂ = ((jointScalarMeasure A B hSC ξ E).toReal : ℂ) := by
  rw [jointEffect_inner, crossMeasureForm_diag A B hSC hE ξ]

/-- **Rectangle agreement.**  `jointEffect (S ×ˢ T) = E_A(S)·E_B(T)` — the joint effect on a
rectangle is the product of the spectral projections (determined by the diagonal,
`op_ext_of_inner_self`). -/
theorem jointEffect_rect (A B : Spectra.Operator.SelfAdjointOperator H) (hSC : StronglyCommute A B)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    jointEffect A B hSC (hS.prod hT) = A.spectralPVM.proj S hS * B.spectralPVM.proj T hT := by
  refine op_ext_of_inner_self fun ξ => ?_
  rw [jointEffect_inner, crossMeasureForm_rect A B hSC hS hT]

/-- **Normalization.**  `jointEffect univ = 1`. -/
theorem jointEffect_univ (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) :
    jointEffect A B hSC (MeasurableSet.univ : MeasurableSet (Set.univ : Set (ℝ × ℝ)))
      = ContinuousLinearMap.id ℂ H := by
  refine op_ext_of_inner_self fun ξ => ?_
  rw [jointEffect_diag, ContinuousLinearMap.id_apply, inner_self_complex]
  congr 1
  rw [← Set.univ_prod_univ,
    jointScalarMeasure_prod A B hSC ξ MeasurableSet.univ MeasurableSet.univ,
    B.spectralPVM.proj_univ, ContinuousLinearMap.id_apply, A.spectralPVM.diag_univ_toReal]

/-! ### The joint POVM and its cylinder marginals (G2.5)

`jointEffect` assembles into a `POVM H (ℝ × ℝ)`: the weld `inner_effect` is `jointEffect_diag`, the
normalization is `jointEffect_univ`, and the diagonal data is the joint scalar measure `μ_ξ`.  Its
`IsJointOf A B` is then immediate from rectangle agreement (`jointEffect_rect`) — `M(S × ℝ) =
E_A(S)·E_B(ℝ) = E_A(S)·1 = E_A(S)`.  `IsProjective` — operator multiplicativity on *all* sets (G2.4)
— is proved separately as `jointPOVM_isProjective` (at the sesquilinear-form level, no
operator-topology σ-additivity needed). -/

/-- **The joint POVM** of a strongly-commuting pair: the operator-valued measure on `ℝ²` whose
effects are `jointEffect` and whose diagonal data is the joint scalar measure `μ_ξ`. -/
noncomputable def jointPOVM (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) :
    POVM H (ℝ × ℝ) where
  effect _ hE := jointEffect A B hSC hE
  diag ξ := jointScalarMeasure A B hSC ξ
  diag_finite ξ := jointScalarMeasure_isFiniteMeasure A B hSC ξ
  inner_effect _ hE ξ := jointEffect_diag A B hSC hE ξ
  effect_univ := jointEffect_univ A B hSC

/-- **G2.5 — the joint POVM has the right cylinder marginals.**  `M(S × ℝ) = E_A(S)` and
`M(ℝ × T) = E_B(T)`: immediate from `jointEffect_rect` and `proj_univ` (the other factor is the
identity).  This is the hypothesis that couples the joint PVM to `A` and `B` (`IsJointOf`). -/
theorem jointPOVM_isJointOf (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) :
    (jointPOVM A B hSC).IsJointOf A B := by
  refine ⟨fun S hS => ?_, fun T hT => ?_⟩
  · change jointEffect A B hSC (hS.prod MeasurableSet.univ) = A.spectralPVM.proj S hS
    rw [jointEffect_rect A B hSC hS MeasurableSet.univ, B.spectralPVM.proj_univ]
    exact mul_one _
  · change jointEffect A B hSC (MeasurableSet.univ.prod hT) = B.spectralPVM.proj T hT
    rw [jointEffect_rect A B hSC MeasurableSet.univ hT, A.spectralPVM.proj_univ]
    exact one_mul _

/-! ### G2.4 — `IsProjective`: the joint effects are multiplicative

`jointEffect (B₁ ∩ B₂) = jointEffect B₁ · jointEffect B₂` for *all* measurable `B₁, B₂` — operator
multiplicativity, the field that upgrades the POVM to a genuine PVM.  Proof: two nested Dynkin
inductions (`induction_on_inter`) at the **sesquilinear-form** level, where σ-additivity is the
clean `crossMeasureForm_iUnion` and no operator-topology σ-additivity is ever needed.  The right
factor is
reduced to a rectangle first (`crossMeasureForm_inter_rect`, induct over `B₁`), then the left factor
to an arbitrary set (`crossMeasureForm_inter`, induct over `B₂`), using self-adjointness of
`jointEffect B₁` to keep the inner-product vectors fixed across the second induction. -/

/-- **Finite additivity of `crossMeasureForm`** in its set argument: each diagonal mass
`μ_z(X ∪ Y) = μ_z(X) + μ_z(Y)` (`measure_union`), and the polarization is linear in the masses. -/
theorem crossMeasureForm_union2 (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B)
    {X Y : Set (ℝ × ℝ)} (_hX : MeasurableSet X) (hY : MeasurableSet Y) (hd : Disjoint X Y)
    (ψ φ : H) :
    crossMeasureForm A B hSC (X ∪ Y) ψ φ
      = crossMeasureForm A B hSC X ψ φ + crossMeasureForm A B hSC Y ψ φ := by
  have hm : ∀ z : H, ((jointScalarMeasure A B hSC z (X ∪ Y)).toReal : ℂ)
      = ((jointScalarMeasure A B hSC z X).toReal : ℂ)
        + ((jointScalarMeasure A B hSC z Y).toReal : ℂ) := by
    intro z
    rw [measure_union hd hY, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    push_cast; ring
  rw [crossMeasureForm, crossMeasureForm, crossMeasureForm,
    hm (ψ + φ), hm (ψ - φ), hm (ψ + I • φ), hm (ψ - I • φ)]
  ring

/-- **Each joint effect is self-adjoint.**  `⟪ξ, jointEffect E ξ⟫ = μ_ξ(E)` is real for every `ξ`
(`jointEffect_diag`), and a real diagonal characterizes self-adjointness. -/
theorem jointEffect_isSelfAdjoint (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) : IsSelfAdjoint (jointEffect A B hSC hE) :=
  (jointPOVM A B hSC).isSelfAdjoint_effect E hE

/-- The self-adjointness swap: `⟪jointEffect E ζ, ω⟫ = ⟪ζ, jointEffect E ω⟫`. -/
theorem jointEffect_swap (A B : Spectra.Operator.SelfAdjointOperator H) (hSC : StronglyCommute A B)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (ζ ω : H) :
    ⟪(jointEffect A B hSC hE) ζ, ω⟫_ℂ = ⟪ζ, (jointEffect A B hSC hE) ω⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, (jointEffect_isSelfAdjoint A B hSC hE).adjoint_eq]

/-- **Step A — right factor a rectangle.**  `crossMeasureForm (B₁ ∩ (S₂×T₂)) ξ η =
crossMeasureForm B₁ ξ (jointEffect (S₂×T₂) η)` for all measurable `B₁`.  Dynkin induction over `B₁`
on the rectangle π-system: base = `jointRect_mul`, complement/⋃ = `crossMeasureForm_compl`/`_iUnion`
with the vectors `(ξ, jointEffect (S₂×T₂) η)` fixed. -/
theorem crossMeasureForm_inter_rect (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) {S₂ T₂ : Set ℝ} (hS₂ : MeasurableSet S₂) (hT₂ : MeasurableSet T₂)
    {B₁ : Set (ℝ × ℝ)} (hB₁ : MeasurableSet B₁) :
    ∀ ξ η : H, crossMeasureForm A B hSC (B₁ ∩ (S₂ ×ˢ T₂)) ξ η
      = crossMeasureForm A B hSC B₁ ξ (jointEffect A B hSC (hS₂.prod hT₂) η) := by
  refine MeasurableSpace.induction_on_inter
    (C := fun B₁ _ => ∀ ξ η : H, crossMeasureForm A B hSC (B₁ ∩ (S₂ ×ˢ T₂)) ξ η
      = crossMeasureForm A B hSC B₁ ξ (jointEffect A B hSC (hS₂.prod hT₂) η))
    generateFrom_jointRectangles isSetSemiring_jointRectangles.isPiSystem ?_ ?_ ?_ ?_ B₁ hB₁
  · intro ξ η
    rw [Set.empty_inter]; simp [crossMeasureForm]
  · rintro _ ⟨S₁, T₁, hS₁, hT₁, rfl⟩ ξ η
    rw [Set.prod_inter_prod, crossMeasureForm_rect A B hSC (hS₁.inter hS₂) (hT₁.inter hT₂),
      crossMeasureForm_rect A B hSC hS₁ hT₁, jointEffect_rect A B hSC hS₂ hT₂,
      show (A.spectralPVM.proj S₁ hS₁ * B.spectralPVM.proj T₁ hT₁)
          ((A.spectralPVM.proj S₂ hS₂ * B.spectralPVM.proj T₂ hT₂) η)
        = (A.spectralPVM.proj (S₁ ∩ S₂) (hS₁.inter hS₂)
            * B.spectralPVM.proj (T₁ ∩ T₂) (hT₁.inter hT₂)) η from by
        rw [← ContinuousLinearMap.mul_apply, jointRect_mul A B hSC hS₁ hS₂ hT₁ hT₂]]
  · intro t htm ih ξ η
    have hd : Disjoint (t ∩ (S₂ ×ˢ T₂)) (tᶜ ∩ (S₂ ×ˢ T₂)) := by
      rw [Set.disjoint_left]; rintro x ⟨hxt, _⟩ ⟨hxtc, _⟩; exact hxtc hxt
    have hunion : (t ∩ (S₂ ×ˢ T₂)) ∪ (tᶜ ∩ (S₂ ×ˢ T₂)) = S₂ ×ˢ T₂ := by
      rw [← Set.union_inter_distrib_right, Set.union_compl_self, Set.univ_inter]
    have hkey : crossMeasureForm A B hSC (S₂ ×ˢ T₂) ξ η
        = crossMeasureForm A B hSC (t ∩ (S₂ ×ˢ T₂)) ξ η
          + crossMeasureForm A B hSC (tᶜ ∩ (S₂ ×ˢ T₂)) ξ η := by
      conv_lhs => rw [← hunion]
      exact crossMeasureForm_union2 A B hSC (htm.inter (hS₂.prod hT₂))
        (htm.compl.inter (hS₂.prod hT₂)) hd ξ η
    rw [crossMeasureForm_compl A B hSC htm, ← ih ξ η,
      jointEffect_inner A B hSC (hS₂.prod hT₂) ξ η, hkey]
    ring
  · intro g hgd hgm ih ξ η
    rw [Set.iUnion_inter,
      crossMeasureForm_iUnion A B hSC
        (fun i j hij => (hgd hij).mono Set.inter_subset_left Set.inter_subset_left)
        (fun i => (hgm i).inter (hS₂.prod hT₂)),
      crossMeasureForm_iUnion A B hSC hgd hgm]
    exact tsum_congr fun i => ih i ξ η

/-- **Step B — both factors arbitrary.**  `crossMeasureForm (B₁ ∩ B₂) ξ η =
crossMeasureForm B₂ (jointEffect B₁ ξ) η`.  Dynkin induction over `B₂`: base = Step A + the
self-adjointness swap of `jointEffect B₁`, complement/⋃ with the vectors `(jointEffect B₁ ξ, η)`
fixed. -/
theorem crossMeasureForm_inter (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B)
    {B₁ : Set (ℝ × ℝ)} (hB₁ : MeasurableSet B₁) {B₂ : Set (ℝ × ℝ)} (hB₂ : MeasurableSet B₂) :
    ∀ ξ η : H, crossMeasureForm A B hSC (B₁ ∩ B₂) ξ η
      = crossMeasureForm A B hSC B₂ (jointEffect A B hSC hB₁ ξ) η := by
  refine MeasurableSpace.induction_on_inter
    (C := fun B₂ _ => ∀ ξ η : H, crossMeasureForm A B hSC (B₁ ∩ B₂) ξ η
      = crossMeasureForm A B hSC B₂ (jointEffect A B hSC hB₁ ξ) η)
    generateFrom_jointRectangles isSetSemiring_jointRectangles.isPiSystem ?_ ?_ ?_ ?_ B₂ hB₂
  · intro ξ η
    rw [Set.inter_empty]; simp [crossMeasureForm]
  · rintro _ ⟨S₂, T₂, hS₂, hT₂, rfl⟩ ξ η
    rw [crossMeasureForm_inter_rect A B hSC hS₂ hT₂ hB₁ ξ η,
      ← jointEffect_inner A B hSC hB₁ ξ (jointEffect A B hSC (hS₂.prod hT₂) η),
      ← jointEffect_inner A B hSC (hS₂.prod hT₂) (jointEffect A B hSC hB₁ ξ) η,
      jointEffect_swap A B hSC hB₁ ξ (jointEffect A B hSC (hS₂.prod hT₂) η)]
  · intro t htm ih ξ η
    have hd : Disjoint (B₁ ∩ t) (B₁ ∩ tᶜ) := by
      rw [Set.disjoint_left]; rintro x ⟨_, hxt⟩ ⟨_, hxtc⟩; exact hxtc hxt
    have hunion : (B₁ ∩ t) ∪ (B₁ ∩ tᶜ) = B₁ := by
      rw [← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ]
    have hkey : crossMeasureForm A B hSC B₁ ξ η
        = crossMeasureForm A B hSC (B₁ ∩ t) ξ η + crossMeasureForm A B hSC (B₁ ∩ tᶜ) ξ η := by
      conv_lhs => rw [← hunion]
      exact crossMeasureForm_union2 A B hSC (hB₁.inter htm) (hB₁.inter htm.compl) hd ξ η
    rw [crossMeasureForm_compl A B hSC htm, ← ih ξ η,
      jointEffect_swap A B hSC hB₁ ξ η, jointEffect_inner A B hSC hB₁ ξ η, hkey]
    ring
  · intro g hgd hgm ih ξ η
    rw [Set.inter_iUnion,
      crossMeasureForm_iUnion A B hSC
        (fun i j hij => (hgd hij).mono Set.inter_subset_right Set.inter_subset_right)
        (fun i => hB₁.inter (hgm i)),
      crossMeasureForm_iUnion A B hSC hgd hgm]
    exact tsum_congr fun i => ih i ξ η

/-- **Operator multiplicativity of the joint effects** (`IsProjective` on the nose).
`jointEffect (B₁ ∩ B₂) = jointEffect B₁ · jointEffect B₂`.  From the form identity
`crossMeasureForm_inter` by full sesquilinear extensionality (`ext_inner_left`) + the swap. -/
theorem jointEffect_inter (A B : Spectra.Operator.SelfAdjointOperator H) (hSC : StronglyCommute A B)
    {B₁ B₂ : Set (ℝ × ℝ)} (h₁ : MeasurableSet B₁) (h₂ : MeasurableSet B₂) :
    jointEffect A B hSC (h₁.inter h₂) = jointEffect A B hSC h₁ * jointEffect A B hSC h₂ := by
  refine ContinuousLinearMap.ext fun η => ext_inner_left ℂ fun ξ => ?_
  rw [jointEffect_inner, crossMeasureForm_inter A B hSC h₁ h₂ ξ η,
    ← jointEffect_inner A B hSC h₂ (jointEffect A B hSC h₁ ξ) η,
    jointEffect_swap A B hSC h₁ ξ (jointEffect A B hSC h₂ η), ContinuousLinearMap.mul_apply]

/-- **G2.4 — the joint POVM is projective.**  Immediate from `jointEffect_inter`. -/
theorem jointPOVM_isProjective (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) :
    (jointPOVM A B hSC).IsProjective :=
  fun _ _ h₁ h₂ => (jointEffect_inter A B hSC h₁ h₂).symm

/-- **Commutativity ⟺ a joint spectral measure.**

* **Forward** (`StronglyCommute ⟹ joint PVM`): the multivariate spectral theorem — the commuting
  PVMs generate a joint PVM on `ℝ²` with the right cylinder marginals.  This is the genuine new
  construction, **proved** here (`jointPOVM`, `jointPOVM_isProjective`, `jointPOVM_isJointOf`); it
  is the two-dimensional analogue of the in-house Herglotz/Stone build (or the product of the two
  commuting `spectralPVM`s).
* **Backward** (`joint PVM ⟹ StronglyCommute`): **proved**, `stronglyCommute_of_jointPVM`.

This replaces the naive `commute_iff_joint_law`: the witness is an operator-valued PVM
(`IsJointOf`), not a per-state coupling, which is why the equivalence has content. -/
theorem stronglyCommute_iff_jointPVM (A B : SelfAdjointOperator H) :
    StronglyCommute A B ↔ ∃ M : POVM H (ℝ × ℝ), M.IsProjective ∧ M.IsJointOf A B :=
  ⟨fun hSC => ⟨jointPOVM A B hSC, jointPOVM_isProjective A B hSC, jointPOVM_isJointOf A B hSC⟩,
    fun ⟨_M, hproj, hjoint⟩ => stronglyCommute_of_jointPVM hproj hjoint⟩

/-! ### G3 — Step B: the coordinate second moments and integrability of `xy`

The marginals of `μ_ξ = jointScalarMeasure A B hSC ξ` are `A`'s and `B`'s Born measures
(`jointBornMeasure_fst/_snd` via `jointPOVM_isJointOf`), so the coordinate second moments are the
1-D second moments `‖Aξ‖²`, `‖Bξ‖²` (`spectralPVM_integral_sq`).  Cauchy–Schwarz
(`MemLp.integrable_mul`, `2·2 → 1`) then gives `xy ∈ L¹(μ_ξ)`. -/

/-- **A-coordinate second moment.**  `∫ p.1² dμ_ξ = ‖Aξ‖²` (needs `ξ ∈ D(A)`): push the integral to
the first marginal `μ_ξ.fst = A.spectralPVM.diag ξ` (`jointBornMeasure_fst`, `integral_map`) and
apply the 1-D second moment `spectralPVM_integral_sq`. -/
theorem jointScalarMeasure_integral_fst_sq (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) {ξ : H} (hξA : ξ ∈ A.domain) :
    ∫ p : ℝ × ℝ, p.1 ^ 2 ∂(jointScalarMeasure A B hSC ξ) = ‖A.toLinearPMap ⟨ξ, hξA⟩‖ ^ 2 := by
  have hfst : (jointScalarMeasure A B hSC ξ).fst = A.spectralPVM.diag ξ :=
    jointBornMeasure_fst (jointPOVM_isJointOf A B hSC) ξ
  calc ∫ p : ℝ × ℝ, p.1 ^ 2 ∂(jointScalarMeasure A B hSC ξ)
      = ∫ s : ℝ, s ^ 2 ∂((jointScalarMeasure A B hSC ξ).fst) :=
        (integral_map measurable_fst.aemeasurable (continuous_pow 2).aestronglyMeasurable).symm
    _ = ∫ s : ℝ, s ^ 2 ∂(A.spectralPVM.diag ξ) := by rw [hfst]
    _ = ‖A.toLinearPMap ⟨ξ, hξA⟩‖ ^ 2 := SpectralTheory.spectralPVM_integral_sq A.selfAdjoint ξ hξA

/-- **B-coordinate second moment.**  `∫ p.2² dμ_ξ = ‖Bξ‖²` (needs `ξ ∈ D(B)`). -/
theorem jointScalarMeasure_integral_snd_sq (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) {ξ : H} (hξB : ξ ∈ B.domain) :
    ∫ p : ℝ × ℝ, p.2 ^ 2 ∂(jointScalarMeasure A B hSC ξ) = ‖B.toLinearPMap ⟨ξ, hξB⟩‖ ^ 2 := by
  have hsnd : (jointScalarMeasure A B hSC ξ).snd = B.spectralPVM.diag ξ :=
    jointBornMeasure_snd (jointPOVM_isJointOf A B hSC) ξ
  calc ∫ p : ℝ × ℝ, p.2 ^ 2 ∂(jointScalarMeasure A B hSC ξ)
      = ∫ t : ℝ, t ^ 2 ∂((jointScalarMeasure A B hSC ξ).snd) :=
        (integral_map measurable_snd.aemeasurable (continuous_pow 2).aestronglyMeasurable).symm
    _ = ∫ t : ℝ, t ^ 2 ∂(B.spectralPVM.diag ξ) := by rw [hsnd]
    _ = ‖B.toLinearPMap ⟨ξ, hξB⟩‖ ^ 2 := SpectralTheory.spectralPVM_integral_sq B.selfAdjoint ξ hξB

/-- **`p.1²` is integrable** for `ξ ∈ D(A)` (the first marginal is `A`'s Born measure, whose second
moment `‖Aξ‖²` is finite, `spectralPVM_integrable_sq`). -/
theorem jointScalarMeasure_integrable_fst_sq (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) {ξ : H} (hξA : ξ ∈ A.domain) :
    Integrable (fun p : ℝ × ℝ => p.1 ^ 2) (jointScalarMeasure A B hSC ξ) := by
  have hfst : (jointScalarMeasure A B hSC ξ).fst = A.spectralPVM.diag ξ :=
    jointBornMeasure_fst (jointPOVM_isJointOf A B hSC) ξ
  have h2 : Integrable (fun s : ℝ => s ^ 2) ((jointScalarMeasure A B hSC ξ).fst) := by
    rw [hfst]; exact SpectralTheory.spectralPVM_integrable_sq A.selfAdjoint ξ hξA
  exact (integrable_map_measure (continuous_pow 2).aestronglyMeasurable
    measurable_fst.aemeasurable).mp h2

/-- **`p.2²` is integrable** for `ξ ∈ D(B)`. -/
theorem jointScalarMeasure_integrable_snd_sq (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) {ξ : H} (hξB : ξ ∈ B.domain) :
    Integrable (fun p : ℝ × ℝ => p.2 ^ 2) (jointScalarMeasure A B hSC ξ) := by
  have hsnd : (jointScalarMeasure A B hSC ξ).snd = B.spectralPVM.diag ξ :=
    jointBornMeasure_snd (jointPOVM_isJointOf A B hSC) ξ
  have h2 : Integrable (fun t : ℝ => t ^ 2) ((jointScalarMeasure A B hSC ξ).snd) := by
    rw [hsnd]; exact SpectralTheory.spectralPVM_integrable_sq B.selfAdjoint ξ hξB
  exact (integrable_map_measure (continuous_pow 2).aestronglyMeasurable
    measurable_snd.aemeasurable).mp h2

/-- **The symbol `xy` is integrable** for `ξ ∈ D(A) ∩ D(B)`: both coordinates are in `L²(μ_ξ)`
(`memLp_two_iff_integrable_sq` + the second moments), so their product is in `L¹`
(`MemLp.integrable_mul`, Hölder `2·2 → 1`).  The L¹ membership that makes `∫ xy dμ_ξ` an honest
absolutely-convergent integral. -/
theorem jointScalarMeasure_integrable_mul (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) {ξ : H} (hξA : ξ ∈ A.domain) (hξB : ξ ∈ B.domain) :
    Integrable (fun p : ℝ × ℝ => p.1 * p.2) (jointScalarMeasure A B hSC ξ) := by
  have hf : MemLp (fun p : ℝ × ℝ => p.1) 2 (jointScalarMeasure A B hSC ξ) :=
    (memLp_two_iff_integrable_sq continuous_fst.aestronglyMeasurable).mpr
      (jointScalarMeasure_integrable_fst_sq A B hSC hξA)
  have hg : MemLp (fun p : ℝ × ℝ => p.2) 2 (jointScalarMeasure A B hSC ξ) :=
    (memLp_two_iff_integrable_sq continuous_snd.aestronglyMeasurable).mpr
      (jointScalarMeasure_integrable_snd_sq A B hSC hξB)
  simpa [Pi.mul_def] using hf.integrable_mul hg

/-! ### G3 — Step A/C infrastructure: the joint functional calculus engine

The correlation proof is the two-dimensional analogue of `weak_first_moment`: truncate the symbol
`xy` to the box `[-N,N]²`, identify the truncated integral with the operator product
`Φ_A(x·1_N)·Φ_B(y·1_N)` (the bounded functional calculi of the two commuting generators), and pass
to the limit `N → ∞`.  The novelty over the 1-D case is the operator product, which replaces the
unavailable Fubini (`μ_ξ` is **not** a product measure).  Its limit `Φ_A(f_N)Φ_B(g_N)ξ → A(Bξ)`
needs `E_B(T)` (a `B`-projection) to preserve `D(A)` and commute with `A` — the *external*
commutation supplied by `StronglyCommute` through the cross-group engines of `Joint.lean §0`. -/

section G3Correlation

open Spectra.QuantumMechanics.SpectralTheory Spectra.YosidaHille
  Spectra.OneParameterUnitaryGroup Spectra.Borel

/-- **Generic difference-quotient intertwining.**  A bounded operator `C` commuting with the group
`U` intertwines the generator's difference quotient: `genDiffQuot (C x) = C ∘ genDiffQuot x`. -/
private lemma genDiffQuot_commute {U_grp : OneParameterUnitaryGroup (H := H)} (C : H →L[ℂ] H)
    (hC : ∀ t, U_grp.U t * C = C * U_grp.U t) (x : H) :
    genDiffQuot U_grp (C x) = fun t => C (genDiffQuot U_grp x t) := by
  funext t
  have hcomm : C (U_grp.U t x) = U_grp.U t (C x) := by
    have h := DFunLike.congr_fun (hC t) x
    simpa only [ContinuousLinearMap.mul_apply] using h.symm
  simp only [genDiffQuot_apply, map_smul, map_sub, hcomm]

/-- **A bounded operator commuting with the group preserves the generator's domain.**  The generic
form of `spectralCalculus_mem_generatorDomain_of_mem`: the only property of `Φ(g)` it uses is
commutation with `U(t)`.  Applied with `C = E_B(T)` (and the external commutation from
`StronglyCommute`) it gives `E_B(T) D(A) ⊆ D(A)`. -/
private lemma mem_generatorDomain_of_commute {U_grp : OneParameterUnitaryGroup (H := H)}
    (C : H →L[ℂ] H) (hC : ∀ t, U_grp.U t * C = C * U_grp.U t) (x : (generator U_grp).domain) :
    (C (x : H)) ∈ (generator U_grp).domain :=
  mem_generatorDomain.mpr ⟨C (generator U_grp x), by
    rw [genDiffQuot_commute C hC]
    exact (C.continuous.tendsto _).comp (generator_tendsto U_grp x)⟩

/-- **A bounded operator commuting with the group commutes with the generator on its domain**:
`A (C x) = C (A x)`. -/
private lemma generator_commute {U_grp : OneParameterUnitaryGroup (H := H)} (C : H →L[ℂ] H)
    (hC : ∀ t, U_grp.U t * C = C * U_grp.U t) (x : (generator U_grp).domain) :
    generator U_grp ⟨C (x : H), mem_generatorDomain_of_commute C hC x⟩ = C (generator U_grp x) :=
  tendsto_nhds_unique
    (generator_tendsto U_grp ⟨_, mem_generatorDomain_of_commute C hC x⟩)
    (by rw [genDiffQuot_commute C hC]
        exact (C.continuous.tendsto _).comp (generator_tendsto U_grp x))

/-- **Cross-group commutation**: the unitary group of `A` commutes with the spectral projections of
`B`, for strongly-commuting `A, B`.  One application of the projection→calculus engine
`commute_spectralCalculus_of_commute_proj` (lifting the `A`-indicators to a character), then
`spectralCalculus_char`.  This is the hypothesis the domain-commutation engine above consumes. -/
private lemma commute_groupA_projB (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) (t : ℝ) {T : Set ℝ} (hT : MeasurableSet T) :
    (genToGroup A.selfAdjoint).U t * B.spectralPVM.proj T hT
      = B.spectralPVM.proj T hT * (genToGroup A.selfAdjoint).U t := by
  have h := commute_spectralCalculus_of_commute_proj (genToGroup A.selfAdjoint)
    (B.spectralPVM.proj T hT) (fun S hS => hSC S T hS hT) (char_measurable t) (char_bdd t)
  rw [spectralCalculus_char] at h
  exact h.eq

/-- **The `B`-section identity (Step A base case).**  Integrating a bounded `x`-symbol `f` against
the `y`-cylinder `T` recovers the operator pairing: `∫ f(x)·1_T(y) dμ_ξ = ⟪ξ, Φ_A(f) E_B(T) ξ⟫`.
Route: the `y`-cylinder section of `μ_ξ` pushed to the `x`-axis is `μ^A_{E_B(T)ξ}`
(`jointScalarMeasure_prod`), so the integral is `∫ f dμ^A_{E_B(T)ξ} = ⟪E_B(T)ξ, Φ_A(f) E_B(T)ξ⟫`
(`spectralForm_self`, `inner_spectralCalculus`), and the left `E_B(T)` drops by self-adjointness +
idempotence + the calculus/projection commutation. -/
private lemma joint_section_inner (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) {f : ℝ → ℂ} (hfm : Measurable f) (hfb : ∃ C, ∀ ω, ‖f ω‖ ≤ C)
    (ξ : H) {T : Set ℝ} (hT : MeasurableSet T) :
    ∫ p, f p.1 * Set.indicator T (fun _ => (1 : ℂ)) p.2 ∂(jointScalarMeasure A B hSC ξ)
      = ⟪ξ, spectralCalculus (genToGroup A.selfAdjoint) f hfm hfb
          (B.spectralPVM.proj T hT ξ)⟫_ℂ := by
  set UA := genToGroup A.selfAdjoint with _hUA
  set EB := B.spectralPVM.proj T hT with _hEB
  set Φf := spectralCalculus UA f hfm hfb with _hΦf
  -- rewrite the integrand as the indicator of the cylinder `univ ×ˢ T`
  have hpt : ∀ p : ℝ × ℝ, f p.1 * Set.indicator T (fun _ => (1 : ℂ)) p.2
      = Set.indicator (Set.univ ×ˢ T) (fun p => f p.1) p := by
    intro p
    by_cases h : p.2 ∈ T
    · rw [Set.indicator_of_mem h, mul_one, Set.indicator_of_mem (by simp [h])]
    · rw [Set.indicator_of_notMem h, mul_zero, Set.indicator_of_notMem (by simp [h])]
  -- the cylinder section pushed to the `x`-axis is `μ^A_{E_B(T)ξ}`
  have hmap : (jointScalarMeasure A B hSC ξ |>.restrict (Set.univ ×ˢ T)).map Prod.fst
      = A.spectralPVM.diag (EB ξ) := by
    ext S hS
    rw [Measure.map_apply measurable_fst hS, Measure.restrict_apply (measurable_fst hS)]
    have hset : Prod.fst ⁻¹' S ∩ (Set.univ ×ˢ T) = S ×ˢ T := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
    rw [hset, jointScalarMeasure_prod A B hSC ξ hS hT]
  -- the calculus commutes with `E_B(T)` (external projection commutation from `StronglyCommute`)
  have hcomm : Commute Φf EB :=
    commute_spectralCalculus_of_commute_proj UA EB (fun S hS => hSC S T hS hT) hfm hfb
  have hidem : EB * EB = EB := B.spectralPVM.proj_idem T hT
  have hadj : ContinuousLinearMap.adjoint EB = EB := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact B.spectralPVM.isSelfAdjoint_proj T hT
  have hdrop : EB (Φf (EB ξ)) = Φf (EB ξ) := by
    have hop : EB * Φf * EB = Φf * EB := by rw [← hcomm.eq, mul_assoc, hidem]
    have := congrArg (fun M : H →L[ℂ] H => M ξ) hop
    simpa only [ContinuousLinearMap.mul_apply] using this
  calc ∫ p, f p.1 * Set.indicator T (fun _ => (1 : ℂ)) p.2 ∂(jointScalarMeasure A B hSC ξ)
      = ∫ p, Set.indicator (Set.univ ×ˢ T) (fun p => f p.1) p ∂(jointScalarMeasure A B hSC ξ) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∫ p in Set.univ ×ˢ T, f p.1 ∂(jointScalarMeasure A B hSC ξ) :=
        integral_indicator (MeasurableSet.univ.prod hT)
    _ = ∫ x, f x ∂(A.spectralPVM.diag (EB ξ)) := by
        rw [← hmap, integral_map measurable_fst.aemeasurable hfm.aestronglyMeasurable]
    _ = ∫ l, f l ∂(borelMeasure UA (EB ξ)) := rfl
    _ = spectralForm UA (EB ξ) (EB ξ) f := (spectralForm_self UA (EB ξ) hfm hfb).symm
    _ = ⟪EB ξ, Φf (EB ξ)⟫_ℂ := (inner_spectralCalculus UA f hfm hfb (EB ξ) (EB ξ)).symm
    _ = ⟪ξ, EB (Φf (EB ξ))⟫_ℂ := by
        rw [← ContinuousLinearMap.adjoint_inner_left EB (Φf (EB ξ)) ξ, hadj]
    _ = ⟪ξ, Φf (EB ξ)⟫_ℂ := by rw [hdrop]

/-- A simple function `ℝ → ℂ` is bounded (finite range). -/
private lemma simpleFunc_bdd (s : MeasureTheory.SimpleFunc ℝ ℂ) :
    ∃ C, ∀ ω, ‖(s : ℝ → ℂ) ω‖ ≤ C := by
  have hbdd : BddAbove (Set.range (fun ω => ‖(s : ℝ → ℂ) ω‖)) := by
    have hr : Set.range (fun ω => ‖(s : ℝ → ℂ) ω‖)
        = (fun z : ℂ => ‖z‖) '' Set.range (s : ℝ → ℂ) := Set.range_comp _ _
    rw [hr]; exact (s.finite_range.image _).bddAbove
  obtain ⟨C, hC⟩ := hbdd
  exact ⟨C, fun ω => hC ⟨ω, rfl⟩⟩

/-- **Step A on simple `y`-symbols.**  For a simple function `s`, the product moment
`∫ f(x)·s(y) dμ_ξ` equals the `B`-spectral form `spectralForm_B (Φ_A(f)† ξ) ξ s`.  By
`SimpleFunc.induction`: the indicator base case is `joint_section_inner` (scaled), and additivity is
the bilinearity of both the integral and `spectralForm` (`spectralForm_add_fun`). -/
private lemma joint_product_form_simple (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) {f : ℝ → ℂ} (hfm : Measurable f) (hfb : ∃ C, ∀ ω, ‖f ω‖ ≤ C)
    (ξ : H) (s : MeasureTheory.SimpleFunc ℝ ℂ) :
    ∫ p, f p.1 * (s : ℝ → ℂ) p.2 ∂(jointScalarMeasure A B hSC ξ)
      = spectralForm (genToGroup B.selfAdjoint)
          (ContinuousLinearMap.adjoint (spectralCalculus (genToGroup A.selfAdjoint) f hfm hfb) ξ)
          ξ (s : ℝ → ℂ) := by
  set UA := genToGroup A.selfAdjoint with _hUA
  set UB := genToGroup B.selfAdjoint with _hUB
  set Φf := spectralCalculus UA f hfm hfb with hΦf
  set η := ContinuousLinearMap.adjoint Φf ξ with hη
  -- finite measure ⟹ `f(x)·h(y)` is integrable for any bounded measurable `h`
  have hintegrable : ∀ {h : ℝ → ℂ}, Measurable h → (∃ C, ∀ ω, ‖h ω‖ ≤ C) →
      Integrable (fun p : ℝ × ℝ => f p.1 * h p.2) (jointScalarMeasure A B hSC ξ) := by
    intro h hhm hhb
    obtain ⟨Cf, hCf⟩ := hfb
    obtain ⟨Ch, hCh⟩ := hhb
    refine Integrable.mono' (integrable_const (max Cf 0 * max Ch 0))
      ((hfm.comp measurable_fst).mul (hhm.comp measurable_snd)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [norm_mul]
    exact mul_le_mul ((hCf _).trans (le_max_left _ _)) ((hCh _).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)
  -- the indicator base identity (Step A on a single cylinder)
  have hbase : ∀ {S : Set ℝ} (hS : MeasurableSet S),
      spectralForm UB η ξ (Set.indicator S (fun _ => (1 : ℂ)))
        = ⟪ξ, Φf (B.spectralPVM.proj S hS ξ)⟫_ℂ := by
    intro S hS
    have h1 : spectralCalculus UB (Set.indicator S (fun _ => (1 : ℂ)))
        (measurable_const.indicator hS) (indicator_one_bdd S) = B.spectralPVM.proj S hS := rfl
    rw [← inner_spectralCalculus UB (Set.indicator S (fun _ => (1 : ℂ)))
      (measurable_const.indicator hS) (indicator_one_bdd S) η ξ, h1, hη,
      ContinuousLinearMap.adjoint_inner_left]
  -- the induction
  induction s using MeasureTheory.SimpleFunc.induction with
  | @const c S hS =>
    -- base: `s = c · 1_S`
    have hcoe : ((MeasureTheory.SimpleFunc.piecewise S hS (MeasureTheory.SimpleFunc.const ℝ c)
        (MeasureTheory.SimpleFunc.const ℝ 0)) : ℝ → ℂ) = Set.indicator S (fun _ => c) := by
      ext y; by_cases h : y ∈ S <;>
        simp [MeasureTheory.SimpleFunc.piecewise_apply, h, Set.indicator_of_mem,
          Set.indicator_of_notMem]
    rw [hcoe]
    have hci : ∀ y : ℝ, Set.indicator S (fun _ => c) y
        = c * Set.indicator S (fun _ => (1 : ℂ)) y := by
      intro y; by_cases h : y ∈ S <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    calc ∫ p, f p.1 * Set.indicator S (fun _ => c) p.2 ∂(jointScalarMeasure A B hSC ξ)
        = ∫ p, c * (f p.1 * Set.indicator S (fun _ => (1 : ℂ)) p.2)
            ∂(jointScalarMeasure A B hSC ξ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          by_cases h : p.2 ∈ S
          · simp only [Set.indicator_of_mem h]; ring
          · simp only [Set.indicator_of_notMem h]; ring
      _ = c * ∫ p, f p.1 * Set.indicator S (fun _ => (1 : ℂ)) p.2
            ∂(jointScalarMeasure A B hSC ξ) := integral_const_mul _ _
      _ = c * ⟪ξ, Φf (B.spectralPVM.proj S hS ξ)⟫_ℂ := by
          rw [joint_section_inner A B hSC hfm hfb ξ hS]
      _ = c * spectralForm UB η ξ (Set.indicator S (fun _ => (1 : ℂ))) := by rw [hbase hS]
      _ = spectralForm UB η ξ (Set.indicator S (fun _ => c)) := by
          rw [← spectralForm_smul_fun UB η ξ c (Set.indicator S (fun _ => (1 : ℂ)))]
          congr 1; ext y; rw [hci y]
  | @add s₁ s₂ _hdisj h₁ h₂ =>
    -- additive step
    obtain ⟨C₁, hC₁⟩ := simpleFunc_bdd s₁
    obtain ⟨C₂, hC₂⟩ := simpleFunc_bdd s₂
    have hcoe : ((s₁ + s₂ : MeasureTheory.SimpleFunc ℝ ℂ) : ℝ → ℂ)
        = fun y => (s₁ : ℝ → ℂ) y + (s₂ : ℝ → ℂ) y := by
      ext y; simp [MeasureTheory.SimpleFunc.coe_add]
    rw [hcoe]
    calc ∫ p, f p.1 * ((s₁ : ℝ → ℂ) p.2 + (s₂ : ℝ → ℂ) p.2) ∂(jointScalarMeasure A B hSC ξ)
        = ∫ p, (f p.1 * (s₁ : ℝ → ℂ) p.2 + f p.1 * (s₂ : ℝ → ℂ) p.2)
            ∂(jointScalarMeasure A B hSC ξ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_); ring
      _ = (∫ p, f p.1 * (s₁ : ℝ → ℂ) p.2 ∂(jointScalarMeasure A B hSC ξ))
            + ∫ p, f p.1 * (s₂ : ℝ → ℂ) p.2 ∂(jointScalarMeasure A B hSC ξ) :=
          integral_add (hintegrable s₁.measurable ⟨C₁, hC₁⟩) (hintegrable s₂.measurable ⟨C₂, hC₂⟩)
      _ = spectralForm UB η ξ (s₁ : ℝ → ℂ) + spectralForm UB η ξ (s₂ : ℝ → ℂ) := by rw [h₁, h₂]
      _ = spectralForm UB η ξ (fun y => (s₁ : ℝ → ℂ) y + (s₂ : ℝ → ℂ) y) :=
          (spectralForm_add_fun UB η ξ s₁.measurable ⟨C₁, hC₁⟩ s₂.measurable ⟨C₂, hC₂⟩).symm

/-- **Step A — the bounded product-moment identity.**  For bounded measurable `f, g`, the joint
integral of the product symbol equals the operator-product matrix element:
`∫ f(x)·g(y) dμ_ξ = ⟪ξ, Φ_A(f) Φ_B(g) ξ⟫`.  Extends `joint_product_form_simple` from simple to
bounded `g` by approximating with `SimpleFunc.approxOn` and dominated convergence on both sides (the
left integral over the finite `μ_ξ`; the right `spectralForm`, a fixed combination of integrals over
the finite measures `μ^B_w`).  The operator product `Φ_A(f)Φ_B(g)` is what replaces the unavailable
Fubini. -/
private lemma joint_product_form (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) {f g : ℝ → ℂ} (hfm : Measurable f) (hfb : ∃ C, ∀ ω, ‖f ω‖ ≤ C)
    (hgm : Measurable g) (hgb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (ξ : H) :
    ∫ p, f p.1 * g p.2 ∂(jointScalarMeasure A B hSC ξ)
      = ⟪ξ, spectralCalculus (genToGroup A.selfAdjoint) f hfm hfb
          (spectralCalculus (genToGroup B.selfAdjoint) g hgm hgb ξ)⟫_ℂ := by
  set UA := genToGroup A.selfAdjoint with _hUA
  set UB := genToGroup B.selfAdjoint with _hUB
  set Φf := spectralCalculus UA f hfm hfb with hΦf
  set η := ContinuousLinearMap.adjoint Φf ξ with hη
  -- it suffices to prove the `spectralForm` version, then convert through the adjoint
  suffices hform : ∫ p, f p.1 * g p.2 ∂(jointScalarMeasure A B hSC ξ) = spectralForm UB η ξ g by
    rw [hform, ← inner_spectralCalculus UB g hgm hgb η ξ]
    exact ContinuousLinearMap.adjoint_inner_left Φf (spectralCalculus UB g hgm hgb ξ) ξ
  obtain ⟨Cg, hCg⟩ := hgb
  -- the approximating simple functions
  set gN : ℕ → MeasureTheory.SimpleFunc ℝ ℂ :=
    fun n => MeasureTheory.SimpleFunc.approxOn g hgm Set.univ 0 (Set.mem_univ 0) n with _hgN
  have hgN_tendsto : ∀ y, Filter.Tendsto (fun n => (gN n : ℝ → ℂ) y) atTop (𝓝 (g y)) := fun y =>
    MeasureTheory.SimpleFunc.tendsto_approxOn hgm (Set.mem_univ 0) (by simp)
  have hgN_bound : ∀ n y, ‖(gN n : ℝ → ℂ) y‖ ≤ 2 * Cg := by
    intro n y
    have h := MeasureTheory.SimpleFunc.norm_approxOn_y₀_le hgm (Set.mem_univ (0 : ℂ)) y n
    simp only [sub_zero] at h
    calc ‖(gN n : ℝ → ℂ) y‖ ≤ ‖g y‖ + ‖g y‖ := h
      _ ≤ Cg + Cg := add_le_add (hCg y) (hCg y)
      _ = 2 * Cg := by ring
  -- LHS: dominated convergence over the finite measure `μ_ξ`
  have hLHS : Filter.Tendsto
      (fun n => ∫ p, f p.1 * (gN n : ℝ → ℂ) p.2 ∂(jointScalarMeasure A B hSC ξ)) atTop
      (𝓝 (∫ p, f p.1 * g p.2 ∂(jointScalarMeasure A B hSC ξ))) := by
    obtain ⟨Cf, hCf⟩ := hfb
    refine tendsto_integral_of_dominated_convergence (fun _ => max Cf 0 * (2 * Cg))
      (fun n => ((hfm.comp measurable_fst).mul
        ((gN n).measurable.comp measurable_snd)).aestronglyMeasurable)
      (integrable_const _) (fun n => Filter.Eventually.of_forall fun p => ?_)
      (Filter.Eventually.of_forall fun p => ?_)
    · rw [norm_mul]
      exact mul_le_mul ((hCf _).trans (le_max_left _ _)) (hgN_bound n p.2)
        (norm_nonneg _) (le_max_right _ _)
    · exact tendsto_const_nhds.mul (hgN_tendsto p.2)
  -- RHS: each of the four `spectralForm` integrals converges by dominated convergence
  have hconv : ∀ w : H, Filter.Tendsto (fun n => ∫ l, (gN n : ℝ → ℂ) l ∂(borelMeasure UB w)) atTop
      (𝓝 (∫ l, g l ∂(borelMeasure UB w))) := by
    intro w
    haveI : MeasureTheory.IsFiniteMeasure (borelMeasure UB w) := borelMeasure_isFiniteMeasure UB w
    exact tendsto_integral_of_dominated_convergence (fun _ => 2 * Cg)
      (fun n => (gN n).measurable.aestronglyMeasurable) (integrable_const _)
      (fun n => Filter.Eventually.of_forall fun l => hgN_bound n l)
      (Filter.Eventually.of_forall hgN_tendsto)
  have hRHS : Filter.Tendsto (fun n => spectralForm UB η ξ (gN n : ℝ → ℂ)) atTop
      (𝓝 (spectralForm UB η ξ g)) := by
    simp only [spectralForm]
    exact (((hconv (η + ξ)).sub (hconv (η - ξ))).add
      (((hconv (η - I • ξ)).sub (hconv (η + I • ξ))).mul_const I)).div_const 4
  -- the per-`n` simple-function identity, then identify the limits
  have heq : Filter.Tendsto
      (fun n => ∫ p, f p.1 * (gN n : ℝ → ℂ) p.2 ∂(jointScalarMeasure A B hSC ξ)) atTop
      (𝓝 (spectralForm UB η ξ g)) := by
    refine hRHS.congr fun n => ?_
    exact (joint_product_form_simple A B hSC hfm hfb ξ (gN n)).symm
  exact tendsto_nhds_unique hLHS heq

/-- **Step C — the truncated vector identity.**  The operator product applied to `ξ` collapses to
nested truncated projections of `A(Bξ)`:
`Φ_A(x·1_N) Φ_B(y·1_N) ξ = E_A([-N,N]) E_B([-N,N]) (A(Bξ))`.  Inside out:
`Φ_B(y·1_N)ξ = E_B([-N,N])(Bξ)` (`generator_spectralProjection`), then `E_B([-N,N])` preserves
`D(A)` and commutes with `A` (`generator_commute` + `commute_groupA_projB`), so `Φ_A(x·1_N)` acting
on it is `E_A([-N,N])` applied to `E_B([-N,N])(A(Bξ))`. -/
private lemma joint_truncated_vector (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) {ξ : H} (hξ : ξ ∈ B.domain)
    (hξ' : B.toLinearPMap ⟨ξ, hξ⟩ ∈ A.domain) (N : ℕ) :
    spectralCalculus (genToGroup A.selfAdjoint)
        (fun l => (l : ℂ) * Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ)) (fun _ => (1 : ℂ)) l)
        (id_indicator_measurable measurableSet_Icc)
        (id_indicator_bdd (fun _x hx => abs_le_max_of_mem_Icc hx))
        (spectralCalculus (genToGroup B.selfAdjoint)
          (fun l => (l : ℂ) * Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ)) (fun _ => (1 : ℂ)) l)
          (id_indicator_measurable measurableSet_Icc)
          (id_indicator_bdd (fun _x hx => abs_le_max_of_mem_Icc hx)) ξ)
      = A.spectralPVM.proj (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc
          (B.spectralPVM.proj (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc
            (A.toLinearPMap ⟨B.toLinearPMap ⟨ξ, hξ⟩, hξ'⟩)) := by
  set UA := genToGroup A.selfAdjoint with _hUA
  set UB := genToGroup B.selfAdjoint with _hUB
  set IccN := Set.Icc (-(N : ℝ)) (N : ℝ) with _hIccN
  have habs : ∀ x ∈ IccN, |x| ≤ max |(-(N : ℝ))| |(N : ℝ)| := fun x hx => abs_le_max_of_mem_Icc hx
  set ψ := B.toLinearPMap ⟨ξ, hξ⟩ with _hψ
  set EB := B.spectralPVM.proj IccN measurableSet_Icc with _hEB
  -- inner truncation: `Φ_B(y·1_N) ξ = E_B(N) (Bξ)`
  have hξB' : ξ ∈ (generator UB).domain := by rw [generator_genToGroup]; exact hξ
  have hBval : generator UB ⟨ξ, hξB'⟩ = ψ := (le_of_eq (generator_genToGroup B.selfAdjoint)).2 rfl
  have h1 : spectralCalculus UB
        (fun l => (l : ℂ) * Set.indicator IccN (fun _ => (1 : ℂ)) l)
        (id_indicator_measurable measurableSet_Icc) (id_indicator_bdd habs) ξ = EB ψ := by
    have h := generator_spectralProjection_comm (B := IccN) UB measurableSet_Icc ⟨ξ, hξB'⟩
    rw [hBval] at h
    rw [← generator_spectralProjection UB measurableSet_Icc habs ξ]
    exact h
  -- `E_B(N)` preserves `D(A)` and commutes with `A`
  have hψA : ψ ∈ (generator UA).domain := by rw [generator_genToGroup]; exact hξ'
  have hAval : generator UA ⟨ψ, hψA⟩ = A.toLinearPMap ⟨ψ, hξ'⟩ :=
    (le_of_eq (generator_genToGroup A.selfAdjoint)).2 rfl
  have hC : ∀ t, UA.U t * EB = EB * UA.U t := fun t =>
    commute_groupA_projB A B hSC t measurableSet_Icc
  have hχA : EB ψ ∈ (generator UA).domain := mem_generatorDomain_of_commute EB hC ⟨ψ, hψA⟩
  have hgenχ : generator UA ⟨EB ψ, hχA⟩ = EB (A.toLinearPMap ⟨ψ, hξ'⟩) := by
    rw [generator_commute EB hC ⟨ψ, hψA⟩, hAval]
  -- outer truncation: `Φ_A(x·1_N) (E_B(N)ψ) = E_A(N) (generator_A (E_B(N)ψ)) = E_A(N) E_B(N) (Aψ)`
  rw [h1]
  have h2 := generator_spectralProjection_comm (B := IccN) UA measurableSet_Icc ⟨EB ψ, hχA⟩
  rw [hgenχ] at h2
  rw [← generator_spectralProjection UA measurableSet_Icc habs (EB ψ)]
  exact h2

/-- **The truncation converges to the identity in two coordinates.**  For any vector `v`,
`E_A([-N,N]) E_B([-N,N]) v → v`: `E_B([-N,N])v → v` and `E_A([-N,N])v → v`
(`tendsto_spectralProjection_Icc_univ`), and `E_A` is a contraction, so the composite differs from
`v` by at most `‖E_B([-N,N])v − v‖ + ‖E_A([-N,N])v − v‖ → 0`. -/
private lemma joint_truncated_tendsto (A B : Spectra.Operator.SelfAdjointOperator H) (v : H) :
    Filter.Tendsto (fun N : ℕ =>
        A.spectralPVM.proj (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc
          (B.spectralPVM.proj (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc v)) atTop (𝓝 v) := by
  have hA : Filter.Tendsto (fun N : ℕ =>
      A.spectralPVM.proj (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc v) atTop (𝓝 v) :=
    tendsto_spectralProjection_Icc_univ (genToGroup A.selfAdjoint) v
  have hB : Filter.Tendsto (fun N : ℕ =>
      B.spectralPVM.proj (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc v) atTop (𝓝 v) :=
    tendsto_spectralProjection_Icc_univ (genToGroup B.selfAdjoint) v
  rw [tendsto_iff_norm_sub_tendsto_zero] at hA hB ⊢
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) (by simpa using hB.add hA)
  set EA := A.spectralPVM.proj (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc with _hEA
  set EB := B.spectralPVM.proj (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc with _hEB
  calc ‖EA (EB v) - v‖ = ‖(EA (EB v) - EA v) + (EA v - v)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖EA (EB v) - EA v‖ + ‖EA v - v‖ := norm_add_le _ _
    _ = ‖EA (EB v - v)‖ + ‖EA v - v‖ := by rw [← map_sub]
    _ ≤ ‖EB v - v‖ + ‖EA v - v‖ := by
        gcongr
        exact A.spectralPVM.norm_proj_apply_le _ measurableSet_Icc _

/-- **The correlation.**  The content a generic coupling lacks: the genuine joint law reproduces
`⟪ξ, AB ξ⟫` (the cross-moment), the bridge to Bell/CHSH.

Stated for the **canonical projective joint PVM** `M = jointPOVM A B hSC` (so
`jointBornMeasure = jointScalarMeasure = μ_ξ`).  This specialization is essential, **not** cosmetic:
for a *generic* `M` with only `M.IsJointOf A B`, the cross-moment `∫ xy dμ_ξ` is
**under-determined** — `IsJointOf` fixes only the cylinder marginals (`jointBornMeasure_fst/_snd`),
leaving the rectangle coupling free (`POVM.ext_of_diag`), so the identity would be false.
Projectivity forces the rectangle values `μ_ξ(S×T) = ⟪ξ, E_A(S)E_B(T)ξ⟫`, which is what carries the
correlation.

The domain hypotheses are `ξ ∈ D(A) ∩ D(B)` and `Bξ ∈ D(A)`: `ξ ∈ D(B)` and `Bξ ∈ D(A)` make the RHS
`⟪ξ, A(Bξ)⟫` meaningful, and `ξ ∈ D(A)` is needed for integrability of the symbol `xy` on the LHS
(`∫ x² dμ_ξ = ‖Aξ‖² < ∞` via the first marginal, then Cauchy–Schwarz with `∫ y² = ‖Bξ‖²`).

Proof: the 2-D analogue of `weak_first_moment` — truncate `xy` to the box `[-N,N]²`, identify the
truncated integral via the commuting bounded calculi `Φ_A(x·1_N)Φ_B(y·1_N)`, then dominated
convergence (left) and the domain-commutation engine `generator_spectralProjection_comm` (right) as
`N → ∞`.  See the Vault plan `Plan - G3 Correlation.md`. -/
theorem jointBornMeasure_correlation {A B : Spectra.Operator.SelfAdjointOperator H}
    (hSC : StronglyCommute A B) {ξ : H} (hξA : ξ ∈ A.domain) (hξ : ξ ∈ B.domain)
    (hξ' : (B.toLinearPMap ⟨ξ, hξ⟩) ∈ A.domain) :
    ∫ p, p.1 * p.2 ∂(jointBornMeasure (jointPOVM A B hSC) ξ)
      = (⟪ξ, A.toLinearPMap ⟨B.toLinearPMap ⟨ξ, hξ⟩, hξ'⟩⟫_ℂ).re := by
  change ∫ p, p.1 * p.2 ∂(jointScalarMeasure A B hSC ξ)
    = (⟪ξ, A.toLinearPMap ⟨B.toLinearPMap ⟨ξ, hξ⟩, hξ'⟩⟫_ℂ).re
  -- the truncated box integral `∫_{[-N,N]²} xy dμ_ξ` equals the truncated operator matrix element
  have key : ∀ N : ℕ,
      (∫ p, Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ) ×ˢ Set.Icc (-(N : ℝ)) (N : ℝ))
          (fun q : ℝ × ℝ => q.1 * q.2) p ∂(jointScalarMeasure A B hSC ξ))
        = (⟪ξ, A.spectralPVM.proj (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc
            (B.spectralPVM.proj (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc
              (A.toLinearPMap ⟨B.toLinearPMap ⟨ξ, hξ⟩, hξ'⟩))⟫_ℂ).re := by
    intro N
    -- Step A: the box integral (complex symbols) is the operator product;
    -- Step C: the operator product collapses to nested truncations of `A(Bξ)`
    have hjpf := joint_product_form A B hSC
      (f := fun l => (l : ℂ) * Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ)) (fun _ => (1 : ℂ)) l)
      (g := fun l => (l : ℂ) * Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ)) (fun _ => (1 : ℂ)) l)
      (id_indicator_measurable measurableSet_Icc)
      (id_indicator_bdd (fun x hx => abs_le_max_of_mem_Icc hx))
      (id_indicator_measurable measurableSet_Icc)
      (id_indicator_bdd (fun x hx => abs_le_max_of_mem_Icc hx)) ξ
    rw [joint_truncated_vector A B hSC hξ hξ' N] at hjpf
    -- the complex box integral is the `ofReal` of the real box integral
    have hcoe : (∫ p : ℝ × ℝ, (p.1 : ℂ) * Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ))
              (fun _ => (1 : ℂ)) p.1
            * ((p.2 : ℂ) * Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ))
              (fun _ => (1 : ℂ)) p.2) ∂(jointScalarMeasure A B hSC ξ))
        = ((∫ p, Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ) ×ˢ Set.Icc (-(N : ℝ)) (N : ℝ))
            (fun q : ℝ × ℝ => q.1 * q.2) p ∂(jointScalarMeasure A B hSC ξ) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      by_cases h1 : p.1 ∈ Set.Icc (-(N : ℝ)) (N : ℝ)
      · by_cases h2 : p.2 ∈ Set.Icc (-(N : ℝ)) (N : ℝ)
        · simp only [Set.indicator_of_mem h1, Set.indicator_of_mem h2,
            Set.indicator_of_mem (Set.mem_prod.mpr ⟨h1, h2⟩), mul_one, Complex.ofReal_mul]
        · simp only [Set.indicator_of_notMem h2,
            Set.indicator_of_notMem
              (show p ∉ Set.Icc (-(N : ℝ)) (N : ℝ) ×ˢ Set.Icc (-(N : ℝ)) (N : ℝ)
                from fun hh => h2 hh.2), mul_zero, Complex.ofReal_zero]
      · simp only [Set.indicator_of_notMem h1,
          Set.indicator_of_notMem (show p ∉ Set.Icc (-(N : ℝ)) (N : ℝ) ×ˢ Set.Icc (-(N : ℝ)) (N : ℝ)
            from fun hh => h1 hh.1), zero_mul, mul_zero, Complex.ofReal_zero]
    rw [← (hcoe.symm.trans hjpf), Complex.ofReal_re]
  -- LHS: dominated convergence (the box exhausts `ℝ²`; dominant `|xy| ∈ L¹` from Step B)
  have hDCT : Filter.Tendsto (fun N : ℕ => ∫ p, Set.indicator
        (Set.Icc (-(N : ℝ)) (N : ℝ) ×ˢ Set.Icc (-(N : ℝ)) (N : ℝ)) (fun q : ℝ × ℝ => q.1 * q.2) p
        ∂(jointScalarMeasure A B hSC ξ)) atTop
      (𝓝 (∫ p, p.1 * p.2 ∂(jointScalarMeasure A B hSC ξ))) := by
    refine tendsto_integral_of_dominated_convergence (fun p => ‖p.1 * p.2‖)
      (fun N => ((measurable_fst.mul measurable_snd).indicator
        (measurableSet_Icc.prod measurableSet_Icc)).aestronglyMeasurable)
      (jointScalarMeasure_integrable_mul A B hSC hξA hξ).norm
      (fun N => Filter.Eventually.of_forall fun p => norm_indicator_le_norm_self _ _)
      (Filter.Eventually.of_forall fun p => ?_)
    apply tendsto_const_nhds.congr'
    obtain ⟨N₀, hN₀⟩ := exists_nat_ge (max |p.1| |p.2|)
    filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
    have hNN : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hp : p ∈ Set.Icc (-(N : ℝ)) (N : ℝ) ×ˢ Set.Icc (-(N : ℝ)) (N : ℝ) := by
      have hb1 : |p.1| ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _) hN₀) hNN
      have hb2 : |p.2| ≤ (N : ℝ) := le_trans (le_trans (le_max_right _ _) hN₀) hNN
      exact ⟨⟨by have := neg_abs_le p.1; linarith, by have := le_abs_self p.1; linarith⟩,
        ⟨by have := neg_abs_le p.2; linarith, by have := le_abs_self p.2; linarith⟩⟩
    exact (Set.indicator_of_mem hp (fun q : ℝ × ℝ => q.1 * q.2)).symm
  -- RHS: the truncations converge to `A(Bξ)` and the inner product is continuous
  have hlim : Filter.Tendsto (fun N : ℕ => (⟪ξ,
        A.spectralPVM.proj (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc
          (B.spectralPVM.proj (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc
            (A.toLinearPMap ⟨B.toLinearPMap ⟨ξ, hξ⟩, hξ'⟩))⟫_ℂ).re) atTop
      (𝓝 ((⟪ξ, A.toLinearPMap ⟨B.toLinearPMap ⟨ξ, hξ⟩, hξ'⟩⟫_ℂ).re)) := by
    have hcont : Continuous (fun y : H => (⟪ξ, y⟫_ℂ).re) :=
      Complex.continuous_re.comp (continuous_const.inner continuous_id)
    exact (hcont.tendsto _).comp
      (joint_truncated_tendsto A B (A.toLinearPMap ⟨B.toLinearPMap ⟨ξ, hξ⟩, hξ'⟩))
  exact tendsto_nhds_unique hDCT (hlim.congr fun N => (key N).symm)

end G3Correlation

end Spectra.QuantumMechanics.BornRule
