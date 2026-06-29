/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.BornRule.POVM
import Spectra.QuantumMechanics.Observable.Basic
import Mathlib.MeasureTheory.Measure.Prod
/-!
# The relational layer: joint spectral measures and the Born rule for commuting observables

This file formalizes when two observables admit a *joint* outcome law, and connects that to
commutativity and (forward) to `BellsTheorem`.

## Two corrections to the naive statement

The naive target `Commute A B ↔ ∃ μ : H → Measure (ℝ × ℝ), (marginals are the bornMeasures)` is
**false as content**, for two reasons that must be fixed before anything is provable.

**(1) A per-state coupling is vacuous.**  For *any* `A`, `B` — commuting or not — and any `ξ`, the
product measure `(bornMeasure A ξ).prod (bornMeasure B ξ)` has marginals `bornMeasure A ξ` and
`bornMeasure B ξ`.  So "∃ joint law with these marginals" is always true and characterizes nothing;
marginals never witness non-commutativity.  Commutativity is characterized by a **joint PVM** — an
*operator*-valued measure on `ℝ²`, simultaneously for all states — whose coordinate projections
recover `E_A` and `E_B`.  The per-state joint law is then a *corollary* (forward direction only),
and the content it adds over a generic coupling is the **correlation** `∫ xy dμ_ξ = ⟪ξ, AB ξ⟫`.

**(2) `Commute` is the wrong notion for unbounded operators.**  Algebraic commutation `A·B = B·A`
on a common domain does **not** imply the spectral projections commute (Nelson's counterexample: a
common dense invariant core on which `AB = BA`, yet no joint PVM exists).  The correct hypothesis is
*strong* commutativity — equivalently the spectral projections, the resolvents, or the unitary
groups commute.  This file uses spectral-projection commutation (`StronglyCommute`).

## Main statements

* `StronglyCommute` — the correct commutativity notion (projections of `spectralPVM` commute).
* `POVM.IsProjective` — a POVM is a PVM (multiplicative); the joint PVM is a projective
  `POVM H (ℝ × ℝ)`.
* `stronglyCommute_iff_jointPVM` — **the corrected iff.**  Forward is the multivariate spectral
  theorem; backward is multiplicativity of the joint PVM.
* `jointBornMeasure`, `jointBornMeasure_fst/_snd`, `jointBornMeasure_correlation` — the joint Born
  law for a commuting pair, with the Born measures as marginals and `⟪ξ, AB ξ⟫` as the correlation.

## The Bell connection (forward, to `BellsTheorem`)

A single commuting pair *always* has a joint law, so commuting observables are jointly classical and
satisfy every Bell-type inequality (→ `CHSH_Bounds.Commuting`).  The Bell *obstruction* is not about
one pair: it is the nonexistence of a **single global law over a family of incompatible settings**
`A₁,A₂,B₁,B₂` reproducing all measured correlations `⟪ξ, AᵢBⱼ ξ⟫`.  That global law is exactly the
local-hidden-variable model of `BellsTheorem.LHV`; CHSH (`≤ 2`) and Tsirelson (`≤ 2√2`) quantify the
gap.  Non-commutativity of the *same-side* observables (`A₁,A₂`) is what blocks the global law — not
anything about a single cross-pair `(Aᵢ, Bⱼ)`, each of which (being commuting/spacelike) does have a
joint law.

## Dependencies

`[needs spectralPVM]` throughout (every `E_A` is `A.spectralPVM`).  The forward construction of the
joint PVM additionally needs `[needs infra: 2-parameter Bochner / commuting functional calculus]` —
the two-dimensional analogue of your Herglotz/Stone spectral-measure construction.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*], §VIII.5 (strong commutativity; the
  Nelson counterexample is §VIII, Example 1 in some editions).
* [Conway, *A Course in Operator Theory*], spectral theorem for commuting normal operators.
* [Tsirelson, *Quantum generalizations of Bell's inequality*] (1980).
-/

open MeasureTheory Complex Spectra
open scoped InnerProductSpace
open Spectra.QuantumMechanics.Observable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.QuantumMechanics.BornRule

open PVM

/-! ## §1  Strong commutativity (the correct hypothesis) -/

/-- **Strong commutativity** of two observables: their spectral projections commute for all Borel
sets.  This is the notion that admits a joint PVM.

It is *strictly stronger* than `Commute A.toLinearPMap B.toLinearPMap` (algebraic commutation on a
common domain), which by Nelson's counterexample does **not** imply a joint spectral measure.  It is
equivalent to: the resolvents commute; the unitary groups `e^{isA}`, `e^{itB}` commute (the form your
Stone machinery exposes directly). -/
def StronglyCommute (A B : UnboundedObservable H) : Prop :=
  ∀ (S T : Set ℝ) (hS : MeasurableSet S) (hT : MeasurableSet T),
    Commute (A.spectralPVM.proj S hS) (B.spectralPVM.proj T hT)

/-- `[needs spectralPVM + Stone]` Equivalence with commutation of the unitary groups — the form most
convenient to *verify* in practice (and the one your `OneParameterUnitaryGroup` stack supplies).
Stated as a flag; the proof is the strong-commutativity equivalence theorem. -/
theorem stronglyCommute_iff_groups_commute (A B : UnboundedObservable H) :
    StronglyCommute A B ↔
      ∀ s t : ℝ, Commute ((YosidaHille.genToGroup A.selfAdjoint).U s)
        ((YosidaHille.genToGroup B.selfAdjoint).U t) :=
  sorry

/-! ## §2  The joint PVM as a projective POVM on `ℝ × ℝ`

A joint spectral measure is a PVM on `ℝ²`.  Rather than re-bundle, reuse the `POVM H (ℝ × ℝ)` you
already have and add the projectivity predicate that distinguishes a PVM from a general POVM — i.e.
the `proj_inter` axiom that the POVM structure dropped. -/

/-- A POVM is **projective** — a genuine PVM — when its effects are multiplicative:
`M(B₁) · M(B₂) = M(B₁ ∩ B₂)`.  (Equivalently, every effect is a projection, by `proj_idem`.)
This is exactly the `ProjValMeasure.proj_inter` axiom, reintroduced as a predicate. -/
def _root_.Spectra.POVM.IsProjective {ι : Type*} [MeasurableSpace ι] (M : POVM H ι) : Prop :=
  ∀ (B₁ B₂ : Set ι) (h₁ : MeasurableSet B₁) (h₂ : MeasurableSet B₂),
    M.effect B₁ h₁ * M.effect B₂ h₂ = M.effect (B₁ ∩ B₂) (h₁.inter h₂)

/-- The first coordinate marginal of a joint measure, as a Born-style state-indexed measure
(`MeasureTheory.Measure.fst`). -/
noncomputable def _root_.Spectra.POVM.marginalFst (M : POVM H (ℝ × ℝ)) (ξ : H) : Measure ℝ :=
  (M.diag ξ).fst

/-- The second coordinate marginal. -/
noncomputable def _root_.Spectra.POVM.marginalSnd (M : POVM H (ℝ × ℝ)) (ξ : H) : Measure ℝ :=
  (M.diag ξ).snd

/-- **The marginal PVM property** at the operator level: the effect on the cylinder `S × ℝ` is the
spectral projection `E_A(S)`.  This is the hypothesis with teeth — it forces the marginal *operators*
(not merely the marginal measures) to be `A`'s, which is what couples to commutativity. -/
def _root_.Spectra.POVM.IsJointOf (M : POVM H (ℝ × ℝ)) (A B : UnboundedObservable H) : Prop :=
  (∀ (S : Set ℝ) (hS : MeasurableSet S),
      M.effect (S ×ˢ Set.univ) (hS.prod MeasurableSet.univ) = A.spectralPVM.proj S hS)
    ∧ (∀ (T : Set ℝ) (hT : MeasurableSet T),
      M.effect (Set.univ ×ˢ T) (MeasurableSet.univ.prod hT) = B.spectralPVM.proj T hT)

/-! ## §3  The corrected iff -/

/-- `[done]` The easy half, isolated: a joint projective PVM forces strong commutativity.  For any
`S, T`, `E_A(S)·E_B(T) = M(S×ℝ)·M(ℝ×T) = M((S×ℝ)∩(ℝ×T)) = M((ℝ×T)∩(S×ℝ)) = M(ℝ×T)·M(S×ℝ) =
E_B(T)·E_A(S)`.  Pure algebra from `IsProjective` + `IsJointOf` + `Set.inter_comm`. -/
theorem stronglyCommute_of_jointPVM {A B : UnboundedObservable H} {M : POVM H (ℝ × ℝ)}
    (hproj : M.IsProjective) (hjoint : M.IsJointOf A B) :
    StronglyCommute A B := by
  intro S T hS hT
  rw [← hjoint.1 S hS, ← hjoint.2 T hT]
  show M.effect (S ×ˢ Set.univ) (hS.prod MeasurableSet.univ)
      * M.effect (Set.univ ×ˢ T) (MeasurableSet.univ.prod hT)
    = M.effect (Set.univ ×ˢ T) (MeasurableSet.univ.prod hT)
      * M.effect (S ×ˢ Set.univ) (hS.prod MeasurableSet.univ)
  rw [hproj _ _ _ _, hproj _ _ _ _]
  exact M.effect_congr (Set.inter_comm _ _) _ _

/-- `[needs spectralPVM + 2D Bochner]` **Commutativity ⟺ a joint spectral measure.**

* **Forward** (`StronglyCommute ⟹ joint PVM`): the multivariate spectral theorem — the commuting
  PVMs generate a joint PVM on `ℝ²` with the right cylinder marginals.  This is the genuine new
  construction (still a `sorry`); it is the two-dimensional analogue of your Herglotz/Stone build
  (2-parameter Bochner for the commuting unitary groups `e^{isA} e^{itB}`).
* **Backward** (`joint PVM ⟹ StronglyCommute`): **proved**, `stronglyCommute_of_jointPVM`.

This replaces the naive `commute_iff_joint_law`: the witness is an operator-valued PVM (`IsJointOf`),
not a per-state coupling, which is why the equivalence has content. -/
theorem stronglyCommute_iff_jointPVM (A B : UnboundedObservable H) :
    StronglyCommute A B ↔ ∃ M : POVM H (ℝ × ℝ), M.IsProjective ∧ M.IsJointOf A B :=
  ⟨sorry, fun ⟨_M, hproj, hjoint⟩ => stronglyCommute_of_jointPVM hproj hjoint⟩

/-! ## §4  The joint Born law (forward corollary)

Given a joint PVM for a commuting pair, the per-state joint distribution is its diagonal measure.
Unlike a generic coupling it (a) has the Born measures as *marginals via the operator marginals*, and
(b) reproduces the correlation `⟪ξ, AB ξ⟫`. -/

/-- The **joint Born measure** of a state `ξ` under a joint PVM `M`: the carried diagonal measure on
`ℝ²`.  (Defined for any `M`; physically meaningful when `M.IsJointOf A B`.) -/
noncomputable def jointBornMeasure (M : POVM H (ℝ × ℝ)) (ξ : H) : Measure (ℝ × ℝ) :=
  M.diag ξ

/-- `[done]` For a unit vector, a probability measure on `ℝ²` (mass `‖ξ‖² = 1`, `diag_univ_toReal`). -/
theorem isProbabilityMeasure_jointBornMeasure (M : POVM H (ℝ × ℝ)) {ξ : H} (hξ : ‖ξ‖ = 1) :
    IsProbabilityMeasure (jointBornMeasure M ξ) := by
  refine ⟨(ENNReal.toReal_eq_one_iff _).mp ?_⟩
  show ((M.diag ξ) Set.univ).toReal = 1
  rw [M.diag_univ_toReal, hξ, one_pow]

/-- `[done]` **The first marginal is `A`'s Born measure.**  From `IsJointOf` (operator marginal) and
the welds: `(M.diag ξ).fst S = (M.diag ξ)(S×ℝ) = ⟪ξ, E_A(S) ξ⟫ = (A.spectralPVM.diag ξ) S`. -/
theorem jointBornMeasure_fst {M : POVM H (ℝ × ℝ)} {A B : UnboundedObservable H}
    (hjoint : M.IsJointOf A B) (ξ : H) :
    (jointBornMeasure M ξ).fst = bornMeasure A.spectralPVM ξ := by
  refine Measure.ext fun S hS => ?_
  rw [Measure.fst_apply hS]
  show (M.diag ξ) (Prod.fst ⁻¹' S) = (A.spectralPVM.diag ξ) S
  rw [← Set.prod_univ]
  have hcoe : (((M.diag ξ) (S ×ˢ Set.univ)).toReal : ℂ)
      = (((A.spectralPVM.diag ξ) S).toReal : ℂ) := by
    rw [← M.inner_effect (S ×ˢ Set.univ) (hS.prod MeasurableSet.univ) ξ,
      ← A.spectralPVM.inner_proj S hS ξ, hjoint.1 S hS]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    (by exact_mod_cast hcoe)

/-- `[done]` **The second marginal is `B`'s Born measure.** -/
theorem jointBornMeasure_snd {M : POVM H (ℝ × ℝ)} {A B : UnboundedObservable H}
    (hjoint : M.IsJointOf A B) (ξ : H) :
    (jointBornMeasure M ξ).snd = bornMeasure B.spectralPVM ξ := by
  refine Measure.ext fun T hT => ?_
  rw [Measure.snd_apply hT]
  show (M.diag ξ) (Prod.snd ⁻¹' T) = (B.spectralPVM.diag ξ) T
  rw [← Set.univ_prod]
  have hcoe : (((M.diag ξ) (Set.univ ×ˢ T)).toReal : ℂ)
      = (((B.spectralPVM.diag ξ) T).toReal : ℂ) := by
    rw [← M.inner_effect (Set.univ ×ˢ T) (MeasurableSet.univ.prod hT) ξ,
      ← B.spectralPVM.inner_proj T hT ξ, hjoint.2 T hT]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    (by exact_mod_cast hcoe)

/-- `[needs spectralPVM + joint functional calculus]` **The correlation.**  The content a generic
coupling lacks: the joint law reproduces `⟪ξ, AB ξ⟫`.  For `ξ` in a suitable domain (`ξ ∈ D(AB)`),
`∫ p, p.1 * p.2 ∂(jointBornMeasure M ξ) = (⟪ξ, A(Bξ) ξ'⟫).re` via the joint functional calculus
(`xy` is the product of the two coordinate functions, whose calculus is `A·B` on the commuting joint
PVM).  SIGNATURE TO VERIFY: the spelling of `A(Bξ)` through the `LinearPMap`s and the domain
hypothesis. -/
theorem jointBornMeasure_correlation {M : POVM H (ℝ × ℝ)} {A B : UnboundedObservable H}
    (hjoint : M.IsJointOf A B) {ξ : H} (hξ : ξ ∈ B.domain) (hξ' : (B.toLinearPMap ⟨ξ, hξ⟩) ∈ A.domain) :
    ∫ p, p.1 * p.2 ∂(jointBornMeasure M ξ)
      = (⟪ξ, A.toLinearPMap ⟨B.toLinearPMap ⟨ξ, hξ⟩, hξ'⟩⟫_ℂ).re :=
  sorry

/-! ## §5  The Bell bridge, and the vacuity of the naive backward direction

The forward direction connects to `BellsTheorem`; the "failure of backward" must be located
correctly. -/

/-- **The naive coupling is vacuous** — recorded so no one re-derives a contentless iff.  For *any*
`A, B` (commuting or not) and any `ξ`, the product measure has the Born marginals.  Hence
`∃ μ_ξ` with the right marginals is always true and is *not* equivalent to commutativity.  Proof:
`Measure.fst_prod`, `Measure.snd_prod` (with each marginal a probability measure — hence the unit
vector `‖ξ‖ = 1`, without which the product's marginals are scaled by `‖ξ‖²` and the claim is false). -/
theorem exists_coupling_always (A B : UnboundedObservable H) {ξ : H} (hξ : ‖ξ‖ = 1) :
    ∃ μ : Measure (ℝ × ℝ),
      μ.fst = bornMeasure A.spectralPVM ξ ∧ μ.snd = bornMeasure B.spectralPVM ξ := by
  haveI := isProbabilityMeasure_bornMeasure A.spectralPVM hξ
  haveI := isProbabilityMeasure_bornMeasure B.spectralPVM hξ
  exact ⟨(bornMeasure A.spectralPVM ξ).prod (bornMeasure B.spectralPVM ξ),
    Measure.fst_prod, Measure.snd_prod⟩

/-! ### Forward to `BellsTheorem`

`[connects to BellsTheorem.LHV / CHSH_Bounds.Commuting — verify their API]`

A family `A₁, A₂, B₁, B₂` that **pairwise** strongly commutes (in particular the *same-side* pairs
`A₁,A₂` and `B₁,B₂`) admits a single global joint PVM on `ℝ⁴`, hence a global joint Born law, hence a
local-hidden-variable model in the sense of `BellsTheorem.LHV`, hence the CHSH bound:
```
theorem chsh_le_two_of_stronglyCommute
    (A₁ A₂ B₁ B₂ : UnboundedObservable H)
    (hAA : StronglyCommute A₁ A₂) (hBB : StronglyCommute B₁ B₂)
    (hAB : ∀ i j, StronglyCommute (![A₁,A₂] i) (![B₁,B₂] j)) (ξ : H) :
    |⟪ξ, …CHSH operator… ξ⟫.re| ≤ 2
```
routed through your `BellsTheorem.LHV` model built from the global joint Born law and your existing
`CHSH_Bounds.Commuting`.  The Tsirelson bound (`≤ 2√2`) is the quantum ceiling *without* the
same-side commutativity hypotheses — the regime where no global joint law exists, which is precisely
the failure the naive "backward direction" was groping for, now correctly located at the level of the
incompatible *family* rather than a single pair.
-/

end Spectra.QuantumMechanics.BornRule
