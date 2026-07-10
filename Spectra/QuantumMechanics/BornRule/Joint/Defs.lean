/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.BornRule.POVM
import Spectra.Operator.SelfAdjoint
import Spectra.SpectralTheory.Calculus.Bounded
import Spectra.SpectralTheory.Measure.Convergence
import Spectra.SpectralTheory.ResolventForm
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

## Main definitions

* `StronglyCommute` — the correct commutativity notion (projections of `spectralPVM` commute).
* `POVM.IsProjective` — a POVM is a PVM (multiplicative); the joint PVM is a projective
  `POVM H (ℝ × ℝ)`.
* `POVM.IsJointOf` — the marginal-PVM predicate: the cylinder effects recover `E_A` and `E_B`.
* `jointBornMeasure` — the per-state joint distribution carried by a joint PVM.

## Main statements

* `stronglyCommute_iff_groups_commute` — strong commutativity is equivalent to commutation of the
  one-parameter unitary groups, via the cross-group engines of §0.
* `stronglyCommute_of_jointPVM` — the easy (backward) half of the corrected iff: a joint projective
  PVM forces strong commutativity.
* `jointBornMeasure_fst` / `jointBornMeasure_snd` — the Born measures are the marginals of the joint
  Born measure.
* `exists_coupling_always` — the naive per-state coupling is vacuous.

The full equivalence `stronglyCommute_iff_jointPVM` (whose forward direction is the genuine
multivariate spectral-theorem construction) and the correlation identity
`jointBornMeasure_correlation` (`∫ xy dμ_ξ = ⟪ξ, AB ξ⟫`) live in the cross-file
`BornRule.Joint.Forward`, where they are proved sorry-free and axiom-clean.

## The Bell connection (forward, to `BellsTheorem`)

A single commuting pair *always* has a joint law, so commuting observables are jointly classical and
satisfy every Bell-type inequality (→ `CHSH_Bounds.Commuting`).  The Bell *obstruction* is not about
one pair: it is the nonexistence of a **single global law over a family of incompatible settings**
`A₁,A₂,B₁,B₂` reproducing all measured correlations `⟪ξ, AᵢBⱼ ξ⟫`.  That global law is exactly the
local-hidden-variable model of `BellsTheorem.LHV`; CHSH (`≤ 2`) and Tsirelson (`≤ 2√2`) quantify the
gap.  Non-commutativity of the *same-side* observables (`A₁,A₂`) is what blocks the global law — not
anything about a single cross-pair `(Aᵢ, Bⱼ)`, each of which (being commuting/spacelike) does have a
joint law.

## Implementation notes

Every `E_A` is `A.spectralPVM`.  The forward construction of the joint PVM (in
`BornRule.Joint.Forward`) is built by Carathéodory extension of the bimeasure content
`μ_ξ(S × T) = ⟪ξ, E_A(S) E_B(T) ξ⟫`, with the operator field recovered by polarization; it is the
two-dimensional analogue of the in-house Herglotz/Stone spectral-measure construction.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*][reedsimon1980],
  §VIII.5 (strong commutativity; the Nelson counterexample is §VIII, Example 1 in some editions).
* [Conway, *A Course in Operator Theory*], spectral theorem for commuting normal operators.
* [Tsirelson, *Quantum generalizations of Bell's inequality*] (1980).

## Tags

joint spectral measure, strong commutativity, joint PVM, Born rule, projection-valued measure, Bell,
CHSH
-/

open MeasureTheory Complex Spectra
open scoped InnerProductSpace
open Spectra.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## §0  Cross-group commutation engines

The whole of §1's group/projection equivalence reduces to a single algebraic fact about the
bounded functional calculus of a *fixed* one-parameter unitary group `U`: an operator `D` that
commutes with the group `U(t)` (resp. with every spectral projection `E(S)`) commutes with the
entire bounded Borel calculus `Φ(g)`.  Both are proved by reducing operator commutation to the
polarized pairing `spectralForm` and using that two pairings agreeing on a *determining family*
(characters, resp. indicators) agree on every bounded measurable symbol — the character case is
`integral_combination_ext'` (Fourier uniqueness), the indicator case is elementary
(`Measure.ext`).  No Stone–Weierstrass, no operator topology. -/

namespace Spectra.QuantumMechanics.SpectralTheory

open Complex MeasureTheory
open scoped InnerProductSpace
open Spectra.Borel

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Character determinacy of the pairing.**  Two polarized spectral pairings that agree on
every character agree on every bounded measurable symbol.  A direct instance of
`integral_combination_ext'` over the four polarization vectors. -/
theorem spectralForm_ext_of_char (U : OneParameterUnitaryGroup (H := H)) (ξ₁ η₁ ξ₂ η₂ : H)
    (hchar : ∀ t : ℝ, spectralForm U ξ₁ η₁ (fun l => cexp (I * l * t))
              = spectralForm U ξ₂ η₂ (fun l => cexp (I * l * t)))
    {g : ℝ → ℂ} (hgm : Measurable g) (hgb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) :
    spectralForm U ξ₁ η₁ g = spectralForm U ξ₂ η₂ g := by
  have key := Spectra.Fourier.integral_combination_ext'
    (![1 / 4, -(1 / 4), I / 4, -(I / 4)] : Fin 4 → ℂ)
    (fun i => borelMeasure U (![ξ₁ + η₁, ξ₁ - η₁, ξ₁ - I • η₁, ξ₁ + I • η₁] i))
    (![1 / 4, -(1 / 4), I / 4, -(I / 4)] : Fin 4 → ℂ)
    (fun j => borelMeasure U (![ξ₂ + η₂, ξ₂ - η₂, ξ₂ - I • η₂, ξ₂ + I • η₂] j))
    (fun t => by
      have h := hchar t
      simp only [spectralForm] at h
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, add_zero]
      linear_combination h)
    hgm hgb
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero] at key
  simp only [spectralForm]
  linear_combination key

/-- **Indicator determinacy of the pairing.**  Two polarized spectral pairings that agree on
every indicator agree on every bounded measurable symbol.  Elementary: comparing real and
imaginary parts at indicators yields equalities of the (finite, positive) Borel measures via
`Measure.ext`, after which the bounded-symbol integrals agree term by term. -/
theorem spectralForm_ext_of_set (U : OneParameterUnitaryGroup (H := H)) (ξ₁ η₁ ξ₂ η₂ : H)
    (hset : ∀ (S : Set ℝ), MeasurableSet S →
       spectralForm U ξ₁ η₁ (Set.indicator S (fun _ => (1 : ℂ)))
         = spectralForm U ξ₂ η₂ (Set.indicator S (fun _ => (1 : ℂ))))
    {g : ℝ → ℂ} (hgm : Measurable g) (hgb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) :
    spectralForm U ξ₁ η₁ g = spectralForm U ξ₂ η₂ g := by
  obtain ⟨C, hC⟩ := hgb
  have hgi : ∀ v : H, Integrable g (borelMeasure U v) := fun v =>
    Spectra.Fourier.integrable_of_bounded hgm hC
  have hnt : ∀ (v : H) (S : Set ℝ), (borelMeasure U v) S ≠ ⊤ := fun v S => measure_ne_top _ _
  -- The two real identities extracted from the indicator hypothesis (real / imaginary parts).
  have hparts : ∀ (S : Set ℝ), MeasurableSet S →
      ((borelMeasure U (ξ₁ + η₁)) S).toReal - ((borelMeasure U (ξ₁ - η₁)) S).toReal
          = ((borelMeasure U (ξ₂ + η₂)) S).toReal - ((borelMeasure U (ξ₂ - η₂)) S).toReal
      ∧ ((borelMeasure U (ξ₁ - I • η₁)) S).toReal - ((borelMeasure U (ξ₁ + I • η₁)) S).toReal
          = ((borelMeasure U (ξ₂ - I • η₂)) S).toReal
              - ((borelMeasure U (ξ₂ + I • η₂)) S).toReal := by
    intro S hS
    have h := hset S hS
    simp only [spectralForm, integral_indicator_const (1 : ℂ) hS, Complex.real_smul,
      mul_one, Measure.real_def] at h
    -- clear the `/4` and split into real/imaginary parts
    have h' : ((((borelMeasure U (ξ₁ + η₁)) S).toReal : ℂ) - ((borelMeasure U (ξ₁ - η₁)) S).toReal
            + (((((borelMeasure U (ξ₁ - I • η₁)) S).toReal : ℂ)
              - ((borelMeasure U (ξ₁ + I • η₁)) S).toReal)) * I)
        = ((((borelMeasure U (ξ₂ + η₂)) S).toReal : ℂ) - ((borelMeasure U (ξ₂ - η₂)) S).toReal
            + (((((borelMeasure U (ξ₂ - I • η₂)) S).toReal : ℂ)
              - ((borelMeasure U (ξ₂ + I • η₂)) S).toReal)) * I) := by
      linear_combination (4 : ℂ) * h
    rw [Complex.ext_iff] at h'
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, add_zero, zero_add] at h'
    exact ⟨by linarith [h'.1], by linarith [h'.2]⟩
  -- the two measure identities, via `Measure.ext`
  have M1 : borelMeasure U (ξ₁ + η₁) + borelMeasure U (ξ₂ - η₂)
      = borelMeasure U (ξ₁ - η₁) + borelMeasure U (ξ₂ + η₂) := by
    refine Measure.ext fun S hS => ?_
    rw [Measure.add_apply, Measure.add_apply]
    refine (ENNReal.toReal_eq_toReal_iff'
      (ENNReal.add_ne_top.mpr ⟨hnt _ _, hnt _ _⟩)
      (ENNReal.add_ne_top.mpr ⟨hnt _ _, hnt _ _⟩)).mp ?_
    rw [ENNReal.toReal_add (hnt _ _) (hnt _ _), ENNReal.toReal_add (hnt _ _) (hnt _ _)]
    linarith [(hparts S hS).1]
  have M2 : borelMeasure U (ξ₁ - I • η₁) + borelMeasure U (ξ₂ + I • η₂)
      = borelMeasure U (ξ₁ + I • η₁) + borelMeasure U (ξ₂ - I • η₂) := by
    refine Measure.ext fun S hS => ?_
    rw [Measure.add_apply, Measure.add_apply]
    refine (ENNReal.toReal_eq_toReal_iff'
      (ENNReal.add_ne_top.mpr ⟨hnt _ _, hnt _ _⟩)
      (ENNReal.add_ne_top.mpr ⟨hnt _ _, hnt _ _⟩)).mp ?_
    rw [ENNReal.toReal_add (hnt _ _) (hnt _ _), ENNReal.toReal_add (hnt _ _) (hnt _ _)]
    linarith [(hparts S hS).2]
  -- integrate `g` against the measure identities and recombine
  have h1 : (∫ l, g l ∂(borelMeasure U (ξ₁ + η₁))) + ∫ l, g l ∂(borelMeasure U (ξ₂ - η₂))
      = (∫ l, g l ∂(borelMeasure U (ξ₁ - η₁))) + ∫ l, g l ∂(borelMeasure U (ξ₂ + η₂)) := by
    rw [← integral_add_measure (hgi _) (hgi _), M1, integral_add_measure (hgi _) (hgi _)]
  have h2 : (∫ l, g l ∂(borelMeasure U (ξ₁ - I • η₁))) + ∫ l, g l ∂(borelMeasure U (ξ₂ + I • η₂))
      = (∫ l, g l ∂(borelMeasure U (ξ₁ + I • η₁))) + ∫ l, g l ∂(borelMeasure U (ξ₂ - I • η₂)) := by
    rw [← integral_add_measure (hgi _) (hgi _), M2, integral_add_measure (hgi _) (hgi _)]
  simp only [spectralForm]
  linear_combination (h1 + h2 * I) / 4

/-- **The group commutant lies in the calculus commutant.**  If `D` commutes with `U(t)` for
all `t`, then `D` commutes with the bounded functional calculus `Φ(g)` for every bounded
measurable symbol `g`. -/
theorem commute_spectralCalculus_of_commute_group (U : OneParameterUnitaryGroup (H := H))
    (D : H →L[ℂ] H) (hD : ∀ t : ℝ, Commute (U.U t) D)
    {g : ℝ → ℂ} (hgm : Measurable g) (hgb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) :
    Commute (spectralCalculus U g hgm hgb) D := by
  have hkey : ∀ ξ η : H,
      spectralForm U ξ (D η) g = spectralForm U (ContinuousLinearMap.adjoint D ξ) η g := by
    intro ξ η
    refine spectralForm_ext_of_char U ξ (D η) (ContinuousLinearMap.adjoint D ξ) η
      (fun t => ?_) hgm hgb
    rw [spectralForm_char, spectralForm_char]
    have hcomm : U.U t (D η) = D (U.U t η) := by
      have h := DFunLike.congr_fun (hD t).eq η
      simpa only [ContinuousLinearMap.mul_apply] using h
    rw [hcomm, ContinuousLinearMap.adjoint_inner_left]
  change spectralCalculus U g hgm hgb * D = D * spectralCalculus U g hgm hgb
  refine ContinuousLinearMap.ext fun η => ext_inner_left ℂ fun ξ => ?_
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, inner_spectralCalculus,
    ← ContinuousLinearMap.adjoint_inner_left D (spectralCalculus U g hgm hgb η) ξ,
    inner_spectralCalculus]
  exact hkey ξ η

/-- **The projection commutant lies in the calculus commutant.**  If `D` commutes with every
spectral projection `E(S)`, then `D` commutes with the bounded functional calculus `Φ(g)` for
every bounded measurable symbol `g`. -/
theorem commute_spectralCalculus_of_commute_proj (U : OneParameterUnitaryGroup (H := H))
    (D : H →L[ℂ] H)
    (hD : ∀ (S : Set ℝ) (hS : MeasurableSet S), Commute (spectralProjection U S hS) D)
    {g : ℝ → ℂ} (hgm : Measurable g) (hgb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) :
    Commute (spectralCalculus U g hgm hgb) D := by
  have hkey : ∀ ξ η : H,
      spectralForm U ξ (D η) g = spectralForm U (ContinuousLinearMap.adjoint D ξ) η g := by
    intro ξ η
    refine spectralForm_ext_of_set U ξ (D η) (ContinuousLinearMap.adjoint D ξ) η
      (fun S hS => ?_) hgm hgb
    have hcomm : spectralProjection U S hS (D η) = D (spectralProjection U S hS η) := by
      have h := DFunLike.congr_fun (hD S hS).eq η
      simpa only [ContinuousLinearMap.mul_apply] using h
    change spectralForm U ξ (D η) (Set.indicator S (fun _ => (1 : ℂ)))
        = spectralForm U (ContinuousLinearMap.adjoint D ξ) η (Set.indicator S (fun _ => (1 : ℂ)))
    rw [← inner_spectralCalculus U _ (measurable_const.indicator hS) (indicator_one_bdd S) ξ (D η)]
    rw [← inner_spectralCalculus U _ (measurable_const.indicator hS) (indicator_one_bdd S)
      (ContinuousLinearMap.adjoint D ξ) η]
    change ⟪ξ, spectralProjection U S hS (D η)⟫_ℂ
        = ⟪ContinuousLinearMap.adjoint D ξ, spectralProjection U S hS η⟫_ℂ
    rw [hcomm, ContinuousLinearMap.adjoint_inner_left]
  change spectralCalculus U g hgm hgb * D = D * spectralCalculus U g hgm hgb
  refine ContinuousLinearMap.ext fun η => ext_inner_left ℂ fun ξ => ?_
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, inner_spectralCalculus,
    ← ContinuousLinearMap.adjoint_inner_left D (spectralCalculus U g hgm hgb η) ξ,
    inner_spectralCalculus]
  exact hkey ξ η

end Spectra.QuantumMechanics.SpectralTheory

namespace Spectra.QuantumMechanics.BornRule

open PVM

/-! ## §1  Strong commutativity (the correct hypothesis) -/

/-- **Strong commutativity** of two observables: their spectral projections commute for all Borel
sets.  This is the notion that admits a joint PVM.

It is *strictly stronger* than `Commute A.toLinearPMap B.toLinearPMap` (algebraic commutation on a
common domain), which by Nelson's counterexample does **not** imply a joint spectral measure.  It is
equivalent to: the resolvents commute; the unitary groups `e^{isA}`, `e^{itB}` commute (the form the
Stone machinery exposes directly). -/
def StronglyCommute (A B : SelfAdjointOperator H) : Prop :=
  ∀ (S T : Set ℝ) (hS : MeasurableSet S) (hT : MeasurableSet T),
    Commute (A.spectralPVM.proj S hS) (B.spectralPVM.proj T hT)

/-- **Equivalence with commutation of the unitary groups** — the form most convenient to *verify*
in practice (and the one the `OneParameterUnitaryGroup` stack supplies).

Both directions go through the cross-group commutation engines of §0 — no Stone–Weierstrass, no
operator topology, no Stone's-formula limit.  `(⇐)` lifts character commutation to projection
commutation via `commute_spectralCalculus_of_commute_group` (Fourier uniqueness); `(⇒)` lifts
projection commutation to character commutation via `commute_spectralCalculus_of_commute_proj`
(`Measure.ext`); each is two applications of an engine plus `Commute.symm`, using
`E_A(S) = Φ_A(1_S)` and `e^{isA} = Φ_A(e^{is·})` (`spectralCalculus_char`). -/
theorem stronglyCommute_iff_groups_commute (A B : SelfAdjointOperator H) :
    StronglyCommute A B ↔
      ∀ s t : ℝ, Commute ((YosidaHille.genToGroup A.selfAdjoint).U s)
        ((YosidaHille.genToGroup B.selfAdjoint).U t) := by
  constructor
  · -- (⇒) projections commute ⟹ groups commute
    intro hSC s t
    -- lift the `A`-side indicators to the character `e^{is·}`, keeping `e^{it·}` fixed
    have hstep : ∀ (S : Set ℝ) (hS : MeasurableSet S),
        Commute (SpectralTheory.spectralProjection (YosidaHille.genToGroup A.selfAdjoint) S hS)
          ((YosidaHille.genToGroup B.selfAdjoint).U t) := by
      intro S hS
      have h := SpectralTheory.commute_spectralCalculus_of_commute_proj
        (YosidaHille.genToGroup B.selfAdjoint)
        (SpectralTheory.spectralProjection (YosidaHille.genToGroup A.selfAdjoint) S hS)
        (fun T hT => (hSC S T hS hT).symm)
        (SpectralTheory.char_measurable t) (SpectralTheory.char_bdd t)
      rw [SpectralTheory.spectralCalculus_char] at h
      exact h.symm
    have h2 := SpectralTheory.commute_spectralCalculus_of_commute_proj
      (YosidaHille.genToGroup A.selfAdjoint) ((YosidaHille.genToGroup B.selfAdjoint).U t)
      hstep (SpectralTheory.char_measurable s) (SpectralTheory.char_bdd s)
    rwa [SpectralTheory.spectralCalculus_char] at h2
  · -- (⇐) groups commute ⟹ projections commute
    intro hG S T hS hT
    change Commute (SpectralTheory.spectralProjection (YosidaHille.genToGroup A.selfAdjoint) S hS)
        (SpectralTheory.spectralProjection (YosidaHille.genToGroup B.selfAdjoint) T hT)
    -- lift the `A`-side character `e^{is·}` to indicators, keeping the `B`-projection fixed
    have hstep : ∀ s : ℝ, Commute ((YosidaHille.genToGroup A.selfAdjoint).U s)
        (SpectralTheory.spectralProjection (YosidaHille.genToGroup B.selfAdjoint) T hT) := fun s =>
      (SpectralTheory.commute_spectralCalculus_of_commute_group
        (YosidaHille.genToGroup B.selfAdjoint) ((YosidaHille.genToGroup A.selfAdjoint).U s)
        (fun u => (hG s u).symm)
        (measurable_const.indicator hT) (SpectralTheory.indicator_one_bdd T)).symm
    exact SpectralTheory.commute_spectralCalculus_of_commute_group
      (YosidaHille.genToGroup A.selfAdjoint)
      (SpectralTheory.spectralProjection (YosidaHille.genToGroup B.selfAdjoint) T hT) hstep
      (measurable_const.indicator hS) (SpectralTheory.indicator_one_bdd S)

/-! ## §2  The joint PVM as a projective POVM on `ℝ × ℝ`

A joint spectral measure is a PVM on `ℝ²`.  Rather than re-bundle, reuse the existing
`POVM H (ℝ × ℝ)` and add the projectivity predicate that distinguishes a PVM from a general POVM —
i.e. the `proj_inter` axiom that the POVM structure dropped. -/

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
spectral projection `E_A(S)`.  This is the hypothesis with teeth — it forces the marginal
*operators* (not merely the marginal measures) to be `A`'s, which is what couples to
commutativity. -/
def _root_.Spectra.POVM.IsJointOf (M : POVM H (ℝ × ℝ)) (A B : SelfAdjointOperator H) : Prop :=
  (∀ (S : Set ℝ) (hS : MeasurableSet S),
      M.effect (S ×ˢ Set.univ) (hS.prod MeasurableSet.univ) = A.spectralPVM.proj S hS)
    ∧ (∀ (T : Set ℝ) (hT : MeasurableSet T),
      M.effect (Set.univ ×ˢ T) (MeasurableSet.univ.prod hT) = B.spectralPVM.proj T hT)

/-! ## §3  The corrected iff -/

/-- `[done]` The easy half, isolated: a joint projective PVM forces strong commutativity.  For any
`S, T`, `E_A(S)·E_B(T) = M(S×ℝ)·M(ℝ×T) = M((S×ℝ)∩(ℝ×T)) = M((ℝ×T)∩(S×ℝ)) = M(ℝ×T)·M(S×ℝ) =
E_B(T)·E_A(S)`.  Pure algebra from `IsProjective` + `IsJointOf` + `Set.inter_comm`. -/
theorem stronglyCommute_of_jointPVM {A B : SelfAdjointOperator H} {M : POVM H (ℝ × ℝ)}
    (hproj : M.IsProjective) (hjoint : M.IsJointOf A B) :
    StronglyCommute A B := by
  intro S T hS hT
  rw [← hjoint.1 S hS, ← hjoint.2 T hT]
  change M.effect (S ×ˢ Set.univ) (hS.prod MeasurableSet.univ)
      * M.effect (Set.univ ×ˢ T) (MeasurableSet.univ.prod hT)
    = M.effect (Set.univ ×ˢ T) (MeasurableSet.univ.prod hT)
      * M.effect (S ×ˢ Set.univ) (hS.prod MeasurableSet.univ)
  rw [hproj _ _ _ _, hproj _ _ _ _]
  exact M.effect_congr (Set.inter_comm _ _) _ _

/- The full equivalence `stronglyCommute_iff_jointPVM` (whose **forward** direction is the genuine
multivariate-spectral-theorem construction) lives in `BornRule.Joint.Forward`, sorry-free.  Its
**backward** half is the proved `stronglyCommute_of_jointPVM` above. -/

/-! ## §4  The joint Born law (forward corollary)

Given a joint PVM for a commuting pair, the per-state joint distribution is its diagonal measure.
Unlike a generic coupling it (a) has the Born measures as *marginals via the operator marginals*,
and (b) reproduces the correlation `⟪ξ, AB ξ⟫`. -/

/-- The **joint Born measure** of a state `ξ` under a joint PVM `M`: the carried diagonal measure on
`ℝ²`.  (Defined for any `M`; physically meaningful when `M.IsJointOf A B`.) -/
noncomputable def jointBornMeasure (M : POVM H (ℝ × ℝ)) (ξ : H) : Measure (ℝ × ℝ) :=
  M.diag ξ

/-- `[done]` For a unit vector, a probability measure on `ℝ²`
(mass `‖ξ‖² = 1`, `diag_univ_toReal`). -/
theorem isProbabilityMeasure_jointBornMeasure (M : POVM H (ℝ × ℝ)) {ξ : H} (hξ : ‖ξ‖ = 1) :
    IsProbabilityMeasure (jointBornMeasure M ξ) := by
  refine ⟨(ENNReal.toReal_eq_one_iff _).mp ?_⟩
  change ((M.diag ξ) Set.univ).toReal = 1
  rw [M.diag_univ_toReal, hξ, one_pow]

/-- `[done]` **The first marginal is `A`'s Born measure.**  From `IsJointOf` (operator marginal) and
the welds: `(M.diag ξ).fst S = (M.diag ξ)(S×ℝ) = ⟪ξ, E_A(S) ξ⟫ = (A.spectralPVM.diag ξ) S`. -/
theorem jointBornMeasure_fst {M : POVM H (ℝ × ℝ)} {A B : SelfAdjointOperator H}
    (hjoint : M.IsJointOf A B) (ξ : H) :
    (jointBornMeasure M ξ).fst = bornMeasure A.spectralPVM ξ := by
  refine Measure.ext fun S hS => ?_
  rw [Measure.fst_apply hS]
  change (M.diag ξ) (Prod.fst ⁻¹' S) = (A.spectralPVM.diag ξ) S
  rw [← Set.prod_univ]
  have hcoe : (((M.diag ξ) (S ×ˢ Set.univ)).toReal : ℂ)
      = (((A.spectralPVM.diag ξ) S).toReal : ℂ) := by
    rw [← M.inner_effect (S ×ˢ Set.univ) (hS.prod MeasurableSet.univ) ξ,
      ← A.spectralPVM.inner_proj S hS ξ, hjoint.1 S hS]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    (by exact_mod_cast hcoe)

/-- `[done]` **The second marginal is `B`'s Born measure.** -/
theorem jointBornMeasure_snd {M : POVM H (ℝ × ℝ)} {A B : SelfAdjointOperator H}
    (hjoint : M.IsJointOf A B) (ξ : H) :
    (jointBornMeasure M ξ).snd = bornMeasure B.spectralPVM ξ := by
  refine Measure.ext fun T hT => ?_
  rw [Measure.snd_apply hT]
  change (M.diag ξ) (Prod.snd ⁻¹' T) = (B.spectralPVM.diag ξ) T
  rw [← Set.univ_prod]
  have hcoe : (((M.diag ξ) (Set.univ ×ˢ T)).toReal : ℂ)
      = (((B.spectralPVM.diag ξ) T).toReal : ℂ) := by
    rw [← M.inner_effect (Set.univ ×ˢ T) (MeasurableSet.univ.prod hT) ξ,
      ← B.spectralPVM.inner_proj T hT ξ, hjoint.2 T hT]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    (by exact_mod_cast hcoe)

/- The correlation identity `jointBornMeasure_correlation`
(`∫ p, p.1 * p.2 ∂(jointBornMeasure M ξ) = (⟪ξ, A(Bξ)⟫).re`), a corollary of the joint functional
calculus, lives in `BornRule.Joint.Forward`. -/

/-! ## §5  The Bell bridge, and the vacuity of the naive backward direction

The forward direction connects to `BellsTheorem`; the "failure of backward" must be located
correctly. -/

/-- **The naive coupling is vacuous** — recorded so no one re-derives a contentless iff.  For *any*
`A, B` (commuting or not) and any `ξ`, the product measure has the Born marginals.  Hence
`∃ μ_ξ` with the right marginals is always true and is *not* equivalent to commutativity.  Proof:
`Measure.fst_prod`, `Measure.snd_prod` (with each marginal a probability measure — hence the unit
vector `‖ξ‖ = 1`, without which the product's marginals are scaled by `‖ξ‖²` and the claim is
false). -/
theorem exists_coupling_always (A B : SelfAdjointOperator H) {ξ : H} (hξ : ‖ξ‖ = 1) :
    ∃ μ : Measure (ℝ × ℝ),
      μ.fst = bornMeasure A.spectralPVM ξ ∧ μ.snd = bornMeasure B.spectralPVM ξ := by
  haveI := isProbabilityMeasure_bornMeasure A.spectralPVM hξ
  haveI := isProbabilityMeasure_bornMeasure B.spectralPVM hξ
  exact ⟨(bornMeasure A.spectralPVM ξ).prod (bornMeasure B.spectralPVM ξ),
    Measure.fst_prod, Measure.snd_prod⟩

/-! ### Forward to `BellsTheorem`

`[connects to BellsTheorem.LHV / CHSH_Bounds.Commuting — verify their API]`

A family `A₁, A₂, B₁, B₂` that **pairwise** strongly commutes (in particular the *same-side* pairs
`A₁,A₂` and `B₁,B₂`) admits a single global joint PVM on `ℝ⁴`, hence a global joint Born law, hence
a local-hidden-variable model in the sense of `BellsTheorem.LHV`, hence the CHSH bound:
```
theorem chsh_le_two_of_stronglyCommute
    (A₁ A₂ B₁ B₂ : SelfAdjointOperator H)
    (hAA : StronglyCommute A₁ A₂) (hBB : StronglyCommute B₁ B₂)
    (hAB : ∀ i j, StronglyCommute (![A₁,A₂] i) (![B₁,B₂] j)) (ξ : H) :
    |⟪ξ, …CHSH operator… ξ⟫.re| ≤ 2
```
routed through the `BellsTheorem.LHV` model built from the global joint Born law and the existing
`CHSH_Bounds.Commuting`.  The Tsirelson bound (`≤ 2√2`) is the quantum ceiling *without* the
same-side commutativity hypotheses — the regime where no global joint law exists, which is precisely
the failure the naive "backward direction" was groping for, now correctly located at the level of
the incompatible *family* rather than a single pair.
-/

end Spectra.QuantumMechanics.BornRule
