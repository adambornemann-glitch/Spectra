/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.OneParameterUnitaryGroup.Basic
import Spectra.Mathlib.MeasureTheory.Integral.Basic

/-!
# Resolvent Integrals for Unitary Groups

This file defines the resolvent integrals used in Stone's theorem:
* `R₊(φ) = (-i) ∫₀^∞ e^{-t} U(t)φ dt`
* `R₋(φ) = i ∫₀^∞ e^{-t} U(-t)φ dt`

These solve `(A + iI)ψ = φ` and `(A - iI)ψ = φ` respectively, which establishes
surjectivity of `A ± iI` and hence self-adjointness of the generator.

## Main definitions

* `resolventIntegralPlus`: the integral `(-i) ∫₀^∞ e^{-t} U(t)φ dt`
* `resolventIntegralMinus`: the integral `i ∫₀^∞ e^{-t} U(-t)φ dt`

## Main statements

* `continuous_unitary_apply`: `t ↦ U(t)φ` is continuous.
* `integrable_exp_neg_unitary`: `e^{-t} • U(t)φ` is integrable on `[0, ∞)`.
* `norm_integral_exp_neg_unitary_le`: the exponential-decay integral is bounded by `‖φ‖`.
* `norm_resolventIntegralPlus_le`: `‖R₊(φ)‖ ≤ ‖φ‖`.
* `norm_resolventIntegralMinus_le`: `‖R₋(φ)‖ ≤ ‖φ‖`.

## Implementation notes

`resolventIntegralMinus`'s contraction bound (`norm_resolventIntegralMinus_le`) is obtained by
applying `norm_integral_exp_neg_unitary_le` to the time-reversed group `reversedGroup U_grp`
(`OneParameterUnitaryGroup/Basic.lean`), whose defining property `(reversedGroup U).U t = U.U (-t)`
(`reversedGroup_apply`) turns `U(-t)` into the reversed group's own forward evolution. This lets the
`R₋` contraction proof mirror the `R₊` one exactly instead of re-deriving the bound from scratch.

## References

* [Stone, *On one-parameter unitary groups in Hilbert space*][stone1932], Ann. of Math. 33 (1932).

## Tags

resolvent, unitary group, Laplace transform
-/
open MeasureTheory Topology Complex
open MeasureTheory.Integral
open Spectra.OneParameterUnitaryGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Resolvent

section UnitaryGroupIntegration

variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- `t ↦ U(t)φ` is continuous for a fixed vector `φ`. -/
lemma continuous_unitary_apply (φ : H) :
    Continuous (fun t => U_grp.U t φ) :=
  U_grp.strong_continuous φ

/-- `e^{-t} • U(t)φ` is integrable on `[0, ∞)`. -/
lemma integrable_exp_neg_unitary (φ : H) :
    IntegrableOn (fun t => Real.exp (-t) • U_grp.U t φ) (Set.Ici 0) volume := by
  apply integrable_exp_decay_continuous
    (fun t => U_grp.U t φ)
    (U_grp.strong_continuous φ)
    ‖φ‖
  intro t _ht
  exact le_of_eq (norm_preserving U_grp t φ)

/-- The norm of the exponential-decay integral is bounded by `‖φ‖`. -/
lemma norm_integral_exp_neg_unitary_le (φ : H) :
    ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ‖ ≤ ‖φ‖ := by
  apply norm_integral_exp_decay_le
    (fun t => U_grp.U t φ)
    (U_grp.strong_continuous φ)
    ‖φ‖
  intro t _ht
  exact le_of_eq (norm_preserving U_grp t φ)

end UnitaryGroupIntegration

section ResolventIntegrals

variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- The resolvent integral `R₊(φ) = (-i) ∫₀^∞ e^{-t} U(t)φ dt`.
    This solves `(A + iI)ψ = φ` where `A` is the generator. -/
noncomputable def resolventIntegralPlus (φ : H) : H :=
  (-I) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ

/-- The resolvent integral `R₋(φ) = i ∫₀^∞ e^{-t} U(-t)φ dt`.
    This solves `(A - iI)ψ = φ` where `A` is the generator. -/
noncomputable def resolventIntegralMinus (φ : H) : H :=
  I • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ

/-- `R₊` is a contraction: `‖resolventIntegralPlus φ‖ ≤ ‖φ‖`. -/
lemma norm_resolventIntegralPlus_le (φ : H) :
    ‖resolventIntegralPlus U_grp φ‖ ≤ ‖φ‖ := by
  unfold resolventIntegralPlus
  calc ‖(-I) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ‖
      = ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ‖ := by simp [norm_smul]
    _ ≤ ‖φ‖ := norm_integral_exp_neg_unitary_le U_grp φ

/-- `R₋` is a contraction: `‖resolventIntegralMinus φ‖ ≤ ‖φ‖`. -/
lemma norm_resolventIntegralMinus_le (φ : H) :
    ‖resolventIntegralMinus U_grp φ‖ ≤ ‖φ‖ := by
  unfold resolventIntegralMinus
  calc ‖I • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ‖
      = ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ‖ := by simp [norm_smul]
    _ = ‖∫ t in Set.Ici 0, Real.exp (-t) • (reversedGroup U_grp).U t φ‖ := by
        simp [reversedGroup_apply]
    _ ≤ ‖φ‖ := norm_integral_exp_neg_unitary_le (reversedGroup U_grp) φ

end Spectra.Resolvent.ResolventIntegrals
