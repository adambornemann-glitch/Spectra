/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
File: Spectra/SoboleveSpaces/WeakDerivative.lean
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
/-!
# Sobolev Spaces on ℝ³: Foundations

This file lays the groundwork for `H¹(ℝ³)` and `H²(ℝ³)`:

* the configuration space `R3 := EuclideanSpace ℝ (Fin 3)` with its Lebesgue
  measure structure;
* the Hilbert space `L2_R3 := Lp ℂ 2 (volume : Measure R3)`;
* the predicate `HasWeakDerivative` capturing the distributional definition of
  the partial derivative;
* structural lemmas about smooth, compactly supported test functions — closure
  under complex conjugation, L² membership, and the well-behavedness of their
  partial derivatives — that the rest of the development reuses.

The density theory, submodule layer, integration by parts, and the operator
theory all build on this file.

## References

* [Adams, Fournier, *Sobolev Spaces*][adams2003]
* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975]
* [Lieb, Loss, *Analysis*][lieb2001], Chapter 7.
-/
open MeasureTheory
open scoped Pointwise ContDiff
namespace Spectra.Sobolev

/-! ### Configuration space and Hilbert space -/

/-- The physical configuration space ℝ³. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

instance : MeasurableSpace R3 := borel R3
instance : BorelSpace R3 := ⟨rfl⟩
-- `MeasureSpace R3` is provided by Mathlib's `measureSpaceOfInnerProductSpace`
-- (`volume := stdOrthonormalBasis.toBasis.addHaar`), which agrees with Mathlib's
-- L² Fourier transform. We deliberately do NOT declare our own `⟨Measure.addHaar⟩`
-- instance, to avoid a measure-instance diamond against `Lp.fourierTransformₗᵢ`.

/-- The Hilbert space L²(ℝ³, ℂ) with Lebesgue measure.

    This is the state space of non-relativistic quantum mechanics.
    It carries `NormedAddCommGroup`, `InnerProductSpace ℂ`, and
    `CompleteSpace` instances from Mathlib, making it a valid
    instantiation target for `Generator`. -/
abbrev L2_R3 : Type := Lp ℂ 2 (volume : Measure R3)

/-! ### Weak derivatives -/

/-- Predicate: `g` is the weak partial derivative of `f` in direction `i`.

    That is, for every smooth compactly supported test function φ:
      ∫ f(x) ∂ᵢφ(x) dx = - ∫ g(x) φ(x) dx

    We state this in terms of Lp representatives. The actual verification
    requires the distributional definition against test functions, which
    we axiomatize here and discharge later via mollification. -/
def HasWeakDerivative (f : L2_R3) (i : Fin 3) (g : L2_R3) : Prop :=
  ∀ (φ : R3 → ℂ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ∫ x, f x * fderiv ℝ φ x (EuclideanSpace.single i 1) =
    - ∫ x, g x * φ x

/-! ### Smooth, compactly supported test functions

Closure properties of `C_c^∞(ℝ³, ℂ)` under the operations that recur in
integration-by-parts arguments: complex conjugation, restriction to L², and
taking a partial derivative. -/

/-- Conjugation preserves smoothness (ℝ-smooth). -/
lemma contDiff_starRingEnd_comp {f : R3 → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun x => starRingEnd ℂ (f x)) :=
  ContDiff.continuousLinearMap_comp Complex.conjCLE.toContinuousLinearMap hf

/-- Conjugation preserves compact support (`star z = 0 ↔ z = 0`). -/
lemma hasCompactSupport_starRingEnd_comp {f : R3 → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun x => starRingEnd ℂ (f x)) :=
  hf.comp_left (map_zero (starRingEnd ℂ))

/-- Smooth compactly supported functions on ℝ³ belong to L². -/
lemma memLp_of_smooth_compactSupport (φ : R3 → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) :
    MemLp φ 2 (volume : Measure R3) := by
  have hcont := hφ.continuous
  haveI : IsFiniteMeasureOnCompacts (volume : Measure R3) := inferInstance
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hsupp
  exact hsupp.memLp_of_bound hcont.aestronglyMeasurable C (ae_of_all _ hC)

/-- Compact support of partial derivatives. -/
lemma hasCompactSupport_partialDeriv (φ : R3 → ℂ) (i : Fin 3)
    (hsupp : HasCompactSupport φ) :
    HasCompactSupport (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
  apply HasCompactSupport.mono (hsupp.fderiv ℝ)
  intro x hx
  exact fun h => hx (by simp [h, ContinuousLinearMap.zero_apply])

/-- Smoothness of partial derivatives. -/
lemma contDiff_partialDeriv (φ : R3 → ℂ) (i : Fin 3)
    (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
  (contDiff_infty_iff_fderiv.mp hφ).2.clm_apply contDiff_const

/-- Partial derivatives of smooth compactly supported functions are in L². -/
lemma memLp_partialDeriv (φ : R3 → ℂ) (i : Fin 3)
    (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) :
    MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) 2 volume :=
  memLp_of_smooth_compactSupport _ (contDiff_partialDeriv φ i hφ)
    (hasCompactSupport_partialDeriv φ i hsupp)

end Spectra.Sobolev
