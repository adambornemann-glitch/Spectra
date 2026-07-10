/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Channels.TraceClass.Product
import Spectra.QuantumMechanics.Channels.TraceClass.Cyclic
import Spectra.InformationGeometry.Quantum.State
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# G4a — the Bogoliubov–Kubo–Mori (BKM) metric: the object and its well-definedness

The **Bogoliubov–Kubo–Mori metric** at a faithful state `ρ` is the monotone Riemannian metric

  `g^BKM_ρ(A, B) = ∫₀^∞ tr(A (ρ + s)⁻¹ B (ρ + s)⁻¹) ds`

on the (trace-class, self-adjoint) tangent operators `A, B`.  It is the Hessian of the quantum
relative entropy `D(ρ‖σ)` and the smallest monotone metric — the crown of the information-geometric
"second view" of the Petz recovery map.

This file builds the **object and its algebraic well-definedness**, the part that requires no
operator differentiation.  The full identity `g^BKM = Hessian(D)` needs a derivative-of-CFC /
resolvent integral-representation theory that is a separate (much larger) undertaking; here we
land the metric as a genuine, kernel-checked object.

For a strictly-positive operator `τ` (in the application `τ = ρ + s`, so `τ⁻¹` is bounded) and
trace-class `A, B`, the **BKM integrand kernel** `K_τ(A,B) = tr(A τ⁻¹ B τ⁻¹)` is:

* **well-defined** — the argument `A τ⁻¹ B τ⁻¹` is trace class (`A` trace class, the rest bounded),
  so the trace is honest (`IsHilbertSchmidt.isTraceClass_comp`-era trace-class *ideal*);
* **bilinear** in `A, B` (linearity of the trace);
* **symmetric** `K_τ(A,B) = K_τ(B,A)` — a single cyclicity step,
  `tr((Aτ⁻¹)(Bτ⁻¹)) = tr((Bτ⁻¹)(Aτ⁻¹))`;
* **positive semidefinite** `0 ≤ re K_τ(A,A)` for self-adjoint `A` — since
  `tr(A τ⁻¹ A τ⁻¹) = tr(C⋆ C)` with `C = τ^{-1/2} A τ^{-1/2}` self-adjoint.

The metric `bkmMetric ρ A B = ∫_{s>0} re K_{ρ+s}(A,B) ds` inherits symmetry (pointwise) and positive
semidefiniteness (`integral_nonneg`, robust to non-integrability, which returns the junk value `0`).

## Main definitions

* `bkmKernel τ A B` — the integrand `tr(A τ⁻¹ B τ⁻¹)`.
* `bkmMetric ρ A B` — `∫_{s>0} re K_{ρ+s}(A,B) ds`.

## Main results

* `bkmKernel_isTraceClass`, `bkmKernel_add_left`/`_right`, `bkmKernel_smul_left`, `bkmKernel_comm`,
  `bkmKernel_self_re_nonneg` — the kernel is a symmetric positive-semidefinite bilinear form.
* `bkmMetric_comm`, `bkmMetric_self_nonneg` — the metric is symmetric and positive semidefinite.
-/

open ContinuousLinearMap RCLike MeasureTheory
open scoped InnerProductSpace ENNReal NNReal

namespace Spectra.InformationGeometry.Quantum

open Spectra.QuantumMechanics.Channels

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The BKM integrand kernel -/

/-- The **BKM integrand kernel** `K_τ(A,B) = tr(A τ⁻¹ B τ⁻¹)` (with `τ⁻¹ = Ring.inverse τ`). -/
noncomputable def bkmKernel (τ A B : H →L[ℂ] H) : ℂ :=
  trace (A ∘L Ring.inverse τ ∘L B ∘L Ring.inverse τ)

/-- The kernel's argument `A τ⁻¹ B τ⁻¹` is trace class when `A` is (the rest is bounded). -/
lemma bkmKernel_isTraceClass (τ B : H →L[ℂ] H) {A : H →L[ℂ] H} (hA : IsTraceClass A) :
    IsTraceClass (A ∘L Ring.inverse τ ∘L B ∘L Ring.inverse τ) :=
  IsTraceClass.comp_right hA _

/-! ### Bilinearity -/

lemma bkmKernel_add_left (τ B : H →L[ℂ] H) {A₁ A₂ : H →L[ℂ] H}
    (hA₁ : IsTraceClass A₁) (hA₂ : IsTraceClass A₂) :
    bkmKernel τ (A₁ + A₂) B = bkmKernel τ A₁ B + bkmKernel τ A₂ B := by
  simp only [bkmKernel, ContinuousLinearMap.add_comp]
  exact trace_add (IsTraceClass.comp_right hA₁ _) (IsTraceClass.comp_right hA₂ _)

lemma bkmKernel_smul_left (τ B : H →L[ℂ] H) (c : ℂ) (A : H →L[ℂ] H) :
    bkmKernel τ (c • A) B = c * bkmKernel τ A B := by
  simp only [bkmKernel, ContinuousLinearMap.smul_comp, trace_smul]

lemma bkmKernel_add_right (τ : H →L[ℂ] H) {A : H →L[ℂ] H} (hA : IsTraceClass A)
    (B₁ B₂ : H →L[ℂ] H) :
    bkmKernel τ A (B₁ + B₂) = bkmKernel τ A B₁ + bkmKernel τ A B₂ := by
  simp only [bkmKernel, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  exact trace_add (IsTraceClass.comp_right hA _) (IsTraceClass.comp_right hA _)

/-! ### Symmetry -/

/-- **Symmetry** `K_τ(A,B) = K_τ(B,A)`, a single cyclicity step
`tr((A τ⁻¹)(B τ⁻¹)) = tr((B τ⁻¹)(A τ⁻¹))`. -/
lemma bkmKernel_comm (τ B : H →L[ℂ] H) {A : H →L[ℂ] H} (hA : IsTraceClass A) :
    bkmKernel τ A B = bkmKernel τ B A := by
  change trace (A ∘L Ring.inverse τ ∘L B ∘L Ring.inverse τ)
      = trace (B ∘L Ring.inverse τ ∘L A ∘L Ring.inverse τ)
  rw [← ContinuousLinearMap.comp_assoc A, ← ContinuousLinearMap.comp_assoc B,
    trace_comp_comm (IsTraceClass.comp_right hA (Ring.inverse τ)) (B ∘L Ring.inverse τ)]

/-! ### Positive semidefiniteness -/

/-- For a strictly positive `τ`, the resolvent `τ⁻¹` is self-adjoint. -/
lemma isSelfAdjoint_ringInverse {τ : H →L[ℂ] H} (hτ : IsStrictlyPositive τ) :
    IsSelfAdjoint (Ring.inverse τ) := by
  rw [IsSelfAdjoint, ← Ring.inverse_star, hτ.isSelfAdjoint.star_eq]

/-- For a strictly positive `τ`, the resolvent `τ⁻¹` is nonnegative. -/
lemma ringInverse_nonneg {τ : H →L[ℂ] H} (hτ : IsStrictlyPositive τ) :
    (0 : H →L[ℂ] H) ≤ Ring.inverse τ := by
  rw [Ring.inverse_of_isUnit hτ.isUnit]
  exact (CFC.inv_nonneg _).mpr hτ.nonneg

/-- **Positive semidefiniteness** `0 ≤ re K_τ(A,A)` for self-adjoint `A` and strictly positive `τ`.
Since `tr(A τ⁻¹ A τ⁻¹) = tr(C⋆ C)` with `C = τ^{-1/2} A τ^{-1/2}` self-adjoint, and the trace of a
positive operator has nonnegative real part. -/
lemma bkmKernel_self_re_nonneg {τ A : H →L[ℂ] H} (hτ : IsStrictlyPositive τ)
    (hA : IsTraceClass A) (hAsa : IsSelfAdjoint A) : 0 ≤ (bkmKernel τ A A).re := by
  have hRnn : (0 : H →L[ℂ] H) ≤ Ring.inverse τ := ringInverse_nonneg hτ
  -- `T = τ^{-1/2}`, kept opaque so `Ring.inverse τ` never appears inside it.
  set T := sqrtOp (Ring.inverse τ) with hTdef
  have hTsa : IsSelfAdjoint T := sqrtOp_isSelfAdjoint _
  have hTT : T ∘L T = Ring.inverse τ := by
    rw [hTdef, ← ContinuousLinearMap.mul_def, sqrtOp_mul_self _ hRnn]
  -- `C = T A T` is self-adjoint.
  have hCsa : ContinuousLinearMap.adjoint (T ∘L A ∘L T) = T ∘L A ∘L T := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      ← star_eq_adjoint, ← star_eq_adjoint, hAsa.star_eq, hTsa.star_eq,
      ContinuousLinearMap.comp_assoc]
  -- `bkmKernel τ A A = tr((T A T)(T A T))` by one cyclicity step.
  have hATTAT : IsTraceClass (A ∘L T ∘L T ∘L A ∘L T) := IsTraceClass.comp_right hA _
  have hassoc₁ : A ∘L (T ∘L T) ∘L A ∘L (T ∘L T) = (A ∘L T ∘L T ∘L A ∘L T) ∘L T := by
    simp only [ContinuousLinearMap.comp_assoc]
  have hassoc₂ : T ∘L (A ∘L T ∘L T ∘L A ∘L T) = (T ∘L A ∘L T) ∘L (T ∘L A ∘L T) := by
    simp only [ContinuousLinearMap.comp_assoc]
  have hkey : bkmKernel τ A A = trace ((T ∘L A ∘L T) ∘L (T ∘L A ∘L T)) := by
    change trace (A ∘L Ring.inverse τ ∘L A ∘L Ring.inverse τ)
        = trace ((T ∘L A ∘L T) ∘L (T ∘L A ∘L T))
    rw [← hTT, hassoc₁, trace_comp_comm hATTAT T, hassoc₂]
  rw [hkey]
  -- `tr((T A T)⋆ (T A T))` is the trace of a positive operator.
  have hpos : (0 : H →L[ℂ] H) ≤ ContinuousLinearMap.adjoint (T ∘L A ∘L T) ∘L (T ∘L A ∘L T) := by
    rw [← star_eq_adjoint, ← ContinuousLinearMap.mul_def]; exact star_mul_self_nonneg _
  have htr := trace_of_nonneg hpos (stdHilbertBasis H)
  rw [hCsa] at htr
  rw [htr, Complex.ofReal_re]
  exact ENNReal.toReal_nonneg

/-! ## The BKM metric -/

/-- The **BKM metric** `g^BKM_ρ(A,B) = ∫_{s>0} re tr(A (ρ+s)⁻¹ B (ρ+s)⁻¹) ds`.  The shift `ρ + s`
is strictly positive for `s > 0`, so `(ρ+s)⁻¹` is a genuine bounded resolvent. -/
noncomputable def bkmMetric (ρ : QState H) (A B : H →L[ℂ] H) : ℝ :=
  ∫ s in Set.Ioi (0 : ℝ),
    (bkmKernel (ρ.toOp + algebraMap ℝ (H →L[ℂ] H) s) A B).re

/-- For a state `ρ` and `s > 0`, the shift `ρ + s` is strictly positive. -/
lemma isStrictlyPositive_shift (ρ : QState H) {s : ℝ} (hs : 0 < s) :
    IsStrictlyPositive (ρ.toOp + algebraMap ℝ (H →L[ℂ] H) s) :=
  IsStrictlyPositive.nonneg_add ρ.toOp_nonneg (isStrictlyPositive_algebraMap hs)

/-- **The BKM metric is symmetric.** -/
lemma bkmMetric_comm (ρ : QState H) {A : H →L[ℂ] H} (hA : IsTraceClass A) (B : H →L[ℂ] H) :
    bkmMetric ρ A B = bkmMetric ρ B A := by
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [bkmKernel_comm _ _ hA]

/-- **The BKM metric is positive semidefinite** `0 ≤ g^BKM_ρ(A,A)` for self-adjoint trace-class `A`.
(Robust to non-integrability: the integral is then the junk value `0 ≥ 0`.) -/
lemma bkmMetric_self_nonneg (ρ : QState H) {A : H →L[ℂ] H} (hA : IsTraceClass A)
    (hAsa : IsSelfAdjoint A) : 0 ≤ bkmMetric ρ A A := by
  refine setIntegral_nonneg measurableSet_Ioi fun s hs => ?_
  exact bkmKernel_self_re_nonneg (isStrictlyPositive_shift ρ hs) hA hAsa

end Spectra.InformationGeometry.Quantum
