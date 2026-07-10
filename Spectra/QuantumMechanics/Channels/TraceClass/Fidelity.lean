/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Channels.TraceClass.HilbertSchmidtNorm
import Spectra.QuantumMechanics.Channels.TraceClass.Cyclic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Stage I — the Uhlmann fidelity `F(ρ, σ) = ‖√ρ √σ‖₁`

The **Uhlmann–Jozsa fidelity** of two positive trace-class operators `ρ, σ` (states),
`F(ρ, σ) = ‖√ρ √σ‖₁`, and the elementary bounds that fall directly out of the sharp Schatten–Hölder
inequality (`HilbertSchmidtNorm.lean`):

  `F(ρ, σ) ≤ ‖√ρ‖₂ · ‖√σ‖₂ = √(tr ρ) · √(tr σ) = √(tr ρ · tr σ)`,

so for normalized states (`tr ρ = tr σ = 1`) one gets `F(ρ, σ) ≤ 1`, with `F(ρ, ρ) = tr ρ` (`= 1`).

The square-root factors `√ρ, √σ` are Hilbert–Schmidt exactly because `ρ, σ` are trace class, and
`‖√ρ‖₂ = √(tr ρ)` is definitional (`hsNorm` of `√ρ` is the positive trace of `ρ`).

## Main definitions

* `fidelity ρ σ` — the fidelity `‖√ρ √σ‖₁` (junk value off the positive operators).

## Main results

* `hsNorm_sqrtOp_of_nonneg` — `‖√ρ‖₂ = √(tr ρ)` for `0 ≤ ρ`.
* `fidelity_self` — `F(ρ, ρ) = tr ρ`.
* `fidelity_le_sqrt_mul` — **`F(ρ, σ) ≤ √(tr ρ · tr σ)`** (the Schatten–Hölder / Cauchy–Schwarz
  bound).
* `fidelity_le_one` — `F(ρ, σ) ≤ 1` for normalized states.

## Context

Realizes the information-geometric target I1 (fidelity / Bures) at the elementary level, on the
Hilbert–Schmidt norm and sharp Schatten–Hölder inequality.  The deep Uhlmann theorem
(`F = max |⟨ψ|φ⟩|` over purifications) and joint concavity / channel monotonicity are downstream.
-/

open ContinuousLinearMap RCLike
open scoped InnerProductSpace InnerProduct ENNReal NNReal

namespace Spectra.QuantumMechanics.Channels

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The Hilbert–Schmidt norm of a square root -/

/-- **`‖√ρ‖₂ = √(tr ρ)`** for a positive operator `ρ`.  Definitional: the Hilbert–Schmidt sum of
`√ρ` is `∑ᵢ ‖√ρ eᵢ‖² = ∑ᵢ ⟪eᵢ, ρ eᵢ⟫ = tr ρ` (the positive trace of `ρ`). -/
lemma hsNorm_sqrtOp_of_nonneg {ρ : H →L[ℂ] H} (hρ : 0 ≤ ρ) :
    hsNorm (sqrtOp ρ) = Real.sqrt (traceNorm ρ) := by
  rw [traceNorm_of_nonneg hρ (stdHilbertBasis H)]; rfl

/-- The square root of a positive trace-class operator is Hilbert–Schmidt. -/
lemma isHilbertSchmidt_sqrtOp_of_nonneg {ρ : H →L[ℂ] H} (hρ : 0 ≤ ρ) (hTC : IsTraceClass ρ) :
    IsHilbertSchmidt (sqrtOp ρ) := by
  have h := (isHilbertSchmidt_sqrtOp_absOp ρ).mpr hTC
  rwa [absOp_of_nonneg hρ] at h

/-! ## The trace norm is adjoint-invariant

`‖A⋆‖₁ = ‖A‖₁`, a general trace-class fact used for the symmetry of the fidelity.  Via the polar
decomposition `A = U |A|`, one has `|A⋆| = U |A| U⋆`, and cyclicity of the trace gives
`tr |A⋆| = tr(U |A| U⋆) = tr(|A| U⋆ U) = tr |A|`.  The non-trace-class case is `0 = 0`, using that
`A⋆` is trace class iff `A` is (the trace-class ideal applied to `|A⋆| = U |A| U⋆`). -/

/-- **`|A⋆| = U |A| U⋆`** for the polar isometry `U = polarIsometry A`.  Both sides are nonnegative
with square `A A⋆`, so they agree by uniqueness of the positive square root. -/
private lemma absOp_adjoint_eq (A : H →L[ℂ] H) :
    absOp (A†) = polarIsometry A ∘L absOp A ∘L (polarIsometry A)† := by
  have hAadj : A† = absOp A ∘L (polarIsometry A)† := by
    conv_lhs => rw [← polar_decomposition A]
    rw [ContinuousLinearMap.adjoint_comp, ← star_eq_adjoint, (absOp_isSelfAdjoint A).star_eq]
  have hAcomp : ∀ z : H, A z = polarIsometry A (absOp A z) := fun z => by
    rw [← ContinuousLinearMap.comp_apply, polar_decomposition A]
  -- `U⋆ (U |A| z) = |A| z`, since `U⋆ U` is the projection onto `closure (range |A|)`.
  have hPK : ∀ z : H, ((polarIsometry A)†) (polarIsometry A (absOp A z)) = absOp A z := fun z => by
    rw [← ContinuousLinearMap.comp_apply, polarIsometry_adjoint_comp_self A]
    exact Submodule.starProjection_eq_self_iff.2 (absOp_mem_polarRange A z)
  -- `0 ≤ U |A| U⋆` (conjugation of the nonnegative `|A|`).
  have hstar : star ((polarIsometry A)†) = polarIsometry A := by rw [← star_eq_adjoint, star_star]
  have hVnn : 0 ≤ polarIsometry A ∘L absOp A ∘L (polarIsometry A)† := by
    have h := star_left_conjugate_nonneg (absOp_nonneg A) ((polarIsometry A)†)
    rw [hstar, ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_assoc] at h
    exact h
  -- `(U |A| U⋆)² = A A⋆`.
  have hVV : (polarIsometry A ∘L absOp A ∘L (polarIsometry A)†)
      ∘L (polarIsometry A ∘L absOp A ∘L (polarIsometry A)†) = A ∘L A† := by
    ext x
    simp only [ContinuousLinearMap.comp_apply]
    rw [hPK, ← hAcomp, hAadj, ContinuousLinearMap.comp_apply]
  -- Uniqueness of the positive square root.
  have hsq : absOp (A†) * absOp (A†)
      = (polarIsometry A ∘L absOp A ∘L (polarIsometry A)†)
        * (polarIsometry A ∘L absOp A ∘L (polarIsometry A)†) := by
    rw [absOp_mul_absOp, star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, hVV]
  exact (CFC.mul_self_eq_mul_self_iff (absOp (A†)) _ (absOp_nonneg _) hVnn).mp hsq

/-- **`A⋆` is trace class iff `A` is.**  From `|A⋆| = U |A| U⋆` and the trace-class ideal. -/
lemma isTraceClass_adjoint (A : H →L[ℂ] H) : IsTraceClass (A†) ↔ IsTraceClass A := by
  have fwd : ∀ B : H →L[ℂ] H, IsTraceClass B → IsTraceClass (B†) := by
    intro B hB
    rw [← isTraceClass_absOp, absOp_adjoint_eq B]
    exact (((isTraceClass_absOp _).mpr hB).comp_right ((polarIsometry B)†)).comp_left
      (polarIsometry B)
  refine ⟨fun h => ?_, fwd A⟩
  have h2 := fwd (A†) h
  rwa [ContinuousLinearMap.adjoint_adjoint] at h2

/-- **The trace norm is adjoint-invariant:** `‖A⋆‖₁ = ‖A‖₁`. -/
@[simp] theorem traceNorm_adjoint (A : H →L[ℂ] H) : traceNorm (A†) = traceNorm A := by
  by_cases hA : IsTraceClass A
  · -- `tr |A⋆| = tr(U |A| U⋆) = tr(A U⋆) = tr(U⋆ A) = tr |A|` by cyclicity.
    have htr : trace (absOp (A†)) = trace (absOp A) := by
      rw [absOp_adjoint_eq A, ← ContinuousLinearMap.comp_assoc, polar_decomposition A,
        trace_comp_comm hA ((polarIsometry A)†), polarIsometry_adjoint_comp A]
    have hAdjTr := trace_of_nonneg (absOp_nonneg (A†)) (stdHilbertBasis H)
    have hATr := trace_of_nonneg (absOp_nonneg A) (stdHilbertBasis H)
    rw [hAdjTr, hATr, Complex.ofReal_inj] at htr
    rw [traceNorm_eq (stdHilbertBasis H) (A†), traceNorm_eq (stdHilbertBasis H) A]
    exact htr
  · -- Both are the junk value `0`, since `A⋆` is not trace class either.
    have h1 : posTrace (stdHilbertBasis H) (absOp (A†)) = ⊤ := by
      by_contra h; exact hA ((isTraceClass_adjoint A).mp h)
    have h2 : posTrace (stdHilbertBasis H) (absOp A) = ⊤ := by by_contra h; exact hA h
    change (posTrace (stdHilbertBasis H) (absOp (A†))).toReal
        = (posTrace (stdHilbertBasis H) (absOp A)).toReal
    rw [h1, h2]

/-! ## The fidelity and its elementary bounds -/

/-- The **Uhlmann–Jozsa fidelity** `F(ρ, σ) = ‖√ρ √σ‖₁` of two positive trace-class operators.
Total function (junk value off the positive operators, where `√·` is the
continuous-functional-calculus square root of a non-positive operator). -/
noncomputable def fidelity (ρ σ : H →L[ℂ] H) : ℝ := traceNorm (sqrtOp ρ ∘L sqrtOp σ)

/-- The fidelity is nonnegative. -/
lemma fidelity_nonneg (ρ σ : H →L[ℂ] H) : 0 ≤ fidelity ρ σ := traceNorm_nonneg _

/-- `√ρ √σ` is trace class (so `F(ρ, σ)` is the honest trace norm) for positive trace-class
`ρ, σ`. -/
lemma isTraceClass_sqrtOp_comp_sqrtOp {ρ σ : H →L[ℂ] H} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hTCρ : IsTraceClass ρ) (hTCσ : IsTraceClass σ) : IsTraceClass (sqrtOp ρ ∘L sqrtOp σ) :=
  (isHilbertSchmidt_sqrtOp_of_nonneg hρ hTCρ).isTraceClass_comp
    (isHilbertSchmidt_sqrtOp_of_nonneg hσ hTCσ)

/-- **`F(ρ, ρ) = tr ρ`.**  Since `√ρ √ρ = ρ` for `0 ≤ ρ`. -/
lemma fidelity_self {ρ : H →L[ℂ] H} (hρ : 0 ≤ ρ) : fidelity ρ ρ = traceNorm ρ := by
  change traceNorm (sqrtOp ρ ∘L sqrtOp ρ) = traceNorm ρ
  rw [← ContinuousLinearMap.mul_def, sqrtOp_mul_self ρ hρ]

/-- **The fidelity is symmetric:** `F(ρ, σ) = F(σ, ρ)`.  Since `(√σ √ρ)⋆ = √ρ √σ` (the square
roots are self-adjoint) and the trace norm is adjoint-invariant (`traceNorm_adjoint`). -/
lemma fidelity_comm (ρ σ : H →L[ℂ] H) : fidelity ρ σ = fidelity σ ρ := by
  have hcomp : (sqrtOp σ ∘L sqrtOp ρ)† = sqrtOp ρ ∘L sqrtOp σ := by
    rw [ContinuousLinearMap.adjoint_comp, ← star_eq_adjoint, ← star_eq_adjoint,
      (sqrtOp_isSelfAdjoint ρ).star_eq, (sqrtOp_isSelfAdjoint σ).star_eq]
  change traceNorm (sqrtOp ρ ∘L sqrtOp σ) = traceNorm (sqrtOp σ ∘L sqrtOp ρ)
  rw [← hcomp, traceNorm_adjoint]

/-- **The Schatten–Hölder / Cauchy–Schwarz bound on the fidelity:** `F(ρ, σ) ≤ √(tr ρ · tr σ)`.
Directly from `‖√ρ √σ‖₁ ≤ ‖√ρ‖₂ ‖√σ‖₂` (`traceNorm_comp_le`) and `‖√ρ‖₂ = √(tr ρ)`. -/
theorem fidelity_le_sqrt_mul {ρ σ : H →L[ℂ] H} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hTCρ : IsTraceClass ρ) (hTCσ : IsTraceClass σ) :
    fidelity ρ σ ≤ Real.sqrt (traceNorm ρ * traceNorm σ) := by
  change traceNorm (sqrtOp ρ ∘L sqrtOp σ) ≤ Real.sqrt (traceNorm ρ * traceNorm σ)
  calc traceNorm (sqrtOp ρ ∘L sqrtOp σ)
      ≤ hsNorm (sqrtOp ρ) * hsNorm (sqrtOp σ) :=
        traceNorm_comp_le (isHilbertSchmidt_sqrtOp_of_nonneg hρ hTCρ)
          (isHilbertSchmidt_sqrtOp_of_nonneg hσ hTCσ)
    _ = Real.sqrt (traceNorm ρ) * Real.sqrt (traceNorm σ) := by
        rw [hsNorm_sqrtOp_of_nonneg hρ, hsNorm_sqrtOp_of_nonneg hσ]
    _ = Real.sqrt (traceNorm ρ * traceNorm σ) := (Real.sqrt_mul (traceNorm_nonneg ρ) _).symm

/-- **`F(ρ, σ) ≤ 1`** for normalized states (`tr ρ = tr σ = 1`). -/
theorem fidelity_le_one {ρ σ : H →L[ℂ] H} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hTCρ : IsTraceClass ρ) (hTCσ : IsTraceClass σ) (hnρ : traceNorm ρ = 1)
    (hnσ : traceNorm σ = 1) :
    fidelity ρ σ ≤ 1 := by
  have h := fidelity_le_sqrt_mul hρ hσ hTCρ hTCσ
  rwa [hnρ, hnσ, mul_one, Real.sqrt_one] at h

end Spectra.QuantumMechanics.Channels
