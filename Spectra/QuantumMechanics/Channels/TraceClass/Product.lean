/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Channels.TraceClass.HilbertSchmidt

/-!
# Stage G — Hilbert–Schmidt × Hilbert–Schmidt is trace class, and the trace-class ideal

The product of two Hilbert–Schmidt operators is **trace class**, and consequently the trace-class
operators form a **two-sided ideal** in `B(H)`.

The proof deliberately **avoids the sup-over-orthonormal-bases characterization** of the trace norm
(which `Spectra` does not have): writing `T = X ∘L Y` and using the polar-factor identity
`U⋆ T = |T|` (`polarIsometry_adjoint_comp`), the diagonal of `|T|` is
`⟪eᵢ, |T| eᵢ⟫ = ⟪U eᵢ, T eᵢ⟫ = ⟪X⋆ U eᵢ, Y eᵢ⟫`, so its real part is bounded by the
arithmetic–geometric estimate `re ⟪X⋆ U eᵢ, Y eᵢ⟫ ≤ ‖X⋆ U eᵢ‖² + ‖Y eᵢ‖²`.  Summing over the basis,

  `tr |T| = ∑ᵢ ⟪eᵢ, |T| eᵢ⟫ ≤ ∑ᵢ ‖X⋆ U eᵢ‖² + ∑ᵢ ‖Y eᵢ‖² < ∞`,

where `X⋆ U` is Hilbert–Schmidt because the Hilbert–Schmidt operators are a two-sided ideal
(`isHilbertSchmidt_adjoint` + `IsHilbertSchmidt.comp_right`).  This is *membership* in the trace
class (the qualitative Schatten–Hölder statement); the sharp norm bound `‖XY‖₁ ≤ ‖X‖₂ ‖Y‖₂` would in
addition require an `ℓ²`-Cauchy–Schwarz on the diagonal and a Hilbert–Schmidt norm.

## Main results

* `IsHilbertSchmidt.isTraceClass_comp` — **`X, Y` Hilbert–Schmidt ⟹ `X ∘L Y` trace class.**
* `IsTraceClass.comp_left` / `IsTraceClass.comp_right` — the trace class is a two-sided ideal:
  `B ∘L T` and `T ∘L B` are trace class for trace-class `T` and *bounded* `B`.

## Context

Seventh brick of the trace-class / von Neumann predual development (the discharge-first route to the
Tomita–Takesaki fundamental theorem), building on the Hilbert–Schmidt ideal (`HilbertSchmidt.lean`)
and the bounded polar decomposition (`PolarDecomp.lean`).  It unlocks the trace-class ideal, the
fidelity / Bures functional `‖√ρ √σ‖₁`, and the resolvent-integral BKM metric.
-/

open ContinuousLinearMap RCLike
open scoped InnerProductSpace InnerProduct ENNReal NNReal

namespace Spectra.QuantumMechanics.Channels

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- `(‖v‖₊ : ℝ≥0∞)² = ENNReal.ofReal (‖v‖²)`, bridging the Hilbert–Schmidt sum (in `‖·‖₊`) to the
positive-trace / real-valued sum (in `ENNReal.ofReal`). -/
lemma enorm_sq_eq_ofReal_norm_sq (v : H) :
    (‖v‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
  have h : (‖v‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖v‖ := by
    rw [show ‖v‖ = ((‖v‖₊ : ℝ≥0) : ℝ) from rfl, ENNReal.ofReal_coe_nnreal]
  rw [h, ← ENNReal.ofReal_pow (norm_nonneg v)]

/-- **Hilbert–Schmidt × Hilbert–Schmidt is trace class.**  If `X` and `Y` are Hilbert–Schmidt then
`X ∘L Y` is trace class.

Diagonal estimate (no sup-over-bases characterization): with `T = X ∘L Y` and polar factor
`U = polarIsometry T`, the identity `U⋆ T = |T|` gives
`⟪eᵢ, |T| eᵢ⟫ = ⟪X⋆ U eᵢ, Y eᵢ⟫`, hence `re ⟪eᵢ, |T| eᵢ⟫ ≤ ‖X⋆ U eᵢ‖² + ‖Y eᵢ‖²`.  Summing, the
positive trace of `|T|` is bounded by `‖X⋆ U‖₂² + ‖Y‖₂² < ∞`, with `X⋆ U` Hilbert–Schmidt by the
ideal property. -/
theorem IsHilbertSchmidt.isTraceClass_comp {X Y : H →L[ℂ] H}
    (hX : IsHilbertSchmidt X) (hY : IsHilbertSchmidt Y) : IsTraceClass (X ∘L Y) := by
  set e := stdHilbertBasis H with _he
  -- Diagonal identity `⟪eᵢ, |T| eᵢ⟫ = ⟪X⋆ U eᵢ, Y eᵢ⟫`, via `U⋆ T = |T|`.
  have hdiag : ∀ i, ⟪e i, absOp (X ∘L Y) (e i)⟫_ℂ
      = ⟪(X†) (polarIsometry (X ∘L Y) (e i)), Y (e i)⟫_ℂ := by
    intro i
    rw [← polarIsometry_adjoint_comp (X ∘L Y), ContinuousLinearMap.comp_apply,
      adjoint_inner_right, ContinuousLinearMap.comp_apply, ← adjoint_inner_left X]
  -- `X⋆ U` is Hilbert–Schmidt (the Hilbert–Schmidt operators are a two-sided ideal).
  have hXU : IsHilbertSchmidt ((X†) ∘L polarIsometry (X ∘L Y)) :=
    ((isHilbertSchmidt_adjoint X).mpr hX).comp_right (polarIsometry (X ∘L Y))
  -- Termwise arithmetic–geometric bound on the diagonal of `|T|`.
  have hterm : ∀ i, ENNReal.ofReal (re ⟪e i, absOp (X ∘L Y) (e i)⟫_ℂ)
      ≤ (‖((X†) ∘L polarIsometry (X ∘L Y)) (e i)‖₊ : ℝ≥0∞) ^ 2 + (‖Y (e i)‖₊ : ℝ≥0∞) ^ 2 := by
    intro i
    rw [enorm_sq_eq_ofReal_norm_sq, enorm_sq_eq_ofReal_norm_sq,
      ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rw [hdiag i, ContinuousLinearMap.comp_apply]
    set u := (X†) (polarIsometry (X ∘L Y) (e i))
    have h1 : re ⟪u, Y (e i)⟫_ℂ ≤ ‖⟪u, Y (e i)⟫_ℂ‖ := (le_abs_self _).trans (abs_re_le_norm _)
    have h2 : ‖⟪u, Y (e i)⟫_ℂ‖ ≤ ‖u‖ * ‖Y (e i)‖ := norm_inner_le_norm _ _
    nlinarith [sq_nonneg (‖u‖ - ‖Y (e i)‖), norm_nonneg u, norm_nonneg (Y (e i)), h1, h2]
  -- Sum: `tr |T| ≤ ‖X⋆ U‖₂² + ‖Y‖₂² ≠ ∞`.
  change posTrace e (absOp (X ∘L Y)) ≠ ⊤
  rw [posTrace_eq_tsum_ofReal e (absOp_nonneg (X ∘L Y))]
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
  rw [ENNReal.tsum_add]
  exact ENNReal.add_ne_top.mpr ⟨hXU, hY⟩

/-! ## The trace class is a two-sided ideal

For trace-class `T`, factor `T = (U |T|^{1/2}) ∘L |T|^{1/2}` into two Hilbert–Schmidt operators
(`|T|^{1/2}` is Hilbert–Schmidt iff `T` is trace class, and the Hilbert–Schmidt operators are a
two-sided ideal).  Then `B ∘L T` and `T ∘L B` are again products of two Hilbert–Schmidt operators,
hence trace class by `IsHilbertSchmidt.isTraceClass_comp`. -/

/-- **Left ideal:** `B ∘L T` is trace class when `T` is trace class and `B` is bounded. -/
theorem IsTraceClass.comp_left {T : H →L[ℂ] H} (hT : IsTraceClass T) (B : H →L[ℂ] H) :
    IsTraceClass (B ∘L T) := by
  set D := sqrtOp (absOp T) with hD
  have hDD : D ∘L D = absOp T := by
    rw [hD, ← ContinuousLinearMap.mul_def, sqrtOp_mul_self (absOp T) (absOp_nonneg T)]
  have hCD : (polarIsometry T ∘L D) ∘L D = T := by
    rw [ContinuousLinearMap.comp_assoc, hDD, polar_decomposition]
  have hD_hs : IsHilbertSchmidt D := (isHilbertSchmidt_sqrtOp_absOp T).mpr hT
  have hC_hs : IsHilbertSchmidt (polarIsometry T ∘L D) := hD_hs.comp_left (polarIsometry T)
  have hBT : B ∘L T = (B ∘L (polarIsometry T ∘L D)) ∘L D := by
    rw [ContinuousLinearMap.comp_assoc, hCD]
  rw [hBT]
  exact (hC_hs.comp_left B).isTraceClass_comp hD_hs

/-- **Right ideal:** `T ∘L B` is trace class when `T` is trace class and `B` is bounded. -/
theorem IsTraceClass.comp_right {T : H →L[ℂ] H} (hT : IsTraceClass T) (B : H →L[ℂ] H) :
    IsTraceClass (T ∘L B) := by
  set D := sqrtOp (absOp T) with hD
  have hDD : D ∘L D = absOp T := by
    rw [hD, ← ContinuousLinearMap.mul_def, sqrtOp_mul_self (absOp T) (absOp_nonneg T)]
  have hCD : (polarIsometry T ∘L D) ∘L D = T := by
    rw [ContinuousLinearMap.comp_assoc, hDD, polar_decomposition]
  have hD_hs : IsHilbertSchmidt D := (isHilbertSchmidt_sqrtOp_absOp T).mpr hT
  have hC_hs : IsHilbertSchmidt (polarIsometry T ∘L D) := hD_hs.comp_left (polarIsometry T)
  have hTB : T ∘L B = (polarIsometry T ∘L D) ∘L (D ∘L B) := by
    rw [← ContinuousLinearMap.comp_assoc, hCD]
  rw [hTB]
  exact hC_hs.isTraceClass_comp (hD_hs.comp_right B)

/-- **The fidelity / Bures substrate.**  For trace-class `ρ` and `σ`, the operator
`|ρ|^{1/2} ∘L |σ|^{1/2}` is trace class — for positive `ρ, σ` this is `√ρ √σ`, the operator inside
the Uhlmann fidelity `F(ρ, σ) = ‖√ρ √σ‖₁`.  Each square-root factor is Hilbert–Schmidt exactly
because its argument is trace class (`isHilbertSchmidt_sqrtOp_absOp`), so the product is trace class
by `IsHilbertSchmidt.isTraceClass_comp`. -/
theorem isTraceClass_sqrtOp_absOp_comp {ρ σ : H →L[ℂ] H}
    (hρ : IsTraceClass ρ) (hσ : IsTraceClass σ) :
    IsTraceClass (sqrtOp (absOp ρ) ∘L sqrtOp (absOp σ)) :=
  ((isHilbertSchmidt_sqrtOp_absOp ρ).mpr hρ).isTraceClass_comp
    ((isHilbertSchmidt_sqrtOp_absOp σ).mpr hσ)

end Spectra.QuantumMechanics.Channels
