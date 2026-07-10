/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.Bounded
/-!
# No canonical commutation relation for bounded operators (Wielandt–Wintner)

The classical fact that motivates unbounded operators in quantum mechanics: no pair of *bounded*
self-adjoint operators can satisfy the canonical commutation relation `[A, B] = i·1`. Physically,
position and momentum satisfy exactly this relation, so this theorem is precisely the statement
that they cannot both be represented by bounded operators — quantum mechanics *needs* the
unboundedness machinery of `Operator/Bounded.lean` to even state the CCR correctly.

## Main results

* `Operator.not_ccr_of_bounded` — **Wielandt–Wintner**: for `A B : H →L[ℂ] H` self-adjoint on a
  nontrivial complex Hilbert space, `A * B - B * A ≠ i • 1`.
* `Operator.not_ccr_of_isBounded` — the corollary for `SelfAdjointOperator`: if `A B` are both
  `IsBounded`, their bounded extensions can't satisfy the CCR either.

## Proof sketch

Assuming `A * B - B * A = i • 1`, induction gives `A * B^(n+1) - B^(n+1) * A = (n+1) * i • B^n`
for every `n`. If `B` is nilpotent, `B = 0` (a nilpotent self-adjoint operator is `0`, via
`IsSelfAdjoint.norm_pow_two_pow`), forcing `i • 1 = 0`, contradicting nontriviality. If `B` is not
nilpotent, taking norms turns the induction identity into `n + 1 ≤ 2‖A‖‖B‖` for *every* `n`,
contradicted by the Archimedean property.

## References

* H. Wielandt, "Über die Unbeschränktheit der Operatoren der Quantenmechanik" (1949).
* A. Wintner, "The unboundedness of quantum-mechanical matrices" (1947).
-/
open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.Operator

/-- **Wielandt–Wintner.** No pair of bounded self-adjoint operators on a nontrivial complex
Hilbert space satisfies the canonical commutation relation `A * B - B * A = i • 1`. -/
theorem not_ccr_of_bounded [Nontrivial H] {A B : H →L[ℂ] H} (_ : IsSelfAdjoint A)
    (hB : IsSelfAdjoint B) : A * B - B * A ≠ Complex.I • (1 : H →L[ℂ] H) := by
  intro hCCR
  have key : ∀ n : ℕ, A * B ^ (n + 1) - B ^ (n + 1) * A
      = (((n + 1 : ℕ) : ℂ) * Complex.I) • B ^ n := by
    intro n
    induction n with
    | zero => simpa using hCCR
    | succ n ih =>
      have hstep : A * B ^ (n + 1 + 1) - B ^ (n + 1 + 1) * A
          = (A * B ^ (n + 1) - B ^ (n + 1) * A) * B + B ^ (n + 1) * (A * B - B * A) := by
        rw [pow_succ B (n + 1)]; noncomm_ring
      rw [hstep, ih, hCCR, smul_mul_assoc, ← pow_succ, mul_smul_comm, mul_one, ← add_smul]
      congr 1
      push_cast
      ring
  by_cases hnil : ∃ k : ℕ, B ^ k = 0
  · obtain ⟨k, hk⟩ := hnil
    have hle : k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
    have hzero : B ^ (2 ^ k) = 0 := by
      rw [← Nat.add_sub_cancel' hle, pow_add, hk, zero_mul]
    have hBnorm : ‖B‖ ^ (2 ^ k) = 0 := by rw [← hB.norm_pow_two_pow k, hzero, norm_zero]
    have hB0 : B = 0 := by
      have hnorm0 : ‖B‖ = 0 := by
        by_contra hne
        have hpos : 0 < ‖B‖ := lt_of_le_of_ne (norm_nonneg B) (Ne.symm hne)
        have hposP : 0 < ‖B‖ ^ (2 ^ k) := pow_pos hpos _
        rw [hBnorm] at hposP
        exact lt_irrefl 0 hposP
      exact norm_eq_zero.mp hnorm0
    rw [hB0, mul_zero, zero_mul, sub_zero] at hCCR
    have h1 : (1 : H →L[ℂ] H) = 0 := by
      rcases smul_eq_zero.mp hCCR.symm with h | h
      · exact absurd h Complex.I_ne_zero
      · exact h
    exact one_ne_zero h1
  · push Not at hnil
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * ‖A‖ * ‖B‖)
    have hcontra := key N
    have hnorm1 : ‖(((N + 1 : ℕ) : ℂ) * Complex.I) • B ^ N‖ = ((N : ℝ) + 1) * ‖B ^ N‖ := by
      rw [norm_smul, norm_mul, Complex.norm_natCast, Complex.norm_I, mul_one]
      push_cast
      ring_nf
    rw [← hcontra] at hnorm1
    have hnormle : ((N : ℝ) + 1) * ‖B ^ N‖ ≤ 2 * ‖A‖ * ‖B‖ * ‖B ^ N‖ := by
      rw [← hnorm1]
      calc ‖A * B ^ (N + 1) - B ^ (N + 1) * A‖
          ≤ ‖A * B ^ (N + 1)‖ + ‖B ^ (N + 1) * A‖ := norm_sub_le _ _
        _ ≤ ‖A‖ * ‖B ^ (N + 1)‖ + ‖B ^ (N + 1)‖ * ‖A‖ :=
            add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ ‖A‖ * (‖B‖ * ‖B ^ N‖) + ‖B‖ * ‖B ^ N‖ * ‖A‖ := by
            have hBN1 : ‖B ^ (N + 1)‖ ≤ ‖B‖ * ‖B ^ N‖ := by
              rw [pow_succ']; exact norm_mul_le _ _
            gcongr
        _ = 2 * ‖A‖ * ‖B‖ * ‖B ^ N‖ := by ring
    have hBNpos : 0 < ‖B ^ N‖ := norm_pos_iff.mpr (hnil N)
    have hfinal : (N : ℝ) + 1 ≤ 2 * ‖A‖ * ‖B‖ := le_of_mul_le_mul_right hnormle hBNpos
    linarith

/-- The bounded-`SelfAdjointOperator` corollary: if `A B : SelfAdjointOperator H` are both
`IsBounded`, their `boundedExtension`s can't satisfy the canonical commutation relation either —
so any pair genuinely satisfying the CCR (like position and momentum) must include a genuinely
unbounded operator. -/
theorem not_ccr_of_isBounded [Nontrivial H] {A B : SelfAdjointOperator H}
    (hA : A.IsBounded) (hB : B.IsBounded) :
    A.boundedExtension hA * B.boundedExtension hB -
        B.boundedExtension hB * A.boundedExtension hA ≠ Complex.I • (1 : H →L[ℂ] H) :=
  not_ccr_of_bounded (A.isSelfAdjoint_boundedExtension hA) (B.isSelfAdjoint_boundedExtension hB)

end Spectra.Operator
