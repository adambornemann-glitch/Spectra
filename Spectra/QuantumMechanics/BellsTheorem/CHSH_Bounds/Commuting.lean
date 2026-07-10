/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ported from Isabelle/HOL formalization by Echenim & Mhalla, by Adam Bornemann
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Star.CHSH
import Spectra.QuantumMechanics.BellsTheorem.CHSH_Bounds.CHSH_Basic
import Spectra.QuantumMechanics.BellsTheorem.CHSH_Bounds.Op_square
/-!
# Commuting Observables Cannot Violate CHSH

If either Alice's pair `A₀, A₁` or Bob's pair `B₀, B₁` commutes (`IsCHSHTuple` alone only supplies
the four *cross*-commutators, not this), the CHSH operator squares to `4I` exactly (no commutator
correction term), so `S/2` is an involution and the dichotomic bound applies directly.

## Main results

* `CHSH_commuting_bound` : `‖chshExpect A₀ A₁ B₀ B₁ ρ‖ ≤ 2` whenever `[A₀,A₁] = 0 ∨ [B₀,B₁] = 0`

## References

* [Echenim, Mhalla, *A formalization of the CHSH inequality and Tsirelson's
  upper-bound in Isabelle/HOL*][echenim2023]

## Tags

chsh, commuting observables, quantum information
-/
open Matrix Complex

namespace Spectra.QuantumInfo

/-- **Commuting observables cannot violate CHSH**: if either `[A₀,A₁] = 0` or `[B₀,B₁] = 0`, the
CHSH expectation is bounded by `2`, the same as the classical (LHV) bound — no `2√2` Tsirelson
violation is possible. Either commutation hypothesis kills the `[A₀,A₁]·[B₀,B₁]` correction term
in `CHSH_op_square`, leaving `S² = 4I`, so `S/2` is a Hermitian involution and
`dichotomic_expectation_bound` applies directly. -/
lemma CHSH_commuting_bound {n : ℕ} [NeZero n]
    (A₀ A₁ B₀ B₁ : Matrix (Fin n) (Fin n) ℂ) (ρ : DensityMatrix n)
    (hT : IsCHSHTuple A₀ A₁ B₀ B₁)
    (hcomm : (A₀ * A₁ = A₁ * A₀) ∨ (B₀ * B₁ = B₁ * B₀)) :
    ‖(chshExpect A₀ A₁ B₀ B₁ ρ.toMatrix)‖ ≤ 2 := by
  -- When [A₀,A₁]=0 or [B₀,B₁]=0, the commutator product vanishes
  have h_comm_zero : ⁅A₀, A₁⁆ * ⁅B₀, B₁⁆ = 0 := by
    rcases hcomm with hA | hB
    · -- [A₀, A₁] = 0
      simp only [Ring.lie_def]
      simp only [hA, sub_self, Matrix.zero_mul]
    · -- [B₀, B₁] = 0
      simp only [Ring.lie_def]
      simp only [hB, sub_self, Matrix.mul_zero]
  -- So S² = 4I
  have h_sq : chshOp A₀ A₁ B₀ B₁ * chshOp A₀ A₁ B₀ B₁ = 4 • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [CHSH_op_square A₀ A₁ B₀ B₁ hT, h_comm_zero, sub_zero]
  -- Let S' = S/2, then S'² = I
  let S := chshOp A₀ A₁ B₀ B₁
  let S' := (1/2 : ℂ) • S
  have h_S'_sq : S' * S' = 1 := by
    simp only [S', Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [h_sq]
    module
  -- S' is Hermitian (CHSH operator is Hermitian)
  have h_S_herm : S.IsHermitian := by
    change (chshOp A₀ A₁ B₀ B₁).IsHermitian
    simp only [chshOp]
    simp only [Matrix.IsHermitian]
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_add, Matrix.conjTranspose_sub]
    simp only [Matrix.conjTranspose_mul]
    have hA₀ : A₀ᴴ = A₀ := hT.A₀_sa
    have hA₁ : A₁ᴴ = A₁ := hT.A₁_sa
    have hB₀ : B₀ᴴ = B₀ := hT.B₀_sa
    have hB₁ : B₁ᴴ = B₁ := hT.B₁_sa
    rw [hA₀, hA₁, hB₀, hB₁]
    rw [hT.A₀B₁_commutes, hT.A₀B₀_commutes, hT.A₁B₀_commutes, hT.A₁B₁_commutes]
  have h_S'_herm : S'.IsHermitian := by
    simp only [S', Matrix.IsHermitian]
    rw [Matrix.conjTranspose_smul, h_S_herm.eq]
    congr 1
    simp only [one_div, star_inv₀, star_ofNat]
  -- Apply dichotomic bound to S'
  have h_bound := dichotomic_expectation_bound S' h_S'_herm h_S'_sq ρ
  -- Relate back to S
  simp only [chshExpect]
  calc ‖(S * ρ.toMatrix).trace‖
      = ‖((2 : ℂ) • S' * ρ.toMatrix).trace‖ := by simp [S']
    _ = ‖(2 : ℂ) • (S' * ρ.toMatrix).trace‖ := by rw [Matrix.smul_mul, Matrix.trace_smul]
    _ = ‖(2 : ℂ)‖ * ‖(S' * ρ.toMatrix).trace‖ := norm_smul _ _
    _ ≤ 2 * 1 := by
        apply mul_le_mul _ h_bound (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
        norm_num
    _ = 2 := by ring

end Spectra.QuantumInfo
