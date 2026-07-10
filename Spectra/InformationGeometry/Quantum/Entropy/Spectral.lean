/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Quantum.Eigenbasis
import Spectra.InformationGeometry.Quantum.CfcEigen
import Spectra.InformationGeometry.Quantum.Entropy.VonNeumann
import Spectra.QuantumMechanics.Channels.TraceClass.Compact

/-!
# The spectral form of the von Neumann entropy

The keystone payoff: a quantum state `ρ : QState H` is a positive trace-class operator, hence
**compact** (`QState.isCompactOperator_toOp`), so Mathlib's compact self-adjoint spectral theorem —
assembled into a genuine `HilbertBasis` of eigenvectors in `Eigenbasis.lean` — applies.  This file
attaches that eigenbasis to `ρ`, establishes that the eigenvalues form a probability distribution
(`0 ≤ λᵢ ≤ 1`, `∑ᵢ λᵢ = 1`), and proves the **spectral form** of the von Neumann entropy:
`S(ρ) = ∑ᵢ negMulLog λᵢ = -∑ᵢ λᵢ log λᵢ`.

This closes the loop opened in `VonNeumann.lean`, where `S(ρ) = tr(-ρ log ρ)` was *defined*
operator-theoretically and the eigenvalue-sum form was deferred pending exactly this eigenbasis.

## Main results

* `QState.eigenvalue_nonneg` / `QState.eigenvalue_le_one` — `0 ≤ λᵢ ≤ 1`.
* `QState.hasSum_eigenvalue` — `∑ᵢ λᵢ = 1` (the eigenvalues are a probability distribution).
* `QState.vonNeumannEntropy_eq_tsum` — **`S(ρ) = ∑ᵢ negMulLog λᵢ`**, the spectral form.
-/

open Spectra.QuantumMechanics.Channels RCLike
open scoped InnerProductSpace ENNReal NNReal

namespace Spectra.InformationGeometry.Quantum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace QState

/-! ## The eigenbasis of a quantum state -/

/-- A quantum state's operator is self-adjoint. -/
lemma isSelfAdjoint_toOp (ρ : QState H) : IsSelfAdjoint ρ.toOp := ρ.nonneg.isSelfAdjoint

/-- A quantum state's operator is **compact**: it is positive and trace-class. -/
lemma isCompactOperator_toOp (ρ : QState H) : IsCompactOperator ρ.toOp :=
  IsTraceClass.isCompactOperator ρ.isTraceClass

/-- The **eigenbasis** of a quantum state: an orthonormal `HilbertBasis` of eigenvectors of `ρ`. -/
noncomputable def eigenbasis (ρ : QState H) : HilbertBasis (eigenIndex ρ.toOp) ℂ H :=
  Quantum.eigenbasis ρ.toOp ρ.isSelfAdjoint_toOp ρ.isCompactOperator_toOp

/-- The **eigenvalue** attached to each eigenbasis vector, a real number. -/
noncomputable def eigenvalue (ρ : QState H) : eigenIndex ρ.toOp → ℝ :=
  Quantum.eigenvalue ρ.toOp ρ.isSelfAdjoint_toOp ρ.isCompactOperator_toOp

lemma apply_eigenbasis (ρ : QState H) (i : eigenIndex ρ.toOp) :
    ρ.toOp (ρ.eigenbasis i) = (ρ.eigenvalue i : ℂ) • ρ.eigenbasis i :=
  Quantum.apply_eigenbasis ρ.toOp _ _ i

lemma inner_eigenbasis_self (ρ : QState H) (i : eigenIndex ρ.toOp) :
    ⟪ρ.eigenbasis i, ρ.toOp (ρ.eigenbasis i)⟫_ℂ = (ρ.eigenvalue i : ℂ) :=
  Quantum.inner_eigenbasis_self ρ.toOp _ _ i

lemma inner_eigenbasis_self_eq_one (ρ : QState H) (i : eigenIndex ρ.toOp) :
    ⟪ρ.eigenbasis i, ρ.eigenbasis i⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, ρ.eigenbasis.orthonormal.1 i]
  norm_num

lemma eigenbasis_ne_zero (ρ : QState H) (i : eigenIndex ρ.toOp) : ρ.eigenbasis i ≠ 0 := by
  intro h
  have hh := ρ.inner_eigenbasis_self_eq_one i
  rw [h, inner_zero_right] at hh
  exact one_ne_zero hh.symm

/-! ## The eigenvalues form a probability distribution -/

/-- Each eigenvalue of a quantum state is nonnegative. -/
lemma eigenvalue_nonneg (ρ : QState H) (i : eigenIndex ρ.toOp) : 0 ≤ ρ.eigenvalue i := by
  have hpos := (ContinuousLinearMap.nonneg_iff_isPositive ρ.toOp).mp ρ.toOp_nonneg
  have h := hpos.re_inner_nonneg_right (ρ.eigenbasis i)
  rw [ρ.inner_eigenbasis_self i] at h
  simpa using h

/-- Each eigenvalue lies in the real spectrum of `ρ.toOp` (it is a genuine eigenvalue). -/
lemma eigenvalue_mem_spectrum (ρ : QState H) (i : eigenIndex ρ.toOp) :
    ρ.eigenvalue i ∈ spectrum ℝ ρ.toOp := by
  rw [spectrum.mem_iff]
  intro hunit
  obtain ⟨u, hu⟩ := hunit
  have halg : (algebraMap ℝ (H →L[ℂ] H) (ρ.eigenvalue i))
      = (ρ.eigenvalue i : ℂ) • (1 : H →L[ℂ] H) := by
    rw [IsScalarTower.algebraMap_apply ℝ ℂ (H →L[ℂ] H), Algebra.algebraMap_eq_smul_one]
    simp
  have hker : (algebraMap ℝ (H →L[ℂ] H) (ρ.eigenvalue i) - ρ.toOp) (ρ.eigenbasis i) = 0 := by
    rw [ContinuousLinearMap.sub_apply, halg, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, ρ.apply_eigenbasis i, sub_self]
  rw [← hu] at hker
  have hinv : (↑u⁻¹ : H →L[ℂ] H) ∘L (↑u : H →L[ℂ] H) = 1 := by
    rw [← ContinuousLinearMap.mul_def]; exact_mod_cast u.inv_mul
  have h2 : ρ.eigenbasis i = 0 := by
    have := congrArg (↑u⁻¹ : H →L[ℂ] H) hker
    rwa [map_zero, ← ContinuousLinearMap.comp_apply, hinv,
      ContinuousLinearMap.one_apply] at this
  exact ρ.eigenbasis_ne_zero i h2

/-- The eigenvalues of a quantum state **sum to `1`**: they form a probability distribution.  This
is `Tr ρ = 1` read off in the eigenbasis. -/
lemma hasSum_eigenvalue (ρ : QState H) : HasSum ρ.eigenvalue 1 := by
  have htr : ((posTrace ρ.eigenbasis ρ.toOp).toReal : ℂ) = 1 := by
    rw [← trace_of_nonneg ρ.toOp_nonneg ρ.eigenbasis]; exact ρ.trace_toOp
  have htrR : (posTrace ρ.eigenbasis ρ.toOp).toReal = 1 := by exact_mod_cast htr
  have hne : posTrace ρ.eigenbasis ρ.toOp ≠ ⊤ := by
    intro h; rw [h, ENNReal.toReal_top] at htrR; exact zero_ne_one htrR
  have hpt1 : posTrace ρ.eigenbasis ρ.toOp = 1 := by
    rw [← ENNReal.ofReal_toReal hne, htrR, ENNReal.ofReal_one]
  have hsum_enn : ∑' i, ENNReal.ofReal (ρ.eigenvalue i) = 1 := by
    rw [← hpt1, posTrace_eq_tsum_ofReal ρ.eigenbasis ρ.toOp_nonneg]
    refine tsum_congr fun i => ?_
    rw [ρ.inner_eigenbasis_self i]; simp
  have hnn := ρ.eigenvalue_nonneg
  have heq : (fun i => ((ρ.eigenvalue i).toNNReal : ℝ≥0∞))
      = fun i => ENNReal.ofReal (ρ.eigenvalue i) := rfl
  have hsummable_nn : Summable (fun i => (ρ.eigenvalue i).toNNReal) := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable, heq, hsum_enn]; exact ENNReal.one_ne_top
  have hsummable : Summable ρ.eigenvalue :=
    (NNReal.summable_coe.mpr hsummable_nn).congr fun i => Real.coe_toNNReal _ (hnn i)
  have htsum : ∑' i, ρ.eigenvalue i = 1 := by
    have h1 : (↑(∑' i, (ρ.eigenvalue i).toNNReal) : ℝ≥0∞) = 1 := by
      rw [ENNReal.coe_tsum hsummable_nn, heq, hsum_enn]
    have h2 : (∑' i, (ρ.eigenvalue i).toNNReal) = 1 := by exact_mod_cast h1
    calc ∑' i, ρ.eigenvalue i = ∑' i, ((ρ.eigenvalue i).toNNReal : ℝ) :=
          tsum_congr fun i => (Real.coe_toNNReal _ (hnn i)).symm
      _ = ((∑' i, (ρ.eigenvalue i).toNNReal : ℝ≥0) : ℝ) := NNReal.coe_tsum.symm
      _ = 1 := by rw [h2, NNReal.coe_one]
  exact htsum ▸ hsummable.hasSum

/-- Each eigenvalue is at most `1` (nonnegativity + summing to `1`). -/
lemma eigenvalue_le_one (ρ : QState H) (i : eigenIndex ρ.toOp) : ρ.eigenvalue i ≤ 1 := by
  have h := ρ.hasSum_eigenvalue
  calc ρ.eigenvalue i ≤ ∑' j, ρ.eigenvalue j :=
        h.summable.le_tsum i (fun j _ => ρ.eigenvalue_nonneg j)
    _ = 1 := h.tsum_eq

/-! ## The spectral form of the von Neumann entropy -/

/-- **The spectral form of the von Neumann entropy.**  `S(ρ) = ∑ᵢ negMulLog λᵢ = -∑ᵢ λᵢ log λᵢ`,
the Shannon entropy of `ρ`'s eigenvalue distribution.  This is where the operator definition
`tr(-ρ log ρ)` of `vonNeumannEntropy` meets the classical eigenvalue-sum picture. -/
theorem vonNeumannEntropy_eq_tsum (ρ : QState H) :
    vonNeumannEntropy ρ = ∑' i, ENNReal.ofReal (Real.negMulLog (ρ.eigenvalue i)) := by
  rw [← vonNeumannEntropy_indep ρ.eigenbasis ρ,
    posTrace_eq_tsum_ofReal ρ.eigenbasis (entropyOp_nonneg ρ)]
  refine tsum_congr fun i => ?_
  congr 1
  have hinner : ⟪ρ.eigenbasis i, entropyOp ρ (ρ.eigenbasis i)⟫_ℂ
      = (Real.negMulLog (ρ.eigenvalue i) : ℂ) * ⟪ρ.eigenbasis i, ρ.eigenbasis i⟫_ℂ := by
    rw [entropyOp]
    exact inner_cfc_eigenvector ρ.isSelfAdjoint_toOp (ρ.apply_eigenbasis i)
      (ρ.eigenvalue_mem_spectrum i) Real.continuous_negMulLog.continuousOn
  rw [hinner, ρ.inner_eigenbasis_self_eq_one i, mul_one]; simp

end QState

end Spectra.InformationGeometry.Quantum
