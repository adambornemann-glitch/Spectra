/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Quantum.Entropy.Diagonal
import Spectra.InformationGeometry.Quantum.KleinScalar

/-!
# The Gibbs (commuting-case Klein) inequality

The classical core of Klein's inequality for the quantum relative entropy: for two states
`ρ σ : QState H` with `σ` faithful, the von Neumann entropy `S(ρ)` is bounded by the **measured
cross entropy** `∑ᵢ -λᵢ log sᵢ`, where `λᵢ` are `ρ`'s eigenvalues and `sᵢ = ⟪eᵢ, σ eᵢ⟫` is `σ`'s
diagonal in `ρ`'s eigenbasis.  Equivalently, the classical Kullback–Leibler divergence
`∑ᵢ λᵢ log(λᵢ/sᵢ) ≥ 0` between `ρ`'s eigenvalue distribution and `σ`'s dephased diagonal — Gibbs'
inequality, which is Klein's inequality for the pair `(ρ, D_ρ(σ))` of operators that commute in
`ρ`'s eigenbasis.

The inequality is **not** termwise: it holds only after summation, via the scalar Klein inequality
`λᵢ log(λᵢ/sᵢ) ≥ λᵢ − sᵢ` and the global cancellation `∑ᵢ (λᵢ − sᵢ) = Tr ρ − Tr σ = 0`.  Working in
`ℝ≥0∞` with the subtraction-free statement `S(ρ) ≤ measuredCrossEntropy` sidesteps the `∞ − ∞`
hazard entirely.

## Main results

* `QState.measuredCrossEntropy` — `∑ᵢ -λᵢ log sᵢ` in `ℝ≥0∞`.
* `QState.vonNeumannEntropy_le_measuredCrossEntropy` — **Gibbs' inequality** `S(ρ) ≤ ∑ᵢ -λᵢ log sᵢ`
  for faithful `σ`.
-/

open Spectra.QuantumMechanics.Channels RCLike
open scoped InnerProductSpace ENNReal NNReal

namespace Spectra.InformationGeometry.Quantum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace QState

/-- A nonnegative real family with a finite `ENNReal.ofReal`-sum is summable. -/
private lemma summable_of_ofReal_tsum_ne_top {ι : Type*} {g : ι → ℝ} (hg : ∀ i, 0 ≤ g i)
    (h : ∑' i, ENNReal.ofReal (g i) ≠ ⊤) : Summable g := by
  have heq : (fun i => ((g i).toNNReal : ℝ≥0∞)) = fun i => ENNReal.ofReal (g i) := rfl
  have hnn : Summable (fun i => (g i).toNNReal) := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable, heq]; exact h
  exact (NNReal.summable_coe.mpr hnn).congr fun i => Real.coe_toNNReal _ (hg i)

/-- The **measured cross entropy** `∑ᵢ -λᵢ log sᵢ` of `ρ` against `σ`'s diagonal `sᵢ` in `ρ`'s
eigenbasis, valued in `ℝ≥0∞`.  For faithful `σ` (all `sᵢ ∈ (0,1]`) each summand `-λᵢ log sᵢ ≥ 0`. -/
noncomputable def measuredCrossEntropy (ρ σ : QState H) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (-ρ.eigenvalue i * Real.log (ρ.diagSigma σ i))

/-- **Gibbs' inequality (commuting-case Klein).**  For faithful `σ`, `S(ρ) ≤ ∑ᵢ -λᵢ log sᵢ`.  This
is the classical `KL(λ ‖ s) ≥ 0` between `ρ`'s eigenvalue distribution and `σ`'s dephased
diagonal. -/
theorem vonNeumannEntropy_le_measuredCrossEntropy (ρ σ : QState H)
    (hfaith : ∀ i, 0 < ρ.diagSigma σ i) :
    vonNeumannEntropy ρ ≤ measuredCrossEntropy ρ σ := by
  have hlam_nn := ρ.eigenvalue_nonneg
  have hf_nn : ∀ i, 0 ≤ Real.negMulLog (ρ.eigenvalue i) := fun i =>
    Real.negMulLog_nonneg (hlam_nn i) (ρ.eigenvalue_le_one i)
  have hg_nn : ∀ i, 0 ≤ -ρ.eigenvalue i * Real.log (ρ.diagSigma σ i) := fun i => by
    have hlog : Real.log (ρ.diagSigma σ i) ≤ 0 :=
      Real.log_nonpos (hfaith i).le (ρ.diagSigma_le_one σ i)
    have := hlam_nn i
    nlinarith
  -- the Klein bound: negMulLog λᵢ ≤ -λᵢ log sᵢ + (sᵢ - λᵢ)
  have hbound : ∀ i, Real.negMulLog (ρ.eigenvalue i)
      ≤ (-ρ.eigenvalue i * Real.log (ρ.diagSigma σ i)) + (ρ.diagSigma σ i - ρ.eigenvalue i) := by
    intro i
    have hk := Real.klein_scalar (hlam_nn i) (hfaith i)
    have hsplit : ρ.eigenvalue i * Real.log (ρ.eigenvalue i / ρ.diagSigma σ i)
        = ρ.eigenvalue i * Real.log (ρ.eigenvalue i)
          - ρ.eigenvalue i * Real.log (ρ.diagSigma σ i) := by
      rcases eq_or_lt_of_le (hlam_nn i) with h0 | h0
      · rw [← h0]; ring
      · rw [Real.log_div (ne_of_gt h0) (ne_of_gt (hfaith i)), mul_sub]
    rw [hsplit] at hk
    have hnml : Real.negMulLog (ρ.eigenvalue i) = -ρ.eigenvalue i * Real.log (ρ.eigenvalue i) := by
      rw [Real.negMulLog]
    rw [hnml]; linarith
  rw [vonNeumannEntropy_eq_tsum]
  by_cases hRHS : measuredCrossEntropy ρ σ = ⊤
  · rw [hRHS]; exact le_top
  · have hs_summable : Summable (ρ.diagSigma σ) := (ρ.hasSum_diagSigma σ).summable
    have hlam_summable : Summable ρ.eigenvalue := ρ.hasSum_eigenvalue.summable
    have hg_summable : Summable (fun i => -ρ.eigenvalue i * Real.log (ρ.diagSigma σ i)) :=
      summable_of_ofReal_tsum_ne_top hg_nn (by rwa [measuredCrossEntropy] at hRHS)
    have hh_summable : Summable
        (fun i => (-ρ.eigenvalue i * Real.log (ρ.diagSigma σ i))
          + (ρ.diagSigma σ i - ρ.eigenvalue i)) :=
      hg_summable.add (hs_summable.sub hlam_summable)
    have hf_summable : Summable (fun i => Real.negMulLog (ρ.eigenvalue i)) :=
      Summable.of_nonneg_of_le hf_nn hbound hh_summable
    have hh_hs : HasSum
        (fun i => (-ρ.eigenvalue i * Real.log (ρ.diagSigma σ i))
          + (ρ.diagSigma σ i - ρ.eigenvalue i))
        ((∑' i, -ρ.eigenvalue i * Real.log (ρ.diagSigma σ i)) + (1 - 1)) :=
      hg_summable.hasSum.add ((ρ.hasSum_diagSigma σ).sub ρ.hasSum_eigenvalue)
    have hle : ∑' i, Real.negMulLog (ρ.eigenvalue i)
        ≤ (∑' i, -ρ.eigenvalue i * Real.log (ρ.diagSigma σ i)) + (1 - 1) :=
      hasSum_le hbound hf_summable.hasSum hh_hs
    have htsum_le : ∑' i, Real.negMulLog (ρ.eigenvalue i)
        ≤ ∑' i, (-ρ.eigenvalue i * Real.log (ρ.diagSigma σ i)) := by simpa using hle
    rw [measuredCrossEntropy, ← ENNReal.ofReal_tsum_of_nonneg hf_nn hf_summable,
      ← ENNReal.ofReal_tsum_of_nonneg hg_nn hg_summable]
    exact ENNReal.ofReal_le_ofReal htsum_le

end QState

end Spectra.InformationGeometry.Quantum
