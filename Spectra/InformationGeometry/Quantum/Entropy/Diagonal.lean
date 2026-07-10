/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Quantum.Entropy.Spectral

/-!
# The diagonal of a second state in an eigenbasis

For two quantum states `ρ σ : QState H`, the **diagonal** `sᵢ = ⟪eᵢ, σ eᵢ⟫` of `σ` in `ρ`'s
eigenbasis `{eᵢ}` is the bounded, positive quantity that carries the classical (commuting-case) part
of Klein's inequality: it needs no unbounded functional calculus of `log σ`, only an inner product.
This file records its `[0,1]` bounds and — the key fact — that `∑ᵢ sᵢ = Tr σ = 1`, so `s` is a
probability distribution on `ρ`'s eigen-index.  This is `Tr σ` read off in `ρ`'s basis, and
its proof is the eigenbasis `hasSum_eigenvalue` with `σ.toOp` in place of `ρ.toOp`.

## Main results

* `QState.diagSigma_nonneg` / `QState.diagSigma_le_one` — `0 ≤ sᵢ ≤ 1`.
* `QState.hasSum_diagSigma` — `∑ᵢ sᵢ = 1`.
-/

open Spectra.QuantumMechanics.Channels RCLike
open scoped InnerProductSpace ENNReal NNReal

namespace Spectra.InformationGeometry.Quantum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace QState

/-- The **diagonal** `sᵢ = re ⟪eᵢ, σ eᵢ⟫` of `σ` in `ρ`'s eigenbasis. -/
noncomputable def diagSigma (ρ σ : QState H) (i : eigenIndex ρ.toOp) : ℝ :=
  re ⟪ρ.eigenbasis i, σ.toOp (ρ.eigenbasis i)⟫_ℂ

/-- The diagonal `sᵢ` is nonnegative (`σ` is a positive operator). -/
lemma diagSigma_nonneg (ρ σ : QState H) (i : eigenIndex ρ.toOp) : 0 ≤ ρ.diagSigma σ i :=
  ((ContinuousLinearMap.nonneg_iff_isPositive σ.toOp).mp σ.toOp_nonneg).re_inner_nonneg_right _

/-- The diagonal `sᵢ` is at most `1` (`‖σ‖ ≤ ‖σ‖₁ = 1` and the eigenvectors are unit vectors). -/
lemma diagSigma_le_one (ρ σ : QState H) (i : eigenIndex ρ.toOp) : ρ.diagSigma σ i ≤ 1 := by
  have he : ‖ρ.eigenbasis i‖ = 1 := ρ.eigenbasis.orthonormal.1 i
  have hσ : ‖σ.toOp‖ ≤ 1 := σ.traceNorm_toOp ▸ norm_le_traceNorm σ.isTraceClass
  calc ρ.diagSigma σ i ≤ ‖⟪ρ.eigenbasis i, σ.toOp (ρ.eigenbasis i)⟫_ℂ‖ := re_le_norm _
    _ ≤ ‖ρ.eigenbasis i‖ * ‖σ.toOp (ρ.eigenbasis i)‖ := norm_inner_le_norm _ _
    _ ≤ ‖ρ.eigenbasis i‖ * (‖σ.toOp‖ * ‖ρ.eigenbasis i‖) := by
        gcongr; exact σ.toOp.le_opNorm _
    _ = ‖σ.toOp‖ * ‖ρ.eigenbasis i‖ ^ 2 := by ring
    _ ≤ 1 := by rw [he]; simpa using hσ

/-- **The diagonal is a probability distribution**: `∑ᵢ sᵢ = Tr σ = 1`, read off in `ρ`'s
eigenbasis. The proof is `hasSum_eigenvalue` with `σ.toOp` in place of `ρ.toOp`. -/
lemma hasSum_diagSigma (ρ σ : QState H) : HasSum (ρ.diagSigma σ) 1 := by
  have htr : ((posTrace ρ.eigenbasis σ.toOp).toReal : ℂ) = 1 := by
    rw [← trace_of_nonneg σ.toOp_nonneg ρ.eigenbasis]; exact σ.trace_toOp
  have htrR : (posTrace ρ.eigenbasis σ.toOp).toReal = 1 := by exact_mod_cast htr
  have hne : posTrace ρ.eigenbasis σ.toOp ≠ ⊤ := by
    intro h; rw [h, ENNReal.toReal_top] at htrR; exact zero_ne_one htrR
  have hpt1 : posTrace ρ.eigenbasis σ.toOp = 1 := by
    rw [← ENNReal.ofReal_toReal hne, htrR, ENNReal.ofReal_one]
  have hsum_enn : ∑' i, ENNReal.ofReal (ρ.diagSigma σ i) = 1 := by
    simp only [diagSigma]
    rw [← posTrace_eq_tsum_ofReal ρ.eigenbasis σ.toOp_nonneg, hpt1]
  have hnn := ρ.diagSigma_nonneg σ
  have heq : (fun i => ((ρ.diagSigma σ i).toNNReal : ℝ≥0∞))
      = fun i => ENNReal.ofReal (ρ.diagSigma σ i) := rfl
  have hsummable_nn : Summable (fun i => (ρ.diagSigma σ i).toNNReal) := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable, heq, hsum_enn]; exact ENNReal.one_ne_top
  have hsummable : Summable (ρ.diagSigma σ) :=
    (NNReal.summable_coe.mpr hsummable_nn).congr fun i => Real.coe_toNNReal _ (hnn i)
  have htsum : ∑' i, ρ.diagSigma σ i = 1 := by
    have h1 : (↑(∑' i, (ρ.diagSigma σ i).toNNReal) : ℝ≥0∞) = 1 := by
      rw [ENNReal.coe_tsum hsummable_nn, heq, hsum_enn]
    have h2 : (∑' i, (ρ.diagSigma σ i).toNNReal) = 1 := by exact_mod_cast h1
    calc ∑' i, ρ.diagSigma σ i = ∑' i, ((ρ.diagSigma σ i).toNNReal : ℝ) :=
          tsum_congr fun i => (Real.coe_toNNReal _ (hnn i)).symm
      _ = ((∑' i, (ρ.diagSigma σ i).toNNReal : ℝ≥0) : ℝ) := NNReal.coe_tsum.symm
      _ = 1 := by rw [h2, NNReal.coe_one]
  exact htsum ▸ hsummable.hasSum

end QState

end Spectra.InformationGeometry.Quantum
