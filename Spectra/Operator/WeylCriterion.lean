/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.BoundedBelow
/-!
# Weyl's criterion for the full spectrum

`λ ∈ spectrum A` iff there is an approximate eigensequence `ψ : ℕ → A.domain` with
`‖ψ n‖ → 1` and `‖A ψ n − λ ψ n‖ → 0` — no weak-nullness required (that stronger, *singular*
notion characterizes the essential spectrum, `Spectra.Essential.essSpectrum`).

This is genuinely an **operator/resolvent-theory** fact — `Spectra.Resolvent.spectrum` is itself
defined purely via bounded invertibility of `A - z` (no spectral measure), and both the statement
and the proof below mention nothing but `A` and vectors. The proof is PVM-free: the forward
direction case-splits on whether `A - λ` is bounded below. If not, normalizing witnesses of the
failure at bounds `1/(n+1)` produces the Weyl sequence directly. If so, the range of `A - λ` is
closed (`Spectra.Resolvent.range_isClosed_of_boundedBelow`) and dense
(`Spectra.Resolvent.range_dense_of_boundedBelow_real` — an orthogonal vector is a genuine
`λ`-eigenvector, killed by the bound), so `λ` is a resolvent point
(`Spectra.Resolvent.mem_resolventSet_of_boundedBelow_real`), contradicting `λ ∈ spectrum A`.
The backward direction is a direct squeeze against the bounded left inverse.

## Main results

* `mem_spectrum_iff_exists_weylSequence` — the criterion.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII.3.
* [Weidmann, *Linear Operators in Hilbert Spaces*][weidmann1980], Section 7.2.
-/
open Filter Topology
open scoped InnerProductSpace

namespace Spectra.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- If `A - λ` is not bounded below, normalizing witnesses of the failure at bounds `1/(n+1)`
yields a Weyl sequence: unit vectors with `‖A ψ n - λ ψ n‖ < 1/(n+1) → 0`. -/
private lemma exists_weylSequence_of_not_boundedBelow {A : H →ₗ.[ℂ] H} {lam : ℝ}
    (hbb : ¬ ∃ c : ℝ, 0 < c ∧ ∀ ψ : A.domain, c * ‖(ψ : H)‖ ≤ ‖A ψ - (lam : ℂ) • (ψ : H)‖) :
    ∃ ψ : ℕ → A.domain, Tendsto (fun n => ‖(ψ n : H)‖) atTop (𝓝 1) ∧
      Tendsto (fun n => ‖A (ψ n) - (lam : ℂ) • (ψ n : H)‖) atTop (𝓝 0) := by
  push Not at hbb
  have hseq : ∀ n : ℕ, ∃ ψ : A.domain,
      ‖A ψ - (lam : ℂ) • (ψ : H)‖ < (1 / ((n : ℝ) + 1)) * ‖(ψ : H)‖ :=
    fun n => hbb (1 / ((n : ℝ) + 1)) (by positivity)
  choose ψ0 hψ0 using hseq
  -- strictness forces the witnesses to be nonzero
  have hne : ∀ n, (0 : ℝ) < ‖(ψ0 n : H)‖ := by
    intro n
    by_contra h
    push Not at h
    have h0 : ‖(ψ0 n : H)‖ = 0 := le_antisymm h (norm_nonneg _)
    have hlt := hψ0 n
    rw [h0, mul_zero] at hlt
    exact absurd hlt (not_lt.mpr (norm_nonneg _))
  -- normalize
  set φn : ℕ → A.domain := fun n => (‖(ψ0 n : H)‖ : ℂ)⁻¹ • ψ0 n with _hφn
  have hφnorm : ∀ n, ‖(φn n : H)‖ = 1 := by
    intro n
    change ‖(‖(ψ0 n : H)‖ : ℂ)⁻¹ • (ψ0 n : H)‖ = 1
    rw [norm_smul]
    simp [(hne n).ne']
  have hφeig : ∀ n, ‖A (φn n) - (lam : ℂ) • (φn n : H)‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    have hAφ : A (φn n) = (‖(ψ0 n : H)‖ : ℂ)⁻¹ • A (ψ0 n) := A.map_smul _ (ψ0 n)
    have hcoe : ((φn n : A.domain) : H) = (‖(ψ0 n : H)‖ : ℂ)⁻¹ • (ψ0 n : H) := rfl
    calc ‖A (φn n) - (lam : ℂ) • (φn n : H)‖
        = ‖(‖(ψ0 n : H)‖ : ℂ)⁻¹‖ * ‖A (ψ0 n) - (lam : ℂ) • (ψ0 n : H)‖ := by
          rw [hAφ, hcoe, smul_comm ((lam : ℂ)) _ _, ← smul_sub, norm_smul]
      _ = ‖(ψ0 n : H)‖⁻¹ * ‖A (ψ0 n) - (lam : ℂ) • (ψ0 n : H)‖ := by
          congr 1
          simp
      _ < ‖(ψ0 n : H)‖⁻¹ * ((1 / ((n : ℝ) + 1)) * ‖(ψ0 n : H)‖) := by
          apply mul_lt_mul_of_pos_left (hψ0 n)
          exact inv_pos.mpr (hne n)
      _ = 1 / ((n : ℝ) + 1) := by
          rw [mul_comm (1 / ((n : ℝ) + 1)), ← mul_assoc, inv_mul_cancel₀ (hne n).ne', one_mul]
  refine ⟨φn, ?_, ?_⟩
  · rw [show (fun n => ‖(φn n : H)‖) = fun _ => (1 : ℝ) from funext hφnorm]
    exact tendsto_const_nhds
  · exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hφeig n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat

/-- **Weyl's criterion.** `λ ∈ spectrum A` iff there is an approximate eigensequence
`ψ : ℕ → A.domain` with `‖ψ n‖ → 1` and `‖A ψ n − λ ψ n‖ → 0` — no weak-nullness required. -/
theorem mem_spectrum_iff_exists_weylSequence {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (lam : ℝ) :
    lam ∈ Spectra.Resolvent.spectrum A ↔
      ∃ ψ : ℕ → A.domain, Tendsto (fun n => ‖(ψ n : H)‖) atTop (𝓝 1) ∧
        Tendsto (fun n => ‖A (ψ n) - (lam : ℂ) • (ψ n : H)‖) atTop (𝓝 0) := by
  constructor
  · intro hspec
    by_cases hbb : ∃ c : ℝ, 0 < c ∧
        ∀ ψ : A.domain, c * ‖(ψ : H)‖ ≤ ‖A ψ - (lam : ℂ) • (ψ : H)‖
    · obtain ⟨c, hc, hbound⟩ := hbb
      exact absurd
        (Spectra.Resolvent.mem_resolventSet_of_boundedBelow_real hA lam hc hbound) hspec
    · exact exists_weylSequence_of_not_boundedBelow hbb
  · rintro ⟨ψ, hψ_norm, hψ_eig⟩
    intro hres
    obtain ⟨R, hleft, -⟩ := hres
    have h0 : Tendsto (fun n => ‖(ψ n : H)‖) atTop (𝓝 0) := by
      have hle : ∀ n, ‖(ψ n : H)‖ ≤ ‖R‖ * ‖A (ψ n) - (lam : ℂ) • (ψ n : H)‖ := by
        intro n
        have h1 : R (A (ψ n) - (lam : ℂ) • (ψ n : H)) = (ψ n : H) := hleft (ψ n)
        calc ‖(ψ n : H)‖ = ‖R (A (ψ n) - (lam : ℂ) • (ψ n : H))‖ := by rw [h1]
          _ ≤ ‖R‖ * ‖A (ψ n) - (lam : ℂ) • (ψ n : H)‖ := R.le_opNorm _
      have hub : Tendsto (fun n => ‖R‖ * ‖A (ψ n) - (lam : ℂ) • (ψ n : H)‖) atTop (𝓝 0) := by
        simpa using hψ_eig.const_mul ‖R‖
      exact squeeze_zero (fun n => norm_nonneg _) hle hub
    exact absurd (tendsto_nhds_unique hψ_norm h0) (by norm_num)

end Spectra.Operator
