/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Operator/WeylCriterion.lean
-/
import Spectra.SpectralTheory.Essential.Discrete
/-!
# Weyl's criterion for the full spectrum

`Spectra.Essential.essSpectrum` already characterizes the *essential* spectrum via singular
(weakly-null) Weyl sequences. This file drops the weak-nullness requirement to characterize the
*entire* spectrum: `λ ∈ spectrum A` iff there is an approximate eigensequence `ψ : ℕ → A.domain`
with `‖ψ n‖ → 1` and `‖A ψ n − λ ψ n‖ → 0`.

This is genuinely an **operator/resolvent-theory** fact — `Spectra.Resolvent.spectrum` is itself
defined purely via bounded invertibility of `A - z` (no spectral measure), and the criterion's
*statement* mentions nothing but `A` and vectors. It belongs here in `Operator/`, not in
`SpectralTheory/Essential/`, even though the *proof* below currently takes a shortcut through
spectral-measure machinery.

## TODO: a PVM-free proof

The backward direction (`∃` Weyl sequence `→ λ ∈ spectrum`) is already proof-theoretically pure —
a direct resolvent/squeeze argument, no spectral measure anywhere. The forward direction, though,
currently routes through `essSpectrum` and `SpectralTheory.Essential.Discrete`'s
spectral-annulus construction (built from projection-valued measures) purely for reuse — that
machinery was already sorry-free and available, not because the fact needs it. The classical proof
of "`λ ∈ spectrum` ⟹ `∃` approximate eigensequence" only needs closed-operator theory: if
`A - λ` is not bounded below, an approximate eigensequence falls out of the definition directly;
if it *is* bounded below (hence injective with closed range) but not surjective, a unit vector
orthogonal to the range is — via `(A - λ)` self-adjoint — an honest eigenvector, by the same
weak-eigenvalue/adjoint-domain-membership technique already used in
`Resolvent/Range/Orthogonal.lean` and `YosidaHille/Helpers.lean`'s `op_range_dense`. Reproving the
forward direction this way would let this file drop its `SpectralTheory.Essential` dependency
entirely.

## Main results

* `mem_spectrum_iff_exists_weylSequence` — the criterion. The forward direction case-splits on
  `essSpectrum` membership: inside it, the singular Weyl sequence already built by
  `SpectralTheory.Essential.Discrete` works verbatim (its weak-null component is simply dropped);
  outside it, `mem_pointSpectrum_of_mem_spectrum_notMem_essSpectrum` extracts a genuine
  eigenvector, whose normalization is a constant (hence trivially convergent) Weyl sequence. The
  backward direction is `essSpectrum_subset_spectrum`'s own argument, which never actually used
  weak-nullness.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII.3.
* [Weidmann, *Linear Operators in Hilbert Spaces*][weidmann1980], Section 7.2.
-/
open Filter Topology
open scoped InnerProductSpace
open Spectra.Essential Spectra.Resolvent

namespace Spectra.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A normalized eigenvector gives a constant, exactly-satisfying Weyl sequence. -/
private lemma weylSequence_of_eigenvector {A : H →ₗ.[ℂ] H} {lam : ℝ} {ψ : A.domain}
    (hψne : (ψ : H) ≠ 0) (heig : A ψ = (lam : ℂ) • (ψ : H)) :
    ∃ φ : ℕ → A.domain, Tendsto (fun n => ‖(φ n : H)‖) atTop (𝓝 1) ∧
      Tendsto (fun n => ‖A (φ n) - (lam : ℂ) • (φ n : H)‖) atTop (𝓝 0) := by
  have hnorm_pos : (0 : ℝ) < ‖(ψ : H)‖ := norm_pos_iff.mpr hψne
  set φ : A.domain := (‖(ψ : H)‖ : ℂ)⁻¹ • ψ with hφ
  have hφnorm : ‖(φ : H)‖ = 1 := by
    show ‖(‖(ψ : H)‖ : ℂ)⁻¹ • (ψ : H)‖ = 1
    rw [norm_smul]
    simp [hnorm_pos.ne']
  have hφeig : A φ - (lam : ℂ) • (φ : H) = 0 := by
    have hAφ : A φ = (‖(ψ : H)‖ : ℂ)⁻¹ • A ψ := A.map_smul _ ψ
    have hφval : (φ : H) = (‖(ψ : H)‖ : ℂ)⁻¹ • (ψ : H) := rfl
    rw [hAφ, heig, hφval, smul_smul, smul_smul, mul_comm]
    simp
  refine ⟨fun _ => φ, ?_, ?_⟩
  · rw [show (fun _ : ℕ => ‖(φ : H)‖) = fun _ => (1 : ℝ) from funext (fun _ => hφnorm)]
    exact tendsto_const_nhds
  · rw [show (fun _ : ℕ => ‖A φ - (lam : ℂ) • (φ : H)‖) = fun _ => (0 : ℝ) from
      funext (fun _ => by rw [hφeig, norm_zero])]
    exact tendsto_const_nhds

/-- **Weyl's criterion.** `λ ∈ spectrum A` iff there is an approximate eigensequence
`ψ : ℕ → A.domain` with `‖ψ n‖ → 1` and `‖A ψ n − λ ψ n‖ → 0` — no weak-nullness required. -/
theorem mem_spectrum_iff_exists_weylSequence {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (lam : ℝ) :
    lam ∈ Spectra.Resolvent.spectrum A ↔
      ∃ ψ : ℕ → A.domain, Tendsto (fun n => ‖(ψ n : H)‖) atTop (𝓝 1) ∧
        Tendsto (fun n => ‖A (ψ n) - (lam : ℂ) • (ψ n : H)‖) atTop (𝓝 0) := by
  constructor
  · intro hspec
    by_cases hess : lam ∈ essSpectrum hA
    · obtain ⟨ψ, hnorm, -, heig⟩ := hess
      exact ⟨ψ, hnorm, heig⟩
    · obtain ⟨ψ, hψne, hψeig⟩ :=
        Spectra.QuantumMechanics.SpectralTheory.mem_pointSpectrum_of_mem_spectrum_notMem_essSpectrum
          hA hspec hess
      exact weylSequence_of_eigenvector hψne hψeig
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
