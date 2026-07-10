/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Spectrum
import Spectra.SpectralTheory.Essential.WeakCompact
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# The essential spectrum (singular/Weyl-sequence definition)

For a self-adjoint operator `A` (an unbounded `LinearPMap`) we define the **essential spectrum**
`essSpectrum hA : Set ℝ` by *singular (Weyl) sequences*: `λ ∈ essSpectrum hA` iff there is a
sequence `ψ : ℕ → A.domain` that is

* asymptotically normalized (`‖ψ n‖ → 1`),
* weakly null (`⟪g, ψ n⟫ → 0` for every `g`), and
* an approximate eigensequence (`‖A ψ n − λ ψ n‖ → 0`).

Weak nullness is exactly what is needed for the perturbation theorem (Weyl's theorem): a relatively
compact perturbation does not see a weakly-null approximate-eigenvector sequence
(`IsCompactOperator.tendsto_norm_apply_of_weaklyNull`).  An *orthonormal* approximate eigensequence
is a special case — orthonormal sequences are weakly null
(`Orthonormal.tendsto_inner_atTop_zero`) — so this matches the classical Weyl-criterion definition.

## Main definitions

* `Spectra.Essential.essSpectrum` — the essential spectrum of a self-adjoint `LinearPMap`.

## Main results

* `Spectra.Essential.mem_essSpectrum_of_seq` — build membership from an `H`-valued Weyl sequence.
* `Spectra.Essential.essSpectrum_subset_spectrum` — the essential spectrum is contained in the
  spectrum: a Weyl sequence obstructs bounded invertibility of `A − λ`.
-/

open Filter Topology
open scoped InnerProductSpace

namespace Spectra.Essential

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The **essential spectrum** of a self-adjoint operator `A`, defined by singular (Weyl) sequences:
`λ ∈ essSpectrum hA` iff there is `ψ : ℕ → A.domain` with `‖ψ n‖ → 1`, `ψ` weakly null, and
`‖A ψ n − λ ψ n‖ → 0`.  (`hA` is carried for discoverability; the set depends only on `A`.) -/
def essSpectrum {A : H →ₗ.[ℂ] H} (_hA : IsSelfAdjoint A) : Set ℝ :=
  { lam | ∃ ψ : ℕ → A.domain,
      Tendsto (fun n => ‖(ψ n : H)‖) atTop (𝓝 1) ∧
      (∀ g : H, Tendsto (fun n => ⟪g, (ψ n : H)⟫_ℂ) atTop (𝓝 0)) ∧
      Tendsto (fun n => ‖A (ψ n) - (lam : ℂ) • (ψ n : H)‖) atTop (𝓝 0) }

/-- Membership in `essSpectrum` from an `H`-valued Weyl sequence together with a domain-membership
witness.  This packages the `ℕ → A.domain` data so callers can work with plain vectors. -/
theorem mem_essSpectrum_of_seq {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (lam : ℝ)
    (φ : ℕ → H) (hmem : ∀ n, φ n ∈ A.domain)
    (hnorm : Tendsto (fun n => ‖φ n‖) atTop (𝓝 1))
    (hweak : ∀ g : H, Tendsto (fun n => ⟪g, φ n⟫_ℂ) atTop (𝓝 0))
    (heig : Tendsto (fun n => ‖A ⟨φ n, hmem n⟩ - (lam : ℂ) • φ n‖) atTop (𝓝 0)) :
    lam ∈ essSpectrum hA :=
  ⟨fun n => ⟨φ n, hmem n⟩, hnorm, hweak, heig⟩

/-- An **orthonormal** approximate eigensequence certifies membership in the essential spectrum
(the classical Weyl criterion): orthonormal sequences are normalized and weakly null
(`Orthonormal.tendsto_inner_atTop_zero`), so any orthonormal `ψ ⊆ A.domain` with
`‖A ψ n − λ ψ n‖ → 0` witnesses `λ ∈ essSpectrum hA`. -/
theorem mem_essSpectrum_of_orthonormal {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (lam : ℝ)
    (ψ : ℕ → A.domain) (hortho : Orthonormal ℂ (fun n => (ψ n : H)))
    (heig : Tendsto (fun n => ‖A (ψ n) - (lam : ℂ) • (ψ n : H)‖) atTop (𝓝 0)) :
    lam ∈ essSpectrum hA := by
  refine ⟨ψ, ?_, fun g => hortho.tendsto_inner_atTop_zero g, heig⟩
  have h1 : (fun n => ‖(ψ n : H)‖) = fun _ => (1 : ℝ) := funext fun n => hortho.norm_eq_one n
  rw [h1]; exact tendsto_const_nhds

/-- The essential spectrum is contained in the spectrum.  If `λ` had a bounded resolvent `R`, then
`‖ψ n‖ = ‖R (A ψ n − λ ψ n)‖ ≤ ‖R‖ · ‖A ψ n − λ ψ n‖ → 0`, contradicting `‖ψ n‖ → 1`. -/
theorem essSpectrum_subset_spectrum {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    essSpectrum hA ⊆ Spectra.Resolvent.spectrum A := by
  intro lam hlam
  obtain ⟨ψ, hψ_norm, _, hψ_eig⟩ := hlam
  intro hres
  obtain ⟨R, hleft, _⟩ := hres
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

end Spectra.Essential
