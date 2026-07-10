/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.DFT.Variational.Semibounded
import Spectra.QuantumMechanics.BornRule.Observable
import Spectra.SpectralTheory.Weak

/-!
# The Rayleigh–Ritz variational lower bound

The variational half of Density Functional Theory's Rayleigh–Ritz substrate (lane **S2**): for a
self-adjoint operator that is bounded below, **every trial state's energy expectation is at least
the bottom of the spectrum**, `E₀ ≤ Re⟪ψ, Aψ⟫` for unit `ψ ∈ dom A`. Combined with the marquee
containment `σ(A) ⊆ closure (W(A))` from `Semibounded.lean` (which gives the reverse `inf W ≤ E₀`),
this is the numerical-range–free spectral direction `W(A) ⊆ [E₀, ∞)` of the variational principle.

The proof is the weak spectral theorem in probabilistic form: `Re⟪ψ, Aψ⟫ = ∫ λ dμ_ψ` where `μ_ψ` is
the Born measure, a probability measure (unit `ψ`) supported on the spectrum `⊆ [E₀, ∞)`; hence
`∫ λ dμ_ψ ≥ ∫ E₀ dμ_ψ = E₀`.

## Main results

* `groundStateEnergy_le_rayleigh` — `E₀ ≤ Re⟪ψ, Aψ⟫` for unit `ψ ∈ dom A`.
* `eigenvector_of_rayleigh_eq_groundStateEnergy` — the equality case: a minimizer is a ground
  eigenvector.
* `sInf_rayleigh_eq_groundStateEnergy` — the full variational identity `E₀ = inf Rayleigh`.
* `groundStateEnergy_lt_rayleigh_of_not_eigenvector` — the **strict** bound (lane **HK1S**): off the
  eigenvector, `E₀ < Re⟪ψ, Aψ⟫`.
* `groundStateEnergy_lt_rayleigh_of_not_scalar_multiple` — under a nondegeneracy hypothesis, the
  strict bound off the ground-state eigenline.
* `ground_state_unique_up_to_phase` — a simple ground state is unique up to a phase.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics IV*][reed1980], Section XIII.1.
-/

open scoped InnerProductSpace
open Spectra.Operator Spectra.Resolvent MeasureTheory
open Spectra.QuantumMechanics.BornRule.Observable
open Spectra.QuantumMechanics.BornRule.Moments
open Spectra.QuantumMechanics.BornRule.PVM
open Spectra.QuantumMechanics.SpectralTheory

namespace Spectra.DFT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The Rayleigh–Ritz variational lower bound.** For a self-adjoint operator that is semibounded
below, every unit trial vector in the domain has energy expectation at least the bottom of the
spectrum: `E₀ ≤ Re⟪ψ, Aψ⟫`. Proved from the weak spectral theorem `⟪ψ, Aψ⟫ = ∫ λ dμ_ψ` and the
Born measure being a probability measure supported on `σ(A) ⊆ [E₀, ∞)`. -/
theorem groundStateEnergy_le_rayleigh {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hne : (numericalRange A).Nonempty) {c : ℝ} (hb : IsSemibounded A c)
    {ψ : H} (hψ : ψ ∈ A.domain) (hnorm : ‖ψ‖ = 1) :
    groundStateEnergy A ≤ (⟪ψ, A ⟨ψ, hψ⟩⟫_ℂ).re := by
  set A' : SelfAdjointOperator H := ⟨A, hA⟩ with _hA'
  set μ : Measure ℝ := A'.bornMeasure ψ with _hμ
  haveI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_bornMeasure A' hnorm
  have hint : Integrable (fun s : ℝ => s) μ :=
    spectralPVM_integrable_id hA ψ hψ
  have hval : ∫ s, s ∂μ = (⟪ψ, A ⟨ψ, hψ⟩⟫_ℂ).re :=
    bornExpectation_eq_inner A' hψ
  have hsupp : μ.support ⊆ Set.Ici (groundStateEnergy A) :=
    (bornMeasure_support_subset_spectrum A' ψ).trans
      (spectrum_subset_Ici_groundStateEnergy hA hne hb)
  have hae : ∀ᵐ s ∂μ, groundStateEnergy A ≤ s := by
    filter_upwards [Measure.support_mem_ae (μ := μ)] with s hs using hsupp hs
  calc groundStateEnergy A
      = ∫ _s, groundStateEnergy A ∂μ := by
        rw [integral_const]; simp
    _ ≤ ∫ s, s ∂μ := integral_mono_ae (integrable_const _) hint hae
    _ = (⟪ψ, A ⟨ψ, hψ⟩⟫_ℂ).re := hval

/-- **The variational equality case: a minimizing state is a ground eigenvector.** If a unit vector
`ψ ∈ dom A` attains the bottom of the spectrum as its energy expectation, `Re⟪ψ, Aψ⟫ = E₀`, then it
is an eigenvector with eigenvalue `E₀`: `Aψ = E₀ • ψ`. The Born measure has its mean equal to the
minimum of its support, so it is concentrated at `E₀` (variance zero); the variance is
`‖Aψ − E₀ψ‖²`, which therefore vanishes. This is the keystone for the Hohenberg–Kohn nondegeneracy
lemma (HK1S) and the Levy–Lieb recovery clause. -/
theorem eigenvector_of_rayleigh_eq_groundStateEnergy {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hne : (numericalRange A).Nonempty) {c : ℝ} (hb : IsSemibounded A c)
    {ψ : H} (hψ : ψ ∈ A.domain) (hnorm : ‖ψ‖ = 1)
    (hmin : (⟪ψ, A ⟨ψ, hψ⟩⟫_ℂ).re = groundStateEnergy A) :
    A ⟨ψ, hψ⟩ = (groundStateEnergy A : ℂ) • ψ := by
  set A' : SelfAdjointOperator H := ⟨A, hA⟩ with _hA'
  set E₀ : ℝ := groundStateEnergy A with _hE₀
  haveI : IsProbabilityMeasure (A'.bornMeasure ψ) := isProbabilityMeasure_bornMeasure A' hnorm
  have hint : Integrable (fun s : ℝ => s) (A'.bornMeasure ψ) := spectralPVM_integrable_id hA ψ hψ
  have hexp : bornExpectation A'.spectralPVM ψ = E₀ := (bornExpectation_eq_inner A' hψ).trans hmin
  have hval : ∫ s, s ∂(A'.bornMeasure ψ) = E₀ := hexp
  have hsupp : (A'.bornMeasure ψ).support ⊆ Set.Ici E₀ :=
    (bornMeasure_support_subset_spectrum A' ψ).trans
      (spectrum_subset_Ici_groundStateEnergy hA hne hb)
  have hae : ∀ᵐ s ∂(A'.bornMeasure ψ), E₀ ≤ s := by
    filter_upwards [Measure.support_mem_ae (μ := A'.bornMeasure ψ)] with s hs using hsupp hs
  have hsub0 : ∫ s, (s - E₀) ∂(A'.bornMeasure ψ) = 0 := by
    rw [integral_sub hint (integrable_const E₀), hval, integral_const]; simp
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[A'.bornMeasure ψ] (fun s => s - E₀) := by
    filter_upwards [hae] with s hs
    simp only [Pi.zero_apply]; linarith
  have haez : (fun s : ℝ => s - E₀) =ᵐ[A'.bornMeasure ψ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnn (hint.sub (integrable_const E₀))).1 hsub0
  have hvar0 : bornVariance A'.spectralPVM ψ = 0 := by
    rw [show bornVariance A'.spectralPVM ψ
          = ∫ s, (s - bornExpectation A'.spectralPVM ψ) ^ 2 ∂(bornMeasure A'.spectralPVM ψ)
            from rfl,
        hexp]
    have hsq : (fun s : ℝ => (s - E₀) ^ 2) =ᵐ[bornMeasure A'.spectralPVM ψ] 0 := by
      filter_upwards [haez] with s hs
      simp only [Pi.zero_apply] at hs ⊢
      rw [hs]; ring
    rw [integral_congr_ae hsq]; simp
  have hcm := bornVariance_eq_central_moment A' hψ
  rw [hvar0, hexp] at hcm
  have hz : A ⟨ψ, hψ⟩ - (E₀ : ℂ) • ψ = 0 :=
    norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp hcm.symm)
  exact sub_eq_zero.mp hz

/-- **The Rayleigh–Ritz variational principle.** The bottom of the spectrum is the infimum of the
Rayleigh quotients over unit vectors in the domain:
`E₀ = inf { Re⟪ψ, Aψ⟫ : ψ ∈ dom A, ‖ψ‖ = 1 }` (written as `sInf (Complex.re '' numericalRange A)`).
The `≥` direction is the per-vector lower bound `groundStateEnergy_le_rayleigh`; the `≤` direction
is that `E₀ ∈ σ(A) ⊆ closure (W(A))`, so trial energies approach `E₀` from above. -/
theorem sInf_rayleigh_eq_groundStateEnergy {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hne : (numericalRange A).Nonempty) {c : ℝ} (hb : IsSemibounded A c)
    (hSpec : (spectrum A).Nonempty) :
    sInf (Complex.re '' numericalRange A) = groundStateEnergy A := by
  have hlb : groundStateEnergy A ∈ lowerBounds (Complex.re '' numericalRange A) := by
    rintro r ⟨z, ⟨ψ, hψ1, rfl⟩, rfl⟩
    exact groundStateEnergy_le_rayleigh hA hne hb ψ.2 hψ1
  refine le_antisymm ?_ (le_csInf (hne.image _) hlb)
  have hmemW : (groundStateEnergy A : ℂ) ∈ closure (numericalRange A) :=
    spectrum_subset_closure_numericalRange hA hne _
      (groundStateEnergy_mem_spectrum hA hne hb hSpec)
  have hmemR : groundStateEnergy A ∈ closure (Complex.re '' numericalRange A) :=
    image_closure_subset_closure_image Complex.continuous_re
      ⟨(groundStateEnergy A : ℂ), hmemW, Complex.ofReal_re _⟩
  exact (closure_minimal (fun r hr => csInf_le ⟨_, hlb⟩ hr) isClosed_Ici) hmemR

/-! ## Strict Rayleigh–Ritz and nondegeneracy (lane HK1S)

The strict form of the variational principle, the substrate that turns the (soft) Hohenberg–Kohn
existence statements into the (hard) HK1 injectivity `v ↦ n`. The core fact needs **no** simplicity:
away from the ground eigenline the Rayleigh quotient is *strictly* above `E₀`, because equality
would force `ψ` to be a ground eigenvector (the keystone
`eigenvector_of_rayleigh_eq_groundStateEnergy`). A geometric-nondegeneracy hypothesis — every
`E₀`-eigenvector is a scalar multiple of a fixed unit ground state `ψ₀` — then upgrades "not an
eigenvector" to "not on the eigenline" and yields uniqueness up to phase. -/

/-- **Strict Rayleigh–Ritz, eigenvector form.** For a semibounded self-adjoint operator, a unit
trial vector whose image is *not* the ground-eigenvalue scaling `E₀ • ψ` has energy expectation
**strictly** above the bottom of the spectrum: `E₀ < Re⟪ψ, Aψ⟫`. This needs no simplicity — it is
the contrapositive of `eigenvector_of_rayleigh_eq_groundStateEnergy` combined with the non-strict
bound. -/
theorem groundStateEnergy_lt_rayleigh_of_not_eigenvector {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hne : (numericalRange A).Nonempty) {c : ℝ} (hb : IsSemibounded A c)
    {ψ : H} (hψ : ψ ∈ A.domain) (hnorm : ‖ψ‖ = 1)
    (hoff : A ⟨ψ, hψ⟩ ≠ (groundStateEnergy A : ℂ) • ψ) :
    groundStateEnergy A < (⟪ψ, A ⟨ψ, hψ⟩⟫_ℂ).re := by
  refine lt_of_le_of_ne (groundStateEnergy_le_rayleigh hA hne hb hψ hnorm) ?_
  intro hEq
  exact hoff (eigenvector_of_rayleigh_eq_groundStateEnergy hA hne hb hψ hnorm hEq.symm)

/-- **Strict Rayleigh–Ritz, nondegenerate form (HK1S).** Assume geometric nondegeneracy of the
ground state: every `E₀`-eigenvector is a scalar multiple of a fixed vector `ψ₀`. Then any unit
trial vector that is *not* a scalar multiple of `ψ₀` has energy expectation strictly above `E₀`.
This is the strict variational separation that drives the Hohenberg–Kohn I reductio. -/
theorem groundStateEnergy_lt_rayleigh_of_not_scalar_multiple {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hne : (numericalRange A).Nonempty) {c : ℝ} (hb : IsSemibounded A c) {ψ₀ : H}
    (hsimple : ∀ φ : H, ∀ hφ : φ ∈ A.domain,
      A ⟨φ, hφ⟩ = (groundStateEnergy A : ℂ) • φ → ∃ μ : ℂ, φ = μ • ψ₀)
    {ψ : H} (hψ : ψ ∈ A.domain) (hnorm : ‖ψ‖ = 1) (hoff : ∀ μ : ℂ, ψ ≠ μ • ψ₀) :
    groundStateEnergy A < (⟪ψ, A ⟨ψ, hψ⟩⟫_ℂ).re := by
  refine groundStateEnergy_lt_rayleigh_of_not_eigenvector hA hne hb hψ hnorm (fun hEq => ?_)
  obtain ⟨μ, hμ⟩ := hsimple ψ hψ hEq
  exact hoff μ hμ

omit [CompleteSpace H] in
/-- **A simple ground state is unique up to phase.** Under geometric nondegeneracy (every
`E₀`-eigenvector is a scalar multiple of the unit reference `ψ₀`), any unit ground eigenvector `ψ`
equals `ψ₀` up to a unit-modulus phase: `∃ μ, ‖μ‖ = 1 ∧ ψ = μ • ψ₀`. The scalar comes from
nondegeneracy; its modulus is pinned to `1` by both vectors being unit. -/
theorem ground_state_unique_up_to_phase {A : H →ₗ.[ℂ] H} {ψ₀ : H}
    (hsimple : ∀ φ : H, ∀ hφ : φ ∈ A.domain,
      A ⟨φ, hφ⟩ = (groundStateEnergy A : ℂ) • φ → ∃ μ : ℂ, φ = μ • ψ₀)
    {ψ : H} (hψ : ψ ∈ A.domain) (hnorm : ‖ψ‖ = 1)
    (heig : A ⟨ψ, hψ⟩ = (groundStateEnergy A : ℂ) • ψ) (hψ₀norm : ‖ψ₀‖ = 1) :
    ∃ μ : ℂ, ‖μ‖ = 1 ∧ ψ = μ • ψ₀ := by
  obtain ⟨μ, hμ⟩ := hsimple ψ hψ heig
  refine ⟨μ, ?_, hμ⟩
  have hnm : ‖ψ‖ = ‖μ‖ * ‖ψ₀‖ := by rw [hμ, norm_smul]
  rwa [hnorm, hψ₀norm, mul_one, eq_comm] at hnm

end Spectra.DFT
