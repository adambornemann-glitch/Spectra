/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SpectralTheory.SimplePole
import Spectra.QuantumMechanics.Hydrogen.Spectrum.Isolation
/-!
# Meromorphy of the hydrogen resolvent (Tier C: C3 + C4 + C5)

The resolvent of the hydrogen Hamiltonian is **meromorphic** on `ℂ ∖ [0,∞)`, with a pole at
each negative eigenvalue `Eₙ`.  The pole step (C3) is the operator-general
`meromorphicAt_resolventOf_of_isolated` specialized via the eigenvalue isolation (`C2`) and the
gap-projection (`G3`); the assembly (C4) cases on the region `ℂ ∖ Set.Ici (0:ℂ)`; the residue
step (C5) reads off the limit `(z − Eₙ)·R(z) → −E({Eₙ})`.

## Main statements
* `hydrogen_meromorphicAt_eigenvalue` — `MeromorphicAt (resolventOf H) Eₙ` (C3).
* `hydrogen_meromorphicOn` — `MeromorphicOn (resolventOf H) (Set.Ici (0:ℂ))ᶜ` (C4).
* `hydrogen_residue_eigenvalue` — the residue at `Eₙ` is `−E({Eₙ})` (C5).
-/
open Complex Filter
open scoped ComplexOrder Topology
open Spectra.Resolvent
open Spectra.YosidaHille
open Spectra.OneParameterUnitaryGroup
open Spectra.QuantumMechanics.SpectralTheory
open QuantumMechanics.Hydrogen.RadialEq
open Spectra.QuantumMechanics.Hydrogen

namespace QuantumMechanics.Hydrogen.Spectrum

/-- **C3 — the hydrogen resolvent is meromorphic at each negative eigenvalue `Eₙ`** (a pole,
`MeromorphicAt (resolventOf H) Eₙ`). -/
theorem hydrogen_meromorphicAt_eigenvalue (n : ℕ) (hn : 1 ≤ n) :
    MeromorphicAt (resolventOf (hydrogenHamiltonian ⟨1, one_pos⟩))
      (hydrogenEigenvalue n hn : ℂ) := by
  obtain ⟨δ, hδpos, hiso⟩ := hydrogen_punctured_disk_subset_resolventSet n hn
  set A := hydrogenHamiltonian ⟨1, one_pos⟩ with _hA_def
  have hA : IsSelfAdjoint A := hydrogenHamiltonian_isSelfAdjoint ⟨1, one_pos⟩
  set lam := hydrogenEigenvalue n hn with _hlam
  -- `E(puncturedGap) = 0` (G3 + C2 isolation)
  have hsub : ∀ l ∈ puncturedGap lam δ, (l : ℂ) ∈ resolventSet A := by
    intro l hl
    rw [puncturedGap, Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff] at hl
    obtain ⟨⟨h1, h2⟩, h3⟩ := hl
    refine hiso (l : ℂ) (fun h => h3 (by exact_mod_cast h)) ?_
    have hdist : dist (l : ℂ) (lam : ℂ) = |l - lam| := by
      rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [hdist, abs_lt]; constructor <;> linarith
  have hgapJ : spectralProjection (genToGroup hA) (puncturedGap lam δ)
      (measurableSet_puncturedGap lam δ) = 0 :=
    spectralPVM_proj_eq_zero_of_subset_resolventSet hA (measurableSet_puncturedGap lam δ) hsub
  -- isolation transported to the generator of `e^{itA}`
  have hiso' : ∀ z : ℂ, z ≠ (lam : ℂ) → dist z (lam : ℂ) < δ →
      z ∈ resolventSet (generator (genToGroup hA)) := by
    intro z hzne hzd
    rw [generator_genToGroup hA]
    exact hiso z hzne hzd
  have hmero := meromorphicAt_resolventOf_of_isolated (genToGroup hA) hδpos hgapJ hiso'
  rwa [generator_genToGroup hA] at hmero

/-- **C4 — the hydrogen resolvent is meromorphic on `ℂ ∖ [0,∞)`** (the complement of the
essential spectrum): analytic off the spectrum, with a pole at each negative eigenvalue. -/
theorem hydrogen_meromorphicOn :
    MeromorphicOn (resolventOf (hydrogenHamiltonian ⟨1, one_pos⟩)) (Set.Ici (0 : ℂ))ᶜ := by
  set A := hydrogenHamiltonian ⟨1, one_pos⟩ with _hA_def
  have hA : IsSelfAdjoint A := hydrogenHamiltonian_isSelfAdjoint ⟨1, one_pos⟩
  intro x hx
  by_cases him : x.im = 0
  · -- real `x`, necessarily `x.re < 0`
    have hxre : x.re < 0 := by
      rw [Set.mem_compl_iff, Set.mem_Ici, Complex.nonneg_iff, not_and_or] at hx
      rcases hx with h | h
      · exact not_le.mp h
      · exact absurd him.symm h
    have hxeq : x = (x.re : ℂ) := by apply Complex.ext <;> simp [him]
    by_cases hspec : x.re ∈ Spectra.Resolvent.spectrum A
    · -- eigenvalue (H0): simple pole, C3
      obtain ⟨m, hm, hEm⟩ := mem_eigenvalues_of_mem_spectrum_neg hspec hxre
      rw [hxeq, hEm]
      exact hydrogen_meromorphicAt_eigenvalue m hm
    · -- resolvent point: analytic (C1)
      have hres : (x.re : ℂ) ∈ resolventSet A := by
        by_contra hc; exact hspec hc
      rw [hxeq]
      exact (resolventOf_analyticAt hres).meromorphicAt
  · -- non-real: resolvent point (analytic, C1)
    exact (resolventOf_analyticAt (mem_resolventSet_of_im_ne_zero hA him)).meromorphicAt

/-- **C5 — the residue of the hydrogen resolvent at `Eₙ` is `−E({Eₙ})`** (the spectral
projection): `(z − Eₙ)·R(z) → −E({Eₙ})` in operator norm as `z → Eₙ`. -/
theorem hydrogen_residue_eigenvalue (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun z => (z - (hydrogenEigenvalue n hn : ℂ))
        • resolventOf (hydrogenHamiltonian ⟨1, one_pos⟩) z)
      (𝓝[≠] (hydrogenEigenvalue n hn : ℂ))
      (𝓝 (-(spectralProjection (genToGroup (hydrogenHamiltonian_isSelfAdjoint ⟨1, one_pos⟩))
          {hydrogenEigenvalue n hn} (measurableSet_singleton _)))) := by
  obtain ⟨δ, hδpos, hiso⟩ := hydrogen_punctured_disk_subset_resolventSet n hn
  set A := hydrogenHamiltonian ⟨1, one_pos⟩ with _hA_def
  have hA : IsSelfAdjoint A := hydrogenHamiltonian_isSelfAdjoint ⟨1, one_pos⟩
  set lam := hydrogenEigenvalue n hn with _hlam
  have hsub : ∀ l ∈ puncturedGap lam δ, (l : ℂ) ∈ resolventSet A := by
    intro l hl
    rw [puncturedGap, Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff] at hl
    obtain ⟨⟨h1, h2⟩, h3⟩ := hl
    refine hiso (l : ℂ) (fun h => h3 (by exact_mod_cast h)) ?_
    have hdist : dist (l : ℂ) (lam : ℂ) = |l - lam| := by
      rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [hdist, abs_lt]; constructor <;> linarith
  have hgapJ : spectralProjection (genToGroup hA) (puncturedGap lam δ)
      (measurableSet_puncturedGap lam δ) = 0 :=
    spectralPVM_proj_eq_zero_of_subset_resolventSet hA (measurableSet_puncturedGap lam δ) hsub
  have hres := tendsto_sub_smul_resolventOf (genToGroup hA) hδpos hgapJ
  rwa [generator_genToGroup hA] at hres

end QuantumMechanics.Hydrogen.Spectrum
