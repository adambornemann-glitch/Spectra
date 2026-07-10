/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Spectrum.Complete
import Spectra.Resolvent.Spectrum
/-!
# Isolation of the hydrogen eigenvalues in the spectrum (Tier C: C2)

Each negative hydrogen eigenvalue `Eₙ = −1/(2n²)` is an **isolated** point of the spectrum: there
is a punctured disk around `Eₙ` (in `ℂ`) entirely inside the resolvent set.  This is the geometric
input to the simple-pole statement (C3): on such a punctured disk the resolvent `resolventOf H` is
analytic, so `(z − Eₙ)ⁿ · resolventOf H z` is differentiable off `Eₙ`.

## Main statements

The proof is real-analysis bookkeeping on the eigenvalue sequence (strictly increasing to `0`):
* `hydrogenEigenvalue_gap` — `Eₙ` is bounded away from every other eigenvalue by a fixed
  `g > 0` (the gap to the nearest neighbour `E_{n±1}`).
* `hydrogen_punctured_disk_subset_resolventSet` — combine the gap with `Eₙ < 0` (to stay below the
  essential spectrum `[0,∞)`), `mem_eigenvalues_of_mem_spectrum_neg` (nothing below `0` except the
  `Eₙ`), and `mem_resolventSet_of_im_ne_zero` (non-real points are always resolvent points).

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics IV*][reed1978], §XIII.
-/
open Complex
open QuantumMechanics.Hydrogen.RadialEq
open Spectra.QuantumMechanics.Hydrogen

namespace QuantumMechanics.Hydrogen.Spectrum

/-- **Spectral gap at `Eₙ`.** Every other eigenvalue is at distance `≥ g` from `Eₙ`, for a
fixed `g > 0` (the gap to the nearest neighbour). -/
lemma hydrogenEigenvalue_gap (n : ℕ) (hn : 1 ≤ n) :
    ∃ g : ℝ, 0 < g ∧ ∀ (m : ℕ) (hm : 1 ≤ m), m ≠ n →
      g ≤ |hydrogenEigenvalue m hm - hydrogenEigenvalue n hn| := by
  -- monotonicity of `Eₙ` in `n` (non-strict form).
  have mono_le : ∀ {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b), a ≤ b →
      hydrogenEigenvalue a ha ≤ hydrogenEigenvalue b hb := by
    intro a b ha hb hab
    simp only [hydrogenEigenvalue]
    have _ha0 : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
    have _hb0 : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
    have hab' : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast hab
    simp only [neg_div]
    rw [neg_le_neg_iff]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  rcases Nat.lt_or_ge n 2 with hlt2 | hge2
  · -- `n = 1`: every other eigenvalue is `> E₂`.
    have hn1 : n = 1 := by omega
    subst hn1
    have h2 : (1:ℕ) ≤ 2 := by norm_num
    set δ₀ := hydrogenEigenvalue 2 h2 - hydrogenEigenvalue 1 hn with hδ₀
    refine ⟨δ₀, ?_, ?_⟩
    · rw [hδ₀]; have := hydrogenEigenvalue_strictMono hn h2 (by norm_num); linarith
    · intro m hm hmne
      have hm2 : 2 ≤ m := by omega
      have h1 : hydrogenEigenvalue 2 h2 ≤ hydrogenEigenvalue m hm := mono_le h2 hm hm2
      have h2' : hydrogenEigenvalue 1 hn < hydrogenEigenvalue m hm :=
        hydrogenEigenvalue_strictMono hn hm (by omega)
      rw [abs_of_pos (by linarith)]; rw [hδ₀]; linarith
  · -- `n ≥ 2`: gap is the min of the distances to `E_{n−1}` and `E_{n+1}`.
    have hn1 : (1:ℕ) ≤ n - 1 := by omega
    have hp1 : (1:ℕ) ≤ n + 1 := by omega
    set δ₀ := hydrogenEigenvalue (n + 1) hp1 - hydrogenEigenvalue n hn with hδ₀
    set δ₁ := hydrogenEigenvalue n hn - hydrogenEigenvalue (n - 1) hn1 with hδ₁
    refine ⟨min δ₀ δ₁, ?_, ?_⟩
    · refine lt_min ?_ ?_
      · rw [hδ₀]; have := hydrogenEigenvalue_strictMono hn hp1 (by omega); linarith
      · rw [hδ₁]; have := hydrogenEigenvalue_strictMono hn1 hn (by omega); linarith
    · intro m hm hmne
      rcases lt_or_gt_of_ne hmne with hmn | hmn
      · -- `m < n`
        have hmle : m ≤ n - 1 := by omega
        have h1 : hydrogenEigenvalue m hm ≤ hydrogenEigenvalue (n - 1) hn1 := mono_le hm hn1 hmle
        have h2 : hydrogenEigenvalue (n - 1) hn1 < hydrogenEigenvalue n hn :=
          hydrogenEigenvalue_strictMono hn1 hn (by omega)
        rw [abs_of_neg (by linarith)]
        have hle : min δ₀ δ₁ ≤ δ₁ := min_le_right _ _
        rw [hδ₁] at hle; linarith
      · -- `n < m`
        have h1 : hydrogenEigenvalue (n + 1) hp1 ≤ hydrogenEigenvalue m hm :=
          mono_le hp1 hm (by omega)
        have h2 : hydrogenEigenvalue n hn < hydrogenEigenvalue m hm :=
          hydrogenEigenvalue_strictMono hn hm hmn
        rw [abs_of_pos (by linarith)]
        have hle : min δ₀ δ₁ ≤ δ₀ := min_le_left _ _
        rw [hδ₀] at hle; linarith

/-- **Each negative hydrogen eigenvalue is isolated in the spectrum.** There is a punctured disk
around `Eₙ` (in `ℂ`) inside the resolvent set of the hydrogen Hamiltonian. -/
theorem hydrogen_punctured_disk_subset_resolventSet (n : ℕ) (hn : 1 ≤ n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, z ≠ (hydrogenEigenvalue n hn : ℂ) →
      dist z (hydrogenEigenvalue n hn : ℂ) < δ →
      z ∈ Spectra.Resolvent.resolventSet (hydrogenHamiltonian ⟨1, one_pos⟩) := by
  obtain ⟨g, hg_pos, hg⟩ := hydrogenEigenvalue_gap n hn
  have hEneg : hydrogenEigenvalue n hn < 0 := hydrogenEigenvalue_neg n hn
  refine ⟨min g (-hydrogenEigenvalue n hn), lt_min hg_pos (by linarith), ?_⟩
  intro z hzne hzdist
  by_cases him : z.im = 0
  · -- real `z`: use that the only spectrum below `0` is the `Eₙ`, which are gapped.
    have hzeq : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simp [him]
    rw [hzeq]
    by_contra hcon
    have hspec : z.re ∈ Spectra.Resolvent.spectrum (hydrogenHamiltonian ⟨1, one_pos⟩) := hcon
    have hsub : z - (hydrogenEigenvalue n hn : ℂ) = ((z.re - hydrogenEigenvalue n hn : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [him]
    have hdeq : dist z (hydrogenEigenvalue n hn : ℂ) = |z.re - hydrogenEigenvalue n hn| := by
      rw [dist_eq_norm, hsub, Complex.norm_real, Real.norm_eq_abs]
    rw [hdeq] at hzdist
    have hre_neg : z.re < 0 := by
      have h1 : |z.re - hydrogenEigenvalue n hn| < -hydrogenEigenvalue n hn :=
        lt_of_lt_of_le hzdist (min_le_right _ _)
      have h2 := lt_of_le_of_lt (le_abs_self (z.re - hydrogenEigenvalue n hn)) h1
      linarith
    obtain ⟨m, hm, hEm⟩ := mem_eigenvalues_of_mem_spectrum_neg hspec hre_neg
    have hrene : z.re ≠ hydrogenEigenvalue n hn := fun h => hzne (by rw [hzeq, h])
    have hmne : m ≠ n := by intro h; subst h; exact hrene hEm
    have hgap := hg m hm hmne
    rw [← hEm] at hgap
    have h1 : |z.re - hydrogenEigenvalue n hn| < g := lt_of_lt_of_le hzdist (min_le_left _ _)
    linarith
  · -- non-real `z`: always a resolvent point for a self-adjoint operator.
    exact Spectra.Resolvent.mem_resolventSet_of_im_ne_zero
      (hydrogenHamiltonian_isSelfAdjoint ⟨1, one_pos⟩) him

end QuantumMechanics.Hydrogen.Spectrum
