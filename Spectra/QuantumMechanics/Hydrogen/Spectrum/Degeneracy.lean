/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.TensorDecomp.Basic
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Equation.Basic
import Spectra.QuantumMechanics.Hydrogen.Laplacian.Spherical
import Spectra.QuantumMechanics.Hydrogen.Hamiltonian
import Spectra.QuantumMechanics.Hydrogen.Spectrum.Eigenvalue

/-!
# Hydrogen Level Degeneracy: the Combinatorial Half

The combinatorial content of hydrogen's `n²` degeneracy: the index set of the
`2ℓ+1` magnetic sublevels at each `ℓ < n`, the resulting orthonormal family of
`n²` bound states `ψ_{nℓm}`, and the dimension count for its span.

## Main statements

* `degeneracy_sum` — `Σ_{ℓ=0}^{n-1} (2ℓ+1) = n²`.
* `degenIndex` — the `Finset` of `(ℓ, j)` pairs indexing the `n²` sublevels at level `n`.
* `orthonormal_degenFamily` — the family `{ψ_{nℓm}}` is orthonormal.
* `degenFamily_span_finrank` — `dim span {ψ_{nℓm}} = n²`.

This is the **combinatorial half** of the physical degeneracy `dim ker(H − E_n) = n²`:
it counts the `n²` orthonormal spherical-coordinate bound states and shows their span
has dimension `n²`. Transporting this count to the true `Eₙ`-eigenspace of
`hydrogenHamiltonian` on `Sobolev.l2R3` — via the unitary `chartRealization` and the
completeness of the separated eigenfunctions within each angular-momentum sector — is
carried out in `Spectrum/Projections.lean` (`hydrogen_eigenspace_eq_span` and
`hydrogen_spectral_projection_finrank`), which delivers the full `n²` degeneracy.

## References

* [Schrödinger, *Quantisierung als Eigenwertproblem I-IV*][schrodinger1926]
* [Reed, Simon, *Methods of Modern Mathematical Physics IV*][reed1978], §XIII.3.
* [Bethe, Salpeter, *Quantum Mechanics of One- and Two-Electron Atoms*][bethesalpeter1957].
* [Griffiths, *Introduction to Quantum Mechanics*][griffiths2018], §4.2.
-/

noncomputable section

namespace QuantumMechanics.Hydrogen.Spectrum

open Spectra.QuantumMechanics.Hydrogen Spectra.QuantumMechanics.Hydrogen.Decomposition

/-! ## Degeneracy -/

/-- The degeneracy sum: Σ_{ℓ=0}^{n-1} (2ℓ+1) = n². -/
lemma degeneracy_sum (n : ℕ) :
    ∑ ℓ ∈ Finset.range n, (2 * ℓ + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => simp [Finset.sum_range_succ, ih]; ring

/-- The index set of the `n²` bound states at principal quantum number `n`:
    pairs `(ℓ, j)` with `ℓ < n` and `j < 2ℓ+1`, where `j` enumerates the magnetic
    quantum number `m = j − ℓ ∈ {−ℓ, …, ℓ}`. Indexing the `2ℓ+1` sublevels by
    `j ∈ {0,…,2ℓ}` (rather than `m` directly) makes the cardinality a clean
    `Finset.sigma` count. -/
def degenIndex (n : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.range n).sigma fun ℓ => Finset.range (2 * ℓ + 1)

/-- There are exactly `n²` degenerate bound states at level `n`. -/
@[simp] lemma card_degenIndex (n : ℕ) : (degenIndex n).card = n ^ 2 := by
  rw [degenIndex, Finset.card_sigma]
  simp only [Finset.card_range]
  exact degeneracy_sum n

/-- A member `(ℓ, j)` of `degenIndex n` satisfies `ℓ + 1 ≤ n` and `|m| ≤ ℓ`
    for the magnetic quantum number `m = j − ℓ`. -/
lemma degenIndex_bounds {n : ℕ} (i : ↥(degenIndex n)) :
    i.1.1 + 1 ≤ n ∧ |(i.1.2 : ℤ) - i.1.1| ≤ (i.1.1 : ℤ) := by
  have hmem := i.2
  simp only [degenIndex, Finset.mem_sigma, Finset.mem_range] at hmem
  obtain ⟨hℓ, hj⟩ := hmem
  refine ⟨by omega, ?_⟩
  rw [abs_le]; omega

/-- The family of the `n²` hydrogen bound states at level `n`: `ψ_{n ℓ m}` for
    `0 ≤ ℓ < n` and `m = j − ℓ` with `0 ≤ j ≤ 2ℓ`. -/
noncomputable def degenFamily (n : ℕ) : ↥(degenIndex n) → l2R3 :=
  fun i => hydrogenEigenfunction n i.1.1 ((i.1.2 : ℤ) - i.1.1)
    (degenIndex_bounds i).1 (degenIndex_bounds i).2

/-- The `n²` bound states at level `n` are orthonormal. -/
lemma orthonormal_degenFamily (n : ℕ) : Orthonormal ℂ (degenFamily n) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [degenFamily]
  rw [hydrogen_eigenfunction_orthonormal]
  split_ifs with hc hij hij2
  · rfl
  · refine absurd (Subtype.ext ?_) hij
    obtain ⟨-, hℓ, hm⟩ := hc
    exact Sigma.ext hℓ (heq_of_eq (by omega))
  · subst hij2
    exact absurd ⟨rfl, rfl, rfl⟩ hc
  · rfl

/-- **The span of the n-th level's bound states has dimension n².**

    The `n²` orthonormal bound states `{ψ_{nℓm} : 0 ≤ ℓ < n, |m| ≤ ℓ}` span an
    `n²`-dimensional subspace of `L²(ℝ³)`:
    `dim span {ψ_{nℓm}} = Σ_{ℓ=0}^{n-1} (2ℓ+1) = n²`.

    The sum counts, for each `ℓ ∈ {0,…,n−1}`, the `2ℓ+1` magnetic sublevels
    `m ∈ {−ℓ,…,ℓ}`. Orthonormality (`hydrogen_eigenfunction_orthonormal`) makes the
    family linearly independent, so the dimension of its span equals its cardinality
    `n²` (`card_degenIndex`, via `degeneracy_sum`).

    This is the combinatorial half of the physical degeneracy: it fixes the count on
    the spherical-coordinate side. That the transported span is *exactly* the
    `E_n`-eigenspace of `hydrogenHamiltonian` on `Sobolev.l2R3` — via the unitary
    `chartRealization` and completeness within each angular-momentum sector — is
    established in `Spectrum/Projections.lean` (`hydrogen_eigenspace_eq_span`,
    `hydrogen_spectral_projection_finrank`), yielding the full
    `dim ker(H − E_n) = n²`. -/
theorem degenFamily_span_finrank (n : ℕ) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (degenFamily n))) = n ^ 2 := by
  rw [finrank_span_eq_card (orthonormal_degenFamily n).linearIndependent,
    Fintype.card_coe, card_degenIndex]

end QuantumMechanics.Hydrogen.Spectrum
