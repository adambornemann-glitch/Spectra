/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Spectrum.SeparatedEigenfunction
import Spectra.SpectralTheory.Eigenspace

/-!
# The hydrogen spectral projection onto a discrete eigenspace

This file assembles the *spectral-projection theorem* for the bound states of the
`Z = 1` hydrogen atom: the range of the spectral projection `E({Eₙ})` of the
self-adjoint Hamiltonian `H = −½Δ − 1/r` onto the spectral atom `{Eₙ}` is exactly
the `ℂ`-span of the `n²` degeneracy eigenfunctions `ψ_{nℓm}`.

## Main statements

* `hydrogen_eigenspace_eq_span` — the operator eigenspace
  `ker(H − Eₙ) = { ψ | ∃ h, H ψ = Eₙ ψ }` equals
  `span { chartRealization.symm (degenFamily n ·) }`.  This is the assembly of the two
  inclusions proved in `SeparatedEigenfunction.lean`:
    - `⊇` (`degenFamily_mem_ker`, *H1*): every degeneracy state is a genuine `H²`
      eigenvector at `Eₙ`;
    - `⊆` (`eigenspace_subset_span`, *H2*): every `Eₙ`-eigenstate lies in the span.
* `hydrogen_spectral_projection_discrete` — **`range E({Eₙ}) = span { ψ_{nℓm} }`**.  The
  bridge from the abstract spectral measure to the concrete eigenfunctions, via the
  eigenspace characterization `spectralPVM_proj_singleton_eq_self_iff` (*G1*) and the
  fact that the range of the (idempotent) projection is its fixed-point set.
* `hydrogen_spectral_projection_finrank` — `dim range E({Eₙ}) = n²`, the spectral form of
  the degeneracy count (`degenFamily_span_finrank`), transported along the unitary
  `chartRealization`.

These results identify the discrete spectral subspaces of hydrogen and pin their
dimensions, completing the picture
`σ(H) = { Eₙ = −1/(2n²) : n ≥ 1 } ∪ [0,∞)` already established by
`hydrogen_discrete_spectrum`, `hydrogen_essSpectrum`, and
`hydrogen_no_positive_eigenvalues`.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics IV*][reed1978], §XIII.3.
* [Bethe, Salpeter, *Quantum Mechanics of One- and Two-Electron Atoms*][bethesalpeter1957].
-/

noncomputable section

namespace QuantumMechanics.Hydrogen.Spectrum

open MeasureTheory Complex Filter
open scoped Topology NNReal ENNReal Laplacian
open RadialEq Spectra.QuantumMechanics.Hydrogen Spectra.QuantumMechanics.Hydrogen.Decomposition
open Spectra.QuantumMechanics.SpectralTheory

/-! ## The eigenspace identification (`ker(H − Eₙ) = span`) -/

/-- **The `Eₙ`-eigenspace of hydrogen is the span of the `n²` degeneracy states.**

For the `Z = 1` hydrogen Hamiltonian `H`, the set of `Eₙ`-eigenvectors
`{ ψ | ∃ h : ψ ∈ D(H), H ψ = Eₙ ψ }` coincides with the `ℂ`-span of the transported
degeneracy family `chartRealization.symm (degenFamily n ·)`.

Assembles the two inclusions from `SeparatedEigenfunction.lean`: `⊆` is `eigenspace_subset_span`
(*H2*) and `⊇` is `degenFamily_mem_ker` (*H1*) combined with the eigenvalue characterization
`spectralPVM_proj_singleton_eq_self_iff` (*G1*) — the eigenspace, being the range of the spectral
projection, is automatically a subspace, so containing the generators suffices. -/
theorem hydrogen_eigenspace_eq_span (n : ℕ) (hn : 1 ≤ n) :
    {ψ : Spectra.Sobolev.l2R3 |
        ∃ h : ψ ∈ (hydrogenHamiltonian (⟨1, one_pos⟩ : CoulombParams)).domain,
          hydrogenHamiltonian (⟨1, one_pos⟩ : CoulombParams) ⟨ψ, h⟩
            = ((hydrogenEigenvalue n hn : ℝ) : ℂ) • ψ}
      = ↑(Submodule.span ℂ (Set.range (fun i => chartRealization.symm (degenFamily n i)))) := by
  classical
  set hA := hydrogenHamiltonian_isSelfAdjoint (⟨1, one_pos⟩ : CoulombParams) with _hAdef
  -- abbreviation for the spectral projection `E({Eₙ})`
  set E := (PVM.spectralPVM hA).proj {hydrogenEigenvalue n hn}
    (measurableSet_singleton _) with hEdef
  -- the range of the idempotent projection is its fixed-point set
  have hfix : ∀ ψ : Spectra.Sobolev.l2R3,
      ψ ∈ LinearMap.range (E : Spectra.Sobolev.l2R3 →ₗ[ℂ] Spectra.Sobolev.l2R3) ↔ E ψ = ψ := by
    intro ψ
    constructor
    · rintro ⟨x, rfl⟩
      have hidem := (PVM.spectralPVM hA).proj_idem {hydrogenEigenvalue n hn}
        (measurableSet_singleton _)
      have hx := congrArg (fun T : Spectra.Sobolev.l2R3 →L[ℂ] Spectra.Sobolev.l2R3 => T x) hidem
      simpa [ContinuousLinearMap.mul_apply, ← hEdef] using hx
    · intro h; exact ⟨ψ, h⟩
  ext ψ
  simp only [Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · -- `H ψ = Eₙ ψ ⟹ ψ ∈ span`  (this is H2)
    rintro ⟨h, heig⟩
    exact eigenspace_subset_span n hn ⟨ψ, h⟩ heig
  · -- `ψ ∈ span ⟹ H ψ = Eₙ ψ`  (span ⊆ eigenspace = fixed points of `E`)
    intro hψ
    have hψE : E ψ = ψ := by
      -- `ψ ∈ span ≤ range E`, since each generator is `E`-fixed by H1 + G1
      have hspan_le : Submodule.span ℂ
          (Set.range (fun i => chartRealization.symm (degenFamily n i)))
          ≤ LinearMap.range (E : Spectra.Sobolev.l2R3 →ₗ[ℂ] Spectra.Sobolev.l2R3) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, hfix]
        obtain ⟨hmem, heig⟩ := degenFamily_mem_ker n hn i
        exact (spectralPVM_proj_singleton_eq_self_iff hA _).mpr ⟨hmem, heig⟩
      exact (hfix ψ).mp (hspan_le hψ)
    exact (spectralPVM_proj_singleton_eq_self_iff hA ψ).mp hψE

/-! ## Spectral projections -/

/-- **Spectral projection onto the `n`-th hydrogen eigenspace.**

  `range E({Eₙ}) = span { ψ_{nℓm} : 0 ≤ ℓ < n, |m| ≤ ℓ }`

The range of the spectral projection of `H = −½Δ − 1/r` onto the spectral atom `{Eₙ}` is the
`ℂ`-span of the `n²` transported degeneracy eigenfunctions.  Proof: the range of the idempotent
`E({Eₙ})` is its fixed-point set `{ ψ | E ψ = ψ }`, which by the eigenspace characterization
`spectralPVM_proj_singleton_eq_self_iff` (*G1*) equals the operator eigenspace, identified with the
span in `hydrogen_eigenspace_eq_span`. -/
theorem hydrogen_spectral_projection_discrete (n : ℕ) (hn : 1 ≤ n) :
    LinearMap.range
        ((PVM.spectralPVM (hydrogenHamiltonian_isSelfAdjoint (⟨1, one_pos⟩ : CoulombParams))).proj
          {hydrogenEigenvalue n hn} (measurableSet_singleton _) :
          Spectra.Sobolev.l2R3 →ₗ[ℂ] Spectra.Sobolev.l2R3)
      = Submodule.span ℂ (Set.range (fun i => chartRealization.symm (degenFamily n i))) := by
  classical
  set hA := hydrogenHamiltonian_isSelfAdjoint (⟨1, one_pos⟩ : CoulombParams) with _hAdef
  apply Submodule.ext
  intro ψ
  rw [LinearMap.mem_range, ← SetLike.mem_coe, ← hydrogen_eigenspace_eq_span n hn, Set.mem_setOf_eq]
  constructor
  · -- `ψ ∈ range E ⟹ H ψ = Eₙ ψ`
    rintro ⟨x, rfl⟩
    set E := (PVM.spectralPVM hA).proj {hydrogenEigenvalue n hn}
      (measurableSet_singleton _) with hEdef
    have hidem := (PVM.spectralPVM hA).proj_idem {hydrogenEigenvalue n hn}
      (measurableSet_singleton _)
    have hx := congrArg (fun T : Spectra.Sobolev.l2R3 →L[ℂ] Spectra.Sobolev.l2R3 => T x) hidem
    have hfixEx : E (E x) = E x := by simpa [ContinuousLinearMap.mul_apply, ← hEdef] using hx
    exact (spectralPVM_proj_singleton_eq_self_iff hA (E x)).mp hfixEx
  · -- `H ψ = Eₙ ψ ⟹ ψ ∈ range E`
    rintro ⟨h, heig⟩
    refine ⟨ψ, ?_⟩
    exact (spectralPVM_proj_singleton_eq_self_iff hA ψ).mpr ⟨h, heig⟩

/-- **Degeneracy of the `n`-th spectral subspace.**  `dim range E({Eₙ}) = n²`.

The spectral form of `degenFamily_span_finrank`: the dimension of the range of `E({Eₙ})` equals
`n²`.
Transported from the spherical-side degeneracy count along the unitary `chartRealization` (which
maps `span (degenFamily n)` isometrically onto `span (chartRealization.symm ∘ degenFamily n)`,
preserving dimension). -/
theorem hydrogen_spectral_projection_finrank (n : ℕ) (hn : 1 ≤ n) :
    Module.finrank ℂ
        (LinearMap.range
          ((PVM.spectralPVM (hydrogenHamiltonian_isSelfAdjoint (⟨1, one_pos⟩ : CoulombParams))).proj
            {hydrogenEigenvalue n hn} (measurableSet_singleton _) :
            Spectra.Sobolev.l2R3 →ₗ[ℂ] Spectra.Sobolev.l2R3))
      = n ^ 2 := by
  -- the transported family is linearly independent (image of the orthonormal degeneracy family
  -- under the injective linear isometry `chartRealization.symm`), so the dimension of its span is
  -- its cardinality `n²` — mirroring `degenFamily_span_finrank`.
  have hLI : LinearIndependent ℂ (fun i => chartRealization.symm (degenFamily n i)) :=
    (orthonormal_degenFamily n).linearIndependent.map'
      chartRealization.symm.toLinearEquiv.toLinearMap
      (LinearMap.ker_eq_bot.mpr chartRealization.symm.toLinearEquiv.injective)
  rw [hydrogen_spectral_projection_discrete n hn, finrank_span_eq_card hLI, Fintype.card_coe,
    card_degenIndex]

end QuantumMechanics.Hydrogen.Spectrum
