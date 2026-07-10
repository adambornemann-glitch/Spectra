/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Spectrum.Projections
import Spectra.QuantumMechanics.Hydrogen.Spectrum.Discrete
import Spectra.QuantumMechanics.Hydrogen.Spectrum.Continuous.Compact
import Spectra.SpectralTheory.Essential.Discrete

/-!
# Completeness of the hydrogen bound states

The negative-energy spectral subspace of the `Z = 1` hydrogen Hamiltonian is exactly the closed
span of all bound-state eigenfunctions `ψ_{nℓm}`:

  `range E((−∞,0)) = closure (⨆ₙ span {ψ_{nℓm}})`.

This is the across-levels completeness statement (Milestone 2), assembling:

* **H0** (`mem_eigenvalues_of_mem_spectrum_neg`): `σ(H) ∩ (−∞,0) = {Eₙ}` — every spectral point
  below `0` is one of the Bohr eigenvalues.  Proved from the **discreteness theorem**
  (`mem_pointSpectrum_of_mem_spectrum_notMem_essSpectrum`, the hard half of Weyl), since
  `essSpectrum = [0,∞)` (`hydrogen_essSpectrum`) puts everything below `0` outside the essential
  spectrum, and `hydrogen_discrete_spectrum` identifies the resulting eigenvalues.
* the per-level projection theorem **M1** (`hydrogen_spectral_projection_discrete`),
* **G3** (`spectralPVM_proj_eq_zero_of_subset_resolventSet`): the spectral projection vanishes off
  the spectrum,

and the (free) countable additivity of the diagonal spectral measures.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics IV*][reed1978], §XIII.3.
* [Griffiths, *Introduction to Quantum Mechanics*][griffiths2018], §4.2.
-/

noncomputable section

namespace QuantumMechanics.Hydrogen.Spectrum

open MeasureTheory Complex Filter
open scoped Topology NNReal ENNReal Laplacian InnerProductSpace
open RadialEq Spectra.QuantumMechanics.Hydrogen Spectra.QuantumMechanics.Hydrogen.Decomposition
open Spectra.QuantumMechanics.SpectralTheory Spectra.Resolvent Spectra.Essential

/-! ## H0 — the spectrum below zero is exactly the Bohr eigenvalues -/

/-- **Every spectral point below `0` is a Bohr eigenvalue.**  If `E ∈ σ(H)` and `E < 0`, then
`E = Eₙ = −1/(2n²)` for some `n ≥ 1`.  Below the essential spectrum `[0,∞)` the spectrum is
discrete (the discreteness theorem), and `hydrogen_discrete_spectrum` identifies the eigenvalues. -/
theorem mem_eigenvalues_of_mem_spectrum_neg {E : ℝ}
    (hspec : E ∈ Spectra.Resolvent.spectrum (hydrogenHamiltonian ⟨1, one_pos⟩))
    (hEneg : E < 0) : ∃ (n : ℕ) (hn : 1 ≤ n), E = hydrogenEigenvalue n hn := by
  have hne : E ∉ Spectra.Essential.essSpectrum
    (hydrogenHamiltonian_isSelfAdjoint ⟨1, one_pos⟩) := by
    rw [show Spectra.Essential.essSpectrum (hydrogenHamiltonian_isSelfAdjoint ⟨1, one_pos⟩)
        = Set.Ici (0 : ℝ) from hydrogen_essSpectrum ⟨1, one_pos⟩]
    simp only [Set.mem_Ici, not_le]; exact hEneg
  obtain ⟨ψ, hψ0, hψeig⟩ := mem_pointSpectrum_of_mem_spectrum_notMem_essSpectrum
    (hydrogenHamiltonian_isSelfAdjoint ⟨1, one_pos⟩) hspec hne
  obtain ⟨n, hn, hEeq⟩ := (hydrogen_discrete_spectrum ⟨1, one_pos⟩ E hEneg).mp ⟨ψ, hψ0, hψeig⟩
  exact ⟨n, hn, by rw [hEeq, eigenvalue_Z1]⟩

/-! ## Eigenfunction completeness -/

/-- **Completeness of the hydrogen bound states.**

  `closure (⨆ₙ span {ψ_{nℓm} : ℓ < n}) = range E((−∞,0))`.

The closed `ℂ`-span of all bound-state eigenfunctions equals the negative-energy spectral subspace
`range E((−∞,0))` of `H = −½Δ − 1/r`.  Every state of negative energy is a (closed-span) limit of
superpositions of the `ψ_{nℓm}`, and conversely.

The `⊇` inclusion is monotonicity of the spectral projection (`{Eₙ} ⊆ (−∞,0)`); the `⊆` inclusion
is the orthogonal-complement argument: a negative-energy state orthogonal to every bound state has
its diagonal spectral measure supported on the resolvent set (`G3`) off the eigenvalues (`H0`),
hence is `0`. -/
theorem hydrogen_eigenfunction_complete :
    (⨆ n : ℕ, Submodule.span ℂ
        (Set.range (fun i => chartRealization.symm (degenFamily (n + 1) i)))).topologicalClosure
      = LinearMap.range ((PVM.spectralPVM (hydrogenHamiltonian_isSelfAdjoint ⟨1, one_pos⟩)).proj
          (Set.Iio 0) measurableSet_Iio :
          Spectra.Sobolev.l2R3 →ₗ[ℂ] Spectra.Sobolev.l2R3) := by
  classical
  set hA := hydrogenHamiltonian_isSelfAdjoint ⟨1, one_pos⟩ with _hAdef
  set P := PVM.spectralPVM hA with _hPdef
  set Ev : ℕ → ℝ := fun n => hydrogenEigenvalue (n + 1) (by omega) with hEv
  set En : ℕ → (Spectra.Sobolev.l2R3 →L[ℂ] Spectra.Sobolev.l2R3) :=
    fun n => P.proj {Ev n} (measurableSet_singleton _) with _hEn
  set EIio := P.proj (Set.Iio 0) measurableSet_Iio with _hEIio
  -- convert the degeneracy spans to spectral ranges via M1
  have hM1 : ∀ n : ℕ,
      LinearMap.range (En n : Spectra.Sobolev.l2R3 →ₗ[ℂ] Spectra.Sobolev.l2R3)
        = Submodule.span ℂ (Set.range (fun i => chartRealization.symm (degenFamily (n + 1) i))) :=
    fun n => hydrogen_spectral_projection_discrete (n + 1) (by omega)
  rw [show (⨆ n : ℕ, Submodule.span ℂ
        (Set.range (fun i => chartRealization.symm (degenFamily (n + 1) i))))
      = ⨆ n : ℕ, LinearMap.range (En n : Spectra.Sobolev.l2R3 →ₗ[ℂ] Spectra.Sobolev.l2R3)
      from (iSup_congr hM1).symm]
  set K := ⨆ n : ℕ, LinearMap.range (En n : Spectra.Sobolev.l2R3 →ₗ[ℂ] Spectra.Sobolev.l2R3)
    with _hK
  -- `Eₙ < 0` so `{Eₙ} ⊆ (−∞,0)`
  have hEvneg : ∀ n, Ev n < 0 := fun n => hydrogenEigenvalue_neg (n + 1) (by omega)
  have hEvsub : ∀ n, ({Ev n} : Set ℝ) ⊆ Set.Iio 0 := by
    intro n z hz; rw [Set.mem_singleton_iff] at hz; subst hz; exact hEvneg n
  -- `K ≤ range EIio`
  have hKle : K ≤ LinearMap.range (EIio : Spectra.Sobolev.l2R3 →ₗ[ℂ] Spectra.Sobolev.l2R3) := by
    refine iSup_le (fun n => ?_)
    intro y hy
    rw [LinearMap.mem_range] at hy ⊢
    obtain ⟨x, rfl⟩ := hy
    exact ⟨En n x, P.proj_apply_of_subset measurableSet_Iio
      (measurableSet_singleton _) (hEvsub n) x⟩
  -- `range EIio` is closed (range of a continuous idempotent = its fixed-point set)
  have hclosed : IsClosed (LinearMap.range (EIio : Spectra.Sobolev.l2R3 →ₗ[ℂ] Spectra.Sobolev.l2R3)
      : Set Spectra.Sobolev.l2R3) := by
    have hidem : IsIdempotentElem EIio := P.proj_idem (Set.Iio 0) measurableSet_Iio
    have hfixset : (LinearMap.range (EIio : Spectra.Sobolev.l2R3 →ₗ[ℂ] Spectra.Sobolev.l2R3)
        : Set Spectra.Sobolev.l2R3) = {z | EIio z = z} := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        have hw := congrArg (fun T : Spectra.Sobolev.l2R3 →L[ℂ] Spectra.Sobolev.l2R3 => T w) hidem
        simpa [ContinuousLinearMap.mul_apply] using hw
      · intro hz; exact ⟨z, hz⟩
    rw [hfixset]
    exact isClosed_eq EIio.continuous continuous_id
  apply le_antisymm
  · -- closure K ≤ range EIio
    exact Submodule.topologicalClosure_minimal _ hKle hclosed
  · -- range EIio ≤ closure K = Kᗮᗮ
    rw [← Submodule.orthogonal_orthogonal_eq_closure]
    intro ψ hψ
    rw [LinearMap.mem_range] at hψ
    obtain ⟨w, rfl⟩ := hψ
    rw [Submodule.mem_orthogonal]
    intro yv hyv
    -- `yv ⊥ K ⟹ Eₙ-projection of yv is 0 for every n`
    have hEnyv : ∀ n, En n yv = 0 := by
      intro n
      refine P.proj_apply_eq_zero_of_mem_orthogonal (measurableSet_singleton _) ?_
      exact Submodule.orthogonal_le
        (le_iSup (fun n => LinearMap.range (En n : Spectra.Sobolev.l2R3 →ₗ[ℂ] Spectra.Sobolev.l2R3))
          n) hyv
    have hμatom : ∀ n, (P.diag yv) {Ev n} = 0 := fun n =>
      P.diag_apply_eq_zero_of_proj_apply_eq_zero (measurableSet_singleton _) (hEnyv n)
    -- the bridge `hydrogenEigenvalue m = Ev (m-1)`
    have hEv_eq : ∀ (m : ℕ) (hm : 1 ≤ m), hydrogenEigenvalue m hm = Ev (m - 1) := by
      intro m hm
      have hm1 : m - 1 + 1 = m := by omega
      simp only [hEv, hydrogenEigenvalue, hm1]
    -- `EIio yv = 0`
    have hEIioyv : EIio yv = 0 := by
      refine P.proj_apply_eq_zero_of_diag_apply_eq_zero measurableSet_Iio ?_
      haveI := P.diag_finite yv
      set S := Set.range Ev with hS
      have hSmeas : MeasurableSet S := (Set.countable_range Ev).measurableSet
      have hSU : S = ⋃ n, ({Ev n} : Set ℝ) := by
        rw [hS]; ext x; simp [eq_comm]
      have hμS : (P.diag yv) (Set.Iio 0 ∩ S) = 0 := by
        have hle : (P.diag yv) (Set.Iio 0 ∩ S) ≤ ∑' n, (P.diag yv) {Ev n} := by
          refine le_trans (measure_mono Set.inter_subset_right) ?_
          rw [hSU]; exact measure_iUnion_le _
        rw [tsum_congr hμatom, tsum_zero] at hle
        exact le_zero_iff.mp hle
      have hμresolv : (P.diag yv) (Set.Iio 0 \ S) = 0 := by
        have hzero : P.proj (Set.Iio 0 \ S) (measurableSet_Iio.diff hSmeas) = 0 := by
          refine spectralPVM_proj_eq_zero_of_subset_resolventSet hA
            (measurableSet_Iio.diff hSmeas) ?_
          intro lam hlam
          obtain ⟨hlamneg, hlamnotS⟩ := hlam
          by_contra hres
          have hspec : lam ∈ Spectra.Resolvent.spectrum (hydrogenHamiltonian ⟨1, one_pos⟩) := hres
          obtain ⟨m, hm, hmeq⟩ := mem_eigenvalues_of_mem_spectrum_neg hspec (Set.mem_Iio.mp hlamneg)
          exact hlamnotS ⟨m - 1, by rw [← hEv_eq m hm, ← hmeq]⟩
        exact P.diag_apply_eq_zero_of_proj_apply_eq_zero (measurableSet_Iio.diff hSmeas)
          (by rw [hzero]; rfl)
      have hsplit : (P.diag yv) (Set.Iio 0)
          = (P.diag yv) (Set.Iio 0 ∩ S) + (P.diag yv) (Set.Iio 0 \ S) :=
        (measure_inter_add_diff (Set.Iio 0) hSmeas).symm
      rw [hsplit, hμS, hμresolv, add_zero]
    -- conclude `⟪yv, EIio w⟫ = 0`
    have hadj : ContinuousLinearMap.adjoint EIio = EIio := by
      have := P.isSelfAdjoint_proj (Set.Iio 0) measurableSet_Iio
      rwa [ContinuousLinearMap.isSelfAdjoint_iff'] at this
    calc inner ℂ yv ((EIio : Spectra.Sobolev.l2R3 →ₗ[ℂ] Spectra.Sobolev.l2R3) w)
        = inner ℂ yv (EIio w) := rfl
      _ = inner ℂ (ContinuousLinearMap.adjoint EIio yv) w :=
          (ContinuousLinearMap.adjoint_inner_left EIio w yv).symm
      _ = inner ℂ (EIio yv) w := by rw [hadj]
      _ = inner ℂ (0 : Spectra.Sobolev.l2R3) w := by rw [hEIioyv]
      _ = 0 := inner_zero_left _

end QuantumMechanics.Hydrogen.Spectrum
