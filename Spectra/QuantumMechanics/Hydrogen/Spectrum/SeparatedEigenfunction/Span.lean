/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Spectrum.SeparatedEigenfunction.Eigenpair

/-!
# Separated hydrogen eigenfunctions: spanning the eigenspace

This file proves the reverse inclusion: every Cartesian eigenstate at the hydrogen
energy `E_n` lies in the span of the transported degeneracy family.

## Main statements

* `eigenspace_subset_span` — the H2 deliverable: every `Z = 1` hydrogen eigenstate `ψ` at the
  energy `Eₙ` lies in the `ℂ`-span of the `n²` transported degeneracy states, i.e. the reverse
  inclusion `ker(H − Eₙ) ⊆ span`.
* `coeffFun_dichotomy` — the per-sector dichotomy for any magnetic index: each `⟨ℓ, M⟩` angular
  coefficient of an `Eₙ`-eigenstate is `radialMeasure`-a.e. either zero or (when `ℓ < n`) a
  complex scalar multiple of the radial eigenfunction `R_{nℓ}`.
* `sectorEmbedding_w_mem_span` — each reassembled summand of the spherical decomposition lies in
  the degeneracy span and vanishes once `ℓ ≥ n`, so the summand family is finitely supported.
-/

noncomputable section

namespace QuantumMechanics.Hydrogen.Spectrum

open MeasureTheory MeasureTheory.Measure Real Complex Filter InnerProductSpace
open QuantumMechanics.Hydrogen.RadialEq
open Spectra.QuantumMechanics.Hydrogen Spectra.SphericalHarmonics Spectra.Sobolev
open Spectra.QuantumMechanics.Hydrogen.Decomposition
open Spectra.QuantumMechanics.Hydrogen.Radial (laguerrePolynomial laguerre_smooth)
open scoped Topology ContDiff Laplacian

/-! ## H2 — every `Eₙ` eigenstate lies in the span of the `n²` degeneracy states

The reverse inclusion `ker(H − Eₙ) ⊆ span(degenFamily n)`.  The forward machinery
(`SectorProjection.lean`) gives, sector by sector, a *classical* `C²` radial solution of the
reduced radial eigen-equation at `Eₙ`; the quantization/uniqueness theorems
(`radial_quantization` + `bound_state_eq_smul_eigenfunction`) then force each sector coefficient
to be either zero (if `ℓ ≥ n`) or a scalar multiple of `R_{nℓ}` (if `ℓ < n`).  The
Hilbert-sum reassembly collapses the (finitely-supported) decomposition into a finite span
combination, which `chartRealization.symm` transports back to the Cartesian side. -/

/-- **Injectivity of the energy levels.** `Eₙ = Eₙ' ⟹ n = n'` for `n, n' ≥ 1`
(immediate from strict monotonicity). -/
lemma hydrogenEigenvalue_inj {n n' : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n')
    (h : hydrogenEigenvalue n hn = hydrogenEigenvalue n' hn') : n = n' := by
  rcases lt_trichotomy n n' with hlt | heq | hgt
  · exact absurd h (hydrogenEigenvalue_strictMono hn hn' hlt).ne
  · exact heq
  · exact absurd h.symm (hydrogenEigenvalue_strictMono hn' hn hgt).ne

/-- **Log-coordinate a.e. transport.**  A volume-a.e. equality of `s ↦ f(eˢ)` with `h` transports
to a `radialMeasure`-a.e. equality of `f` with `r ↦ h(log r)`.  (Inverse of the measure-transport
in `exp_ae_ne_of_radial_ae_ne`: the bad set in `r` is the `exp`-image of the volume-null bad set in
`s`, and `radialMeasure ≪ volume`.) -/
lemma radial_ae_of_logCoord_ae {f h : ℝ → ℝ}
    (hae : (fun s => f (Real.exp s)) =ᵐ[volume] h) :
    f =ᵐ[radialMeasure] fun r => h (Real.log r) := by
  have hN : volume {s | ¬ f (Real.exp s) = h s} = 0 := by
    have := hae; rw [Filter.EventuallyEq, ae_iff] at this; simpa using this
  have himg : volume (Real.exp '' {s | ¬ f (Real.exp s) = h s}) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      volume Real.differentiable_exp.differentiableOn hN
  have hac : radialMeasure ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans
      (Measure.restrict_le_self).absolutelyContinuous
  have hIoic : radialMeasure (Set.Ioi (0 : ℝ))ᶜ = 0 := by
    have h := ae_radial_mem_Ioi; rwa [ae_iff] at h
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null
    (show {r | ¬ f r = h (Real.log r)} ⊆
      Real.exp '' {s | ¬ f (Real.exp s) = h s} ∪ (Set.Ioi 0)ᶜ from ?_) ?_
  · intro r hr
    by_cases hr0 : 0 < r
    · exact Or.inl ⟨Real.log r, by simpa [Real.exp_log hr0] using hr, Real.exp_log hr0⟩
    · exact Or.inr (by simpa using hr0)
  · exact measure_union_null (hac himg) hIoic

/-- **Per-sector dichotomy at a *known* level `n`.** A classical `C²`, `L²`, origin-regular
solution `ψ` of the reduced radial eigen-equation `H_ℓ ψ = Eₙ ψ` (at the *given* `Eₙ`) is
*either* identically zero on `(0,∞)`, *or* `ℓ < n` and `ψ = c·R_{nℓ}` for some constant `c`.
Specialization of the general `RadialEq.radial_bound_state_unique` (which quantizes the energy of
a nonzero bound state) to a known `n`, using injectivity of the energy levels
(`hydrogenEigenvalue_inj`) to pin `n' = n`. -/
lemma radial_bound_state_dichotomy_at (ℓ n : ℕ) (hn1 : 1 ≤ n) (ψ : ℝ → ℝ)
    (hL2 : RadialL2 ψ)
    (hψ1 : ∀ r, 0 < r → HasDerivAt ψ (deriv ψ r) r)
    (hψ2 : ∀ r, 0 < r → HasDerivAt (deriv ψ) (deriv^[2] ψ r) r)
    (hψ0 : Filter.Tendsto (fun r => r * ψ r) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (heq : ∀ r, 0 < r → RadialEq.radialHamiltonian ℓ ψ r = hydrogenEigenvalue n hn1 * ψ r) :
    (∀ r, 0 < r → ψ r = 0) ∨
      (∃ (hℓn : ℓ + 1 ≤ n) (c : ℝ), ∀ r, 0 < r → ψ r = c *
        hydrogenRadialWavefunction n ℓ hℓn r) := by
  rcases RadialEq.radial_bound_state_unique ℓ (hydrogenEigenvalue n hn1)
      (hydrogenEigenvalue_neg n hn1) ψ hL2 hψ1 hψ2 hψ0 heq with hzero | ⟨n', hn', c, hEeq, hc⟩
  · exact Or.inl hzero
  · -- injectivity forces `n' = n`, so `ℓ + 1 ≤ n`
    right
    have hnn' : n = n' := hydrogenEigenvalue_inj hn1 (by omega) hEeq
    subst hnn'
    exact ⟨hn', c, hc⟩

/-- **Step A — bridge to the radial coefficient.**  The `i`-th component of the spherical
decomposition of `Φ` is the radial `L²` element built from the angular coefficient `coeffFun i Φ`.
Proved by `ext_inner_left`: pairing the `i`-component against an arbitrary `R` reduces, through
the unitary `sphericalDecomposition` (`lp.inner_single_left`, `inner_map_map`,
`sphericalDecomposition_symm_single`) and the Fubini identity
`inner_sectorEmbedding_eq_integral_coeffFun`, to the radial pairing of `R` against `coeffFun i Φ` -/
lemma sphericalDecomposition_eq_toLp_coeffFun (Φ : Decomposition.l2R3) (i : HarmonicIdx) :
    sphericalDecomposition Φ i = (memLp_coeffFun i Φ).toLp (coeffFun i Φ) := by
  refine ext_inner_left ℂ (fun R => ?_)
  -- LHS: ⟪R, w i⟫ = ⟪single i R, w⟫ = ⟪symm (single i R), Φ⟫ = ⟪sectorEmbedding i R, Φ⟫
  have h1 : inner ℂ R (sphericalDecomposition Φ i)
      = inner ℂ (lp.single 2 i R) (sphericalDecomposition Φ) :=
    (lp.inner_single_left i R (sphericalDecomposition Φ)).symm
  have h2 : inner ℂ (lp.single 2 i R) (sphericalDecomposition Φ)
      = inner ℂ (sphericalDecomposition.symm (lp.single 2 i R)) Φ := by
    have := sphericalDecomposition.symm.inner_map_map (lp.single 2 i R) (sphericalDecomposition Φ)
    rw [LinearIsometryEquiv.symm_apply_apply] at this
    exact this.symm
  rw [h1, h2, sphericalDecomposition_symm_single,
    inner_sectorEmbedding_eq_integral_coeffFun]
  -- RHS: ⟪R, toLp (coeffFun i Φ)⟫ = ∫ conj(R r)·coeffFun i Φ r ∂radialMeasure
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_coeffFun i Φ).coeFn_toLp] with r hr
  rw [hr, RCLike.inner_apply']

/-- **Step B (real, single functional).**  For an `Eₙ`-eigenpair `ψ'`, a sector `⟨ℓ, -(m:ℤ)⟩`
(`m ≤ ℓ`), and a real-linear functional `L`, the radial profile `r ↦ L(coeffFun ⟨ℓ,-(m:ℤ)⟩ Φ' r)`
is `radialMeasure`-a.e. *either* zero *or* (when `ℓ < n`) a real scalar multiple of `R_{nℓ}`.  This
is `forward_eigenvalue`'s sector analysis run with the *given* eigenvalue and closed with the
`radial_bound_state_unique` dichotomy in place of `radial_quantization_Z`. -/
lemma sector_reIm_dichotomy (n : ℕ) (hn1 : 1 ≤ n)
    (ψ' : (hydrogenHamiltonian ⟨1, one_pos⟩).domain)
    (heig' : hydrogenHamiltonian ⟨1, one_pos⟩ ψ'
      = ((hydrogenEigenvalue n hn1 : ℝ) : ℂ) • (ψ' : Spectra.Sobolev.l2R3))
    (ℓ m : ℕ) (hm : m ≤ ℓ) (L : ℂ →L[ℝ] ℝ) :
    (∀ᵐ r ∂radialMeasure, L (coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
        (chartRealization (ψ' : Spectra.Sobolev.l2R3)) r) = 0) ∨
      (∃ (hℓn : ℓ + 1 ≤ n) (c : ℝ), ∀ᵐ r ∂radialMeasure,
        L (coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
          (chartRealization (ψ' : Spectra.Sobolev.l2R3)) r)
          = c * hydrogenRadialWavefunction n ℓ hℓn r) := by
  classical
  set Φ' := chartRealization (ψ' : Spectra.Sobolev.l2R3) with _hΦ'
  set g : ℝ → ℂ := coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩ Φ' with hg
  set E := hydrogenEigenvalue n hn1 with _hE
  -- raw classical `C²` solution of the log-coordinate ODE (mirrors `forward_eigenvalue`)
  obtain ⟨c₀, hae, hc1, hc2, hode⟩ :=
    Spectra.RadialRegularity.classical_of_weak_ode
      (locallyIntegrable_comp_exp g (memLp_coeffFun _ _) L)
      (b := fun s => (ℓ : ℝ) * ((ℓ : ℝ) + 1)
        - 2 * (⟨1, one_pos⟩ : CoulombParams).Z * Real.exp s - 2 * E * Real.exp (2 * s))
      (by fun_prop)
      (sector_sweak ⟨1, one_pos⟩ E ψ' heig' ℓ m hm L)
  obtain ⟨h1, h2, h3⟩ := radial_classical_of_logCoord ℓ (⟨1, one_pos⟩ : CoulombParams).Z E c₀
    hc1 hc2 hode
  set ψr : ℝ → ℝ := fun r => c₀ (Real.log r) with hψr
  have hZ1 : (⟨1, one_pos⟩ : CoulombParams).Z = 1 := rfl
  -- the radial Hamiltonian ODE `H_ℓ ψr = Eₙ ψr` (from `h3`, using `Z = 1`)
  have hHeq : ∀ r, 0 < r → RadialEq.radialHamiltonian ℓ ψr r = E * ψr r := by
    intro r hr
    have h3r := h3 r hr
    rw [hZ1] at h3r
    simp only [RadialEq.radialHamiltonian]
    linarith [h3r]
  -- `ψr ∈ RadialL2`, C¹/C², origin-regular
  have hL2 : RadialL2 ψr := sector_radialL2 g (memLp_coeffFun _ _) L c₀ hae
  have hint : Integrable (fun s => Real.exp s * c₀ s ^ 2) volume :=
    (sector_coulomb_L2 ⟨1, one_pos⟩ ψ' ℓ m hm L).congr
      (by filter_upwards [hae] with s hs; rw [hs])
  have hψ0 : Filter.Tendsto (fun r => r * ψr r) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    radial_bc_of_logCoord ℓ (⟨1, one_pos⟩ : CoulombParams).Z E (by rw [hZ1]; norm_num)
      (hydrogenEigenvalue_neg n hn1) c₀ hc1 hc2 hode hint
  -- the a.e. link `L(g r) =ᵐ[radialMeasure] ψr r`
  have hlink : (fun r => L (g r)) =ᵐ[radialMeasure] ψr :=
    radial_ae_of_logCoord_ae (h := c₀) hae
  -- run the radial dichotomy
  rcases radial_bound_state_dichotomy_at ℓ n hn1 ψr hL2 h1 h2 hψ0 hHeq with hzero | ⟨hℓn, c, hc⟩
  · left
    filter_upwards [hlink, ae_radial_mem_Ioi] with r hrl hr0
    rw [hg] at hrl ⊢; rw [hrl, hψr]
    exact hzero r (Set.mem_Ioi.mp hr0)
  · right
    refine ⟨hℓn, c, ?_⟩
    filter_upwards [hlink, ae_radial_mem_Ioi] with r hrl hr0
    rw [hg] at hrl ⊢; rw [hrl, hψr]
    exact hc r (Set.mem_Ioi.mp hr0)

/-- **Step B (complex coefficient, non-positive index).**  Recombining the real and imaginary
dichotomies (`sector_reIm_dichotomy` at `reCLM`, `imCLM`): the `⟨ℓ,-(m:ℤ)⟩` angular coefficient of
an `Eₙ`-eigenpair is `radialMeasure`-a.e. *either* zero *or* (when `ℓ < n`) a complex scalar
multiple of `R_{nℓ}`. -/
lemma sector_complex_dichotomy (n : ℕ) (hn1 : 1 ≤ n)
    (ψ' : (hydrogenHamiltonian ⟨1, one_pos⟩).domain)
    (heig' : hydrogenHamiltonian ⟨1, one_pos⟩ ψ'
      = ((hydrogenEigenvalue n hn1 : ℝ) : ℂ) • (ψ' : Spectra.Sobolev.l2R3))
    (ℓ m : ℕ) (hm : m ≤ ℓ) :
    (coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
        (chartRealization (ψ' : Spectra.Sobolev.l2R3)) =ᵐ[radialMeasure] 0) ∨
      (∃ (hℓn : ℓ + 1 ≤ n) (c : ℂ),
        coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
          (chartRealization (ψ' : Spectra.Sobolev.l2R3))
          =ᵐ[radialMeasure] fun r => c * Rc n ℓ hℓn r) := by
  classical
  set g : ℝ → ℂ := coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
    (chartRealization (ψ' : Spectra.Sobolev.l2R3)) with hg
  have hre := sector_reIm_dichotomy n hn1 ψ' heig' ℓ m hm Complex.reCLM
  have him := sector_reIm_dichotomy n hn1 ψ' heig' ℓ m hm Complex.imCLM
  rw [← hg] at hre him
  by_cases hz : g =ᵐ[radialMeasure] 0
  · exact Or.inl hz
  · right
    -- some part is nonzero, so its dichotomy is the nonzero branch, fixing `ℓ < n`
    obtain ⟨L, hLeq, hLne⟩ := exists_reIm_comp_ne_zero (μ := radialMeasure) g hz
    -- extract `ℓ < n` and real coefficients for both re and im
    have hgetℓ : ℓ + 1 ≤ n := by
      rcases hLeq with rfl | rfl
      · rcases hre with h | ⟨hℓn, _, _⟩
        · exact absurd h hLne
        · exact hℓn
      · rcases him with h | ⟨hℓn, _, _⟩
        · exact absurd h hLne
        · exact hℓn
    refine ⟨hgetℓ, ?_⟩
    -- real coefficients `cre`, `cim` (zero branch ↦ coefficient 0)
    obtain ⟨cre, hcre⟩ : ∃ cre : ℝ, ∀ᵐ r ∂radialMeasure,
        Complex.reCLM (g r) = cre * hydrogenRadialWavefunction n ℓ hgetℓ r := by
      rcases hre with h | ⟨hℓn', c, hc⟩
      · exact ⟨0, by filter_upwards [h] with r hr; rw [hr]; simp⟩
      · exact ⟨c, by simpa [Subsingleton.elim hℓn' hgetℓ] using hc⟩
    obtain ⟨cim, hcim⟩ : ∃ cim : ℝ, ∀ᵐ r ∂radialMeasure,
        Complex.imCLM (g r) = cim * hydrogenRadialWavefunction n ℓ hgetℓ r := by
      rcases him with h | ⟨hℓn', c, hc⟩
      · exact ⟨0, by filter_upwards [h] with r hr; rw [hr]; simp⟩
      · exact ⟨c, by simpa [Subsingleton.elim hℓn' hgetℓ] using hc⟩
    refine ⟨((cre : ℂ) + (cim : ℂ) * Complex.I), ?_⟩
    filter_upwards [hcre, hcim] with r hr hi
    have hrer : (g r).re = cre * hydrogenRadialWavefunction n ℓ hgetℓ r := by simpa using hr
    have himr : (g r).im = cim * hydrogenRadialWavefunction n ℓ hgetℓ r := by simpa using hi
    apply Complex.ext
    · simp only [Rc, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      rw [hrer]; ring
    · simp only [Rc, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, Complex.mul_im]
      rw [himr]; ring

/-- **Step B (general integer `M`).**  The full per-sector dichotomy for *any* magnetic index
`M ∈ {−ℓ,…,ℓ}` of the spherical decomposition of an `Eₙ`-eigenstate: the `⟨ℓ,M⟩` angular
coefficient of `Φ = chartRealization ψ` is `radialMeasure`-a.e. *either* zero *or* (when `ℓ < n`) a
complex scalar multiple of `R_{nℓ}`.  Non-negative `M` is reduced to the native non-positive index
of `sector_complex_dichotomy` via conjugation (`coeffFun_star`, `hydrogenHamiltonian_star`). -/
lemma coeffFun_dichotomy (n : ℕ) (hn1 : 1 ≤ n)
    (ψ : (hydrogenHamiltonian ⟨1, one_pos⟩).domain)
    (heig : hydrogenHamiltonian ⟨1, one_pos⟩ ψ
      = ((hydrogenEigenvalue n hn1 : ℝ) : ℂ) • (ψ : Spectra.Sobolev.l2R3))
    (ℓ : ℕ) (M : ℤ) (hM : |M| ≤ (ℓ : ℤ)) :
    (coeffFun ⟨ℓ, M, hM⟩ (chartRealization (ψ : Spectra.Sobolev.l2R3)) =ᵐ[radialMeasure] 0) ∨
      (∃ (hℓn : ℓ + 1 ≤ n) (c : ℂ),
        coeffFun ⟨ℓ, M, hM⟩ (chartRealization (ψ : Spectra.Sobolev.l2R3))
          =ᵐ[radialMeasure] fun r => c * Rc n ℓ hℓn r) := by
  classical
  rcases le_total M 0 with hMle | hMge
  · -- `M ≤ 0`: native non-positive index, `m = (-M).toNat`
    obtain ⟨m, hmM⟩ : ∃ m : ℕ, (m : ℤ) = -M := ⟨(-M).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hMeq : M = -(m : ℤ) := by omega
    have hm : m ≤ ℓ := by rw [abs_le] at hM; omega
    -- the index `⟨ℓ, M, hM⟩` *is* `⟨ℓ, -(m:ℤ), _⟩`
    have hidx : (⟨ℓ, M, hM⟩ : HarmonicIdx)
        = ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩ := by
      apply HarmonicIdx.ext <;> simp [hMeq]
    rw [hidx]
    rcases sector_complex_dichotomy n hn1 ψ heig ℓ m hm with h | ⟨hℓn, c, hc⟩
    · exact Or.inl h
    · exact Or.inr ⟨hℓn, c, hc⟩
  · -- `M ≥ 0`: conjugate trick via `star ψ`, `m = M.toNat`
    obtain ⟨m, hmM⟩ : ∃ m : ℕ, (m : ℤ) = M := ⟨M.toNat, Int.toNat_of_nonneg hMge⟩
    have hm : m ≤ ℓ := by rw [abs_le] at hM; omega
    have hmI : |(m : ℤ)| ≤ (ℓ : ℤ) := by rw [hmM]; exact hM
    -- the index `⟨ℓ, M, hM⟩` is `⟨ℓ, (m:ℤ), _⟩`
    have hidx : (⟨ℓ, M, hM⟩ : HarmonicIdx) = ⟨ℓ, (m : ℤ), hmI⟩ := by
      apply HarmonicIdx.ext <;> simp [hmM]
    rw [hidx]
    -- the Condon–Shortley constant
    set κ : ℝ := sphericalNorm ℓ (-(m : ℤ)) * reflectionFactor ℓ (-(m : ℤ))
        / (sphericalNorm ℓ (m : ℤ) * reflectionFactor ℓ (m : ℤ)) with _hκ
    have hκne : κ ≠ 0 := div_ne_zero
      (mul_ne_zero (sphericalNorm_pos _ _).ne' (reflectionFactor_ne_zero _ _))
      (mul_ne_zero (sphericalNorm_pos _ _).ne' (reflectionFactor_ne_zero _ _))
    -- `star ψ` is an eigenpair at `Eₙ`; run the dichotomy on its `-(m:ℤ)` coefficient
    set ψs : (hydrogenHamiltonian ⟨1, one_pos⟩).domain :=
      ⟨star (ψ : Spectra.Sobolev.l2R3), memSobolevH2_star _ ψ.2⟩ with _hψs
    have heigs : hydrogenHamiltonian ⟨1, one_pos⟩ ψs
        = ((hydrogenEigenvalue n hn1 : ℝ) : ℂ) • (ψs : Spectra.Sobolev.l2R3) :=
      hydrogenHamiltonian_star ⟨1, one_pos⟩ (hydrogenEigenvalue n hn1) ψ heig
    -- `coeffFun_star`: the `-(m:ℤ)` coefficient of `star ψ` is `κ·conj` of the `m` coefficient of ψ
    have hcs := coeffFun_star ℓ m hm (ψ : Spectra.Sobolev.l2R3)
    rcases sector_complex_dichotomy n hn1 ψs heigs ℓ m hm with h | ⟨hℓn, c, hc⟩
    · -- the `-(m:ℤ)` coefficient of `star ψ` is a.e. 0, hence so is the `m` coefficient of ψ
      left
      -- `hcs : coeffFun⟨ℓ,-(m)⟩(chartReal (star ψ)) =ᵐ κ·conj(coeffFun⟨ℓ,m⟩(chartReal ψ))`
      have hzero : (fun r => (κ : ℂ) *
          starRingEnd ℂ (coeffFun ⟨ℓ, (m : ℤ), hmI⟩
            (chartRealization (ψ : Spectra.Sobolev.l2R3)) r)) =ᵐ[radialMeasure] 0 :=
        hcs.symm.trans h
      filter_upwards [hzero] with r hr
      simp only [Pi.zero_apply] at hr ⊢
      rcases mul_eq_zero.mp hr with hk | hc0
      · exact absurd (Complex.ofReal_eq_zero.mp hk) hκne
      · rw [starRingEnd_apply, star_eq_zero] at hc0; exact hc0
    · -- the `-(m:ℤ)` coefficient of `star ψ` is `c·Rc`; conjugate back
      right
      refine ⟨hℓn, (κ : ℂ)⁻¹ * starRingEnd ℂ c, ?_⟩
      -- from `hcs` and `hc`: `κ·conj(coeffFun⟨ℓ,m⟩ Φ) =ᵐ c·Rc`
      -- so `coeffFun⟨ℓ,m⟩ Φ =ᵐ conj(κ⁻¹c)·Rc`
      have hcomb : (fun r => (κ : ℂ) *
          starRingEnd ℂ (coeffFun ⟨ℓ, (m : ℤ), hmI⟩
            (chartRealization (ψ : Spectra.Sobolev.l2R3)) r))
          =ᵐ[radialMeasure] fun r => c * Rc n ℓ hℓn r := hcs.symm.trans hc
      filter_upwards [hcomb] with r hr
      have hκc : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκne
      -- solve for the `m` coefficient and conjugate (Rc is real)
      have hval : starRingEnd ℂ (coeffFun ⟨ℓ, (m : ℤ), hmI⟩
          (chartRealization (ψ : Spectra.Sobolev.l2R3)) r) = (κ : ℂ)⁻¹ * (c * Rc n ℓ hℓn r) := by
        field_simp at hr ⊢
        linear_combination hr
      have hRcconj : starRingEnd ℂ (Rc n ℓ hℓn r) = Rc n ℓ hℓn r := by
        simp [Rc, Complex.conj_ofReal]
      have := congrArg (starRingEnd ℂ) hval
      rw [Complex.conj_conj] at this
      rw [this]
      simp only [map_mul, map_inv₀, hRcconj, Complex.conj_ofReal]
      ring

/-- **Index map into the degeneracy family.**  For `ℓ < n` and `|M| ≤ ℓ`, the named eigenfunction
`ψ_{nℓM}` is literally a member of `degenFamily n` (at index `⟨⟨ℓ, (M+ℓ).toNat⟩, _⟩`), hence lies
in the span of its range. -/
lemma hydrogenEigenfunction_mem_span (n ℓ : ℕ) (M : ℤ) (hℓn : ℓ + 1 ≤ n) (hM : |M| ≤ (ℓ : ℤ)) :
    hydrogenEigenfunction n ℓ M hℓn hM ∈ Submodule.span ℂ (Set.range (degenFamily n)) := by
  -- the index `j = (M + ℓ).toNat ∈ {0,…,2ℓ}`
  set j : ℕ := (M + ℓ).toNat with hj
  have hjmem : ⟨ℓ, j⟩ ∈ degenIndex n := by
    simp only [degenIndex, Finset.mem_sigma, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have : |M| ≤ (ℓ : ℤ) := hM
    rw [abs_le] at this
    omega
  set idx : ↥(degenIndex n) := ⟨⟨ℓ, j⟩, hjmem⟩ with hidx
  -- `degenFamily n idx = hydrogenEigenfunction n ℓ ((j:ℤ)-ℓ) _ _`, and `(j:ℤ)-ℓ = M`
  have hjM : ((j : ℤ) - ℓ) = M := by
    have : |M| ≤ (ℓ : ℤ) := hM
    rw [abs_le] at this
    simp only [hj]
    omega
  have heq : degenFamily n idx = hydrogenEigenfunction n ℓ M hℓn hM := by
    simp only [degenFamily, hidx]
    -- the magnetic index agrees; the proof arguments are irrelevant
    have hidxeq : (⟨ℓ, (j : ℤ) - ℓ, (degenIndex_bounds idx).2⟩ : HarmonicIdx)
        = ⟨ℓ, M, hM⟩ := HarmonicIdx.ext rfl (by simpa using hjM)
    simp only [hydrogenEigenfunction]
    rw [hidxeq]
  rw [← heq]
  exact Submodule.subset_span ⟨idx, rfl⟩

/-- **Step C, per sector.**  Each reassembled summand `sectorEmbedding i (w i)` of an
`Eₙ`-eigenstate's spherical decomposition lies in the span of the degeneracy family, *and* it
vanishes whenever `i.1 ≥ n` (so the family `i ↦ sectorEmbedding i (w i)` is finitely supported).
Combining Step A (`w i = toLp (coeffFun i Φ)`), the general-`M` dichotomy (`coeffFun_dichotomy`),
and `radialLp_coeFn` (`⇑(radialLp) =ᵐ R_{nℓ}`): the `i`-component is `0` or `c • ψ_{nℓM}`. -/
lemma sectorEmbedding_w_mem_span (n : ℕ) (hn1 : 1 ≤ n)
    (ψ : (hydrogenHamiltonian ⟨1, one_pos⟩).domain)
    (heig : hydrogenHamiltonian ⟨1, one_pos⟩ ψ
      = ((hydrogenEigenvalue n hn1 : ℝ) : ℂ) • (ψ : Spectra.Sobolev.l2R3))
    (i : HarmonicIdx) :
    sectorEmbedding i (sphericalDecomposition
        (chartRealization (ψ : Spectra.Sobolev.l2R3)) i)
      ∈ Submodule.span ℂ (Set.range (degenFamily n)) ∧
    (n ≤ i.1 → sphericalDecomposition (chartRealization (ψ : Spectra.Sobolev.l2R3)) i = 0) := by
  classical
  obtain ⟨ℓ, M, hM⟩ := i
  set Φ := chartRealization (ψ : Spectra.Sobolev.l2R3) with _hΦ
  -- Step A: the component is the `toLp` of the angular coefficient
  have hA := sphericalDecomposition_eq_toLp_coeffFun Φ ⟨ℓ, M, hM⟩
  rcases coeffFun_dichotomy n hn1 ψ heig ℓ M hM with hzero | ⟨hℓn, c, hc⟩
  · -- zero component
    have hw0 : sphericalDecomposition Φ ⟨ℓ, M, hM⟩ = 0 := by
      rw [hA]
      refine Lp.ext ?_
      filter_upwards [(memLp_coeffFun ⟨ℓ, M, hM⟩ Φ).coeFn_toLp, hzero,
        Lp.coeFn_zero ℂ 2 radialMeasure]
        with r h1 h2 h3
      rw [h1, h2, h3]
    refine ⟨?_, fun _ => hw0⟩
    rw [hw0, map_zero]
    exact Submodule.zero_mem _
  · -- `c • radialLp` component, `ℓ < n`
    have hw : sphericalDecomposition Φ ⟨ℓ, M, hM⟩ = c • radialLp n ℓ hℓn := by
      rw [hA]
      refine Lp.ext ?_
      filter_upwards [(memLp_coeffFun ⟨ℓ, M, hM⟩ Φ).coeFn_toLp, hc,
        Lp.coeFn_smul c (radialLp n ℓ hℓn), radialLp_coeFn n ℓ hℓn] with r h1 h2 h3 h4
      rw [h1, h2, h3, Pi.smul_apply, h4, smul_eq_mul, Rc]
    refine ⟨?_, fun hle => absurd hℓn (by simp only at hle; omega)⟩
    rw [hw, map_smul]
    refine Submodule.smul_mem _ c ?_
    -- `sectorEmbedding ⟨ℓ,M⟩ (radialLp n ℓ hℓn) = hydrogenEigenfunction n ℓ M`
    have : sectorEmbedding ⟨ℓ, M, hM⟩ (radialLp n ℓ hℓn)
        = hydrogenEigenfunction n ℓ M hℓn hM := rfl
    rw [this]
    exact hydrogenEigenfunction_mem_span n ℓ M hℓn hM

/-- The set of harmonic indices with `ℓ < n` is finite (it injects into
`range n ×ˢ Icc (-n) n` via `i ↦ (i.1, i.2.1)`). -/
lemma finite_harmonicIdx_lt (n : ℕ) : {i : HarmonicIdx | (i.1 : ℕ) < n}.Finite := by
  classical
  apply Set.Finite.of_finite_image (f := fun i : HarmonicIdx => (i.1, i.2.1))
  · refine Set.Finite.subset
      ((Set.finite_Iio n).prod (Set.finite_Icc (-(n : ℤ)) n)) ?_
    rintro _ ⟨⟨ℓ, M, hM⟩, hmem, rfl⟩
    simp only [Set.mem_setOf_eq] at hmem
    refine Set.mem_prod.mpr ⟨hmem, ?_⟩
    rw [Set.mem_Icc, ← abs_le]
    exact le_trans hM (by exact_mod_cast hmem.le)
  · intro a _ b _ hab
    exact HarmonicIdx.ext (congrArg Prod.fst hab) (congrArg Prod.snd hab)

/-- **★ H2 deliverable.**  Every `Z = 1` hydrogen eigenstate `ψ` at the energy `Eₙ` lies in the
`ℂ`-span of the `n²` transported degeneracy states `chartRealization.symm (degenFamily n ·)`.

This is the reverse inclusion `ker(H − Eₙ) ⊆ span`, completing (with `degenFamily_mem_ker`, the
forward `⊇`) the identification of the `Eₙ`-eigenspace with the degeneracy span.  The proof: pass
to the spherical side `Φ = chartRealization ψ`, decompose `Φ = ∑' i, sectorEmbedding i (w i)` in the
Hilbert sum; each summand is either `0` (when `ℓ ≥ n`) or a multiple of a degeneracy state (when
`ℓ < n`), and the family is finitely supported, so the sum collapses to a finite span combination,
which `chartRealization.symm` transports back. -/
theorem eigenspace_subset_span (n : ℕ) (hn : 1 ≤ n)
    (ψ : (hydrogenHamiltonian ⟨1, one_pos⟩).domain)
    (heig : hydrogenHamiltonian ⟨1, one_pos⟩ ψ
      = ((hydrogenEigenvalue n hn : ℝ) : ℂ) • (ψ : Spectra.Sobolev.l2R3)) :
    (ψ : Spectra.Sobolev.l2R3)
      ∈ Submodule.span ℂ (Set.range (fun i => chartRealization.symm (degenFamily n i))) := by
  classical
  set Φ := chartRealization (ψ : Spectra.Sobolev.l2R3) with hΦ
  set w := sphericalDecomposition Φ with hw
  set f : HarmonicIdx → Decomposition.l2R3 := fun i => sectorEmbedding i (w i) with hf
  -- the per-sector data: each summand lies in the span; support is within `{ℓ < n}`
  have hsector := fun i => sectorEmbedding_w_mem_span n hn ψ heig i
  -- Step C reassembly on the *spherical* side: `Φ = ∑' i, f i`
  have hsum : Φ = ∑' i, f i := by
    have h := sphericalDecomposition_symm_apply w
    rw [hw, LinearIsometryEquiv.symm_apply_apply] at h
    rw [hΦ] at h ⊢
    exact h
  -- finite support of `f`
  have hsupp : Function.support f ⊆ {i : HarmonicIdx | (i.1 : ℕ) < n} := by
    intro i hi
    by_contra hlt
    simp only [Set.mem_setOf_eq, not_lt] at hlt
    exact hi (by simp only [hf]; rw [(hsector i).2 hlt, map_zero])
  obtain ⟨T, hT⟩ := (finite_harmonicIdx_lt n).subset hsupp |>.exists_finset_coe
  -- the tsum collapses to a finite sum over `T`
  have hΦsum : Φ = ∑ i ∈ T, f i := by
    rw [hsum, tsum_eq_sum (s := T) ?_]
    intro i hiT
    by_contra hne
    exact hiT (hT.ge (Function.mem_support.mpr hne))
  -- `Φ ∈ span (range degenFamily n)` (spherical side)
  have hΦmem : Φ ∈ Submodule.span ℂ (Set.range (degenFamily n)) := by
    rw [hΦsum]
    exact Submodule.sum_mem _ (fun i _ => (hsector i).1)
  -- transport along the linear isometry `chartRealization.symm`
  have htrans : chartRealization.symm Φ
      ∈ Submodule.span ℂ (chartRealization.symm '' Set.range (degenFamily n)) :=
    Submodule.apply_mem_span_image_of_mem_span
      (f := (chartRealization.symm : Decomposition.l2R3 →ₗ[ℂ] Spectra.Sobolev.l2R3)) hΦmem
  rw [← Set.range_comp] at htrans
  -- `chartRealization.symm Φ = ψ`
  have hψ : chartRealization.symm Φ = (ψ : Spectra.Sobolev.l2R3) := by
    rw [hΦ, LinearIsometryEquiv.symm_apply_apply]
  rwa [hψ] at htrans

end QuantumMechanics.Hydrogen.Spectrum
