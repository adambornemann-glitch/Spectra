/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Hamiltonian
import Spectra.QuantumMechanics.Hydrogen.Spectrum.Eigenvalue
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.TensorDecomp.Basic
import Spectra.QuantumMechanics.Hydrogen.Laplacian.ChartRealization

/-!
# Forward direction of the hydrogen discrete spectrum — Phase A plumbing

Foundational lemmas for the **forward direction** (`eigenpair ⟹ E = E_n`) of
`hydrogen_discrete_spectrum`.  They derisk the two endpoints of the proof and
confirm the interface to `RadialEq.radial_quantization`.

## Main statements

* `radial_quantization_Z` — a nonzero classical `L²` solution of the charge-`Z`
  reduced radial eigen-equation at energy `E < 0` forces `E = eigenvalue p n hn`
  for some `n ≥ ℓ + 1` (via the `Z`-dilation to the `Z = 1` quantization theorem).
* `radial_continuum_Z` — the `E ≥ 0` analogue: every square-integrable classical
  solution of the charge-`Z` reduced radial eigen-equation vanishes identically.
* `radial_classical_of_logCoord` — the log-coordinate back-transform, turning a
  classical solution of the log-coordinate ODE into one of the radial equation in `r`.
* `forward_bridge` — the forward log-coordinate change of variables, converting the
  weak radial equation in `r` into the weak `s`-form consumed by the regularity bootstrap.
* `weak_eigenequation_ae` — **Step 1.** For an `H²` eigenfunction of `H = −½Δ − Z/r`
  at energy `E`, the weak Laplacian satisfies the a.e. identity
  `weakLaplacian ψ = 2(E − V)ψ` (recall `weakLaplacian = −Δ` and `V = coulombMultiplier = −Z/r`).
* `cartesian_weak_eigen` — the Cartesian weak eigen-equation with both Laplacian
  derivatives moved onto a smooth compactly supported test function.
* `radialHamiltonian_formallySymm` — formal symmetry of the radial Hamiltonian on
  smooth compactly supported radial test functions w.r.t. the `r² dr` measure.
* `inner_chartRealizationSymm_sectorEmbedding` — the projection bridge: pairing a
  Cartesian `L²` function against a back-transported sector element equals the radial
  pairing against the angular coefficient function.
* `eigenvalue_of_dilated` — **Step 6 (assembly glue).** If the dilated energy `E/Z²`
  equals the `Z = 1` eigenvalue `hydrogenEigenvalue n`, then `E = eigenvalue p n hn`.
* `sphericalDecomposition_ne_zero` — **Step 3 (nonzero transfer).** A nonzero element
  of `L²(ℝ³)` (spherical coordinates) has a nonzero radial component in some sector.

See the discharge plan in `Spectrum/Discrete.lean` for how these compose.
-/

noncomputable section

namespace QuantumMechanics.Hydrogen.Spectrum

open MeasureTheory Complex Filter
open Spectra.Sobolev
open RadialEq Spectra.QuantumMechanics.Hydrogen Spectra.QuantumMechanics.Hydrogen.Decomposition
open scoped Topology ContDiff

/-! ## Step 6 — assembly glue (Z-dilation arithmetic) -/

/-- **Step 6 (assembly glue).** If the dilated energy `E / Z²` is the `Z = 1`
    eigenvalue `hydrogenEigenvalue n = −1/(2n²)`, then `E` is the charge-`Z`
    eigenvalue `eigenvalue p n hn = −Z²/(2n²)`. -/
lemma eigenvalue_of_dilated (p : CoulombParams) {E : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (h : E = p.Z ^ 2 * hydrogenEigenvalue n hn) : E = eigenvalue p n hn := by
  rw [h, eigenvalue, hydrogenEigenvalue]; ring

/-! ## Step 3 — nonzero transfer through the spherical decomposition -/

/-- **Step 3 (nonzero transfer).** A nonzero element of `L²(ℝ³)` written in
    spherical coordinates has a nonzero radial component in some `(ℓ, m)` sector.
    Immediate from injectivity of the unitary `sphericalDecomposition` plus
    componentwise extensionality of the Hilbert-sum space `lp`. -/
lemma sphericalDecomposition_ne_zero {Φ : Decomposition.l2R3} (hΦ : Φ ≠ 0) :
    ∃ i : HarmonicIdx, sphericalDecomposition Φ i ≠ 0 := by
  by_contra hcon
  refine hΦ (sphericalDecomposition.injective ?_)
  rw [map_zero]
  apply lp.ext
  funext i
  have hi : sphericalDecomposition Φ i = 0 := not_not.1 fun h => hcon ⟨i, h⟩
  rw [hi, lp.coeFn_zero, Pi.zero_apply]

/-! ## Step 1 — unfolding the weak eigenequation -/

/-- **Step 1 (unfold the weak eigenequation).** For an `H²` eigenfunction `ψ` of
    `H = −½Δ − Z/r` at energy `E` (i.e. `H ψ = E • ψ`), the weak Laplacian
    satisfies, almost everywhere,

      `weakLaplacian ψ = 2 (E − V) ψ`,   `V = coulombMultiplier p = −Z/r`.

    Equivalently `Δψ = −2(E + Z/r)ψ` (recall `weakLaplacian = −Δ`), the form
    consumed by the classical radial eigen-equation downstream.  This is the
    `bound_state_of_radial_profile` H-computation run backward. -/
theorem weak_eigenequation_ae (p : CoulombParams) (E : ℝ)
    (ψ : (hydrogenHamiltonian p).domain)
    (heig : hydrogenHamiltonian p ψ = (E : ℂ) • (ψ : Spectra.Sobolev.l2R3)) :
    ⇑(weakLaplacian (ψ : Spectra.Sobolev.l2R3) ψ.2) =ᵐ[volume]
      fun x => (2 : ℂ) * ((E : ℂ) - (coulombMultiplier p x : ℂ))
        * (ψ : Spectra.Sobolev.l2R3) x := by
  obtain ⟨Ψ, hH2⟩ := ψ
  change ⇑(weakLaplacian Ψ hH2) =ᵐ[volume]
      fun x => (2 : ℂ) * ((E : ℂ) - (coulombMultiplier p x : ℂ)) * ⇑Ψ x
  have ehalf : ⇑(halfLaplacianPMap ⟨Ψ, hH2⟩) =ᵐ[volume]
      ((1 / 2 : ℝ) : ℂ) • ⇑(weakLaplacian Ψ hH2) := by
    rw [show halfLaplacianPMap ⟨Ψ, hH2⟩ = ((1 / 2 : ℝ) : ℂ) • weakLaplacian Ψ hH2 from by
      rw [halfLaplacianPMap_apply]; rfl]
    exact Lp.coeFn_smul _ _
  have ecoul : ⇑(coulombPotential p ⟨Ψ, hH2⟩) =ᵐ[volume]
      fun x => (coulombMultiplier p x : ℂ) * ⇑Ψ x :=
    (coulomb_mul_memLp_H2 p Ψ hH2).coeFn_toLp
  have eH : ⇑(hydrogenHamiltonian p ⟨Ψ, hH2⟩) =ᵐ[volume]
      fun x => ⇑(halfLaplacianPMap ⟨Ψ, hH2⟩) x + ⇑(coulombPotential p ⟨Ψ, hH2⟩) x := by
    rw [hydrogenHamiltonian_apply]; exact Lp.coeFn_add _ _
  have heigC : ⇑(hydrogenHamiltonian p ⟨Ψ, hH2⟩) =ᵐ[volume] (E : ℂ) • ⇑Ψ := by
    rw [heig]; exact Lp.coeFn_smul (E : ℂ) Ψ
  filter_upwards [eH, ehalf, ecoul, heigC] with x heHx hehalfx hecoulx hheigx
  rw [Pi.smul_apply, smul_eq_mul] at hehalfx hheigx
  have e1 : ((1 / 2 : ℝ) : ℂ) * ⇑(weakLaplacian Ψ hH2) x
      + (coulombMultiplier p x : ℂ) * ⇑Ψ x = (E : ℂ) * ⇑Ψ x := by
    rw [← hehalfx, ← hecoulx, ← heHx, hheigx]
  push_cast at e1 ⊢
  linear_combination (2 : ℂ) * e1

/-! ## Step 0 + Step 5 — the Z-dilation bridge to quantization

Rather than dilate the abstract 3-D `H²` eigenfunction (which needs weak-derivative-
under-scaling machinery), the sector reduction `hydrogen_reduces_half`
already produces the **general-`Z`** radial equation, while `RadialEq.radial_quantization`
is stated at `Z = 1`.  The two are bridged by the **one-dimensional** classical dilation
`φ(r) := ψ(r / Z)`, which carries a classical `C²` solution of the charge-`Z` radial ODE
at energy `E` to one of the `Z = 1` ODE at energy `E / Z²` — the same `HasDerivAt.scomp`
chain rule used (in reverse) by `hydrogen_bound_state`. -/

/-- **Step 0 + Step 5 (dilation + quantization).** A nonzero classical `C²` `L²` solution
    of the **charge-`Z`** reduced radial eigen-equation
    `−½ψ″ − (1/r)ψ′ + (ℓ(ℓ+1)/(2r²) − Z/r)ψ = E ψ`  on `(0,∞)` (with the Dirichlet
    boundary behaviour `r·ψ → 0` at the origin) forces `E = eigenvalue p n hn = −Z²/(2n²)`
    for some `n ≥ ℓ + 1`.

    Proof: the dilation `φ(r) = ψ(r / Z)` solves the `Z = 1` equation
    `RadialEq.radialHamiltonian ℓ φ = (E/Z²) φ`, so `RadialEq.radial_quantization` gives
    `E/Z² = hydrogenEigenvalue n`, and `eigenvalue_of_dilated` finishes. -/
theorem radial_quantization_Z (p : CoulombParams) (ℓ : ℕ) (E : ℝ) (hE : E < 0)
    (ψ : ℝ → ℝ)
    (hnz : ∃ r₀, 0 < r₀ ∧ ψ r₀ ≠ 0)
    (hL2 : RadialL2 ψ)
    (hψ1 : ∀ r, 0 < r → HasDerivAt ψ (deriv ψ r) r)
    (hψ2 : ∀ r, 0 < r → HasDerivAt (deriv ψ) (deriv^[2] ψ r) r)
    (heq : ∀ r, 0 < r →
      -(1 / 2) * deriv^[2] ψ r - (1 / r) * deriv ψ r
        + ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / (2 * r ^ 2) - p.Z / r) * ψ r = E * ψ r)
    (hbc : Tendsto (fun r => r * ψ r) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∃ (n : ℕ) (hn : 1 ≤ n), E = eigenvalue p n hn := by
  set Z : ℝ := p.Z with hZdef
  have hZ : 0 < Z := p.hZ
  have hZ0 : Z ≠ 0 := hZ.ne'
  have hinv : (0 : ℝ) < Z⁻¹ := inv_pos.mpr hZ
  set φ : ℝ → ℝ := fun r => ψ (Z⁻¹ * r) with hφdef
  -- chain rule for the inner scaling
  have hinner : ∀ r : ℝ, HasDerivAt (fun t : ℝ => Z⁻¹ * t) Z⁻¹ r :=
    fun r => by simpa using (hasDerivAt_id r).const_mul Z⁻¹
  -- first derivative of φ on (0,∞)
  have hd1 : ∀ r, 0 < r → HasDerivAt φ (Z⁻¹ * deriv ψ (Z⁻¹ * r)) r := by
    intro r hr
    have hs : 0 < Z⁻¹ * r := by positivity
    simpa [hφdef, Function.comp_def, mul_comm] using (hψ1 (Z⁻¹ * r) hs).comp r (hinner r)
  have hderiv1 : ∀ r, 0 < r → deriv φ r = Z⁻¹ * deriv ψ (Z⁻¹ * r) :=
    fun r hr => (hd1 r hr).deriv
  -- second derivative of φ on (0,∞), via an eventual-equality of `deriv φ`
  have hd2 : ∀ r, 0 < r →
      HasDerivAt (deriv φ) (Z⁻¹ * (Z⁻¹ * deriv^[2] ψ (Z⁻¹ * r))) r := by
    intro r hr
    have hs : 0 < Z⁻¹ * r := by positivity
    have hcomp : HasDerivAt (fun t => deriv ψ (Z⁻¹ * t))
        (Z⁻¹ * deriv^[2] ψ (Z⁻¹ * r)) r := by
      simpa [Function.comp_def, mul_comm] using (hψ2 (Z⁻¹ * r) hs).comp r (hinner r)
    have hD1 : HasDerivAt (fun t => Z⁻¹ * deriv ψ (Z⁻¹ * t))
        (Z⁻¹ * (Z⁻¹ * deriv^[2] ψ (Z⁻¹ * r))) r := hcomp.const_mul Z⁻¹
    refine hD1.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hr] with s hs' using hderiv1 s hs'
  have hderiv2 : ∀ r, 0 < r → deriv^[2] φ r = Z⁻¹ * (Z⁻¹ * deriv^[2] ψ (Z⁻¹ * r)) :=
    fun r hr => (hd2 r hr).deriv
  -- (1) nondegeneracy
  have hφnz : ∃ r₀, 0 < r₀ ∧ φ r₀ ≠ 0 := by
    obtain ⟨r₀, hr₀, hr₀ne⟩ := hnz
    refine ⟨Z * r₀, by positivity, ?_⟩
    simpa [hφdef, ← mul_assoc, inv_mul_cancel₀ hZ0] using hr₀ne
  -- (2) square-integrability, by change of variables r = Z·s
  have hφL2 : RadialL2 φ := by
    have hco := (integrableOn_Ioi_comp_mul_left_iff
        (fun s => Z ^ 2 * (ψ s ^ 2 * s ^ 2)) 0 hinv).mpr
        (by rw [mul_zero]; exact hL2.const_mul (Z ^ 2))
    refine hco.congr_fun (fun r _ => ?_) measurableSet_Ioi
    simp only [hφdef]
    field_simp
  -- (5) the dilated solution satisfies the Z = 1 radial equation at energy E/Z²
  have hφeq : ∀ r, 0 < r → RadialEq.radialHamiltonian ℓ φ r = E / Z ^ 2 * φ r := by
    intro r hr
    have hs : 0 < Z⁻¹ * r := by positivity
    have hE2 := heq (Z⁻¹ * r) hs
    have hrne : r ≠ 0 := hr.ne'
    have _hsne : Z⁻¹ * r ≠ 0 := hs.ne'
    have hkey : Z ^ 2 * RadialEq.radialHamiltonian ℓ φ r = E * φ r := by
      simp only [RadialEq.radialHamiltonian]
      rw [hderiv1 r hr, hderiv2 r hr]
      simp only [hφdef]
      rw [← hE2]
      field_simp
      ring
    rw [div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hZ0)]
    linear_combination hkey
  -- (6) boundary condition at the origin
  have hφbc : Tendsto (fun r => r * φ r) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hmaps : Tendsto (fun r => Z⁻¹ * r) (nhdsWithin 0 (Set.Ioi 0))
        (nhdsWithin 0 (Set.Ioi 0)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h0 : Tendsto (fun r : ℝ => Z⁻¹ * r) (nhds 0) (nhds 0) := by
          simpa using (tendsto_id (x := nhds (0 : ℝ))).const_mul Z⁻¹
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact mul_pos hinv hr
    have hcomp := (hbc.comp hmaps).const_mul Z
    simp only [mul_zero] at hcomp
    refine hcomp.congr (fun r => ?_)
    simp only [hφdef, Function.comp_apply, ← mul_assoc, mul_inv_cancel₀ hZ0, one_mul]
  -- quantize the dilated solution and undo the dilation
  have hEZ : E / Z ^ 2 < 0 := div_neg_of_neg_of_pos hE (by positivity)
  obtain ⟨n, hn, hEeq⟩ := (RadialEq.radial_quantization ℓ (E / Z ^ 2) hEZ).mp
    ⟨φ, hφnz, hφL2, fun r hr => by rw [hderiv1 r hr]; exact hd1 r hr,
      fun r hr => by rw [hderiv2 r hr]; exact hd2 r hr, hφeq, hφbc⟩
  refine ⟨n, by omega, eigenvalue_of_dilated p (by omega) ?_⟩
  rw [← hEeq, ← hZdef]
  field_simp

/-! ## Continuum endpoint (no positive eigenvalues) — the `E ≥ 0` analogue of the dilation -/

/-- **Charge-`Z` continuum vanishing.** At energy `E ≥ 0`, every classical `C²`,
square-integrable solution of the charge-`Z` reduced radial eigen-equation
`−½ψ″ − (1/r)ψ′ + (ℓ(ℓ+1)/(2r²) − Z/r)ψ = E ψ` on `(0,∞)` is identically `0`.

This is the `E ≥ 0` analogue of `radial_quantization_Z`.  The proof reuses the same
`Z`-dilation `φ(r) = ψ(Z⁻¹r)` (which carries the charge-`Z` equation at energy `E` to the
`Z = 1` equation `RadialEq.radialHamiltonian` at energy `E/Z² ≥ 0`), then invokes
`RadialEq.radial_continuum` — which, unlike `RadialEq.radial_quantization`, needs neither a
nonzero point nor a boundary condition at the origin.  It is consumed by
`no_positive_eigenvalue` (and ultimately `hydrogen_no_positive_eigenvalues`, Kato's theorem
for hydrogen). -/
theorem radial_continuum_Z (p : CoulombParams) (ℓ : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (ψ : ℝ → ℝ)
    (hL2 : RadialL2 ψ)
    (hψ1 : ∀ r, 0 < r → HasDerivAt ψ (deriv ψ r) r)
    (hψ2 : ∀ r, 0 < r → HasDerivAt (deriv ψ) (deriv^[2] ψ r) r)
    (heq : ∀ r, 0 < r →
      -(1 / 2) * deriv^[2] ψ r - (1 / r) * deriv ψ r
        + ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / (2 * r ^ 2) - p.Z / r) * ψ r = E * ψ r) :
    ∀ r, 0 < r → ψ r = 0 := by
  set Z : ℝ := p.Z with _hZdef
  have hZ : 0 < Z := p.hZ
  have hZ0 : Z ≠ 0 := hZ.ne'
  have hinv : (0 : ℝ) < Z⁻¹ := inv_pos.mpr hZ
  set φ : ℝ → ℝ := fun r => ψ (Z⁻¹ * r) with hφdef
  -- chain rule for the inner scaling
  have hinner : ∀ r : ℝ, HasDerivAt (fun t : ℝ => Z⁻¹ * t) Z⁻¹ r :=
    fun r => by simpa using (hasDerivAt_id r).const_mul Z⁻¹
  -- first derivative of φ on (0,∞)
  have hd1 : ∀ r, 0 < r → HasDerivAt φ (Z⁻¹ * deriv ψ (Z⁻¹ * r)) r := by
    intro r hr
    have hs : 0 < Z⁻¹ * r := by positivity
    simpa [hφdef, Function.comp_def, mul_comm] using (hψ1 (Z⁻¹ * r) hs).comp r (hinner r)
  have hderiv1 : ∀ r, 0 < r → deriv φ r = Z⁻¹ * deriv ψ (Z⁻¹ * r) :=
    fun r hr => (hd1 r hr).deriv
  -- second derivative of φ on (0,∞), via an eventual-equality of `deriv φ`
  have hd2 : ∀ r, 0 < r →
      HasDerivAt (deriv φ) (Z⁻¹ * (Z⁻¹ * deriv^[2] ψ (Z⁻¹ * r))) r := by
    intro r hr
    have hs : 0 < Z⁻¹ * r := by positivity
    have hcomp : HasDerivAt (fun t => deriv ψ (Z⁻¹ * t))
        (Z⁻¹ * deriv^[2] ψ (Z⁻¹ * r)) r := by
      simpa [Function.comp_def, mul_comm] using (hψ2 (Z⁻¹ * r) hs).comp r (hinner r)
    have hD1 : HasDerivAt (fun t => Z⁻¹ * deriv ψ (Z⁻¹ * t))
        (Z⁻¹ * (Z⁻¹ * deriv^[2] ψ (Z⁻¹ * r))) r := hcomp.const_mul Z⁻¹
    refine hD1.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hr] with s hs' using hderiv1 s hs'
  have hderiv2 : ∀ r, 0 < r → deriv^[2] φ r = Z⁻¹ * (Z⁻¹ * deriv^[2] ψ (Z⁻¹ * r)) :=
    fun r hr => (hd2 r hr).deriv
  -- square-integrability of the dilated solution, by change of variables r = Z·s
  have hφL2 : RadialL2 φ := by
    have hco := (integrableOn_Ioi_comp_mul_left_iff
        (fun s => Z ^ 2 * (ψ s ^ 2 * s ^ 2)) 0 hinv).mpr
        (by rw [mul_zero]; exact hL2.const_mul (Z ^ 2))
    refine hco.congr_fun (fun r _ => ?_) measurableSet_Ioi
    simp only [hφdef]
    field_simp
  -- the dilated solution satisfies the Z = 1 radial equation at energy E/Z²
  have hφeq : ∀ r, 0 < r → RadialEq.radialHamiltonian ℓ φ r = E / Z ^ 2 * φ r := by
    intro r hr
    have hs : 0 < Z⁻¹ * r := by positivity
    have hE2 := heq (Z⁻¹ * r) hs
    have hrne : r ≠ 0 := hr.ne'
    have _hsne : Z⁻¹ * r ≠ 0 := hs.ne'
    have hkey : Z ^ 2 * RadialEq.radialHamiltonian ℓ φ r = E * φ r := by
      simp only [RadialEq.radialHamiltonian]
      rw [hderiv1 r hr, hderiv2 r hr]
      simp only [hφdef]
      rw [← hE2]
      field_simp
      ring
    rw [div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hZ0)]
    linear_combination hkey
  -- continuum: the dilated Z = 1 solution vanishes identically on (0,∞)
  have hEZ : 0 ≤ E / Z ^ 2 := div_nonneg hE (by positivity)
  have hφ0 : ∀ r, 0 < r → φ r = 0 :=
    RadialEq.radial_continuum ℓ (E / Z ^ 2) hEZ φ
      (fun r hr => by rw [hderiv1 r hr]; exact hd1 r hr)
      (fun r hr => by rw [hderiv2 r hr]; exact hd2 r hr) hφeq hφL2
  -- undo the dilation: ψ r = φ (Z · r)
  intro r hr
  have hval : φ (Z * r) = 0 := hφ0 (Z * r) (by positivity)
  simpa [hφdef, ← mul_assoc, inv_mul_cancel₀ hZ0] using hval

/-! ## Step 4 (log-coordinate back-transform) — classical solution from the bootstrap

The companion to the dilation bridge above, sitting on the *input* side of
`radial_quantization_Z`.  The elliptic-regularity bootstrap
`Spectra.RadialRegularity.classical_of_weak_ode` produces a pointwise `C²` solution of the radial
equation written in the **logarithmic coordinate** `s = log r`, namely `c₀'' + c₀' − b c₀ = 0`
with `b(s) = ℓ(ℓ+1) − 2Z e^s − 2E e^{2s}`.  This lemma changes variables back to `r`, turning that
`c₀` into a classical `C²` solution `ψ(r) = c₀(log r)` of the charge-`Z` reduced radial
eigen-equation on `(0,∞)` — exactly the `hψ1`/`hψ2`/`heq` hypotheses of `radial_quantization_Z`.
The derivatives transform as `ψ'(r) = c₀'(log r)/r` and `ψ''(r) = (c₀''(log r) − c₀'(log r))/r²`. -/

/-- **Log-coordinate back-transform.** A classical `C²` solution `c₀` of the log-coordinate radial
ODE `c₀'' + c₀' − (ℓ(ℓ+1) − 2Z e^s − 2E e^{2s}) c₀ = 0` on `ℝ` yields, via `ψ(r) = c₀(log r)`, a
classical `C²` solution of the charge-`Z` reduced radial eigen-equation
`−½ψ″ − (1/r)ψ′ + (ℓ(ℓ+1)/(2r²) − Z/r)ψ = E ψ` on `(0,∞)`.  Pure chain rule; pairs with
`Spectra.RadialRegularity.classical_of_weak_ode` (which supplies `c₀`) and feeds the
`hψ1`/`hψ2`/`heq` hypotheses of `radial_quantization_Z`. -/
theorem radial_classical_of_logCoord (ℓ : ℕ) (Z E : ℝ) (c₀ : ℝ → ℝ)
    (hc1 : ∀ s, HasDerivAt c₀ (deriv c₀ s) s)
    (hc2 : ∀ s, HasDerivAt (deriv c₀) (deriv^[2] c₀ s) s)
    (hode : ∀ s, deriv^[2] c₀ s + deriv c₀ s
      - ((ℓ : ℝ) * ((ℓ : ℝ) + 1) - 2 * Z * Real.exp s - 2 * E * Real.exp (2 * s)) * c₀ s = 0) :
    (∀ r, 0 < r → HasDerivAt (fun r => c₀ (Real.log r))
        (deriv (fun r => c₀ (Real.log r)) r) r) ∧
    (∀ r, 0 < r → HasDerivAt (deriv (fun r => c₀ (Real.log r)))
        (deriv^[2] (fun r => c₀ (Real.log r)) r) r) ∧
    (∀ r, 0 < r → -(1 / 2) * deriv^[2] (fun r => c₀ (Real.log r)) r
        - (1 / r) * deriv (fun r => c₀ (Real.log r)) r
        + ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / (2 * r ^ 2) - Z / r) * (fun r => c₀ (Real.log r)) r
        = E * (fun r => c₀ (Real.log r)) r) := by
  set ψ : ℝ → ℝ := fun r => c₀ (Real.log r) with hψdef
  -- first derivative on `(0,∞)`
  have hd1 : ∀ r, 0 < r → HasDerivAt ψ (deriv c₀ (Real.log r) * r⁻¹) r := fun r hr =>
    (hc1 (Real.log r)).comp r (Real.hasDerivAt_log hr.ne')
  have hderiv1 : ∀ r, 0 < r → deriv ψ r = deriv c₀ (Real.log r) * r⁻¹ :=
    fun r hr => (hd1 r hr).deriv
  -- second derivative on `(0,∞)`, via eventual equality of `deriv ψ`
  have hd2 : ∀ r, 0 < r → HasDerivAt (deriv ψ)
      (deriv^[2] c₀ (Real.log r) * r⁻¹ * r⁻¹ + deriv c₀ (Real.log r) * (-(r ^ 2)⁻¹)) r := by
    intro r hr
    have hcomp : HasDerivAt (fun t => deriv c₀ (Real.log t))
        (deriv^[2] c₀ (Real.log r) * r⁻¹) r :=
      (hc2 (Real.log r)).comp r (Real.hasDerivAt_log hr.ne')
    have hD : HasDerivAt (fun t => deriv c₀ (Real.log t) * t⁻¹)
        (deriv^[2] c₀ (Real.log r) * r⁻¹ * r⁻¹ + deriv c₀ (Real.log r) * (-(r ^ 2)⁻¹)) r :=
      hcomp.mul (hasDerivAt_inv hr.ne')
    refine hD.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hr] with s hs using hderiv1 s hs
  have hderiv2 : ∀ r, 0 < r → deriv^[2] ψ r =
      deriv^[2] c₀ (Real.log r) * r⁻¹ * r⁻¹ + deriv c₀ (Real.log r) * (-(r ^ 2)⁻¹) := by
    intro r hr
    change deriv (deriv ψ) r = _
    exact (hd2 r hr).deriv
  refine ⟨fun r hr => by rw [hderiv1 r hr]; exact hd1 r hr,
    fun r hr => by rw [hderiv2 r hr]; exact hd2 r hr, ?_⟩
  intro r hr
  have hrne : r ≠ 0 := hr.ne'
  have hexp : Real.exp (Real.log r) = r := Real.exp_log hr
  have hexp2 : Real.exp (2 * Real.log r) = r ^ 2 := by
    rw [two_mul, Real.exp_add, hexp]; ring
  have hODEr := hode (Real.log r)
  rw [hexp, hexp2] at hODEr
  have key : deriv^[2] c₀ (Real.log r) + deriv c₀ (Real.log r)
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) - 2 * Z * r - 2 * E * r ^ 2) * c₀ (Real.log r) := by
    linarith [hODEr]
  rw [hderiv2 r hr, hderiv1 r hr]
  simp only [hψdef]
  field_simp
  linear_combination -key

/-! ## Step 4 (forward log-coordinate bridge) — weak radial eqn ⟹ weak `s`-form

The *forward* half of the log-coordinate change of variables (the companion to
`radial_classical_of_logCoord`).  It converts the **weak radial equation** in `r` produced by the
sector reduction (Phase C) — pairing the charge-`Z` radial Hamiltonian
`H_{ℓ,Z}χ = −½χ″ − (1/r)χ′ + (ℓ(ℓ+1)/(2r²) − Z/r)χ` against radial test functions `χ` supported in
`(0,∞)`, with the `r²dr` measure — into the **weak `s`-form**
`∫ R(eˢ)·(η″ − η′ − b η) ds = 0` (`b(s) = ℓ(ℓ+1) − 2Z eˢ − 2E e^{2s}`) consumed by
`Spectra.RadialRegularity.classical_of_weak_ode`.

Mechanism: feed the weak hypothesis the specific radial test `χ(r) = η(log r)/r` (extended by `0`),
then change variables `r = eˢ` via `integral_image_eq_integral_abs_deriv_smul` for `exp`
(`exp '' univ = Ioi 0`, jacobian `eˢ`).  The `/r` weight is exactly what aligns the first-order
terms so that the recovered coefficient is `b` and the reduced variable is the unweighted
`s ↦ R(eˢ)` — matching `radial_classical_of_logCoord`.  Pure analysis; `R : ℝ → ℝ` (the `ℂ`-valued
`coeffFun` is handled at the application site by taking real and imaginary parts). -/
open Set in
/-- **Forward log-coordinate bridge.** Given the weak charge-`Z` radial equation in `r`
    (pairing the radial Hamiltonian against radial test functions `χ` with the `r² dr` measure),
    every smooth compactly supported `η` satisfies the weak log-coordinate `s`-form
    `∫ R(eˢ)·(η″ − η′ − b η) ds = 0` with `b(s) = ℓ(ℓ+1) − 2Z eˢ − 2E e^{2s}`.
    Obtained by feeding the weak hypothesis the test `χ(r) = η(log r)/r` and changing
    variables `r = eˢ`; the output is the input of
    `Spectra.RadialRegularity.classical_of_weak_ode`. -/
theorem forward_bridge (ℓ : ℕ) (Z E : ℝ) (R : ℝ → ℝ)
    (hweak : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → (∀ᶠ r in 𝓝 (0 : ℝ), χ r = 0) →
        ∫ r in Set.Ioi 0,
          (-(1 / 2) * deriv^[2] χ r - (1 / r) * deriv χ r
            + ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / (2 * r ^ 2) - Z / r) * χ r - E * χ r) * R r * r ^ 2 = 0) :
    ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ s, R (Real.exp s) *
        (deriv (deriv η) s - deriv η s
          - ((ℓ : ℝ) * ((ℓ : ℝ) + 1) - 2 * Z * Real.exp s
              - 2 * E * Real.exp (2 * s)) * η s) = 0 := by
  intro η hη hη0
  -- `η` derivative facts
  have hη1 : ∀ s, HasDerivAt η (deriv η s) s := fun s =>
    (hη.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hη2 : ∀ s, HasDerivAt (deriv η) (deriv (deriv η) s) s := fun s =>
    (((contDiff_infty_iff_deriv.mp hη).2).differentiable (by norm_num)).differentiableAt.hasDerivAt
  -- a support bound for `η`
  obtain ⟨M, _hM0, hMsub⟩ : ∃ M : ℝ, 0 ≤ M ∧ Function.support η ⊆ Icc (-M) M := by
    obtain ⟨M, hMsub⟩ := hη0.isBounded.subset_closedBall (0 : ℝ)
    refine ⟨max M 0, le_max_right _ _, fun x hx => ?_⟩
    have hx' := hMsub (subset_tsupport η hx)
    rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hx'
    exact ⟨le_trans (neg_le_neg (le_max_left _ _)) hx'.1, le_trans hx'.2 (le_max_left _ _)⟩
  -- the radial test function `χ(r) = η(log r)/r`, extended by `0`
  set χ : ℝ → ℝ := fun r => if 0 < r then η (Real.log r) * r⁻¹ else 0 with hχdef
  have hχ_pos : ∀ r, 0 < r → χ r = η (Real.log r) * r⁻¹ := fun r hr => if_pos hr
  have _hχ_nonpos : ∀ r ≤ 0, χ r = 0 := fun r hr => if_neg (not_lt.mpr hr)
  have hχ_lo : ∀ r, r < Real.exp (-M) → χ r = 0 := by
    intro r hr
    by_cases h0 : 0 < r
    · rw [hχ_pos r h0]
      have hlog : Real.log r < -M := by
        have := Real.log_lt_log h0 hr; rwa [Real.log_exp] at this
      rw [Function.notMem_support.mp fun hs => absurd (hMsub hs).1 (not_le.mpr hlog), zero_mul]
    · rw [hχdef]; simp [h0]
  have hχ_hi : ∀ r, Real.exp M < r → χ r = 0 := by
    intro r hr
    have h0 : 0 < r := lt_trans (Real.exp_pos M) hr
    rw [hχ_pos r h0]
    have hlog : M < Real.log r := by
      have := Real.log_lt_log (Real.exp_pos M) hr; rwa [Real.log_exp] at this
    rw [Function.notMem_support.mp fun hs => absurd (hMsub hs).2 (not_le.mpr hlog), zero_mul]
  have hχ_smooth : ContDiff ℝ ∞ χ := by
    rw [contDiff_iff_contDiffAt]
    intro r₀
    by_cases hr₀ : 0 < r₀
    · have hev : χ =ᶠ[𝓝 r₀] (fun r => η (Real.log r) * r⁻¹) := by
        filter_upwards [Ioi_mem_nhds hr₀] with r hr; exact hχ_pos r hr
      refine ContDiffAt.congr_of_eventuallyEq ?_ hev
      exact (hη.comp_contDiffAt r₀ (Real.contDiffAt_log.mpr hr₀.ne')).mul
        (contDiffAt_inv (𝕜 := ℝ) hr₀.ne')
    · have hr₀' : r₀ < Real.exp (-M) := lt_of_le_of_lt (not_lt.mp hr₀) (Real.exp_pos _)
      have hev : χ =ᶠ[𝓝 r₀] (fun _ => 0) := by
        filter_upwards [Iio_mem_nhds hr₀'] with r hr; exact hχ_lo r hr
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hχ_cs : HasCompactSupport χ := by
    apply HasCompactSupport.intro (isCompact_Icc (a := Real.exp (-M)) (b := Real.exp M))
    intro x hx
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hlt | hgt
    · exact hχ_lo x hlt
    · exact hχ_hi x hgt
  -- derivatives of `χ` on `(0,∞)`
  have hd1 : ∀ r, 0 < r → deriv χ r = (deriv η (Real.log r) - η (Real.log r)) * (r ^ 2)⁻¹ := by
    intro r hr
    have hev : χ =ᶠ[𝓝 r] (fun t => η (Real.log t) * t⁻¹) := by
      filter_upwards [Ioi_mem_nhds hr] with t ht; exact hχ_pos t ht
    have hbase : HasDerivAt (fun t => η (Real.log t) * t⁻¹)
        ((deriv η (Real.log r) - η (Real.log r)) * (r ^ 2)⁻¹) r := by
      have h0 := ((hη1 (Real.log r)).comp r (Real.hasDerivAt_log hr.ne')).mul
        (hasDerivAt_inv hr.ne')
      simp only [Function.comp_def] at h0
      convert h0 using 1
      field_simp; ring
    exact (hbase.congr_of_eventuallyEq hev).deriv
  have hd2 : ∀ r, 0 < r → deriv^[2] χ r =
      (deriv (deriv η) (Real.log r) - 3 * deriv η (Real.log r)
        + 2 * η (Real.log r)) * (r ^ 3)⁻¹ := by
    intro r hr
    have hrne : r ≠ 0 := hr.ne'
    have hev : deriv χ =ᶠ[𝓝 r] (fun t => (deriv η (Real.log t) - η (Real.log t)) * (t ^ 2)⁻¹) := by
      filter_upwards [Ioi_mem_nhds hr] with t ht; exact hd1 t ht
    have hP1 : HasDerivAt (fun t => deriv η (Real.log t)) (deriv (deriv η) (Real.log r) * r⁻¹) r :=
      (hη2 (Real.log r)).comp r (Real.hasDerivAt_log hr.ne')
    have hP2 : HasDerivAt (fun t => η (Real.log t)) (deriv η (Real.log r) * r⁻¹) r :=
      (hη1 (Real.log r)).comp r (Real.hasDerivAt_log hr.ne')
    have hbase : HasDerivAt (fun t => (deriv η (Real.log t) - η (Real.log t)) * (t ^ 2)⁻¹)
        ((deriv (deriv η) (Real.log r) - 3 * deriv η (Real.log r)
          + 2 * η (Real.log r)) * (r ^ 3)⁻¹) r := by
      have h0 := (hP1.sub hP2).mul ((hasDerivAt_pow 2 r).inv (pow_ne_zero 2 hr.ne'))
      simp only [Pi.sub_apply, Pi.inv_apply] at h0
      convert h0 using 1
      field_simp; ring
    change deriv (deriv χ) r = _
    rw [hev.deriv_eq]
    exact hbase.deriv
  -- feed the weak hypothesis the test `χ` (which vanishes on a neighbourhood of `0`)
  have happly := hweak χ hχ_smooth hχ_cs
    (by filter_upwards [Iio_mem_nhds (Real.exp_pos (-M))] with r hr; exact hχ_lo r hr)
  set INTEG : ℝ → ℝ := fun r =>
    (-(1 / 2) * deriv^[2] χ r - (1 / r) * deriv χ r
      + ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / (2 * r ^ 2) - Z / r) * χ r - E * χ r) * R r * r ^ 2 with hINTEG
  -- change of variables `r = eˢ`
  have hCoV : (∫ r in Set.Ioi 0, INTEG r) = ∫ s, Real.exp s * INTEG (Real.exp s) := by
    have h := integral_image_eq_integral_abs_deriv_smul (f := Real.exp) (f' := Real.exp)
      (s := (Set.univ : Set ℝ)) MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) (Real.exp_injective.injOn) INTEG
    rw [Set.image_univ, Real.range_exp, Measure.restrict_univ] at h
    rw [h]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    simp only [abs_of_pos (Real.exp_pos s), smul_eq_mul]
  -- the pointwise change-of-variables identity
  have hpt : ∀ s, R (Real.exp s) *
        (deriv (deriv η) s - deriv η s
          - ((ℓ : ℝ) * ((ℓ : ℝ) + 1) - 2 * Z * Real.exp s - 2 * E * Real.exp (2 * s)) * η s)
      = -2 * (Real.exp s * INTEG (Real.exp s)) := by
    intro s
    have hes : (0 : ℝ) < Real.exp s := Real.exp_pos s
    have hd2s := hd2 (Real.exp s) hes
    have hd1s := hd1 (Real.exp s) hes
    have hχs := hχ_pos (Real.exp s) hes
    rw [Real.log_exp] at hd2s hd1s hχs
    have hexp2 : Real.exp (2 * s) = (Real.exp s) ^ 2 := by rw [two_mul, Real.exp_add]; ring
    simp only [hINTEG]
    rw [hd2s, hd1s, hχs, hexp2]
    field_simp
    ring
  calc ∫ s, R (Real.exp s) *
        (deriv (deriv η) s - deriv η s
          - ((ℓ : ℝ) * ((ℓ : ℝ) + 1) - 2 * Z * Real.exp s - 2 * E * Real.exp (2 * s)) * η s)
      = ∫ s, -2 * (Real.exp s * INTEG (Real.exp s)) := integral_congr_ae (ae_of_all _ hpt)
    _ = -2 * ∫ s, Real.exp s * INTEG (Real.exp s) := integral_const_mul _ _
    _ = -2 * ∫ r in Set.Ioi 0, INTEG r := by rw [← hCoV]
    _ = -2 * 0 := by rw [happly]
    _ = 0 := mul_zero _

/-! ## Step 2/3 — the projection bridge (Cartesian pairing ↔ radial coefficient)

The first brick of the `chartRealization` sector-projection (hard-core (a)).  Pairing a
Cartesian `L²` function `ψ` against the back-transported sector element
`chartRealization⁻¹ (R ⊗ Yᵢ)` equals the *radial* pairing of `R` against the angular
coefficient function `cᵢ(r) = ∫_{S²} Ȳᵢ · (chartRealization ψ)(r, ·)` of `ψ`'s spherical
realization.  Combines the unitarity of `chartRealization` (`inner_map_map`) with the
Fubini factorization `inner_sectorEmbedding_eq_integral_coeffFun` already proved for the
spherical space.  This is how the forward proof will extract a radial weak equation from
the Cartesian eigen-equation, by choosing `R` to range over radial test functions. -/
/-- **Projection bridge (Cartesian pairing ↔ radial coefficient).** Pairing a Cartesian
    `L²` function `ψ` against the back-transported sector element `chartRealization⁻¹ (R ⊗ Yᵢ)`
    equals the radial pairing of `R` against the angular coefficient function
    `coeffFun i (chartRealization ψ)` of `ψ`'s spherical realization, in the radial measure. -/
theorem inner_chartRealizationSymm_sectorEmbedding (i : HarmonicIdx)
    (ψ : Spectra.Sobolev.l2R3) (R : RadialL2) :
    inner ℂ (chartRealization.symm (sectorEmbedding i R)) ψ
      = ∫ r, (starRingEnd ℂ) (R r) * coeffFun i (chartRealization ψ) r ∂radialMeasure := by
  rw [← chartRealization.inner_map_map (chartRealization.symm (sectorEmbedding i R)) ψ,
    chartRealization.apply_symm_apply]
  exact inner_sectorEmbedding_eq_integral_coeffFun i R (chartRealization ψ)

/-! ## Step 4 prerequisite — formal self-adjointness of the radial Hamiltonian

The radial Hamiltonian `H_ℓ` (at `Z = 1`) is formally symmetric on smooth compactly
supported radial test functions with respect to the radial measure `r² dr`: the kinetic
part is in divergence form `−½u″ − (1/r)u′ = −(1/2r²)(r²u′)′`, so the antisymmetric
combination `(H_ℓ u · v − u · H_ℓ v)·r²` is the exact derivative of
`g = −½ r² (u′v − uv′)`, whose integral over `(0,∞)` vanishes (compact support,
`g(0) = 0`).  This formal symmetry underpins the weak formulation of the radial
eigenvalue problem produced by the sector reduction. -/
/-- **Formal symmetry of the radial Hamiltonian.** For smooth compactly supported `u`, `v`,
    the radial Hamiltonian `RadialEq.radialHamiltonian ℓ` (at `Z = 1`) is symmetric with
    respect to the `r² dr` measure:
    `∫₀^∞ (H_ℓ u)·v·r² = ∫₀^∞ u·(H_ℓ v)·r²`.  The antisymmetric combination is an exact
    derivative of `g = −½ r² (u′v − uv′)`, whose integral over `(0,∞)` vanishes. -/
theorem radialHamiltonian_formallySymm (ℓ : ℕ) (u v : ℝ → ℝ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hu0 : HasCompactSupport u) (hv0 : HasCompactSupport v) :
    ∫ r in Set.Ioi 0, RadialEq.radialHamiltonian ℓ u r * v r * r ^ 2
      = ∫ r in Set.Ioi 0, u r * RadialEq.radialHamiltonian ℓ v r * r ^ 2 := by
  -- smoothness of the derivatives
  have hu1 : ∀ r, HasDerivAt u (deriv u r) r := fun r =>
    (hu.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hv1 : ∀ r, HasDerivAt v (deriv v r) r := fun r =>
    (hv.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hu' : ContDiff ℝ ∞ (deriv u) := (contDiff_infty_iff_deriv.mp hu).2
  have hv' : ContDiff ℝ ∞ (deriv v) := (contDiff_infty_iff_deriv.mp hv).2
  have hv2cont : Continuous (deriv^[2] v) := ((contDiff_infty_iff_deriv.mp hv').2).continuous
  have hu2 : ∀ r, HasDerivAt (deriv u) (deriv^[2] u r) r := fun r =>
    (hu'.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hv2 : ∀ r, HasDerivAt (deriv v) (deriv^[2] v r) r := fun r =>
    (hv'.differentiable (by norm_num)).differentiableAt.hasDerivAt
  -- the primitive g and its derivative
  set W : ℝ → ℝ := fun r => deriv u r * v r - u r * deriv v r with hWdef
  set g : ℝ → ℝ := fun r => -(1 / 2 : ℝ) * (r ^ 2 * W r) with hgdef
  have hWcd : ContDiff ℝ ∞ W := (hu'.mul hv).sub (hu.mul hv')
  have hWcs : HasCompactSupport W := (hv0.mul_left).sub (hu0.mul_right)
  have hgcd : ContDiff ℝ ∞ g := by
    rw [hgdef]; exact contDiff_const.mul ((contDiff_id.pow 2).mul hWcd)
  have hg0g : HasCompactSupport g := by
    rw [hgdef]; exact (hWcs.mul_left).mul_left
  have hg1 : ∀ r, HasDerivAt g
      (-(1 / 2 : ℝ) * (2 * r * W r + r ^ 2 *
        ((deriv^[2] u r * v r + deriv u r * deriv v r)
          - (deriv u r * deriv v r + u r * deriv^[2] v r)))) r := by
    intro r
    have hr2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by simpa using hasDerivAt_pow 2 r
    have hWr : HasDerivAt W
        ((deriv^[2] u r * v r + deriv u r * deriv v r)
          - (deriv u r * deriv v r + u r * deriv^[2] v r)) r :=
      ((hu2 r).mul (hv1 r)).sub ((hu1 r).mul (hv2 r))
    exact (hr2.mul hWr).const_mul (-(1 / 2 : ℝ))
  -- the antisymmetric combination is the derivative of g on (0,∞)
  have hkey : Set.EqOn (fun r => RadialEq.radialHamiltonian ℓ u r * v r * r ^ 2)
      (fun r => u r * RadialEq.radialHamiltonian ℓ v r * r ^ 2 + deriv g r) (Set.Ioi 0) := by
    intro r hr
    have hrne : r ≠ 0 := (hr : (0:ℝ) < r).ne'
    simp only [(hg1 r).deriv, RadialEq.radialHamiltonian, hWdef]
    field_simp
    ring
  -- integrability of the right-hand integrand and of `deriv g`
  have hBint : IntegrableOn (fun r => u r * RadialEq.radialHamiltonian ℓ v r * r ^ 2)
      (Set.Ioi 0) := by
    set Breg : ℝ → ℝ := fun r => u r * (-(1 / 2) * deriv^[2] v r * r ^ 2 - r * deriv v r
      + ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / 2) * v r - r * v r) with hBregdef
    have hBregcont : Continuous Breg := by
      rw [hBregdef]
      have hdv : Continuous (deriv v) := hv'.continuous
      fun_prop
    have hBregint : IntegrableOn Breg (Set.Ioi 0) :=
      (hBregcont.integrable_of_hasCompactSupport
        (by rw [hBregdef]; exact hu0.mul_right)).integrableOn
    refine hBregint.congr_fun ?_ measurableSet_Ioi
    intro r hr
    have hrne : r ≠ 0 := (hr : (0:ℝ) < r).ne'
    simp only [RadialEq.radialHamiltonian, hBregdef]
    field_simp
  have hgint : IntegrableOn (deriv g) (Set.Ioi 0) :=
    (((contDiff_infty_iff_deriv.mp hgcd).2).continuous.integrable_of_hasCompactSupport
      hg0g.deriv).integrableOn
  have hgzero : ∫ r in Set.Ioi 0, deriv g r = 0 := by
    rw [HasCompactSupport.integral_Ioi_deriv_eq (hgcd.of_le (by norm_num)) hg0g 0, hgdef]
    simp
  rw [setIntegral_congr_fun measurableSet_Ioi hkey, integral_add hBint hgint, hgzero, add_zero]

/-! ## Phase C, brick 1 — the Cartesian weak eigen-equation

The first foundational brick of the sector-reduction assembly.  Both Laplacian derivatives are moved
off the (only `L²`) eigenfunction `ψ` and onto a smooth compactly supported test function `φ`, via
the weak-derivative integration-by-parts identity, turning `H ψ = E ψ` into the **classical** weak
form `∫ ψ·((−½Δ + V)φ − Eφ) = 0`.  This avoids ever differentiating `ψ` and is the entry point for
projecting onto an angular sector (against a separated test `φ = χ ⊗ Yᵢ`). -/

/-- The coercion of a finite `Lp`-sum is a.e. the pointwise sum of coercions. -/
private lemma coeFn_finsetSum (s : Finset (Fin 3)) (f : Fin 3 → Spectra.Sobolev.l2R3) :
    ⇑(∑ i ∈ s, f i) =ᵐ[volume] fun x => ∑ i ∈ s, (f i) x := by
  induction s using Finset.cons_induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact Lp.coeFn_zero ℂ 2 (volume : Measure Spectra.Sobolev.R3)
  | cons a s ha ih =>
      filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x h1 h2
      simp only [Finset.sum_cons]
      rw [h1, Pi.add_apply, h2]

/-- **Weak-Laplacian test pairing.** For an `H²` function `ψ` and a smooth compactly supported
test `φ`, the weak Laplacian pairs against `φ` by moving both derivatives onto `φ`:
`∫ (weakLaplacian ψ)·φ = −∫ ψ·(∑ᵢ ∂ᵢ²φ)`.  (Recall `weakLaplacian = −Δ`.) -/
lemma integral_weakLaplacian_mul (ψ : Spectra.Sobolev.l2R3) (hψ : MemSobolevH2 ψ)
    (φ : Spectra.Sobolev.R3 → ℂ) (hφ : ContDiff ℝ ∞ φ) (hφ0 : HasCompactSupport φ) :
    ∫ x, ⇑(weakLaplacian ψ hψ) x * φ x
      = -∫ x, ⇑ψ x * ∑ i : Fin 3,
          fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single i 1) := by
  have hφ2 : MemLp φ 2 volume := memLp_of_smooth_compactSupport φ hφ hφ0
  have hint_g : ∀ i : Fin 3, Integrable (fun x => ⇑((hψ.2 i i).choose) x * φ x) := fun i =>
    memLp_one_iff_integrable.mp (MemLp.mul' (r := 1) hφ2 (Lp.memLp ((hψ.2 i i).choose)))
  have hint_ψ : ∀ i : Fin 3, Integrable (fun x => ⇑ψ x *
      fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1)) := by
    intro i
    have h2 : MemLp (fun y => fderiv ℝ (fun z => fderiv ℝ φ z (EuclideanSpace.single i 1)) y
        (EuclideanSpace.single i 1)) 2 volume :=
      memLp_partialDeriv _ i (contDiff_partialDeriv φ i hφ) (hasCompactSupport_partialDeriv φ i hφ0)
    exact memLp_one_iff_integrable.mp (MemLp.mul' (r := 1) h2 (Lp.memLp ψ))
  have key : ∀ i : Fin 3, ∫ x, ⇑((hψ.2 i i).choose) x * φ x
      = ∫ x, ⇑ψ x *
          fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single i 1) := by
    intro i
    obtain ⟨h_i, hd1, hd2⟩ := (hψ.2 i i).choose_spec
    have e2 := hd2 φ hφ hφ0
    have e1 := hd1 (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1))
      (contDiff_partialDeriv φ i hφ) (hasCompactSupport_partialDeriv φ i hφ0)
    rw [e1, e2]; ring
  have hcoe : ⇑(weakLaplacian ψ hψ) =ᵐ[volume]
      fun x => -∑ i : Fin 3, ⇑((hψ.2 i i).choose) x := by
    rw [weakLaplacian]
    filter_upwards [Lp.coeFn_neg (∑ i : Fin 3, (hψ.2 i i).choose),
      coeFn_finsetSum Finset.univ (fun i => (hψ.2 i i).choose)] with x h1 h2
    rw [h1, Pi.neg_apply, h2]
  calc ∫ x, ⇑(weakLaplacian ψ hψ) x * φ x
      = ∫ x, (-∑ i : Fin 3, ⇑((hψ.2 i i).choose) x) * φ x := by
        refine integral_congr_ae ?_
        filter_upwards [hcoe] with x hx; rw [hx]
    _ = ∫ x, -∑ i : Fin 3, ⇑((hψ.2 i i).choose) x * φ x := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [neg_mul, Finset.sum_mul]
    _ = -∑ i : Fin 3, ∫ x, ⇑((hψ.2 i i).choose) x * φ x := by
        rw [integral_neg, integral_finsetSum _ (fun i _ => hint_g i)]
    _ = -∑ i : Fin 3, ∫ x, ⇑ψ x *
          fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single i 1) := by rw [Finset.sum_congr rfl (fun i _ => key i)]
    _ = -∫ x, ∑ i : Fin 3, ⇑ψ x *
          fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single i 1) := by rw [integral_finsetSum _ (fun i _ => hint_ψ i)]
    _ = -∫ x, ⇑ψ x * ∑ i : Fin 3,
          fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single i 1) := by
        refine congrArg Neg.neg (integral_congr_ae (ae_of_all _ fun x => ?_))
        simp only [Finset.mul_sum]

/-- **Cartesian weak eigen-equation (derivatives on the test function).** For an `H²` eigenfunction
`H ψ = E ψ`, pairing against a smooth compactly supported `φ` gives `−∫ ψ·Δφ = ∫ 2(E − V)·ψ·φ`
(`V = coulombMultiplier p`), the classical weak form with all derivatives on the test function.
Combines `integral_weakLaplacian_mul` (move derivatives onto `φ`) with `weak_eigenequation_ae`
(`weakLaplacian ψ = 2(E − V)ψ`). -/
theorem cartesian_weak_eigen (p : CoulombParams) (E : ℝ)
    (ψ : (hydrogenHamiltonian p).domain)
    (heig : hydrogenHamiltonian p ψ = (E : ℂ) • (ψ : Spectra.Sobolev.l2R3))
    (φ : Spectra.Sobolev.R3 → ℂ) (hφ : ContDiff ℝ ∞ φ) (hφ0 : HasCompactSupport φ) :
    -∫ x, ⇑(ψ : Spectra.Sobolev.l2R3) x * ∑ i : Fin 3,
        fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)
      = ∫ x, (2 : ℂ) * ((E : ℂ) - (coulombMultiplier p x : ℂ)) * ⇑(ψ : Spectra.Sobolev.l2R3) x
          * φ x := by
  have hpair := integral_weakLaplacian_mul (ψ : Spectra.Sobolev.l2R3) ψ.2 φ hφ hφ0
  have hwe := weak_eigenequation_ae p E ψ heig
  rw [← hpair]
  refine integral_congr_ae ?_
  filter_upwards [hwe] with x hx
  rw [hx]

end QuantumMechanics.Hydrogen.Spectrum
