/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Hamiltonian
import Spectra.QuantumMechanics.Hydrogen.Spectrum.Eigenvalue
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.TensorDecomp.Basic
import Spectra.QuantumMechanics.Hydrogen.Laplacian.ChartRealization

/-!
# Forward direction of the hydrogen discrete spectrum — Phase A plumbing

Foundational, zero-to-moderate-risk lemmas for the **forward direction**
(`eigenpair ⟹ E = E_n`) of `hydrogen_discrete_spectrum`.  These derisk the two
endpoints of the proof and confirm the interface to `RadialEq.radial_quantization`:

* `eigenvalue_of_dilated` — **Step 6 (assembly glue).** If the dilated energy `E/Z²`
  equals the `Z = 1` eigenvalue `hydrogenEigenvalue n`, then `E = eigenvalue p n hn`.
* `sphericalDecomposition_ne_zero` — **Step 3 (nonzero transfer).** A nonzero element
  of `L²(ℝ³)` (spherical coordinates) has a nonzero radial component in some sector.
* `weak_eigenequation_ae` — **Step 1 (unfold the weak eigenequation).** For an `H²`
  eigenfunction of `H = −½Δ − Z/r` at energy `E`, the weak Laplacian satisfies the
  a.e. identity `weakLaplacian ψ = 2(E − V)ψ` (recall `weakLaplacian = −Δ` and
  `V = coulombMultiplier = −Z/r`).

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
lemma sphericalDecomposition_ne_zero {Φ : Decomposition.L2_R3} (hΦ : Φ ≠ 0) :
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
    (heig : hydrogenHamiltonian p ψ = (E : ℂ) • (ψ : Spectra.Sobolev.L2_R3)) :
    ⇑(weakLaplacian (ψ : Spectra.Sobolev.L2_R3) ψ.2) =ᵐ[volume]
      fun x => (2 : ℂ) * ((E : ℂ) - (coulombMultiplier p x : ℂ))
        * (ψ : Spectra.Sobolev.L2_R3) x := by
  obtain ⟨Ψ, hH2⟩ := ψ
  show ⇑(weakLaplacian Ψ hH2) =ᵐ[volume]
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
under-scaling machinery), we observe that the sector reduction `hydrogen_reduces_half`
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
    have hsne : Z⁻¹ * r ≠ 0 := hs.ne'
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

/-! ## Step 2/3 — the projection bridge (Cartesian pairing ↔ radial coefficient)

The first brick of the `chartRealization` sector-projection (hard-core (a)).  Pairing a
Cartesian `L²` function `ψ` against the back-transported sector element
`chartRealization⁻¹ (R ⊗ Yᵢ)` equals the *radial* pairing of `R` against the angular
coefficient function `cᵢ(r) = ∫_{S²} Ȳᵢ · (chartRealization ψ)(r, ·)` of `ψ`'s spherical
realization.  Combines the unitarity of `chartRealization` (`inner_map_map`) with the
Fubini factorization `inner_sectorEmbedding_eq_integral_coeffFun` already proved for the
spherical space.  This is how the forward proof will extract a radial weak equation from
the Cartesian eigen-equation, by choosing `R` to range over radial test functions. -/
theorem inner_chartRealizationSymm_sectorEmbedding (i : HarmonicIdx)
    (ψ : Spectra.Sobolev.L2_R3) (R : RadialL2) :
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
      (hBregcont.integrable_of_hasCompactSupport (by rw [hBregdef]; exact hu0.mul_right)).integrableOn
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

end QuantumMechanics.Hydrogen.Spectrum
