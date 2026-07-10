/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Spectrum.Eigenvalue
import Spectra.QuantumMechanics.Hydrogen.Hamiltonian
import Spectra.QuantumMechanics.Hydrogen.Laplacian.ChartRealization
import Spectra.QuantumMechanics.Hydrogen.Laplacian.GreensIdentity
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The Cartesian `s`-state eigenfunction and its off-origin eigen-equation

Foundations for the **reverse direction** (`E = E_n ⟹ eigenpair exists`) of
`hydrogen_discrete_spectrum` at `Z = 1`, for the `ℓ = 0` (spherically symmetric)
bound states.

The bound state `Ψ_{n00} = hydrogenEigenfunction n 0 0` lives on the spherical-coordinate
space `Decomposition.l2R3`.  Transporting it to the Cartesian space
`Spectra.Sobolev.l2R3` via `chartRealization.symm` produces a **purely radial** function

  `x ↦ (sphericalNorm 0 0) · R_{n0}(‖x‖)`        (`chartRealization_symm_eigenfunction_coeFn`)

(the angular factor `Y_0^0` is constant, `harmonic_zero_zero`).  This function is `C^∞`
away from the origin but has the **Kato cusp** at `x = 0` for the physical low-`n`
`s`-states, so it is not globally `C²`.

Because it is purely radial, however, its classical Laplacian off the origin is given by
`laplacian_comp_norm` (needing only the *one-dimensional* radial profile to be `C²`, which
it is — `contDiff_Rc`), with **no global `C²` hypothesis required**.  Combined with the
real radial ODE `radial_eigenvalue_eq` (which is cusp-free, holding pointwise for `r > 0`),
this yields the classical eigen-equation away from the origin:

  `-½·Δ(R_{n0}∘‖·‖)(x) − (1/‖x‖)·R_{n0}(‖x‖) = E_n · R_{n0}(‖x‖)`   (`x ≠ 0`)
                                                       (`classical_radial_eigen`)

with `E_n = hydrogenEigenvalue n = −1/(2n²)`.

## The cutoff-integration-by-parts route

To remove the origin's Kato cusp (establishing `MemSobolevH2` of the cusped radial function
and computing its `weakLaplacian` a.e. equal to the classical Laplacian above — no Dirac
delta, since the gradient is bounded and the single origin carries no `H¹` capacity), this
file builds a smooth-cutoff integration by parts: multiply by a cutoff `χ_ε` (`chi`)
vanishing near the origin, apply `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`, and
let `ε → 0` (the shell term scales like `(1/ε)·ε³ → 0` because the gradient is bounded,
`shell_tendsto_zero`).  This handles both the first weak derivative (where the function is
continuous) and the second (where the classical first derivative is bounded but
discontinuous at the origin) uniformly, culminating in the **master cutoff integration by
parts** `master_ibp`.  `RadialEigenfunction.Basic` uses `master_ibp` to assemble the Green's
identity, the required `L²` memberships, and the full reverse direction.

## Main statements

* `classical_radial_eigen` — the classical radial eigen-identity
  `−½·Δ(R_{n0}∘‖·‖)(x) − (1/‖x‖)·R_{n0}(‖x‖) = E_n·R_{n0}(‖x‖)` at every `x ≠ 0`.
* `chartRealization_symm_eigenfunction_coeFn` — the Cartesian transport of the `s`-state
  eigenfunction is a.e. the cusped radial function `x ↦ (sphericalNorm 0 0)·R_{n0}(‖x‖)`.
* `master_ibp` — the master cutoff integration by parts, giving the weak-derivative identity
  `∫ v·∂ⱼφ = −∫ w·φ` for a function `v` that is continuous and `C¹` off the origin and bounded
  near it, with classical `j`-partial `w`.
-/

noncomputable section

namespace QuantumMechanics.Hydrogen.Spectrum

open MeasureTheory Real InnerProductSpace Laplacian Complex Filter
open Spectra.Sobolev Spectra.SphericalHarmonics
open RadialEq Spectra.QuantumMechanics.Hydrogen Spectra.QuantumMechanics.Hydrogen.Decomposition
open scoped ContDiff Topology SchwartzMap

/-- The origin is a null set in `ℝ³`, so almost every point is nonzero. Shared by the many
    cutoff/integrability arguments in this file and in `RadialEigenfunction.Basic` that only
    need a classical (pointwise, off-origin) fact to hold almost everywhere. -/
lemma ae_ne_zero_R3 : ∀ᵐ x : R3, x ≠ 0 := by
  rw [ae_iff]; simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
  exact measure_singleton 0

/-! ## The classical eigen-equation off the origin -/

/-- **Classical radial eigen-identity off the origin (`Z = 1`).**
    For the purely radial profile `R_{n0}` (`ℓ = 0`), at every `x ≠ 0`:
      `−½·Δ(R_{n0}∘‖·‖)(x) − (1/‖x‖)·R_{n0}(‖x‖) = E_n·R_{n0}(‖x‖)`.
    Bypasses the global-`C²` blocker: `laplacian_comp_norm` needs only the 1-D profile
    to be `C²` (it is, `contDiff_Rc`) and `x ≠ 0`; the radial ODE `radial_eigenvalue_eq`
    is cusp-free. -/
lemma classical_radial_eigen (n : ℕ) (hn : 0 + 1 ≤ n) {x : R3} (hx : x ≠ 0) :
    (-(1 / 2 : ℂ)) * Δ (fun y : R3 => Rc n 0 hn ‖y‖) x
        - (1 / (‖x‖ : ℂ)) * Rc n 0 hn ‖x‖
      = (hydrogenEigenvalue n (by omega) : ℂ) * Rc n 0 hn ‖x‖ := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have _hrne : (‖x‖ : ℝ) ≠ 0 := ne_of_gt hr
  rw [laplacian_comp_norm (Rc n 0 hn) (contDiff_Rc n 0 hn) hx]
  have hid2 : iteratedDeriv 2 (Rc n 0 hn) ‖x‖ = deriv (deriv (Rc n 0 hn)) ‖x‖ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hid2, deriv2_Rc n 0 hn, deriv_Rc n 0 hn]
  simp only [Rc]
  have heig := radial_eigenvalue_eq n 0 hn ‖x‖ hr
  have heig' : -(1 / 2 : ℝ) * deriv (deriv (hydrogenRadialWavefunction n 0 hn)) ‖x‖
      - (1 / ‖x‖) * deriv (hydrogenRadialWavefunction n 0 hn) ‖x‖
      - (1 / ‖x‖) * hydrogenRadialWavefunction n 0 hn ‖x‖
      = hydrogenEigenvalue n (by omega) * hydrogenRadialWavefunction n 0 hn ‖x‖ := by
    have h2 : deriv^[2] (hydrogenRadialWavefunction n 0 hn) ‖x‖
        = deriv (deriv (hydrogenRadialWavefunction n 0 hn)) ‖x‖ := by
      simp [Function.iterate_succ]
    have hbridge : RadialEq.radialHamiltonian 0 (hydrogenRadialWavefunction n 0 hn) ‖x‖
        = -(1 / 2 : ℝ) * deriv (deriv (hydrogenRadialWavefunction n 0 hn)) ‖x‖
          - (1 / ‖x‖) * deriv (hydrogenRadialWavefunction n 0 hn) ‖x‖
          - (1 / ‖x‖) * hydrogenRadialWavefunction n 0 hn ‖x‖ := by
      unfold RadialEq.radialHamiltonian
      rw [h2]; push_cast; ring
    rw [← hbridge, heig]
  have hC := congrArg (fun t : ℝ => (t : ℂ)) heig'
  push_cast at hC ⊢
  linear_combination hC

/-! ## The spherical harmonic `Y_0^0` is constant -/

/-- The `ℓ = 0, m = 0` spherical harmonic is the constant `sphericalNorm 0 0`. -/
private lemma harmonic_zero_zero (hm : |(0 : ℤ)| ≤ (0 : ℤ)) (p : ℝ × ℝ) :
    harmonic ⟨0, ⟨0, hm⟩⟩ p = (sphericalNorm 0 0 : ℂ) := by
  simp only [harmonic, SphericalHarmonic, associatedLegendre_0_0]
  simp [Complex.exp_zero]

/-! ## The radial `L²` element collapses to the radial profile -/

/-- `radialLp` collapses a.e. (in `radialMeasure`) to the complex radial profile `Rc`.
    Composes `radialReduction_symm_coeFn` (divide by `r`) with `reducedLp_coeFn`
    (`χ = r·R`). -/
lemma radialLp_coeFn (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    ⇑(radialLp n ℓ hn) =ᵐ[radialMeasure]
      fun r => ((hydrogenRadialWavefunction n ℓ hn r : ℝ) : ℂ) := by
  have h1 := radialReduction_symm_coeFn (reducedLp n ℓ hn)
  have h2 := (reducedLp_coeFn n ℓ hn).filter_mono radialMeasure_absolutelyContinuous.ae_le
  filter_upwards [h1, h2, ae_radial_mem_Ioi] with r hr1 hr2 hrIoi
  have hrne : ((r : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Set.mem_Ioi.mp hrIoi))
  simp only [radialLp]
  rw [hr1, hr2]
  simp only [hydrogenReducedWavefunction]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ hrne, one_mul]

/-! ## The Cartesian realization of the `s`-state bound state -/

/-- The eigenfunction's a.e. value on the spherical side is the pure tensor
    `(r,(θ,φ)) ↦ (sphericalNorm 0 0) · R_{n0}(r)`. -/
lemma eigenfunction_sph_coeFn (n : ℕ) (hn : 0 + 1 ≤ n) (hm : |(0 : ℤ)| ≤ (0 : ℤ)) :
    ⇑(hydrogenEigenfunction n 0 0 hn hm)
      =ᵐ[radialMeasure.prod sphereMeasure]
      fun p : ℝ × ℝ × ℝ => (sphericalNorm 0 0 : ℂ) * Rc n 0 hn p.1 := by
  have hsec := sectorEmbedding_coeFn ⟨0, ⟨0, hm⟩⟩ (radialLp n 0 hn)
  have hrad := (Measure.quasiMeasurePreserving_fst (μ := radialMeasure)
    (ν := sphereMeasure)).ae_eq_comp (radialLp_coeFn n 0 hn)
  filter_upwards [hsec, hrad] with p hp hr
  simp only [hydrogenEigenfunction]
  rw [hp]
  simp only [tensorFun]
  rw [harmonic_zero_zero hm]
  simp only [Function.comp_apply] at hr
  rw [hr]
  simp only [Rc]
  ring

/-- The radial coordinate of the inverse chart is the Euclidean norm. -/
lemma sphereChartInv_fst (x : R3) : (sphereChartInv x).1 = ‖x‖ := by
  rw [sphereChartInv, reshuffle_apply]
  simp only [sphereCoordSymmInvF, Matrix.cons_val_zero]
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  congr 1
  simp [Real.norm_eq_abs, sq_abs]

/-- **The Cartesian transport of the `s`-state eigenfunction is the cusped radial function**
    `x ↦ (sphericalNorm 0 0) · R_{n0}(‖x‖)`.  This is the witness whose `MemSobolevH2`
    membership and `weakLaplacian` realise the reverse direction. -/
lemma chartRealization_symm_eigenfunction_coeFn (n : ℕ) (hn : 0 + 1 ≤ n)
    (hm : |(0 : ℤ)| ≤ (0 : ℤ)) :
    ⇑(chartRealization.symm (hydrogenEigenfunction n 0 0 hn hm))
      =ᵐ[volume] fun x : R3 => (sphericalNorm 0 0 : ℂ) * Rc n 0 hn ‖x‖ := by
  have hsymm := chartRealization_symm_coeFn (hydrogenEigenfunction n 0 0 hn hm)
  have htrans := (measurePreserving_sphereChartInv.quasiMeasurePreserving).ae_eq_comp
    (eigenfunction_sph_coeFn n hn hm)
  filter_upwards [hsymm, htrans] with x hx ht
  rw [hx]
  simp only [Function.comp_apply] at ht
  rw [ht, sphereChartInv_fst]

/-! ## Classical first derivatives of a radial function off the origin

These feed the weak-derivative analysis: the first weak derivative of the cusped
function `c·R(‖·‖)` equals its classical gradient off the origin, established by a smooth
cutoff integration by parts.  Recorded here are the classical Fréchet derivative `∂ᵢ(g∘‖·‖) =
(xᵢ/‖x‖)·g′(‖x‖)`, its boundedness (`≤ |g′|`, the key input to the vanishing of the cutoff
shell term), and `C²` smoothness away from the origin. -/

/-- **Gradient of the Euclidean norm off the origin**, `∇‖·‖(x) = x/‖x‖`. -/
lemma hasFDerivAt_norm_ne_zero {x : R3} (hx : x ≠ 0) :
    HasFDerivAt (fun y : R3 => ‖y‖) ((‖x‖⁻¹ : ℝ) • innerSL ℝ x) x := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hsq : (‖x‖ : ℝ) ^ 2 ≠ 0 := by positivity
  have hq : HasFDerivAt (fun y : R3 => ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * ‖x‖)) (‖x‖ ^ 2) := by
    have h := Real.hasDerivAt_sqrt hsq
    rwa [Real.sqrt_sq hxpos.le] at h
  have hcomp := hsqrt.comp_hasFDerivAt x hq
  simp only [Function.comp_def] at hcomp
  have hfun : (fun y : R3 => Real.sqrt (‖y‖ ^ 2)) = fun y : R3 => ‖y‖ := by
    funext y; rw [Real.sqrt_sq (norm_nonneg y)]
  rw [hfun] at hcomp
  convert hcomp using 1
  ext y
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  field_simp

/-- **Fréchet derivative of a radial composition `g(‖·‖)` off the origin.** -/
lemma hasFDerivAt_radial (g : ℝ → ℂ) {g' : ℂ} {x : R3} (hx : x ≠ 0)
    (hg : HasDerivAt g g' ‖x‖) :
    HasFDerivAt (fun y : R3 => g ‖y‖)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) g').comp
        ((‖x‖⁻¹ : ℝ) • innerSL ℝ x)) x :=
  hg.hasFDerivAt.comp x (hasFDerivAt_norm_ne_zero hx)

/-- The `i`-th classical partial derivative of `g(‖·‖)` is `(xᵢ/‖x‖)·g′(‖x‖)`. -/
private lemma fderiv_radial_apply (g : ℝ → ℂ) {g' : ℂ} {x : R3} (hx : x ≠ 0)
    (hg : HasDerivAt g g' ‖x‖) (i : Fin 3) :
    fderiv ℝ (fun y : R3 => g ‖y‖) x (EuclideanSpace.single i 1)
      = ((x i / ‖x‖ : ℝ) : ℂ) * g' := by
  rw [(hasFDerivAt_radial g hx hg).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, one_mul, RCLike.conj_to_real, Complex.real_smul,
    smul_eq_mul]
  push_cast
  ring

/-- A coordinate is bounded by the norm, `|xᵢ| ≤ ‖x‖`. -/
private lemma abs_coord_le_norm (x : R3) (i : Fin 3) : |x.ofLp i| ≤ ‖x‖ := by
  have h : ⟪x, EuclideanSpace.single i (1 : ℝ)⟫_ℝ = x.ofLp i := by
    rw [EuclideanSpace.inner_single_right]; simp
  calc |x.ofLp i| = ‖⟪x, EuclideanSpace.single i (1 : ℝ)⟫_ℝ‖ := by rw [h, Real.norm_eq_abs]
    _ ≤ ‖x‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ := norm_inner_le_norm _ _
    _ = ‖x‖ := by rw [PiLp.norm_single]; simp

/-- The `i`-th partial derivative of `g(‖·‖)` is bounded by `|g′(‖x‖)|` (the bound that makes
    the cutoff shell term vanish in the weak-derivative IBP). -/
lemma norm_fderiv_radial_le (g : ℝ → ℂ) {g' : ℂ} {x : R3} (hx : x ≠ 0)
    (hg : HasDerivAt g g' ‖x‖) (i : Fin 3) :
    ‖fderiv ℝ (fun y : R3 => g ‖y‖) x (EuclideanSpace.single i 1)‖ ≤ ‖g'‖ := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [fderiv_radial_apply g hx hg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_div, abs_of_pos hxpos]
  calc |x.ofLp i| / ‖x‖ * ‖g'‖ ≤ 1 * ‖g'‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [div_le_one hxpos]; exact abs_coord_le_norm x i
    _ = ‖g'‖ := one_mul _

/-- The gradient (operator norm of the Fréchet derivative) of `g(‖·‖)` is bounded by
    `‖g′(‖x‖)‖` off the origin.  This bounds `∇f` near the origin, which makes the cutoff
    shell terms vanish in the Green's-identity integration by parts. -/
lemma norm_fderiv_radial_op_le (g : ℝ → ℂ) {g' : ℂ} {x : R3} (hx : x ≠ 0)
    (hg : HasDerivAt g g' ‖x‖) :
    ‖fderiv ℝ (fun y : R3 => g ‖y‖) x‖ ≤ ‖g'‖ := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [(hasFDerivAt_radial g hx hg).fderiv]
  calc ‖(ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) g').comp ((‖x‖⁻¹ : ℝ) • innerSL ℝ x)‖
      ≤ ‖ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) g'‖ * ‖(‖x‖⁻¹ : ℝ) • innerSL ℝ x‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖g'‖ * (‖x‖⁻¹ * ‖x‖) := by
        rw [ContinuousLinearMap.norm_smulRight_apply, norm_one, one_mul, norm_smul,
          norm_inv, Real.norm_eq_abs, abs_of_pos hxpos, innerSL_apply_norm]
    _ = ‖g'‖ := by rw [inv_mul_cancel₀ (ne_of_gt hxpos), mul_one]

/-- `g(‖·‖)` is `C²` away from the origin (`g` a `C²` radial profile). -/
lemma contDiffAt_radial (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) {x : R3} (hx : x ≠ 0) :
    ContDiffAt ℝ 2 (fun y : R3 => g ‖y‖) x :=
  hg.contDiffAt.comp x (contDiffAt_norm ℝ hx)

/-! ## Second derivatives of a radial function off the origin

The second cutoff integration by parts (applied to `v = ∂ⱼf`) needs `∂ⱼ∂ⱼf` to be integrable
against the test function.  For the cusped radial `f = g(‖·‖)` the classical second derivative has
a `1/‖x‖` singularity at the origin (`∂ⱼ∂ᵢf ∼ g″·xᵢxⱼ/r² + g′·(δᵢⱼ/r − xᵢxⱼ/r³)`), which is
locally `L²` in `ℝ³`.  The key estimate `‖∇(∂ⱼf)(x)‖ ≤ ‖g″(‖x‖)‖ + 2‖g′(‖x‖)‖/‖x‖` is obtained
from the product rule `∂ⱼf = (xⱼ/‖x‖)·g′(‖x‖)`: the radial factor `g′(‖·‖)` contributes `‖g″‖`
and the homogeneous-degree-`0` factor `xⱼ/‖x‖` contributes the `2/‖x‖`. -/

/-- Gradient of the inverse Euclidean norm off the origin:
    `∇(‖·‖⁻¹)(x) = −‖x‖⁻² • (‖x‖⁻¹ • innerSL x)`. -/
private lemma hasFDerivAt_inv_norm {x : R3} (hx : x ≠ 0) :
    HasFDerivAt (fun y : R3 => ‖y‖⁻¹)
      ((-(‖x‖ ^ 2)⁻¹) • ((‖x‖⁻¹ : ℝ) • innerSL ℝ x)) x := by
  have hr : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  exact (hasDerivAt_inv (ne_of_gt hr)).comp_hasFDerivAt x (hasFDerivAt_norm_ne_zero hx)

/-- The cusp-direction function `y ↦ yⱼ/‖y‖` (written via `innerSL`) is differentiable off the
    origin, with gradient norm `≤ 2/‖x‖`. -/
private lemma fderiv_coord_div_norm_bound {x : R3} (hx : x ≠ 0) (j : Fin 3) :
    DifferentiableAt ℝ
        (fun y : R3 => (innerSL ℝ (EuclideanSpace.single j (1 : ℝ))) y * ‖y‖⁻¹) x ∧
      ‖fderiv ℝ (fun y : R3 => (innerSL ℝ (EuclideanSpace.single j (1 : ℝ))) y * ‖y‖⁻¹) x‖
        ≤ 2 / ‖x‖ := by
  have hr : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hpfd : HasFDerivAt (fun y => (innerSL ℝ (EuclideanSpace.single j (1 : ℝ))) y)
      (innerSL ℝ (EuclideanSpace.single j (1 : ℝ))) x :=
    (innerSL ℝ (EuclideanSpace.single j (1 : ℝ))).hasFDerivAt
  have hqfd : HasFDerivAt (fun y : R3 => ‖y‖⁻¹)
      ((-(‖x‖ ^ 2)⁻¹) • ((‖x‖⁻¹ : ℝ) • innerSL ℝ x)) x := hasFDerivAt_inv_norm hx
  have hmul := hpfd.mul hqfd
  refine ⟨hmul.differentiableAt, ?_⟩
  rw [show (fun y : R3 => (innerSL ℝ (EuclideanSpace.single j (1 : ℝ))) y * ‖y‖⁻¹)
        = (fun y : R3 => (innerSL ℝ (EuclideanSpace.single j (1 : ℝ))) y)
            * fun y : R3 => ‖y‖⁻¹ from rfl, hmul.fderiv]
  have he1 : ‖(EuclideanSpace.single j (1 : ℝ) : R3)‖ = 1 := by rw [PiLp.norm_single, norm_one]
  have hpnorm : ‖innerSL ℝ (EuclideanSpace.single j (1 : ℝ))‖ = 1 := by
    rw [innerSL_apply_norm, he1]
  have hpx : ‖(innerSL ℝ (EuclideanSpace.single j (1 : ℝ))) x‖ ≤ ‖x‖ := by
    rw [innerSL_apply_apply]
    calc ‖⟪EuclideanSpace.single j (1 : ℝ), x⟫_ℝ‖
          ≤ ‖(EuclideanSpace.single j (1 : ℝ) : R3)‖ * ‖x‖ := norm_inner_le_norm _ _
      _ = ‖x‖ := by rw [he1, one_mul]
  have hqnorm : ‖((-(‖x‖ ^ 2)⁻¹) • ((‖x‖⁻¹ : ℝ) • innerSL ℝ x))‖ = (‖x‖ ^ 2)⁻¹ := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, innerSL_apply_norm,
      abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
    rw [sq, mul_inv, mul_assoc, inv_mul_cancel₀ hr.ne', mul_one]
  have hB : ‖(‖x‖⁻¹ : ℝ) • (innerSL ℝ (EuclideanSpace.single j (1 : ℝ)))‖ = ‖x‖⁻¹ := by
    rw [norm_smul, hpnorm, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
  have hfin : ‖x‖ * (‖x‖ ^ 2)⁻¹ + ‖x‖⁻¹ = 2 / ‖x‖ := by field_simp; ring
  calc ‖(innerSL ℝ (EuclideanSpace.single j (1 : ℝ))) x
            • ((-(‖x‖ ^ 2)⁻¹) • ((‖x‖⁻¹ : ℝ) • innerSL ℝ x))
          + (‖x‖⁻¹ : ℝ) • innerSL ℝ (EuclideanSpace.single j (1 : ℝ))‖
      ≤ ‖(innerSL ℝ (EuclideanSpace.single j (1 : ℝ))) x
            • ((-(‖x‖ ^ 2)⁻¹) • ((‖x‖⁻¹ : ℝ) • innerSL ℝ x))‖
          + ‖(‖x‖⁻¹ : ℝ) • innerSL ℝ (EuclideanSpace.single j (1 : ℝ))‖ := norm_add_le _ _
    _ ≤ ‖x‖ * (‖x‖ ^ 2)⁻¹ + ‖x‖⁻¹ := by
        rw [hB]
        gcongr
        rw [norm_smul, hqnorm]
        exact mul_le_mul_of_nonneg_right hpx (by positivity)
    _ = 2 / ‖x‖ := hfin

/-- **Second-derivative bound for a radial `C²` function off the origin.**
    `‖∇(∂ⱼ(g∘‖·‖))(x)‖ ≤ ‖g″(‖x‖)‖ + 2‖g′(‖x‖)‖/‖x‖` — the `1/r` blow-up that is `L²`-integrable
    in `ℝ³`.  This is the input to the second cutoff IBP's integrability obligation. -/
lemma norm_fderiv_fderiv_radial_le (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) {x : R3} (hx : x ≠ 0)
    (j : Fin 3) :
    ‖fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single j 1)) x‖
      ≤ ‖deriv (deriv g) ‖x‖‖ + 2 * ‖deriv g ‖x‖‖ / ‖x‖ := by
  have hr : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hg2 : HasDerivAt (deriv g) (deriv (deriv g) ‖x‖) ‖x‖ :=
    (hg.differentiable_deriv_two ‖x‖).hasDerivAt
  obtain ⟨hu₀diff, hu₀bd⟩ := fderiv_coord_div_norm_bound hx j
  have hu₀fd := hu₀diff.hasFDerivAt
  have hVdiff : DifferentiableAt ℝ (fun y : R3 => deriv g ‖y‖) x :=
    (hasFDerivAt_radial (deriv g) hx hg2).differentiableAt
  have hVfd := hVdiff.hasFDerivAt
  have hVbd : ‖fderiv ℝ (fun y : R3 => deriv g ‖y‖) x‖ ≤ ‖deriv (deriv g) ‖x‖‖ :=
    norm_fderiv_radial_op_le (deriv g) hx hg2
  have hu₀x : ‖(innerSL ℝ (EuclideanSpace.single j (1 : ℝ))) x * ‖x‖⁻¹‖ ≤ 1 := by
    have he1 : ‖(EuclideanSpace.single j (1 : ℝ) : R3)‖ = 1 := by rw [PiLp.norm_single, norm_one]
    have hpx : ‖(innerSL ℝ (EuclideanSpace.single j (1 : ℝ))) x‖ ≤ ‖x‖ := by
      rw [innerSL_apply_apply]
      calc ‖⟪EuclideanSpace.single j (1 : ℝ), x⟫_ℝ‖
            ≤ ‖(EuclideanSpace.single j (1 : ℝ) : R3)‖ * ‖x‖ := norm_inner_le_norm _ _
        _ = ‖x‖ := by rw [he1, one_mul]
    rw [norm_mul, norm_inv, norm_norm]
    calc ‖(innerSL ℝ (EuclideanSpace.single j (1 : ℝ))) x‖ * ‖x‖⁻¹ ≤ ‖x‖ * ‖x‖⁻¹ :=
          mul_le_mul_of_nonneg_right hpx (by positivity)
      _ = 1 := mul_inv_cancel₀ hr.ne'
  have heq : (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single j 1))
      =ᶠ[𝓝 x] (fun y => ((innerSL ℝ (EuclideanSpace.single j (1 : ℝ))) y * ‖y‖⁻¹)
        • deriv g ‖y‖) := by
    filter_upwards [compl_singleton_mem_nhds hx] with y hy
    have hy' : y ≠ 0 := hy
    rw [fderiv_radial_apply g hy'
        ((hg.differentiable (by norm_num)).differentiableAt.hasDerivAt) j, Complex.real_smul]
    congr 1
    rw [innerSL_apply_apply, EuclideanSpace.inner_single_left]
    push_cast
    simp [div_eq_mul_inv]
  have hsmul := hu₀fd.smul hVfd
  rw [heq.fderiv_eq,
    show (fun y : R3 => ((innerSL ℝ (EuclideanSpace.single j (1 : ℝ))) y * ‖y‖⁻¹) • deriv g ‖y‖)
        = (fun y : R3 => (innerSL ℝ (EuclideanSpace.single j (1 : ℝ))) y * ‖y‖⁻¹)
            • fun y : R3 => deriv g ‖y‖ from rfl, hsmul.fderiv]
  calc ‖((innerSL ℝ (EuclideanSpace.single j (1 : ℝ))) x * ‖x‖⁻¹)
            • fderiv ℝ (fun y : R3 => deriv g ‖y‖) x
          + (fderiv ℝ (fun y : R3 => (innerSL ℝ (EuclideanSpace.single j (1 : ℝ))) y * ‖y‖⁻¹)
              x).smulRight (deriv g ‖x‖)‖
      ≤ ‖((innerSL ℝ (EuclideanSpace.single j (1 : ℝ))) x * ‖x‖⁻¹)
            • fderiv ℝ (fun y : R3 => deriv g ‖y‖) x‖
          + ‖(fderiv ℝ (fun y : R3 => (innerSL ℝ (EuclideanSpace.single j (1 : ℝ))) y * ‖y‖⁻¹)
              x).smulRight (deriv g ‖x‖)‖ := norm_add_le _ _
    _ ≤ ‖deriv (deriv g) ‖x‖‖ + 2 / ‖x‖ * ‖deriv g ‖x‖‖ := by
        gcongr ?_ + ?_
        · rw [norm_smul]
          exact (mul_le_mul hu₀x hVbd (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
        · rw [ContinuousLinearMap.norm_smulRight_apply]
          exact mul_le_mul_of_nonneg_right hu₀bd (norm_nonneg _)
    _ = ‖deriv (deriv g) ‖x‖‖ + 2 * ‖deriv g ‖x‖‖ / ‖x‖ := by ring

/-! ## The 3-D radial cutoff `χ_ε`

`χ_ε(x) = cutoffP(‖x‖/ε)` is the radial cutoff for the Green's-identity integration by parts:
`0` on `ball 0 ε`, `1` outside `ball 0 (2ε)`, differentiable everywhere (it is constantly `0` near
the origin, so the norm's non-smoothness there is irrelevant), with gradient bounded by `M/ε`.
Multiplying the cusped `f` by `χ_ε` produces a globally-`C¹` function to which the classical
integration by parts applies; the `O(1/ε)` gradient against the `O(ε³)` shell makes the error
vanish as `ε → 0`. -/

/-- The 3-D radial cutoff: `0` on `ball 0 ε`, `1` outside `ball 0 (2ε)`. -/
def chi (ε : ℝ) (x : R3) : ℝ := cutoffP (‖x‖ / ε)

/-- The cutoff vanishes on the closed ball `‖x‖ ≤ ε`. -/
private lemma chi_eq_zero {ε : ℝ} (hε : 0 < ε) {x : R3} (hx : ‖x‖ ≤ ε) : chi ε x = 0 := by
  rw [chi]; exact cutoffP_eq_zero (by rw [div_le_one hε]; exact hx)

/-- The cutoff is constantly `0` in a neighbourhood of the origin. -/
private lemma chi_eventually_zero {ε : ℝ} (hε : 0 < ε) : chi ε =ᶠ[nhds 0] (fun _ => 0) := by
  filter_upwards [Metric.ball_mem_nhds 0 hε] with x hx
  rw [Metric.mem_ball, dist_zero_right] at hx
  exact chi_eq_zero hε (le_of_lt hx)

/-- The cutoff has vanishing Fréchet derivative at the origin (it is constantly `0` nearby). -/
private lemma hasFDerivAt_chi_zero {ε : ℝ} (hε : 0 < ε) :
    HasFDerivAt (chi ε) (0 : R3 →L[ℝ] ℝ) 0 := by
  refine HasFDerivAt.congr_of_eventuallyEq ?_ (chi_eventually_zero hε)
  exact hasFDerivAt_const (0 : ℝ) (0 : R3)

/-- Off the origin, the cutoff's Fréchet derivative (radial-composition form). -/
private lemma hasFDerivAt_chi {ε : ℝ} (_hε : 0 < ε) {x : R3} (hx : x ≠ 0) :
    HasFDerivAt (chi ε)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv cutoffP (‖x‖ / ε) / ε)).comp
        ((‖x‖⁻¹ : ℝ) • innerSL ℝ x)) x := by
  have hg : HasDerivAt (fun r : ℝ => cutoffP (r / ε)) (deriv cutoffP (‖x‖ / ε) / ε) ‖x‖ := by
    have h1 : HasDerivAt cutoffP (deriv cutoffP (‖x‖ / ε)) (‖x‖ / ε) :=
      (cutoffP_contDiff.differentiable (by norm_num)).differentiableAt.hasDerivAt
    have h2 : HasDerivAt (fun r : ℝ => r / ε) (1 / ε) ‖x‖ := (hasDerivAt_id ‖x‖).div_const ε
    have h3 := h1.comp ‖x‖ h2
    rw [mul_one_div] at h3
    exact h3
  exact hg.hasFDerivAt.comp x (hasFDerivAt_norm_ne_zero hx)

/-- The cutoff `χ_ε` is everywhere differentiable (constant `0` near the origin, radial
    composition off it). -/
private lemma differentiable_chi {ε : ℝ} (hε : 0 < ε) : Differentiable ℝ (chi ε) := by
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · exact (hasFDerivAt_chi_zero hε).differentiableAt
  · exact (hasFDerivAt_chi hε hx).differentiableAt

/-- The cutoff gradient is bounded by `M/ε` (`M` any global bound on the profile derivative).
    This is the bound that makes the shell terms vanish in the Green's-identity IBP. -/
private lemma norm_fderiv_chi_le {ε : ℝ} (hε : 0 < ε) (x : R3)
    {M : ℝ} (hM : ∀ t : ℝ, |deriv cutoffP t| ≤ M) :
    ‖fderiv ℝ (chi ε) x‖ ≤ M / ε := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [(hasFDerivAt_chi_zero hε).fderiv, norm_zero]
    exact div_nonneg ((abs_nonneg _).trans (hM 0)) hε.le
  · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hL : ‖(‖x‖⁻¹ : ℝ) • innerSL ℝ x‖ = 1 := by
      rw [norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        inv_mul_cancel₀ (ne_of_gt hxpos)]
    have hS : ‖ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv cutoffP (‖x‖ / ε) / ε)‖
        = |deriv cutoffP (‖x‖ / ε)| / ε := by
      rw [ContinuousLinearMap.norm_smulRight_apply, norm_one, one_mul, Real.norm_eq_abs, abs_div,
        abs_of_pos hε]
    rw [(hasFDerivAt_chi hε hx).fderiv]
    calc ‖(ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv cutoffP (‖x‖ / ε) / ε)).comp
            ((‖x‖⁻¹ : ℝ) • innerSL ℝ x)‖
        ≤ ‖ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv cutoffP (‖x‖ / ε) / ε)‖
            * ‖(‖x‖⁻¹ : ℝ) • innerSL ℝ x‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ = |deriv cutoffP (‖x‖ / ε)| / ε := by rw [hS, hL, mul_one]
      _ ≤ M / ε := by gcongr; exact hM _

/-! ## The cutoff integration by parts (per `ε`)

Multiplying the cusped `v` by `χ_ε` produces a globally-`C¹` function `↑χ_ε·v` (the cutoff masks
`v`'s non-smoothness at the origin), to which the classical integration by parts applies.  This is
the per-`ε` step of the master cutoff IBP; the `ε → 0` limit then yields `∫ v·∂ⱼφ = −∫ w·φ`. -/

/-- `↑χ_ε · v` is differentiable everywhere when `v` is differentiable off the origin
    (the cutoff is `0` near the origin, masking the cusp). -/
private lemma differentiableAt_chi_mul {ε : ℝ} (hε : 0 < ε) {v : R3 → ℂ}
    (hv : ∀ x : R3, x ≠ 0 → DifferentiableAt ℝ v x) (x : R3) :
    DifferentiableAt ℝ (fun y => (↑(chi ε y) : ℂ) * v y) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · apply (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : R3) hε] with y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    rw [chi_eq_zero hε hy.le, Complex.ofReal_zero, zero_mul]
  · have h1 : DifferentiableAt ℝ (fun y => (↑(chi ε y) : ℂ)) x :=
      Complex.ofRealCLM.differentiableAt.comp x (differentiable_chi hε x)
    exact h1.mul (hv x hx)

/-- Off the origin, the product rule for `∂ⱼ(↑χ_ε · v)`. -/
private lemma fderiv_chi_mul_apply {ε : ℝ} (hε : 0 < ε) {v : R3 → ℂ} {x : R3}
    (hv : HasFDerivAt v (fderiv ℝ v x) x) (j : Fin 3) :
    fderiv ℝ (fun y => (↑(chi ε y) : ℂ) * v y) x (EuclideanSpace.single j 1)
      = (↑(chi ε x) : ℂ) * (fderiv ℝ v x (EuclideanSpace.single j 1))
        + v x * (↑(fderiv ℝ (chi ε) x (EuclideanSpace.single j 1)) : ℂ) := by
  have hχ : HasFDerivAt (fun y => (↑(chi ε y) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (chi ε) x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (differentiable_chi hε x).hasFDerivAt
  rw [show (fun y : R3 => (↑(chi ε y) : ℂ) * v y) = (fun y => (↑(chi ε y) : ℂ)) * v from rfl,
    (hχ.mul hv).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]

/-- `↑χ_ε · v` is continuous everywhere when `v` is continuous off the origin. -/
private lemma continuous_chi_mul {ε : ℝ} (hε : 0 < ε) {v : R3 → ℂ}
    (hv : ContinuousOn v {(0 : R3)}ᶜ) : Continuous (fun y => (↑(chi ε y) : ℂ) * v y) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · apply ContinuousAt.congr (continuousAt_const (x := (0 : R3)) (y := (0 : ℂ)))
    filter_upwards [Metric.ball_mem_nhds (0 : R3) hε] with y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    rw [chi_eq_zero hε hy.le, Complex.ofReal_zero, zero_mul]
  · exact (Complex.continuous_ofReal.continuousAt.comp (differentiable_chi hε x).continuousAt).mul
      (hv.continuousAt (compl_singleton_mem_nhds hx))

/-- The cutoff is `C¹` everywhere. -/
private lemma contDiff_chi {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 1 (chi ε) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : R3) hε] with y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact chi_eq_zero hε hy.le
  · have hn : ContDiffAt ℝ 1 (fun y : R3 => ‖y‖ / ε) x :=
      (contDiffAt_norm ℝ hx).div_const ε
    exact (cutoffP_contDiff.contDiffAt.of_le (by norm_num)).comp x hn

/-- `↑χ_ε · v` is `C¹` everywhere when `v` is `C¹` off the origin. -/
private lemma contDiff_chi_mul {ε : ℝ} (hε : 0 < ε) {v : R3 → ℂ}
    (hv : ContDiffOn ℝ 1 v {(0 : R3)}ᶜ) : ContDiff ℝ 1 (fun y => (↑(chi ε y) : ℂ) * v y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : R3) hε] with y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    rw [chi_eq_zero hε hy.le, Complex.ofReal_zero, zero_mul]
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x (contDiff_chi hε).contDiffAt).mul
      (hv.contDiffAt (compl_singleton_mem_nhds hx))

/-- **Per-`ε` integration by parts.** With the cutoff masking the cusp, `↑χ_ε·v` is globally
    `C¹`, so the classical integration by parts applies. -/
private lemma chi_ibp {ε : ℝ} (hε : 0 < ε) {v w : R3 → ℂ} (j : Fin 3)
    (hv : ContDiffOn ℝ 1 v {(0 : R3)}ᶜ)
    (hvw : ∀ x : R3, x ≠ 0 → fderiv ℝ v x (EuclideanSpace.single j 1) = w x)
    {φ : R3 → ℂ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ x, (↑(chi ε x) : ℂ) * v x * fderiv ℝ φ x (EuclideanSpace.single j 1)
      = - ∫ x, (↑(fderiv ℝ (chi ε) x (EuclideanSpace.single j 1)) * v x
              + ↑(chi ε x) * w x) * φ x := by
  set F : R3 → ℂ := fun y => (↑(chi ε y) : ℂ) * v y with _hF
  have hv_diff : ∀ x : R3, x ≠ 0 → DifferentiableAt ℝ v x :=
    fun x hx => (hv.contDiffAt (compl_singleton_mem_nhds hx)).differentiableAt one_ne_zero
  have hFc1 : ContDiff ℝ 1 F := contDiff_chi_mul hε hv
  have hFcont : Continuous F := hFc1.continuous
  have hdF : Continuous (fun x => fderiv ℝ F x (EuclideanSpace.single j 1)) :=
    (hFc1.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const)
  have hφcont : Continuous φ := hφ.continuous
  have hdφ : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single j 1)) :=
    (hφ.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hdφ_supp : HasCompactSupport (fun x => fderiv ℝ φ x (EuclideanSpace.single j 1)) :=
    (hφc.fderiv ℝ).comp_left (g := fun L : R3 →L[ℝ] ℂ => L (EuclideanSpace.single j 1))
      (ContinuousLinearMap.zero_apply _)
  have hfg : Integrable (fun x => F x * φ x) :=
    (hFcont.mul hφcont).integrable_of_hasCompactSupport hφc.mul_left
  have hfg' : Integrable (fun x => F x * fderiv ℝ φ x (EuclideanSpace.single j 1)) :=
    (hFcont.mul hdφ).integrable_of_hasCompactSupport hdφ_supp.mul_left
  have hf'g : Integrable (fun x => fderiv ℝ F x (EuclideanSpace.single j 1) * φ x) :=
    (hdF.mul hφcont).integrable_of_hasCompactSupport hφc.mul_left
  have hf : ∀ x ∈ tsupport φ, DifferentiableAt ℝ F x :=
    fun x _ => differentiableAt_chi_mul hε hv_diff x
  have hg : ∀ x ∈ tsupport F, DifferentiableAt ℝ φ x :=
    fun x _ => (hφ.differentiable (by simp)) x
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure R3)) (v := EuclideanSpace.single j 1)
    hf'g hfg' hfg hf hg
  rw [show (fun x => (↑(chi ε x) : ℂ) * v x * fderiv ℝ φ x (EuclideanSpace.single j 1))
        = fun x => F x * fderiv ℝ φ x (EuclideanSpace.single j 1) from rfl, key]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_ne_zero_R3] with x hx
  rw [fderiv_chi_mul_apply hε ((hv_diff x hx).hasFDerivAt) j, hvw x hx]
  ring

/-! ## The `ε → 0` limit: cutoff far-field behaviour and the shell estimate -/

/-- The cutoff equals `1` outside `ball 0 (2ε)`. -/
private lemma chi_eq_one {ε : ℝ} (hε : 0 < ε) {x : R3} (hx : 2 * ε ≤ ‖x‖) : chi ε x = 1 := by
  rw [chi]; apply cutoffP_eq_one
  rw [le_div_iff₀ hε]; linarith

/-- The cutoff is constantly `1` near any point with `‖x‖ > 2ε`. -/
private lemma chi_eventually_one {ε : ℝ} (hε : 0 < ε) {x : R3} (hx : 2 * ε < ‖x‖) :
    chi ε =ᶠ[𝓝 x] (fun _ => 1) := by
  have hopen : {y : R3 | 2 * ε < ‖y‖} ∈ 𝓝 x :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hx
  filter_upwards [hopen] with y hy
  exact chi_eq_one hε (le_of_lt hy)

/-- The cutoff gradient vanishes outside `closedBall 0 (2ε)`. -/
private lemma fderiv_chi_eq_zero_far {ε : ℝ} (hε : 0 < ε) {x : R3} (hx : 2 * ε < ‖x‖) :
    fderiv ℝ (chi ε) x = 0 := by
  rw [(chi_eventually_one hε hx).fderiv_eq]
  exact (hasFDerivAt_const (1 : ℝ) x).fderiv

/-- For `x ≠ 0`, the cutoff at scale `1/(n+1)` tends to `1`. -/
private lemma chi_tendsto_one {x : R3} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => chi (1 / (n + 1)) x) atTop (𝓝 1) := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  apply Tendsto.congr' _ tendsto_const_nhds
  have hlim : Tendsto (fun n : ℕ => 2 * (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
  have hev : ∀ᶠ n : ℕ in atTop, (2 : ℝ) * (1 / (n + 1)) < ‖x‖ := hlim.eventually_lt_const hxpos
  filter_upwards [hev] with n hn
  exact (chi_eq_one (by positivity) (le_of_lt hn)).symm

/-- **Shell bound.** The cutoff-gradient term is `O(ε²)`: its integrand lives in the shell
    `ε ≤ ‖x‖ ≤ 2ε` where `‖∇χ_ε‖ ≤ M/ε`, against a ball of volume `O(ε³)`. -/
private lemma shell_bound {v : R3 → ℂ} (j : Fin 3) {Mv Md Mφ r₀ : ℝ}
    (hMv : ∀ x : R3, ‖x‖ ≤ r₀ → ‖v x‖ ≤ Mv) (hMv0 : 0 ≤ Mv)
    (hMd : ∀ t : ℝ, |deriv cutoffP t| ≤ Md) (hMd0 : 0 ≤ Md)
    {φ : R3 → ℂ} (hMφ : ∀ x : R3, ‖φ x‖ ≤ Mφ)
    {ε : ℝ} (hε : 0 < ε) (hεr : 2 * ε ≤ r₀) :
    ‖∫ x, (↑(fderiv ℝ (chi ε) x (EuclideanSpace.single j 1)) : ℂ) * v x * φ x‖
      ≤ (Md * Mv * Mφ) * (volume (Metric.closedBall (0 : R3) (2 * ε))).toReal / ε := by
  set g : R3 → ℂ := fun x => (↑(fderiv ℝ (chi ε) x (EuclideanSpace.single j 1)) : ℂ) * v x * φ x
    with hg
  have hMdε : (0 : ℝ) ≤ Md / ε := div_nonneg hMd0 hε.le
  have hbound : ∀ x : R3, ‖g x‖ ≤
      (Metric.closedBall (0 : R3) (2 * ε)).indicator (fun _ => Md / ε * Mv * Mφ) x := by
    intro x
    classical
    rw [Set.indicator_apply]
    split_ifs with hxin
    · rw [Metric.mem_closedBall, dist_zero_right] at hxin
      have hdj : |fderiv ℝ (chi ε) x (EuclideanSpace.single j 1)| ≤ Md / ε := by
        calc |fderiv ℝ (chi ε) x (EuclideanSpace.single j 1)|
            ≤ ‖fderiv ℝ (chi ε) x‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ := by
              rw [← Real.norm_eq_abs]; exact (fderiv ℝ (chi ε) x).le_opNorm _
          _ ≤ Md / ε := by
              rw [PiLp.norm_single, norm_one, mul_one]; exact norm_fderiv_chi_le hε x hMd
      have hvx : ‖v x‖ ≤ Mv := hMv x (le_trans hxin hεr)
      calc ‖g x‖ = |fderiv ℝ (chi ε) x (EuclideanSpace.single j 1)| * ‖v x‖ * ‖φ x‖ := by
            rw [hg]; simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ Md / ε * Mv * Mφ :=
            mul_le_mul (mul_le_mul hdj hvx (norm_nonneg _) hMdε) (hMφ x) (norm_nonneg _)
              (mul_nonneg hMdε hMv0)
    · rw [Metric.mem_closedBall, dist_zero_right, not_le] at hxin
      rw [hg]
      simp only [fderiv_chi_eq_zero_far hε hxin, ContinuousLinearMap.zero_apply,
        Complex.ofReal_zero, zero_mul, norm_zero, le_refl]
  have hint_bound : Integrable
      ((Metric.closedBall (0 : R3) (2 * ε)).indicator (fun _ => Md / ε * Mv * Mφ)) volume :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      (integrableOn_const measure_closedBall_lt_top.ne)
  calc ‖∫ x, g x‖ ≤ ∫ x, ‖g x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (Metric.closedBall (0 : R3) (2 * ε)).indicator
          (fun _ => Md / ε * Mv * Mφ) x :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
          hint_bound (Filter.Eventually.of_forall hbound)
    _ = Md / ε * Mv * Mφ * (volume (Metric.closedBall (0 : R3) (2 * ε))).toReal := by
        rw [integral_indicator_const _ measurableSet_closedBall, measureReal_def, smul_eq_mul,
          mul_comm]
    _ = Md * Mv * Mφ * (volume (Metric.closedBall (0 : R3) (2 * ε))).toReal / ε := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div]

/-- The cutoff-gradient (shell) term tends to `0` as `ε_n = 1/(n+1) → 0` (`O(ε²)` decay). -/
private lemma shell_tendsto_zero {v : R3 → ℂ} (j : Fin 3) {Mv r₀ : ℝ} (hr₀ : 0 < r₀)
    (hMv : ∀ x : R3, ‖x‖ ≤ r₀ → ‖v x‖ ≤ Mv) (hMv0 : 0 ≤ Mv)
    {φ : R3 → ℂ} (hφc : Continuous φ) (hφcs : HasCompactSupport φ) :
    Tendsto (fun n : ℕ => ∫ x, (↑(fderiv ℝ (chi (1 / (n + 1))) x (EuclideanSpace.single j 1)) : ℂ)
      * v x * φ x) atTop (𝓝 0) := by
  obtain ⟨Mφ, hMφ⟩ := hφc.bounded_above_of_compact_support hφcs
  obtain ⟨Md, hMd0, hMd⟩ := deriv_cutoffP_bounded
  set c₁ := (volume (Metric.closedBall (0 : R3) 1)).toReal with _hc₁
  refine squeeze_zero_norm' (a := fun n : ℕ => 8 * (Md * Mv * Mφ) * c₁ * (1 / (n + 1)) ^ 2) ?_ ?_
  · have hev : ∀ᶠ n : ℕ in atTop, (2 : ℝ) * (1 / (n + 1)) ≤ r₀ := by
      have hlim : Tendsto (fun n : ℕ => 2 * (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
        simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
      exact hlim.eventually_le_const hr₀
    filter_upwards [hev] with n hn
    have hεpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    have hball : (volume (Metric.closedBall (0 : R3) (2 * (1 / (n + 1))))).toReal
        = (2 * (1 / (n + 1))) ^ 3 * c₁ := by
      rw [← measureReal_def, Measure.addHaar_real_closedBall' volume 0 (by positivity),
        measureReal_def, finrank_euclideanSpace_fin]
    have hb := shell_bound j hMv hMv0 hMd hMd0 hMφ hεpos hn
    rw [hball] at hb
    refine hb.trans (le_of_eq ?_)
    field_simp
    ring
  · have hbase : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hpow : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ)) ^ 2) atTop (𝓝 (0 : ℝ)) := by
      simpa using hbase.pow 2
    have hmul : Continuous (fun y : ℝ => 8 * (Md * Mv * Mφ) * c₁ * y) := by fun_prop
    have hcomp := (hmul.tendsto 0).comp hpow
    simpa only [Function.comp_def, mul_zero] using hcomp

/-! ## The master cutoff integration by parts

Assembling the per-`ε` IBP (`chi_ibp`), the two dominated-convergence limits, and the vanishing
shell estimate (`shell_tendsto_zero`) into the weak-derivative identity `∫ v·∂ⱼφ = −∫ w·φ` for a
function `v` that is continuous and `C¹` off the origin and bounded near it, with classical
`j`-partial `w` off the origin.  The boundedness of `v` near `0` is exactly what makes the cusp
contribute nothing in the `ε → 0` limit. -/

/-- The cutoff gradient vanishes on the open ball `ball 0 ε` (the cutoff is constantly `0`
    there).  This is the near-origin companion of `fderiv_chi_eq_zero_far`. -/
private lemma fderiv_chi_eq_zero_near {ε : ℝ} (hε : 0 < ε) {x : R3} (hx : ‖x‖ < ε) :
    fderiv ℝ (chi ε) x = 0 := by
  have hmem : Metric.ball (0 : R3) ε ∈ 𝓝 x := by
    apply Metric.isOpen_ball.mem_nhds
    rw [Metric.mem_ball, dist_zero_right]; exact hx
  have heq : chi ε =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [hmem] with y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact chi_eq_zero hε hy.le
  rw [heq.fderiv_eq]
  exact (hasFDerivAt_const (0 : ℝ) x).fderiv

/-- `↑(∂ⱼχ_ε) · v` is continuous everywhere when `v` is continuous off the origin
    (the cutoff gradient is `0` near the origin, masking `v`'s cusp). -/
private lemma continuous_fderiv_chi_mul {ε : ℝ} (hε : 0 < ε) {v : R3 → ℂ}
    (hv : ContinuousOn v {(0 : R3)}ᶜ) (j : Fin 3) :
    Continuous (fun x => (↑(fderiv ℝ (chi ε) x (EuclideanSpace.single j 1)) : ℂ) * v x) := by
  have hd : Continuous (fun y => fderiv ℝ (chi ε) y (EuclideanSpace.single j (1 : ℝ))) :=
    ((contDiff_chi hε).continuous_fderiv_apply one_ne_zero).comp
      (continuous_id.prodMk continuous_const)
  have hdc : Continuous (fun y => (↑(fderiv ℝ (chi ε) y (EuclideanSpace.single j 1)) : ℂ)) :=
    Complex.continuous_ofReal.comp hd
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · apply ContinuousAt.congr (continuousAt_const (x := (0 : R3)) (y := (0 : ℂ)))
    filter_upwards [Metric.ball_mem_nhds (0 : R3) hε] with y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    rw [fderiv_chi_eq_zero_near hε hy, ContinuousLinearMap.zero_apply, Complex.ofReal_zero,
      zero_mul]
  · exact hdc.continuousAt.mul (hv.continuousAt (compl_singleton_mem_nhds hx))

/-- **The master cutoff integration by parts.**  For `v` continuous and `C¹` off the origin,
    bounded near it, with classical `j`-partial `w` off the origin (`Integrable (w·φ)`), the
    weak-derivative identity `∫ v·∂ⱼφ = −∫ w·φ` holds against any test function `φ`.  The cusp
    at the origin contributes nothing because `v` is bounded there. -/
lemma master_ibp {v w : R3 → ℂ} (j : Fin 3)
    (hvcont : ContinuousOn v {(0 : R3)}ᶜ) (hv_c1 : ContDiffOn ℝ 1 v {(0 : R3)}ᶜ)
    (hvw : ∀ x : R3, x ≠ 0 → fderiv ℝ v x (EuclideanSpace.single j 1) = w x)
    {Mv r₀ : ℝ} (hr₀ : 0 < r₀) (hMv : ∀ x : R3, ‖x‖ ≤ r₀ → ‖v x‖ ≤ Mv) (hMv0 : 0 ≤ Mv)
    {φ : R3 → ℂ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hvφ : Integrable (fun x => v x * fderiv ℝ φ x (EuclideanSpace.single j 1)))
    (hwφ : Integrable (fun x => w x * φ x)) :
    ∫ x, v x * fderiv ℝ φ x (EuclideanSpace.single j 1) = - ∫ x, w x * φ x := by
  have hdφ_cont : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single j (1 : ℝ))) :=
    (hφ.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hae : ∀ᵐ x : R3, x ≠ 0 := ae_ne_zero_R3
  -- DCT 1: ∫ ↑χ·v·∂ⱼφ → ∫ v·∂ⱼφ
  have hdct1 : Tendsto (fun n : ℕ => ∫ x, (↑(chi (1 / (n + 1)) x) : ℂ) * v x
      * fderiv ℝ φ x (EuclideanSpace.single j 1)) atTop
      (𝓝 (∫ x, v x * fderiv ℝ φ x (EuclideanSpace.single j 1))) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => ‖v x * fderiv ℝ φ x (EuclideanSpace.single j 1)‖)
    · intro n
      exact ((continuous_chi_mul (by positivity) hvcont).mul hdφ_cont).aestronglyMeasurable
    · exact hvφ.norm
    · intro n
      refine Filter.Eventually.of_forall (fun x => ?_)
      rw [show (↑(chi (1 / (n + 1)) x) : ℂ) * v x * fderiv ℝ φ x (EuclideanSpace.single j 1)
            = (↑(chi (1 / (n + 1)) x) : ℂ)
              * (v x * fderiv ℝ φ x (EuclideanSpace.single j 1)) by ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, chi, abs_of_nonneg (cutoffP_nonneg _)]
      calc cutoffP (‖x‖ / (1 / (n + 1)))
              * ‖v x * fderiv ℝ φ x (EuclideanSpace.single j 1)‖
          ≤ 1 * ‖v x * fderiv ℝ φ x (EuclideanSpace.single j 1)‖ :=
            mul_le_mul_of_nonneg_right (cutoffP_le_one _) (norm_nonneg _)
        _ = ‖v x * fderiv ℝ φ x (EuclideanSpace.single j 1)‖ := one_mul _
    · filter_upwards [hae] with x hx
      have h1 : Tendsto (fun n : ℕ => (↑(chi (1 / (n + 1)) x) : ℂ)) atTop (𝓝 1) := by
        simpa [Function.comp_def] using
          (Complex.continuous_ofReal.tendsto 1).comp (chi_tendsto_one hx)
      have h2 := h1.mul (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => v x * fderiv ℝ φ x (EuclideanSpace.single j 1)) atTop
          (𝓝 (v x * fderiv ℝ φ x (EuclideanSpace.single j 1))))
      simpa [mul_assoc] using h2
  -- DCT 2: ∫ ↑χ·(w·φ) → ∫ w·φ
  have hdct2 : Tendsto (fun n : ℕ => ∫ x, (↑(chi (1 / (n + 1)) x) : ℂ) * (w x * φ x)) atTop
      (𝓝 (∫ x, w x * φ x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖w x * φ x‖)
    · intro n
      exact ((Complex.continuous_ofReal.comp
        (differentiable_chi (by positivity)).continuous).aestronglyMeasurable).mul hwφ.1
    · exact hwφ.norm
    · intro n
      refine Filter.Eventually.of_forall (fun x => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, chi, abs_of_nonneg (cutoffP_nonneg _)]
      calc cutoffP (‖x‖ / (1 / (n + 1))) * ‖w x * φ x‖
          ≤ 1 * ‖w x * φ x‖ := mul_le_mul_of_nonneg_right (cutoffP_le_one _) (norm_nonneg _)
        _ = ‖w x * φ x‖ := one_mul _
    · filter_upwards [hae] with x hx
      have h1 : Tendsto (fun n : ℕ => (↑(chi (1 / (n + 1)) x) : ℂ)) atTop (𝓝 1) := by
        simpa [Function.comp_def] using
          (Complex.continuous_ofReal.tendsto 1).comp (chi_tendsto_one hx)
      have h2 := h1.mul (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => w x * φ x) atTop (𝓝 (w x * φ x)))
      simpa using h2
  -- per-`n` splitting identity, from `chi_ibp` + `integral_add`
  have hkey : ∀ n : ℕ, ∫ x, (↑(chi (1 / (n + 1)) x) : ℂ) * v x
      * fderiv ℝ φ x (EuclideanSpace.single j 1)
      = - ((∫ x, (↑(fderiv ℝ (chi (1 / (n + 1))) x (EuclideanSpace.single j 1)) : ℂ) * v x * φ x)
          + ∫ x, (↑(chi (1 / (n + 1)) x) : ℂ) * (w x * φ x)) := by
    intro n
    have hε : (0 : ℝ) < 1 / (n + 1) := by positivity
    have hg1_int : Integrable (fun x =>
        (↑(fderiv ℝ (chi (1 / (n + 1))) x (EuclideanSpace.single j 1)) : ℂ) * v x * φ x) :=
      ((continuous_fderiv_chi_mul hε hvcont j).mul hφ.continuous).integrable_of_hasCompactSupport
        hφc.mul_left
    have hg2_int : Integrable (fun x => (↑(chi (1 / (n + 1)) x) : ℂ) * (w x * φ x)) :=
      hwφ.bdd_mul
        (Complex.continuous_ofReal.comp (differentiable_chi hε).continuous).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun x => by
          rw [Complex.norm_real, Real.norm_eq_abs, chi, abs_of_nonneg (cutoffP_nonneg _)]
          exact cutoffP_le_one _))
    rw [chi_ibp hε j hv_c1 hvw hφ hφc]
    congr 1
    rw [show (fun x => ((↑(fderiv ℝ (chi (1 / (n + 1))) x (EuclideanSpace.single j 1)) : ℂ) * v x
              + (↑(chi (1 / (n + 1)) x) : ℂ) * w x) * φ x)
          = (fun x =>
              (↑(fderiv ℝ (chi (1 / (n + 1))) x (EuclideanSpace.single j 1)) : ℂ) * v x * φ x
              + (↑(chi (1 / (n + 1)) x) : ℂ) * (w x * φ x)) from funext (fun x => by ring)]
    exact integral_add hg1_int hg2_int
  -- assemble via uniqueness of limits
  have hB : Tendsto (fun n : ℕ => ∫ x, (↑(chi (1 / (n + 1)) x) : ℂ) * v x
      * fderiv ℝ φ x (EuclideanSpace.single j 1)) atTop (𝓝 (- ∫ x, w x * φ x)) := by
    have hsum : Tendsto (fun n : ℕ =>
        (∫ x, (↑(fderiv ℝ (chi (1 / (n + 1))) x (EuclideanSpace.single j 1)) : ℂ) * v x * φ x)
          + ∫ x, (↑(chi (1 / (n + 1)) x) : ℂ) * (w x * φ x)) atTop (𝓝 (∫ x, w x * φ x)) := by
      have := (shell_tendsto_zero j hr₀ hMv hMv0 hφ.continuous hφc).add hdct2
      simpa using this
    exact hsum.neg.congr (fun n => (hkey n).symm)
  exact tendsto_nhds_unique hdct1 hB

end QuantumMechanics.Hydrogen.Spectrum
