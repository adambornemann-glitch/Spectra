/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Perturbation.CoulombBound
import Spectra.QuantumMechanics.Hydrogen.Hamiltonian
import Spectra.QuantumMechanics.Hydrogen.Laplacian.EssentialSpectrum
import Spectra.SpectralTheory.Essential.Weyl
import Spectra.QuantumMechanics.Hydrogen.Laplacian.FreeGreens.Fourier
import Spectra.QuantumMechanics.Hydrogen.Laplacian.FreeGreens.Convolution
import Spectra.SpectralTheory.TranslationKernel
import Spectra.SpectralTheory.IntegralOperatorCompact

/-!
# The hydrogen continuous spectrum `σ_ess(H) = [0, ∞)`

This file assembles the continuous-spectrum half of the hydrogen problem via the abstract Weyl
theorem (`Spectra.Essential.essSpectrum_eq_of_isCompactOperator_perturb`).

**Reduction.** The on-ramp needs a compact `W : L²(ℝ³) →L[ℂ] L²(ℝ³)` with `Bχ − Aχ = W(Aχ − i·χ)`
for `χ` in the domain. For hydrogen `A = laplacianPMap`, `B = hydrogenHamiltonian` and
`Bχ − Aχ = V·χ` (Coulomb), so `W = V·R_i` is forced. This file builds `coulombResolvent` (`= W`) as
a CLM (boundedness from the Hardy relative bound `coulombB_bound` + the resolvent estimate),
verifies `coulomb_hVW`, and obtains `hydrogen_essSpectrum_eq_Ici_of_compact` *given* `W` compact.

**Kernel data for compactness.** The compactness of `W` is proved (in the companion file) from a
*ball* truncation: `truncCoulombBall` keeps the `L²`-integrable `1/|x|` singularity and cuts off
only the `L^∞`-small tail, and the truncated resolvent kernel `Vⁿ(x)·G̃_i(x−y)` lies in
`L²(ℝ³×ℝ³)` (`truncKernelG_memLp`), so each `integralOperator Kₙ` is compact via the A3 gate.

## Main statements

* `coulombResolventAt` / `coulombResolvent` / `coulombResolventHalf` — the Coulomb-perturbed
  resolvent `W = V · R_z` as a bounded operator on `L²(ℝ³)`, at general non-real `z`, at `z = i`,
  and (for the textbook `−½Δ` reduction) at `z = 2i`.
* `coulombResolventLinearAt_bound` — the operator-norm bound `‖W ψ‖ ≤ C ‖ψ‖` underlying
  boundedness of `W`.
* `coulomb_hVW` — the Weyl on-ramp identity `Bχ − Aχ = W(Aχ − i·χ)` for `A = −½Δ`, `B = H`.
* `hydrogen_essSpectrum_of_compact` / `hydrogen_essSpectrum_eq_Ici_of_compact` — given `W` compact,
  the hydrogen Hamiltonian shares the essential spectrum of `−½Δ`, namely `[0, ∞)`.
* `truncCoulombBall_memLp` / `truncKernelG_memLp` — the ball-truncated potential and the truncated
  free-resolvent kernel lie in `L²`, the kernel data feeding the compactness proof of `W`.
-/

open MeasureTheory Complex Filter InnerProductSpace Metric Set
open Spectra.Sobolev Spectra.CompactOperator
open Spectra.QuantumMechanics.SpectralTheory Spectra.Operator Spectra.Essential
open scoped Topology

noncomputable section

namespace Spectra.QuantumMechanics.Hydrogen

/-! ## The compact perturbation `W = V · R_z` (general spectral parameter `z`) -/

/-- The resolvent `R_z = (−Δ − z)⁻¹` of the free Laplacian at an arbitrary non-real `z`. -/
def freeResolventAt (z : ℂ) (hz : z.im ≠ 0) : l2R3 →L[ℂ] l2R3 :=
  selfAdjointResolvent laplacian_isSelfAdjoint z hz

/-- `R_z ψ` lands in the Laplacian domain. -/
lemma freeResolventAt_mem_domain (z : ℂ) (hz : z.im ≠ 0) (ψ : l2R3) :
    (freeResolventAt z hz ψ) ∈ laplacianPMap.domain :=
  selfAdjointResolvent_mem_domain laplacian_isSelfAdjoint z hz ψ

/-- The corestriction `ψ ↦ ⟨R_z ψ, mem⟩` as a linear map into the domain. -/
def freeResolventCodAt (z : ℂ) (hz : z.im ≠ 0) :
    l2R3 →ₗ[ℂ] laplacianPMap.domain :=
  LinearMap.codRestrict laplacianPMap.domain
    (freeResolventAt z hz : l2R3 →L[ℂ] l2R3).toLinearMap
    (freeResolventAt_mem_domain z hz)

/-- The corestriction `freeResolventCodAt` agrees with `freeResolventAt` after forgetting the
domain membership. -/
@[simp] lemma freeResolventCodAt_coe (z : ℂ) (hz : z.im ≠ 0) (ψ : l2R3) :
    ((freeResolventCodAt z hz ψ : laplacianPMap.domain) : l2R3) = freeResolventAt z hz ψ := rfl

/-- The Coulomb-perturbed resolvent `W = V · R_z`, as a `ℂ`-linear map. -/
def coulombResolventLinearAt (p : CoulombParams) (z : ℂ) (hz : z.im ≠ 0) :
    l2R3 →ₗ[ℂ] l2R3 :=
  (coulombPotential p).comp (freeResolventCodAt z hz)

/-- The constant `b` from the relative bound at slope `a = 1`. -/
def coulombB (p : CoulombParams) : ℝ :=
  (coulomb_relative_bound_is_zero p 1 (by norm_num)).choose

/-- The relative-bound constant `coulombB` is non-negative. -/
lemma coulombB_nonneg (p : CoulombParams) : 0 ≤ coulombB p :=
  (coulomb_relative_bound_is_zero p 1 (by norm_num)).choose_spec.1

/-- The Coulomb relative bound at slope `a = 1`:
`‖V ψ‖ ≤ ‖−Δ ψ‖ + coulombB p · ‖ψ‖` for `ψ` in the Laplacian domain. -/
lemma coulombB_bound (p : CoulombParams) (ψ : laplacianPMap.domain) :
    ‖coulombPotential p ψ‖ ≤ 1 * ‖laplacianPMap ψ‖ + coulombB p * ‖(ψ : l2R3)‖ :=
  (coulomb_relative_bound_is_zero p 1 (by norm_num)).choose_spec.2 ψ

/-- The operator-norm bound constant for `W = V · R_z`. -/
def coulombResolventCAt (p : CoulombParams) (z : ℂ) (hz : z.im ≠ 0) : ℝ :=
  1 + (1 + coulombB p) * (1 + ‖z‖) * ‖freeResolventAt z hz‖

/-- The norm bound `‖W ψ‖ ≤ C ‖ψ‖`. -/
lemma coulombResolventLinearAt_bound (p : CoulombParams) (z : ℂ) (hz : z.im ≠ 0) (ψ : l2R3) :
    ‖coulombResolventLinearAt p z hz ψ‖ ≤ coulombResolventCAt p z hz * ‖ψ‖ := by
  set χ : laplacianPMap.domain := freeResolventCodAt z hz ψ with _hχdef
  have hχval : (χ : l2R3) = freeResolventAt z hz ψ := rfl
  have hWval : coulombResolventLinearAt p z hz ψ = coulombPotential p χ := rfl
  rw [hWval]
  have hrel : ‖coulombPotential p χ‖ ≤ 1 * ‖laplacianPMap χ‖ + coulombB p * ‖(χ : l2R3)‖ :=
    coulombB_bound p χ
  have hsolve :
      laplacianPMap ⟨freeResolventAt z hz ψ, freeResolventAt_mem_domain z hz ψ⟩
        - z • (freeResolventAt z hz ψ) = ψ :=
    selfAdjointResolvent_solves laplacian_isSelfAdjoint z hz ψ
  have hlapeq : laplacianPMap χ
      = laplacianPMap ⟨freeResolventAt z hz ψ, freeResolventAt_mem_domain z hz ψ⟩ := rfl
  have hlap : laplacianPMap χ = ψ + z • (χ : l2R3) := by
    have h2 : laplacianPMap ⟨freeResolventAt z hz ψ, freeResolventAt_mem_domain z hz ψ⟩
        = ψ + z • (freeResolventAt z hz ψ) := eq_add_of_sub_eq hsolve
    rw [hlapeq, h2, hχval]
  have hlapnorm : ‖laplacianPMap χ‖ ≤ ‖ψ‖ + ‖z‖ * ‖(χ : l2R3)‖ := by
    rw [hlap]
    calc ‖ψ + z • (χ : l2R3)‖
        ≤ ‖ψ‖ + ‖z • (χ : l2R3)‖ := norm_add_le _ _
      _ = ‖ψ‖ + ‖z‖ * ‖(χ : l2R3)‖ := by rw [norm_smul]
  have hRnorm : ‖(χ : l2R3)‖ ≤ ‖freeResolventAt z hz‖ * ‖ψ‖ := by
    rw [hχval]; exact (freeResolventAt z hz : l2R3 →L[ℂ] l2R3).le_opNorm ψ
  have hb0 : 0 ≤ coulombB p := coulombB_nonneg p
  have _hnormψ : (0:ℝ) ≤ ‖ψ‖ := norm_nonneg _
  have hznn : (0:ℝ) ≤ ‖z‖ := norm_nonneg _
  have hχnn : (0:ℝ) ≤ ‖(χ : l2R3)‖ := norm_nonneg _
  have _h1c : (0:ℝ) ≤ (1 + coulombB p) * (1 + ‖z‖) := by positivity
  calc ‖coulombPotential p χ‖
      ≤ 1 * ‖laplacianPMap χ‖ + coulombB p * ‖(χ : l2R3)‖ := hrel
    _ ≤ 1 * (‖ψ‖ + ‖z‖ * ‖(χ : l2R3)‖) + coulombB p * ‖(χ : l2R3)‖ := by gcongr
    _ ≤ ‖ψ‖ + (1 + coulombB p) * (1 + ‖z‖) * ‖(χ : l2R3)‖ := by
        nlinarith [hχnn, hznn, hb0, mul_nonneg (mul_nonneg hb0 hznn) hχnn]
    _ ≤ ‖ψ‖ + (1 + coulombB p) * (1 + ‖z‖) * (‖freeResolventAt z hz‖ * ‖ψ‖) := by
        gcongr
    _ = coulombResolventCAt p z hz * ‖ψ‖ := by rw [coulombResolventCAt]; ring

/-- The Coulomb-perturbed resolvent `W = V · R_z : L²(ℝ³) →L[ℂ] L²(ℝ³)`. -/
def coulombResolventAt (p : CoulombParams) (z : ℂ) (hz : z.im ≠ 0) : l2R3 →L[ℂ] l2R3 :=
  LinearMap.mkContinuous (coulombResolventLinearAt p z hz) (coulombResolventCAt p z hz)
    (coulombResolventLinearAt_bound p z hz)

/-- `W ψ = V · (R_z ψ)`: the perturbed resolvent applied to `ψ` is the Coulomb potential on the
corestricted free resolvent. -/
lemma coulombResolventAt_apply (p : CoulombParams) (z : ℂ) (hz : z.im ≠ 0) (ψ : l2R3) :
    coulombResolventAt p z hz ψ = coulombPotential p (freeResolventCodAt z hz ψ) := rfl

/-! ## The `z = i` instance (drives the `−Δ` essential-spectrum proof) -/

/-- The resolvent `R_i = (−Δ − i)⁻¹` of the free Laplacian at `z = i`. -/
def freeResolvent : l2R3 →L[ℂ] l2R3 :=
  freeResolventAt Complex.I I_im_ne_zero

/-- `R_i ψ` lands in the Laplacian domain. -/
lemma freeResolvent_mem_domain (ψ : l2R3) :
    (freeResolvent ψ) ∈ laplacianPMap.domain :=
  freeResolventAt_mem_domain Complex.I I_im_ne_zero ψ

/-- The corestriction `ψ ↦ ⟨R_i ψ, mem⟩` as a linear map into the domain. -/
def freeResolventCod :
    l2R3 →ₗ[ℂ] laplacianPMap.domain :=
  freeResolventCodAt Complex.I I_im_ne_zero

/-- The corestriction `freeResolventCod` agrees with `freeResolvent` after forgetting the domain
membership. -/
@[simp] lemma freeResolventCod_coe (ψ : l2R3) :
    ((freeResolventCod ψ : laplacianPMap.domain) : l2R3) = freeResolvent ψ := rfl

/-- The Coulomb-perturbed resolvent `W = V · R_i : L²(ℝ³) →L[ℂ] L²(ℝ³)`. -/
def coulombResolvent (p : CoulombParams) : l2R3 →L[ℂ] l2R3 :=
  coulombResolventAt p Complex.I I_im_ne_zero

/-- `W ψ = V · (R_i ψ)` at the spectral parameter `z = i`. -/
lemma coulombResolvent_apply (p : CoulombParams) (ψ : l2R3) :
    coulombResolvent p ψ = coulombPotential p (freeResolventCod ψ) :=
  coulombResolventAt_apply p Complex.I I_im_ne_zero ψ

/-! ## The `z = 2i` instance (drives the `−½Δ` essential-spectrum proof) -/

/-- `2i` is off the real axis: the spectral parameter for the `−½Δ` reduction. -/
lemma h2I : (2 * Complex.I).im ≠ 0 := by
  simp [Complex.mul_im, Complex.I_im, Complex.I_re]

/-- The compact perturbation for the textbook hydrogen Hamiltonian: `W = V·(−½Δ − i)⁻¹`,
realised as `2 • (V·(−Δ − 2i)⁻¹)` via `(−½Δ − i)⁻¹ = 2·(−Δ − 2i)⁻¹`. -/
def coulombResolventHalf (p : CoulombParams) : l2R3 →L[ℂ] l2R3 :=
  (2 : ℂ) • coulombResolventAt p (2 * Complex.I) h2I

/-- **The Weyl on-ramp hypothesis `hVW` for `−½Δ`.**

The reduction `A = −½Δ`, `B = H` gives `Bχ − Aχ = V·χ`, exhibited here as
`W(Aχ − i·χ)` with `W = coulombResolventHalf`.  Algebra: `½Δχ − iχ = ½(Δχ − 2iχ)`,
the free resolvent at `2i` is linear and a left inverse on `Dom(−Δ)`, so
`R_{2i}(½Δχ − iχ) = ½χ`, and `2 • V(½χ) = V(χ)`. -/
lemma coulomb_hVW (p : CoulombParams) (χ : l2R3) (hχ : χ ∈ halfLaplacianPMap.domain) :
    (hydrogenHamiltonian p) ⟨χ, hχ⟩ - halfLaplacianPMap ⟨χ, hχ⟩
      = coulombResolventHalf p (halfLaplacianPMap ⟨χ, hχ⟩ - Complex.I • χ) := by
  -- `Dom(−½Δ) = Dom(−Δ)` definitionally.
  have hχ' : χ ∈ laplacianPMap.domain := hχ
  -- LHS = V·χ.
  have hLHS : (hydrogenHamiltonian p) ⟨χ, hχ⟩ - halfLaplacianPMap ⟨χ, hχ⟩
      = coulombPotential p ⟨χ, hχ⟩ := by
    rw [hydrogenHamiltonian_apply p ⟨χ, hχ⟩]
    exact add_sub_cancel_left _ _
  rw [hLHS]
  -- The input to `W`: `½Δχ − iχ = ½ • (Δχ − 2i·χ)`.
  have hψeq : halfLaplacianPMap ⟨χ, hχ⟩ - Complex.I • χ
      = ((1 / 2 : ℝ) : ℂ) • (laplacianPMap ⟨χ, hχ'⟩ - (2 * Complex.I) • χ) := by
    rw [halfLaplacianPMap_apply ⟨χ, hχ⟩, smul_sub, smul_smul]
    congr 2
    push_cast; ring
  -- Unfold `W = 2 • (V·R_{2i})` and apply linearity of `R_{2i}`.
  rw [coulombResolventHalf, ContinuousLinearMap.smul_apply, hψeq,
    map_smul, coulombResolventAt_apply]
  -- `R_{2i}(Δχ − 2i·χ) = χ`, so its corestriction is `⟨χ, _⟩`.
  have hinv : freeResolventCodAt (2 * Complex.I) h2I
      (laplacianPMap ⟨χ, hχ'⟩ - (2 * Complex.I) • χ)
        = (⟨χ, hχ'⟩ : laplacianPMap.domain) := by
    apply Subtype.ext
    rw [freeResolventCodAt_coe]
    exact selfAdjointResolvent_left_inverse laplacian_isSelfAdjoint (2 * Complex.I) h2I ⟨χ, hχ'⟩
  -- `R_{2i}(½Δχ − iχ) = ½χ` reduces `V` to `V⟨χ,_⟩`; then `2 • ½ • Vχ = Vχ`.
  rw [hinv]
  have hpot : (coulombPotential p) (⟨χ, hχ'⟩ : laplacianPMap.domain)
      = (coulombPotential p) ⟨χ, hχ⟩ := rfl
  rw [hpot, smul_smul]
  norm_num

/-- **Reduction.**  If the Coulomb-perturbed resolvent `W = coulombResolventHalf` is compact, then
the hydrogen Hamiltonian and the textbook kinetic operator `−½Δ` have the same essential
spectrum. -/
lemma hydrogen_essSpectrum_of_compact (p : CoulombParams)
    (hW : IsCompactOperator (⇑(coulombResolventHalf p))) :
    Spectra.Essential.essSpectrum (hydrogen_isSelfAdjoint p)
      = Spectra.Essential.essSpectrum halfLaplacian_isSelfAdjoint :=
  (essSpectrum_eq_of_isCompactOperator_perturb halfLaplacian_isSelfAdjoint
    (hydrogen_isSelfAdjoint p) (perturbedOp_domain _ _).symm
    (coulombResolventHalf p) hW (coulomb_hVW p)).symm

/-- The same, with the RHS rewritten to `[0, ∞)`. -/
lemma hydrogen_essSpectrum_eq_Ici_of_compact (p : CoulombParams)
    (hW : IsCompactOperator (⇑(coulombResolventHalf p))) :
    Spectra.Essential.essSpectrum (hydrogen_isSelfAdjoint p) = Set.Ici (0 : ℝ) :=
  (hydrogen_essSpectrum_of_compact p hW).trans essSpectrum_halfLaplacian

/-! ## Kernel data for the compactness of `W` -/

/-- Ball-truncated Coulomb potential: `−Z/|x|` cut off to `closedBall 0 (n+1)` (keeps the
`L²`-integrable singularity at `0`, truncates only the `L^∞`-small tail at infinity). -/
def truncCoulombBall (p : CoulombParams) (n : ℕ) : R3 → ℂ :=
  (closedBall (0 : R3) (n + 1 : ℝ)).indicator (fun x => ((coulombMultiplier p x : ℝ) : ℂ))

/-- The ball-truncated Coulomb potential is `L²`: keeping the integrable `1/|x|` singularity and
cutting the tail leaves `truncCoulombBall p n` in `L²(ℝ³)`. -/
lemma truncCoulombBall_memLp (p : CoulombParams) (n : ℕ) :
    MemLp (truncCoulombBall p n) 2 volume := by
  rw [truncCoulombBall, memLp_indicator_iff_restrict measurableSet_closedBall]
  have haesm : AEStronglyMeasurable (fun x => ((coulombMultiplier p x : ℝ) : ℂ))
      (volume.restrict (closedBall (0:R3) (n+1))) :=
    ((Complex.measurable_ofReal.comp
      (coulombMultiplier_measurable p)).aestronglyMeasurable).restrict
  refine (memLp_two_iff_integrable_sq_norm haesm).mpr ?_
  have hball : IntegrableOn (fun x => p.Z ^ 2 * inverseRSq x) (ball (0:R3) (n + 2)) volume :=
    (inverseRSq_integrableOn_ball (n + 2)).const_mul (p.Z ^ 2)
  have hclosed : Integrable (fun x => p.Z ^ 2 * inverseRSq x)
      (volume.restrict (closedBall (0:R3) (n + 1))) :=
    hball.mono_set (closedBall_subset_ball (by linarith))
  refine hclosed.congr ?_
  filter_upwards with x
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, coulombMultiplier_sq]

/-- The truncated free-resolvent kernel `Kₙ(x,y) = Vⁿ(x)·G̃_z(x−y)` lies in `L²(ℝ³×ℝ³)`. -/
lemma truncKernelG_memLp (p : CoulombParams) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    MemLp (fun q : R3 × R3 =>
        truncCoulombBall p n q.1 * (freeGreensFunctionL2 z hz : R3 → ℂ) (q.1 - q.2)) 2
      ((volume : Measure R3).prod (volume : Measure R3)) :=
  memLp_kernel_mul_sub (truncCoulombBall_memLp p n) (Lp.memLp (freeGreensFunctionL2 z hz))

end Spectra.QuantumMechanics.Hydrogen
