/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Spectrum.Continuous.Defs
import Spectra.QuantumMechanics.Hydrogen.Laplacian.FreeGreens.Convolution
import Spectra.SpectralTheory.IntegralOperatorCompact

/-!
# Compactness of the Coulomb resolvent perturbation, and `σ_ess(H) = [0, ∞)`

This file proves that the Coulomb-potential perturbation of the free resolvent is a compact
operator on `L²(ℝ³)`, and concludes that the textbook hydrogen Hamiltonian
`H = −½Δ − Z/r` has essential spectrum `[0, ∞)`.

## Main definitions

* `multIndicatorBall n` — multiplication by `𝟙_{closedBall 0 (n+1)}` as a continuous linear map
  on `L²(ℝ³)`; the tool used to truncate the Coulomb kernel to a bounded region.
* `truncKernelGLpAt p n z hz` — the Coulomb-Green's-function kernel
  `Kₙ(x, y) = 𝟙_{closedBall 0 (n+1)}(x) · V(x) · G_z(x - y)` truncated to the ball of radius
  `n + 1`, viewed as an element of `L²(ℝ³ × ℝ³)`.

## Main statements

* `coulombResolventAt_isCompact` — the Coulomb resolvent `coulombResolventAt p z hz` is a compact
  operator on `L²(ℝ³)`, for every spectral parameter `z` off the real axis.
* `coulombResolvent_isCompact` / `coulombResolventHalf_isCompact` — the `z = i` and textbook
  (`z = 2i`, rescaled) instances used downstream.
* `hydrogen_essSpectrum` — the essential spectrum of the self-adjoint hydrogen Hamiltonian is
  `Set.Ici 0`, i.e. `[0, ∞)`.

## Implementation notes

Compactness is proved by the classical kernel-truncation argument: the integral operator with
kernel `Kₙ ∈ L²(ℝ³ × ℝ³)` is compact for every `n` (Hilbert–Schmidt), and the truncated
kernels converge to the Coulomb resolvent in operator norm as `n → ∞`, since the tail of the
Coulomb multiplier `Z/‖x‖` outside `closedBall 0 (n+1)` is bounded by `Z/(n+1) → 0`. A limit
of compact operators in operator norm is compact, which finishes the argument. The proof runs in
five stages, each isolated as its own section below:

1. **Kernel truncation as a bounded operator** (`multIndicatorBall`): package
   "multiply by `𝟙_{closedBall 0 (n+1)}`" as a CLM of operator norm `≤ 1`.
2. **Coulomb resolvent as a multiplier** (`coulombResolventAt_coeFn`): identify the Coulomb
   resolvent pointwise a.e. as multiplication by `coulombMultiplier` composed with the free
   resolvent.
3. **Schwartz-level kernel agreement** (`step_B_at`): on Schwartz test functions, the truncated
   integral operator agrees a.e. with `multIndicatorBall n ∘ coulombResolventAt`.
4. **Density to the full operator identity** (`step_C_at`): extend the Schwartz-level agreement to
   all of `L²(ℝ³)` by density of Schwartz functions.
5. **Operator-norm tail bound and the limit** (`step_D_at`, `step_E_tendsto_at`): bound
   `‖coulombResolventAt − integralOperator Kₙ‖ ≤ (Z/(n+1)) · ‖freeResolventAt‖ → 0`,
   then invoke `isCompactOperator_of_tendsto`.

## References

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics, Vol. IV: Analysis of Operators*,
  Theorem XIII.16 and surrounding discussion — compactness of Coulomb-type perturbations via
  kernel truncation, and `σ_ess(−Δ + V) = σ_ess(−Δ)` for relatively compact `V`.
-/
open MeasureTheory Complex Filter InnerProductSpace Metric Set
open Spectra.Sobolev Spectra.CompactOperator
open Spectra.QuantumMechanics.SpectralTheory Spectra.Essential
open FourierTransform SchwartzMap
open scoped Convolution Topology NNReal ENNReal

namespace Spectra.QuantumMechanics.Hydrogen
/-! ## Kernel truncation as a bounded operator -/

/-- The underlying linear map `f ↦ (𝟙_{closedBall 0 (n+1)} · f).toLp`. -/
noncomputable def multIndicatorBallLM (n : ℕ) : l2R3 →ₗ[ℂ] l2R3 where
  toFun f := (MemLp.indicator (s := closedBall (0 : R3) (n + 1 : ℝ))
      (f := (f : R3 → ℂ)) (μ := (volume : Measure R3)) (p := 2)
      measurableSet_closedBall (Lp.memLp f)).toLp
      ((closedBall (0 : R3) (n + 1 : ℝ)).indicator (f : R3 → ℂ))
  map_add' f g := by
    rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
    filter_upwards [Lp.coeFn_add f g] with x hx
    simp only [Pi.add_apply]
    by_cases h : x ∈ closedBall (0 : R3) (n + 1 : ℝ)
    · simp only [Set.indicator_of_mem h, Pi.add_apply, hx]
    · simp only [Set.indicator_of_notMem h, add_zero]
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
    filter_upwards [Lp.coeFn_smul c f] with x hx
    simp only [Pi.smul_apply]
    by_cases h : x ∈ closedBall (0 : R3) (n + 1 : ℝ)
    · simp only [Set.indicator_of_mem h, Pi.smul_apply, hx]
    · simp only [Set.indicator_of_notMem h, smul_zero]

/-- The coeFn of the underlying map. -/
lemma multIndicatorBallLM_coeFn (n : ℕ) (f : l2R3) :
    (multIndicatorBallLM n f : R3 → ℂ) =ᵐ[volume]
      (closedBall (0 : R3) (n + 1 : ℝ)).indicator (f : R3 → ℂ) :=
  MemLp.coeFn_toLp (MemLp.indicator (s := closedBall (0 : R3) (n + 1 : ℝ))
    (f := (f : R3 → ℂ)) (μ := (volume : Measure R3)) (p := 2)
    measurableSet_closedBall (Lp.memLp f))

/-- Boundedness: `‖𝟙·f‖₂ ≤ 1 · ‖f‖₂`. -/
lemma multIndicatorBallLM_bound (n : ℕ) (f : l2R3) :
    ‖multIndicatorBallLM n f‖ ≤ 1 * ‖f‖ := by
  rw [one_mul, Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
  calc eLpNorm (multIndicatorBallLM n f : R3 → ℂ) 2 volume
      = eLpNorm ((closedBall (0 : R3) (n + 1 : ℝ)).indicator (f : R3 → ℂ)) 2 volume :=
        eLpNorm_congr_ae (multIndicatorBallLM_coeFn n f)
    _ ≤ eLpNorm (f : R3 → ℂ) 2 volume := by
        apply eLpNorm_mono
        intro x
        exact norm_indicator_le_norm_self _ _

/-- Multiplication by `𝟙_{closedBall 0 (n+1)}` as a CLM on `L²`. -/
noncomputable def multIndicatorBall (n : ℕ) : l2R3 →L[ℂ] l2R3 :=
  LinearMap.mkContinuous (multIndicatorBallLM n) 1 (multIndicatorBallLM_bound n)

/-- The coeFn of `multIndicatorBall n f` is a.e. `𝟙_{closedBall 0 (n+1)} · f`. -/
lemma multIndicatorBall_coeFn (n : ℕ) (f : l2R3) :
    (multIndicatorBall n f : R3 → ℂ) =ᵐ[volume]
      (closedBall (0 : R3) (n + 1 : ℝ)).indicator (f : R3 → ℂ) :=
  multIndicatorBallLM_coeFn n f

/-! ## Coulomb resolvent as a multiplier -/

/-- The Coulomb resolvent acts a.e. as multiplication by `coulombMultiplier` on `R_z ψ`. -/
lemma coulombResolventAt_coeFn (p : CoulombParams) (z : ℂ) (hz : z.im ≠ 0) (ψ : l2R3) :
    (coulombResolventAt p z hz ψ : R3 → ℂ) =ᵐ[volume]
      fun x => (coulombMultiplier p x : ℂ) * (freeResolventAt z hz ψ : R3 → ℂ) x := by
  rw [coulombResolventAt_apply]
  -- `freeResolventCodAt z hz ψ = ⟨freeResolventAt z hz ψ, _⟩`
  have hcod : (freeResolventCodAt z hz ψ : SobolevH2 (d := 3))
      = ⟨freeResolventAt z hz ψ, freeResolventAt_mem_domain z hz ψ⟩ := rfl
  rw [hcod]
  -- unfold coulombPotential on the explicit pair
  exact MemLp.coeFn_toLp
    (coulomb_mul_memLp_H2 p (freeResolventAt z hz ψ) (freeResolventAt_mem_domain z hz ψ))

/-! ## Schwartz-level kernel agreement -/

/-- The truncated kernel `Kₙ ∈ L²(ℝ³×ℝ³)` at spectral parameter `z`. -/
noncomputable def truncKernelGLpAt (p : CoulombParams) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    Lp ℂ 2 ((volume : Measure R3).prod (volume : Measure R3)) :=
  (truncKernelG_memLp p n z hz).toLp _

/-- On Schwartz inputs, the integral operator `integralOperator Kₙ` agrees with
`multIndicatorBall n ∘ coulombResolventAt p z hz`. -/
lemma step_B_at (p : CoulombParams) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) (ψ : 𝓢(R3, ℂ)) :
    (integralOperator (truncKernelGLpAt p n z hz) (ψ.toLp 2 volume) : R3 → ℂ) =ᵐ[volume]
      ⇑(multIndicatorBall n (coulombResolventAt p z hz (ψ.toLp 2 volume))) := by
  -- ψ.toLp 2 volume =ᵐ ψ
  have hψae : (ψ.toLp 2 volume : R3 → ℂ) =ᵐ[volume] (ψ : R3 → ℂ) :=
    SchwartzMap.coeFn_toLp ψ 2 volume
  -- LHS: kernel integral
  have hLHS : (integralOperator (truncKernelGLpAt p n z hz) (ψ.toLp 2 volume) : R3 → ℂ) =ᵐ[volume]
      fun x => ∫ y, (truncKernelGLpAt p n z hz : R3 × R3 → ℂ) (x, y) *
        (ψ.toLp 2 volume : R3 → ℂ) y :=
    integralOperator_coeFn (K := truncKernelGLpAt p n z hz) (ψ.toLp 2 volume)
  -- Kₙ representative: truncCoulombBall x * G̃_z(x-y)
  have hKae : (truncKernelGLpAt p n z hz : R3 × R3 → ℂ)
      =ᵐ[(volume : Measure R3).prod (volume : Measure R3)]
      fun q : R3 × R3 => truncCoulombBall p n q.1 *
        (freeGreensFunctionL2 z hz : R3 → ℂ) (q.1 - q.2) :=
    MemLp.coeFn_toLp _
  -- for a.e. x, the inner integrands agree a.e. in y
  have hKae2 : ∀ᵐ x ∂(volume : Measure R3),
      (fun y => (truncKernelGLpAt p n z hz : R3 × R3 → ℂ) (x, y))
      =ᵐ[volume] fun y => truncCoulombBall p n x *
        (freeGreensFunctionL2 z hz : R3 → ℂ) (x - y) :=
    Measure.ae_ae_of_ae_prod hKae
  -- S3: ∫ y, G̃_z(x-y) ψ y = (freeResolventAt z hz ψ) x  a.e. x
  have hS3 : ∀ᵐ x ∂(volume : Measure R3),
      (freeResolventAt z hz (ψ.toLp 2 volume) : R3 → ℂ) x
        = ∫ y, (freeGreensFunctionL2 z hz : R3 → ℂ) (x - y) * (ψ : R3 → ℂ) y :=
    freeGreens_resolvent_kernel_schwartz z hz ψ
  -- W coeFn at the Schwartz input
  have hW := coulombResolventAt_coeFn p z hz (ψ.toLp 2 volume)
  -- multIndicatorBall coeFn
  have hM := multIndicatorBall_coeFn n (coulombResolventAt p z hz (ψ.toLp 2 volume))
  filter_upwards [hLHS, hKae2, hS3, hW, hM, hψae] with x hLHSx hKae2x hS3x hWx hMx _hψaex
  -- compute LHS at x
  rw [hLHSx]
  -- inner integral with Kₙ rep, and ψ.toLp = ψ
  have hint1 : ∫ y, (truncKernelGLpAt p n z hz : R3 × R3 → ℂ) (x, y) * (ψ.toLp 2 volume : R3 → ℂ) y
      = ∫ y, truncCoulombBall p n x *
          ((freeGreensFunctionL2 z hz : R3 → ℂ) (x - y) * (ψ : R3 → ℂ) y) := by
    apply integral_congr_ae
    filter_upwards [hKae2x, hψae] with y hy hψy
    rw [hy, hψy]; ring
  rw [hint1, integral_const_mul]
  -- substitute S3
  rw [← hS3x]
  -- now LHS = truncCoulombBall p n x * (freeResolventAt z hz (ψ.toLp 2 volume)) x
  -- RHS via hMx, hWx
  rw [hMx]
  by_cases hball : x ∈ closedBall (0 : R3) (n + 1 : ℝ)
  · rw [Set.indicator_of_mem hball, hWx]
    -- truncCoulombBall p n x = coulombMultiplier on the ball
    rw [truncCoulombBall, Set.indicator_of_mem hball]
  · rw [Set.indicator_of_notMem hball]
    rw [truncCoulombBall, Set.indicator_of_notMem hball, zero_mul]

/-! ## Density to the full operator identity -/

/-- `integralOperator Kₙ = (multIndicatorBall n) ∘ (coulombResolventAt p z hz)` as CLMs. -/
lemma step_C_at (p : CoulombParams) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    integralOperator (truncKernelGLpAt p n z hz)
      = (multIndicatorBall n).comp (coulombResolventAt p z hz) := by
  -- dense range of Schwartz → L²
  have hdr : DenseRange (SchwartzMap.toLpCLM ℂ ℂ (2 : ℝ≥0∞) (volume : Measure R3)) :=
    SchwartzMap.denseRange_toLpCLM (by norm_num)
  -- density of the span of the range
  have hdense : Dense (Submodule.span ℂ
      (Set.range (SchwartzMap.toLpCLM ℂ ℂ (2 : ℝ≥0∞) (volume : Measure R3))) : Set l2R3) :=
    Dense.mono Submodule.subset_span hdr
  refine ContinuousLinearMap.ext_on hdense ?_
  rintro _ ⟨φ, rfl⟩
  -- on `φ.toLp 2 volume`, both sides agree via the Schwartz-level kernel agreement
  apply Lp.ext
  have hB := step_B_at p n z hz φ
  -- toLpCLM φ = φ.toLp 2 volume
  simpa only [SchwartzMap.toLpCLM_apply, ContinuousLinearMap.comp_apply] using hB

/-! ## Operator-norm tail bound -/

/-- Pointwise: on the complement of `closedBall 0 (n+1)`, `|coulombMultiplier x| ≤ Z/(n+1)`. -/
lemma coulombMultiplier_le_on_compl (p : CoulombParams) (n : ℕ) {x : R3}
    (hx : x ∉ closedBall (0 : R3) (n + 1 : ℝ)) :
    ‖(coulombMultiplier p x : ℂ)‖ ≤ p.Z / (n + 1) := by
  rw [Complex.norm_real, Real.norm_eq_abs, coulombMultiplier_abs]
  -- x ∉ closedBall ↔ ‖x‖ > n+1, so inverseR x = 1/‖x‖ ≤ 1/(n+1)
  rw [mem_closedBall, dist_zero_right, not_le] at hx
  have hxpos : (0 : ℝ) < ‖x‖ := lt_trans (by positivity) hx
  have hne : ‖x‖ ≠ 0 := ne_of_gt hxpos
  have hnpos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  rw [inverseR, if_neg hne, mul_one_div]
  exact div_le_div_of_nonneg_left (le_of_lt p.hZ) hnpos (le_of_lt hx)

/-- Operator-norm tail bound for the integral-operator approximants. -/
lemma step_D_at (p : CoulombParams) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    ‖coulombResolventAt p z hz - integralOperator (truncKernelGLpAt p n z hz)‖
      ≤ p.Z / (n + 1) * ‖freeResolventAt z hz‖ := by
  have hZnn : (0 : ℝ) ≤ p.Z / (n + 1) :=
    div_nonneg (le_of_lt p.hZ) (by positivity)
  have hbound : (0 : ℝ) ≤ p.Z / (n + 1) * ‖freeResolventAt z hz‖ :=
    mul_nonneg hZnn (norm_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _ hbound (fun ψ => ?_)
  -- (W - intK) ψ coeFn analysis
  have hCdiff : (coulombResolventAt p z hz - integralOperator (truncKernelGLpAt p n z hz)) ψ
      = coulombResolventAt p z hz ψ - multIndicatorBall n (coulombResolventAt p z hz ψ) := by
    rw [ContinuousLinearMap.sub_apply, step_C_at p n z hz, ContinuousLinearMap.comp_apply]
  -- pointwise: ‖((W-intK)ψ) x‖ ≤ (Z/(n+1)) ‖(freeResolventAt z hz ψ) x‖  a.e.
  have hWcoe := coulombResolventAt_coeFn p z hz ψ
  have hMcoe := multIndicatorBall_coeFn n (coulombResolventAt p z hz ψ)
  -- eLpNorm bound
  have hpt : (((coulombResolventAt p z hz -
        integralOperator (truncKernelGLpAt p n z hz)) ψ) : R3 → ℂ)
      =ᵐ[volume] fun x => (closedBall (0 : R3) (n + 1 : ℝ))ᶜ.indicator
        (fun y => (coulombMultiplier p y : ℂ) * (freeResolventAt z hz ψ : R3 → ℂ) y) x := by
    rw [hCdiff]
    filter_upwards [Lp.coeFn_sub (coulombResolventAt p z hz ψ)
        (multIndicatorBall n (coulombResolventAt p z hz ψ)),
      hWcoe, hMcoe] with x hsub hWx hMx
    rw [hsub, Pi.sub_apply, hMx]
    by_cases hball : x ∈ closedBall (0 : R3) (n + 1 : ℝ)
    · rw [Set.indicator_of_mem hball, hWx, Set.indicator_of_notMem (by simpa using hball), sub_self]
    · rw [Set.indicator_of_notMem hball, hWx, Set.indicator_of_mem (by simpa using hball), sub_zero]
  -- now bound norms
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hpt]
  -- pointwise ‖𝟙ᶜ · cm · R‖ ≤ (Z/(n+1)) ‖R‖
  have hmono : eLpNorm (fun x => (closedBall (0 : R3) (n + 1 : ℝ))ᶜ.indicator
        (fun y => (coulombMultiplier p y : ℂ) * (freeResolventAt z hz ψ : R3 → ℂ) y) x) 2 volume
      ≤ eLpNorm ((p.Z / (n + 1) : ℝ) • (freeResolventAt z hz ψ : R3 → ℂ)) 2 volume := by
    apply eLpNorm_mono
    intro x
    by_cases hball : x ∈ closedBall (0 : R3) (n + 1 : ℝ)
    · rw [Set.indicator_of_notMem (by simpa using hball)]
      simp only [norm_zero]
      exact norm_nonneg _
    · rw [Set.indicator_of_mem (by simpa using hball), norm_mul, Pi.smul_apply, norm_smul]
      simp only [Real.norm_eq_abs, abs_of_nonneg hZnn]
      exact mul_le_mul_of_nonneg_right (coulombMultiplier_le_on_compl p n hball) (norm_nonneg _)
  calc (eLpNorm (fun x => (closedBall (0 : R3) (n + 1 : ℝ))ᶜ.indicator
          (fun y => (coulombMultiplier p y : ℂ) * (freeResolventAt z hz ψ : R3 → ℂ) y) x)
          2 volume).toReal
      ≤ (eLpNorm ((p.Z / (n + 1) : ℝ) • (freeResolventAt z hz ψ : R3 → ℂ)) 2 volume).toReal :=
        ENNReal.toReal_mono (by
          rw [eLpNorm_const_smul]
          exact ENNReal.mul_ne_top (by finiteness) (Lp.eLpNorm_ne_top _)) hmono
    _ = p.Z / (n + 1) * (eLpNorm (freeResolventAt z hz ψ : R3 → ℂ) 2 volume).toReal := by
        rw [eLpNorm_const_smul, ENNReal.toReal_mul]
        congr 1
        simp only [enorm_eq_nnnorm, Real.nnnorm_of_nonneg hZnn, ENNReal.coe_toReal,
          NNReal.coe_mk]
    _ = p.Z / (n + 1) * ‖freeResolventAt z hz ψ‖ := by rw [← Lp.norm_def]
    _ ≤ p.Z / (n + 1) * (‖freeResolventAt z hz‖ * ‖ψ‖) :=
        mul_le_mul_of_nonneg_left ((freeResolventAt z hz).le_opNorm ψ) hZnn
    _ = p.Z / (n + 1) * ‖freeResolventAt z hz‖ * ‖ψ‖ := by ring

/-! ## Limit and compactness -/

/-- The integral-operator approximants converge to `coulombResolventAt p z hz` in operator norm. -/
lemma step_E_tendsto_at (p : CoulombParams) (z : ℂ) (hz : z.im ≠ 0) :
    Tendsto (fun n => integralOperator (truncKernelGLpAt p n z hz)) atTop
      (𝓝 (coulombResolventAt p z hz)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero
    (f := fun n => ‖integralOperator (truncKernelGLpAt p n z hz) - coulombResolventAt p z hz‖)
    (g := fun n => p.Z / (n + 1) * ‖freeResolventAt z hz‖)
    (fun n => norm_nonneg _) (fun n => ?_) ?_
  · rw [norm_sub_rev]
    exact step_D_at p n z hz
  · -- (Z/(n+1))·‖R‖ → 0
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hZdiv : (fun n : ℕ => p.Z / (n + 1)) = fun n : ℕ => p.Z * (1 / (n + 1)) := by
      funext n; rw [mul_one_div]
    have h2 : Tendsto (fun n : ℕ => p.Z / (n + 1) * ‖freeResolventAt z hz‖) atTop
        (𝓝 (p.Z * 0 * ‖freeResolventAt z hz‖)) := by
      apply Tendsto.mul_const
      rw [hZdiv]
      exact h1.const_mul p.Z
    simpa using h2

/-- `coulombResolventAt p z hz` is a compact operator, for any non-real `z`. This is the
kernel-truncation limit argument: `coulombResolventAt` is the operator-norm limit of the compact
integral operators `integralOperator (truncKernelGLpAt p n z hz)`. -/
lemma coulombResolventAt_isCompact (p : CoulombParams) (z : ℂ) (hz : z.im ≠ 0) :
    IsCompactOperator (⇑(coulombResolventAt p z hz)) := by
  apply isCompactOperator_of_tendsto (step_E_tendsto_at p z hz)
  exact Eventually.of_forall
    (fun n => isCompactOperator_integralOperator (truncKernelGLpAt p n z hz))

/-- `coulombResolvent p` is a compact operator (the `z = i` instance). -/
theorem coulombResolvent_isCompact (p : CoulombParams) :
    IsCompactOperator (⇑(coulombResolvent p)) :=
  coulombResolventAt_isCompact p Complex.I I_im_ne_zero

/-- The textbook perturbation `W = coulombResolventHalf` is compact: a scalar multiple of the
compact `coulombResolventAt p (2i)`. -/
theorem coulombResolventHalf_isCompact (p : CoulombParams) :
    IsCompactOperator (⇑(coulombResolventHalf p)) := by
  rw [coulombResolventHalf, ContinuousLinearMap.coe_smul']
  exact (coulombResolventAt_isCompact p (2 * Complex.I) h2I).smul (2 : ℂ)

/-- The textbook hydrogen Hamiltonian `H = −½Δ − Z/r` has essential spectrum `[0, ∞)`. -/
theorem hydrogen_essSpectrum (p : CoulombParams) :
    Spectra.Essential.essSpectrum (hydrogen_isSelfAdjoint p) = Set.Ici (0 : ℝ) :=
  hydrogen_essSpectrum_eq_Ici_of_compact p (coulombResolventHalf_isCompact p)

end Spectra.QuantumMechanics.Hydrogen
