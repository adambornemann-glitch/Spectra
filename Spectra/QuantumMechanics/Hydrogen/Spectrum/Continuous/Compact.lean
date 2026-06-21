/-
Copyright (c) 2026 Spectra Project, Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Spectrum.Continuous.Defs
import Spectra.QuantumMechanics.Hydrogen.Laplacian.FreeGreens.Convolution
import Spectra.SpectralTheory.IntegralOperatorCompact

open MeasureTheory Complex Filter InnerProductSpace Metric Set
open Spectra.Sobolev Spectra.CompactOperator
open Spectra.QuantumMechanics.SpectralTheory Spectra.Essential
open FourierTransform SchwartzMap
open scoped Convolution Topology NNReal ENNReal

namespace Spectra.QuantumMechanics.Hydrogen

/-! ## STEP A — multiplication by the ball indicator as a CLM -/

/-- The underlying linear map `f ↦ (𝟙_{closedBall 0 (n+1)} · f).toLp`. -/
noncomputable def multIndicatorBallLM (n : ℕ) : L2_R3 →ₗ[ℂ] L2_R3 where
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
theorem multIndicatorBallLM_coeFn (n : ℕ) (f : L2_R3) :
    (multIndicatorBallLM n f : R3 → ℂ) =ᵐ[volume]
      (closedBall (0 : R3) (n + 1 : ℝ)).indicator (f : R3 → ℂ) :=
  MemLp.coeFn_toLp (MemLp.indicator (s := closedBall (0 : R3) (n + 1 : ℝ))
    (f := (f : R3 → ℂ)) (μ := (volume : Measure R3)) (p := 2)
    measurableSet_closedBall (Lp.memLp f))

/-- Boundedness: `‖𝟙·f‖₂ ≤ 1 · ‖f‖₂`. -/
theorem multIndicatorBallLM_bound (n : ℕ) (f : L2_R3) :
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

/-- **Step A.** Multiplication by `𝟙_{closedBall 0 (n+1)}` as a CLM on `L²`. -/
noncomputable def multIndicatorBall (n : ℕ) : L2_R3 →L[ℂ] L2_R3 :=
  LinearMap.mkContinuous (multIndicatorBallLM n) 1 (multIndicatorBallLM_bound n)

theorem multIndicatorBall_coeFn (n : ℕ) (f : L2_R3) :
    (multIndicatorBall n f : R3 → ℂ) =ᵐ[volume]
      (closedBall (0 : R3) (n + 1 : ℝ)).indicator (f : R3 → ℂ) :=
  multIndicatorBallLM_coeFn n f

/-! ## W coeFn -/

/-- The Coulomb resolvent acts a.e. as multiplication by `coulombMultiplier` on `R_z ψ`. -/
theorem coulombResolventAt_coeFn (p : CoulombParams) (z : ℂ) (hz : z.im ≠ 0) (ψ : L2_R3) :
    (coulombResolventAt p z hz ψ : R3 → ℂ) =ᵐ[volume]
      fun x => (coulombMultiplier p x : ℂ) * (freeResolventAt z hz ψ : R3 → ℂ) x := by
  rw [coulombResolventAt_apply]
  -- `freeResolventCodAt z hz ψ = ⟨freeResolventAt z hz ψ, _⟩`
  have hcod : (freeResolventCodAt z hz ψ : SobolevH2)
      = ⟨freeResolventAt z hz ψ, freeResolventAt_mem_domain z hz ψ⟩ := rfl
  rw [hcod]
  -- unfold coulombPotential on the explicit pair
  exact MemLp.coeFn_toLp
    (coulomb_mul_memLp_H2 p (freeResolventAt z hz ψ) (freeResolventAt_mem_domain z hz ψ))

/-- The `z = i` instance. -/
theorem coulombResolvent_coeFn (p : CoulombParams) (ψ : L2_R3) :
    (coulombResolvent p ψ : R3 → ℂ) =ᵐ[volume]
      fun x => (coulombMultiplier p x : ℂ) * (freeResolvent ψ : R3 → ℂ) x :=
  coulombResolventAt_coeFn p Complex.I I_im_ne_zero ψ

/-! ## STEP B — Schwartz-level agreement -/

/-- The truncated kernel `Kₙ ∈ L²(ℝ³×ℝ³)` at spectral parameter `z`. -/
noncomputable def truncKernelGLpAt (p : CoulombParams) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    Lp ℂ 2 ((volume : Measure R3).prod (volume : Measure R3)) :=
  (truncKernelG_memLp p n z hz).toLp _

/-- The `z = i` instance. -/
noncomputable def truncKernelGLp (p : CoulombParams) (n : ℕ) :
    Lp ℂ 2 ((volume : Measure R3).prod (volume : Measure R3)) :=
  truncKernelGLpAt p n Complex.I I_im_ne_zero

/-- **Step B.**  On Schwartz inputs, the integral operator `integralOperator Kₙ` agrees with
`multIndicatorBall n ∘ coulombResolventAt p z hz`. -/
theorem step_B_at (p : CoulombParams) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) (ψ : 𝓢(R3, ℂ)) :
    (integralOperator (truncKernelGLpAt p n z hz) (ψ.toLp 2 volume) : R3 → ℂ) =ᵐ[volume]
      ⇑(multIndicatorBall n (coulombResolventAt p z hz (ψ.toLp 2 volume))) := by
  -- ψ.toLp 2 volume =ᵐ ψ
  have hψae : (ψ.toLp 2 volume : R3 → ℂ) =ᵐ[volume] (ψ : R3 → ℂ) :=
    SchwartzMap.coeFn_toLp ψ 2 volume
  -- LHS: kernel integral
  have hLHS : (integralOperator (truncKernelGLpAt p n z hz) (ψ.toLp 2 volume) : R3 → ℂ) =ᵐ[volume]
      fun x => ∫ y, (truncKernelGLpAt p n z hz : R3 × R3 → ℂ) (x, y) * (ψ.toLp 2 volume : R3 → ℂ) y :=
    integralOperator_coeFn (K := truncKernelGLpAt p n z hz) (ψ.toLp 2 volume)
  -- Kₙ representative: truncCoulombBall x * G̃_z(x-y)
  have hKae : (truncKernelGLpAt p n z hz : R3 × R3 → ℂ)
      =ᵐ[(volume : Measure R3).prod (volume : Measure R3)]
      fun q : R3 × R3 => truncCoulombBall p n q.1 *
        (freeGreensFunctionL2 z hz : R3 → ℂ) (q.1 - q.2) :=
    MemLp.coeFn_toLp _
  -- for a.e. x, the inner integrands agree a.e. in y
  have hKae2 : ∀ᵐ x ∂(volume : Measure R3), (fun y => (truncKernelGLpAt p n z hz : R3 × R3 → ℂ) (x, y))
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
  filter_upwards [hLHS, hKae2, hS3, hW, hM, hψae] with x hLHSx hKae2x hS3x hWx hMx hψaex
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

/-- The `z = i` instance. -/
theorem step_B (p : CoulombParams) (n : ℕ) (ψ : 𝓢(R3, ℂ)) :
    (integralOperator (truncKernelGLp p n) (ψ.toLp 2 volume) : R3 → ℂ) =ᵐ[volume]
      ⇑(multIndicatorBall n (coulombResolvent p (ψ.toLp 2 volume))) :=
  step_B_at p n Complex.I I_im_ne_zero ψ

/-! ## STEP C — the operator identity -/

/-- **Step C.**  `integralOperator Kₙ = (multIndicatorBall n) ∘ (coulombResolventAt p z hz)`
as CLMs. -/
theorem step_C_at (p : CoulombParams) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    integralOperator (truncKernelGLpAt p n z hz)
      = (multIndicatorBall n).comp (coulombResolventAt p z hz) := by
  -- dense range of Schwartz → L²
  have hdr : DenseRange (SchwartzMap.toLpCLM ℂ ℂ (2 : ℝ≥0∞) (volume : Measure R3)) :=
    SchwartzMap.denseRange_toLpCLM (by norm_num)
  -- density of the span of the range
  have hdense : Dense (Submodule.span ℂ
      (Set.range (SchwartzMap.toLpCLM ℂ ℂ (2 : ℝ≥0∞) (volume : Measure R3))) : Set L2_R3) :=
    Dense.mono Submodule.subset_span hdr
  refine ContinuousLinearMap.ext_on hdense ?_
  rintro _ ⟨φ, rfl⟩
  -- on `φ.toLp 2 volume`, both sides agree via Step B
  apply Lp.ext
  have hB := step_B_at p n z hz φ
  -- toLpCLM φ = φ.toLp 2 volume
  simpa only [SchwartzMap.toLpCLM_apply, ContinuousLinearMap.comp_apply] using hB

/-- The `z = i` instance. -/
theorem step_C (p : CoulombParams) (n : ℕ) :
    integralOperator (truncKernelGLp p n)
      = (multIndicatorBall n).comp (coulombResolvent p) :=
  step_C_at p n Complex.I I_im_ne_zero

/-! ## STEP D — op-norm tail bound -/

/-- Pointwise: on the complement of `closedBall 0 (n+1)`, `|coulombMultiplier x| ≤ Z/(n+1)`. -/
theorem coulombMultiplier_le_on_compl (p : CoulombParams) (n : ℕ) {x : R3}
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

/-- **Step D.**  Operator-norm tail bound for the integral-operator approximants. -/
theorem step_D_at (p : CoulombParams) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
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
  have hpt : (((coulombResolventAt p z hz - integralOperator (truncKernelGLpAt p n z hz)) ψ) : R3 → ℂ)
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
          (fun y => (coulombMultiplier p y : ℂ) * (freeResolventAt z hz ψ : R3 → ℂ) y) x) 2 volume).toReal
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

/-- The `z = i` instance. -/
theorem step_D (p : CoulombParams) (n : ℕ) :
    ‖coulombResolvent p - integralOperator (truncKernelGLp p n)‖
      ≤ p.Z / (n + 1) * ‖freeResolvent‖ :=
  step_D_at p n Complex.I I_im_ne_zero

/-! ## STEP E — limit + compactness -/

/-- The integral-operator approximants converge to `coulombResolventAt p z hz` in operator norm. -/
theorem step_E_tendsto_at (p : CoulombParams) (z : ℂ) (hz : z.im ≠ 0) :
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

/-- **Step E.**  `coulombResolventAt p z hz` is a compact operator, for any non-real `z`. -/
theorem coulombResolventAt_isCompact (p : CoulombParams) (z : ℂ) (hz : z.im ≠ 0) :
    IsCompactOperator (⇑(coulombResolventAt p z hz)) := by
  apply isCompactOperator_of_tendsto (step_E_tendsto_at p z hz)
  exact Eventually.of_forall
    (fun n => isCompactOperator_integralOperator (truncKernelGLpAt p n z hz))

/-- The `z = i` instance. -/
theorem step_E_tendsto (p : CoulombParams) :
    Tendsto (fun n => integralOperator (truncKernelGLp p n)) atTop
      (𝓝 (coulombResolvent p)) :=
  step_E_tendsto_at p Complex.I I_im_ne_zero

/-- **GOAL 1.**  `coulombResolvent p` is a compact operator. -/
theorem coulombResolvent_isCompact (p : CoulombParams) :
    IsCompactOperator (⇑(coulombResolvent p)) :=
  coulombResolventAt_isCompact p Complex.I I_im_ne_zero

/-- The textbook perturbation `W = coulombResolventHalf` is compact: a scalar multiple of the
compact `coulombResolventAt p (2i)`. -/
theorem coulombResolventHalf_isCompact (p : CoulombParams) :
    IsCompactOperator (⇑(coulombResolventHalf p)) := by
  rw [coulombResolventHalf, ContinuousLinearMap.coe_smul']
  exact (coulombResolventAt_isCompact p (2 * Complex.I) h2I).smul (2 : ℂ)

/-- **GOAL 2.**  The textbook hydrogen Hamiltonian `H = −½Δ − Z/r` has essential spectrum
`[0, ∞)`. -/
theorem hydrogen_essSpectrum (p : CoulombParams) :
    Spectra.Essential.essSpectrum (hydrogen_isSelfAdjoint p) = Set.Ici (0 : ℝ) :=
  hydrogen_essSpectrum_eq_Ici_of_compact p (coulombResolventHalf_isCompact p)

end Spectra.QuantumMechanics.Hydrogen
