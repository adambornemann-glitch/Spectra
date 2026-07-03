/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
File: Spectra/Spaces/Sobolev/DensityResults.lean
-/
import Spectra.Spaces.Sobolev.IntegrationByParts
import Spectra.Spaces.Sobolev.MeyersMulti
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

open MeasureTheory Complex
open scoped Pointwise ContDiff

namespace Spectra.Sobolev

/-! ### Density results -/

/-- For smooth compactly supported `φ`, the classical partial derivative `∂ᵢφ`
    is the weak derivative of `hmem.toLp φ` in direction `i`. -/
lemma hasWeakDerivative_of_smooth_compactSupport
    {φ : R3 → ℂ} (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ)
    {i : Fin 3}
    (hmem : MemLp φ 2 (volume : Measure R3))
    (hdmem : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) 2
      (volume : Measure R3)) :
    HasWeakDerivative (hmem.toLp φ) i
      (hdmem.toLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))) := by
  haveI : (volume : Measure R3).IsAddHaarMeasure := by
    infer_instance
  haveI : IsFiniteMeasureOnCompacts (volume : Measure R3) := by
    infer_instance
  intro ψ hψ_s hψ_c
  -- Continuities & compact supports
  have hφ_cont  : Continuous φ := hφ.continuous
  have hψ_cont  : Continuous ψ := hψ_s.continuous
  have hdφ_cont : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (contDiff_partialDeriv φ i hφ).continuous
  have hdψ_cont : Continuous (fun x => fderiv ℝ ψ x (EuclideanSpace.single i 1)) :=
    (contDiff_partialDeriv ψ i hψ_s).continuous
  have hdφ_supp : HasCompactSupport
      (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    hasCompactSupport_partialDeriv φ i hsupp
  -- Integrabilities for IBP
  have hint_f'g : Integrable
      (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1) * ψ x) volume :=
    (hdφ_cont.mul hψ_cont).integrable_of_hasCompactSupport hdφ_supp.mul_right
  have hint_fg' : Integrable
      (fun x => φ x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) volume :=
    (hφ_cont.mul hdψ_cont).integrable_of_hasCompactSupport hsupp.mul_right
  have hint_fg : Integrable (fun x => φ x * ψ x) volume :=
    (hφ_cont.mul hψ_cont).integrable_of_hasCompactSupport hsupp.mul_right
  -- Differentiability everywhere
  have hφ_diff  : Differentiable ℝ φ :=
    hφ.differentiable  (by exact_mod_cast ENat.top_ne_zero)
  have hψ_diff  : Differentiable ℝ ψ :=
    hψ_s.differentiable (by exact_mod_cast ENat.top_ne_zero)
  -- Mathlib's IBP for Fréchet derivatives along a direction
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure R3)) (𝕜 := ℂ)
    (v := (EuclideanSpace.single i (1 : ℝ)))
    hint_f'g hint_fg' hint_fg
    (fun x _ => hφ_diff x) (fun x _ => hψ_diff x)
  -- Bridge L² coercions to bare functions
  have h_lhs : ∫ x, (hmem.toLp φ : R3 → ℂ) x *
        fderiv ℝ ψ x (EuclideanSpace.single i 1) =
      ∫ x, φ x * fderiv ℝ ψ x (EuclideanSpace.single i 1) :=
    integral_congr_ae (hmem.coeFn_toLp.mono fun x hx => by simp [hx])
  have h_rhs : ∫ x,
        (hdmem.toLp (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) : R3 → ℂ) x *
        ψ x = ∫ x, fderiv ℝ φ x (EuclideanSpace.single i 1) * ψ x :=
    integral_congr_ae (hdmem.coeFn_toLp.mono fun x hx => by simp [hx])
  rw [h_lhs, h_rhs]
  exact hibp

/-- Smooth compactly supported functions belong to H². -/
lemma smooth_compactSupport_memSobolevH2 (φ : R3 → ℂ)
    (hφ_inf : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ)
    (hmem : MemLp φ 2 (volume : Measure R3)) :
    MemSobolevH2 (MemLp.toLp φ hmem) := by
  refine ⟨?h1, ?h2⟩
  case h1 =>
    intro i
    exact ⟨_, hasWeakDerivative_of_smooth_compactSupport hφ_inf hsupp
      hmem (memLp_partialDeriv φ i hφ_inf hsupp)⟩
  case h2 =>
    intro i j
    have hdiφ_s : ContDiff ℝ ∞
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
      contDiff_partialDeriv φ i hφ_inf
    have hdiφ_c : HasCompactSupport
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
      hasCompactSupport_partialDeriv φ i hsupp
    exact ⟨_, _,
      hasWeakDerivative_of_smooth_compactSupport hφ_inf hsupp
        hmem (memLp_partialDeriv φ i hφ_inf hsupp),
      hasWeakDerivative_of_smooth_compactSupport hdiφ_s hdiφ_c
        (memLp_partialDeriv φ i hφ_inf hsupp)
        (memLp_partialDeriv _ j hdiφ_s hdiφ_c)⟩

/-- **H²(ℝ³) is dense in L²(ℝ³).** -/
theorem sobolevH2_dense : Dense (SobolevH2 : Set L2_R3) := by
  apply Dense.mono _ dense_test_functions_L2
  rintro g ⟨φ, hφ, hsupp, hae⟩
  show MemSobolevH2 g
  have hmem := memLp_of_smooth_compactSupport φ hφ hsupp
  have h_eq : g = hmem.toLp φ :=
    Subtype.ext (AEEqFun.ext (hae.trans hmem.coeFn_toLp.symm))
  rw [h_eq]
  exact smooth_compactSupport_memSobolevH2 φ hφ hsupp hmem

/-- **C_c^∞(ℝ³) is dense in H¹(ℝ³).**-/
theorem smooth_compactly_supported_dense_H1 :
    ∀ (f : L2_R3) (hf : MemSobolevH1 f) (ε : ℝ) (_hε : 0 < ε),
    ∃ (g : L2_R3) (hg : MemSobolevH2 g),
      ‖f - g‖ < ε ∧
      ∀ i, ‖weakGradient f hf i - weakGradient g (sobolevH2_le_H1 hg) i‖ < ε := by
  intro f hf ε hε
  obtain ⟨φ, hφ, hφ_supp, hf_close, hgrad_close⟩ :=
    meyers_serrin_approx_multi f (weakGradient f hf)
      (weakGradient_spec f hf) ε hε
  set hmem := memLp_of_smooth_compactSupport φ hφ hφ_supp
  refine ⟨hmem.toLp φ,
    smooth_compactSupport_memSobolevH2 φ hφ hφ_supp hmem,
    hf_close, ?_⟩
  intro i
  have h_grad_eq : weakGradient (hmem.toLp φ)
      (sobolevH2_le_H1
        (smooth_compactSupport_memSobolevH2 φ hφ hφ_supp hmem)) i =
      (memLp_partialDeriv φ i hφ hφ_supp).toLp
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
    apply hasWeakDerivative_unique (hmem.toLp φ) i
    · exact weakGradient_spec _ _ i
    · exact hasWeakDerivative_of_smooth_compactSupport hφ hφ_supp hmem
        (memLp_partialDeriv φ i hφ hφ_supp)
  rw [h_grad_eq]
  exact hgrad_close i

end Spectra.Sobolev
