/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Diagonal.Basic
import Spectra.Fourier.IsUnique
import Spectra.Kernel.Poisson.Lemmas

/-!
# The Fourier identity linking the resolvent to the unitary group

For a strongly continuous one-parameter unitary group `U_grp` and a vector `ξ`, this file proves
the key identity connecting the resolvent of the generator to the Fourier–Laplace transform of the
diagonal matrix element `t ↦ ⟪ξ, U_grp.U t ξ⟫`:

`2 · Im ⟪ξ, R(λ + iε) ξ⟫ = ∫ t, e^{-iλt} e^{-ε|t|} ⟪ξ, U_grp.U t ξ⟫ dt`.

The proof splits the resolvent at `λ ± iε` into one-sided Laplace transforms via
`resolvent_diag_lower_laplace`/`resolvent_diag_upper_eq_conj`, reflects the upper piece using the
Hermitian symmetry `⟪ξ, U(-t)ξ⟫ = conj ⟪ξ, U(t)ξ⟫` (`inner_unitary_neg`), and glues the two halves
into the two-sided integral. The elementary Fourier transform of the two-sided exponential kernel
`e^{-δ|·|}` needed elsewhere is recorded as `fourier_kernel_eval`.

## Main results

* `fourier_identity` : the resolvent/Fourier-transform identity above.
* `fourier_kernel_eval` : `∫ e^{-iλt} e^{-δ|λ|} dλ = 2δ/(t² + δ²)`.
-/

open Complex MeasureTheory Filter Topology
open Spectra.OneParameterUnitaryGroup
open scoped InnerProductSpace
open Spectra.Resolvent
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Fourier
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- Hermitian symmetry of the correlation:
`⟪ξ, U(-t)ξ⟫ = conj⟪ξ, U(t)ξ⟫`, since `U(-t) = U(t)*`. -/
lemma inner_unitary_neg
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H) (t : ℝ) :
    ⟪ξ, U_grp.U (-t) ξ⟫_ℂ = starRingEnd ℂ ⟪ξ, U_grp.U t ξ⟫_ℂ := by
  have hcomp : U_grp.U t (U_grp.U (-t) ξ) = ξ := by
    have hlaw := congrArg (fun f : H →L[ℂ] H => f ξ) (U_grp.group_law t (-t))
    simp only [add_neg_cancel, U_grp.identity, ContinuousLinearMap.id_apply,
               ContinuousLinearMap.comp_apply] at hlaw
    exact hlaw.symm
  calc ⟪ξ, U_grp.U (-t) ξ⟫_ℂ
      = ⟪U_grp.U t ξ, U_grp.U t (U_grp.U (-t) ξ)⟫_ℂ := (U_grp.unitary t ξ _).symm
    _ = ⟪U_grp.U t ξ, ξ⟫_ℂ := by rw [hcomp]
    _ = starRingEnd ℂ ⟪ξ, U_grp.U t ξ⟫_ℂ :=
      Eq.symm (InnerProductSpace.conj_inner_symm ((U_grp.U t) ξ) ξ)

/-- Key Fourier identity:
`2 Im ⟨ξ, R(λ+iε) ξ⟩ = ∫_ℝ e^{-iλt} e^{-ε|t|} ⟨ξ, U(t)ξ⟩ dt`. -/
lemma fourier_identity
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H)
    {ε : ℝ} (hε : 0 < ε) (lambda : ℝ) :
    ((2 * (⟪ξ, resolvent (⟨lambda, ε⟩ : ℂ) hε.ne'
                (generator_isFormalAdjoint U_grp)
                (range_plus_i_eq_top U_grp)
                (range_minus_i_eq_top U_grp) ξ⟫_ℂ).im : ℝ) : ℂ)
      = ∫ t : ℝ, cexp (-(I * (lambda : ℂ) * (t : ℂ))) *
                  cexp (-(↑ε * ↑|t|)) * ⟪ξ, U_grp.U t ξ⟫_ℂ := by
  set hsym := generator_isFormalAdjoint U_grp
  set hplus := range_plus_i_eq_top U_grp
  set hminus := range_minus_i_eq_top U_grp
  set m_plus := ⟪ξ, resolvent (⟨lambda, ε⟩ : ℂ) hε.ne' hsym hplus hminus ξ⟫_ℂ
  set m_minus := ⟪ξ, resolvent (⟨lambda, -ε⟩ : ℂ) (neg_ne_zero.mpr hε.ne')
                    hsym hplus hminus ξ⟫_ℂ
  -- The two pieces from the helpers:
  have h_minus_int : m_minus = -I * ∫ t in Set.Ici (0:ℝ),
        cexp (-(I * (lambda:ℂ) * (t:ℂ))) * (Real.exp (-(ε * t)) : ℂ) *
        ⟪ξ, U_grp.U t ξ⟫_ℂ :=
    resolvent_diag_lower_laplace U_grp ξ hε lambda
  have h_conj : m_plus = starRingEnd ℂ m_minus :=
    resolvent_diag_upper_eq_conj U_grp ξ hε lambda
  -- ── Stage A: m_plus as an integral over Iic 0
  have h_plus_int : m_plus = I * ∫ s in Set.Iic (0:ℝ),
        cexp (-(I * (lambda:ℂ) * (s:ℂ))) * (Real.exp (ε * s) : ℂ) *
        ⟪ξ, U_grp.U s ξ⟫_ℂ := by
    rw [h_conj, h_minus_int]
    rw [map_mul, map_neg, Complex.conj_I, neg_neg]
    congr 1
    rw [← integral_conj]
    -- Substitute via measurePreserving_neg (sends Ici 0 ↦ Iic 0).
    have h_mp : MeasurePreserving (Neg.neg : ℝ → ℝ) volume volume :=
      Measure.measurePreserving_neg volume
    have h_emb : MeasurableEmbedding (Neg.neg : ℝ → ℝ) :=
      (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
    have h_pre : (Neg.neg : ℝ → ℝ) ⁻¹' Set.Ici 0 = Set.Iic 0 := by
      ext x; simp only [Set.neg_preimage, Set.neg_Ici, neg_zero, Set.mem_Iic]
    rw [← h_mp.setIntegral_preimage_emb h_emb
          (fun t => starRingEnd ℂ
                      (cexp (-(I * (lambda:ℂ) * (t:ℂ))) *
                       (Real.exp (-(ε * t)) : ℂ) *
                       ⟪ξ, U_grp.U t ξ⟫_ℂ)) (Set.Ici 0), h_pre]
    refine setIntegral_congr_fun measurableSet_Iic (fun s _ => ?_)
    simp only [map_mul, ← Complex.exp_conj, Complex.conj_ofReal]
    simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal,
               Complex.ofReal_neg, inner_unitary_neg, Complex.conj_conj]
    congr 1; · push_cast; ring_nf
  -- ── Stage B: combine m_plus - m_minus into ∫_ℝ ────────────────────────────
  have h_main : m_plus - m_minus = I * ∫ t : ℝ,
        cexp (-(I * (lambda:ℂ) * (t:ℂ))) * cexp (-(↑ε * ↑|t|)) *
        ⟪ξ, U_grp.U t ξ⟫_ℂ := by
    simp only [h_plus_int, h_minus_int, ofReal_exp, ofReal_mul, ofReal_neg,
      neg_mul, sub_neg_eq_add, sub_neg_eq_add, ← mul_add]
    -- Match integrands to the e^{-ε|t|} form on each half (|s| = -s on Iic, |t| = t on Ici).
    have h_iic : (∫ s in Set.Iic (0:ℝ),
            cexp (-(I * (lambda:ℂ) * (s:ℂ))) * cexp ((↑ε * ↑s : ℂ)) *
            ⟪ξ, U_grp.U s ξ⟫_ℂ) =
          ∫ s in Set.Iic (0:ℝ),
            cexp (-(I * (lambda:ℂ) * (s:ℂ))) * cexp (-(↑ε * ↑|s|)) *
            ⟪ξ, U_grp.U s ξ⟫_ℂ := by
      refine setIntegral_congr_fun measurableSet_Iic (fun s hs => ?_)
      have : (↑ε * (↑s : ℂ)) = -((↑ε : ℂ) * ↑|s|) := by
        rw [show |s| = -s from abs_of_nonpos hs]; push_cast; ring
      rw [this]
    have h_ici : (∫ t in Set.Ici (0:ℝ),
            cexp (-(I * (lambda:ℂ) * (t:ℂ))) * cexp (-(↑ε * ↑t : ℂ)) *
            ⟪ξ, U_grp.U t ξ⟫_ℂ) =
          ∫ t in Set.Ici (0:ℝ),
            cexp (-(I * (lambda:ℂ) * (t:ℂ))) * cexp (-(↑ε * ↑|t|)) *
            ⟪ξ, U_grp.U t ξ⟫_ℂ := by
      refine setIntegral_congr_fun measurableSet_Ici (fun t ht => ?_)
      rw [show |t| = t from abs_of_nonneg ht]
    rw [h_iic, h_ici]
    have F_int : Integrable
        (fun t : ℝ => cexp (-(I * (lambda:ℂ) * (t:ℂ))) * cexp (-(↑ε * ↑|t|)) *
                      ⟪ξ, U_grp.U t ξ⟫_ℂ) volume := by
      -- (FT kernel) × decay is integrable.
      have h_int : Integrable
          (fun t : ℝ => cexp (-(I * (lambda:ℂ) * (t:ℂ))) * cexp (-(↑ε * ↑|t|))) volume := by
        have h_eq : (fun t : ℝ => cexp (-(I * (lambda:ℂ) * (t:ℂ))) * cexp (-(↑ε * ↑|t|))) =
                    (fun t : ℝ => cexp (-(↑ε * ↑|t|)) * cexp (I * ↑(-lambda) * ↑t)) := by
          funext t; rw [mul_comm]; congr 1; push_cast; ring_nf
        rw [h_eq]
        exact integrable_two_sided_exp hε (-lambda)
      -- ⟪ξ, U(t)ξ⟫ is bounded by ‖ξ‖²  — pass the bound directly, no `∃`.
      have h_bnd : ∀ᵐ t ∂(volume : Measure ℝ), ‖⟪ξ, U_grp.U t ξ⟫_ℂ‖ ≤ ‖ξ‖^2 := by
        filter_upwards with t
        calc ‖⟪ξ, U_grp.U t ξ⟫_ℂ‖
            ≤ ‖ξ‖ * ‖U_grp.U t ξ‖ := norm_inner_le_norm ξ _
          _ = ‖ξ‖ * ‖ξ‖           := by rw [norm_preserving U_grp t ξ]
          _ = ‖ξ‖^2               := by ring
      exact h_int.mul_bdd
        (continuous_const.inner (U_grp.strong_continuous ξ)).aestronglyMeasurable h_bnd
    rw [← MeasureTheory.integral_add_compl (μ := volume) measurableSet_Iic F_int,
        show (Set.Iic (0:ℝ))ᶜ = Set.Ioi 0 from by ext; simp,
        MeasureTheory.setIntegral_congr_set (Ioi_ae_eq_Ici (a := 0))]
  -- ── Stage C: algebra m+ − m₋ = (2·Im m+)·I ────────────────────────────────
  have h_2_im : m_plus - m_minus = ((2 * m_plus.im : ℝ) : ℂ) * I := by
    have h_mm_eq : m_minus = starRingEnd ℂ m_plus := by
      rw [h_conj]; exact (Complex.conj_conj _).symm
    rw [h_mm_eq]
    apply Complex.ext
    · simp [Complex.sub_re, Complex.conj_re, Complex.mul_re, Complex.mul_im,
            Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    · simp [Complex.sub_im, Complex.conj_im, Complex.mul_re, Complex.mul_im,
            Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
  -- ── Conclude: divide by I ─────────────────────────────────────────────────
  have h_cancel : I * ((2 * m_plus.im : ℝ) : ℂ) = I * ∫ t : ℝ,
        cexp (-(I * (lambda:ℂ) * (t:ℂ))) * cexp (-(↑ε * ↑|t|)) *
        ⟪ξ, U_grp.U t ξ⟫_ℂ := by
    rw [← h_main, h_2_im, mul_comm]
  exact mul_left_cancel₀ Complex.I_ne_zero h_cancel

/-- `∫_λ e^{-iλt} e^{-δ|λ|} dλ = 2δ/(t²+δ²)`, the FT of `e^{-δ|·|}` at frequency `-t`. -/
lemma fourier_kernel_eval {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    (∫ lambda : ℝ, cexp (-(I * (lambda : ℂ) * (t : ℂ))) * (Real.exp (-(δ * |lambda|)) : ℂ))
      = ((2 * δ / (t ^ 2 + δ ^ 2) : ℝ) : ℂ) := by
  have h_eq :
      (fun lambda : ℝ => cexp (-(I * (lambda : ℂ) * (t : ℂ))) * (Real.exp (-(δ * |lambda|)) : ℂ))
        = (fun lambda : ℝ => cexp (-(↑δ * ↑|lambda|)) * cexp (I * (↑(-t)) * ↑lambda)) := by
    funext lambda
    rw [Complex.ofReal_exp, mul_comm]
    congr 1
    · congr 1; push_cast; ring
    · congr 1; push_cast; ring
  rw [h_eq, fourier_two_sided_exp hδ (-t)]
  congr 1
  rw [neg_sq]

end Spectra.Fourier
