/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: QuantumMechanics/SpectralTheory/ScalarMeasure/Exists.lean
-/
import Spectra.Bochner.Borel.Basic
import Spectra.Fourier.Inversion
/-!
# Statement

For any strongly continuous one-parameter unitary group `U(t)` on a Hilbert
space `H` and any vector `ξ ∈ H`, there exists a finite positive Borel measure
`μ` on `ℝ` such that:

  `⟨ξ, U(t)ξ⟩ = ∫ e^{itlambda} dμ(lambda)`    for all `t ∈ ℝ`

with `μ(ℝ) = ‖ξ‖²`.

Combined with Fourier uniqueness (**proved**, `Fourier/Unique.lean`), this
gives the complete Bochner theorem.

## Tags

spectral theorem, axiom, projection-valued measure, scalar spectral measure
-/
open Complex MeasureTheory Filter Topology
open Spectra.Resolvent
open Spectra.Fourier
open Spectra.Kernels
open Spectra.Herglotz
open Spectra.QuantumMechanics
open OneParameterUnitaryGroup
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U_grp : OneParameterUnitaryGroup (H := H))

namespace Spectra.Bochner


/-! ## Half-line ⇒ two-sided -----------------------------------------------------------------

For continuous, bounded, Hermitian `h`, the `e^{-ε|t|}`-regularized full-line transform at
frequency `s` equals `L_h(s-iε) + conj L_h(s-iε)`, where `L_h(z) = ∫_{t≥0} e^{-izt} h(t) dt`.
Split `ℝ = Iic 0 ⊔ Ioi 0`: on `Ioi 0` (`|t| = t`) we get `L_h` directly; on `Iic 0` the
substitution `t ↦ -t` together with `h(-t) = conj h(t)` yields `conj L_h`. -/
private lemma two_sided_split {h : ℝ → ℂ} (hcont : Continuous h)
    {C : ℝ} (hbnd : ∀ t, ‖h t‖ ≤ C) (hherm : ∀ t, h (-t) = starRingEnd ℂ (h t))
    (s : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∫ t : ℝ, cexp (-(I * (s:ℂ) * (t:ℂ))) * cexp (-((ε:ℂ) * ((|t| : ℝ):ℂ))) * h t)
      = (∫ t in Set.Ici (0:ℝ), cexp (-(I * ((s:ℂ) - (ε:ℂ) * I) * (t:ℂ))) * h t)
        + starRingEnd ℂ (∫ t in Set.Ici (0:ℝ),
            cexp (-(I * ((s:ℂ) - (ε:ℂ) * I) * (t:ℂ))) * h t) := by
  set z : ℂ := (s:ℂ) - (ε:ℂ) * I with hz_def
  -- full-line integrand integrable: |kernel| = e^{-ε|t|}, times bounded h
  have F_int : Integrable (fun t : ℝ =>
      cexp (-(I * (s:ℂ) * (t:ℂ))) * cexp (-((ε:ℂ) * ((|t| : ℝ):ℂ))) * h t) volume := by
    have hker : Integrable (fun t : ℝ =>
        cexp (-(I * (s:ℂ) * (t:ℂ))) * cexp (-((ε:ℂ) * ((|t| : ℝ):ℂ)))) volume := by
      refine (integrable_two_sided_exp hε (-s)).congr ?_
      filter_upwards with t
      rw [show I * ((-s : ℝ) : ℂ) * (t : ℂ) = -(I * (s:ℂ) * (t:ℂ)) from by push_cast; ring]
      ring
    exact hker.mul_bdd hcont.aestronglyMeasurable (.of_forall hbnd)
  -- ℝ = Iic 0 ⊔ Ioi 0
  rw [← MeasureTheory.integral_add_compl (μ := volume) measurableSet_Iic F_int,
      show (Set.Iic (0:ℝ))ᶜ = Set.Ioi 0 from by ext x; simp]
  -- Ioi 0 part  =  L_h(z)
  have h_ioi : (∫ t in Set.Ioi (0:ℝ),
        cexp (-(I * (s:ℂ) * (t:ℂ))) * cexp (-((ε:ℂ) * ((|t| : ℝ):ℂ))) * h t)
      = ∫ t in Set.Ici (0:ℝ), cexp (-(I * z * (t:ℂ))) * h t := by
    rw [MeasureTheory.setIntegral_congr_set (Ioi_ae_eq_Ici (a := 0))]
    refine setIntegral_congr_fun measurableSet_Ici (fun t ht => ?_)
    rw [show (|t| : ℝ) = t from abs_of_nonneg ht, ← Complex.exp_add]
    congr 1
    congr 1
    rw [hz_def]
    apply Complex.ext <;>
      simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re,
        Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
  -- Iic 0 part  =  conj L_h(z)   (t ↦ -t  +  Hermitian symmetry)
  have h_iic : (∫ t in Set.Iic (0:ℝ),
        cexp (-(I * (s:ℂ) * (t:ℂ))) * cexp (-((ε:ℂ) * ((|t| : ℝ):ℂ))) * h t)
      = starRingEnd ℂ (∫ t in Set.Ici (0:ℝ), cexp (-(I * z * (t:ℂ))) * h t) := by
    have h_mp : MeasurePreserving (Neg.neg : ℝ → ℝ) volume volume :=
      Measure.measurePreserving_neg volume
    have h_emb : MeasurableEmbedding (Neg.neg : ℝ → ℝ) :=
      (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
    have h_pre : (Neg.neg : ℝ → ℝ) ⁻¹' Set.Ici 0 = Set.Iic 0 := by
      ext x; simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic, neg_nonneg]
    -- ∫_{Iic} F(t) = ∫_{Iic} (F∘neg)(-t),  then push through the embedding to Ici
    rw [show (∫ t in Set.Iic (0:ℝ),
            cexp (-(I * (s:ℂ) * (t:ℂ))) * cexp (-((ε:ℂ) * ((|t| : ℝ):ℂ))) * h t)
          = ∫ t in Set.Iic (0:ℝ),
            (fun u : ℝ => cexp (-(I * (s:ℂ) * ((-u : ℝ):ℂ)))
                * cexp (-((ε:ℂ) * ((|(-u)| : ℝ):ℂ))) * h (-u)) (-t) from by
        refine setIntegral_congr_fun measurableSet_Iic (fun t _ => ?_); simp]
    rw [← h_pre,
        h_mp.setIntegral_preimage_emb h_emb                            -- ⚠ orientation (mirror of fourier_identity)
          (fun u : ℝ => cexp (-(I * (s:ℂ) * ((-u : ℝ):ℂ)))
              * cexp (-((ε:ℂ) * ((|(-u)| : ℝ):ℂ))) * h (-u)) (Set.Ici 0),
        ← integral_conj]
    refine setIntegral_congr_fun measurableSet_Ici (fun u hu => ?_)
    field_simp
    -- pointwise (u ≥ 0):  F(-u) = conj(e^{-izu} h u)
    rw [map_mul, ← hherm u]
    congr 1
    rw [show (|(-u)| : ℝ) = u from by rw [abs_neg, abs_of_nonneg hu],
        ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    rw [hz_def]
    apply Complex.ext <;>
      simp [Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
  rw [h_iic, h_ioi]
  ring

/-! ## The existence theorem --------------------------------------------------------- -/

/-- For any strongly continuous one-parameter unitary group on a complex
Hilbert space and any vector ξ, there exists a finite positive Borel
measure μ on ℝ such that `⟨ξ, U(t)ξ⟩ = ∫ e^{itlambda} dμ(lambda)`. -/
theorem spectral_scalar_measure_exists
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H) :
    ∃ (μ : Measure ℝ), IsFiniteMeasure μ ∧
      (∀ t : ℝ, ⟪ ξ, U_grp.U t ξ⟫_ℂ = ∫ lambda, cexp (I * lambda * t) ∂μ) := by
  classical
  set μ := borelMeasure U_grp ξ with hμ
  haveI : IsFiniteMeasure μ := borelMeasure_isFiniteMeasure U_grp ξ
  refine ⟨μ, inferInstance, ?_⟩
  set f : ℝ → ℂ := fun t => ⟪ξ, U_grp.U t ξ⟫_ℂ with hf
  set g : ℝ → ℂ := fun t => ∫ lambda, cexp (I * (lambda:ℂ) * (t:ℂ)) ∂μ with hg
  suffices h : f = g by intro t; exact congrFun h t
  -- continuity of f
  have hf_cont : Continuous f := continuous_const.inner (continuous_unitary_apply U_grp ξ)
  -- continuity of g : dominated convergence, |e^{iλt}| = 1, μ finite
  have hg_cont : Continuous g := by
    simp only [hg]
    apply continuous_of_dominated (bound := fun _ : ℝ => (1:ℝ))
    · intro t
      exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    · intro t
      filter_upwards with lambda
      have hnorm : ‖cexp (I * (lambda:ℂ) * (t:ℂ))‖ = 1 := by
        rw [Complex.norm_exp]
        have h0 : (I * (lambda:ℂ) * (t:ℂ)).re = 0 := by
          simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im]
        rw [h0, Real.exp_zero]
      exact hnorm.le
    · exact integrable_const (1:ℝ)
    · filter_upwards with lambda
      exact Complex.continuous_exp.comp (by fun_prop)
  -- boundedness of f by ‖ξ‖²
  have hf_bdd : ∃ C, ∀ t, ‖f t‖ ≤ C := ⟨‖ξ‖ ^ 2, fun t => by
    have h := norm_inner_le_norm (𝕜 := ℂ) ξ (U_grp.U t ξ)
    rw [norm_preserving U_grp t ξ] at h; nlinarith [norm_nonneg ξ]⟩
  -- boundedness of g by μ(univ)
  have hg_bdd : ∃ C, ∀ t, ‖g t‖ ≤ C := ⟨(μ Set.univ).toReal, fun t => by
    simp only [hg]
    calc ‖∫ lambda, cexp (I * (lambda:ℂ) * (t:ℂ)) ∂μ‖
        ≤ ∫ lambda, ‖cexp (I * (lambda:ℂ) * (t:ℂ))‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ _lambda, (1:ℝ) ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall (fun lambda => ?_))
            simp only [Complex.norm_exp]
            have h0 : (I * (lambda:ℂ) * (t:ℂ)).re = 0 := by
              simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
                    Complex.ofReal_re, Complex.ofReal_im]
            rw [h0, Real.exp_zero]
      _ = (μ Set.univ).toReal := by
        rw [integral_const, smul_eq_mul, mul_one];
        exact Measure.real_def μ Set.univ⟩
  -- Hermitian symmetry of f : exactly `inner_unitary_neg`
  have hf_herm : ∀ t, f (-t) = (starRingEnd ℂ) (f t) := by
    intro t; simp only [hf]; exact inner_unitary_neg U_grp ξ t
  -- Hermitian symmetry of g : conj passes through the (real, positive) measure
  have hg_herm : ∀ t, g (-t) = (starRingEnd ℂ) (g t) := by
    intro t
    simp only [hg]
    rw [← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun lambda => ?_))
    simp only [← Complex.exp_conj]
    congr 1
    rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal,
        Complex.ofReal_neg]
    ring
  -- the two half-line Laplace transforms coincide (both = i · ∫ (λ-z)⁻¹ dμ)
  have hL : ∀ z : ℂ, z.im < 0 →
      (∫ t in Set.Ici (0:ℝ), cexp (-(I * z * t)) * f t)
        = ∫ t in Set.Ici (0:ℝ), cexp (-(I * z * t)) * g t := by
    intro z hz
    -- f-side : ⟪ξ,Rξ⟫ = -I·∫₀^∞ e^{-izt} f   and   ⟪ξ,Rξ⟫ = ∫ (λ-z)⁻¹ dμ
    have hf_lap : (∫ t in Set.Ici (0:ℝ), cexp (-(I * z * t)) * f t)
        = I * ∫ lambda, ((lambda:ℂ) - z)⁻¹ ∂μ := by
      have hB := resolvent_diag_laplace U_grp ξ hz
      have hA := m_eq_cauchy_transform U_grp ξ (ne_of_lt hz)
      rw [← hμ] at hA
      simp only [hf]
      -- both `hA` and `hB` carry the SAME resolvent (same `ne_of_lt hz` and proof args),
      -- so `⟪ξ,Rξ⟫` is syntactically shared and we may rewrite freely:
      rw [← hA, hB, ← mul_assoc,
          show I * -I = 1 from by rw [mul_neg, Complex.I_mul_I, neg_neg],
          one_mul]
    -- g-side : Fubini + laplace_exp
    have hg_lap : (∫ t in Set.Ici (0:ℝ), cexp (-(I * z * t)) * g t)
        = I * ∫ lambda, ((lambda:ℂ) - z)⁻¹ ∂μ := by
      simp only [hg]
      -- (1) pull the t-exponential into the λ-integral
      have hpull : ∀ t : ℝ,
          cexp (-(I * z * (t:ℂ))) * (∫ lambda, cexp (I * (lambda:ℂ) * (t:ℂ)) ∂μ)
            = ∫ lambda, cexp (-(I * z * (t:ℂ))) * cexp (I * (lambda:ℂ) * (t:ℂ)) ∂μ := by
        intro t; rw [integral_const_mul]
      simp_rw [hpull]
      -- (2) Fubini swap : ∫_{t≥0} ∫_λ  →  ∫_λ ∫_{t≥0}
      have hswap_int : Integrable
          (Function.uncurry (fun (t lambda : ℝ) =>
            cexp (-(I * z * (t:ℂ))) * cexp (I * (lambda:ℂ) * (t:ℂ))))
          ((volume.restrict (Set.Ici (0:ℝ))).prod μ) := by
        have h_meas : AEStronglyMeasurable
            (Function.uncurry (fun (t lambda : ℝ) =>
              cexp (-(I * z * (t:ℂ))) * cexp (I * (lambda:ℂ) * (t:ℂ))))
            ((volume.restrict (Set.Ici (0:ℝ))).prod μ) := by
          apply Continuous.aestronglyMeasurable
          show Continuous (fun p : ℝ × ℝ =>
            cexp (-(I * z * (p.1:ℂ))) * cexp (I * (p.2:ℂ) * (p.1:ℂ)))
          exact (Complex.continuous_exp.comp (by fun_prop)).mul
                (Complex.continuous_exp.comp (by fun_prop))
        -- dominator exp(z.im · t), independent of λ
        have hexp_int : Integrable (fun t : ℝ => Real.exp (z.im * t))
            (volume.restrict (Set.Ici (0:ℝ))) :=
          (integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_exp_mul_Ioi hz 0)
        have h_dom : Integrable
            (fun p : ℝ × ℝ => Real.exp (z.im * p.1) * (1:ℝ))
            ((volume.restrict (Set.Ici (0:ℝ))).prod μ) :=
          hexp_int.mul_prod (integrable_const (1:ℝ))
        refine h_dom.mono' h_meas ?_
        filter_upwards with p
        show ‖cexp (-(I * z * (p.1:ℂ))) * cexp (I * (p.2:ℂ) * (p.1:ℂ))‖
              ≤ Real.exp (z.im * p.1) * (1:ℝ)
        have h1 : (-(I * z * (p.1:ℂ))).re = z.im * p.1 := by
          simp [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im];
        have h2 : (I * (p.2:ℂ) * (p.1:ℂ)).re = 0 := by
          simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im]
        simp only [norm_mul, Complex.norm_exp, Complex.norm_exp, h1, h2, Real.exp_zero, mul_one, mul_one]
        exact le_refl (Real.exp (z.im * p.1))
      rw [integral_integral_swap hswap_int]
      -- (3) inner t-integral via laplace_exp
      have hlam : ∀ lambda : ℝ,
          (∫ t in Set.Ici (0:ℝ), cexp (-(I * z * (t:ℂ))) * cexp (I * (lambda:ℂ) * (t:ℂ)))
            = I / ((lambda:ℂ) - z) := by
        intro lambda
        apply laplace_exp
        rw [Complex.sub_im, Complex.ofReal_im]
        linarith [hz]
      simp_rw [hlam, div_eq_mul_inv]
      rw [integral_const_mul]
    rw [hf_lap, hg_lap]
  -- two-sided regularized transforms coincide:  2·Re of `hL`
  have hdecay : ∀ ε : ℝ, 0 < ε → ∀ s : ℝ,
      (∫ t : ℝ, cexp (-(I * (s:ℂ) * (t:ℂ))) * cexp (-((ε:ℂ) * ((|t| : ℝ):ℂ))) * f t)
        = ∫ t : ℝ, cexp (-(I * (s:ℂ) * (t:ℂ))) * cexp (-((ε:ℂ) * ((|t| : ℝ):ℂ))) * g t := by
    intro ε hε s
    obtain ⟨Cf, hCf⟩ := hf_bdd
    obtain ⟨Cg, hCg⟩ := hg_bdd
    rw [two_sided_split hf_cont hCf hf_herm s hε,
        two_sided_split hg_cont hCg hg_herm s hε,
        hL ((s:ℂ) - (ε:ℂ) * I)
          (show ((s:ℂ) - (ε:ℂ) * I).im < 0 from by
            simp [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]; linarith)]
  -- conclude via your proved keystone
  exact eq_of_fourier_decay_eq hf_cont hg_cont hf_bdd hg_bdd hdecay

end Spectra.Bochner
