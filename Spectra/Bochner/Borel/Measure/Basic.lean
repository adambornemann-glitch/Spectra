/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Bochner.Borel.Identity.CauchyVague
import Spectra.Mathlib.CharFunBridge
import Spectra.Fourier.Inversion
/-!
# Existence of the diagonal Bochner spectral measure

For any strongly continuous one-parameter unitary group `U(t)` on a Hilbert
space `H` and any vector `ξ ∈ H`, there exists a finite positive Borel measure
`μ` on `ℝ` such that:

  `⟨ξ, U(t)ξ⟩ = ∫ e^{itlambda} dμ(lambda)`    for all `t ∈ ℝ`

with `μ(ℝ) = ‖ξ‖²`.

The measure is `borelMeasure U ξ` and the identity is the named lemma
`borelMeasure_fourier`; the existential `spectral_scalar_measure_exists` is a corollary.

Combined with Fourier uniqueness (**proved**, `Fourier/Unique.lean`), this
gives the complete Bochner theorem.

## Main definitions

* `borelMeasure U_grp ξ` — the diagonal Bochner spectral measure (defined upstream in
  `Bochner/Borel/CDF.lean`), used throughout this file but not redefined here.

## Main statements

* `borelMeasure_fourier` — the defining identity `⟨ξ,U(t)ξ⟩ = ∫ e^{itlambda} dμ(lambda)`.
* `spectral_scalar_measure_exists` — the packaged existence theorem.
* `m_eq_cauchy_transform` — the Cauchy-transform companion identity, `⟪ξ, R(z)ξ⟫ =
  ∫ (λ - z)⁻¹ dμ(λ)` for `z` off the real axis.
* `borelMeasure_mass` — total mass `μ(ℝ) = ‖ξ‖²`.
* `borelMeasure_smul` — `μ_{c•ξ} = ‖c‖² • μ_ξ`.
* `borelMeasure_zero` — the zero vector carries the zero measure.
* `borel_combination_ext` — extensionality bridge for complex combinations of diagonal
  measures, used downstream to prove the sesquilinearity lemmas of the polarized measure
  (`SpectralTheory/Measure/Polarized.lean`).

## Tags

spectral theorem, axiom, projection-valued measure, scalar spectral measure
-/
open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace
open Spectra.Resolvent
open Spectra.Fourier
open Spectra.OneParameterUnitaryGroup
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Borel
variable (U_grp : OneParameterUnitaryGroup (H := H))
namespace SpectralMeasure

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
      rw [show I * ((-s : ℝ) : ℂ) * (t : ℂ) = -(I * (s:ℂ) * (t:ℂ))
            from by push_cast; ring]
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
    -- push the `Iic`-integral through the `neg` embedding onto `Ici`
    rw [← h_pre,
        h_mp.setIntegral_preimage_emb h_emb
          (fun u : ℝ => cexp (-(I * (s:ℂ) * ((-u : ℝ):ℂ)))
              * cexp (-((ε:ℂ) * ((|(-u)| : ℝ):ℂ))) * h (-u)) (Set.Ici 0),
        ← integral_conj]
    refine setIntegral_congr_fun measurableSet_Ici (fun u hu => ?_)
    -- clear the `-(-u)` double negation and normalize the `cexp` argument left over
    -- from the `neg`-embedding substitution, matching the pointwise goal below
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

/-- **The Borel-transform identity** For every `z` off the real
axis, `⟪ξ, R(z)ξ⟫ = ∫ (λ - z)⁻¹ d(borelMeasure U_grp ξ)(λ)`. -/
lemma m_eq_cauchy_transform
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H) {z : ℂ} (hz : z.im ≠ 0) :
    ⟪ξ, resolvent z hz (generator_isFormalAdjoint U_grp)
          (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) ξ⟫_ℂ
      = ∫ lambda, ((lambda : ℂ) - z)⁻¹ ∂(borelMeasure U_grp ξ) :=
  tendsto_nhds_unique
    (borel_cauchy_approx_tendsto U_grp ξ hz) (borel_cauchy_vague U_grp ξ hz)

/-! ## The existence theorem --------------------------------------------------------- -/

/-- **Defining identity of the diagonal spectral measure**: for any strongly continuous
one-parameter unitary group on a complex Hilbert space and any vector ξ,

  `⟨ξ, U(t)ξ⟩ = ∫ e^{itlambda} d(borelMeasure U ξ)(lambda)`.

This is the concrete form of `spectral_scalar_measure_exists`, naming the witness. -/
theorem borelMeasure_fourier
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H) (t : ℝ) :
    ⟪ξ, U_grp.U t ξ⟫_ℂ = ∫ lambda, cexp (I * lambda * t) ∂(borelMeasure U_grp ξ) := by
  classical
  set μ := borelMeasure U_grp ξ with hμ
  haveI : IsFiniteMeasure μ := borelMeasure_isFiniteMeasure U_grp ξ
  set f : ℝ → ℂ := fun t => ⟪ξ, U_grp.U t ξ⟫_ℂ with hf
  set g : ℝ → ℂ := fun t => ∫ lambda, cexp (I * (lambda:ℂ) * (t:ℂ)) ∂μ with hg
  suffices h : f = g by exact congrFun h t
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
        rw [Complex.norm_exp, re_I_mul_ofReal_mul_ofReal, Real.exp_zero]
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
        ≤ ∫ lambda, ‖cexp (I * (lambda:ℂ) * (t:ℂ))‖ ∂μ :=
            norm_integral_le_integral_norm _
      _ = ∫ _lambda, (1:ℝ) ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall (fun lambda => ?_))
            simp only [Complex.norm_exp]
            rw [re_I_mul_ofReal_mul_ofReal, Real.exp_zero]
      _ = (μ Set.univ).toReal := by
        rw [integral_const, smul_eq_mul, mul_one]
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
          change Continuous (fun p : ℝ × ℝ =>
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
        change ‖cexp (-(I * z * (p.1:ℂ))) * cexp (I * (p.2:ℂ) * (p.1:ℂ))‖
              ≤ Real.exp (z.im * p.1) * (1:ℝ)
        have h1 : (-(I * z * (p.1:ℂ))).re = z.im * p.1 := by
          simp [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im]
        have h2 : (I * (p.2:ℂ) * (p.1:ℂ)).re = 0 := re_I_mul_ofReal_mul_ofReal p.2 p.1
        simp only [norm_mul, Complex.norm_exp, h1, h2, Real.exp_zero, mul_one]
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
        = ∫ t : ℝ,
            cexp (-(I * (s:ℂ) * (t:ℂ))) * cexp (-((ε:ℂ) * ((|t| : ℝ):ℂ))) * g t := by
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

/-- For any strongly continuous one-parameter unitary group on a complex
Hilbert space and any vector ξ, there exists a finite positive Borel
measure μ on ℝ such that `⟨ξ, U(t)ξ⟩ = ∫ e^{itlambda} dμ(lambda)`.

The witness is `borelMeasure U_grp ξ`; prefer `borelMeasure_fourier` downstream. -/
theorem spectral_scalar_measure_exists
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H) :
    ∃ (μ : Measure ℝ), IsFiniteMeasure μ ∧
      (∀ t : ℝ, ⟪ ξ, U_grp.U t ξ⟫_ℂ = ∫ lambda, cexp (I * lambda * t) ∂μ) :=
  ⟨borelMeasure U_grp ξ, borelMeasure_isFiniteMeasure U_grp ξ,
    fun t => borelMeasure_fourier U_grp ξ t⟩

/-- Total mass: evaluate `borelMeasure_fourier` at `t = 0`. -/
lemma borelMeasure_mass (ξ : H) :
    ((borelMeasure U_grp ξ) Set.univ).toReal = ‖ξ‖ ^ 2 := by
  have h := borelMeasure_fourier U_grp ξ 0
  -- left side: `U 0 = id` and `⟪ξ, ξ⟫ = ↑(‖ξ‖²)`
  rw [U_grp.identity, ContinuousLinearMap.id_apply, inner_self_eq_norm_sq_to_K] at h
  -- right side: the character at `t = 0` is the constant `1`, whose integral is the mass
  have hint : (∫ lambda : ℝ, cexp (I * (lambda : ℂ) * ((0 : ℝ) : ℂ))
        ∂(borelMeasure U_grp ξ))
      = ((((borelMeasure U_grp ξ) Set.univ).toReal : ℝ) : ℂ) := by
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [integral_const, Complex.real_smul, mul_one, Measure.real_def]
  rw [hint, ← coe_algebraMap] at h
  exact_mod_cast h.symm

/-- Scaling: `μ_{c•ξ} = ‖c‖₊² • μ_ξ`.  Both sides have transform `‖c‖²·⟪ξ,U(t)ξ⟫`;
conclude by `measure_ext_of_fourier`. -/
lemma borelMeasure_smul (c : ℂ) (ξ : H) :
    borelMeasure U_grp (c • ξ) = (‖c‖₊ ^ 2) • borelMeasure U_grp ξ := by
  refine measure_ext_of_fourier fun t => ?_
  -- left transform: sesquilinearity pulls out `conj c · c = ‖c‖²`
  have hL : (∫ ω, cexp (I * ω * t) ∂(borelMeasure U_grp (c • ξ)))
      = ((‖c‖ ^ 2 : ℝ) : ℂ) * ∫ ω, cexp (I * ω * t) ∂(borelMeasure U_grp ξ) := by
    rw [← borelMeasure_fourier U_grp (c • ξ) t, ← borelMeasure_fourier U_grp ξ t,
        map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, RCLike.conj_mul]
    norm_cast
  -- right transform: the `ℝ≥0` factor passes through the integral
  have hR : (∫ ω, cexp (I * ω * t) ∂((‖c‖₊ ^ 2) • borelMeasure U_grp ξ))
      = ((‖c‖ ^ 2 : ℝ) : ℂ) * ∫ ω, cexp (I * ω * t) ∂(borelMeasure U_grp ξ) := by
    rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    norm_cast
  rw [hL, hR]

/-- The zero vector carries the zero measure: `borelMeasure_smul` with `c = 0`. -/
lemma borelMeasure_zero : borelMeasure U_grp (0 : H) = 0 := by
  simpa using borelMeasure_smul U_grp 0 (0 : H)

/-- **Bridge to the workhorse.**  Two complex combinations of diagonal spectral measures whose
matrix-element combinations agree for all `t` have equal integrals against every bounded
measurable function.  Specialization of `integral_combination_ext'` along
`borelMeasure_fourier`; the sesquilinearity lemmas of the polarized measure
(`SpectralTheory/Measure/Polarized.lean`) are instances of this bridge. -/
lemma borel_combination_ext {n m : ℕ} (c : Fin n → ℂ) (v : Fin n → H)
    (d : Fin m → ℂ) (w : Fin m → H)
    (h : ∀ t : ℝ, ∑ i, c i * ⟪v i, U_grp.U t (v i)⟫_ℂ
        = ∑ j, d j * ⟪w j, U_grp.U t (w j)⟫_ℂ)
    {g : ℝ → ℂ} (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) :
    ∑ i, c i * ∫ ω, g ω ∂(borelMeasure U_grp (v i))
      = ∑ j, d j * ∫ ω, g ω ∂(borelMeasure U_grp (w j)) := by
  refine integral_combination_ext' c (fun i => borelMeasure U_grp (v i)) d
    (fun j => borelMeasure U_grp (w j)) (fun t => ?_) hg_meas hg_bdd
  simp only [← borelMeasure_fourier]
  exact h t

end Spectra.Borel.SpectralMeasure
