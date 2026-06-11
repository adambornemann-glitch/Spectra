/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: U1Cover.lean
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Spectra.ModularTheory.Cocycle
import Spectra.ModularTheory.NaturalCone

namespace Spectra.KMS

open Real Complex

/-! ## The Structural 2π — Universal Cover of U(1)

This section sits entirely upstream of operator theory. Its single result
formalises the source of every 2π appearing downstream in modular theory:
the exponential `t ↦ exp(it)` realises `Circle ≃ ℝ/2πℤ`, with kernel
exactly `2πℤ`.

No Hilbert spaces, no antilinear operators, no closures, no modular
operators — just the period of `e^{iθ}`. Every 2π elsewhere in this
library (KMS strip width, the 1/4 in `Δ^{1/4}Ω`, eventually
Bisognano–Wichmann's `2π·K_boost`) is a downstream normalisation choice
against this one fact. -/

/-- **The 2π is the kernel of the universal cover `ℝ ↠ U(1)`.**

    The exponential `ℝ → Circle, t ↦ exp(it)` is a continuous surjective
    group homomorphism whose kernel is `2πℤ`. Equivalently, `Circle ≃ ℝ/2πℤ`.

    This is the irreducible source of the 2π in modular theory:
    `modularUnitary M Δ t` is, on each spectral subspace with eigenvalue
    `λ > 0`, the character `t ↦ exp(it · log λ)`, which factors through
    this universal cover. -/
theorem Circle.exp_eq_one_iff_int_mul_two_pi (t : ℝ) :
    Circle.exp t = 1 ↔ ∃ n : ℤ, t = n * (2 * Real.pi) := by
  erw [Subtype.ext_iff]
  -- (Circle.exp t : ℂ) = Complex.exp (t * I);  ((1 : Circle) : ℂ) = 1
  change Complex.exp (↑t * Complex.I) = 1 ↔ _
  rw [Complex.exp_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- hn : (t : ℂ) * I = n * (2 * π * I)
    have h : (↑t : ℂ) * Complex.I = (↑n * (2 * (↑Real.pi : ℂ))) * Complex.I := by
      rw [hn]; ring
    have := mul_right_cancel₀ Complex.I_ne_zero h
    exact_mod_cast this
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

section ExistenceOfAlpha

open MeasureTheory intervalIntegral

variable {χ : ℝ → Circle}

/-! ### Setup: the ℂ-valued character and its primitive -/

/-- The ℂ-valued version of `χ`, obtained by coercing `Circle → ℂ`. -/
private noncomputable abbrev fχ (χ : ℝ → Circle) (t : ℝ) : ℂ := (χ t : ℂ)

/-- The primitive `F(t) = ∫₀ᵗ (χ s : ℂ) ds`. -/
private noncomputable def Fχ (χ : ℝ → Circle) (t : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..t, fχ χ s

/-- `fχ` is continuous. -/
private lemma fχ_continuous (h_cts : Continuous χ) : Continuous (fχ χ) :=
  continuous_subtype_val.comp h_cts

/-- `fχ 0 = 1`. -/
private lemma fχ_zero (h_zero : χ 0 = 1) : fχ χ 0 = 1 := by
  show ((χ 0 : Circle) : ℂ) = 1
  rw [h_zero]; rfl

/-- `fχ` is multiplicative: `fχ(s + t) = fχ(s) · fχ(t)`. -/
private lemma fχ_mul (h_hom : ∀ s t, χ (s + t) = χ s * χ t) (s t : ℝ) :
    fχ χ (s + t) = fχ χ s * fχ χ t := by
  show ((χ (s + t) : Circle) : ℂ) = ((χ s : Circle) : ℂ) * ((χ t : Circle) : ℂ)
  rw [h_hom]
  rfl  -- Submonoid coercion preserves multiplication

/-! ### `F` is C¹ via FTC -/

/-- `F(0) = 0`. -/
private lemma Fχ_zero : Fχ χ 0 = 0 :=
  intervalIntegral.integral_same

/-- `F` is differentiable everywhere with `F'(t) = fχ(t)`. -/
private lemma Fχ_hasDerivAt (h_cts : Continuous χ) (t : ℝ) :
    HasDerivAt (Fχ χ) (fχ χ t) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((fχ_continuous h_cts).intervalIntegrable 0 t)
    (fχ_continuous h_cts).stronglyMeasurable.stronglyMeasurableAtFilter
    (fχ_continuous h_cts).continuousAt

/-- `F'(0) = 1`. -/
private lemma Fχ_deriv_at_zero (h_zero : χ 0 = 1) (h_cts : Continuous χ) :
    HasDerivAt (Fχ χ) 1 0 := by
  have h := Fχ_hasDerivAt h_cts 0
  rwa [fχ_zero h_zero] at h

/-- Since `F(0) = 0` and `F'(0) = 1`, `F` is nonzero on a punctured neighbourhood
    of `0`: there exists `δ > 0` with `F δ ≠ 0`. -/
private lemma Fχ_exists_nonzero (h_zero : χ 0 = 1) (h_cts : Continuous χ) :
    ∃ δ > 0, Fχ χ δ ≠ 0 := by
  have hderiv := Fχ_deriv_at_zero h_zero h_cts
  have hslope := hderiv.tendsto_slope
  -- hslope : Tendsto (slope (Fχ χ) 0) (𝓝[≠] 0) (𝓝 1)
  rw [Metric.tendsto_nhdsWithin_nhds] at hslope
  obtain ⟨δ₀, hδ₀_pos, h_close⟩ := hslope (1/2) (by norm_num)
  refine ⟨δ₀/2, by linarith, ?_⟩
  intro hF_zero
  have h_ne : (δ₀/2 : ℝ) ≠ 0 := by positivity
  have h_dist : dist (δ₀/2 : ℝ) 0 < δ₀ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith : (0 : ℝ) < δ₀/2)]
    linarith
  have h := h_close h_ne h_dist
  -- h : dist (slope (Fχ χ) 0 (δ₀/2)) 1 < 1/2
  -- But slope vanishes since Fχ χ 0 = 0 and Fχ χ (δ₀/2) = 0.
  have hslope_zero : slope (Fχ χ) 0 (δ₀/2) = 0 := by
    show (δ₀/2 - 0)⁻¹ • (Fχ χ (δ₀/2) - Fχ χ 0) = 0
    rw [Fχ_zero, hF_zero]; simp
  rw [hslope_zero] at h
  -- h : dist (0 : ℂ) 1 < 1/2; but dist 0 1 = 1.
  rw [dist_zero_left] at h
  simp at h
  linarith

end ExistenceOfAlpha

/-- **Part B: Classification of Continuous Characters of ℝ.**

    Every continuous group homomorphism `χ : ℝ → Circle` factors through
    `Circle.exp`: there is a *unique* `α : ℝ` with `χ(t) = Circle.exp(α · t)`.

    Combined with Part A (`Circle.exp_eq_one_iff_int_mul_two_pi`), this
    establishes the structural claim in full:

      Cont_grp(ℝ, U(1)) ≅ ℝ,    χ ↦ α,

    realised concretely by the universal cover `ℝ ↠ ℝ/2πℤ = U(1)`.
    Every 2π in modular theory descends from this. -/
theorem Circle.continuous_addChar_classify
    (χ : ℝ → Circle)
    (h_zero : χ 0 = 1)
    (h_hom : ∀ s t : ℝ, χ (s + t) = χ s * χ t)
    (h_cts : Continuous χ) :
    ∃! α : ℝ, ∀ t : ℝ, χ t = Circle.exp (α * t) := by
  have hexist : ∃ α : ℝ, ∀ t : ℝ, χ t = Circle.exp (α * t) := by
    -- ===== Step 1: Translation identity  F(s+t) = F(s) + χ(s)·F(t) =====
    -- Strategy: g(u) := F(s+u) − F(s) − χ(s)·F(u) has g(0)=0 and g'(·)=0, so g ≡ 0.
    have h_Fχ_trans : ∀ s t : ℝ, Fχ χ (s + t) = Fχ χ s + fχ χ s * Fχ χ t := by
      intro s t
      suffices h : Fχ χ (s + t) - Fχ χ s - fχ χ s * Fχ χ t = 0 by linear_combination h
      set g : ℝ → ℂ := fun u => Fχ χ (s + u) - Fχ χ s - fχ χ s * Fχ χ u with hg_def
      have hg0 : g 0 = 0 := by simp [hg_def, Fχ_zero]
      have hgd : ∀ x : ℝ, HasDerivAt g 0 x := by
        intro x
        have h_shift : HasDerivAt (fun u : ℝ => s + u) 1 x :=
          (hasDerivAt_id x).const_add s
        have h1 : HasDerivAt (fun u : ℝ => Fχ χ (s + u)) (fχ χ (s + x)) x := by
          have h := (Fχ_hasDerivAt h_cts (s + x)).scomp x h_shift
          simp only [one_smul] at h
          exact HasDerivAt.congr_deriv h rfl
        have h2 : HasDerivAt (fun _ : ℝ => Fχ χ s) 0 x := hasDerivAt_const x _
        have h3 : HasDerivAt (fun u : ℝ => fχ χ s * Fχ χ u) (fχ χ s * fχ χ x) x :=
          (Fχ_hasDerivAt h_cts x).const_mul (fχ χ s)
        have hg : HasDerivAt g (fχ χ (s + x) - 0 - fχ χ s * fχ χ x) x :=
          (h1.sub h2).sub h3
        have heq : fχ χ (s + x) - 0 - fχ χ s * fχ χ x = 0 := by
          rw [fχ_mul h_hom]; ring
        rwa [heq] at hg
      have hg_const : g t = g 0 :=
        is_const_of_deriv_eq_zero (fun x => (hgd x).differentiableAt)
          (fun x => (hgd x).deriv) t 0
      exact
        (AddSemiconjBy.eq_zero_iff (g 0)
              (congrFun (congrArg HAdd.hAdd (id (Eq.symm hg_const))) (g 0))).mp
          hg0
    -- ===== Step 2: Pick δ > 0 with F(δ) ≠ 0 =====
    obtain ⟨δ, hδ_pos, hδ_ne⟩ := Fχ_exists_nonzero h_zero h_cts
    -- ===== Step 3: χ(s) = (F(s+δ) − F(s))/F(δ) =====
    have h_fχ_eq : ∀ s, fχ χ s = (Fχ χ (s + δ) - Fχ χ s) / Fχ χ δ := by
      intro s
      have h := h_Fχ_trans s δ
      rw [eq_div_iff hδ_ne]
      exact Eq.symm (sub_eq_of_eq_add' (h_Fχ_trans s δ))
    -- ===== Step 4: fχ has derivative c·fχ where c := (χ(δ) − 1)/F(δ) =====
    set c : ℂ := (fχ χ δ - 1) / Fχ χ δ with hc_def
    have h_fχ_deriv : ∀ s, HasDerivAt (fχ χ) (c * fχ χ s) s := by
      intro s
      have h_shift : HasDerivAt (fun u : ℝ => u + δ) 1 s := (hasDerivAt_id s).add_const δ
      have h1 : HasDerivAt (fun u : ℝ => Fχ χ (u + δ)) (fχ χ (s + δ)) s := by
        have h := (Fχ_hasDerivAt h_cts (s + δ)).scomp s h_shift
        simp only [one_smul] at h
        exact HasDerivAt.congr_deriv h rfl
      have h2 : HasDerivAt (Fχ χ) (fχ χ s) s := Fχ_hasDerivAt h_cts s
      have h3 : HasDerivAt (fun u : ℝ => (Fχ χ (u + δ) - Fχ χ u) / Fχ χ δ)
                  ((fχ χ (s + δ) - fχ χ s) / Fχ χ δ) s :=
        (h1.sub h2).div_const (Fχ χ δ)
      -- Convert function back to fχ χ via h_fχ_eq.
      have h_fun_eq : (fun u : ℝ => (Fχ χ (u + δ) - Fχ χ u) / Fχ χ δ) = fχ χ :=
        funext (fun s => (h_fχ_eq s).symm)
      rw [h_fun_eq] at h3
      -- Convert value via fχ_mul: (fχ(s+δ) − fχ(s))/F(δ) = c · fχ(s).
      have h_val : (fχ χ (s + δ) - fχ χ s) / Fχ χ δ = c * fχ χ s := by
        rw [hc_def, fχ_mul h_hom]; field_simp
      rwa [h_val] at h3
    -- ===== Step 5: fχ(t) = exp(c·t)  (linear ODE y' = c·y, y(0) = 1) =====
    -- Strategy: g(u) := fχ(u)·exp(−c·u) has g(0) = 1 and g'(·) = 0, so g ≡ 1.
    have h_fχ_exp : ∀ t, fχ χ t = Complex.exp (c * (t : ℂ)) := by
      intro t
      set g : ℝ → ℂ := fun u => fχ χ u * Complex.exp (-c * (u : ℂ)) with hg_def
      have hg0 : g 0 = 1 := by
        simp [hg_def, fχ_zero h_zero]
      have hgd : ∀ x : ℝ, HasDerivAt g 0 x := by
        intro x
        have h1 : HasDerivAt (fχ χ) (c * fχ χ x) x := h_fχ_deriv x
        have h_id : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 x :=
          Complex.ofRealCLM.hasDerivAt
        have h_lin : HasDerivAt (fun u : ℝ => -c * (u : ℂ)) (-c) x := by
          simpa using h_id.const_mul (-c)
        have h2 : HasDerivAt (fun u : ℝ => Complex.exp (-c * (u : ℂ)))
                    (Complex.exp (-c * (x : ℂ)) * (-c)) x := h_lin.cexp
        have hg : HasDerivAt g
            (c * fχ χ x * Complex.exp (-c * (x : ℂ)) +
              fχ χ x * (Complex.exp (-c * (x : ℂ)) * (-c))) x := h1.mul h2
        have heq : c * fχ χ x * Complex.exp (-c * (x : ℂ)) +
            fχ χ x * (Complex.exp (-c * (x : ℂ)) * (-c)) = 0 := by ring
        rwa [heq] at hg
      have hgt : g t = 1 := by
        have h_const : g t = g 0 :=
          is_const_of_deriv_eq_zero (fun x => (hgd x).differentiableAt)
            (fun x => (hgd x).deriv) t 0
        rw [h_const, hg0]
      -- From  fχ(t)·exp(−c·t) = 1  extract  fχ(t) = exp(c·t).
      have hinv : fχ χ t = (Complex.exp (-c * (t : ℂ)))⁻¹ :=
        Eq.symm (inv_eq_of_mul_eq_one_left hgt)
      rw [hinv, show -c * (t : ℂ) = -(c * t) by ring, Complex.exp_neg, inv_inv]
    -- ===== Step 6: Re(c) = 0  (unitarity of χ forces c imaginary) =====
    have h_re_c : c.re = 0 := by
      have h_norm : ‖fχ χ 1‖ = 1 := by
        change ‖((χ 1 : Circle) : ℂ)‖ = 1
        exact Circle.norm_coe (χ 1)
      have h_exp : fχ χ 1 = Complex.exp c := by
        rw [h_fχ_exp 1]; push_cast; ring_nf
      rw [h_exp, Complex.norm_exp] at h_norm
      exact (Real.exp_eq_one_iff c.re).mp h_norm
    -- ===== Step 7: α := Im(c). Then χ(t) = exp(i α t) = Circle.exp(α t). =====
    refine ⟨c.im, fun t => ?_⟩
    apply Circle.ext
    show fχ χ t = ((Circle.exp (c.im * t) : Circle) : ℂ)
    rw [Circle.coe_exp, h_fχ_exp t]
    -- Goal: Complex.exp (c * ↑t) = Complex.exp (↑(c.im * t) * I)
    congr 1
    have hc_eq : c = (c.im : ℂ) * Complex.I := by
      have h := Complex.re_add_im c
      rw [h_re_c] at h
      push_cast at h
      linear_combination -h
    rw [hc_eq]
    push_cast
    ring_nf;
    simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    exact mul_rotate (↑c.im) I ↑t
  -- === UNIQUENESS (cleanly from Part A) ===
  obtain ⟨α, hα⟩ := hexist
  refine ⟨α, hα, fun β hβ => ?_⟩
  by_contra hne
  have hγ : α - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  -- Pick t₀ = π/(α - β). Both formulas for χ(t₀) must agree.
  have heq : Circle.exp (α * (π / (α - β))) = Circle.exp (β * (π / (α - β))) :=
    (hα _).symm.trans (hβ _)
  -- This collapses to Circle.exp π = 1.
  have hπ_one : Circle.exp π = 1 := by
    have hcollapse : Circle.exp ((α - β) * (π / (α - β))) = 1 := by
      rw [show (α - β) * (π / (α - β)) =
            α * (π / (α - β)) + (-(β * (π / (α - β)))) by ring]
      rw [Circle.exp_add, heq, Circle.exp_neg, mul_inv_cancel]
    have hcompute : (α - β) * (π / (α - β)) = π := by field_simp
    rwa [hcompute] at hcollapse
  -- Part A: forces π ∈ 2πℤ, i.e. 1 = 2n for some n ∈ ℤ. Impossible.
  rw [Circle.exp_eq_one_iff_int_mul_two_pi] at hπ_one
  obtain ⟨n, hn⟩ := hπ_one
  have hπ_pos : (0 : ℝ) < π := Real.pi_pos
  have h_eq : (1 : ℝ) = 2 * (n : ℝ) := by
    have h1 : π * 1 = π * (2 * (n : ℝ)) := by
      rw [mul_one, hn]; ring_nf; grind => ring
    exact mul_left_cancel₀ (ne_of_gt hπ_pos) h1
  have h_int : (2 * n : ℤ) = 1 := by exact_mod_cast h_eq.symm
  omega

end Spectra.KMS
