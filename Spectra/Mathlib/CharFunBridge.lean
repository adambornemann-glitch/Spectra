/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
/-!
# Bridge: our Fourier transform of measures = Mathlib's `charFun`

Mathlib (Stiefel–Degenne–Zhu, `MeasureTheory/Measure/CharacteristicFunction/Basic.lean`) now has
`charFun μ t = ∫ x, exp (⟪x, t⟫ * I) ∂μ` together with the uniqueness theorem
`Measure.ext_of_charFun` on complete second-countable inner-product spaces — `ℝ` qualifies, and
on `ℝ` the definition unfolds to exactly our `∫ ω, cexp (I * ω * t) ∂μ`.

This file:

1. `charFun_real` — the translation;
2. `measure_ext_of_fourier` — positive uniqueness, **directly from Mathlib** (this should also
   subsume `Spectra.Fourier.Unique`; see AUDIT.md §1.2);
3. `measure_add_ext_of_fourier`, `measure_sum_ext_of_fourier` — additive rearrangements;
4. `integral_combination_ext` — **the workhorse**: two finite complex combinations of
   (density-weighted) finite positive measures with equal Fourier transforms have equal
   integrals against every bounded measurable function.  This is what turns "equal on
   characters" into "equal on bounded Borel functions", and is the engine behind
   multiplicativity of the Borel functional calculus (no Stone–Weierstrass anywhere).

## Implementation note

Both `signed_combination_ext` and `integral_combination_ext` are corollaries of a single
private engine, `combination_ext_zero_real`: a *one-sided* (`= 0`) combination identity over
an arbitrary `Fintype` index, with bounded measurable **real**-valued densities.  The engine
absorbs the positive/negative parts of each density into `Measure.withDensity` and finishes
with `measure_ext_of_fourier`.  A real *coefficient* is a constant real *density*, so the
signed version is the engine applied over `Fin n ⊕ Fin m` with constant densities; the complex
version reduces to two engine calls (real and imaginary parts) via the `t ↦ -t` conjugation
symmetry of characters, which acts trivially on real densities.

Sorry count: 0.
-/
open Complex MeasureTheory Filter
open scoped RealInnerProductSpace NNReal ENNReal

namespace Spectra.Fourier

/-! ## Basic integrability and symmetry of characters -/

/-- Characters are integrable against any finite measure. -/
lemma integrable_char (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    Integrable (fun ω : ℝ => cexp (I * ω * t)) μ := by
  refine (integrable_const (1 : ℝ)).mono'
    (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable ?_
  filter_upwards with ω
  have h0 : (I * (ω : ℂ) * (t : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  exact le_of_eq (by rw [Complex.norm_exp, h0, Real.exp_zero])

/-- On `ℝ`, Mathlib's `charFun` is our Fourier transform. -/
lemma charFun_real (μ : Measure ℝ) (t : ℝ) :
    charFun μ t = ∫ ω, cexp (I * ω * t) ∂μ := by
  rw [charFun_apply]
  refine integral_congr_ae (.of_forall fun ω => ?_)
  simp [RCLike.inner_apply]; congr 1; ring

/-- Hermitian symmetry: the transform of a (positive) finite measure at `-t` is the conjugate of
its value at `t`.  Restatement of Mathlib's `charFun_neg` in our orientation. -/
lemma fourier_neg_eq_conj (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    (∫ ω, cexp (I * ω * ((-t : ℝ) : ℂ)) ∂μ)
      = starRingEnd ℂ (∫ ω, cexp (I * ω * t) ∂μ) := by
  rw [← charFun_real, ← charFun_real, charFun_neg]

/-! ## Uniqueness, positive and rearranged -/

/-- **Fourier uniqueness for finite positive measures on `ℝ`** — directly from
`Measure.ext_of_charFun`.  Compare with `Spectra.Fourier.Unique`: that file can now in principle
be re-proved by this one-liner. -/
theorem measure_ext_of_fourier {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t : ℝ, ∫ ω, cexp (I * ω * t) ∂μ = ∫ ω, cexp (I * ω * t) ∂ν) :
    μ = ν :=
  Measure.ext_of_charFun <| funext fun t => by
    rw [charFun_real, charFun_real]; exact h t

/-- Uniqueness for differences, without ever forming a signed measure: the standard
`μ₁ − ν₁ = μ₂ − ν₂ ⟺ μ₁ + ν₂ = μ₂ + ν₁` rearrangement. -/
theorem measure_add_ext_of_fourier {μ₁ ν₁ μ₂ ν₂ : Measure ℝ}
    [IsFiniteMeasure μ₁] [IsFiniteMeasure ν₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν₂]
    (h : ∀ t : ℝ,
      (∫ ω, cexp (I * ω * t) ∂μ₁) + ∫ ω, cexp (I * ω * t) ∂ν₂
        = (∫ ω, cexp (I * ω * t) ∂μ₂) + ∫ ω, cexp (I * ω * t) ∂ν₁) :
    μ₁ + ν₂ = μ₂ + ν₁ := by
  refine measure_ext_of_fourier fun t => ?_
  rw [integral_add_measure (integrable_char _ t) (integrable_char _ t),
    integral_add_measure (integrable_char _ t) (integrable_char _ t)]
  exact h t

/-- Finite-sum version: finite families of finite positive measures with equal summed transforms
have equal sums. -/
theorem measure_sum_ext_of_fourier {n m : ℕ}
    {μ : Fin n → Measure ℝ} {ν : Fin m → Measure ℝ}
    [∀ i, IsFiniteMeasure (μ i)] [∀ j, IsFiniteMeasure (ν j)]
    (h : ∀ t : ℝ,
      ∑ i, ∫ ω, cexp (I * ω * t) ∂(μ i) = ∑ j, ∫ ω, cexp (I * ω * t) ∂(ν j)) :
    ∑ i, μ i = ∑ j, ν j := by
  refine measure_ext_of_fourier fun t => ?_
  rw [integral_finsetSum_measure (fun i _ => integrable_char _ t),
    integral_finsetSum_measure (fun j _ => integrable_char _ t)]
  exact h t

/-! ## Helper lemmas for the workhorse -/

/-- Bounded measurable functions are integrable against finite measures. -/
lemma integrable_of_bounded {ρ : Measure ℝ} [IsFiniteMeasure ρ] {F : ℝ → ℂ}
    (hF : Measurable F) {C : ℝ} (hC : ∀ ω, ‖F ω‖ ≤ C) : Integrable F ρ :=
  (integrable_const C).mono' hF.aestronglyMeasurable (Filter.Eventually.of_forall hC)

private lemma measurable_char (t : ℝ) : Measurable fun ω : ℝ => cexp (I * ω * t) :=
  (Complex.continuous_exp.comp (by fun_prop)).measurable

private lemma norm_char_le_one (t ω : ℝ) : ‖cexp (I * ω * t)‖ ≤ 1 := by
  have h0 : (I * (ω : ℂ) * (t : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  exact le_of_eq (by rw [Complex.norm_exp, h0, Real.exp_zero])

/-- `x = x⁺ − x⁻`, as complex numbers. -/
private lemma toNNReal_split (x : ℝ) :
    ((x.toNNReal : ℝ) : ℂ) - (((-x).toNNReal : ℝ) : ℂ) = (x : ℂ) := by
  have h : (x.toNNReal : ℝ) - ((-x).toNNReal : ℝ) = x := by
    rw [Real.coe_toNNReal', Real.coe_toNNReal']
    rcases le_total 0 x with hx | hx
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
    · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx), zero_sub, neg_neg]
  exact_mod_cast h

/-- Pulling a complex constant out of a Bochner integral, multiplicatively. -/
private lemma integral_const_mul' (r : ℂ) (φ : ℝ → ℂ) (ρ : Measure ℝ) :
    ∫ ω, r * φ ω ∂ρ = r * ∫ ω, φ ω ∂ρ := by
  simpa [smul_eq_mul] using integral_smul (μ := ρ) r φ

/-- Conjugating a character times a complex value flips the sign of the frequency. -/
private lemma conj_char_mul (t ω : ℝ) (z : ℂ) :
    (starRingEnd ℂ) (cexp (I * ω * ((-t : ℝ) : ℂ)) * z)
      = cexp (I * ω * (t : ℂ)) * (starRingEnd ℂ) z := by
  have harg : (starRingEnd ℂ) (I * ω * ((-t : ℝ) : ℂ)) = I * ω * (t : ℂ) := by
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg,
      neg_mul, map_neg, conj_ofReal, mul_neg, neg_neg]
  rw [map_mul, ← Complex.exp_conj, harg]

/-- The `t ↦ -t` conjugation symmetry of the transform, with an arbitrary **real**-valued
density (generalizing `fourier_neg_eq_conj`, where the density is `1`).  Conjugation acts
trivially on the density, so no positivity is needed. -/
private lemma conj_integral_char_ofReal (v : ℝ → ℝ) (ρ : Measure ℝ) (t : ℝ) :
    (starRingEnd ℂ) (∫ ω, cexp (I * ω * ((-t : ℝ) : ℂ)) * (v ω : ℂ) ∂ρ)
      = ∫ ω, cexp (I * ω * (t : ℂ)) * (v ω : ℂ) ∂ρ := by
  rw [← integral_conj]
  refine integral_congr_ae (.of_forall fun ω => ?_)
  ring_nf; rw [conj_char_mul, Complex.conj_ofReal]
  exact mul_comm' (cexp (I * ↑ω * ↑t)) ↑(v ω)

/-! ## The engine

A one-sided combination identity over an arbitrary finite index, with bounded measurable
**real**-valued densities.  Proof: absorb the positive and negative parts of each density
into `withDensity` measures `mp x`, `mm x` (finite, positive); the hypothesis becomes
`∑ mp` and `∑ mm` having equal transforms; conclude `∑ mp = ∑ mm` by
`measure_ext_of_fourier` and integrate `g` against both sides. -/

private theorem combination_ext_zero_real {ι : Type*} [Fintype ι]
    (M : ι → Measure ℝ) [∀ x, IsFiniteMeasure (M x)]
    (r : ι → ℝ → ℝ) (hr_meas : ∀ x, Measurable (r x))
    (hr_bdd : ∀ x, ∃ C, ∀ ω, |r x ω| ≤ C)
    (h : ∀ t : ℝ, ∑ x, ∫ ω, cexp (I * ω * t) * (r x ω : ℂ) ∂(M x) = 0)
    {g : ℝ → ℂ} (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) :
    ∑ x, ∫ ω, g ω * (r x ω : ℂ) ∂(M x) = 0 := by
  -- the positive and negative parts of the densities, absorbed into the measures
  set mp : ι → Measure ℝ :=
    fun x => (M x).withDensity fun ω => ((r x ω).toNNReal : ℝ≥0∞) with hmp_def
  set mm : ι → Measure ℝ :=
    fun x => (M x).withDensity fun ω => ((-(r x ω)).toNNReal : ℝ≥0∞) with hmm_def
  -- finiteness of the density measures
  have hfin : ∀ (s : ℝ → ℝ), (∃ C, ∀ ω, |s ω| ≤ C) → ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ],
      IsFiniteMeasure (ρ.withDensity fun ω => ((s ω).toNNReal : ℝ≥0∞)) := by
    intro s hs ρ _
    obtain ⟨C, hC⟩ := hs
    refine isFiniteMeasure_withDensity (ne_of_lt (lt_of_le_of_lt
      (lintegral_mono (g := fun _ => ENNReal.ofReal C) fun ω =>
        ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hC ω))) ?_))
    rw [lintegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  haveI hmp_fin : ∀ x, IsFiniteMeasure (mp x) := fun x => by
    simp only [hmp_def]
    exact hfin (r x) (hr_bdd x) (M x)
  haveI hmm_fin : ∀ x, IsFiniteMeasure (mm x) := fun x => by
    simp only [hmm_def]
    refine hfin (fun ω => -(r x ω)) ?_ (M x)
    obtain ⟨C, hC⟩ := hr_bdd x
    exact ⟨C, fun ω => by rw [abs_neg]; exact hC ω⟩
  -- integrating any bounded measurable function against `r x · M x` splits as `mp x − mm x`
  have hsplit : ∀ (x : ι) (F : ℝ → ℂ), Measurable F → ∀ CF : ℝ, (∀ ω, ‖F ω‖ ≤ CF) →
      ∫ ω, F ω * (r x ω : ℂ) ∂(M x)
        = (∫ ω, F ω ∂(mp x)) - ∫ ω, F ω ∂(mm x) := by
    intro x F hF CF hCF
    obtain ⟨Cr, hCr⟩ := hr_bdd x
    have hCr0 : 0 ≤ Cr := (abs_nonneg _).trans (hCr 0)
    have hint : ∀ (s : ℝ → ℝ), Measurable s → (∀ ω, |s ω| ≤ Cr) →
        Integrable (fun ω => (((s ω).toNNReal : ℝ) : ℂ) * F ω) (M x) := by
      intro s hs hsC
      refine integrable_of_bounded
        ((Complex.measurable_ofReal.comp hs.real_toNNReal.coe_nnreal_real).mul hF)
        (C := Cr * CF) fun ω => ?_
      rw [norm_mul]
      refine mul_le_mul ?_ (hCF ω) (norm_nonneg _) hCr0
      rw [Complex.norm_real, Real.norm_of_nonneg ((s ω).toNNReal.coe_nonneg),
        Real.coe_toNNReal']
      exact max_le ((le_abs_self _).trans (hsC ω)) hCr0
    have hwd : ∀ (s : ℝ → ℝ), Measurable s →
        ∫ ω, F ω ∂((M x).withDensity fun ω => ((s ω).toNNReal : ℝ≥0∞))
          = ∫ ω, (((s ω).toNNReal : ℝ) : ℂ) * F ω ∂(M x) := by
      intro s hs
      rw [integral_withDensity_eq_integral_smul hs.real_toNNReal F]
      refine integral_congr_ae (.of_forall fun ω => ?_)
      simp only [NNReal.smul_def, Complex.real_smul]
    simp only [hmp_def, hmm_def]
    rw [hwd _ (hr_meas x), hwd _ (hr_meas x).neg,
      ← integral_sub (hint _ (hr_meas x) hCr)
        (hint _ (hr_meas x).neg fun ω => by rw [abs_neg]; exact hCr ω)]
    refine integral_congr_ae (.of_forall fun ω => ?_)
    simp only [← sub_mul, toNNReal_split]
    exact mul_comm _ _
  -- the two positive total measures have equal transforms, hence are equal
  have hPQ : (∑ x, mp x) = ∑ x, mm x := by
    refine measure_ext_of_fourier fun t => ?_
    rw [integral_finsetSum_measure (fun x _ => integrable_char _ t),
      integral_finsetSum_measure (fun x _ => integrable_char _ t)]
    have h' := h t
    have hh : ∀ x : ι, ∫ ω, cexp (I * ω * t) * (r x ω : ℂ) ∂(M x)
        = (∫ ω, cexp (I * ω * t) ∂(mp x)) - ∫ ω, cexp (I * ω * t) ∂(mm x) :=
      fun x => hsplit x _ (measurable_char t) 1 (norm_char_le_one t)
    simp only [hh] at h'
    rwa [Finset.sum_sub_distrib, sub_eq_zero] at h'
  -- integrate `g` against both sides and rearrange back
  obtain ⟨C, hC⟩ := hg_bdd
  have hgg : ∀ x : ι, ∫ ω, g ω * (r x ω : ℂ) ∂(M x)
      = (∫ ω, g ω ∂(mp x)) - ∫ ω, g ω ∂(mm x) :=
    fun x => hsplit x g hg_meas C hC
  simp only [hgg]
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  calc ∑ x, ∫ ω, g ω ∂(mp x)
      = ∫ ω, g ω ∂(∑ x, mp x) :=
        (integral_finsetSum_measure fun x _ => integrable_of_bounded hg_meas hC).symm
    _ = ∫ ω, g ω ∂(∑ x, mm x) := by rw [hPQ]
    _ = ∑ x, ∫ ω, g ω ∂(mm x) :=
        integral_finsetSum_measure fun x _ => integrable_of_bounded hg_meas hC

/-! ## The workhorse: real and complex combinations -/

/-- Real-coefficient layer: two real-linear combinations of finite positive measures with equal
Fourier transforms have equal integrals against every bounded measurable `g : ℝ → ℂ`.

Proof: a real coefficient is a constant real density, so this is
`combination_ext_zero_real` over `Fin n ⊕ Fin m` with the `ν`-side coefficients negated. -/
theorem signed_combination_ext {n m : ℕ}
    (a : Fin n → ℝ) (μ : Fin n → Measure ℝ) (b : Fin m → ℝ) (ν : Fin m → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ j, IsFiniteMeasure (ν j)]
    (h : ∀ t : ℝ,
      ∑ i, (a i : ℂ) * ∫ ω, cexp (I * ω * t) ∂(μ i)
        = ∑ j, (b j : ℂ) * ∫ ω, cexp (I * ω * t) ∂(ν j))
    {g : ℝ → ℂ} (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) :
    ∑ i, (a i : ℂ) * ∫ ω, g ω ∂(μ i) = ∑ j, (b j : ℂ) * ∫ ω, g ω ∂(ν j) := by
  set M : Fin n ⊕ Fin m → Measure ℝ := Sum.elim μ ν with hM_def
  set r : Fin n ⊕ Fin m → ℝ → ℝ :=
    Sum.elim (fun i _ => a i) (fun j _ => -(b j)) with hr_def
  haveI hM_fin : ∀ x, IsFiniteMeasure (M x) := by
    rintro (i | j) <;> simp only [hM_def, Sum.elim_inl, Sum.elim_inr] <;> infer_instance
  have hr_meas : ∀ x, Measurable (r x) := by
    rintro (i | j) <;> simp only [hr_def, Sum.elim_inl, Sum.elim_inr] <;>
      exact measurable_const
  have hr_bdd : ∀ x, ∃ C, ∀ ω, |r x ω| ≤ C := by
    rintro (i | j)
    · exact ⟨|a i|, fun ω => le_of_eq (by simp only [hr_def, Sum.elim_inl])⟩
    · exact ⟨|b j|, fun ω => le_of_eq (by simp only [hr_def, Sum.elim_inr, abs_neg])⟩
  -- folding the combined family back into the two stated sums
  have hsum : ∀ F : ℝ → ℂ,
      ∑ x, ∫ ω, F ω * (r x ω : ℂ) ∂(M x)
        = (∑ i, (a i : ℂ) * ∫ ω, F ω ∂(μ i)) - ∑ j, (b j : ℂ) * ∫ ω, F ω ∂(ν j) := by
    intro F
    rw [Fintype.sum_sum_type, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hr_def, hM_def, Sum.elim_inl]
      rw [← integral_const_mul']
      exact integral_congr_ae (.of_forall fun ω => mul_comm _ _)
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hr_def, hM_def, Sum.elim_inr]
      rw [← integral_const_mul', ← integral_neg]
      refine integral_congr_ae (.of_forall fun ω => ?_)
      push_cast
      ring
  have key := combination_ext_zero_real M r hr_meas hr_bdd
    (fun t => by rw [hsum (fun ω => cexp (I * ω * t)), h t, sub_self]) hg_meas hg_bdd
  rw [hsum g] at key
  exact sub_eq_zero.mp key

/-- **The workhorse.**  Two finite *complex* combinations of density-weighted finite positive
measures with equal Fourier transforms have equal integrals against every bounded measurable
function.  The densities `f i`, `k j` (bounded measurable, complex-valued) are what later let the
keystone lemma compare `∫ g dμ_{ξ, U(t)η}` with `∫ e^{itλ} g(λ) dμ_{ξ,η}` without ever
constructing a complex measure object.

Proof: fold coefficients and densities into a single signed complex density family `h` over
`Fin n ⊕ Fin m`; split `h = re h + I · im h` pointwise; evaluating the hypothesis at `t` and
`-t` and conjugating (conjugation flips only the character, since `re h`, `im h` are real)
isolates the real- and imaginary-part identities, each killed by
`combination_ext_zero_real`; recombine. -/
theorem integral_combination_ext {n m : ℕ}
    (c : Fin n → ℂ) (μ : Fin n → Measure ℝ) (f : Fin n → ℝ → ℂ)
    (d : Fin m → ℂ) (ν : Fin m → Measure ℝ) (k : Fin m → ℝ → ℂ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ j, IsFiniteMeasure (ν j)]
    (hf_meas : ∀ i, Measurable (f i)) (hf_bdd : ∀ i, ∃ C, ∀ ω, ‖f i ω‖ ≤ C)
    (hk_meas : ∀ j, Measurable (k j)) (hk_bdd : ∀ j, ∃ C, ∀ ω, ‖k j ω‖ ≤ C)
    (heq : ∀ t : ℝ,
      ∑ i, c i * ∫ ω, cexp (I * ω * t) * f i ω ∂(μ i)
        = ∑ j, d j * ∫ ω, cexp (I * ω * t) * k j ω ∂(ν j))
    {g : ℝ → ℂ} (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) :
    ∑ i, c i * ∫ ω, g ω * f i ω ∂(μ i) = ∑ j, d j * ∫ ω, g ω * k j ω ∂(ν j) := by
  -- combine both sides into one family over `Fin n ⊕ Fin m`, with signed complex densities
  set M : Fin n ⊕ Fin m → Measure ℝ := Sum.elim μ ν with hM_def
  set h : Fin n ⊕ Fin m → ℝ → ℂ :=
    Sum.elim (fun i ω => c i * f i ω) (fun j ω => -(d j * k j ω)) with hh_def
  haveI hM_fin : ∀ x, IsFiniteMeasure (M x) := by
    rintro (i | j) <;> simp only [hM_def, Sum.elim_inl, Sum.elim_inr] <;> infer_instance
  have hh_meas : ∀ x, Measurable (h x) := by
    rintro (i | j)
    · simpa only [hh_def, Sum.elim_inl] using (hf_meas i).const_mul (c i)
    · simpa only [hh_def, Sum.elim_inr] using ((hk_meas j).const_mul (d j)).neg
  have hh_bdd : ∀ x, ∃ C, ∀ ω, ‖h x ω‖ ≤ C := by
    rintro (i | j)
    · obtain ⟨C, hC⟩ := hf_bdd i
      refine ⟨‖c i‖ * C, fun ω => ?_⟩
      simp only [hh_def, Sum.elim_inl]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC ω) (norm_nonneg _)
    · obtain ⟨C, hC⟩ := hk_bdd j
      refine ⟨‖d j‖ * C, fun ω => ?_⟩
      simp only [hh_def, Sum.elim_inr]
      rw [norm_neg, norm_mul]
      exact mul_le_mul_of_nonneg_left (hC ω) (norm_nonneg _)
  -- folding the combined family back into the two stated sums (no integrability needed)
  have hsum : ∀ F : ℝ → ℂ,
      ∑ x, ∫ ω, F ω * h x ω ∂(M x)
        = (∑ i, c i * ∫ ω, F ω * f i ω ∂(μ i))
          - ∑ j, d j * ∫ ω, F ω * k j ω ∂(ν j) := by
    intro F
    rw [Fintype.sum_sum_type, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hh_def, hM_def, Sum.elim_inl]
      rw [← integral_const_mul']
      exact integral_congr_ae (.of_forall fun ω => by ring)
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hh_def, hM_def, Sum.elim_inr]
      rw [← integral_const_mul', ← integral_neg]
      exact integral_congr_ae (.of_forall fun ω => by ring)
  -- the hypothesis, in one-sided combined form
  have SA : ∀ t : ℝ, ∑ x, ∫ ω, cexp (I * ω * t) * h x ω ∂(M x) = 0 := fun t => by
    rw [hsum (fun ω => cexp (I * ω * t)), heq t, sub_self]
  -- splitting the density into real and imaginary parts, under the integral
  have hreim : ∀ (x : Fin n ⊕ Fin m) (F : ℝ → ℂ), Measurable F →
      ∀ CF : ℝ, (∀ ω, ‖F ω‖ ≤ CF) →
      ∫ ω, F ω * h x ω ∂(M x)
        = (∫ ω, F ω * ((h x ω).re : ℂ) ∂(M x))
          + I * ∫ ω, F ω * ((h x ω).im : ℂ) ∂(M x) := by
    intro x F hF CF hCF
    obtain ⟨Ch, hCh⟩ := hh_bdd x
    have hint : ∀ (v : ℝ → ℝ), Measurable v → (∀ ω, |v ω| ≤ Ch) →
        Integrable (fun ω => F ω * ((v ω : ℝ) : ℂ)) (M x) := by
      intro v hv hvC
      refine integrable_of_bounded (hF.mul (Complex.measurable_ofReal.comp hv))
        (C := CF * Ch) fun ω => ?_
      rw [norm_mul]
      refine mul_le_mul (hCF ω) ?_ (norm_nonneg _) ((norm_nonneg (F 0)).trans (hCF 0))
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hvC ω
    erw [← integral_const_mul',
      ← integral_add
        (hint _ (Complex.measurable_re.comp (hh_meas x))
          (fun ω => (Complex.abs_re_le_norm _).trans (hCh ω)))
        ((hint _ (Complex.measurable_im.comp (hh_meas x))
          (fun ω => (Complex.abs_im_le_norm _).trans (hCh ω))).const_mul I)]
    refine integral_congr_ae (.of_forall fun ω => ?_)
    have expand : ∀ w F0 : ℂ, F0 * w = F0 * (w.re : ℂ) + I * (F0 * (w.im : ℂ)) := by
      intro w F0
      conv_lhs => rw [← Complex.re_add_im w]
      ring
    exact expand (h x ω) (F ω)
  have hsum_reim : ∀ (F : ℝ → ℂ), Measurable F → ∀ CF : ℝ, (∀ ω, ‖F ω‖ ≤ CF) →
      ∑ x, ∫ ω, F ω * h x ω ∂(M x)
        = (∑ x, ∫ ω, F ω * ((h x ω).re : ℂ) ∂(M x))
          + I * ∑ x, ∫ ω, F ω * ((h x ω).im : ℂ) ∂(M x) := by
    intro F hF CF hCF
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => hreim x F hF CF hCF
  -- the split hypothesis: (Re part) + I · (Im part) = 0
  have hB1 : ∀ t : ℝ,
      (∑ x, ∫ ω, cexp (I * ω * t) * ((h x ω).re : ℂ) ∂(M x))
        + I * ∑ x, ∫ ω, cexp (I * ω * t) * ((h x ω).im : ℂ) ∂(M x) = 0 := fun t => by
    rw [← hsum_reim (fun ω => cexp (I * ω * t)) (measurable_char t) 1 (norm_char_le_one t)]
    exact SA t
  have hconjsum : ∀ (v : Fin n ⊕ Fin m → ℝ → ℝ) (t : ℝ),
      ∑ x, (starRingEnd ℂ) (∫ ω, cexp (I * ω * ((-t : ℝ) : ℂ)) * (v x ω : ℂ) ∂(M x))
        = ∑ x, ∫ ω, cexp (I * ω * (t : ℂ)) * (v x ω : ℂ) ∂(M x) :=
    fun v t => Finset.sum_congr rfl fun x _ => conj_integral_char_ofReal (v x) (M x) t
  -- the `t ↦ -t` conjugation trick isolates the real and imaginary parts
  have hRe : ∀ t : ℝ,
      ∑ x, ∫ ω, cexp (I * ω * t) * ((h x ω).re : ℂ) ∂(M x) = 0 := by
    intro t
    have e1 := hB1 t
    have e2 := congrArg (starRingEnd ℂ) (hB1 (-t))
    rw [map_zero, map_add, map_mul, Complex.conj_I, map_sum, map_sum,
      hconjsum (fun x ω => (h x ω).re) t, hconjsum (fun x ω => (h x ω).im) t] at e2
    linear_combination (e1 + e2) / 2
  have hIm : ∀ t : ℝ,
      ∑ x, ∫ ω, cexp (I * ω * t) * ((h x ω).im : ℂ) ∂(M x) = 0 := by
    intro t
    have e1 := hB1 t
    have e2 := congrArg (starRingEnd ℂ) (hB1 (-t))
    rw [map_zero, map_add, map_mul, Complex.conj_I, map_sum, map_sum,
      hconjsum (fun x ω => (h x ω).re) t, hconjsum (fun x ω => (h x ω).im) t] at e2
    have h2 : (2 : ℂ) * I
        * ∑ x, ∫ ω, cexp (I * ω * t) * ((h x ω).im : ℂ) ∂(M x) = 0 := by
      linear_combination e1 - e2
    rcases mul_eq_zero.mp h2 with h0 | h0
    · exact absurd h0 (mul_ne_zero two_ne_zero Complex.I_ne_zero)
    · exact h0
  -- two engine calls, one per part
  have hRe0 :=
    combination_ext_zero_real M (fun x ω => (h x ω).re)
      (fun x => Complex.measurable_re.comp (hh_meas x))
      (fun x => by
        obtain ⟨C, hC⟩ := hh_bdd x
        exact ⟨C, fun ω => (Complex.abs_re_le_norm _).trans (hC ω)⟩)
      hRe hg_meas hg_bdd
  have hIm0 :=
    combination_ext_zero_real M (fun x ω => (h x ω).im)
      (fun x => Complex.measurable_im.comp (hh_meas x))
      (fun x => by
        obtain ⟨C, hC⟩ := hh_bdd x
        exact ⟨C, fun ω => (Complex.abs_im_le_norm _).trans (hC ω)⟩)
      hIm hg_meas hg_bdd
  -- recombine and unfold the `Sum.elim` packaging
  obtain ⟨Cg, hCg⟩ := hg_bdd
  have hg0 : ∑ x, ∫ ω, g ω * h x ω ∂(M x) = 0 := by
    rw [hsum_reim g hg_meas Cg hCg, hRe0, hIm0, mul_zero, add_zero]
  have hgoal := hsum g
  rw [hg0] at hgoal
  exact sub_eq_zero.mp hgoal.symm

/-- Specialization with trivial densities: equal complex combinations of plain transforms give
equal combinations of integrals.  (The form most proofs will actually invoke.) -/
theorem integral_combination_ext' {n m : ℕ}
    (c : Fin n → ℂ) (μ : Fin n → Measure ℝ) (d : Fin m → ℂ) (ν : Fin m → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ j, IsFiniteMeasure (ν j)]
    (heq : ∀ t : ℝ,
      ∑ i, c i * ∫ ω, cexp (I * ω * t) ∂(μ i)
        = ∑ j, d j * ∫ ω, cexp (I * ω * t) ∂(ν j))
    {g : ℝ → ℂ} (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) :
    ∑ i, c i * ∫ ω, g ω ∂(μ i) = ∑ j, d j * ∫ ω, g ω ∂(ν j) := by
  have h := integral_combination_ext c μ (fun _ _ => 1) d ν (fun _ _ => 1)
    (fun _ => measurable_const) (fun _ => ⟨1, fun _ => by simp⟩)
    (fun _ => measurable_const) (fun _ => ⟨1, fun _ => by simp⟩)
    (by simpa using heq) hg_meas hg_bdd
  simpa using h

end Spectra.Fourier
