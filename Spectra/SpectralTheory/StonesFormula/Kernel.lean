/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: ResolventTheory/Kernel.lean
-/
import Spectra.SpectralTheory.PositiveDefinite
import Spectra.SpectralTheory.BochnerTheorem.Fourier
import Spectra.SpectralTheory.CayleyTransform.Unitary
import Spectra.SpectralTheory.ScalarMeasure.Herglotz.FejerMeasure
import Spectra.UnitaryEvolution.BochnerIntegration.Domain
import Spectra.UnitaryEvolution.Resolvent.Analytic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Data.Rat.Defs
/-!
# Resolvent Kernel Analysis

This file develops the analytical properties of the resolvent kernel `(s - z)⁻¹`
and the associated Lorentzian approximation to the delta function.

## Main definitions

* `offRealPoint`: Helper to construct `t + iε` as an `OffRealAxis` point
* `offRealPointNeg`: Helper to construct `t - iε` as an `OffRealAxis` point
* `resolvent_integrand`: The kernel `(s - z)⁻¹`

## Main statements

### Resolvent kernel
* `resolvent_integrand_bound`: `|(s - z)⁻¹| ≤ 1/|Im(z)|` for all `s ∈ ℝ`
* `resolvent_kernel_im`: `Im((s - (t + iε))⁻¹) = ε/((s-t)² + ε²)`
* `resolvent_kernel_diff`: `(s - (t+iε))⁻¹ - (s - (t-iε))⁻¹ = 2iε/((s-t)² + ε²)`

### Lorentzian kernel
* `lorentzian_nonneg`: The Lorentzian is non-negative
* `lorentzian_bound`: The Lorentzian is bounded by `1/ε`
* `lorentzian_total_integral`: `∫ ε/((s-t)² + ε²) ds = π` (axiom)
* `lorentzian_concentration`: Lorentzian concentrates at `t` as `ε → 0` (axiom)
* `lorentzian_approx_delta`: `(1/π) · ε/((s-t)² + ε²) → δ(s-t)` as `ε → 0`

### Arctan integration
* `lorentzian_arctan_integral`: `∫_a^b ε/((s-t)² + ε²) dt = arctan(...) - arctan(...)`
* `arctan_indicator_limit`: The arctan kernel converges to the indicator function
* `arctan_kernel_bound`: The arctan kernel is uniformly bounded by 1

## Physical interpretation

The Lorentzian kernel `ε/((s-t)² + ε²)` is the imaginary part of the resolvent
kernel at `z = t + iε`. As `ε → 0`, it becomes an approximation to the delta
function `δ(s-t)`, which is the key to extracting spectral information from
the resolvent.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VII
* Stone, "Linear Transformations in Hilbert Space" (1932)

## Tags

resolvent, Lorentzian, approximate identity, Poisson kernel
-/
namespace SpectralBridge.Resolvent

open Complex MeasureTheory Filter Topology TopologicalSpace
open QuantumMechanics.SpectralTheory QuantumMechanics.Bochner.FourierUniqueness
open scoped NNReal ENNReal InnerProductSpace
/-! ### Off-real axis points -/

/-- A complex number with non-zero imaginary part. -/
structure OffRealAxis where
  val : ℂ
  im_ne_zero : val.im ≠ 0

/-- Construct `t + iε` as an off-real point. -/
def offRealPoint (t : ℝ) (ε : ℝ) (hε : ε > 0) : QuantumMechanics.Resolvent.OffRealAxis :=
  ⟨↑t + ↑ε * I, by simp [Complex.add_im]; exact ne_of_gt hε⟩

/-- Construct `t - iε` as an off-real point. -/
def offRealPointNeg (t : ℝ) (ε : ℝ) (hε : ε > 0) : QuantumMechanics.Resolvent.OffRealAxis :=
  ⟨↑t - ↑ε * I, by simp [Complex.sub_im]; exact ne_of_gt hε⟩

/-! ### Resolvent kernel -/

/-- The resolvent integrand `(s - z)⁻¹`. -/
noncomputable def resolvent_integrand (z : ℂ) : ℝ → ℂ :=
  fun s => ((s : ℂ) - z)⁻¹

/-- The resolvent integrand is bounded by `1/|Im(z)|`.

This is the key estimate: for `z` off the real axis, the kernel `(s - z)⁻¹`
is uniformly bounded in `s ∈ ℝ`, with bound depending only on `|Im(z)|`. -/
lemma resolvent_integrand_bound (z : ℂ) (hz : z.im ≠ 0) (s : ℝ) :
    ‖((s : ℂ) - z)⁻¹‖ ≤ 1 / |z.im| := by
  have h_im : ((s : ℂ) - z).im = -z.im := by simp
  have h_norm_ge : ‖(s : ℂ) - z‖ ≥ |z.im| := by
    calc ‖(s : ℂ) - z‖
        ≥ |((s : ℂ) - z).im| := Complex.abs_im_le_norm _
      _ = |-z.im| := by rw [h_im]
      _ = |z.im| := abs_neg _
  have h_pos : |z.im| > 0 := abs_pos.mpr hz
  calc ‖((s : ℂ) - z)⁻¹‖
      = 1 / ‖(s : ℂ) - z‖ := by rw [norm_inv]; simp only [one_div]
    _ ≤ 1 / |z.im| := by
        apply div_le_div_of_nonneg_left (by norm_num) h_pos h_norm_ge

/-! ### Lorentzian kernel -/

/-- Imaginary part of resolvent kernel: `Im((s - z)⁻¹) = ε/((s-t)² + ε²)` for `z = t + iε`.

This shows that the imaginary part of the resolvent kernel is exactly the
Lorentzian (Cauchy/Poisson) kernel, which is an approximation to the delta function. -/
lemma resolvent_kernel_im (s t ε : ℝ) (hε : ε > 0) :
    (((s : ℂ) - (↑t + ↑ε * I))⁻¹).im = ε / ((s - t)^2 + ε^2) := by
  have h_denom_ne : ((s - t : ℝ)^2 + ε^2 : ℂ) ≠ 0 := by
    have h : (s - t)^2 + ε^2 > 0 := by positivity
    exact_mod_cast h.ne'

  have h_diff : (s : ℂ) - (↑t + ↑ε * I) = (s - t : ℝ) - ε * I := by
    simp only [Complex.ofReal_sub]
    ring

  rw [h_diff]
  -- ((s-t) - εi)⁻¹ = ((s-t) + εi) / ((s-t)² + ε²)
  have h_conj : ((s - t : ℝ) - ε * I)⁻¹ =
      ((s - t : ℝ) + ε * I) / ((s - t)^2 + ε^2 : ℂ) := by
    have h_mul : ((s - t : ℝ) - ε * I) * ((s - t : ℝ) + ε * I) =
        ((s - t)^2 + ε^2 : ℂ) := by
      push_cast
      have hI2 : (I : ℂ)^2 = -1 := Complex.I_sq
      linear_combination (norm := ring) -ε^2 * hI2
    have h_conj_ne : (↑(s - t) : ℂ) + ↑ε * I ≠ 0 := by
      intro h
      have : ε = 0 := by simpa using congrArg Complex.im h
      linarith
    rw [← h_mul]
    field_simp [h_conj_ne]

  rw [h_conj]
  have h_real : ((s - t)^2 + ε^2 : ℂ) = ((s - t)^2 + ε^2 : ℝ) := by push_cast; ring
  rw [h_real, Complex.div_ofReal_im]
  simp [Complex.add_im, Complex.mul_im]

/-- The Lorentzian kernel is non-negative. -/
lemma lorentzian_nonneg (s t ε : ℝ) (hε : ε > 0) :
    0 ≤ ε / ((s - t)^2 + ε^2) := by
  apply div_nonneg (le_of_lt hε)
  positivity

/-- The Lorentzian kernel is bounded by `1/ε`. -/
lemma lorentzian_bound (s t ε : ℝ) (hε : ε > 0) :
    ε / ((s - t)^2 + ε^2) ≤ 1 / ε := by
  have h_denom : ε^2 ≤ (s - t)^2 + ε^2 := by linarith [sq_nonneg (s - t)]
  have h1 : ε / ((s - t)^2 + ε^2) ≤ ε / ε^2 :=
    div_le_div_of_nonneg_left (le_of_lt hε) (sq_pos_of_pos hε) h_denom
  simp only [one_div]
  calc ε / ((s - t)^2 + ε^2) ≤ ε / ε^2 := h1
    _ = ε⁻¹ := by field_simp


/-- The Lorentzian integrates to π over ℝ.

This is equivalent to the residue theorem for `∫ 1/(x² + 1) dx = π`. -/
lemma lorentzian_total_integral (t ε : ℝ) (hε : ε > 0) :
    ∫ s, ε / ((s - t)^2 + ε^2) = Real.pi := by
  -- Translate: ∫ f(s - t) ds = ∫ f(u) du
  have h_shift : ∫ s, ε / ((s - t) ^ 2 + ε ^ 2) = ∫ u, ε / (u ^ 2 + ε ^ 2) :=
    integral_sub_right_eq_self (fun u => ε / (u ^ 2 + ε ^ 2)) t
  rw [h_shift]
  -- Factor: ε/(u² + ε²) = π * poissonKernel ε u
  open QuantumMechanics.Bochner.FourierUniqueness in
  have h_eq : (fun u : ℝ => ε / (u ^ 2 + ε ^ 2)) =
      fun u => Real.pi * poissonKernel ε u := by
    ext u; unfold poissonKernel; field_simp
  open QuantumMechanics.Bochner.FourierUniqueness in
  rw [h_eq, MeasureTheory.integral_const_mul, poissonKernel_integral_eq_one hε, mul_one]




/-! ### Arctan integration -/

/-- Arctan antiderivative for the Lorentzian kernel.

`∫_a^b ε/((s-t)² + ε²) dt = arctan((b-s)/ε) - arctan((a-s)/ε)`

This is obtained by the substitution `u = (t-s)/ε`. -/
lemma lorentzian_arctan_integral (s a b ε : ℝ) (hε : ε > 0) :
    ∫ t in a..b, ε / ((s - t)^2 + ε^2) =
      Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε) := by
  have hε_ne : ε ≠ 0 := ne_of_gt hε
  let F : ℝ → ℝ := fun t => Real.arctan ((t - s) / ε)
  suffices h : ∫ t in a..b, ε / ((s - t)^2 + ε^2) = F b - F a by
    simp only [F] at h; exact h
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  -- HasDerivAt on uIcc
  · intro t _
    have hg : HasDerivAt (fun t => (t - s) / ε) (1 / ε) t := by
      simpa using ((hasDerivAt_id t).sub (hasDerivAt_const t s)).div_const ε
    have hchain := (Real.hasDerivAt_arctan ((t - s) / ε)).comp t hg
    convert hchain using 1
    have : (s - t) ^ 2 + ε ^ 2 > 0 := by positivity
    have : 1 + ((t - s) / ε) ^ 2 > 0 := by positivity
    field_simp
    ring
  -- IntervalIntegrable
  · apply Continuous.intervalIntegrable
    apply continuous_const.div
    · exact ((continuous_const.sub continuous_id).pow 2).add continuous_const
    · intro t; positivity



/-- The arctan kernel converges to the indicator function away from endpoints.

For `s ∉ {a, b}`,
`(1/π)[arctan((b-s)/ε) - arctan((a-s)/ε)] → 𝟙_{(a,b]}(s)` as `ε → 0+`

At the endpoints `s = a` and `s = b` the limit is `1/2`, not `0` or `1`,
which is the source of the averaged endpoint terms in Stone's formula.

This is because `arctan(x) → π/2` as `x → +∞` and `arctan(x) → -π/2` as `x → -∞`. -/
lemma arctan_indicator_limit (a b s : ℝ) (hab : a < b)
    (hs_a : s ≠ a) (hs_b : s ≠ b) :
    Tendsto (fun ε : ℝ => (1 / Real.pi) *
      (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)))
      (𝓝[>] 0)
      (𝓝 (Set.indicator (Set.Ioc a b) 1 s)) := by
  have hπ_pos := Real.pi_pos
  -- Step 1: c/ε → +∞ as ε → 0+ when c > 0
  have div_atTop : ∀ c : ℝ, 0 < c →
      Tendsto (fun ε : ℝ => c / ε) (𝓝[>] 0) atTop := by
    intro c hc
    simp_rw [div_eq_mul_inv, mul_comm c]
    exact tendsto_inv_nhdsGT_zero.atTop_mul_const hc
  -- Step 2: c/ε → -∞ when c < 0
  have div_atBot : ∀ c : ℝ, c < 0 →
      Tendsto (fun ε : ℝ => c / ε) (𝓝[>] 0) atBot := by
    intro c hc
    have key : (fun ε : ℝ => c / ε) = (fun ε => -((-c) / ε)) := by ext; simp [neg_div]
    rw [key]
    exact tendsto_neg_atTop_atBot.comp (div_atTop (-c) (neg_pos.mpr hc))
  -- Step 3: arctan limit compositions
  have lim_pos : ∀ c : ℝ, 0 < c →
      Tendsto (fun ε : ℝ => Real.arctan (c / ε)) (𝓝[>] 0) (𝓝 (Real.pi / 2)) :=
    fun c hc => (Real.tendsto_arctan_atTop.comp (div_atTop c hc)).mono_right nhdsWithin_le_nhds
  have lim_neg : ∀ c : ℝ, c < 0 →
      Tendsto (fun ε : ℝ => Real.arctan (c / ε)) (𝓝[>] 0) (𝓝 (-(Real.pi / 2))) :=
    fun c hc => (Real.tendsto_arctan_atBot.comp (div_atBot c hc)).mono_right nhdsWithin_le_nhds
  -- Step 4: case analysis on s
  rcases lt_or_gt_of_ne hs_a with hsa | hsa
  · -- s < a: both (b-s), (a-s) > 0 → both arctans → π/2 → difference → 0
    have hmem : s ∉ Set.Ioc a b := fun h => absurd h.1 (not_lt.mpr (le_of_lt hsa))
    simp only [Set.indicator_apply, if_neg hmem, Pi.one_apply]
    have h1 := (lim_pos _ (by aesop)).sub (lim_pos _ (by aesop))
    simp only [sub_self] at h1
    have h2 := (tendsto_const_nhds (x := 1 / Real.pi)).mul h1
    exact QuantumMechanics.Bochner.FourierUniqueness.arctanRecovery_tendsto_zero_of_lt' hsa hab
  · rcases lt_or_gt_of_ne hs_b with hsb | hsb
    · -- a < s < b: (b-s) > 0 → π/2, (a-s) < 0 → -π/2, difference → π
      have hmem : s ∈ Set.Ioc a b := ⟨hsa, le_of_lt hsb⟩
      simp only [Set.indicator_of_mem hmem, Pi.one_apply]
      have hbs : 0 < b - s := by linarith
      have has : a - s < 0 := by linarith
      have h1 := (lim_pos _ hbs).sub (lim_neg _ has)
      simp only [sub_neg_eq_add, add_halves] at h1
      have h2 := (tendsto_const_nhds (x := 1 / Real.pi)).mul h1
      simpa [div_mul_cancel₀] using h2
    · -- s > b: both (b-s), (a-s) < 0 → both arctans → -π/2 → difference → 0
      have hmem : s ∉ Set.Ioc a b := fun h => absurd h.2 (not_le.mpr hsb)
      simp only [Set.indicator_apply, if_neg hmem, Pi.one_apply]
      have hbs : b - s < 0 := by linarith
      have has : a - s < 0 := by linarith [hab]
      have h1 := (lim_neg _ hbs).sub (lim_neg _ has)
      simp only [sub_self] at h1
      have h2 := (tendsto_const_nhds (x := 1 / Real.pi)).mul h1
      simpa [mul_zero] using h2

/-- The arctan kernel is uniformly bounded by 1.

Since `|arctan(x)| ≤ π/2` for all `x`, the difference is at most `π`. -/
lemma arctan_kernel_bound (a b s ε : ℝ) (_hε : ε > 0) :
    |(1 / Real.pi) * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε))| ≤ 1 := by
  have hπ_pos := Real.pi_pos
  have h_diff : |Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)| ≤ Real.pi := by
    rw [abs_le]
    constructor <;>
      linarith [Real.neg_pi_div_two_lt_arctan ((b - s) / ε),
        Real.arctan_lt_pi_div_two ((b - s) / ε),
        Real.neg_pi_div_two_lt_arctan ((a - s) / ε),
        Real.arctan_lt_pi_div_two ((a - s) / ε)]
  rw [abs_mul, abs_of_pos (by positivity)]
  calc (1 / Real.pi) * |Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)|
      ≤ (1 / Real.pi) * Real.pi := by apply mul_le_mul_of_nonneg_left h_diff; positivity
    _ = 1 := by field_simp


/-- The Lorentzian concentrates near `t` as `ε → 0`.

For any `δ > 0`, the integral outside `(t-δ, t+δ)` vanishes as `ε → 0+`. -/
lemma lorentzian_concentration (t δ : ℝ) (hδ : δ > 0) :
    Tendsto (fun ε : ℝ => ∫ s in Set.Iic (t - δ) ∪ Set.Ici (t + δ),
      ε / ((s - t)^2 + ε^2)) (𝓝[>] 0) (𝓝 0) := by
  -- Integrability for each ε > 0
  have h_int : ∀ ε : ℝ, 0 < ε → Integrable (fun s => ε / ((s - t)^2 + ε^2)) := by
    intro ε hε
    open QuantumMechanics.Bochner.FourierUniqueness in
    have h_eq : (fun s => ε / ((s - t)^2 + ε^2)) =
        fun s => Real.pi * poissonKernel ε (s - t) := by
      ext s; simp only [poissonKernel]; field_simp
    rw [h_eq]
    exact ((poissonKernel_integrable hε).comp_sub_right t).const_mul _
  -- Complement identity
  have h_compl : (Set.Iic (t - δ) ∪ Set.Ici (t + δ))ᶜ = Set.Ioo (t - δ) (t + δ) := by
    ext s; simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_Iic, Set.mem_Ici,
      Set.mem_Ioo, not_or, not_le]
  -- Tail = π - interval integral
  have h_tail_eq : ∀ ε > 0,
      ∫ s in Set.Iic (t - δ) ∪ Set.Ici (t + δ), ε / ((s - t)^2 + ε^2) =
      Real.pi - ∫ s in (t - δ)..(t + δ), ε / ((s - t)^2 + ε^2) := by
    intro ε hε
    have h_split := integral_add_compl
      (s := Set.Iic (t - δ) ∪ Set.Ici (t + δ))
      (measurableSet_Iic.union measurableSet_Ici) (h_int ε hε)
    rw [lorentzian_total_integral t ε hε, h_compl] at h_split
    -- Ioo and Ioc agree a.e. for Lebesgue measure
    have h_ioo_interval : ∫ s in Set.Ioo (t - δ) (t + δ), ε / ((s - t) ^ 2 + ε ^ 2) =
        ∫ s in (t - δ)..(t + δ), ε / ((s - t) ^ 2 + ε ^ 2) := by
      rw [intervalIntegral.integral_of_le (by linarith : t - δ ≤ t + δ)]
      exact Eq.symm integral_Ioc_eq_integral_Ioo
    linarith
  -- Near integral via arctan
  have h_near_val : ∀ ε > 0,
      ∫ s in (t - δ)..(t + δ), ε / ((s - t)^2 + ε^2) =
      Real.arctan (δ / ε) - Real.arctan (-δ / ε) := by
    intro ε hε
    simp_rw [show ∀ s, (s - t) ^ 2 + ε ^ 2 = (t - s) ^ 2 + ε ^ 2 from by intro s; ring]
    rw [lorentzian_arctan_integral t (t - δ) (t + δ) ε hε]
    congr 1 <;> ring_nf
  -- Arctan limit → π
  have h_lim : Tendsto (fun ε => Real.arctan (δ / ε) - Real.arctan (-δ / ε))
      (𝓝[>] 0) (𝓝 Real.pi) := by
    simp_rw [neg_div, Real.arctan_neg, sub_neg_eq_add, ← two_mul]
    rw [show Real.pi = 2 * (Real.pi / 2) from by ring]
    exact (tendsto_const_nhds (x := (2 : ℝ))).mul
      ((Real.tendsto_arctan_atTop.comp (by
        exact tendsto_pos_div_zero_atTop hδ)).mono_right nhdsWithin_le_nhds)
  -- Combine: tail = π - arctan → π - π = 0
  have h_tail_tendsto : Tendsto (fun ε =>
      Real.pi - (Real.arctan (δ / ε) - Real.arctan (-δ / ε)))
      (𝓝[>] 0) (𝓝 0) := by
    have := (tendsto_const_nhds (f := 𝓝[>] (0 : ℝ)) (x := Real.pi)).sub h_lim
    simp only [sub_self] at this
    exact this
  exact h_tail_tendsto.congr' (by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have h1 := h_tail_eq ε hε
    have h2 := h_near_val ε hε
    linarith)


/-! ### Resolvent kernel difference -/

/-- Key identity: difference of resolvent kernels at conjugate points.

`(s - (t + iε))⁻¹ - (s - (t - iε))⁻¹ = 2iε / ((s-t)² + ε²)`

This shows the resolvent difference is purely imaginary and proportional to the Lorentzian.
This identity is the basis for Stone's formula. -/
lemma resolvent_kernel_diff (s t ε : ℝ) (hε : ε > 0) :
    ((s : ℂ) - (↑t + ↑ε * I))⁻¹ - ((s : ℂ) - (↑t - ↑ε * I))⁻¹ =
    (2 * ε * I) / ((s - t)^2 + ε^2 : ℂ) := by

  have h_z_plus : (↑t + ↑ε * I : ℂ) - (↑t - ↑ε * I) = 2 * ε * I := by ring
  have h_denom : ((s : ℂ) - (↑t + ↑ε * I)) * ((s : ℂ) - (↑t - ↑ε * I)) =
      ((s - t)^2 + ε^2 : ℂ) := by
    have hI2 : (I : ℂ)^2 = -1 := Complex.I_sq
    linear_combination (norm := ring) -ε^2 * hI2
  have h_denom_ne : ((s - t : ℝ)^2 + ε^2 : ℂ) ≠ 0 := by
    have h : (s - t)^2 + ε^2 > 0 := by positivity
    exact_mod_cast h.ne'
  have h_prod_ne : ((s : ℂ) - (↑t + ↑ε * I)) * ((s : ℂ) - (↑t - ↑ε * I)) ≠ 0 := by
    rw [h_denom]
    push_cast at h_denom_ne ⊢
    exact h_denom_ne
  have h_left_ne : (s : ℂ) - (↑t + ↑ε * I) ≠ 0 := by
    intro h
    apply h_prod_ne
    rw [h, zero_mul]
  have h_right_ne : (s : ℂ) - (↑t - ↑ε * I) ≠ 0 := by
    intro h
    apply h_prod_ne
    rw [h, mul_zero]
  -- Main calculation
  have h_denom_ne' : (↑s - ↑t : ℂ) ^ 2 + ↑ε ^ 2 ≠ 0 := by
    have h : (s - t)^2 + ε^2 > 0 := by positivity
    exact_mod_cast h.ne'
  field_simp [h_left_ne, h_right_ne, h_denom_ne']
  push_cast [sq]
  ring_nf
  simp only [I_pow_three, mul_neg, neg_mul, sub_neg_eq_add]

/-- Normalized resolvent difference equals the Lorentzian kernel.
    This is the kernel-level form of Stone's formula. -/
lemma resolvent_kernel_diff_normalized (s t ε : ℝ) (hε : ε > 0) :
    (1 / (2 * Real.pi * I)) *
      (((s : ℂ) - (↑t + ↑ε * I))⁻¹ - ((s : ℂ) - (↑t - ↑ε * I))⁻¹) =
    ↑(ε / ((s - t)^2 + ε^2) / Real.pi) := by
  rw [resolvent_kernel_diff s t ε hε]
  have hπ : (Real.pi : ℝ) ≠ 0 := Real.pi_pos.ne'
  have h_denom : (s - t) ^ 2 + ε ^ 2 > 0 := by positivity
  push_cast
  field_simp

/-- The Lorentzian kernel smeared against an integrable function is integrable.
    This is the basic integrability input for Stone's formula and the
    resolvent functional calculus: if `f ∈ L¹(ℝ)` then `s ↦ ε/((s-t)²+ε²) · f(s)` is in `L¹(ℝ)`,
    with the bound `‖K·f‖_{L¹} ≤ (1/ε)‖f‖_{L¹}` following from `lorentzian_bound`. -/
lemma lorentzian_smul_integrable (f : ℝ → ℂ) (hf_int : Integrable f)
    (t : ℝ) (ε : ℝ) (hε : ε > 0) :
    Integrable (fun s => (ε / ((s - t)^2 + ε^2)) • f s) := by
  have h_rw : ∀ s, (ε / ((s - t)^2 + ε^2)) • f s =
      (Complex.ofReal (ε / ((s - t)^2 + ε^2))) * f s :=
    fun s => by exact real_smul
  simp_rw [h_rw]
  apply Integrable.mono' (hf_int.norm.const_mul (1 / ε))
  -- timing out
  · have h_denom_ne : ∀ s : ℝ, (s - t) ^ 2 + ε ^ 2 ≠ 0 :=
      fun s => ne_of_gt (by positivity)
    have h_cont : Continuous (fun s => Complex.ofReal (ε / ((s - t) ^ 2 + ε ^ 2))) :=
      Complex.continuous_ofReal.comp
        (continuous_const.div
          ((continuous_id.sub continuous_const).pow 2 |>.add continuous_const)
          h_denom_ne)
    exact h_cont.aestronglyMeasurable.mul hf_int.aestronglyMeasurable
  · filter_upwards with s
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (lorentzian_nonneg s t ε hε)]
    exact mul_le_mul_of_nonneg_right (lorentzian_bound s t ε hε) (norm_nonneg _)


/-- The Lorentzian is an approximation to the delta function.

`(1/π) · ε/((s-t)² + ε²) → δ(s-t)` as `ε → 0+` in the sense that
`(1/π) ∫ ε/((s-t)² + ε²) f(s) ds → f(t)` for continuous integrable `f`. -/
lemma lorentzian_approx_delta (f : ℝ → ℂ) (hf_cont : Continuous f)
    (hf_int : Integrable f) (t : ℝ) :
    Tendsto (fun ε : ℝ => (1 / Real.pi) • ∫ s, (ε / ((s - t)^2 + ε^2)) • f s)
            (𝓝[>] 0) (𝓝 (f t)) := by
  -- ═══ Setup: define normalized kernel K ═══
  let K : ℝ → ℝ → ℝ := fun ε s => (1 / Real.pi) * (ε / ((s - t)^2 + ε^2))
  -- Rewrite goal in terms of K (same as your existing h_rewrite)
  suffices h : Tendsto (fun ε => ∫ s, (K ε s) • f s) (𝓝[>] 0) (𝓝 (f t)) by
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [K]
    rw [show (fun s => (1 / Real.pi * (ε / ((s - t) ^ 2 + ε ^ 2))) • f s) =
         (fun s => (1 / Real.pi) • (ε / ((s - t) ^ 2 + ε ^ 2)) • f s) from by
      ext s; exact (smul_smul _ _ _).symm]
    exact (integral_smul (1 / Real.pi) _)
  -- ═══ Key properties of K ═══
  have hK_nonneg : ∀ ε > 0, ∀ s, 0 ≤ K ε s :=
    fun ε hε s => mul_nonneg (by positivity) (lorentzian_nonneg s t ε hε)
  have hK_total : ∀ ε > 0, ∫ s, K ε s = 1 := by
    intro ε hε
    simp only [K]
    rw [integral_const_mul, lorentzian_total_integral t ε hε]; field_simp
  -- ═══ Pointwise far-field decay: K(ε,s) ≤ ε/(πδ²) when |s-t| ≥ δ ═══
  have hK_far_ptwise : ∀ δ > 0, ∀ ε > 0, ∀ s, |s - t| ≥ δ →
      K ε s ≤ ε / (Real.pi * δ^2) := by
    intro δ hδ ε hε s hs
    simp only [K]
    -- On |s-t| ≥ δ: (s-t)² + ε² ≥ δ², so ε/((s-t)²+ε²) ≤ ε/δ²
    have h_denom : δ^2 ≤ (s - t)^2 + ε^2 := by nlinarith [sq_abs (s - t)]
    have h_lor : ε / ((s - t)^2 + ε^2) ≤ ε / δ^2 :=
      div_le_div_of_nonneg_left hε.le (by positivity) h_denom
    calc (1 / Real.pi) * (ε / ((s - t)^2 + ε^2))
        ≤ (1 / Real.pi) * (ε / δ^2) := by apply mul_le_mul_of_nonneg_left h_lor; positivity
      _ = ε / (Real.pi * δ^2) := by ring
  -- ═══ Main proof: Metric.tendsto ═══
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro η hη
  -- Step 0: Choose δ by continuity of f at t
  have hf_cont_t := hf_cont.continuousAt (x := t)
  rw [Metric.continuousAt_iff] at hf_cont_t
  obtain ⟨δ, hδ, hδ_close⟩ := hf_cont_t (η / 3) (by positivity)
  -- Step 1: Choose ε₁ so that |f(t)| · ∫_far K < η/3
  -- This uses lorentzian_concentration
  have h_conc := lorentzian_concentration t δ hδ
  -- We need: ∫_far K ε s ds → 0, which follows from lorentzian_concentration
  -- after multiplying by 1/π. Then |f(t)| · ∫_far K < η/3 eventually.
  obtain ⟨ε₁, hε₁_pos, hε₁⟩ : ∃ ε₁ > 0, ∀ ε, 0 < ε → ε < ε₁ →
      ‖f t‖ * ∫ s in Set.Iic (t - δ) ∪ Set.Ici (t + δ), K ε s < η / 3 := by
    -- K tail integral → 0
    have hK_conc : Tendsto (fun ε => ∫ s in Set.Iic (t - δ) ∪ Set.Ici (t + δ), K ε s)
        (𝓝[>] 0) (𝓝 0) := by
      simp only [K]
      simp_rw [integral_const_mul]
      have := (tendsto_const_nhds (f := 𝓝[>] (0 : ℝ)) (x := 1 / Real.pi)).mul
        (lorentzian_concentration t δ hδ)
      simp only [mul_zero] at this
      exact this
    -- ‖f t‖ * tail → 0
    have h_prod : Tendsto (fun ε => ‖f t‖ *
        ∫ s in Set.Iic (t - δ) ∪ Set.Ici (t + δ), K ε s)
        (𝓝[>] 0) (𝓝 0) := by
      have := (tendsto_const_nhds (f := 𝓝[>] (0 : ℝ)) (x := ‖f t‖)).mul hK_conc
      simp only [mul_zero] at this
      exact this
    -- Extract ε₁ from Tendsto
    rw [Metric.tendsto_nhdsWithin_nhds] at h_prod
    obtain ⟨ε₁, hε₁_pos, hε₁_spec⟩ := h_prod (η / 3) (by positivity)
    refine ⟨ε₁, hε₁_pos, fun ε hε hε_lt => ?_⟩
    have h := hε₁_spec hε (by rwa [Real.dist_eq, sub_zero, abs_of_pos hε])
    rw [Real.dist_eq, sub_zero] at h
    exact lt_of_le_of_lt (le_abs_self _) h
  -- Step 2: Choose ε₂ so that (ε/(πδ²)) · ‖f‖_{L¹} < η/3
  -- This is the Von Neumann observation: pointwise decay controls ∫_far K|f|
  have hf_norm_int : Integrable (fun s => ‖f s‖) := hf_int.norm
  let C := ∫ s, ‖f s‖
  obtain ⟨ε₂, hε₂_pos, hε₂⟩ : ∃ ε₂ > 0, ∀ ε, 0 < ε → ε < ε₂ →
      ε / (Real.pi * δ^2) * C < η / 3 := by
    have hC_nonneg : 0 ≤ C := integral_nonneg (fun s => norm_nonneg (f s))
    have hπδ_pos : 0 < Real.pi * δ ^ 2 := by positivity
    have hC1_pos : 0 < C + 1 := by linarith
    refine ⟨η * Real.pi * δ ^ 2 / (3 * (C + 1)), by positivity, fun ε hε hε_lt => ?_⟩
    have key : ε * (3 * (C + 1)) < η * Real.pi * δ ^ 2 := by
      rwa [lt_div_iff₀ (by positivity : (0 : ℝ) < 3 * (C + 1))] at hε_lt
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ hπδ_pos (by positivity : (0 : ℝ) < 3)]
    nlinarith
  -- Step 3: Combine. For ε < min(ε₁, ε₂), the error < η.
  refine ⟨min ε₁ ε₂, lt_min hε₁_pos hε₂_pos, fun ε hε_pos hε_small => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos hε_pos] at hε_small
  have hε₁' := hε₁ ε hε_pos (lt_of_lt_of_le hε_small (min_le_left _ _))
  have hε₂' := hε₂ ε hε_pos (lt_of_lt_of_le hε_small (min_le_right _ _))
  -- ═══ The 3ε decomposition ═══
  -- ═══ Integrability helpers ═══
  have hK_int : Integrable (fun s => K ε s) := by
    have : (fun s => K ε s) = fun s => poissonKernel ε (s - t) := by
      ext s; simp only [K, poissonKernel]
    rw [this]
    exact (poissonKernel_integrable hε_pos).comp_sub_right t
  have hKf_int : Integrable (fun s => (K ε s) • f s) := by
    -- Rewrite ℝ-smul as ℂ-multiplication
    have h_rw : (fun s => (K ε s) • f s) = fun s => (↑(K ε s) : ℂ) * f s := by
      ext s; exact real_smul
    rw [h_rw]
    -- K is bounded by 1/(πε), so |↑(K s)| · |f s| ≤ (1/(πε)) · |f s|
    apply Integrable.mono' (hf_int.norm.const_mul (1 / (Real.pi * ε)))
    · exact (Complex.continuous_ofReal.comp
        ((poissonKernel_continuous hε_pos).comp (continuous_id.sub continuous_const))
        |>.aestronglyMeasurable.mul hf_int.aestronglyMeasurable)
    · filter_upwards with s
      simp [Real.norm_eq_abs, abs_of_nonneg (hK_nonneg ε hε_pos s)]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simp only [K]
      calc (1 / Real.pi) * (ε / ((s - t) ^ 2 + ε ^ 2))
          ≤ (1 / Real.pi) * (1 / ε) := by
            apply mul_le_mul_of_nonneg_left (lorentzian_bound s t ε hε_pos); positivity
        _ = 1 / (Real.pi * ε) := by field_simp
      simp only [one_div, mul_inv_rev, Std.le_refl]
  have hKft_int : Integrable (fun s => (K ε s) • f t) :=
    hK_int.smul_const (f t)
  -- ═══ Centering: ∫ K•f - f(t) = ∫ K•(f - f(t)) ═══
  have h_center : (∫ s, (K ε s) • f s) - f t = ∫ s, (K ε s) • (f s - f t) := by
    have h1 : ∫ s, (K ε s) • f t = f t := by
      trans (∫ s, K ε s) • f t
      · exact integral_smul_const (fun s => K ε s) (f t)
      · rw [hK_total ε hε_pos]; simp only [real_smul, ofReal_one, one_mul]
    rw [show (fun s => (K ε s) • (f s - f t)) = fun s => (K ε s) • f s - (K ε s) • f t from
      by ext s; exact smul_sub _ _ _]
    rw [integral_sub hKf_int hKft_int, h1]
  -- ═══ Integrability of K•(f - ft) ═══
  have hKff_int : Integrable (fun s => (K ε s) • (f s - f t)) := by
    rw [show (fun s => (K ε s) • (f s - f t)) = fun s => (K ε s) • f s - (K ε s) • f t from
      by ext s; exact smul_sub _ _ _]
    exact hKf_int.sub hKft_int
  -- ═══ Near/far sets ═══
  let near := Set.Ioo (t - δ) (t + δ)
  let far := Set.Iic (t - δ) ∪ Set.Ici (t + δ)
  have hfar_meas : MeasurableSet far := measurableSet_Iic.union measurableSet_Ici
  have hfar_compl : farᶜ = near := by
    simp only [far, near]; ext s
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_Iic, Set.mem_Ici,
      Set.mem_Ioo, not_or, not_le]
  -- ═══ Near contribution ═══
  have h_near : ‖∫ s in near, (K ε s) • (f s - f t)‖ ≤ η / 3 := by
    calc ‖∫ s in near, (K ε s) • (f s - f t)‖
        ≤ ∫ s in near, ‖(K ε s) • (f s - f t)‖ := norm_integral_le_integral_norm _
      _ = ∫ s in near, K ε s * ‖f s - f t‖ := by
          congr 1; ext s
          rw [Complex.real_smul, norm_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg (hK_nonneg ε hε_pos s)]
      _ ≤ ∫ s in near, K ε s * (η / 3) := by
          apply setIntegral_mono_on
          · have : (fun x => K ε x * ‖f x - f t‖) = fun x => ‖(K ε x) • (f x - f t)‖ := by
              ext s; rw [Complex.real_smul, norm_mul, Complex.norm_real,
                         Real.norm_eq_abs, abs_of_nonneg (hK_nonneg ε hε_pos s)]
            rw [this]
            exact hKff_int.norm.restrict
          · exact (hK_int.restrict).mul_const _
          · measurability
          · intro s hs
            apply mul_le_mul_of_nonneg_left _ (hK_nonneg ε hε_pos s)
            have : dist s t < δ := by
              simp only [near, Set.mem_Ioo] at hs
              rw [Real.dist_eq]; exact abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
            exact le_of_lt (by rw [← dist_eq_norm]; exact hδ_close this)
      _ = (η / 3) * ∫ s in near, K ε s := by rw [@integral_mul_const]; ring
      _ ≤ (η / 3) * ∫ s, K ε s := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact setIntegral_le_integral hK_int (Eventually.of_forall (hK_nonneg ε hε_pos))
      _ = η / 3 := by rw [hK_total ε hε_pos, mul_one]
  -- ═══ Far contribution ═══
  have h_far : ‖∫ s in far, (K ε s) • (f s - f t)‖ < 2 * η / 3 := by
    calc ‖∫ s in far, (K ε s) • (f s - f t)‖
        ≤ ‖∫ s in far, (K ε s) • f s‖ + ‖∫ s in far, (K ε s) • f t‖ := by
          rw [show (fun s => (K ε s) • (f s - f t)) = fun s => (K ε s) • f s - (K ε s) • f t from
            by ext s; exact smul_sub _ _ _]
          rw [integral_sub hKf_int.restrict hKft_int.restrict]
          exact norm_sub_le _ _
      _ < η / 3 + η / 3 := by
          apply add_lt_add
          -- ‖∫_far K•f‖ ≤ ∫_far K‖f‖ ≤ (ε/(πδ²)) · C < η/3
          · calc ‖∫ s in far, (K ε s) • f s‖
                ≤ ∫ s in far, K ε s * ‖f s‖ := by
                    calc ‖∫ s in far, (K ε s) • f s‖
                        ≤ ∫ s in far, ‖(K ε s) • f s‖ := norm_integral_le_integral_norm _
                      _ = ∫ s in far, K ε s * ‖f s‖ := by
                          congr 1; ext s
                          rw [Complex.real_smul, norm_mul, Complex.norm_real,
                              Real.norm_eq_abs, abs_of_nonneg (hK_nonneg ε hε_pos s)]
              _ ≤ ∫ s in far, (ε / (Real.pi * δ ^ 2)) * ‖f s‖ := by
                    apply setIntegral_mono_on
                    · have : (fun x => K ε x * ‖f x‖) = fun x => ‖(K ε x) • f x‖ := by
                        ext s; rw [Complex.real_smul, norm_mul, Complex.norm_real,
                                   Real.norm_eq_abs, abs_of_nonneg (hK_nonneg ε hε_pos s)]
                      rw [this]
                      exact hKf_int.norm.restrict
                    · exact (hf_norm_int.const_mul _).restrict
                    · exact hfar_meas
                    · intro s hs
                      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
                      apply hK_far_ptwise δ hδ ε hε_pos s
                      rcases hs with h | h
                      · exact le_abs.mpr (Or.inr (by linarith [Set.mem_Iic.mp h]))
                      · exact le_abs.mpr (Or.inl (by linarith [Set.mem_Ici.mp h]))
              _ = ε / (Real.pi * δ ^ 2) * ∫ s in far, ‖f s‖ :=
                    integral_const_mul _ _
              _ ≤ ε / (Real.pi * δ ^ 2) * C := by
                    apply mul_le_mul_of_nonneg_left _
                      (div_nonneg hε_pos.le (mul_pos Real.pi_pos (sq_pos_of_pos hδ)).le)
                    exact setIntegral_le_integral hf_norm_int
                      (Eventually.of_forall (fun s => norm_nonneg (f s)))
              _ < η / 3 := hε₂'
          -- ‖(∫_far K)•f(t)‖ = ‖f(t)‖ · ∫_far K < η/3
          · have h_smul : ∫ s in far, (K ε s) • f t = (∫ s in far, K ε s) • f t :=
              integral_smul_const (μ := volume.restrict far) (fun s => K ε s) (f t)
            rw [h_smul, Complex.real_smul, norm_mul, Complex.norm_real,
                mul_comm, Real.norm_eq_abs,
                abs_of_nonneg (setIntegral_nonneg hfar_meas (fun s _ => hK_nonneg ε hε_pos s))]
            exact hε₁'
      _ = 2 * η / 3 := by ring
  -- ═══ Assembly ═══
  calc dist (∫ s, (K ε s) • f s) (f t)
      = ‖(∫ s, (K ε s) • f s) - f t‖ := dist_eq_norm _ _
    _ = ‖∫ s, (K ε s) • (f s - f t)‖ := by congr 1
    _ = ‖(∫ s in near, (K ε s) • (f s - f t)) + ∫ s in far, (K ε s) • (f s - f t)‖ := by
        rw [← hfar_compl]
        rw [← integral_add_compl hfar_meas hKff_int]
        congr 1; ring
    _ ≤ ‖∫ s in near, (K ε s) • (f s - f t)‖ + ‖∫ s in far, (K ε s) • (f s - f t)‖ :=
        norm_add_le _ _
    _ < η / 3 + 2 * η / 3 := add_lt_add_of_le_of_lt h_near h_far
    _ = η := by ring

end SpectralBridge.Resolvent
