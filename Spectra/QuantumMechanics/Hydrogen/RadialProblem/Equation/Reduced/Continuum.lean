/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Equation.Reduced.Quantization

/-!
# Reduced Radial Continuum Exclusion

The nonnegative-energy reduced radial equation has no nonzero square-integrable
classical solutions. This is the reduced and unreduced continuum exclusion used by
the hydrogen spectrum development.

## Main definitions

This file introduces only private potential and ODE-energy auxiliaries.

## Main statements

* `reduced_radial_continuum` — nonnegative-energy reduced `L²` solutions vanish.
* `radial_continuum` — no nonzero classical radial `L²` solutions exist for `E ≥ 0`.

## References

* [Schrödinger, *Quantisierung als Eigenwertproblem I*][schrodinger1926]
* [Griffiths, *Introduction to Quantum Mechanics*][griffiths2018], §4.2.
-/

open MeasureTheory Complex Filter Real
open scoped Topology NNReal ENNReal Nat
open Spectra.QuantumMechanics.Hydrogen.Radial
open Spectra.Kummer

namespace QuantumMechanics.Hydrogen.RadialEq

/-! ### Non-existence of `L²` solutions at `E ≥ 0` (continuous spectrum)

Elementary energy/Grönwall machinery for `reduced_radial_continuum`: the potential
`W = ℓ(ℓ+1)/r² − 2/r − 2E` is eventually negative and increasing, the energy
`χ'² − Wχ²` controls the solution, and an `L²` solution is forced to vanish. -/

/-- The reduced-radial potential at energy `E`: `W(r) = ℓ(ℓ+1)/r² − 2/r − 2E`. -/
private noncomputable def contW (ℓ : ℕ) (E : ℝ) : ℝ → ℝ :=
  fun r => (ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r - 2 * E

/-- Derivative of the reduced-radial potential: for `r > 0`,
`W'(r) = −2ℓ(ℓ+1)/r³ + 2/r²`. -/
private lemma contW_hasDerivAt (ℓ : ℕ) (E : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (contW ℓ E)
      (-2 * (ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 3 + 2 / r ^ 2) r := by
  have hr2 : (r : ℝ) ^ 2 ≠ 0 := by positivity
  have hrne : r ≠ 0 := ne_of_gt hr
  have h1 : HasDerivAt (fun s : ℝ => (ℓ : ℝ) * ((ℓ : ℝ) + 1) / s ^ 2)
      (((0 : ℝ) * r ^ 2 - (ℓ : ℝ) * ((ℓ : ℝ) + 1) * (2 * r ^ (2 - 1))) / (r ^ 2) ^ 2) r :=
    (hasDerivAt_const r ((ℓ : ℝ) * ((ℓ : ℝ) + 1))).div (hasDerivAt_pow 2 r) hr2
  have h2 : HasDerivAt (fun s : ℝ => 2 / s)
      (((0 : ℝ) * r - 2 * 1) / r ^ 2) r :=
    (hasDerivAt_const r (2 : ℝ)).div (hasDerivAt_id r) hrne
  have h3 : HasDerivAt (fun _ : ℝ => 2 * E) 0 r := hasDerivAt_const r _
  have hsum := (h1.sub h2).sub h3
  convert hsum using 1
  field_simp
  ring

/-- Threshold facts: for `r ≥ ℓ(ℓ+1)+1` (and `E ≥ 0`) the potential is negative with
`−W ≥ 1/r` and increasing (`W' ≥ 0`). -/
private lemma contW_thresh (ℓ : ℕ) (E : ℝ) (hE : 0 ≤ E) {r : ℝ}
    (hr : (ℓ : ℝ) * ((ℓ : ℝ) + 1) + 1 ≤ r) :
    0 < r ∧ 1 / r ≤ -contW ℓ E r ∧ contW ℓ E r < 0 ∧
      0 ≤ -2 * (ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 3 + 2 / r ^ 2 := by
  have hℓ : (0 : ℝ) ≤ (ℓ : ℝ) * ((ℓ : ℝ) + 1) := by positivity
  have hr0 : 0 < r := by nlinarith
  have hrge : (ℓ : ℝ) * ((ℓ : ℝ) + 1) < r := by nlinarith
  -- ℓ(ℓ+1)/r² ≤ 1/r  (since ℓ(ℓ+1) < r)
  have hkey : (ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 ≤ 1 / r := by
    rw [← sub_nonneg, show (1 : ℝ) / r - (ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2
      = (r - (ℓ : ℝ) * ((ℓ : ℝ) + 1)) / r ^ 2 from by field_simp]
    apply div_nonneg _ (by positivity)
    linarith [hrge]
  have hW : -contW ℓ E r = 2 / r + 2 * E - (ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 := by
    simp only [contW]; ring
  have h2E : (0 : ℝ) ≤ 2 * E := by linarith
  have e1 : (2 : ℝ) / r = 2 * (1 / r) := by ring
  have h1r : (0 : ℝ) < 1 / r := by positivity
  refine ⟨hr0, ?_, ?_, ?_⟩
  · rw [hW]; linarith [hkey, h2E, e1, h1r]
  · rw [show contW ℓ E r = -(-contW ℓ E r) from by ring, hW]; linarith [hkey, h2E, e1, h1r]
  · -- W' = 2/r² − 2ℓ(ℓ+1)/r³ ≥ 0
    have h3 : (0 : ℝ) < r ^ 3 := by positivity
    rw [show -2 * (ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 3 + 2 / r ^ 2
        = (2 * (r - (ℓ : ℝ) * ((ℓ : ℝ) + 1))) / r ^ 3 from by field_simp; ring]
    apply div_nonneg _ (le_of_lt h3)
    nlinarith [hrge]

/-- **Energy differential inequality.** With `G = χ'² − Wχ²`, on `[r₀,∞)`
(`r₀ ≥ ℓ(ℓ+1)+1`) `G` is decreasing and `G/(−W)` is increasing
(`G'(−W) + GW' = W'χ'² ≥ 0`), giving the
cross-multiplied lower bound `G(r₀)·(−W r) ≤ G(r)·(−W r₀)`. -/
private lemma energy_diff_ineq (ℓ : ℕ) (E : ℝ) (hE : 0 ≤ E) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    (hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r - 2 * E) * χ r)
    {r₀ : ℝ} (hr₀R : (ℓ : ℝ) * ((ℓ : ℝ) + 1) + 1 ≤ r₀) :
    (∀ r, r₀ ≤ r → (deriv χ r) ^ 2 - contW ℓ E r * (χ r) ^ 2
        ≤ (deriv χ r₀) ^ 2 - contW ℓ E r₀ * (χ r₀) ^ 2)
    ∧ (∀ r, r₀ ≤ r →
        ((deriv χ r₀) ^ 2 - contW ℓ E r₀ * (χ r₀) ^ 2) * (-contW ℓ E r)
          ≤ ((deriv χ r) ^ 2 - contW ℓ E r * (χ r) ^ 2) * (-contW ℓ E r₀)) := by
  have hr₀pos : 0 < r₀ := (contW_thresh ℓ E hE hr₀R).1
  set G : ℝ → ℝ := fun r => (deriv χ r) ^ 2 - contW ℓ E r * (χ r) ^ 2 with hGdef
  set Wd : ℝ → ℝ := fun x => -2 * (ℓ : ℝ) * ((ℓ : ℝ) + 1) / x ^ 3 + 2 / x ^ 2 with _hWddef
  have hpos : ∀ x, r₀ ≤ x → 0 < x := fun x hx => lt_of_lt_of_le hr₀pos hx
  have hWdnn : ∀ x, r₀ ≤ x → 0 ≤ Wd x := fun x hx => (contW_thresh ℓ E hE (le_trans hr₀R hx)).2.2.2
  have hWneg : ∀ x, r₀ ≤ x → contW ℓ E x < 0 :=
    fun x hx => (contW_thresh ℓ E hE (le_trans hr₀R hx)).2.2.1
  have hGderiv : ∀ x, 0 < x → HasDerivAt G (-(Wd x) * (χ x) ^ 2) x := by
    intro x hx
    have h1 : HasDerivAt (fun s => deriv χ s ^ 2) (2 * deriv χ x * deriv^[2] χ x) x := by
      have h := (hχ2 x hx).mul (hχ2 x hx)
      rw [show (fun s => deriv χ s ^ 2) = (fun s => deriv χ s * deriv χ s) from by
        funext s; rw [pow_two]]
      convert h using 1; ring
    have hp : HasDerivAt (fun s => χ s ^ 2) (2 * χ x * deriv χ x) x := by
      have h := (hχ1 x hx).mul (hχ1 x hx)
      rw [show (fun s => χ s ^ 2) = (fun s => χ s * χ s) from by funext s; rw [pow_two]]
      convert h using 1; ring
    have h2 : HasDerivAt (fun s => contW ℓ E s * (χ s) ^ 2)
        (Wd x * (χ x) ^ 2 + contW ℓ E x * (2 * χ x * deriv χ x)) x :=
      (contW_hasDerivAt ℓ E hx).mul hp
    have hG := h1.sub h2
    convert hG using 1
    rw [hode x hx, show contW ℓ E x = (ℓ : ℝ) * ((ℓ : ℝ) + 1) / x ^ 2 - 2 / x - 2 * E from rfl]
    ring
  have hWc : ContinuousOn (contW ℓ E) (Set.Ici r₀) :=
    fun x hx => (contW_hasDerivAt ℓ E (hpos x hx)).continuousAt.continuousWithinAt
  have hχc : ContinuousOn χ (Set.Ici r₀) :=
    fun x hx => (hχ1 x (hpos x hx)).continuousAt.continuousWithinAt
  have hdχc : ContinuousOn (deriv χ) (Set.Ici r₀) :=
    fun x hx => (hχ2 x (hpos x hx)).continuousAt.continuousWithinAt
  have hGc : ContinuousOn G (Set.Ici r₀) := (hdχc.pow 2).sub (hWc.mul (hχc.pow 2))
  have hGdiff : DifferentiableOn ℝ G (interior (Set.Ici r₀)) := by
    rw [interior_Ici]
    exact fun x hx => (hGderiv x (lt_trans hr₀pos hx)).differentiableAt.differentiableWithinAt
  have hGdec : AntitoneOn G (Set.Ici r₀) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici r₀) hGc hGdiff
    intro x hx
    rw [interior_Ici] at hx
    rw [(hGderiv x (lt_trans hr₀pos hx)).deriv]
    nlinarith [sq_nonneg (χ x), hWdnn x (le_of_lt hx)]
  set H : ℝ → ℝ := fun s => G s / (-contW ℓ E s) with hHdef
  have hDne : ∀ x, r₀ ≤ x → -contW ℓ E x ≠ 0 := fun x hx => by have := hWneg x hx; linarith
  have hHc : ContinuousOn H (Set.Ici r₀) := hGc.div hWc.neg (fun x hx => hDne x hx)
  have hHderiv : ∀ x, r₀ ≤ x → HasDerivAt H
      ((-(Wd x) * (χ x) ^ 2 * (-contW ℓ E x) - G x * (-(Wd x))) / (-contW ℓ E x) ^ 2) x :=
    fun x hx => (hGderiv x (hpos x hx)).div ((contW_hasDerivAt ℓ E (hpos x hx)).neg) (hDne x hx)
  have hHdiff : DifferentiableOn ℝ H (interior (Set.Ici r₀)) := by
    rw [interior_Ici]
    exact fun x hx => (hHderiv x (le_of_lt hx)).differentiableAt.differentiableWithinAt
  have hHinc : MonotoneOn H (Set.Ici r₀) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici r₀) hHc hHdiff
    intro x hx
    rw [interior_Ici] at hx
    rw [(hHderiv x (le_of_lt hx)).deriv]
    apply div_nonneg _ (sq_nonneg _)
    rw [show -(Wd x) * (χ x) ^ 2 * (-contW ℓ E x) - G x * (-(Wd x)) = Wd x * (deriv χ x) ^ 2 from by
      rw [hGdef]; ring]
    exact mul_nonneg (hWdnn x (le_of_lt hx)) (sq_nonneg _)
  refine ⟨fun r hr => hGdec Set.self_mem_Ici (Set.mem_Ici.2 hr) hr, fun r hr => ?_⟩
  have hHle : H r₀ ≤ H r := hHinc Set.self_mem_Ici (Set.mem_Ici.2 hr) hr
  simp only [hHdef] at hHle
  have hD0 : 0 < -contW ℓ E r₀ := by have := hWneg r₀ (le_refl r₀); linarith
  have hDr : 0 < -contW ℓ E r := by have := hWneg r hr; linarith
  have hD0ne : (-contW ℓ E r₀) ≠ 0 := hD0.ne'
  have hDrne : (-contW ℓ E r) ≠ 0 := hDr.ne'
  have hmul := mul_le_mul_of_nonneg_right hHle (le_of_lt (mul_pos hD0 hDr))
  have key0 : G r₀ / (-contW ℓ E r₀) * (-contW ℓ E r₀ * -contW ℓ E r) = G r₀ * -contW ℓ E r := by
    rw [← mul_assoc, div_mul_cancel₀ _ hD0ne]
  have key1 : G r / (-contW ℓ E r) * (-contW ℓ E r₀ * -contW ℓ E r) = G r * -contW ℓ E r₀ := by
    rw [mul_comm (-contW ℓ E r₀) (-contW ℓ E r), ← mul_assoc, div_mul_cancel₀ _ hDrne]
  rw [key0, key1] at hmul
  exact hmul

/-- A function that is `L²` on `(a,∞)` and Lipschitz there tends to `0` at `+∞`.
Small-tail argument: if `|f r₀| ≥ ε` then `|f| ≥ ε/2` on `[r₀, r₀+δ]`, contributing
`(ε/2)²δ` to the integral — but the tail past a large `T₁` is smaller. -/
private lemma l2_tendsto_zero {f : ℝ → ℝ} {a B : ℝ} (hB : 0 ≤ B)
    (hlip : ∀ x y, a ≤ x → a ≤ y → |f x - f y| ≤ B * |x - y|)
    (hint : IntegrableOn (fun r => f r ^ 2) (Set.Ioi a)) :
    Filter.Tendsto f Filter.atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have _hBp : (0 : ℝ) < B + 1 := by linarith
  set δ := ε / (2 * (B + 1)) with hδdef
  have hδpos : 0 < δ := by positivity
  have hδeq : ε = 2 * (B * δ) + 2 * δ := by rw [hδdef]; field_simp
  have htail : Filter.Tendsto (fun T => ∫ x in Set.Ioi T, f x ^ 2) Filter.atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero (f := fun r => f r ^ 2) (b := id) tendsto_id
  have hcpos : (0 : ℝ) < (ε / 2) ^ 2 * δ := by positivity
  obtain ⟨T₁, hT₁tail, hT₁a⟩ :=
    ((htail.eventually (gt_mem_nhds hcpos)).and (eventually_ge_atTop a)).exists
  refine ⟨T₁ + 1, fun r hr => ?_⟩
  rw [Real.dist_eq, sub_zero]
  by_contra hcon
  have hcon' : ε ≤ |f r| := not_lt.1 hcon
  have hrT₁ : T₁ < r := by linarith
  have hra : a ≤ r := le_trans hT₁a (by linarith)
  have hBδ : B * δ ≤ ε / 2 := by linarith [hδeq, hδpos]
  have hlb_pt : ∀ s ∈ Set.Ioc r (r + δ), (ε / 2) ^ 2 ≤ f s ^ 2 := by
    intro s hs
    have hsa : a ≤ s := le_trans hra (le_of_lt hs.1)
    have hsr : |r - s| ≤ δ := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hs.1])]; linarith [hs.2]
    have h2 : |f r - f s| ≤ B * δ :=
      le_trans (hlip r s hra hsa) (le_trans (mul_le_mul_of_nonneg_left hsr hB) (le_refl _))
    have h1 : |f r| - |f s| ≤ |f r - f s| := abs_sub_abs_le_abs_sub (f r) (f s)
    have hfs : ε / 2 ≤ |f s| := by linarith [h1, h2, hBδ, hcon']
    have : (ε / 2) ^ 2 ≤ |f s| ^ 2 := pow_le_pow_left₀ (by positivity) hfs 2
    rwa [sq_abs] at this
  have hintIoc : IntegrableOn (fun r => f r ^ 2) (Set.Ioc r (r + δ)) :=
    hint.mono_set (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi hra))
  have hlb : (ε / 2) ^ 2 * δ ≤ ∫ x in Set.Ioc r (r + δ), f x ^ 2 := by
    have hconst : ∫ _x in Set.Ioc r (r + δ), ((ε / 2) ^ 2 : ℝ) = (ε / 2) ^ 2 * δ := by
      rw [setIntegral_const, volume_real_Ioc_of_le (by linarith : r ≤ r + δ), smul_eq_mul]; ring
    have hci : IntegrableOn (fun _x : ℝ => ((ε / 2) ^ 2 : ℝ)) (Set.Ioc r (r + δ)) :=
      integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    rw [← hconst]
    exact setIntegral_mono_on hci hintIoc measurableSet_Ioc hlb_pt
  have hintIoiT : IntegrableOn (fun r => f r ^ 2) (Set.Ioi T₁) :=
    hint.mono_set (Set.Ioi_subset_Ioi hT₁a)
  have hub : (∫ x in Set.Ioc r (r + δ), f x ^ 2) ≤ ∫ x in Set.Ioi T₁, f x ^ 2 := by
    apply setIntegral_mono_set hintIoiT (Filter.Eventually.of_forall (fun x => sq_nonneg _))
    exact (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi hrT₁.le)).eventuallyLE
  linarith [hlb, hub, hT₁tail]

/-- **Forward uniqueness** for `u'' = V u` with zero Cauchy data at the left endpoint:
Grönwall on the system `(u, u')`, needing only the norm bound
`‖(u', Vu)‖ ≤ (M+1)‖(u,u')‖`. -/
private lemma forward_zero {u du V : ℝ → ℝ} {a b : ℝ} (_hab : a ≤ b)
    (hu : ∀ x ∈ Set.Icc a b, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Set.Icc a b, HasDerivAt du (V x * u x) x)
    (hVc : ContinuousOn V (Set.Icc a b))
    (hu0 : u a = 0) (hdu0 : du a = 0) :
    ∀ x ∈ Set.Icc a b, u x = 0 := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hVc
  set F : ℝ → ℝ × ℝ := fun t => (u t, du t) with hFdef
  have huc : ContinuousOn u (Set.Icc a b) :=
    fun x hx => (hu x hx).continuousAt.continuousWithinAt
  have hduc : ContinuousOn du (Set.Icc a b) :=
    fun x hx => (hdu x hx).continuousAt.continuousWithinAt
  have hcont : ContinuousOn F (Set.Icc a b) := huc.prodMk hduc
  have hderiv : ∀ x ∈ Set.Ico a b, HasDerivWithinAt F (du x, V x * u x) (Set.Ici x) x := by
    intro x hx
    have hxab : x ∈ Set.Icc a b := ⟨hx.1, le_of_lt hx.2⟩
    exact ((hu x hxab).prodMk (hdu x hxab)).hasDerivWithinAt
  have hinit : F a = 0 := by rw [hFdef]; simp only [Prod.mk_eq_zero]; exact ⟨hu0, hdu0⟩
  have hbound : ∀ x ∈ Set.Ico a b, ‖(du x, V x * u x)‖ ≤ (M + 1) * ‖F x‖ := by
    intro x hx
    have hxab : x ∈ Set.Icc a b := ⟨hx.1, le_of_lt hx.2⟩
    rw [Prod.norm_def, hFdef, Prod.norm_def]
    simp only [Real.norm_eq_abs]
    have hMx : |V x| ≤ M := by have := hM x hxab; rwa [Real.norm_eq_abs] at this
    have hMnn : 0 ≤ M := le_trans (abs_nonneg _) hMx
    have hmax_nn : 0 ≤ max |u x| |du x| := le_trans (abs_nonneg _) (le_max_left _ _)
    apply max_le
    · calc |du x| ≤ max |u x| |du x| := le_max_right _ _
        _ ≤ (M + 1) * max |u x| |du x| := by nlinarith [hmax_nn, hMnn]
    · rw [abs_mul]
      calc |V x| * |u x| ≤ M * |u x| := mul_le_mul_of_nonneg_right hMx (abs_nonneg _)
        _ ≤ M * max |u x| |du x| := mul_le_mul_of_nonneg_left (le_max_left _ _) hMnn
        _ ≤ (M + 1) * max |u x| |du x| := by nlinarith [hmax_nn]
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hcont hderiv hinit hbound
  intro x hx
  have h1 := congrArg Prod.fst (hzero x hx)
  simpa [hFdef] using h1

/-- Two-sided uniqueness: a `C²` solution of the reduced equation with zero Cauchy data at
`r₁ > 0` vanishes on all of `(0,∞)` (forward via `forward_zero`, backward via reflection). -/
private lemma cont_cauchy_zero (ℓ : ℕ) (E : ℝ) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    (hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r - 2 * E) * χ r)
    {r₁ : ℝ} (hr₁ : 0 < r₁) (h0 : χ r₁ = 0) (h0' : deriv χ r₁ = 0) :
    ∀ r, 0 < r → χ r = 0 := by
  have hodeW : ∀ x, 0 < x → contW ℓ E x * χ x = deriv^[2] χ x := fun x hx => by
    rw [hode x hx]; simp only [contW]
  have hlin : ∀ x : ℝ, HasDerivAt (fun t => 2 * r₁ - t) (-1 : ℝ) x :=
    fun x => (hasDerivAt_id x).const_sub (2 * r₁)
  have hfwd : ∀ r, r₁ ≤ r → χ r = 0 := by
    intro r hrr
    have hVc : ContinuousOn (contW ℓ E) (Set.Icc r₁ r) :=
      fun x hx => (contW_hasDerivAt ℓ E (lt_of_lt_of_le hr₁ hx.1)).continuousAt.continuousWithinAt
    refine forward_zero hrr (fun x hx => hχ1 x (lt_of_lt_of_le hr₁ hx.1)) ?_ hVc h0 h0' r
      (Set.right_mem_Icc.2 hrr)
    intro x hx
    rw [hodeW x (lt_of_lt_of_le hr₁ hx.1)]
    exact hχ2 x (lt_of_lt_of_le hr₁ hx.1)
  have hbwd : ∀ r, 0 < r → r ≤ r₁ → χ r = 0 := by
    intro r hrpos hrr₁
    rcases eq_or_lt_of_le hrr₁ with heq | hlt
    · rw [heq]; exact h0
    set b := 2 * r₁ - r with hbdef
    have hr₁b : r₁ ≤ b := by rw [hbdef]; linarith
    have hpos2 : ∀ x ∈ Set.Icc r₁ b, 0 < 2 * r₁ - x := by
      intro x hx; have hxb := hx.2; rw [hbdef] at hxb; linarith
    have hu : ∀ x ∈ Set.Icc r₁ b, HasDerivAt (fun t => χ (2 * r₁ - t))
        (-deriv χ (2 * r₁ - x)) x := by
      intro x hx
      have h := (hχ1 (2 * r₁ - x) (hpos2 x hx)).comp x (hlin x)
      convert h using 1; ring
    have hdu : ∀ x ∈ Set.Icc r₁ b, HasDerivAt (fun t => -deriv χ (2 * r₁ - t))
        (contW ℓ E (2 * r₁ - x) * χ (2 * r₁ - x)) x := by
      intro x hx
      rw [hodeW (2 * r₁ - x) (hpos2 x hx)]
      have h := ((hχ2 (2 * r₁ - x) (hpos2 x hx)).comp x (hlin x)).neg
      convert h using 1; ring
    have hVc : ContinuousOn (fun t => contW ℓ E (2 * r₁ - t)) (Set.Icc r₁ b) :=
      fun x hx => (contW_hasDerivAt ℓ E (hpos2 x hx)).continuousAt.comp_continuousWithinAt
        ((continuous_const.sub continuous_id).continuousWithinAt)
    have hu0 : (fun t => χ (2 * r₁ - t)) r₁ = 0 := by
      change χ (2 * r₁ - r₁) = 0; rw [show 2 * r₁ - r₁ = r₁ from by ring]; exact h0
    have hdu0 : (fun t => -deriv χ (2 * r₁ - t)) r₁ = 0 := by
      change -deriv χ (2 * r₁ - r₁) = 0; rw [show 2 * r₁ - r₁ = r₁ from by ring, h0']; ring
    have hfz := forward_zero hr₁b hu hdu hVc hu0 hdu0 b (Set.right_mem_Icc.2 hr₁b)
    have hfz' : χ (2 * r₁ - b) = 0 := hfz
    rwa [show 2 * r₁ - b = r from by rw [hbdef]; ring] at hfz'
  intro r hr
  rcases le_total r r₁ with h | h
  · exact hbwd r hr h
  · exact hfwd r h

/-- **For `E ≥ 0`, every `C²` square-integrable solution of the reduced radial equation
    vanishes** (the continuous spectrum carries no bound states).

    Any `χ` solving `χ''(r) = (ℓ(ℓ+1)/r² − 2/r − 2E)·χ(r)` on `(0,∞)` and
    square-integrable there is identically `0`.

    **Proof.** For `r ≥ ℓ(ℓ+1)+1` the potential `W = ℓ(ℓ+1)/r² − 2/r − 2E` is
    negative, increasing, with `−W ≥ 1/r`. The energy `G = χ'² − Wχ²` is decreasing
    (`G' = −W'χ²`) and `G/(−W)` is increasing (`(G/(−W))' = W'χ'²/W² ≥ 0`), so
    `G ≥ K·(−W)` with `K = G(r₀)/(−W(r₀)) > 0` whenever `χ(r₀) ≠ 0`
    (`energy_diff_ineq`). Then `χ'` is bounded, so the `L²` function `χ` is Lipschitz
    and tends to `0` (`l2_tendsto_zero`); hence
    `(χχ')' = χ'² − (−W)χ² ≥ (K/2)·(−W) ≥ (K/2)/r` eventually,
    forcing `χχ' → +∞` by log-divergence — contradicting `χχ' → 0`
    (`χ → 0`, `χ'` bounded). So `χ ≡ 0` on
    `[ℓ(ℓ+1)+1, ∞)`, and Cauchy-data uniqueness (`cont_cauchy_zero`, Grönwall forward +
    reflection backward) extends this to all of `(0,∞)`. -/
theorem reduced_radial_continuum (ℓ : ℕ) (E : ℝ) (hE : 0 ≤ E) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    (hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r - 2 * E) * χ r)
    (hL2 : IntegrableOn (fun r => χ r ^ 2) (Set.Ioi 0)) :
    ∀ r, 0 < r → χ r = 0 := by
  have hodeW : ∀ x, 0 < x → contW ℓ E x * χ x = deriv^[2] χ x := fun x hx => by
    rw [hode x hx]; simp only [contW]
  have hRpos : (0 : ℝ) < (ℓ : ℝ) * ((ℓ : ℝ) + 1) + 1 := by positivity
  -- Step 1: χ ≡ 0 on [R, ∞)
  have hRzero : ∀ r, (ℓ : ℝ) * ((ℓ : ℝ) + 1) + 1 ≤ r → χ r = 0 := by
    by_contra hcon
    rw [not_forall] at hcon
    obtain ⟨r₀, hr₀⟩ := hcon
    rw [Classical.not_imp] at hr₀
    obtain ⟨hr₀R, hr₀ne⟩ := hr₀
    have hr₀pos : 0 < r₀ := lt_of_lt_of_le hRpos hr₀R
    obtain ⟨hGdec, hGratio⟩ := energy_diff_ineq ℓ E hE χ hχ1 hχ2 hode hr₀R
    set G0 := (deriv χ r₀) ^ 2 - contW ℓ E r₀ * (χ r₀) ^ 2 with hG0def
    have hWr₀neg : contW ℓ E r₀ < 0 := (contW_thresh ℓ E hE hr₀R).2.2.1
    have hD0pos : 0 < -contW ℓ E r₀ := by linarith
    have hχ₀sq : 0 < (χ r₀) ^ 2 := by positivity
    have hG0pos : 0 < G0 := by
      rw [hG0def]; nlinarith [sq_nonneg (deriv χ r₀), mul_pos hD0pos hχ₀sq]
    set K := G0 / (-contW ℓ E r₀) with hKdef
    have hKpos : 0 < K := div_pos hG0pos hD0pos
    -- threshold facts at any r ≥ r₀
    have hWfacts : ∀ r, r₀ ≤ r → contW ℓ E r < 0 ∧ 1 / r ≤ -contW ℓ E r := fun r hr =>
      ⟨(contW_thresh ℓ E hE (le_trans hr₀R hr)).2.2.1, (contW_thresh ℓ E hE (le_trans hr₀R hr)).2.1⟩
    -- G(r) ≥ K·(−W r)
    have hGlb : ∀ r, r₀ ≤ r →
        K * (-contW ℓ E r) ≤ (deriv χ r) ^ 2 - contW ℓ E r * (χ r) ^ 2 := by
      intro r hr
      have hg := hGratio r hr
      rw [hKdef, div_mul_eq_mul_div, div_le_iff₀ hD0pos]
      exact hg
    -- χ' is bounded by √G0
    have hBnd : ∀ r, r₀ ≤ r → |deriv χ r| ≤ Real.sqrt G0 := by
      intro r hr
      have hDr : 0 ≤ -contW ℓ E r := le_of_lt (by linarith [(hWfacts r hr).1])
      have h1 : (deriv χ r) ^ 2 ≤ G0 := by
        have := hGdec r hr; nlinarith [mul_nonneg hDr (sq_nonneg (χ r)), this]
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt h1
    -- χ is Lipschitz on [r₀, ∞)
    have hlip : ∀ x y, r₀ ≤ x → r₀ ≤ y → |χ x - χ y| ≤ Real.sqrt G0 * |x - y| := by
      intro x y hx hy
      have hbd := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := χ) (f' := deriv χ) (s := Set.Ici r₀) (C := Real.sqrt G0)
        (fun z hz => (hχ1 z (lt_of_lt_of_le hr₀pos hz)).hasDerivWithinAt)
        (fun z hz => by rw [Real.norm_eq_abs]; exact hBnd z hz) (convex_Ici r₀)
        (Set.mem_Ici.2 hy) (Set.mem_Ici.2 hx)
      simp only [Real.norm_eq_abs] at hbd
      exact hbd
    -- χ → 0
    have hχ0 : Filter.Tendsto χ Filter.atTop (𝓝 0) :=
      l2_tendsto_zero (Real.sqrt_nonneg G0) hlip
        (hL2.mono_set (Set.Ioi_subset_Ioi (le_of_lt hr₀pos)))
    -- χ² → 0
    have hχ0sq : Filter.Tendsto (fun r => (χ r) ^ 2) Filter.atTop (𝓝 0) := by
      have h := hχ0.mul hχ0
      simpa [← pow_two] using h
    -- pick r₂ ≥ r₀ with χ² < K/4 beyond it
    obtain ⟨r₂, hr₂⟩ := Filter.eventually_atTop.1
      ((hχ0sq.eventually (eventually_lt_nhds (show (0 : ℝ) < K / 4 by positivity))).and
        (eventually_ge_atTop r₀))
    have hr₂r₀ : r₀ ≤ r₂ := (hr₂ r₂ le_rfl).2
    have hr₂pos : 0 < r₂ := lt_of_lt_of_le hr₀pos hr₂r₀
    -- derivative of χ·χ'
    have hχχ'd : ∀ s, 0 < s →
        HasDerivAt (fun t => χ t * deriv χ t) ((deriv χ s) ^ 2 + contW ℓ E s * (χ s) ^ 2) s := by
      intro s hs
      convert (hχ1 s hs).mul (hχ2 s hs) using 1
      rw [← hodeW s hs]; ring
    -- pointwise lower bound (K/2)/s ≤ (χχ')'
    have hptw : ∀ s, r₂ ≤ s → (K / 2) * (1 / s) ≤ (deriv χ s) ^ 2 + contW ℓ E s * (χ s) ^ 2 := by
      intro s hs
      have hsr₀ : r₀ ≤ s := le_trans hr₂r₀ hs
      have hgl := hGlb s hsr₀
      have hsmall : (χ s) ^ 2 < K / 4 := (hr₂ s hs).1
      have hWs := hWfacts s hsr₀
      have hDs : 0 < -contW ℓ E s := by linarith [hWs.1]
      have heq : (deriv χ s) ^ 2 + contW ℓ E s * (χ s) ^ 2
          = ((deriv χ s) ^ 2 - contW ℓ E s * (χ s) ^ 2) - 2 * ((-contW ℓ E s) * (χ s) ^ 2) := by
        ring
      rw [heq]
      have hp1 : (-contW ℓ E s) * (K / 2) ≤ (-contW ℓ E s) * (K - 2 * (χ s) ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hDs)
      have hp2 : (1 / s) * (K / 2) ≤ (-contW ℓ E s) * (K / 2) :=
        mul_le_mul_of_nonneg_right hWs.2 (by linarith)
      nlinarith [hgl, hp1, hp2]
    -- χ·χ' → +∞
    have hχχ'top : Filter.Tendsto (fun T => χ T * deriv χ T) Filter.atTop Filter.atTop := by
      have hlow : ∀ T, r₂ ≤ T →
          χ r₂ * deriv χ r₂ + (K / 2) * Real.log (T / r₂) ≤ χ T * deriv χ T := by
        intro T hT
        have hsub : Set.uIcc r₂ T ⊆ Set.Ioi 0 := by
          rw [Set.uIcc_of_le hT]; exact fun z hz => lt_of_lt_of_le hr₂pos hz.1
        have hd : ContinuousOn (deriv χ) (Set.uIcc r₂ T) :=
          fun z hz => (hχ2 z (hsub hz)).continuousAt.continuousWithinAt
        have hc : ContinuousOn χ (Set.uIcc r₂ T) :=
          fun z hz => (hχ1 z (hsub hz)).continuousAt.continuousWithinAt
        have hw : ContinuousOn (contW ℓ E) (Set.uIcc r₂ T) :=
          fun z hz => (contW_hasDerivAt ℓ E (hsub hz)).continuousAt.continuousWithinAt
        have hcont : ContinuousOn (fun s => (deriv χ s) ^ 2 + contW ℓ E s * (χ s) ^ 2)
            (Set.uIcc r₂ T) := (hd.pow 2).add (hw.mul (hc.pow 2))
        have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun s hs => hχχ'd s (hsub hs)) hcont.intervalIntegrable
        have hmono : (K / 2) * Real.log (T / r₂)
            ≤ ∫ s in r₂..T, ((deriv χ s) ^ 2 + contW ℓ E s * (χ s) ^ 2) := by
          have h0notin : (0 : ℝ) ∉ Set.uIcc r₂ T := fun h => by
            have := hsub h; rw [Set.mem_Ioi] at this; exact lt_irrefl 0 this
          have hone : ∫ s in r₂..T, (K / 2) * (1 / s) = (K / 2) * Real.log (T / r₂) := by
            rw [intervalIntegral.integral_const_mul, integral_one_div h0notin]
          have hci : IntervalIntegrable (fun s => (K / 2) * (1 / s)) volume r₂ T :=
            (continuousOn_const.mul (continuousOn_const.div continuousOn_id
              (fun z hz => ne_of_gt (hsub hz)))).intervalIntegrable
          rw [← hone]
          refine intervalIntegral.integral_mono_on hT hci hcont.intervalIntegrable (fun s hs => ?_)
          exact hptw s hs.1
        linarith [hftc, hmono]
      have htendlog : Filter.Tendsto (fun T => χ r₂ * deriv χ r₂ + (K / 2) * Real.log (T / r₂))
          Filter.atTop Filter.atTop := by
        apply Filter.tendsto_atTop_add_const_left
        apply Filter.Tendsto.const_mul_atTop (by positivity)
        exact Real.tendsto_log_atTop.comp (Filter.tendsto_id.atTop_div_const hr₂pos)
      exact Filter.tendsto_atTop_mono' _ (Filter.eventually_atTop.2 ⟨r₂, hlow⟩) htendlog
    -- χ·χ' → 0
    have hχχ'zero : Filter.Tendsto (fun T => χ T * deriv χ T) Filter.atTop (𝓝 0) := by
      have hb : ∀ᶠ T in Filter.atTop, ‖χ T * deriv χ T‖ ≤ Real.sqrt G0 * |χ T| := by
        filter_upwards [eventually_ge_atTop r₀] with T hT
        rw [Real.norm_eq_abs, abs_mul]
        calc |χ T| * |deriv χ T| ≤ |χ T| * Real.sqrt G0 :=
              mul_le_mul_of_nonneg_left (hBnd T hT) (abs_nonneg _)
          _ = Real.sqrt G0 * |χ T| := mul_comm _ _
      have hg : Filter.Tendsto (fun T => Real.sqrt G0 * |χ T|) Filter.atTop (𝓝 0) := by
        have hax : Filter.Tendsto (fun T => |χ T|) Filter.atTop (𝓝 0) := by
          simpa using hχ0.abs
        simpa using hax.const_mul (Real.sqrt G0)
      exact squeeze_zero_norm' hb hg
    exact (not_tendsto_atTop_of_tendsto_nhds hχχ'zero) hχχ'top
  -- Step 2: extend to (0, ∞) via Cauchy-data uniqueness at R+1
  set r₁ := (ℓ : ℝ) * ((ℓ : ℝ) + 1) + 2 with hr₁def
  have hr₁pos : 0 < r₁ := by rw [hr₁def]; positivity
  have hr₁ev : χ =ᶠ[𝓝 r₁] 0 := by
    filter_upwards [Ioi_mem_nhds (show (ℓ : ℝ) * ((ℓ : ℝ) + 1) + 1 < r₁ by rw [hr₁def]; linarith)]
      with x hx
    exact hRzero x (le_of_lt hx)
  have h0 : χ r₁ = 0 := hr₁ev.eq_of_nhds
  have h0' : deriv χ r₁ = 0 := by
    rw [hr₁ev.deriv_eq]; simp
  exact cont_cauchy_zero ℓ E χ hχ1 hχ2 hode hr₁pos h0 h0'

/-! ## Continuous spectrum -/

/-- **For E ≥ 0, every classical L² solution vanishes (continuous spectrum).**

    This gives the continuous spectrum [0, ∞) of H_ℓ: at energy `E ≥ 0` there are
    no `L²` bound states, so any `C²` square-integrable solution is identically
    `0` on `(0,∞)`. (As in `radial_quantization`, the `C²` hypotheses are needed
    for the `deriv`-based `radialHamiltonian` to express a genuine classical ODE.)

    **Reduction (proved).** Passing to `χ = r·ψ` via `reduced_ode`, the claim is
    `reduced_radial_continuum`: with `W = ℓ(ℓ+1)/r² − 2/r − 2E → −2E ≤ 0`, the energy
    `χ'² − Wχ²` controls the solution and an elementary Grönwall/monotonicity argument
    forces any `L²` solution to vanish (no decaying solution exists in the oscillatory
    regime) — see `reduced_radial_continuum`. -/
theorem radial_continuum (ℓ : ℕ) (E : ℝ) (hE : 0 ≤ E) :
    ∀ ψ : ℝ → ℝ,
      (∀ r, 0 < r → HasDerivAt ψ (deriv ψ r) r) →
      (∀ r, 0 < r → HasDerivAt (deriv ψ) (deriv^[2] ψ r) r) →
      (∀ r, 0 < r → radialHamiltonian ℓ ψ r = E * ψ r) → RadialL2 ψ →
      ∀ r, 0 < r → ψ r = 0 := by
  intro ψ hψ1 hψ2 heq hL2
  set χ : ℝ → ℝ := fun s => s * ψ s with hχdef
  have hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r := by
    intro r hr
    rw [hχdef, deriv_reducedMul ψ (hψ1 r hr)]
    exact hasDerivAt_reducedMul ψ (hψ1 r hr)
  have hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r := by
    intro r hr
    rw [hχdef, deriv2_reducedMul ψ hψ1 hψ2 hr]
    exact hasDerivAt_deriv_reducedMul ψ hψ1 hψ2 hr
  have hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r - 2 * E) * χ r := by
    intro r hr
    have hχr : χ r = r * ψ r := rfl
    rw [show deriv^[2] χ r = deriv^[2] (fun s => s * ψ s) r from rfl,
      reduced_ode ℓ E ψ hψ1 hψ2 heq hr, hχr]
  have hχL2 : IntegrableOn (fun r => χ r ^ 2) (Set.Ioi 0) := reduced_integrableOn_sq ψ hL2
  have h0 := reduced_radial_continuum ℓ E hE χ hχ1 hχ2 hode hχL2
  intro r hr
  have hrψ : r * ψ r = 0 := h0 r hr
  exact (mul_eq_zero.1 hrψ).resolve_left (ne_of_gt hr)

end QuantumMechanics.Hydrogen.RadialEq
