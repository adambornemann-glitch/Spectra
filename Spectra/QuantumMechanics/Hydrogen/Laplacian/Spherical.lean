/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Spectra.Spaces.Sobolev.WeakDerivative
import Spectra.SphericalHarmonics.Basic
/-!
# Separation of the Laplacian in spherical coordinates

The spherical-coordinate chart and the pointwise separation of the 3D Laplacian
`−Δ = −(1/r²)∂_r(r²∂_r) + L̂²/r²`, where `L̂² = laplaceBeltrami` is the angular
Laplacian from `SphericalHarmonics/Basic.lean`. Everything here is proved sorry-free.

## Main statements

* `sphereChart` — the chart `(r, θ, φ) ↦ (r sinθ cosφ, r sinθ sinφ, r cosθ) : ℝ³`.
* `norm_sphereChart` — `‖sphereChart r θ φ‖ = |r|`.
* `radialPart_eq` — the radial operator in divergence form, `(1/r²)∂_r(r²∂_r R) = R″ + (2/r)R′`.
* `iteratedFDeriv_two_line` — the line-restriction bridge: the directional second
  derivative `iteratedFDeriv 2 F x ![v,v]` is the 1D `(d²/dt²)F(x+t·v)|₀`.
* `laplacian_comp_normSq` — **the radial Laplacian** `Δ(g∘‖·‖²) = 4‖x‖²·g″(‖x‖²) + 6·g′(‖x‖²)`
  on `ℝ³`, for globally `C²` `g`. This is the genuine analytic core (the orthonormal-basis
  Laplacian sum, the per-direction 1D chain rule, and Parseval), done without any
  norm-Hessian — by parametrizing the radial profile through the globally smooth `‖·‖²`.
* `laplacian_comp_norm` — the `‖·‖` form `Δ(g∘‖·‖) = g″ + (2/r)g′` on `ℝ³ \ {0}`, obtained
  from `laplacian_comp_normSq` with `g∘√` after localizing `√`'s origin singularity by a
  `C²` (`Real.smoothTransition`) modification and using locality of `Δ`.
* `sphereFrame_orthonormal`, `sphereFrameONB`, `laplacian_sphereFrame_sum` — the spherical
  orthonormal frame `(ê_r, ê_θ, ê_φ)` and the basis-independent decomposition of `Δf` into
  its three diagonal Hessian contractions in that frame.
* `laplacian_separates` — the full pointwise separation on the chart,
  `Δf = (1/r²)∂_r(r²∂_r f) − (1/r²)L̂²f`, assembled from the frame decomposition and the
  `SphereSep` chart-curve lemmas (radial half via `radialPart_eq`, angular half via
  `laplaceBeltrami`; the gradient cross-terms cancel).

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics IV*][reed1978], §XIII.3.
-/

noncomputable section

open MeasureTheory Real InnerProductSpace Laplacian
open Spectra.Sobolev Spectra.SphericalHarmonics
open scoped RealInnerProductSpace Topology

namespace Spectra.QuantumMechanics.Hydrogen

/-! ## The spherical-coordinate chart -/

/-- The spherical-coordinate chart
    `(r, θ, φ) ↦ (r sin θ cos φ, r sin θ sin φ, r cos θ)` into `ℝ³`. -/
noncomputable def sphereChart (r θ φ : ℝ) : R3 :=
  !₂[r * Real.sin θ * Real.cos φ, r * Real.sin θ * Real.sin φ, r * Real.cos θ]

/-- The chart lands on the sphere of radius `|r|`: `‖sphereChart r θ φ‖ = |r|`. -/
lemma norm_sphereChart (r θ φ : ℝ) : ‖sphereChart r θ φ‖ = |r| := by
  rw [EuclideanSpace.norm_eq]
  have hsum : (∑ i, ‖(sphereChart r θ φ) i‖ ^ 2) = r ^ 2 := by
    simp only [sphereChart, Fin.sum_univ_three, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Real.norm_eq_abs, sq_abs]
    linear_combination (r ^ 2 * Real.sin θ ^ 2) * Real.sin_sq_add_cos_sq φ
      + r ^ 2 * Real.sin_sq_add_cos_sq θ
  rw [hsum, Real.sqrt_sq_eq_abs]

/-! ## The radial operator -/

/-- **Radial operator, divergence form = expanded form.**
    `(1/r²)·(r²·R')′ = R″ + (2/r)·R′` for `r ≠ 0`.

    This is the radial half of the separation already at the operator level: it
    identifies the `(1/r²)∂_r(r²∂_r)` form of the radial Laplacian appearing in
    `laplacian_separates` with the expanded `R″ + (2/r)R′` form used by
    `RadialEq.radialHamiltonian`. Pure 1D calculus. -/
lemma radialPart_eq (R : ℝ → ℂ) (hR : ContDiff ℝ 2 R) {r : ℝ} (hr : r ≠ 0) :
    (1 / (r : ℂ) ^ 2) * deriv (fun s : ℝ => (s : ℂ) ^ 2 * deriv R s) r
      = deriv (deriv R) r + (2 / (r : ℂ)) * deriv R r := by
  have hrne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hRd2 : Differentiable ℝ (deriv R) := hR.differentiable_deriv_two
  -- `s ↦ (↑s)²` has derivative `2·↑r` (differentiate `s ↦ s²` in ℝ, then coerce).
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
    simpa using hasDerivAt_pow 2 r
  have hpow : HasDerivAt (fun s : ℝ => (s : ℂ) ^ 2) (2 * (r : ℂ)) r := by
    have h := hsq.ofReal_comp
    simp only [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_ofNat] at h
    exact h
  -- product rule for `(↑s)²·R′`.
  have hprod : HasDerivAt (fun s : ℝ => (s : ℂ) ^ 2 * deriv R s)
      (2 * (r : ℂ) * deriv R r + (r : ℂ) ^ 2 * deriv (deriv R) r) r :=
    hpow.mul (hRd2 r).hasDerivAt
  rw [hprod.deriv]
  field_simp
  ring

/-! ## Line restriction of the second derivative -/

/-- **Directional second derivative as a 1D iterated derivative.**
    `iteratedFDeriv ℝ 2 F x ![v,v] = (d²/dt²) F(x + t·v)|_{t=0}` for `F` globally `C²`.
    This is the bridge that reduces the multivariable Hessian (and hence the Laplacian)
    to one-dimensional calculus along coordinate lines. -/
lemma iteratedFDeriv_two_line {F : R3 → ℂ} (hF : ContDiff ℝ 2 F) (x v : R3) :
    iteratedFDeriv ℝ 2 F x ![v, v]
      = iteratedDeriv 2 (fun t : ℝ => F (x + t • v)) 0 := by
  have hcd : ContDiff ℝ 2 (fun z : R3 => F (x + z)) :=
    hF.comp (contDiff_const.add contDiff_id)
  have hcomp : (fun t : ℝ => F (x + t • v))
      = (fun z : R3 => F (x + z)) ∘ (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v) := by
    funext t; simp
  rw [hcomp, iteratedDeriv_eq_iteratedFDeriv,
    ContinuousLinearMap.iteratedFDeriv_comp_right _ hcd 0 (le_refl 2),
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [map_zero, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
    one_smul]
  rw [iteratedFDeriv_comp_add_left 2 x 0, add_zero]
  congr 1
  funext i
  fin_cases i <;> rfl

/-! ## Radial functions of `‖·‖²`: the radial Laplacian -/

/-- **Radial Laplacian (in the `‖·‖²` variable).**
    For globally `C²` `g`, `Δ(g ∘ ‖·‖²) = 4‖x‖²·g″(‖x‖²) + 6·g′(‖x‖²)` on `ℝ³`.

    The dimension `3` enters as the `6 = 2·3`. Proved by the line-restriction bridge
    (`iteratedFDeriv_two_line`): along each coordinate direction `bᵢ`, `‖x + t·bᵢ‖²` is
    the quadratic `t² + 2⟪x,bᵢ⟫t + ‖x‖²`, the 1D second-order chain rule gives the
    per-direction term, and Parseval `∑ᵢ⟪x,bᵢ⟫² = ‖x‖²` assembles the sum.

    Using `‖·‖²` (globally smooth) rather than `‖·‖` sidesteps the singularity of the
    norm at the origin; the `‖·‖` version `laplacian_comp_norm` then needs only the
    localization `g ∘ ‖·‖ = (g∘√) ∘ ‖·‖²` away from `0`. -/
theorem laplacian_comp_normSq (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) (x : R3) :
    Δ (fun y : R3 => g (‖y‖ ^ 2)) x
      = 4 * (‖x‖ ^ 2 : ℂ) * iteratedDeriv 2 g (‖x‖ ^ 2) + 6 * deriv g (‖x‖ ^ 2) := by
  have hF : ContDiff ℝ 2 (fun y : R3 => g (‖y‖ ^ 2)) := hg.comp (contDiff_norm_sq ℝ)
  set b := stdOrthonormalBasis ℝ R3 with hb
  -- Per-direction term, via the line-restriction bridge and the 1D chain rule.
  have hterm : ∀ i, iteratedFDeriv ℝ 2 (fun y : R3 => g (‖y‖ ^ 2)) x ![b i, b i]
      = (2 * ⟪x, b i⟫_ℝ) ^ 2 • iteratedDeriv 2 g (‖x‖ ^ 2)
        + (2 * ‖b i‖ ^ 2) • deriv g (‖x‖ ^ 2) := by
    intro i
    rw [iteratedFDeriv_two_line hF x (b i)]
    set q : ℝ → ℝ := fun t => ‖b i‖ ^ 2 * t ^ 2 + 2 * ⟪x, b i⟫_ℝ * t + ‖x‖ ^ 2 with hqdef
    have hq_cd : ContDiff ℝ 2 q := by rw [hqdef]; fun_prop
    have hqval : (fun t : ℝ => g (‖x + t • b i‖ ^ 2)) = g ∘ q := by
      funext t
      simp only [Function.comp_apply, hqdef]
      congr 1
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    have hq0 : q 0 = ‖x‖ ^ 2 := by rw [hqdef]; ring
    -- `q` derivatives at `0` (q is a quadratic).
    have hqderiv : ∀ t : ℝ, HasDerivAt q (‖b i‖ ^ 2 * (2 * t) + 2 * ⟪x, b i⟫_ℝ * 1) t := by
      intro t
      rw [hqdef]
      exact ((((show HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t by
            simpa using hasDerivAt_pow 2 t).const_mul (‖b i‖ ^ 2)).add
          ((hasDerivAt_id t).const_mul (2 * ⟪x, b i⟫_ℝ))).add_const (‖x‖ ^ 2))
    have hq' : deriv q 0 = 2 * ⟪x, b i⟫_ℝ := by rw [(hqderiv 0).deriv]; ring
    have hq'' : iteratedDeriv 2 q 0 = 2 * ‖b i‖ ^ 2 := by
      have hd1 : deriv q = fun t => ‖b i‖ ^ 2 * (2 * t) + 2 * ⟪x, b i⟫_ℝ * 1 :=
        funext fun t => (hqderiv t).deriv
      rw [iteratedDeriv_succ, iteratedDeriv_one, hd1,
        (((show HasDerivAt (fun t : ℝ => 2 * t) 2 0 by
              simpa using (hasDerivAt_id (0 : ℝ)).const_mul 2).const_mul (‖b i‖ ^ 2)).add_const
          (2 * ⟪x, b i⟫_ℝ * 1)).deriv]
      ring
    rw [hqval, iteratedDeriv_vcomp_two hg.contDiffAt hq_cd.contDiffAt, hq0, hq', hq'',
      fderiv_eq_smul_deriv]
    congr 1
    rw [show (fun _ : Fin 2 => 2 * ⟪x, b i⟫_ℝ)
          = (fun _ : Fin 2 => (2 * ⟪x, b i⟫_ℝ) • (1 : ℝ)) by simp,
      ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← iteratedDeriv_eq_iteratedFDeriv]
  -- Norm/Parseval bookkeeping.
  have hb_norm : ∀ i, ‖b i‖ ^ 2 = 1 := fun i => by rw [b.orthonormal.1 i]; norm_num
  have hpars : ∑ i, ⟪x, b i⟫_ℝ ^ 2 = ‖x‖ ^ 2 := by
    have h := b.sum_inner_mul_inner x x
    rw [real_inner_self_eq_norm_sq] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm (b i) x, ← pow_two]
  have hdim : Fintype.card (Fin (Module.finrank ℝ R3)) = 3 := by
    rw [Fintype.card_fin, finrank_euclideanSpace_fin]
  -- Assemble the sum.
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [← hb]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
    ← Finset.sum_smul, ← Finset.sum_smul]
  have hs1 : ∑ i, (2 * ⟪x, b i⟫_ℝ) ^ 2 = 4 * ‖x‖ ^ 2 := by
    rw [Finset.sum_congr rfl fun i _ => (by ring : (2 * ⟪x, b i⟫_ℝ) ^ 2 = 4 * ⟪x, b i⟫_ℝ ^ 2),
      ← Finset.mul_sum, hpars]
  have hs2 : ∑ i, 2 * ‖b i‖ ^ 2 = 6 := by
    have hconst : ∀ i, (2 : ℝ) * ‖b i‖ ^ 2 = 2 := fun i => by rw [hb_norm i]; ring
    rw [Finset.sum_congr rfl fun i _ => hconst i, Finset.sum_const, Finset.card_univ, hdim]
    norm_num
  rw [hs1, hs2, Complex.real_smul, Complex.real_smul]
  push_cast
  ring

/-! ## Radial functions: the radial Laplacian -/

/-- `Δ(g ∘ ‖·‖) = g″ + (2/r)·g′` on `ℝ³ \ {0}`: the Laplacian of a radially symmetric
    function is its radial part.

    Reduced to `laplacian_comp_normSq`, which proves the same identity in the `‖·‖²`
    variable (`Δ(h∘‖·‖²) = 4‖x‖²h″ + 6h′`): setting `h = g∘√` (so `g‖y‖ = h(‖y‖²)`) gives
    exactly `g″(‖x‖) + (2/‖x‖)g′(‖x‖)` after the `√` chain rule. The reduction needs `h`
    to be globally `C²`, but `√` is singular at `0`; the proof handles this by replacing
    `√` with a global `C²` function (a `Real.smoothTransition` modification, positive
    everywhere and equal to `√` near `‖x‖²`) and invoking locality of `Δ`. -/
theorem laplacian_comp_norm (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) {x : R3} (hx : x ≠ 0) :
    Δ (fun y : R3 => g ‖y‖) x = iteratedDeriv 2 g ‖x‖ + (2 / (‖x‖ : ℂ)) * deriv g ‖x‖ := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hrne : (‖x‖ : ℝ) ≠ 0 := ne_of_gt hr
  have hxc : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrne
  have hs₀ : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
  have hs₀ne : (‖x‖ : ℝ) ^ 2 ≠ 0 := ne_of_gt hs₀
  have hsqrt_s₀ : Real.sqrt (‖x‖ ^ 2) = ‖x‖ := Real.sqrt_sq hr.le
  -- `iteratedDeriv 2 = deriv ∘ deriv` (pointwise) -----------------------------------------
  have hid2 : ∀ (h : ℝ → ℂ) (z : ℝ), iteratedDeriv 2 h z = deriv (deriv h) z := by
    intro h z; rw [iteratedDeriv_succ, iteratedDeriv_one]
  -- ── σ: a globally smooth modification of √, positive everywhere, = √ near ‖x‖² ──────────
  set c : ℝ := ‖x‖ ^ 2 / 4 with hcdef
  have hc : 0 < c := by positivity
  set ρ : ℝ → ℝ := fun s => c + (s - c) * Real.smoothTransition ((s - c) / c) with hρdef
  have hρ_cd : ContDiff ℝ 2 ρ :=
    contDiff_const.add ((contDiff_id.sub contDiff_const).mul
      (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const c)))
  have hρ_pos : ∀ s, 0 < ρ s := by
    intro s
    rw [hρdef]; simp only
    rcases le_or_gt s c with h | h
    · rw [Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (by linarith) hc.le)]
      simpa using hc
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s - c)
        (Real.smoothTransition.nonneg ((s - c) / c))]
  have hρ_id : ρ =ᶠ[𝓝 (‖x‖ ^ 2)] (fun s => s) := by
    have hmem : Set.Ioi (2 * c) ∈ 𝓝 (‖x‖ ^ 2) :=
      isOpen_Ioi.mem_nhds (by rw [Set.mem_Ioi, hcdef]; linarith)
    filter_upwards [hmem] with s hs
    rw [Set.mem_Ioi] at hs
    rw [hρdef]; simp only
    rw [Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hc]; linarith)]; ring
  set σ : ℝ → ℝ := fun s => Real.sqrt (ρ s) with hσdef
  have hσ_cd : ContDiff ℝ 2 σ := hρ_cd.sqrt (fun s => (hρ_pos s).ne')
  have hσ_eq : σ =ᶠ[𝓝 (‖x‖ ^ 2)] Real.sqrt := by
    filter_upwards [hρ_id] with s hs; rw [hσdef]; simp only [hs]
  -- ── locality swap, then apply the proven `‖·‖²` Laplacian to the smooth `g ∘ σ` ─────────
  have hG_cd : ContDiff ℝ 2 (fun s => g (σ s)) := hg.comp hσ_cd
  have hfeq : (fun y : R3 => g ‖y‖) =ᶠ[𝓝 x] (fun y : R3 => g (σ (‖y‖ ^ 2))) := by
    have hqc : Filter.Tendsto (fun y : R3 => ‖y‖ ^ 2) (𝓝 x) (𝓝 (‖x‖ ^ 2)) :=
      (continuous_norm.pow 2).tendsto x
    filter_upwards [hqc.eventually hσ_eq] with y hy
    rw [hy, Real.sqrt_sq (norm_nonneg y)]
  rw [(laplacian_congr_nhds hfeq).eq_of_nhds, laplacian_comp_normSq (fun s => g (σ s)) hG_cd x]
  -- ── transfer the `g ∘ σ` 2-jet to the `g ∘ √` 2-jet at ‖x‖² ─────────────────────────────
  have hcompσ : (fun s => g (σ s)) =ᶠ[𝓝 (‖x‖ ^ 2)] (fun s => g (Real.sqrt s)) :=
    hσ_eq.fun_comp g
  rw [hcompσ.deriv_eq, (hcompσ.iteratedDeriv 2).eq_of_nhds]
  -- ── J₁ = deriv (g ∘ √) (‖x‖²) ──────────────────────────────────────────────────────────
  have hsqrt' : HasDerivAt Real.sqrt (1 / (2 * ‖x‖)) (‖x‖ ^ 2) := by
    have h := Real.hasDerivAt_sqrt hs₀ne; rwa [hsqrt_s₀] at h
  have hJ1 : deriv (fun s => g (Real.sqrt s)) (‖x‖ ^ 2) = (1 / (2 * ‖x‖)) • deriv g ‖x‖ := by
    have hgr : HasDerivAt g (deriv g ‖x‖) (Real.sqrt (‖x‖ ^ 2)) := by
      rw [hsqrt_s₀]; exact (hg.differentiable (by norm_num)).differentiableAt.hasDerivAt
    have hcomp : HasDerivAt (g ∘ Real.sqrt) ((1 / (2 * ‖x‖)) • deriv g ‖x‖) (‖x‖ ^ 2) :=
      HasDerivAt.scomp (‖x‖ ^ 2) hgr hsqrt'
    exact hcomp.deriv
  -- ── J₂ = iteratedDeriv 2 (g ∘ √) (‖x‖²) ────────────────────────────────────────────────
  -- the first derivative of `g ∘ √` equals an explicit function on `(0, ∞)`
  have hderiv_ev : deriv (fun s => g (Real.sqrt s)) =ᶠ[𝓝 (‖x‖ ^ 2)]
      (fun s => (1 / (2 * Real.sqrt s)) • deriv g (Real.sqrt s)) := by
    filter_upwards [isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hs₀)] with s hs
    rw [Set.mem_Ioi] at hs
    have h1 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt s)) s := Real.hasDerivAt_sqrt (ne_of_gt hs)
    have h2 : HasDerivAt g (deriv g (Real.sqrt s)) (Real.sqrt s) :=
      (hg.differentiable (by norm_num)).differentiableAt.hasDerivAt
    have hc : HasDerivAt (g ∘ Real.sqrt) ((1 / (2 * Real.sqrt s)) • deriv g (Real.sqrt s)) s :=
      HasDerivAt.scomp s h2 h1
    exact hc.deriv
  -- a(s) = 1/(2√s),  a'(‖x‖²) = -1/(4‖x‖³)
  have ha : HasDerivAt (fun s => 1 / (2 * Real.sqrt s)) (-(1 / (4 * ‖x‖ ^ 3))) (‖x‖ ^ 2) := by
    have hu : HasDerivAt (fun s => 2 * Real.sqrt s) (1 / ‖x‖) (‖x‖ ^ 2) := by
      have h := (Real.hasDerivAt_sqrt hs₀ne).const_mul (2 : ℝ)
      rw [hsqrt_s₀] at h; convert h using 1; field_simp
    have hd0 : (fun s => 2 * Real.sqrt s) (‖x‖ ^ 2) ≠ 0 := by
      simp only [hsqrt_s₀]; exact mul_ne_zero two_ne_zero hrne
    have h := (hasDerivAt_const (‖x‖ ^ 2) (1 : ℝ)).div hu hd0
    convert h using 1
    simp only [hsqrt_s₀]; field_simp; ring
  -- b(s) = deriv g (√ s),  b'(‖x‖²) = (1/(2‖x‖)) • iteratedDeriv 2 g ‖x‖
  have hb : HasDerivAt (fun s => deriv g (Real.sqrt s))
      ((1 / (2 * ‖x‖)) • iteratedDeriv 2 g ‖x‖) (‖x‖ ^ 2) := by
    have h2 : HasDerivAt (deriv g) (iteratedDeriv 2 g ‖x‖) (Real.sqrt (‖x‖ ^ 2)) := by
      rw [hsqrt_s₀, hid2 g ‖x‖]; exact (hg.differentiable_deriv_two ‖x‖).hasDerivAt
    exact (HasDerivAt.scomp (‖x‖ ^ 2) h2 hsqrt' :
      HasDerivAt (deriv g ∘ Real.sqrt) ((1 / (2 * ‖x‖)) • iteratedDeriv 2 g ‖x‖) (‖x‖ ^ 2))
  have hJ2 : iteratedDeriv 2 (fun s => g (Real.sqrt s)) (‖x‖ ^ 2)
      = (1 / (2 * ‖x‖)) • ((1 / (2 * ‖x‖)) • iteratedDeriv 2 g ‖x‖)
        + (-(1 / (4 * ‖x‖ ^ 3))) • deriv g ‖x‖ := by
    rw [hid2 (fun s => g (Real.sqrt s)) (‖x‖ ^ 2), hderiv_ev.deriv_eq]
    have h := (ha.smul hb).deriv
    simp only [hsqrt_s₀] at h
    exact h
  -- ── assemble ───────────────────────────────────────────────────────────────────────────
  rw [hJ1, hJ2]
  simp only [Complex.real_smul]
  push_cast
  field_simp
  ring

/-! ## The spherical orthonormal frame

At the chart point `sphereChart r θ φ` the unit vectors
`ê_r = (sinθcosφ, sinθsinφ, cosθ)`, `ê_θ = (cosθcosφ, cosθsinφ, −sinθ)`,
`ê_φ = (−sinφ, cosφ, 0)` form an orthonormal basis of `ℝ³` (for *every* `θ, φ`).
Because the Laplacian is the trace of the Hessian — basis-independent — it is the
sum of the three diagonal Hessian contractions in this frame
(`laplacian_sphereFrame_sum`). This is the frame half of the separation of variables:
the remaining work in `laplacian_separates` expresses each contraction through the
spherical-coordinate derivatives via the chart curves' velocities and accelerations. -/

/-- The radial unit vector `ê_r` of the spherical frame at `(θ, φ)`
    (`= sphereChart 1 θ φ`). -/
def sphereFrameR (θ φ : ℝ) : R3 := !₂[Real.sin θ * Real.cos φ, Real.sin θ * Real.sin φ, Real.cos θ]

/-- The polar unit vector `ê_θ` of the spherical frame at `(θ, φ)`. -/
def sphereFrameθ (θ φ : ℝ) : R3 := !₂[Real.cos θ * Real.cos φ, Real.cos θ * Real.sin φ, -Real.sin θ]

/-- The azimuthal unit vector `ê_φ` of the spherical frame at `φ`. -/
def sphereFrameφ (φ : ℝ) : R3 := !₂[-Real.sin φ, Real.cos φ, 0]

/-- The spherical orthonormal frame `(ê_r, ê_θ, ê_φ)` at `(θ, φ)` as a family. -/
def sphereFrame (θ φ : ℝ) : Fin 3 → R3 := ![sphereFrameR θ φ, sphereFrameθ θ φ, sphereFrameφ φ]

/-- The spherical frame is orthonormal, for every `(θ, φ)`. The six pairings reduce to the
    Pythagorean identity `sin² + cos² = 1` in `θ` and `φ`. -/
theorem sphereFrame_orthonormal (θ φ : ℝ) : Orthonormal ℝ (sphereFrame θ φ) := by
  rw [orthonormal_iff_ite]; intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [sphereFrame, sphereFrameR, sphereFrameθ, sphereFrameφ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq,
      if_true, if_false, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Fin.sum_univ_three]
  · linear_combination (Real.sin θ ^ 2) * Real.sin_sq_add_cos_sq φ + Real.sin_sq_add_cos_sq θ
  · linear_combination (Real.sin θ * Real.cos θ) * Real.sin_sq_add_cos_sq φ
  · ring
  · linear_combination (Real.sin θ * Real.cos θ) * Real.sin_sq_add_cos_sq φ
  · linear_combination (Real.cos θ ^ 2) * Real.sin_sq_add_cos_sq φ + Real.sin_sq_add_cos_sq θ
  · ring
  · ring
  · ring
  · linear_combination Real.sin_sq_add_cos_sq φ

/-- The spherical frame packaged as an `OrthonormalBasis` of `ℝ³` (three orthonormal vectors
    in a 3-dimensional space). -/
def sphereFrameONB (θ φ : ℝ) : OrthonormalBasis (Fin 3) ℝ R3 :=
  (basisOfOrthonormalOfCardEqFinrank (sphereFrame_orthonormal θ φ)
    (by rw [Fintype.card_fin, finrank_euclideanSpace_fin])).toOrthonormalBasis (by
      rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact sphereFrame_orthonormal θ φ)

@[simp] theorem sphereFrameONB_apply (θ φ : ℝ) (i : Fin 3) :
    sphereFrameONB θ φ i = sphereFrame θ φ i := by
  rw [sphereFrameONB, Module.Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]

/-- **Frame decomposition of the Laplacian.** At the chart point, `Δf` is the sum of the three
    diagonal Hessian contractions in the spherical orthonormal frame:

      `Δf(r,θ,φ) = D²f[ê_r,ê_r] + D²f[ê_θ,ê_θ] + D²f[ê_φ,ê_φ]`.

    This is `laplacian_eq_iteratedFDeriv_orthonormalBasis` specialized to `sphereFrameONB`.
    It is the basis-independent core of the spherical separation of variables: combined with the
    per-direction chain rule through the chart curves it yields `laplacian_separates`. -/
theorem laplacian_sphereFrame_sum (f : R3 → ℂ) (r θ φ : ℝ) :
    Δ f (sphereChart r θ φ)
      = iteratedFDeriv ℝ 2 f (sphereChart r θ φ) ![sphereFrameR θ φ, sphereFrameR θ φ]
        + iteratedFDeriv ℝ 2 f (sphereChart r θ φ) ![sphereFrameθ θ φ, sphereFrameθ θ φ]
        + iteratedFDeriv ℝ 2 f (sphereChart r θ φ) ![sphereFrameφ φ, sphereFrameφ φ] := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (sphereFrameONB θ φ)]
  simp only [Fin.sum_univ_three, sphereFrameONB_apply, sphereFrame, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-! ## Chart-curve calculus for the separation of variables

Helper lemmas (in `SphereSep`) that turn each diagonal Hessian contraction `D²f[ê,ê]`
into spherical-coordinate derivatives, via the chart curves `u ↦ sphereChart …` and the
second-order chain rule `iteratedDeriv_vcomp_two`. The chart velocities are
`ê_r, r ê_θ, r sinθ ê_φ`; the accelerations are `0, −r ê_r, −(r sinθ) v_ρ` (with
`v_ρ = sinθ ê_r + cosθ ê_θ`). -/

namespace SphereSep

attribute [local simp] PiLp.smul_apply PiLp.add_apply PiLp.toLp_apply
  Matrix.cons_val_zero Matrix.cons_val_one Matrix.head_cons Matrix.cons_val_two Matrix.tail_cons

/-- The horizontal radial direction `v_ρ = (cos φ, sin φ, 0)` at azimuth `φ`; it appears as
    the azimuthal acceleration and decomposes as `sin θ ê_r + cos θ ê_θ` (see `vρ_eq`). -/
def vρ (φ : ℝ) : R3 := !₂[cos φ, sin φ, 0]

/-- The standard basis vector `ê₁ = (1, 0, 0)` of `ℝ³`. -/
def e1 : R3 := !₂[1, 0, 0]

/-- The standard basis vector `ê₂ = (0, 1, 0)` of `ℝ³`. -/
def e2 : R3 := !₂[0, 1, 0]

/-- The standard basis vector `ê₃ = (0, 0, 1)` of `ℝ³`. -/
def e3 : R3 := !₂[0, 0, 1]

/-- The constant `Fin 2`-tuple `fun _ => w` equals the pair `![w, w]`. -/
lemma const_fin2 (w : R3) : (fun _ : Fin 2 => w) = ![w, w] := by funext i; fin_cases i <;> rfl

/-- Homogeneity of the diagonal second derivative in a scaled direction:
    `iteratedFDeriv 2 f x ![c•v, c•v] = c² • iteratedFDeriv 2 f x ![v, v]`. -/
lemma iFD2_smul_diag (f : R3 → ℂ) (x : R3) (c : ℝ) (v : R3) :
    iteratedFDeriv ℝ 2 f x ![c • v, c • v] = (c ^ 2 : ℝ) • iteratedFDeriv ℝ 2 f x ![v, v] := by
  have h : (![c • v, c • v] : Fin 2 → R3) = fun i => c • (![v, v] : Fin 2 → R3) i := by
    funext i; fin_cases i <;> rfl
  rw [h, ContinuousMultilinearMap.map_smul_univ]; congr 1
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Second-order chain rule along a curve: the 1D second derivative of `f ∘ γ` splits into the
    Hessian term `D²f[γ′, γ′]` plus the gradient acting on the curve's acceleration `γ″`. -/
lemma curve_jet (f : R3 → ℂ) (hf : ContDiff ℝ 2 f) {γ : ℝ → R3} {t₀ : ℝ}
    (hγ : ContDiffAt ℝ 2 γ t₀) :
    iteratedDeriv 2 (fun u => f (γ u)) t₀
      = iteratedFDeriv ℝ 2 f (γ t₀) ![deriv γ t₀, deriv γ t₀]
        + fderiv ℝ f (γ t₀) (iteratedDeriv 2 γ t₀) := by
  change iteratedDeriv 2 (f ∘ γ) t₀ = _
  rw [iteratedDeriv_vcomp_two hf.contDiffAt hγ, const_fin2]

/-- First-order chain rule along a curve: `(f ∘ γ)′ = Df[γ′]`. -/
lemma curve_deriv (f : R3 → ℂ) (hf : ContDiff ℝ 2 f) {γ : ℝ → R3} {t₀ : ℝ}
    (hγ : ContDiffAt ℝ 2 γ t₀) :
    deriv (fun u => f (γ u)) t₀ = fderiv ℝ f (γ t₀) (deriv γ t₀) :=
  (((hf.differentiable (by norm_num) (γ t₀)).hasFDerivAt).comp_hasDerivAt t₀
    ((hγ.differentiableAt (by norm_num)).hasDerivAt)).deriv

/-- The second iterated derivative is the second-order derivative: `iteratedDeriv 2 g = (g′)′`. -/
lemma id2_dd (g : ℝ → ℂ) (t : ℝ) : iteratedDeriv 2 g t = deriv (deriv g) t := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

/-- The radial chart curve `u ↦ sphereChart u θ φ` is the straight line `u ↦ u • ê_r`. -/
lemma chart_radial_eq (θ φ : ℝ) :
    (fun u => sphereChart u θ φ) = fun u => u • sphereFrameR θ φ := by
  funext u; refine PiLp.ext (fun i => ?_)
  fin_cases i <;> simp [sphereChart, sphereFrameR] <;> ring

/-- The radial chart curve is `C²` at every point. -/
lemma chart_radial_contDiffAt (θ φ t₀ : ℝ) :
    ContDiffAt ℝ 2 (fun u => sphereChart u θ φ) t₀ := by
  rw [chart_radial_eq]; exact (contDiff_id.smul contDiff_const).contDiffAt

/-- Velocity of the radial chart curve: `∂_r (sphereChart r θ φ) = ê_r`. -/
lemma chart_radial_deriv (θ φ t₀ : ℝ) :
    deriv (fun u => sphereChart u θ φ) t₀ = sphereFrameR θ φ := by
  rw [chart_radial_eq]
  have : HasDerivAt (fun s : ℝ => s • sphereFrameR θ φ) (sphereFrameR θ φ) t₀ := by
    simpa using (hasDerivAt_id t₀).smul_const (sphereFrameR θ φ)
  exact this.deriv

/-- Acceleration of the radial chart curve vanishes: `∂²_r (sphereChart r θ φ) = 0`
    (the radial curve is a straight line). -/
lemma chart_radial_iteratedDeriv (θ φ t₀ : ℝ) :
    iteratedDeriv 2 (fun u => sphereChart u θ φ) t₀ = 0 := by
  rw [chart_radial_eq, iteratedDeriv_succ, iteratedDeriv_one]
  have hd : deriv (fun s : ℝ => s • sphereFrameR θ φ) = fun _ => sphereFrameR θ φ :=
    funext fun u => by simpa using ((hasDerivAt_id u).smul_const (sphereFrameR θ φ)).deriv
  rw [hd]; simp

/-- The polar chart curve `u ↦ sphereChart r u φ` as `u ↦ (r sin u) v_ρ + (r cos u) ê₃`. -/
lemma chart_polar_eq (r φ : ℝ) :
    (fun u => sphereChart r u φ) = fun u => (r * sin u) • vρ φ + (r * cos u) • e3 := by
  funext u; refine PiLp.ext (fun i => ?_); fin_cases i <;> simp [sphereChart, vρ, e3]

/-- The radial chart curve is globally `C²`. -/
lemma chart_radial_contDiff (θ φ : ℝ) : ContDiff ℝ 2 (fun u => sphereChart u θ φ) := by
  rw [chart_radial_eq]; exact contDiff_id.smul contDiff_const

/-- The polar chart curve is `C²` at every angle. -/
lemma chart_polar_contDiffAt (r θ φ : ℝ) :
    ContDiffAt ℝ 2 (fun u => sphereChart r u φ) θ := by
  rw [chart_polar_eq]
  exact (((contDiff_const.mul Real.contDiff_sin).smul contDiff_const).add
    ((contDiff_const.mul Real.contDiff_cos).smul contDiff_const)).contDiffAt

/-- Velocity of the polar chart curve: `∂_θ (sphereChart r θ φ) = r ê_θ`. -/
lemma chart_polar_deriv (r θ φ : ℝ) :
    deriv (fun u => sphereChart r u φ) θ = r • sphereFrameθ θ φ := by
  rw [chart_polar_eq]
  have hv : HasDerivAt (fun u => (r * sin u) • vρ φ + (r * cos u) • e3)
      ((r * cos θ) • vρ φ + (r * (-sin θ)) • e3) θ :=
    (((Real.hasDerivAt_sin θ).const_mul r).smul_const (vρ φ)).add
      (((Real.hasDerivAt_cos θ).const_mul r).smul_const e3)
  rw [hv.deriv]
  refine PiLp.ext (fun i => ?_); fin_cases i <;> simp [vρ, e3, sphereFrameθ] <;> ring

/-- Acceleration of the polar chart curve: `∂²_θ (sphereChart r θ φ) = -r ê_r`. -/
lemma chart_polar_iteratedDeriv (r θ φ : ℝ) :
    iteratedDeriv 2 (fun u => sphereChart r u φ) θ = (-r) • sphereFrameR θ φ := by
  rw [chart_polar_eq, iteratedDeriv_succ, iteratedDeriv_one]
  have hd : deriv (fun u => (r * sin u) • vρ φ + (r * cos u) • e3)
      = fun u => (r * cos u) • vρ φ + (r * (-sin u)) • e3 := by
    funext u
    exact ((((Real.hasDerivAt_sin u).const_mul r).smul_const (vρ φ)).add
      (((Real.hasDerivAt_cos u).const_mul r).smul_const e3)).deriv
  rw [hd]
  have ha : HasDerivAt (fun u => (r * cos u) • vρ φ + (r * (-sin u)) • e3)
      ((r * (-sin θ)) • vρ φ + (r * (-cos θ)) • e3) θ :=
    (((Real.hasDerivAt_cos θ).const_mul r).smul_const (vρ φ)).add
      (((Real.hasDerivAt_sin θ).neg.const_mul r).smul_const e3)
  rw [ha.deriv]
  refine PiLp.ext (fun i => ?_); fin_cases i <;> simp [vρ, e3, sphereFrameR] <;> ring

/-- The azimuthal chart curve `u ↦ sphereChart r θ u` in standard-basis form
    `u ↦ (r sinθ cos u) ê₁ + (r sinθ sin u) ê₂ + (r cosθ) ê₃`. -/
lemma chart_azim_eq (r θ : ℝ) :
    (fun u => sphereChart r θ u)
      = fun u => ((r * sin θ) * cos u) • e1 + ((r * sin θ) * sin u) • e2 + (r * cos θ) • e3 := by
  funext u; refine PiLp.ext (fun i => ?_); fin_cases i <;> simp [sphereChart, e1, e2, e3]

/-- The azimuthal chart curve is `C²` at every angle. -/
lemma chart_azim_contDiffAt (r θ φ : ℝ) :
    ContDiffAt ℝ 2 (fun u => sphereChart r θ u) φ := by
  rw [chart_azim_eq]
  exact ((((contDiff_const.mul Real.contDiff_cos).smul contDiff_const).add
    ((contDiff_const.mul Real.contDiff_sin).smul contDiff_const)).add contDiff_const).contDiffAt

/-- Velocity of the azimuthal chart curve: `∂_φ (sphereChart r θ φ) = (r sinθ) ê_φ`. -/
lemma chart_azim_deriv (r θ φ : ℝ) :
    deriv (fun u => sphereChart r θ u) φ = (r * sin θ) • sphereFrameφ φ := by
  rw [chart_azim_eq]
  have hv : HasDerivAt
      (fun u => ((r * sin θ) * cos u) • e1 + ((r * sin θ) * sin u) • e2 + (r * cos θ) • e3)
      (((r * sin θ) * (-sin φ)) • e1 + ((r * sin θ) * cos φ) • e2 + (0 : R3)) φ :=
    ((((Real.hasDerivAt_cos φ).const_mul (r * sin θ)).smul_const e1).add
      (((Real.hasDerivAt_sin φ).const_mul (r * sin θ)).smul_const e2)).add
      (hasDerivAt_const φ ((r * cos θ) • e3))
  rw [hv.deriv]
  refine PiLp.ext (fun i => ?_); fin_cases i <;> simp [e1, e2, sphereFrameφ]

/-- Acceleration of the azimuthal chart curve: `∂²_φ (sphereChart r θ φ) = -(r sinθ) v_ρ`. -/
lemma chart_azim_iteratedDeriv (r θ φ : ℝ) :
    iteratedDeriv 2 (fun u => sphereChart r θ u) φ = (-(r * sin θ)) • vρ φ := by
  rw [chart_azim_eq, iteratedDeriv_succ, iteratedDeriv_one]
  have hd : deriv
      (fun u => ((r * sin θ) * cos u) • e1 + ((r * sin θ) * sin u) • e2 + (r * cos θ) • e3)
      = fun u => ((r * sin θ) * (-sin u)) • e1 + ((r * sin θ) * cos u) • e2 + (0 : R3) := by
    funext u
    exact (((((Real.hasDerivAt_cos u).const_mul (r * sin θ)).smul_const e1).add
      (((Real.hasDerivAt_sin u).const_mul (r * sin θ)).smul_const e2)).add
      (hasDerivAt_const u ((r * cos θ) • e3))).deriv
  rw [hd]
  have ha : HasDerivAt
      (fun u => ((r * sin θ) * (-sin u)) • e1 + ((r * sin θ) * cos u) • e2 + (0 : R3))
      (((r * sin θ) * (-cos φ)) • e1 + ((r * sin θ) * (-sin φ)) • e2 + (0 : R3)) φ :=
    ((((Real.hasDerivAt_sin φ).neg.const_mul (r * sin θ)).smul_const e1).add
      (((Real.hasDerivAt_cos φ).const_mul (r * sin θ)).smul_const e2)).add
      (hasDerivAt_const φ (0 : R3))
  rw [ha.deriv]
  refine PiLp.ext (fun i => ?_); fin_cases i <;> simp [e1, e2, vρ]

/-- Decomposition of the horizontal radial direction in the spherical frame:
    `v_ρ = sin θ ê_r + cos θ ê_θ`. -/
lemma vρ_eq (θ φ : ℝ) : vρ φ = sin θ • sphereFrameR θ φ + cos θ • sphereFrameθ θ φ := by
  refine PiLp.ext (fun i => ?_); fin_cases i <;> simp [vρ, sphereFrameR, sphereFrameθ]
  · linear_combination (-cos φ) * sin_sq_add_cos_sq θ
  · linear_combination (-sin φ) * sin_sq_add_cos_sq θ
  · ring

/-- Radial second jet: since the radial curve has zero acceleration, its 1D second derivative
    is the pure Hessian contraction `D²f[ê_r, ê_r]`. -/
lemma jet_radial (f : R3 → ℂ) (hf : ContDiff ℝ 2 f) (r θ φ : ℝ) :
    iteratedDeriv 2 (fun u => f (sphereChart u θ φ)) r
      = iteratedFDeriv ℝ 2 f (sphereChart r θ φ) ![sphereFrameR θ φ, sphereFrameR θ φ] := by
  rw [curve_jet f hf (chart_radial_contDiffAt θ φ r), chart_radial_deriv,
    chart_radial_iteratedDeriv]; simp

/-- Radial first jet: `∂_r (f ∘ chart) = Df[ê_r]`. -/
lemma fst_radial (f : R3 → ℂ) (hf : ContDiff ℝ 2 f) (r θ φ : ℝ) :
    deriv (fun u => f (sphereChart u θ φ)) r
      = fderiv ℝ f (sphereChart r θ φ) (sphereFrameR θ φ) := by
  rw [curve_deriv f hf (chart_radial_contDiffAt θ φ r), chart_radial_deriv]

/-- Polar first jet: `∂_θ (f ∘ chart) = r · Df[ê_θ]`. -/
lemma fst_polar (f : R3 → ℂ) (hf : ContDiff ℝ 2 f) (r θ φ : ℝ) :
    deriv (fun u => f (sphereChart r u φ)) θ
      = r • fderiv ℝ f (sphereChart r θ φ) (sphereFrameθ θ φ) := by
  rw [curve_deriv f hf (chart_polar_contDiffAt r θ φ), chart_polar_deriv, map_smul]

/-- The polar chart curve is globally `C²`. -/
lemma chart_polar_contDiff (r φ : ℝ) : ContDiff ℝ 2 (fun u => sphereChart r u φ) := by
  rw [chart_polar_eq]
  exact ((contDiff_const.mul Real.contDiff_sin).smul contDiff_const).add
    ((contDiff_const.mul Real.contDiff_cos).smul contDiff_const)

/-- The azimuthal chart curve is globally `C²`. -/
lemma chart_azim_contDiff (r θ : ℝ) : ContDiff ℝ 2 (fun u => sphereChart r θ u) := by
  rw [chart_azim_eq]
  exact (((contDiff_const.mul Real.contDiff_cos).smul contDiff_const).add
    ((contDiff_const.mul Real.contDiff_sin).smul contDiff_const)).add contDiff_const

/-- The angular Laplacian `laplaceBeltrami` of `f` pulled back to the chart, written through the
    1D polar and azimuthal derivatives of `f ∘ chart`. -/
lemma lapBeltrami_chart (f : R3 → ℂ) (hf : ContDiff ℝ 2 f) (r θ φ : ℝ) :
    laplaceBeltrami (fun p => f (sphereChart r p.1 p.2)) (θ, φ)
      = -((1 / (sin θ : ℂ)) * ((cos θ : ℂ) * deriv (fun u => f (sphereChart r u φ)) θ
            + (sin θ : ℂ) * iteratedDeriv 2 (fun u => f (sphereChart r u φ)) θ)
          + (1 / (sin θ : ℂ) ^ 2) * iteratedDeriv 2 (fun u => f (sphereChart r θ u)) φ) := by
  have hFθ : ContDiff ℝ 2 (fun u => f (sphereChart r u φ)) := hf.comp (chart_polar_contDiff r φ)
  have hprod : deriv (fun t => (sin t : ℂ) * deriv (fun u => f (sphereChart r u φ)) t) θ
      = (cos θ : ℂ) * deriv (fun u => f (sphereChart r u φ)) θ
        + (sin θ : ℂ) * iteratedDeriv 2 (fun u => f (sphereChart r u φ)) θ := by
    have hsinc : HasDerivAt (fun t => (sin t : ℂ)) (cos θ : ℂ) θ := by
      simpa using (Real.hasDerivAt_sin θ).ofReal_comp
    have hdF : HasDerivAt (deriv (fun u => f (sphereChart r u φ)))
        (iteratedDeriv 2 (fun u => f (sphereChart r u φ)) θ) θ := by
      rw [id2_dd]; exact (hFθ.differentiable_deriv_two θ).hasDerivAt
    have hmul : HasDerivAt (fun t => (sin t : ℂ) * deriv (fun u => f (sphereChart r u φ)) t)
        ((cos θ : ℂ) * deriv (fun u => f (sphereChart r u φ)) θ
          + (sin θ : ℂ) * iteratedDeriv 2 (fun u => f (sphereChart r u φ)) θ) θ :=
      hsinc.mul hdF
    exact hmul.deriv
  have hsec : deriv (deriv (fun q => f (sphereChart r θ q))) φ
      = iteratedDeriv 2 (fun u => f (sphereChart r θ u)) φ := (id2_dd _ φ).symm
  rw [laplaceBeltrami]
  simp only [hprod, hsec]

/-- Polar second jet: `∂²_θ (f ∘ chart) = r² · D²f[ê_θ, ê_θ] + Df[(-r) ê_r]`, combining the
    velocity `r ê_θ` (Hessian term) with the acceleration `-r ê_r` (gradient term). -/
lemma jet_polar (f : R3 → ℂ) (hf : ContDiff ℝ 2 f) (r θ φ : ℝ) :
    iteratedDeriv 2 (fun u => f (sphereChart r u φ)) θ
      = (r ^ 2 : ℝ) • iteratedFDeriv ℝ 2 f (sphereChart r θ φ) ![sphereFrameθ θ φ, sphereFrameθ θ φ]
        + fderiv ℝ f (sphereChart r θ φ) ((-r) • sphereFrameR θ φ) := by
  rw [curve_jet f hf (chart_polar_contDiffAt r θ φ), chart_polar_deriv, chart_polar_iteratedDeriv,
    iFD2_smul_diag]

/-- Azimuthal second jet: `∂²_φ (f ∘ chart) = (r sinθ)² · D²f[ê_φ, ê_φ] + Df[-(r sinθ) v_ρ]`,
    combining the velocity `(r sinθ) ê_φ` (Hessian term) with the acceleration `-(r sinθ) v_ρ`. -/
lemma jet_azim (f : R3 → ℂ) (hf : ContDiff ℝ 2 f) (r θ φ : ℝ) :
    iteratedDeriv 2 (fun u => f (sphereChart r θ u)) φ
      = ((r * sin θ) ^ 2 : ℝ) • iteratedFDeriv ℝ 2 f (sphereChart r θ φ)
          ![sphereFrameφ φ, sphereFrameφ φ]
        + fderiv ℝ f (sphereChart r θ φ) ((-(r * sin θ)) • vρ φ) := by
  rw [curve_jet f hf (chart_azim_contDiffAt r θ φ), chart_azim_deriv, chart_azim_iteratedDeriv,
    iFD2_smul_diag]

end SphereSep

/-! ## The separation identity -/

open SphereSep

/-- **Separation of the Laplacian in spherical coordinates.**

    `Δf = (1/r²)∂_r(r²∂_r f) − (1/r²) L̂²f`, with `L̂² = laplaceBeltrami` the angular
    Laplacian (Condon–Shortley sign, so `L̂² Y_ℓ^m = +ℓ(ℓ+1) Y_ℓ^m`). This is the
    textbook separation of variables, here fully derived: the basis-independent frame
    decomposition `laplacian_sphereFrame_sum` reduces `Δf` to the three diagonal Hessian
    contractions, and the `SphereSep` chart-curve lemmas express each through the radial
    and angular derivatives (the gradient cross-terms cancel). -/
theorem laplacian_separates (f : R3 → ℂ) (hf : ContDiff ℝ 2 f)
    {r θ φ : ℝ} (hr : 0 < r) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    Δ f (sphereChart r θ φ)
      = (1 / (r : ℂ) ^ 2) *
          deriv (fun s : ℝ => (s : ℂ) ^ 2 * deriv (fun u : ℝ => f (sphereChart u θ φ)) s) r
        - (1 / (r : ℂ) ^ 2) *
          laplaceBeltrami (fun p : ℝ × ℝ => f (sphereChart r p.1 p.2)) (θ, φ) := by
  have hr0 : (r : ℝ) ≠ 0 := hr.ne'
  have hsin : sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne'
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0
  have hsinC : (sin θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsin
  have hFr : ContDiff ℝ 2 (fun u => f (sphereChart u θ φ)) := hf.comp (chart_radial_contDiff θ φ)
  rw [laplacian_sphereFrame_sum f r θ φ,
    radialPart_eq (fun u => f (sphereChart u θ φ)) hFr hr0,
    lapBeltrami_chart f hf r θ φ, ← id2_dd, jet_radial f hf, fst_radial f hf,
    jet_polar f hf, fst_polar f hf, jet_azim f hf, vρ_eq θ φ]
  simp only [map_smul, map_neg, map_add, neg_smul, Complex.real_smul,
    Complex.ofReal_mul, Complex.ofReal_pow]
  field_simp
  ring



end Spectra.QuantumMechanics.Hydrogen
