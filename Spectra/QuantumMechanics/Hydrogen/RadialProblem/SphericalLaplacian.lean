/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Spectra.SobolevSpaces.WeakDerivative
import Spectra.SphericalHarmonics.Basic
/-!
# Separation of the Laplacian in spherical coordinates (scaffolding)

The spherical-coordinate chart and the pointwise separation of the 3D Laplacian
`−Δ = −(1/r²)∂_r(r²∂_r) + L̂²/r²`, where `L̂² = laplaceBeltrami` is the angular
Laplacian from `SphericalHarmonics/Basic.lean`.

## What is proved here

* `sphereChart` — the chart `(r, θ, φ) ↦ (r sinθ cosφ, r sinθ sinφ, r cosθ) : ℝ³`.
* `norm_sphereChart` — `‖sphereChart r θ φ‖ = |r|`.
* `radialPart_eq` — the radial operator in divergence form, `(1/r²)∂_r(r²∂_r R) = R″ + (2/r)R′`.
* `iteratedFDeriv_two_line` — the line-restriction bridge: the directional second
  derivative `iteratedFDeriv 2 F x ![v,v]` is the 1D `(d²/dt²)F(x+t·v)|₀`.
* `laplacian_comp_normSq` — **the radial Laplacian** `Δ(g∘‖·‖²) = 4‖x‖²·g″(‖x‖²) + 6·g′(‖x‖²)`
  on `ℝ³`, for globally `C²` `g`. This is the genuine analytic core (the orthonormal-basis
  Laplacian sum, the per-direction 1D chain rule, and Parseval), done without any
  norm-Hessian — by parametrizing the radial profile through the globally smooth `‖·‖²`.

## Documented gaps

* `laplacian_comp_norm` — the `‖·‖` form `Δ(g∘‖·‖) = g″ + (2/r)g′` on `ℝ³ \ {0}`. The
  analytic content is `laplacian_comp_normSq` with `g∘√`; only the localization of `√`'s
  singularity at the origin (a `C²` extension + locality of `Δ`) is deferred.
* `laplacian_separates` — the full pointwise separation on the chart (radial half via
  `radialPart_eq` ∘ `laplacian_comp_norm`, angular half via `laplaceBeltrami`).

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics IV*][reed1978], §XIII.3.
-/

noncomputable section

open MeasureTheory Real InnerProductSpace Laplacian
open Spectra.Sobolev Spectra.SphericalHarmonics
open scoped RealInnerProductSpace

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

    **The analytic core is done** — `laplacian_comp_normSq` proves the same identity in
    the `‖·‖²` variable (`Δ(h∘‖·‖²) = 4‖x‖²h″ + 6h′`), and setting `h = g∘√` (so
    `g‖y‖ = h(‖y‖²)`) gives exactly `g″(‖x‖) + (2/‖x‖)g′(‖x‖)` after the `√` chain rule.

    **[Remaining gap — localization across the origin.]** The reduction needs `h = g∘√`
    to be globally `C²` to feed `laplacian_comp_normSq`, but `√` is singular at `0`. Away
    from `x ≠ 0` one replaces `√` by a global `C²` function agreeing with it near `‖x‖²`
    and uses locality of `Δ`; building that extension (a `C²` mollification of `√`) is the
    only deferred step. No norm-Hessian or missing-infrastructure obstruction remains. -/
theorem laplacian_comp_norm (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) {x : R3} (hx : x ≠ 0) :
    Δ (fun y : R3 => g ‖y‖) x = iteratedDeriv 2 g ‖x‖ + (2 / (‖x‖ : ℂ)) * deriv g ‖x‖ := by
  sorry

/-! ## The separation identity -/

/-- **[Pure-calculus gap — separation of the Laplacian.]**

    The full pointwise separation in spherical coordinates:
    `Δf = (1/r²)∂_r(r²∂_r f) − (1/r²) L̂²f`,
    where `L̂² = laplaceBeltrami` carries the Condon–Shortley minus sign so that
    `L̂² Y_ℓ^m = +ℓ(ℓ+1) Y_ℓ^m` (`sphericalHarmonic_eigenvalue`). Equivalently, in the
    physics convention, `−Δ = −(1/r²)∂_r(r²∂_r) + L̂²/r²`.

    The chart `sphereChart` is smooth and the identity is the chain rule for `Δ` through
    it: the radial half is `radialPart_eq` composed with `laplacian_comp_norm` (whose
    analytic core `laplacian_comp_normSq` is **proved**); the angular half is the
    `(θ,φ)`-derivatives of `f ∘ sphereChart` matching `laplaceBeltrami`. Deferred pending
    the same origin-localization as `laplacian_comp_norm` plus the chart Jacobian
    bookkeeping. -/
theorem laplacian_separates (f : R3 → ℂ) (hf : ContDiff ℝ 2 f)
    {r θ φ : ℝ} (hr : 0 < r) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    Δ f (sphereChart r θ φ)
      = (1 / (r : ℂ) ^ 2) *
          deriv (fun s : ℝ => (s : ℂ) ^ 2 * deriv (fun u : ℝ => f (sphereChart u θ φ)) s) r
        - (1 / (r : ℂ) ^ 2) *
          laplaceBeltrami (fun p : ℝ × ℝ => f (sphereChart r p.1 p.2)) (θ, φ) := by
  sorry

end Spectra.QuantumMechanics.Hydrogen
