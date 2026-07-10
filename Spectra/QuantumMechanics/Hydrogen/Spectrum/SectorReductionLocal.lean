/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Spectrum.Eigenvalue
import Spectra.QuantumMechanics.Hydrogen.Laplacian.SolidHarmonic

/-!
# Local sector reduction of the hydrogen Hamiltonian

The lemmas `laplacian_in_sector` / `hydrogen_reduces` / `hydrogen_reduces_half`
(`Spectrum/Eigenvalue.lean`) reduce the Laplacian and the hydrogen Hamiltonian to the radial
operator on an angular sector, but require the *global* separation hypothesis

  `∀ a b c, f (sphereChart a b c) = R a · Yℓᵐ(b, c)`.

For the **forward direction** of the discrete-spectrum theorem this hypothesis is unusable:
a globally `C²` separated function with that property does not exist for odd `m` (the chart is
many-to-one, and `R(a)·Yℓᵐ(b,c)` — through the `√(1−cos²b)^m = |sin b|^m` factor in the surface
harmonic — is multivalued on a given point of `ℝ³`). The smooth solid harmonic
`χ(‖x‖)·solidHarmonicNat ℓ m x` only realizes the separation on the *physical* chart domain
`{r > 0, θ ∈ (0,π)}` — i.e. *near* the evaluation point.

This file provides **local** versions, where the separation is supplied only as an `EventuallyEq`
along the radial curve (`u ↦ f (sphereChart u θ φ)` near `u = r`) and the angular surface
(`(b,c) ↦ f (sphereChart r b c)` near `(θ,φ)`). The point is that the underlying operators are
*local*: `laplacian_separates` is hypothesis-free, and `laplaceBeltrami` is built from `deriv`, so
both respect eventual equality.

## Main statements

* `laplaceBeltrami_congr` — `laplaceBeltrami` respects `EventuallyEq` at a point.
* `laplacian_in_sector_local` — the `−Δ` reduction with local separation.
* `hydrogen_reduces_half_local` — the half-Laplacian hydrogen Hamiltonian reduction with local
  separation.
* `solidTest_contDiff` — the smooth separated test function `χ(‖x‖) · solidHarmonicNat ℓ m x` is
  globally `C²`.
* `solidTest_reduces_half` — the local half-Laplacian reduction specialized to that test function
  (the form consumed by the forward direction's sector projection).
-/

open Spectra.QuantumMechanics.Hydrogen
open Spectra.SphericalHarmonics
open scoped Laplacian ContDiff Topology

namespace Spectra.QuantumMechanics.Hydrogen

/-- **`laplaceBeltrami` is a local operator**: it respects eventual equality at a point. -/
lemma laplaceBeltrami_congr {Y₁ Y₂ : ℝ × ℝ → ℂ} {p : ℝ × ℝ} (h : Y₁ =ᶠ[𝓝 p] Y₂) :
    laplaceBeltrami Y₁ p = laplaceBeltrami Y₂ p := by
  have hg₁ : Filter.Tendsto (fun s => (s, p.2)) (𝓝 p.1) (𝓝 p) := by
    simpa using (continuous_id.prodMk continuous_const).tendsto p.1
  have hg₂ : Filter.Tendsto (fun q => (p.1, q)) (𝓝 p.2) (𝓝 p) := by
    simpa using (continuous_const.prodMk continuous_id).tendsto p.2
  have slice₁ : (fun s => Y₁ (s, p.2)) =ᶠ[𝓝 p.1] (fun s => Y₂ (s, p.2)) := hg₁.eventually h
  have slice₂ : (fun q => Y₁ (p.1, q)) =ᶠ[𝓝 p.2] (fun q => Y₂ (p.1, q)) := hg₂.eventually h
  have hA' : deriv (fun t => (Real.sin t : ℂ) * deriv (fun s => Y₁ (s, p.2)) t) p.1
           = deriv (fun t => (Real.sin t : ℂ) * deriv (fun s => Y₂ (s, p.2)) t) p.1 := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [slice₁.deriv] with t ht
    rw [ht]
  have hB' : deriv (deriv (fun q => Y₁ (p.1, q))) p.2 = deriv (deriv (fun q => Y₂ (p.1, q))) p.2 :=
    Filter.EventuallyEq.deriv_eq slice₂.deriv
  unfold laplaceBeltrami
  rw [hA', hB']

/-- **Local sector reduction of `−Δ`.** Same as `laplacian_in_sector` but the separation only
needs to hold *near* the evaluation point (as `EventuallyEq` along the radial curve and the angular
surface), which is what a globally-smooth separated test function can provide. -/
theorem laplacian_in_sector_local (ℓ : ℕ) (m : ℤ) (hm : |m| ≤ ℓ)
    (R : ℝ → ℂ) (hR : ContDiff ℝ 2 R)
    (f : Spectra.Sobolev.R3 → ℂ) (hf : ContDiff ℝ 2 f)
    {r θ φ : ℝ} (hr : 0 < r) (hθ : θ ∈ Set.Ioo 0 Real.pi)
    (hcurve : (fun u => f (sphereChart u θ φ)) =ᶠ[𝓝 r]
        (fun u => R u * SphericalHarmonic ℓ m hm (θ, φ)))
    (hsurf : (fun q : ℝ × ℝ => f (sphereChart r q.1 q.2)) =ᶠ[𝓝 (θ, φ)]
        (fun q => R r * SphericalHarmonic ℓ m hm q)) :
    Δ f (sphereChart r θ φ)
      = (deriv (deriv R) r + (2 / (r : ℂ)) * deriv R r
          - ((ℓ * (ℓ + 1) : ℝ) / (r : ℂ) ^ 2) * R r) * SphericalHarmonic ℓ m hm (θ, φ) := by
  have hr0 : (r : ℝ) ≠ 0 := hr.ne'
  have hRp : ContDiff ℝ 2 (fun s => R s * SphericalHarmonic ℓ m hm (θ, φ)) := hR.mul contDiff_const
  have hd1 : ∀ s, deriv (fun u => R u * SphericalHarmonic ℓ m hm (θ, φ)) s
      = deriv R s * SphericalHarmonic ℓ m hm (θ, φ) := fun s =>
    ((hR.differentiable (by norm_num) s).hasDerivAt.mul_const _).deriv
  have hd2 : deriv (deriv (fun u => R u * SphericalHarmonic ℓ m hm (θ, φ))) r
      = deriv (deriv R) r * SphericalHarmonic ℓ m hm (θ, φ) := by
    have hfun : deriv (fun u => R u * SphericalHarmonic ℓ m hm (θ, φ))
        = fun s => deriv R s * SphericalHarmonic ℓ m hm (θ, φ) := funext hd1
    rw [hfun]
    exact ((hR.differentiable_deriv_two r).hasDerivAt.mul_const _).deriv
  have hA : deriv (fun s : ℝ => (s : ℂ) ^ 2 * deriv (fun u => f (sphereChart u θ φ)) s) r
          = deriv (fun s : ℝ => (s : ℂ) ^ 2 *
              deriv (fun u => R u * SphericalHarmonic ℓ m hm (θ, φ)) s) r := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hcurve.deriv] with s hs
    rw [hs]
  rw [laplacian_separates f hf hr hθ, hA, laplaceBeltrami_congr hsurf,
    radialPart_eq (fun s => R s * SphericalHarmonic ℓ m hm (θ, φ)) hRp hr0,
    laplaceBeltrami_const_mul (R r) (SphericalHarmonic ℓ m hm) (θ, φ),
    sphericalHarmonic_eigenvalue ℓ m hm (θ, φ) hθ, hd2, hd1 r]
  ring

/-- **Local sector reduction of the half-Laplacian hydrogen Hamiltonian.** The
`hydrogen_reduces_half` identity with separation required only *near* the evaluation point — the
form usable with a globally smooth separated test function (e.g.
`χ(‖x‖) · solidHarmonicNat ℓ m x`). -/
theorem hydrogen_reduces_half_local (p : CoulombParams) (ℓ : ℕ) (m : ℤ) (hm : |m| ≤ ℓ)
    (R : ℝ → ℂ) (hR : ContDiff ℝ 2 R)
    (f : Spectra.Sobolev.R3 → ℂ) (hf : ContDiff ℝ 2 f)
    {r θ φ : ℝ} (hr : 0 < r) (hθ : θ ∈ Set.Ioo 0 Real.pi)
    (hcurve : (fun u => f (sphereChart u θ φ)) =ᶠ[𝓝 r]
        (fun u => R u * SphericalHarmonic ℓ m hm (θ, φ)))
    (hsurf : (fun q : ℝ × ℝ => f (sphereChart r q.1 q.2)) =ᶠ[𝓝 (θ, φ)]
        (fun q => R r * SphericalHarmonic ℓ m hm q)) :
    ((-(1 / 2 : ℂ)) * Δ f (sphereChart r θ φ))
        + (coulombMultiplier p (sphereChart r θ φ) : ℂ) * f (sphereChart r θ φ)
      = ((-(1 / 2 : ℂ)) * (deriv (deriv R) r) - (1 / (r : ℂ)) * deriv R r
          + (((ℓ * (ℓ + 1) : ℝ) / (2 * (r : ℂ) ^ 2)) - (p.Z : ℂ) / (r : ℂ)) * R r)
        * SphericalHarmonic ℓ m hm (θ, φ) := by
  have hpt : f (sphereChart r θ φ) = R r * SphericalHarmonic ℓ m hm (θ, φ) := by
    have := hsurf.eq_of_nhds; simpa using this
  have hnorm : ‖sphereChart r θ φ‖ = r := by rw [norm_sphereChart, abs_of_pos hr]
  have hne : ‖sphereChart r θ φ‖ ≠ 0 := by rw [hnorm]; exact hr.ne'
  have hcoul : (coulombMultiplier p (sphereChart r θ φ) : ℂ) * f (sphereChart r θ φ)
      = (-(p.Z : ℂ) / (r : ℂ) * R r) * SphericalHarmonic ℓ m hm (θ, φ) := by
    have hval : coulombMultiplier p (sphereChart r θ φ) = -p.Z / ‖sphereChart r θ φ‖ := by
      unfold coulombMultiplier; exact if_neg hne
    rw [hval, hnorm, hpt]; push_cast; ring
  rw [laplacian_in_sector_local ℓ m hm R hR f hf hr hθ hcurve hsurf, hcoul]
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp
  ring

/-! ## The solid-harmonic test function

The concrete instance of the local reduction used by the forward direction: the smooth, separated
test function `χ(‖x‖) · solidHarmonicNat ℓ m x` (with `χ` a smooth radial cutoff vanishing near the
origin). It is globally `C²`, and on the physical chart domain it realizes the separation with
radial profile `R a = χ(a)·a^ℓ`, so the local half-Laplacian reduction applies. -/

/-- The smooth separated test function `χ(‖x‖) · solidHarmonicNat ℓ m x` is globally `C²`. -/
lemma solidTest_contDiff (ℓ m : ℕ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχ0 : ∀ᶠ s in 𝓝 (0 : ℝ), χ s = 0) :
    ContDiff ℝ 2 (fun x : Spectra.Sobolev.R3 => (χ ‖x‖ : ℂ) * solidHarmonicNat ℓ m x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · have hev : (fun x : Spectra.Sobolev.R3 => (χ ‖x‖ : ℂ) * solidHarmonicNat ℓ m x)
        =ᶠ[𝓝 x] (fun _ => 0) := by
      have htend : Filter.Tendsto (fun y : Spectra.Sobolev.R3 => ‖y‖) (𝓝 x) (𝓝 0) := by
        rw [hx]; simpa using (continuous_norm (E := Spectra.Sobolev.R3)).tendsto 0
      filter_upwards [htend.eventually hχ0] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have h2le : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
    have hnorm : ContDiffAt ℝ 2 (fun y : Spectra.Sobolev.R3 => ‖y‖) x := contDiffAt_norm ℝ hx
    have h1 : ContDiffAt ℝ 2 (fun y : Spectra.Sobolev.R3 => (χ ‖y‖ : ℂ)) x :=
      Complex.ofRealCLM.contDiff.comp_contDiffAt x ((hχ.of_le h2le).comp_contDiffAt x hnorm)
    have h2 : ContDiffAt ℝ 2 (solidHarmonicNat ℓ m) x :=
      ((solidHarmonicNat_contDiffOn ℓ m).contDiffAt
        (isOpen_compl_singleton.mem_nhds hx)).of_le h2le
    exact h1.mul h2

/-- **Sector reduction for the solid-harmonic test function.** Applying the local half-Laplacian
reduction to `f = χ(‖·‖)·solidHarmonicNat ℓ m` (a globally smooth, separated test function) with
radial profile `R a = χ(a)·a^ℓ`: at every interior chart point the hydrogen Hamiltonian acts as the
radial operator on `R`, tensored with `Yℓᵐ`. This is the form fed into the forward direction's
sector projection. -/
theorem solidTest_reduces_half (p : CoulombParams) (ℓ m : ℕ) (hm : m ≤ ℓ)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ᶠ s in 𝓝 (0 : ℝ), χ s = 0)
    {r θ φ : ℝ} (hr : 0 < r) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    ((-(1 / 2 : ℂ)) * Δ (fun x => (χ ‖x‖ : ℂ) * solidHarmonicNat ℓ m x) (sphereChart r θ φ))
        + (coulombMultiplier p (sphereChart r θ φ) : ℂ)
          * ((χ ‖sphereChart r θ φ‖ : ℂ) * solidHarmonicNat ℓ m (sphereChart r θ φ))
      = ((-(1 / 2 : ℂ)) * deriv (deriv (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ)) r
          - (1 / (r : ℂ)) * deriv (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ) r
          + (((ℓ * (ℓ + 1) : ℝ) / (2 * (r : ℂ) ^ 2)) - (p.Z : ℂ) / (r : ℂ))
            * ((χ r : ℂ) * (r : ℂ) ^ ℓ))
        * SphericalHarmonic ℓ (m : ℤ) (by simpa using hm) (θ, φ) := by
  have hm' : |(m : ℤ)| ≤ (ℓ : ℤ) := by simpa using hm
  have hf : ContDiff ℝ 2 (fun x : Spectra.Sobolev.R3 => (χ ‖x‖ : ℂ) * solidHarmonicNat ℓ m x) :=
    solidTest_contDiff ℓ m χ hχ hχ0
  have h2le : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hR : ContDiff ℝ 2 (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ) :=
    (Complex.ofRealCLM.contDiff.comp (hχ.of_le h2le)).mul (Complex.ofRealCLM.contDiff.pow ℓ)
  have hcurve : (fun u => (fun x => (χ ‖x‖ : ℂ) * solidHarmonicNat ℓ m x) (sphereChart u θ φ))
      =ᶠ[𝓝 r]
      (fun u => (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ) u * SphericalHarmonic ℓ (m : ℤ) hm' (θ, φ)) := by
    filter_upwards [Ioi_mem_nhds hr] with u hu
    have hu0 : (0 : ℝ) < u := hu
    change (χ ‖sphereChart u θ φ‖ : ℂ) * solidHarmonicNat ℓ m (sphereChart u θ φ)
        = ((χ u : ℂ) * (u : ℂ) ^ ℓ) * SphericalHarmonic ℓ (m : ℤ) hm' (θ, φ)
    rw [norm_sphereChart, abs_of_pos hu0, solidHarmonicNat_sphereChart ℓ m hm hu0 hθ]
    ring
  have hsurf : (fun q : ℝ × ℝ => (fun x => (χ ‖x‖ : ℂ) * solidHarmonicNat ℓ m x)
        (sphereChart r q.1 q.2))
      =ᶠ[𝓝 (θ, φ)] (fun q => (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ) r
        * SphericalHarmonic ℓ (m : ℤ) hm' q) := by
    have hU : {q : ℝ × ℝ | q.1 ∈ Set.Ioo 0 Real.pi} ∈ 𝓝 (θ, φ) :=
      (isOpen_Ioo.preimage continuous_fst).mem_nhds hθ
    filter_upwards [hU] with q hq
    show (χ ‖sphereChart r q.1 q.2‖ : ℂ) * solidHarmonicNat ℓ m (sphereChart r q.1 q.2)
        = ((χ r : ℂ) * (r : ℂ) ^ ℓ) * SphericalHarmonic ℓ (m : ℤ) hm' q
    rw [norm_sphereChart, abs_of_pos hr, solidHarmonicNat_sphereChart ℓ m hm hr hq]
    ring
  exact hydrogen_reduces_half_local p ℓ (m : ℤ) hm' (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ) hR
    (fun x => (χ ‖x‖ : ℂ) * solidHarmonicNat ℓ m x) hf hr hθ hcurve hsurf

end Spectra.QuantumMechanics.Hydrogen
