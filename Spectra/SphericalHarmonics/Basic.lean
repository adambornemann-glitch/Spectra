/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SphericalHarmonics.AssociatedLegendre
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
/-!
# Spherical harmonics

The spherical harmonics `Y_ℓ^m(θ, φ) = N_{ℓm} P_ℓ^m(cos θ) e^{imφ}` as
eigenfunctions of the angular Laplacian (Laplace–Beltrami operator) on `S²`:
their definition and normalisation, the eigenvalue equation, orthonormality in
`L²(S²)`, the coordinate model of `L²(S²)`, and the finite-dimensional angular
sectors `V_ℓ`.

The one-variable Legendre theory lives in
`Spectra.SphericalHarmonics.AssociatedLegendre`; completeness of `{Y_ℓ^m}` in
`L²(S²)` lives in `Spectra.SphericalHarmonics.Completeness`.

## Physical significance

When I separated variables in the hydrogen equation, the angular part gave me
the spherical harmonics — functions on the unit sphere that encode the *shape*
of the electron's orbital. The quantum number `ℓ` is the orbital angular
momentum, `m` its projection onto a chosen axis. These are the s, p, d, f
orbitals of chemistry.

## Note on the normalisation

`sphericalNorm` uses the **signed** index `m`,
`N_{ℓm} = √((2ℓ+1)/(4π)·(ℓ-m)!/(ℓ+m)!)`. Combined with the reflection
convention built into `AssociatedLegendre`
(`P_ℓ^{-m} = (-1)^m (ℓ-m)!/(ℓ+m)! P_ℓ^m`), this makes `⟨Y_ℓ^m, Y_ℓ^m⟩ = 1`
for all `|m| ≤ ℓ`. (An earlier `|m|`-based definition made
`sphericalHarmonic_orthonormal` false: e.g. `‖Y₁^{-1}‖²` would be `1/4`.)

## Main definitions

* `SphericalHarmonic ℓ m` — `Y_ℓ^m(θ, φ)` on the coordinate rectangle.
* `laplaceBeltrami` — the angular Laplacian in spherical coordinates.
* `sphereMeasure`, `L2_S2` — the `sin θ`-weighted measure on the coordinate
  rectangle `(0,π] × (0,2π]` and the resulting `L²(S²)`.
* `AngularSector ℓ` — `V_ℓ = span{Y_ℓ^m : |m| ≤ ℓ}` as a `Submodule ℂ L2_S2`.

## Main statements

* `sphericalHarmonic_eigenvalue` — `L̂² Y_ℓ^m = ℓ(ℓ+1) Y_ℓ^m`.
* `sphericalHarmonic_orthonormal` — `⟨Y_ℓ^m, Y_{ℓ'}^{m'}⟩ = δ_{ℓℓ'} δ_{mm'}`.
* `memLp_sphericalHarmonic` — `Y_ℓ^m ∈ L²(S²)`.
* `angularSector_dim`, `angularSector_orthogonal`.
-/

open MeasureTheory Complex Filter InnerProductSpace
open scoped Topology NNReal ENNReal ContDiff

namespace Spectra.SphericalHarmonics

/-- The normalisation constant for Y_ℓ^m, with the **signed** index `m`:
      N_{ℓm} = √((2ℓ+1)/(4π) · (ℓ-m)!/(ℓ+m)!).

    (Previously this used `|m|`, which together with the reflection convention
    in `AssociatedLegendre` broke orthonormality for m < 0 — see the revision
    notes. `Int.toNat` keeps the definition total; for the physical range
    `|m| ≤ ℓ` both `ℓ-m` and `ℓ+m` are non-negative, so nothing is clamped.) -/
noncomputable def sphericalNorm (ℓ : ℕ) (m : ℤ) : ℝ :=
  Real.sqrt ((2 * ℓ + 1) / (4 * Real.pi) *
    (Nat.factorial ((ℓ - m).toNat)) / (Nat.factorial ((ℓ + m).toNat)))

/-- The normalisation constant is positive (`Int.toNat` makes the inner
    factorials ≥ 1 even without `|m| ≤ ℓ`). -/
lemma sphericalNorm_pos (ℓ : ℕ) (m : ℤ) : 0 < sphericalNorm ℓ m := by
  unfold sphericalNorm
  apply Real.sqrt_pos.mpr
  have h1 : (0:ℝ) < 2 * ℓ + 1 := by positivity
  have h2 : (0:ℝ) < 4 * Real.pi := by positivity
  have hf1 : (0:ℝ) < (Nat.factorial ((ℓ - m).toNat) : ℝ) := by
    exact_mod_cast ((ℓ - m).toNat).factorial_pos
  have hf2 : (0:ℝ) < (Nat.factorial ((ℓ + m).toNat) : ℝ) := by
    exact_mod_cast ((ℓ + m).toNat).factorial_pos
  exact div_pos (mul_pos (div_pos h1 h2) hf1) hf2

/-- The square of the normalisation constant. -/
lemma sphericalNorm_sq (ℓ : ℕ) (m : ℤ) :
    sphericalNorm ℓ m ^ 2 =
      (2 * ℓ + 1) / (4 * Real.pi) *
        (Nat.factorial ((ℓ - m).toNat)) / (Nat.factorial ((ℓ + m).toNat)) := by
  unfold sphericalNorm
  refine Real.sq_sqrt ?_
  positivity

/-- The spherical harmonic Y_ℓ^m(θ, φ) as a function on ℝ × ℝ (coordinates
    (θ, φ); the physical domain is [0,π] × [0,2π)).

    Y_ℓ^m(θ, φ) = N_{ℓm} P_ℓ^m(cos θ) e^{imφ}

    This is the standard physics convention (Condon-Shortley phase). -/
noncomputable def SphericalHarmonic (ℓ : ℕ) (m : ℤ) (_hm : |m| ≤ ℓ) : ℝ × ℝ → ℂ :=
  fun p =>
    (sphericalNorm ℓ m : ℂ) *
    (AssociatedLegendre ℓ m (Real.cos p.1) : ℂ) *
    Complex.exp (I * m * p.2)

lemma sphericalHarmonic_continuous (ℓ : ℕ) (m : ℤ) (hm : |m| ≤ ℓ) :
    Continuous (SphericalHarmonic ℓ m hm) := by
  have hP := associatedLegendre_continuous ℓ m
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
      (hP.comp (Real.continuous_cos.comp continuous_fst)))).mul
    (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_snd)))

/-- The uniform product form of Y_ℓ^m, with the reflection factor made
    explicit. The workhorse representation for the eigenvalue and
    orthonormality proofs. -/
lemma sphericalHarmonic_eq (ℓ : ℕ) (m : ℤ) (hm : |m| ≤ ℓ) (a b : ℝ) :
    SphericalHarmonic ℓ m hm (a, b) =
      ((sphericalNorm ℓ m * reflectionFactor ℓ m *
          assocLegendreNat ℓ m.natAbs (Real.cos a) : ℝ) : ℂ) *
        Complex.exp (I * m * b) := by
  change (sphericalNorm ℓ m : ℂ) * ((AssociatedLegendre ℓ m (Real.cos a) : ℝ) : ℂ) *
      Complex.exp (I * m * b) = _
  rw [associatedLegendre_eq_reflection]
  push_cast
  ring

/-! ## The Fourier half of orthonormality (proved) -/

/-- ∫₀^{2π} e^{ikφ} dφ = 0 for k ∈ ℤ, k ≠ 0. Combined with
    `associatedLegendre_orthogonality`, this is the engine behind
    `sphericalHarmonic_orthonormal`: the conjugate product of two harmonics
    carries the phase e^{i(m'-m)φ}, so distinct `m` are killed by this lemma
    and equal `m` reduce to the θ-integral. -/
lemma integral_exp_I_int_mul {k : ℤ} (hk : k ≠ 0) :
    ∫ φ in (0:ℝ)..(2 * Real.pi), Complex.exp (I * k * φ) = 0 := by
  have hc : (I * (k : ℂ)) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hk)
  rw [integral_exp_mul_complex hc]
  have h1 : Complex.exp (I * (k : ℂ) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    rw [show (I * (k : ℂ) * ((2 * Real.pi : ℝ) : ℂ)) =
        (k : ℂ) * (2 * (Real.pi : ℂ) * I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I k
  rw [h1]
  simp

/-! ## Eigenvalue equation -/

/-- The angular Laplacian (Laplace–Beltrami operator on S²) in spherical
    coordinates, acting on a function of (θ, φ):

      L̂² Y = -[ (1/sin θ) ∂_θ (sin θ ∂_θ Y) + (1/sin² θ) ∂_φ² Y ].

    Meaningful pointwise away from the coordinate singularities θ ∈ {0, π}. -/
noncomputable def laplaceBeltrami (Y : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ := fun p =>
  -((1 / (Real.sin p.1 : ℂ)) *
      deriv (fun t => (Real.sin t : ℂ) * deriv (fun s => Y (s, p.2)) t) p.1
    + (1 / (Real.sin p.1 : ℂ) ^ 2) * deriv (deriv (fun q => Y (p.1, q))) p.2)

/-- **`L̂²` is `ℂ`-linear over constant factors**: `L̂²(c · Y) = c · (L̂² Y)`.

    The angular Laplacian is built only from `deriv` and scalar multiplication, so a
    constant pulls straight out — this is just `deriv_const_mul_field` applied at each
    of the three derivative layers (no differentiability of `Y` required). Used to
    detach the radial factor `R(r)` from the angular factor when reducing `−Δ` within
    a fixed `ℓ`-sector. -/
theorem laplaceBeltrami_const_mul (c : ℂ) (Y : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    laplaceBeltrami (fun q => c * Y q) p = c * laplaceBeltrami Y p := by
  have hθ : deriv (fun t => (Real.sin t : ℂ) * deriv (fun s => c * Y (s, p.2)) t) p.1
      = c * deriv (fun t => (Real.sin t : ℂ) * deriv (fun s => Y (s, p.2)) t) p.1 := by
    have e1 : (fun t => (Real.sin t : ℂ) * deriv (fun s => c * Y (s, p.2)) t)
        = (fun t => c * ((Real.sin t : ℂ) * deriv (fun s => Y (s, p.2)) t)) := by
      funext t; rw [deriv_const_mul_field]; ring
    rw [e1, deriv_const_mul_field]
  have hφ : deriv (deriv (fun q => c * Y (p.1, q))) p.2
      = c * deriv (deriv (fun q => Y (p.1, q))) p.2 := by
    have e2 : deriv (fun q => c * Y (p.1, q))
        = fun q => c * deriv (fun q' => Y (p.1, q')) q := by
      funext q; rw [deriv_const_mul_field]
    rw [e2, deriv_const_mul_field]
  simp only [laplaceBeltrami]
  rw [hθ, hφ]
  ring

/-- `cos` maps the open chart `(0, π)` into the open interval `(-1, 1)`. -/
lemma cos_mem_Ioo_of_mem_Ioo {t : ℝ} (ht : t ∈ Set.Ioo 0 Real.pi) :
    Real.cos t ∈ Set.Ioo (-1 : ℝ) 1 := by
  constructor
  · have h := Real.strictAntiOn_cos ⟨ht.1.le, ht.2.le⟩
      ⟨Real.pi_pos.le, le_rfl⟩ ht.2
    rwa [Real.cos_pi] at h
  · have h := Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩
      ⟨ht.1.le, ht.2.le⟩ ht.1
    rwa [Real.cos_zero] at h

/-- `(natAbs m : ℝ)² = (m : ℝ)²` — the eigenvalue only sees `m²`. -/
lemma natAbs_sq_real (m : ℤ) : ((m.natAbs : ℝ)) ^ 2 = ((m : ℝ)) ^ 2 := by
  have _hz : ((m.natAbs : ℤ)) ^ 2 = m ^ 2 := by
    rcases Int.natAbs_eq m with h | h
    · conv_rhs => rw [h]
    · conv_rhs => rw [h]
      ring
  simp only [Nat.cast_natAbs, Int.cast_abs, sq_abs]

/-- **Eigenvalue equation**: L̂² Y_ℓ^m = ℓ(ℓ+1) Y_ℓ^m, pointwise on the open
    chart θ ∈ (0, π). This is the angular part of the separation of variables
    that I performed in January 1926.

    The φ-derivatives produce the factor -m² (`Complex.I_sq`); the θ-part is
    `hasDerivAt_assocLegendreSL` — the associated Legendre ODE — transported
    along `x = cos θ`, with the key simplification `sin²θ = 1 - cos²θ` turning
    the Sturm–Liouville weight into `sin θ`. -/
theorem sphericalHarmonic_eigenvalue (ℓ : ℕ) (m : ℤ) (hm : |m| ≤ ℓ)
    (p : ℝ × ℝ) (hθ : p.1 ∈ Set.Ioo 0 Real.pi) :
    laplaceBeltrami (SphericalHarmonic ℓ m hm) p =
      ((ℓ * (ℓ + 1) : ℝ) : ℂ) * SphericalHarmonic ℓ m hm p := by
  obtain ⟨θ, φ⟩ := p
  replace hθ : θ ∈ Set.Ioo 0 Real.pi := hθ
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hx : Real.cos θ ∈ Set.Ioo (-1 : ℝ) 1 := cos_mem_Ioo_of_mem_Ioo hθ
  -- abbreviation for the (real) amplitude constant
  have hA2R : ((m.natAbs : ℝ)) ^ 2 = ((m : ℝ)) ^ 2 := natAbs_sq_real m
  -- ===== θ-part =====
  -- first derivative of t ↦ Y(t, φ), valid on all of (0, π)
  have hθderiv : ∀ t ∈ Set.Ioo (0:ℝ) Real.pi,
      deriv (fun a => SphericalHarmonic ℓ m hm (a, φ)) t =
        ((sphericalNorm ℓ m * reflectionFactor ℓ m : ℝ) : ℂ) *
          Complex.exp (I * m * φ) *
          ((assocLegendreSL ℓ m.natAbs (Real.cos t) / (1 - Real.cos t ^ 2)
              * (-Real.sin t) : ℝ) : ℂ) := by
    intro t ht
    have hxt := cos_mem_Ioo_of_mem_Ioo ht
    have hchain :=
      (hasDerivAt_assocLegendreNat ℓ m.natAbs hxt).comp t (Real.hasDerivAt_cos t)
    have hfull := hchain.ofReal_comp.const_mul
      (((sphericalNorm ℓ m * reflectionFactor ℓ m : ℝ) : ℂ) * Complex.exp (I * m * φ))
    have hfunθ : (fun a => SphericalHarmonic ℓ m hm (a, φ)) =
        fun a => (((sphericalNorm ℓ m * reflectionFactor ℓ m : ℝ) : ℂ) *
            Complex.exp (I * m * φ)) *
          ((assocLegendreNat ℓ m.natAbs (Real.cos a) : ℝ) : ℂ) := by
      funext a
      rw [sphericalHarmonic_eq]
      push_cast
      ring
    rw [hfunθ]
    erw [hfull.deriv]
  -- the inner product sin·∂_θ Y agrees near θ with the SL momentum, which we
  -- can differentiate
  have hG : (fun t => (Real.sin t : ℂ) *
        deriv (fun a => SphericalHarmonic ℓ m hm (a, φ)) t)
      =ᶠ[𝓝 θ] fun t =>
        -(((sphericalNorm ℓ m * reflectionFactor ℓ m : ℝ) : ℂ) *
            Complex.exp (I * m * φ)) *
          ((assocLegendreSL ℓ m.natAbs (Real.cos t) : ℝ) : ℂ) := by
    refine Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hθ) ?_
    intro t ht
    have _hxt := cos_mem_Ioo_of_mem_Ioo ht
    have hst : Real.sin t ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
    have hsqC : ((Real.sin t : ℂ)) ^ 2 = 1 - ((Real.cos t : ℂ)) ^ 2 := by
      exact_mod_cast Real.sin_sq t
    simp only [hθderiv t ht]
    push_cast [-Complex.ofReal_cos, -Complex.ofReal_sin]
    rw [← hsqC]
    have hstC : ((Real.sin t : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hst
    field_simp [hstC]
  -- second θ-derivative term, via the ODE
  have hD1 : deriv (fun t => (Real.sin t : ℂ) *
        deriv (fun a => SphericalHarmonic ℓ m hm (a, φ)) t) θ =
      -(((sphericalNorm ℓ m * reflectionFactor ℓ m : ℝ) : ℂ) *
          Complex.exp (I * m * φ)) *
        ((Real.sin θ *
            ((ℓ : ℝ) * ((ℓ : ℝ) + 1) - (m : ℝ) ^ 2 / (1 - Real.cos θ ^ 2)) *
            assocLegendreNat ℓ m.natAbs (Real.cos θ) : ℝ) : ℂ) := by
    rw [hG.deriv_eq]
    have h := ((hasDerivAt_assocLegendreSL ℓ m.natAbs hx).comp θ
        (Real.hasDerivAt_cos θ)).ofReal_comp.const_mul
      (-(((sphericalNorm ℓ m * reflectionFactor ℓ m : ℝ) : ℂ) *
          Complex.exp (I * m * φ)))
    erw [h.deriv]
    push_cast [hA2R]
    ring
  -- ===== φ-part =====
  have hexp : ∀ q : ℝ, HasDerivAt (fun b : ℝ => Complex.exp (I * m * b))
      (Complex.exp (I * m * q) * (I * m)) q := by
    intro q
    have hlin : HasDerivAt (fun b : ℝ => I * (m : ℂ) * (b : ℂ)) (I * m) q := by
      simpa using (hasDerivAt_id q).ofReal_comp.const_mul (I * (m : ℂ))
    exact hlin.cexp
  have hfunφ : (fun q => SphericalHarmonic ℓ m hm (θ, q)) =
      fun q : ℝ => (((sphericalNorm ℓ m * reflectionFactor ℓ m *
          assocLegendreNat ℓ m.natAbs (Real.cos θ) : ℝ) : ℂ)) *
        Complex.exp (I * m * q) := by
    funext q
    rw [sphericalHarmonic_eq]
  have hφ1 : deriv (fun q => SphericalHarmonic ℓ m hm (θ, q)) =
      fun q : ℝ => (((sphericalNorm ℓ m * reflectionFactor ℓ m *
          assocLegendreNat ℓ m.natAbs (Real.cos θ) : ℝ) : ℂ)) *
        (Complex.exp (I * m * q) * (I * m)) := by
    funext q
    rw [hfunφ]
    exact ((hexp q).const_mul _).deriv
  have hD2 : deriv (deriv (fun q => SphericalHarmonic ℓ m hm (θ, q))) φ =
      -((m : ℂ)) ^ 2 *
        ((((sphericalNorm ℓ m * reflectionFactor ℓ m *
            assocLegendreNat ℓ m.natAbs (Real.cos θ) : ℝ) : ℂ)) *
          Complex.exp (I * m * φ)) := by
    rw [hφ1]
    have h := (((hexp φ).mul_const (I * (m : ℂ))).const_mul
      (((sphericalNorm ℓ m * reflectionFactor ℓ m *
          assocLegendreNat ℓ m.natAbs (Real.cos θ) : ℝ) : ℂ))).deriv
    rw [h]
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (((sphericalNorm ℓ m * reflectionFactor ℓ m *
        assocLegendreNat ℓ m.natAbs (Real.cos θ) : ℝ) : ℂ) *
      Complex.exp (I * m * φ) * (m : ℂ) ^ 2) * hI2
  -- ===== assembly =====
  have hlb : laplaceBeltrami (SphericalHarmonic ℓ m hm) (θ, φ) =
      -((1 / (Real.sin θ : ℂ)) *
          deriv (fun t => (Real.sin t : ℂ) *
            deriv (fun s => SphericalHarmonic ℓ m hm (s, φ)) t) θ
        + (1 / (Real.sin θ : ℂ) ^ 2) *
            deriv (deriv (fun q => SphericalHarmonic ℓ m hm (θ, q))) φ) := rfl
  rw [hlb, hD1, hD2, sphericalHarmonic_eq ℓ m hm θ φ]
  have hsC : ((Real.sin θ : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hsin.ne'
  have hsqC : ((Real.sin θ : ℂ)) ^ 2 = 1 - ((Real.cos θ : ℂ)) ^ 2 := by
    exact_mod_cast Real.sin_sq θ
  push_cast [-Complex.ofReal_cos, -Complex.ofReal_sin]
  rw [← hsqC]
  field_simp [hsC]
  ring

/-! ## Orthonormality -/

/-- **Orthonormality**: ∫_{S²} Ȳ_ℓ^m · Y_{ℓ'}^{m'} dΩ = δ_{ℓℓ'} δ_{mm'},
    written in coordinates with dΩ = sin θ dθ dφ.

    Proof structure:
    - φ-integral: `integral_exp_I_int_mul` kills m ≠ m'.
    - θ-integral: substitute x = cos θ
      (`intervalIntegral.integral_deriv_smul_comp`); ℓ ≠ ℓ' dies by
      `assocLegendreNat_orthogonality`.
    - Diagonal: `assocLegendreNat_normalization` (now proved) plus
      the factorial algebra of `sphericalNorm` — which is where the corrected
      (signed-m) normalisation is essential. -/
theorem sphericalHarmonic_orthonormal (ℓ ℓ' : ℕ) (m m' : ℤ)
    (hm : |m| ≤ ℓ) (hm' : |m'| ≤ ℓ') :
    (∫ θ in (0:ℝ)..Real.pi, ∫ φ in (0:ℝ)..(2 * Real.pi),
        (starRingEnd ℂ) (SphericalHarmonic ℓ m hm (θ, φ)) *
          SphericalHarmonic ℓ' m' hm' (θ, φ) * (Real.sin θ : ℂ)) =
      if ℓ = ℓ' ∧ m = m' then 1 else 0 := by
  -- the pointwise reduction of the integrand: real amplitude × pure phase
  have hpt : ∀ θ φ : ℝ,
      (starRingEnd ℂ) (SphericalHarmonic ℓ m hm (θ, φ)) *
          SphericalHarmonic ℓ' m' hm' (θ, φ) * (Real.sin θ : ℂ) =
        ((sphericalNorm ℓ m * reflectionFactor ℓ m *
            assocLegendreNat ℓ m.natAbs (Real.cos θ) *
            (sphericalNorm ℓ' m' * reflectionFactor ℓ' m' *
              assocLegendreNat ℓ' m'.natAbs (Real.cos θ)) * Real.sin θ : ℝ) : ℂ) *
          Complex.exp (I * ((m' - m : ℤ) : ℂ) * φ) := by
    intro θ φ
    rw [sphericalHarmonic_eq ℓ m hm θ φ, sphericalHarmonic_eq ℓ' m' hm' θ φ]
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    rw [show (starRingEnd ℂ) (I * (m : ℂ) * (φ : ℂ)) = -(I * (m : ℂ) * (φ : ℂ)) by
      simp [map_mul, Complex.conj_I, Complex.conj_ofReal]]
    calc ((sphericalNorm ℓ m * reflectionFactor ℓ m *
            assocLegendreNat ℓ m.natAbs (Real.cos θ) : ℝ) : ℂ) *
            Complex.exp (-(I * (m : ℂ) * (φ : ℂ))) *
          (((sphericalNorm ℓ' m' * reflectionFactor ℓ' m' *
              assocLegendreNat ℓ' m'.natAbs (Real.cos θ) : ℝ) : ℂ) *
            Complex.exp (I * m' * φ)) * ((Real.sin θ : ℝ) : ℂ)
        = (((sphericalNorm ℓ m * reflectionFactor ℓ m *
              assocLegendreNat ℓ m.natAbs (Real.cos θ) : ℝ) : ℂ) *
            ((sphericalNorm ℓ' m' * reflectionFactor ℓ' m' *
              assocLegendreNat ℓ' m'.natAbs (Real.cos θ) : ℝ) : ℂ) *
            ((Real.sin θ : ℝ) : ℂ)) *
          (Complex.exp (-(I * (m : ℂ) * (φ : ℂ))) * Complex.exp (I * m' * φ)) := by
          ring
      _ = _ := by
          rw [← Complex.exp_add,
            show -(I * (m : ℂ) * (φ : ℂ)) + I * (m' : ℂ) * (φ : ℂ) =
              I * ((m' - m : ℤ) : ℂ) * (φ : ℂ) by push_cast; ring]
          push_cast
          ring
  by_cases hmm' : m = m'
  · -- equal magnetic numbers: the φ-integral contributes 2π
    subst hmm'
    have hφint : ∀ θ : ℝ,
        (∫ φ in (0:ℝ)..(2 * Real.pi),
          (starRingEnd ℂ) (SphericalHarmonic ℓ m hm (θ, φ)) *
            SphericalHarmonic ℓ' m hm' (θ, φ) * (Real.sin θ : ℂ)) =
        ((2 * Real.pi *
            (sphericalNorm ℓ m * reflectionFactor ℓ m *
              assocLegendreNat ℓ m.natAbs (Real.cos θ) *
              (sphericalNorm ℓ' m * reflectionFactor ℓ' m *
                assocLegendreNat ℓ' m.natAbs (Real.cos θ)) * Real.sin θ) : ℝ) : ℂ) := by
      intro θ
      calc (∫ φ in (0:ℝ)..(2 * Real.pi),
            (starRingEnd ℂ) (SphericalHarmonic ℓ m hm (θ, φ)) *
              SphericalHarmonic ℓ' m hm' (θ, φ) * (Real.sin θ : ℂ))
          = ∫ φ in (0:ℝ)..(2 * Real.pi),
              ((sphericalNorm ℓ m * reflectionFactor ℓ m *
                  assocLegendreNat ℓ m.natAbs (Real.cos θ) *
                  (sphericalNorm ℓ' m * reflectionFactor ℓ' m *
                    assocLegendreNat ℓ' m.natAbs (Real.cos θ)) * Real.sin θ : ℝ) : ℂ) *
                Complex.exp (I * ((m - m : ℤ) : ℂ) * φ) :=
            intervalIntegral.integral_congr fun φ _ => hpt θ φ
        _ = _ := by
            simp only [sub_self, Int.cast_zero, mul_zero, zero_mul,
              Complex.exp_zero, mul_one]
            rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul]
            push_cast
            ring
    calc (∫ θ in (0:ℝ)..Real.pi, ∫ φ in (0:ℝ)..(2 * Real.pi),
            (starRingEnd ℂ) (SphericalHarmonic ℓ m hm (θ, φ)) *
              SphericalHarmonic ℓ' m hm' (θ, φ) * (Real.sin θ : ℂ))
        = ∫ θ in (0:ℝ)..Real.pi,
            ((2 * Real.pi *
              (sphericalNorm ℓ m * reflectionFactor ℓ m *
                assocLegendreNat ℓ m.natAbs (Real.cos θ) *
                (sphericalNorm ℓ' m * reflectionFactor ℓ' m *
                  assocLegendreNat ℓ' m.natAbs (Real.cos θ)) * Real.sin θ) : ℝ) : ℂ) :=
          intervalIntegral.integral_congr fun θ _ => hφint θ
      _ = (((∫ θ in (0:ℝ)..Real.pi,
            2 * Real.pi *
              (sphericalNorm ℓ m * reflectionFactor ℓ m *
                assocLegendreNat ℓ m.natAbs (Real.cos θ) *
                (sphericalNorm ℓ' m * reflectionFactor ℓ' m *
                  assocLegendreNat ℓ' m.natAbs (Real.cos θ)) * Real.sin θ)) : ℝ) : ℂ) :=
          intervalIntegral.integral_ofReal
      _ = if ℓ = ℓ' ∧ m = m then 1 else 0 := by
          -- pull out constants and substitute x = cos θ
          have hpull : ∀ θ : ℝ,
              2 * Real.pi *
                (sphericalNorm ℓ m * reflectionFactor ℓ m *
                  assocLegendreNat ℓ m.natAbs (Real.cos θ) *
                  (sphericalNorm ℓ' m * reflectionFactor ℓ' m *
                    assocLegendreNat ℓ' m.natAbs (Real.cos θ)) * Real.sin θ) =
              (2 * Real.pi * (sphericalNorm ℓ m * reflectionFactor ℓ m *
                  (sphericalNorm ℓ' m * reflectionFactor ℓ' m))) *
                (Real.sin θ * (assocLegendreNat ℓ m.natAbs (Real.cos θ) *
                  assocLegendreNat ℓ' m.natAbs (Real.cos θ))) :=
            fun θ => by ring
          have hsubst : (∫ θ in (0:ℝ)..Real.pi,
                Real.sin θ * (assocLegendreNat ℓ m.natAbs (Real.cos θ) *
                  assocLegendreNat ℓ' m.natAbs (Real.cos θ))) =
              ∫ x in (-1:ℝ)..1,
                assocLegendreNat ℓ m.natAbs x * assocLegendreNat ℓ' m.natAbs x := by
            have hg : Continuous fun x : ℝ =>
                assocLegendreNat ℓ m.natAbs x * assocLegendreNat ℓ' m.natAbs x :=
              (assocLegendreNat_continuous _ _).mul (assocLegendreNat_continuous _ _)
            have h := intervalIntegral.integral_deriv_smul_comp
              (f := Real.cos) (f' := fun t => -Real.sin t)
              (g := fun x => assocLegendreNat ℓ m.natAbs x *
                assocLegendreNat ℓ' m.natAbs x)
              (a := 0) (b := Real.pi)
              (fun t _ => Real.hasDerivAt_cos t)
              (Real.continuous_sin.neg.continuousOn) hg
            simp only [Function.comp_apply, smul_eq_mul, Real.cos_zero,
              Real.cos_pi, neg_mul] at h
            rw [intervalIntegral.integral_neg,
              show (∫ x in (1:ℝ)..(-1),
                  assocLegendreNat ℓ m.natAbs x * assocLegendreNat ℓ' m.natAbs x) =
                -∫ x in (-1:ℝ)..1,
                  assocLegendreNat ℓ m.natAbs x * assocLegendreNat ℓ' m.natAbs x
                from intervalIntegral.integral_symm (-1 : ℝ) 1] at h
            linarith [h]
          rw [intervalIntegral.integral_congr (g := fun θ =>
              (2 * Real.pi * (sphericalNorm ℓ m * reflectionFactor ℓ m *
                  (sphericalNorm ℓ' m * reflectionFactor ℓ' m))) *
                (Real.sin θ * (assocLegendreNat ℓ m.natAbs (Real.cos θ) *
                  assocLegendreNat ℓ' m.natAbs (Real.cos θ))))
              (fun θ _ => hpull θ),
            intervalIntegral.integral_const_mul, hsubst]
          by_cases hll : ℓ = ℓ'
          · -- the diagonal: normalisation
            subst hll
            rw [if_pos ⟨rfl, rfl⟩]
            have hA_le : m.natAbs ≤ ℓ := by
              have h := hm
              rw [Int.abs_eq_natAbs] at h
              exact_mod_cast h
            rw [assocLegendreNat_normalization ℓ m.natAbs hA_le]
            -- the factorial algebra, with the *signed-m* normalisation
            have hreal : 2 * Real.pi * (sphericalNorm ℓ m * reflectionFactor ℓ m *
                  (sphericalNorm ℓ m * reflectionFactor ℓ m)) *
                (2 / (2 * (ℓ : ℝ) + 1) * ((ℓ + m.natAbs).factorial : ℝ) /
                  ((ℓ - m.natAbs).factorial : ℝ)) = 1 := by
              have hfacm : (((ℓ - m.natAbs).factorial : ℝ)) ≠ 0 :=
                Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
              have hfacp : (((ℓ + m.natAbs).factorial : ℝ)) ≠ 0 :=
                Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
              have h2l : ((2 * (ℓ : ℝ) + 1)) ≠ 0 := by positivity
              rcases le_or_gt 0 m with hm0 | hm0
              · -- m ≥ 0 : reflection factor 1
                have hr : reflectionFactor ℓ m = 1 := if_pos hm0
                have ht1 : ((ℓ : ℤ) - m).toNat = ℓ - m.natAbs := by omega
                have ht2 : ((ℓ : ℤ) + m).toNat = ℓ + m.natAbs := by omega
                have hN := sphericalNorm_sq ℓ m
                rw [ht1, ht2] at hN
                rw [hr, show sphericalNorm ℓ m * 1 * (sphericalNorm ℓ m * 1) =
                    sphericalNorm ℓ m ^ 2 by ring, hN]
                field_simp
                ring
              · -- m < 0 : the reflection factor squared meets the flipped
                -- factorial ratio in `sphericalNorm` — this is exactly where
                -- the old |m|-based normalisation broke
                have hr : reflectionFactor ℓ m =
                    (-1 : ℝ) ^ m.natAbs * (ℓ - m.natAbs).factorial /
                      (ℓ + m.natAbs).factorial := if_neg (not_le.mpr hm0)
                have ht1 : ((ℓ : ℤ) - m).toNat = ℓ + m.natAbs := by omega
                have ht2 : ((ℓ : ℤ) + m).toNat = ℓ - m.natAbs := by omega
                have hN := sphericalNorm_sq ℓ m
                rw [ht1, ht2] at hN
                have hneg : ((-1 : ℝ)) ^ m.natAbs * ((-1 : ℝ)) ^ m.natAbs = 1 := by
                  rw [← pow_add]
                  exact Even.neg_one_pow ⟨m.natAbs, rfl⟩
                rw [hr, show sphericalNorm ℓ m *
                      ((-1 : ℝ) ^ m.natAbs * ((ℓ - m.natAbs).factorial : ℝ) /
                        ((ℓ + m.natAbs).factorial : ℝ)) *
                    (sphericalNorm ℓ m *
                      ((-1 : ℝ) ^ m.natAbs * ((ℓ - m.natAbs).factorial : ℝ) /
                        ((ℓ + m.natAbs).factorial : ℝ))) =
                    sphericalNorm ℓ m ^ 2 *
                      ((-1 : ℝ) ^ m.natAbs * (-1 : ℝ) ^ m.natAbs) *
                      (((ℓ - m.natAbs).factorial : ℝ) /
                        ((ℓ + m.natAbs).factorial : ℝ)) ^ 2 by ring,
                  hneg, hN]
                field_simp
                ring
            rw [hreal, Complex.ofReal_one]
          · -- ℓ ≠ ℓ' : orthogonality of the Legendre functions
            rw [assocLegendreNat_orthogonality ℓ ℓ' m.natAbs hll, mul_zero,
              Complex.ofReal_zero, if_neg (fun hcon => hll hcon.1)]
  · -- m ≠ m' : the φ-integral vanishes
    have hk : (m' - m : ℤ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hmm')
    have hφzero : ∀ θ : ℝ,
        (∫ φ in (0:ℝ)..(2 * Real.pi),
          (starRingEnd ℂ) (SphericalHarmonic ℓ m hm (θ, φ)) *
            SphericalHarmonic ℓ' m' hm' (θ, φ) * (Real.sin θ : ℂ)) = 0 := by
      intro θ
      calc (∫ φ in (0:ℝ)..(2 * Real.pi),
            (starRingEnd ℂ) (SphericalHarmonic ℓ m hm (θ, φ)) *
              SphericalHarmonic ℓ' m' hm' (θ, φ) * (Real.sin θ : ℂ))
          = ∫ φ in (0:ℝ)..(2 * Real.pi),
              ((sphericalNorm ℓ m * reflectionFactor ℓ m *
                  assocLegendreNat ℓ m.natAbs (Real.cos θ) *
                  (sphericalNorm ℓ' m' * reflectionFactor ℓ' m' *
                    assocLegendreNat ℓ' m'.natAbs (Real.cos θ)) * Real.sin θ : ℝ) : ℂ) *
                Complex.exp (I * ((m' - m : ℤ) : ℂ) * φ) :=
            intervalIntegral.integral_congr fun φ _ => hpt θ φ
        _ = 0 := by
            rw [intervalIntegral.integral_const_mul, integral_exp_I_int_mul hk,
              mul_zero]
    calc (∫ θ in (0:ℝ)..Real.pi, ∫ φ in (0:ℝ)..(2 * Real.pi),
            (starRingEnd ℂ) (SphericalHarmonic ℓ m hm (θ, φ)) *
              SphericalHarmonic ℓ' m' hm' (θ, φ) * (Real.sin θ : ℂ))
        = ∫ _ in (0:ℝ)..Real.pi, (0 : ℂ) :=
          intervalIntegral.integral_congr fun θ _ => hφzero θ
      _ = 0 := intervalIntegral.integral_zero
      _ = if ℓ = ℓ' ∧ m = m' then 1 else 0 := by
          rw [if_neg (fun hcon => hmm' hcon.2)]

/-! ## L²(S²) -/

/-- The measure sin θ dθ dφ on the coordinate rectangle (0, π] × (0, 2π].
    Up to the standard chart, this is the surface measure on S². -/
noncomputable def sphereMeasure : Measure (ℝ × ℝ) :=
  ((volume : Measure (ℝ × ℝ)).restrict
      (Set.Ioc 0 Real.pi ×ˢ Set.Ioc 0 (2 * Real.pi))).withDensity
    fun p => ENNReal.ofReal (Real.sin p.1)

instance : IsFiniteMeasure sphereMeasure := by
  unfold sphereMeasure
  apply isFiniteMeasure_withDensity
  have hle : (∫⁻ p, ENNReal.ofReal (Real.sin p.1)
        ∂((volume : Measure (ℝ × ℝ)).restrict
          (Set.Ioc 0 Real.pi ×ˢ Set.Ioc 0 (2 * Real.pi))))
      ≤ (volume : Measure (ℝ × ℝ)) (Set.Ioc 0 Real.pi ×ˢ Set.Ioc 0 (2 * Real.pi)) := by
    calc (∫⁻ p, ENNReal.ofReal (Real.sin p.1)
          ∂((volume : Measure (ℝ × ℝ)).restrict
            (Set.Ioc 0 Real.pi ×ˢ Set.Ioc 0 (2 * Real.pi))))
        ≤ ∫⁻ _, 1 ∂((volume : Measure (ℝ × ℝ)).restrict
            (Set.Ioc 0 Real.pi ×ˢ Set.Ioc 0 (2 * Real.pi))) :=
          lintegral_mono fun p => ENNReal.ofReal_le_one.mpr (Real.sin_le_one _)
      _ = (volume : Measure (ℝ × ℝ)) (Set.Ioc 0 Real.pi ×ˢ Set.Ioc 0 (2 * Real.pi)) := by
          rw [lintegral_one, Measure.restrict_apply_univ]
  refine ne_top_of_le_ne_top ?_ hle
  rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioc]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- L²(S², dΩ) in coordinates. -/
abbrev L2_S2 : Type := Lp ℂ 2 sphereMeasure

/-- Every spherical harmonic lies in L²(S²): it is continuous, hence bounded
    on the (compact closure of the) coordinate rectangle carrying the finite
    measure `sphereMeasure`. -/
lemma memLp_sphericalHarmonic (ℓ : ℕ) (m : ℤ) (hm : |m| ≤ ℓ) :
    MemLp (SphericalHarmonic ℓ m hm) 2 sphereMeasure := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    ((sphericalHarmonic_continuous ℓ m hm).continuousOn
      (s := Set.Icc 0 Real.pi ×ˢ Set.Icc 0 (2 * Real.pi)))
  refine MemLp.of_bound
    ((sphericalHarmonic_continuous ℓ m hm).aestronglyMeasurable) C ?_
  have hbox : MeasurableSet (Set.Ioc (0:ℝ) Real.pi ×ˢ Set.Ioc (0:ℝ) (2 * Real.pi)) :=
    measurableSet_Ioc.prod measurableSet_Ioc
  have hae : ∀ᵐ p ∂sphereMeasure,
      p ∈ Set.Ioc (0:ℝ) Real.pi ×ˢ Set.Ioc (0:ℝ) (2 * Real.pi) :=
    (ae_restrict_mem hbox).filter_mono
      (Measure.AbsolutelyContinuous.ae_le (withDensity_absolutelyContinuous _ _))
  filter_upwards [hae] with p hp
  exact hC p ⟨⟨hp.1.1.le, hp.1.2⟩, ⟨hp.2.1.le, hp.2.2⟩⟩

/-! ## The L² bridge

Reducing inner products in `L2_S2` to the iterated `sin θ`-weighted interval
integrals appearing in `sphericalHarmonic_orthonormal`. -/

/-- Integration against `sphereMeasure` of a continuous function is the
    iterated weighted interval integral. -/
lemma integral_sphereMeasure_eq {F : ℝ × ℝ → ℂ} (hF : Continuous F) :
    (∫ p, F p ∂sphereMeasure) =
      ∫ θ in (0:ℝ)..Real.pi, ∫ φ in (0:ℝ)..(2 * Real.pi),
        F (θ, φ) * (Real.sin θ : ℂ) := by
  have hbox : MeasurableSet (Set.Ioc (0:ℝ) Real.pi ×ˢ Set.Ioc (0:ℝ) (2 * Real.pi)) :=
    measurableSet_Ioc.prod measurableSet_Ioc
  have hmeas : Measurable fun p : ℝ × ℝ => Real.toNNReal (Real.sin p.1) :=
    (continuous_real_toNNReal.comp (Real.continuous_sin.comp continuous_fst)).measurable
  have hG : Continuous fun p : ℝ × ℝ => F p * (Real.sin p.1 : ℂ) :=
    hF.mul (Complex.continuous_ofReal.comp (Real.continuous_sin.comp continuous_fst))
  -- Step 1: peel the density off `sphereMeasure`
  have h1 : (∫ p, F p ∂sphereMeasure) =
      ∫ p in Set.Ioc (0:ℝ) Real.pi ×ˢ Set.Ioc (0:ℝ) (2 * Real.pi),
        Real.toNNReal (Real.sin p.1) • F p ∂(volume : Measure (ℝ × ℝ)) := by
    rw [show sphereMeasure =
        ((volume : Measure (ℝ × ℝ)).restrict
            (Set.Ioc 0 Real.pi ×ˢ Set.Ioc 0 (2 * Real.pi))).withDensity
          (fun p => ((Real.toNNReal (Real.sin p.1) : ℝ≥0) : ℝ≥0∞)) from rfl]
    exact integral_withDensity_eq_integral_smul hmeas F
  -- Step 2: on the box, `sin ≥ 0`, so the `ℝ≥0`-smul is multiplication by sin
  have h2 : (∫ p in Set.Ioc (0:ℝ) Real.pi ×ˢ Set.Ioc (0:ℝ) (2 * Real.pi),
        Real.toNNReal (Real.sin p.1) • F p ∂(volume : Measure (ℝ × ℝ))) =
      ∫ p in Set.Ioc (0:ℝ) Real.pi ×ˢ Set.Ioc (0:ℝ) (2 * Real.pi),
        F p * (Real.sin p.1 : ℂ) ∂(volume : Measure (ℝ × ℝ)) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hbox] with p hp
    have h0 : 0 ≤ Real.sin p.1 :=
      Real.sin_nonneg_of_nonneg_of_le_pi hp.1.1.le hp.1.2
    rw [NNReal.smul_def, Real.coe_toNNReal _ h0, Complex.real_smul, mul_comm]
  -- Step 3: the restricted planar measure is a product of restricted lines
  have h3 : ((volume : Measure (ℝ × ℝ)).restrict
        (Set.Ioc (0:ℝ) Real.pi ×ˢ Set.Ioc (0:ℝ) (2 * Real.pi))) =
      ((volume : Measure ℝ).restrict (Set.Ioc 0 Real.pi)).prod
        ((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hIntOn : Integrable (fun p : ℝ × ℝ => F p * (Real.sin p.1 : ℂ))
      (((volume : Measure ℝ).restrict (Set.Ioc 0 Real.pi)).prod
        ((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi)))) := by
    rw [← h3]
    exact (hG.continuousOn.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  rw [h1, h2, h3, MeasureTheory.integral_prod _ hIntOn]
  -- Step 4: set integrals over `Ioc` are interval integrals
  rw [← intervalIntegral.integral_of_le Real.pi_pos.le]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi)]

/-- The `Lp` inner product of two (toLp'd) spherical harmonics is exactly the
    iterated integral of `sphericalHarmonic_orthonormal`. -/
lemma inner_toLp_sphericalHarmonic (ℓ ℓ' : ℕ) (m m' : ℤ)
    (hm : |m| ≤ ℓ) (hm' : |m'| ≤ ℓ') :
    inner (𝕜 := ℂ)
        ((memLp_sphericalHarmonic ℓ m hm).toLp (SphericalHarmonic ℓ m hm))
        ((memLp_sphericalHarmonic ℓ' m' hm').toLp (SphericalHarmonic ℓ' m' hm')) =
      ∫ θ in (0:ℝ)..Real.pi, ∫ φ in (0:ℝ)..(2 * Real.pi),
        (starRingEnd ℂ) (SphericalHarmonic ℓ m hm (θ, φ)) *
          SphericalHarmonic ℓ' m' hm' (θ, φ) * (Real.sin θ : ℂ) := by
  rw [MeasureTheory.L2.inner_def]
  have hcongr : (∫ p,
        inner ℂ (((memLp_sphericalHarmonic ℓ m hm).toLp (SphericalHarmonic ℓ m hm)) p)
          (((memLp_sphericalHarmonic ℓ' m' hm').toLp (SphericalHarmonic ℓ' m' hm')) p)
        ∂sphereMeasure) =
      ∫ p, (starRingEnd ℂ) (SphericalHarmonic ℓ m hm p) *
          SphericalHarmonic ℓ' m' hm' p ∂sphereMeasure := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_sphericalHarmonic ℓ m hm).coeFn_toLp,
      (memLp_sphericalHarmonic ℓ' m' hm').coeFn_toLp] with p h1 h2
    rw [h1, h2, RCLike.inner_apply']
  rw [hcongr]
  erw [integral_sphereMeasure_eq
  /-Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ∫ (p : ℝ × ℝ), (⇑(starRingEnd ℂ) ∘ SphericalHarmonic ℓ m hm
    * SphericalHarmonic ℓ' m' hm') p ∂sphereMeasure
in the target expression
  ∫ (p : ℝ × ℝ), (starRingEnd ℂ) (SphericalHarmonic ℓ m hm p)
    * SphericalHarmonic ℓ' m' hm' p ∂sphereMeasure =
    ∫ (θ : ℝ) in 0..Real.pi,
      ∫ (φ : ℝ) in 0..2 * Real.pi,
        (starRingEnd ℂ) (SphericalHarmonic ℓ m hm (θ, φ))
          * SphericalHarmonic ℓ' m' hm' (θ, φ) * ↑(Real.sin θ)-/
    (((Complex.continuous_conj).comp (sphericalHarmonic_continuous ℓ m hm)).mul
      (sphericalHarmonic_continuous ℓ' m' hm'))]
  exact intervalIntegral.integral_congr fun ⦃x⦄ => congrFun rfl

/-! ## Quantum number constraints (proved)

(Moved ahead of the angular sectors: `angularSector_dim` now genuinely
consumes `sphericalHarmonic_count`.) -/

/-- For each ℓ, the magnetic quantum number m ranges over {-ℓ, ..., ℓ}. -/
lemma sphericalHarmonic_m_range (ℓ : ℕ) (m : ℤ) (hm : |m| ≤ ℓ) :
    -↑ℓ ≤ m ∧ m ≤ ↑ℓ :=
  abs_le.mp hm

/-- The number of spherical harmonics for angular momentum ℓ is 2ℓ+1. -/
lemma sphericalHarmonic_count (ℓ : ℕ) :
    Finset.card (Finset.Icc (-↑ℓ : ℤ) ↑ℓ) = 2 * ℓ + 1 := by
  simp only [Int.card_Icc, sub_neg_eq_add]
  omega

/-! ## Angular sectors -/

/-- The angular eigenspace of eigenvalue ℓ(ℓ+1):
    V_ℓ = span{Y_ℓ^m : m = -ℓ, ..., ℓ} ⊆ L²(S²), a (2ℓ+1)-dimensional space. -/
noncomputable def AngularSector (ℓ : ℕ) : Submodule ℂ L2_S2 :=
  Submodule.span ℂ
    {g : L2_S2 | ∃ (m : ℤ) (hm : |m| ≤ (ℓ : ℤ)),
      g = (memLp_sphericalHarmonic ℓ m hm).toLp (SphericalHarmonic ℓ m hm)}

/-- Membership in the index window gives the |m| ≤ ℓ bound. -/
lemma abs_le_of_mem_Icc {ℓ : ℕ} {m : ℤ}
    (hm : m ∈ Finset.Icc (-(ℓ : ℤ)) (ℓ : ℤ)) : |m| ≤ (ℓ : ℤ) :=
  abs_le.mpr (Finset.mem_Icc.mp hm)

/-- The Y_ℓ^m for fixed ℓ, indexed by the window {-ℓ, ..., ℓ}, form an
    orthonormal family in L²(S²). -/
lemma orthonormal_sphericalHarmonic (ℓ : ℕ) :
    Orthonormal ℂ (fun m : (Finset.Icc (-(ℓ : ℤ)) (ℓ : ℤ)) =>
      (memLp_sphericalHarmonic ℓ m.1 (abs_le_of_mem_Icc m.2)).toLp
        (SphericalHarmonic ℓ m.1 (abs_le_of_mem_Icc m.2))) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_toLp_sphericalHarmonic, sphericalHarmonic_orthonormal]
  have hcond : (ℓ = ℓ ∧ (i : ℤ) = (j : ℤ)) ↔ i = j := by
    simp only [SetLike.coe_eq_coe, true_and]
  rw [if_congr hcond rfl rfl]

/-- `AngularSector ℓ` is the span of the range of the orthonormal family. -/
lemma angularSector_eq_span_range (ℓ : ℕ) :
    AngularSector ℓ = Submodule.span ℂ (Set.range
      (fun m : (Finset.Icc (-(ℓ : ℤ)) (ℓ : ℤ)) =>
        (memLp_sphericalHarmonic ℓ m.1 (abs_le_of_mem_Icc m.2)).toLp
          (SphericalHarmonic ℓ m.1 (abs_le_of_mem_Icc m.2)))) := by
  unfold AngularSector
  congr 1
  ext g
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, Finset.mem_Icc.mpr (abs_le.mp hm)⟩, rfl⟩
  · rintro ⟨⟨m, hmem⟩, rfl⟩
    exact ⟨m, abs_le_of_mem_Icc hmem, rfl⟩

/-- dim V_ℓ = 2ℓ + 1: the 2ℓ+1 spanning harmonics are orthonormal, hence
    linearly independent. -/
theorem angularSector_dim (ℓ : ℕ) :
    Module.finrank ℂ (AngularSector ℓ) = 2 * ℓ + 1 := by
  rw [angularSector_eq_span_range,
    finrank_span_eq_card (orthonormal_sphericalHarmonic ℓ).linearIndependent,
    Fintype.card_coe, sphericalHarmonic_count]

/-- The angular sectors are mutually orthogonal in L²(S²): orthogonality of
    the spanning harmonics (the ℓ ≠ ℓ' case of `sphericalHarmonic_orthonormal`)
    extends to spans. -/
theorem angularSector_orthogonal (ℓ ℓ' : ℕ) (hne : ℓ ≠ ℓ')
    (f g : L2_S2) (hf : f ∈ AngularSector ℓ) (hg : g ∈ AngularSector ℓ') :
    inner (𝕜 := ℂ) f g = 0 := by
  have key : Submodule.IsOrtho (AngularSector ℓ) (AngularSector ℓ') := by
    unfold AngularSector
    refine Submodule.isOrtho_span.mpr ?_
    rintro u ⟨m, hmu, rfl⟩ v ⟨m', hmv, rfl⟩
    rw [inner_toLp_sphericalHarmonic, sphericalHarmonic_orthonormal,
      if_neg (fun hcon => hne hcon.1)]
  exact key.inner_eq hf hg

end Spectra.SphericalHarmonics
