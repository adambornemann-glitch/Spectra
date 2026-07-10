/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Spectra.Bochner.Borel.Measure.Basic
import Spectra.Mathlib.CharFunBridge
import Spectra.YosidaHille.Basic
/-!
# Polarized spectral measures and the keystone lemma

For a strongly continuous one-parameter unitary group `U` we already have the diagonal scalar
spectral measures `μ_ξ := borelMeasure U ξ` with

  `⟪ξ, U(t) ξ⟫ = ∫ e^{itλ} dμ_ξ(λ)`,   `μ_ξ(ℝ) = ‖ξ‖²`.

This file defines the *off-diagonal* pairing by polarization — not as a complex measure object,
but as the scalar functional

  `spectralForm U ξ η g  :=  "∫ g dμ_{ξ,η}"`

given by the four-term combination mirroring `inner_eq_sum_norm_sq_div_four` exactly:

  `spectralForm ξ η g = (∫g dμ_{ξ+η} − ∫g dμ_{ξ−η} + (∫g dμ_{ξ−I•η} − ∫g dμ_{ξ+I•η})·I) / 4`.

The design intent (see AUDIT.md §1.6): every lemma is a statement about scalars, so the entire
file runs on machinery already proven (positive Borel–Stieltjes measures) plus the
`CharFunBridge` workhorse; packaging as a genuine `MeasureTheory.ComplexMeasure` is a later,
local refactor.

## Main statements (sorry count 0)

* `spectralForm_char` — `spectralForm ξ η (e^{i·t}) = ⟪ξ, U(t) η⟫`: the defining property.
* sesquilinearity (`_add_left`, `_add_right`, `_smul_left`, `_smul_right`, `_conj_symm`).
* `norm_spectralForm_le` — `‖spectralForm ξ η g‖ ≤ 2C‖ξ‖‖η‖` for `‖g‖ ≤ C` (crude constant;
  the sharp `C` comes after the calculus exists and is not needed before then).
* `spectralForm_unitary_right` — **keystone**:
  `spectralForm ξ (U(t)η) g = spectralForm ξ η (e^{itλ}·g)`.
  This is multiplicativity-in-waiting: applied to indicators it will give `E(S)E(T) = E(S∩T)`
  with no Stone–Weierstrass and no operator topology arguments.
-/
open Complex MeasureTheory
open scoped InnerProductSpace
open Spectra.Fourier
open Spectra.Borel
open SpectralMeasure
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.QuantumMechanics
variable (U_grp : OneParameterUnitaryGroup (H := H))
namespace SpectralTheory

/-! ## The polarized pairing -/

/-- The polarized spectral pairing `g ↦ "∫ g dμ_{ξ,η}"`, by the same sign pattern as
`inner_eq_sum_norm_sq_div_four` (conjugate-linear slot first, matching Mathlib and the rest of
the project).  For `g = 1` this is `⟪ξ, η⟫`; for `g = e^{i·t}` it is `⟪ξ, U(t) η⟫`
(`spectralForm_char`). -/
noncomputable def spectralForm (ξ η : H) (g : ℝ → ℂ) : ℂ :=
  ((∫ l, g l ∂(borelMeasure U_grp (ξ + η)))
    - (∫ l, g l ∂(borelMeasure U_grp (ξ - η)))
    + ((∫ l, g l ∂(borelMeasure U_grp (ξ - I • η)))
        - (∫ l, g l ∂(borelMeasure U_grp (ξ + I • η)))) * I) / 4

/-- **Defining property**: on characters, the polarized pairing returns the matrix elements of
the group.  This is the polarization identity for the sesquilinear form `(x, y) ↦ ⟪x, U(t) y⟫`:
expand the four `borelMeasure_fourier` identities by sesquilinearity; the residue of the
`ring`-level algebra is exactly `(r − q)(1 + I²)/2`, killed by `I² = −1`. -/
theorem spectralForm_char (ξ η : H) (t : ℝ) :
    spectralForm U_grp ξ η (fun l => cexp (I * l * t)) = ⟪ξ, U_grp.U t η⟫_ℂ := by
  simp only [spectralForm]
  rw [← borelMeasure_fourier U_grp (ξ + η) t, ← borelMeasure_fourier U_grp (ξ - η) t,
      ← borelMeasure_fourier U_grp (ξ - I • η) t, ← borelMeasure_fourier U_grp (ξ + I • η) t]
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_I]
  linear_combination ((⟪η, U_grp.U t ξ⟫_ℂ - ⟪ξ, U_grp.U t η⟫_ℂ) / 2) * Complex.I_mul_I

/-- Diagonal consistency: `spectralForm ξ ξ g = ∫ g dμ_ξ`.
All four vectors are `c • ξ` for `c ∈ {2, 0, 1−I, 1+I}`; `borelMeasure_smul` turns each integral
into `conj c · c · ∫ g dμ_ξ`, and in that form the four terms collapse by `ring` alone
(`(1+I)(1−I) − (1−I)(1+I) = 0` commutatively, no `I² = −1` needed).
The hypotheses on `g` are not used by this proof; they are kept for signature stability. -/
theorem spectralForm_self (ξ : H) {g : ℝ → ℂ}
    (_hg_meas : Measurable g) (_hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) :
    spectralForm U_grp ξ ξ g = ∫ l, g l ∂(borelMeasure U_grp ξ) := by
  have key : ∀ c : ℂ, (∫ l, g l ∂(borelMeasure U_grp (c • ξ)))
      = (starRingEnd ℂ) c * c * ∫ l, g l ∂(borelMeasure U_grp ξ) := by
    intro c
    have hcc : (starRingEnd ℂ) c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.conj_mul]; norm_cast
    rw [borelMeasure_smul, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul,
      hcc]
    norm_cast
  have e1 : ξ + ξ = (2 : ℂ) • ξ := (two_smul ℂ ξ).symm
  have e2 : ξ - ξ = (0 : ℂ) • ξ := by rw [zero_smul, sub_self]
  have e3 : ξ - I • ξ = ((1 : ℂ) - I) • ξ := by rw [sub_smul, one_smul]
  have e4 : ξ + I • ξ = ((1 : ℂ) + I) • ξ := by rw [add_smul, one_smul]
  simp only [spectralForm]
  rw [e1, e2, e3, e4, key 2, key 0, key ((1 : ℂ) - I), key ((1 : ℂ) + I)]
  simp only [map_ofNat, map_zero, map_sub, map_add, map_one, Complex.conj_I]
  ring

/-- Normalization: at `g = 1` the polarized pairing is the inner product —
`spectralForm_char` at `t = 0`, where the character is the constant `1`. -/
theorem spectralForm_one (ξ η : H) :
    spectralForm U_grp ξ η (fun _ => (1 : ℂ)) = ⟪ξ, η⟫_ℂ := by
  have hfun : (fun l : ℝ => cexp (I * l * ((0 : ℝ) : ℂ))) = fun _ : ℝ => (1 : ℂ) := by
    funext l
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have h := spectralForm_char U_grp ξ η 0
  rw [U_grp.identity, ContinuousLinearMap.id_apply, hfun] at h
  exact h

/-! ### Sesquilinearity

Each of these compares two finite complex combinations of positive measures that agree on
characters, so each is an instance of `borel_combination_ext` with explicit coefficient/vector
families.  The character-side identities are sesquilinear-expansion algebra: `add_right` and
`conj_symm` are *polynomial* identities in the atoms (closed by `ring`), while `smul_right`
leaves the residue `(conj c − c)·⟪η, U(t)ξ⟫·(1 + I²)/2` and needs `I² = −1`.
Boundedness/measurability hypotheses on `g` are intrinsic, not incidental. -/

theorem spectralForm_add_right (ξ η₁ η₂ : H) {g : ℝ → ℂ}
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) :
    spectralForm U_grp ξ (η₁ + η₂) g
      = spectralForm U_grp ξ η₁ g + spectralForm U_grp ξ η₂ g := by
  have key := borel_combination_ext U_grp
    (![1 / 4, -(1 / 4), I / 4, -(I / 4)])
    (![ξ + (η₁ + η₂), ξ - (η₁ + η₂), ξ - I • (η₁ + η₂), ξ + I • (η₁ + η₂)])
    (![1 / 4, -(1 / 4), I / 4, -(I / 4), 1 / 4, -(1 / 4), I / 4, -(I / 4)])
    (![ξ + η₁, ξ - η₁, ξ - I • η₁, ξ + I • η₁, ξ + η₂, ξ - η₂, ξ - I • η₂, ξ + I • η₂])
    (fun t => by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, add_zero, map_add, map_sub, map_smul, inner_add_left,
        inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        Complex.conj_I]
      ring)
    hg_meas hg_bdd
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    add_zero] at key
  simp only [spectralForm]
  linear_combination key

theorem spectralForm_smul_right (ξ η : H) (c : ℂ) {g : ℝ → ℂ}
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) :
    spectralForm U_grp ξ (c • η) g = c * spectralForm U_grp ξ η g := by
  have key := borel_combination_ext U_grp
    (![1 / 4, -(1 / 4), I / 4, -(I / 4)])
    (![ξ + c • η, ξ - c • η, ξ - I • (c • η), ξ + I • (c • η)])
    (![c / 4, -(c / 4), c * I / 4, -(c * I / 4)])
    (![ξ + η, ξ - η, ξ - I • η, ξ + I • η])
    (fun t => by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, add_zero, map_add, map_sub, map_smul, inner_add_left,
        inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        Complex.conj_I]
      linear_combination ((((starRingEnd ℂ) c - c) * ⟪η, U_grp.U t ξ⟫_ℂ) / 2)
        * Complex.I_mul_I)
    hg_meas hg_bdd
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    add_zero] at key
  simp only [spectralForm]
  linear_combination key

/-- Conjugate symmetry, the measure-level avatar of `μ_{η,ξ} = conj μ_{ξ,η}`.
Pushing the outer conjugation through the four *positive* measures (`integral_conj`) flips only
the sign of the `I`-weighted pair, so the claim is `borel_combination_ext` between the
`(η, ξ)`-family and the `(ξ, η)`-family with coefficients `(1/4, −1/4, −I/4, I/4)`; the
character-side identity is polynomial (both sides expand to `(2q + 2r + 2I²q − 2I²r)/4`). -/
theorem spectralForm_conj_symm (ξ η : H) {g : ℝ → ℂ}
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) :
    spectralForm U_grp η ξ g
      = starRingEnd ℂ (spectralForm U_grp ξ η (fun l => starRingEnd ℂ (g l))) := by
  have key := borel_combination_ext U_grp
    (![1 / 4, -(1 / 4), I / 4, -(I / 4)])
    (![η + ξ, η - ξ, η - I • ξ, η + I • ξ])
    (![1 / 4, -(1 / 4), -(I / 4), I / 4])
    (![ξ + η, ξ - η, ξ - I • η, ξ + I • η])
    (fun t => by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, add_zero, map_add, map_sub, map_smul, inner_add_left,
        inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        Complex.conj_I]
      ring)
    hg_meas hg_bdd
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    add_zero] at key
  simp only [spectralForm, integral_conj, map_div₀, map_add, map_sub, map_mul, map_ofNat,
    Complex.conj_I, Complex.conj_conj]
  linear_combination key

/-- Additivity in the conjugate-linear slot.  Direct `borel_combination_ext` instance; on
characters the identity is polynomial in the atoms, exactly as in `spectralForm_add_right`. -/
theorem spectralForm_add_left (ξ₁ ξ₂ η : H) {g : ℝ → ℂ}
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) :
    spectralForm U_grp (ξ₁ + ξ₂) η g
      = spectralForm U_grp ξ₁ η g + spectralForm U_grp ξ₂ η g := by
  have key := borel_combination_ext U_grp
    (![1 / 4, -(1 / 4), I / 4, -(I / 4)])
    (![ξ₁ + ξ₂ + η, ξ₁ + ξ₂ - η, ξ₁ + ξ₂ - I • η, ξ₁ + ξ₂ + I • η])
    (![1 / 4, -(1 / 4), I / 4, -(I / 4), 1 / 4, -(1 / 4), I / 4, -(I / 4)])
    (![ξ₁ + η, ξ₁ - η, ξ₁ - I • η, ξ₁ + I • η, ξ₂ + η, ξ₂ - η, ξ₂ - I • η, ξ₂ + I • η])
    (fun t => by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, add_zero, map_add, map_sub, map_smul, inner_add_left,
        inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        Complex.conj_I]
      ring)
    hg_meas hg_bdd
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    add_zero] at key
  simp only [spectralForm]
  linear_combination key

/-- Conjugate-homogeneity in the first slot: `spectralForm (c•ξ) η g = conj c · spectralForm`.
The character-side residue is `(c − conj c)·⟪η, U(t)ξ⟫·(1 + I²)/2` — the mirror of
`spectralForm_smul_right`, with the conjugate landing on the other atom. -/
theorem spectralForm_smul_left (ξ η : H) (c : ℂ) {g : ℝ → ℂ}
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) :
    spectralForm U_grp (c • ξ) η g = (starRingEnd ℂ) c * spectralForm U_grp ξ η g := by
  have key := borel_combination_ext U_grp
    (![1 / 4, -(1 / 4), I / 4, -(I / 4)])
    (![c • ξ + η, c • ξ - η, c • ξ - I • η, c • ξ + I • η])
    (![(starRingEnd ℂ) c / 4, -((starRingEnd ℂ) c / 4),
        (starRingEnd ℂ) c * I / 4, -((starRingEnd ℂ) c * I / 4)])
    (![ξ + η, ξ - η, ξ - I • η, ξ + I • η])
    (fun t => by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, add_zero, map_add, map_sub, map_smul, inner_add_left,
        inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        Complex.conj_I]
      linear_combination ((c - (starRingEnd ℂ) c) * ⟪η, U_grp.U t ξ⟫_ℂ / 2)
        * Complex.I_mul_I)
    hg_meas hg_bdd
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    add_zero] at key
  simp only [spectralForm]
  linear_combination key

/-! ### Linearity in the function slot -/

-- `integrable_of_bounded` lives in `Spectra.Fourier` (`CharFunBridge`); it is in scope here
-- via `open Spectra.Fourier`.

/-- Additivity in the function slot: integrals split (`integral_add`, with integrability
from boundedness), and the four-term combinations rearrange by `ring`. -/
theorem spectralForm_add_fun (ξ η : H) {g₁ g₂ : ℝ → ℂ}
    (hg₁_meas : Measurable g₁) (hg₁_bdd : ∃ C, ∀ ω, ‖g₁ ω‖ ≤ C)
    (hg₂_meas : Measurable g₂) (hg₂_bdd : ∃ C, ∀ ω, ‖g₂ ω‖ ≤ C) :
    spectralForm U_grp ξ η (fun l => g₁ l + g₂ l)
      = spectralForm U_grp ξ η g₁ + spectralForm U_grp ξ η g₂ := by
  obtain ⟨C₁, hC₁⟩ := hg₁_bdd
  obtain ⟨C₂, hC₂⟩ := hg₂_bdd
  have hsplit : ∀ v : H, (∫ l, g₁ l + g₂ l ∂(borelMeasure U_grp v))
      = (∫ l, g₁ l ∂(borelMeasure U_grp v)) + ∫ l, g₂ l ∂(borelMeasure U_grp v) := fun v =>
    integral_add (integrable_of_bounded hg₁_meas hC₁) (integrable_of_bounded hg₂_meas hC₂)
  simp only [spectralForm, hsplit]
  ring

/-- Scalars pull out of the function slot unconditionally (`integral_const_mul` needs no
integrability). -/
theorem spectralForm_smul_fun (ξ η : H) (c : ℂ) (g : ℝ → ℂ) :
    spectralForm U_grp ξ η (fun l => c * g l) = c * spectralForm U_grp ξ η g := by
  simp only [spectralForm, integral_const_mul]
  ring

/-- Crude operator-norm bound, sufficient for `continuousLinearMapOfBilin`. -/
theorem norm_spectralForm_le (ξ η : H) {g : ℝ → ℂ} {C : ℝ}
    (hg_meas : Measurable g) (hg_bdd : ∀ ω, ‖g ω‖ ≤ C) :
    ‖spectralForm U_grp ξ η g‖ ≤ 2 * C * ‖ξ‖ * ‖η‖ := by
  -- Step 0: the elementary estimate `‖(a − b + (c − d)·I)/4‖ ≤ (‖a‖+‖b‖+‖c‖+‖d‖)/4`.
  have habs : ∀ a b c d : ℂ,
      ‖(a - b + (c - d) * I) / 4‖ ≤ (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) / 4 := by
    intro a b c d
    rw [norm_div, Complex.norm_ofNat]
    gcongr
    calc ‖a - b + (c - d) * I‖
        ≤ ‖a - b‖ + ‖(c - d) * I‖ := norm_add_le _ _
      _ = ‖a - b‖ + ‖c - d‖ := by rw [norm_mul, Complex.norm_I, mul_one]
      _ ≤ ‖a‖ + ‖b‖ + (‖c‖ + ‖d‖) := add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
      _ = ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by ring
  -- Step 1: each diagonal integral is bounded by `C · mass = C·‖v‖²`.
  have hint : ∀ v : H, ‖∫ l, g l ∂(borelMeasure U_grp v)‖ ≤ C * (‖v‖ * ‖v‖) := by
    intro v
    haveI : IsFiniteMeasure (borelMeasure U_grp v) := borelMeasure_isFiniteMeasure U_grp v
    have h := norm_integral_le_of_norm_le (μ := borelMeasure U_grp v)
      (integrable_const C) (Filter.Eventually.of_forall hg_bdd)
    rw [integral_const, smul_eq_mul, Measure.real_def, borelMeasure_mass] at h
    calc ‖∫ l, g l ∂(borelMeasure U_grp v)‖ ≤ ‖v‖ ^ 2 * C := h
      _ = C * (‖v‖ * ‖v‖) := by ring
  -- Step 2: the crude bound `C(‖x‖² + ‖y‖²)`, parallelogram law twice.
  have hmain : ∀ x y : H,
      ‖spectralForm U_grp x y g‖ ≤ C * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) := by
    intro x y
    have h1 := hint (x + y)
    have h2 := hint (x - y)
    have h3 := hint (x - I • y)
    have h4 := hint (x + I • y)
    have hpar1 := parallelogram_law_with_norm (𝕜 := ℂ) x y
    have hpar2 := parallelogram_law_with_norm (𝕜 := ℂ) x (I • y)
    rw [norm_smul, Complex.norm_I, one_mul] at hpar2
    calc ‖spectralForm U_grp x y g‖
        ≤ (‖∫ l, g l ∂(borelMeasure U_grp (x + y))‖
            + ‖∫ l, g l ∂(borelMeasure U_grp (x - y))‖
            + ‖∫ l, g l ∂(borelMeasure U_grp (x - I • y))‖
            + ‖∫ l, g l ∂(borelMeasure U_grp (x + I • y))‖) / 4 := by
          simp only [spectralForm]; exact habs _ _ _ _
      _ ≤ (C * (‖x + y‖ * ‖x + y‖) + C * (‖x - y‖ * ‖x - y‖)
            + C * (‖x - I • y‖ * ‖x - I • y‖)
            + C * (‖x + I • y‖ * ‖x + I • y‖)) / 4 := by gcongr
      _ = C * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) := by
          linear_combination (C / 4) * hpar1 + (C / 4) * hpar2
  -- Step 3a: `η = 0` — the form vanishes by `smul_right` at `c = 0`.
  rcases eq_or_ne η 0 with rfl | hη
  · have h0 : spectralForm U_grp ξ (0 : H) g = 0 := by
      have h := spectralForm_smul_right U_grp ξ (0 : H) (0 : ℂ) hg_meas ⟨C, hg_bdd⟩
      simpa using h
    simp [h0]
  -- Step 3b: `ξ = 0` — the four measures cancel in pairs, since `μ_{−v} = μ_v`.
  rcases eq_or_ne ξ 0 with rfl | hξ
  · have hneg : ∀ v : H, borelMeasure U_grp (-v) = borelMeasure U_grp v := by
      intro v
      have h := borelMeasure_smul U_grp (-1 : ℂ) v
      simpa using h
    have h0 : spectralForm U_grp (0 : H) η g = 0 := by
      simp only [spectralForm, zero_add, zero_sub, hneg]
      ring
    simp [h0]
  -- Step 4: rescale `η ↦ (‖ξ‖/‖η‖) • η` and optimize: `C(‖ξ‖² + ‖ξ‖²)/t = 2C‖ξ‖‖η‖`.
  have hξ0 : (0 : ℝ) < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hη0 : (0 : ℝ) < ‖η‖ := norm_pos_iff.mpr hη
  set t : ℝ := ‖ξ‖ / ‖η‖ with ht_def
  have ht : 0 < t := div_pos hξ0 hη0
  have hb := hmain ξ ((t : ℂ) • η)
  rw [spectralForm_smul_right U_grp ξ η (t : ℂ) hg_meas ⟨C, hg_bdd⟩, norm_mul, norm_smul,
    Complex.norm_of_nonneg ht.le] at hb
  have htη : t * ‖η‖ = ‖ξ‖ := by
    rw [ht_def]; exact div_mul_cancel₀ ‖ξ‖ hη0.ne'
  rw [htη] at hb
  have key : ‖spectralForm U_grp ξ η g‖ ≤ C * (‖ξ‖ * ‖ξ‖ + ‖ξ‖ * ‖ξ‖) / t :=
    (le_div_iff₀' ht).mpr hb
  refine key.trans (le_of_eq ?_)
  rw [ht_def, div_div_eq_mul_div, div_eq_iff hξ0.ne']
  ring

/-! ## The keystone -/

/- `CharFunBridge`'s `measurable_char` / `norm_char_le_one` are `private`; restate locally,
in both character orientations. -/

lemma char_measurable (t : ℝ) : Measurable fun ω : ℝ => cexp (I * ω * t) :=
  (Complex.continuous_exp.comp (by fun_prop)).measurable

private lemma neg_char_measurable (t : ℝ) : Measurable fun ω : ℝ => cexp (-(I * ω * t)) :=
  (Complex.continuous_exp.comp (by fun_prop)).measurable

lemma char_norm_le_one (t ω : ℝ) : ‖cexp (I * ω * t)‖ ≤ 1 := by
  have h0 : (I * (ω : ℂ) * (t : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  exact le_of_eq (by rw [Complex.norm_exp, h0, Real.exp_zero])

private lemma neg_char_norm_le_one (t ω : ℝ) : ‖cexp (-(I * ω * t))‖ ≤ 1 := by
  have h0 : (-(I * (ω : ℂ) * (t : ℂ))).re = 0 := by
    simp [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  exact le_of_eq (by rw [Complex.norm_exp, h0, Real.exp_zero])

/-- **Keystone.**  Moving the group through the pairing twists the integrand by a character:

  `"∫ g dμ_{ξ, U(t)η}" = "∫ e^{itλ} g(λ) dμ_{ξ,η}"`.

Instance of `integral_combination_ext` with densities `f = 1` on the left and `k = e^{it·}` on
the right; on characters `e^{i·s}` the identity is the group law
`⟪ξ, U(s)(U(t)η)⟫ = ⟪ξ, U(s+t)η⟫` together with `e^{iλs}·e^{iλt} = e^{iλ(s+t)}`, both sides
read off by `spectralForm_char`.

Downstream: with `Φ(g)` defined from `spectralForm` via `continuousLinearMapOfBilin`, this lemma
*is* `Φ(g) ∘ U(t) = Φ(e^{it·}g)`, whence `μ_{ξ,Φ(h)η} = h·dμ_{ξ,η}` and
`Φ(g)Φ(h) = Φ(gh)` — multiplicativity with no Stone–Weierstrass. -/
theorem spectralForm_unitary_right (ξ η : H) (t : ℝ) {g : ℝ → ℂ}
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) :
    spectralForm U_grp ξ (U_grp.U t η) g
      = spectralForm U_grp ξ η (fun l => cexp (I * l * t) * g l) := by
  have key := integral_combination_ext
    (![1 / 4, -(1 / 4), I / 4, -(I / 4)])
    (fun i => borelMeasure U_grp
      (![ξ + U_grp.U t η, ξ - U_grp.U t η,
          ξ - I • U_grp.U t η, ξ + I • U_grp.U t η] i))
    (fun _ _ => (1 : ℂ))
    (![1 / 4, -(1 / 4), I / 4, -(I / 4)])
    (fun j => borelMeasure U_grp (![ξ + η, ξ - η, ξ - I • η, ξ + I • η] j))
    (fun _ ω => cexp (I * ω * t))
    (fun _ => measurable_const) (fun _ => ⟨1, fun _ => by simp⟩)
    (fun _ => char_measurable t) (fun _ => ⟨1, fun ω => char_norm_le_one t ω⟩)
    (fun s => by
      have A := spectralForm_char U_grp ξ (U_grp.U t η) s
      have B := spectralForm_char U_grp ξ η (s + t)
      simp only [spectralForm, ← borelMeasure_fourier] at A B
      have hglue : ⟪ξ, U_grp.U s (U_grp.U t η)⟫_ℂ = ⟪ξ, U_grp.U (s + t) η⟫_ℂ := by
        rw [U_grp.group_law, ContinuousLinearMap.comp_apply]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, add_zero, mul_one, ← Complex.exp_add, ← mul_add,
        ← Complex.ofReal_add, ← borelMeasure_fourier]
      linear_combination A - B + hglue)
    hg_meas hg_bdd
  have hflip : ∀ v : H, (∫ l, cexp (I * l * t) * g l ∂(borelMeasure U_grp v))
      = ∫ l, g l * cexp (I * l * t) ∂(borelMeasure U_grp v) := fun v =>
    integral_congr_ae (.of_forall fun ω => mul_comm _ _)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    add_zero, mul_one] at key
  simp only [spectralForm, hflip]
  linear_combination key

/-- Companion on the left slot (conjugate twist).  Proved directly by the same template as
`spectralForm_unitary_right` (rather than through `spectralForm_conj_symm`, which would cost
function-level conjugation plumbing): densities `1` vs `e^{−it·}`, and on characters the glue is
unitarity, `⟪U(t)ξ, U(s)η⟫ = ⟪ξ, U(s−t)η⟫`, against `e^{iλs}·e^{−iλt} = e^{iλ(s−t)}`.
Stated now because the adjoint identity `Φ(g)† = Φ(conj g)` will want it. -/
theorem spectralForm_unitary_left (ξ η : H) (t : ℝ) {g : ℝ → ℂ}
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) :
    spectralForm U_grp (U_grp.U t ξ) η g
      = spectralForm U_grp ξ η (fun l => cexp (-(I * l * t)) * g l) := by
  have key := integral_combination_ext
    (![1 / 4, -(1 / 4), I / 4, -(I / 4)])
    (fun i => borelMeasure U_grp
      (![U_grp.U t ξ + η, U_grp.U t ξ - η,
          U_grp.U t ξ - I • η, U_grp.U t ξ + I • η] i))
    (fun _ _ => (1 : ℂ))
    (![1 / 4, -(1 / 4), I / 4, -(I / 4)])
    (fun j => borelMeasure U_grp (![ξ + η, ξ - η, ξ - I • η, ξ + I • η] j))
    (fun _ ω => cexp (-(I * ω * t)))
    (fun _ => measurable_const) (fun _ => ⟨1, fun _ => by simp⟩)
    (fun _ => neg_char_measurable t) (fun _ => ⟨1, fun ω => neg_char_norm_le_one t ω⟩)
    (fun s => by
      have A := spectralForm_char U_grp (U_grp.U t ξ) η s
      have B := spectralForm_char U_grp ξ η (s - t)
      simp only [spectralForm, ← borelMeasure_fourier] at A B
      have hglue : ⟪U_grp.U t ξ, U_grp.U s η⟫_ℂ = ⟪ξ, U_grp.U (s - t) η⟫_ℂ := by
        have hs : U_grp.U s η = U_grp.U t (U_grp.U (s - t) η) := by
          rw [← ContinuousLinearMap.comp_apply, ← U_grp.group_law,
            show t + (s - t) = s from by ring]
        rw [hs, U_grp.unitary]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, add_zero, mul_one, ← Complex.exp_add, ← sub_eq_add_neg,
        ← mul_sub, ← Complex.ofReal_sub, ← borelMeasure_fourier]
      linear_combination A - B + hglue)
    hg_meas hg_bdd
  have hflip : ∀ v : H, (∫ l, cexp (-(I * l * t)) * g l ∂(borelMeasure U_grp v))
      = ∫ l, g l * cexp (-(I * l * t)) ∂(borelMeasure U_grp v) := fun v =>
    integral_congr_ae (.of_forall fun ω => mul_comm _ _)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    add_zero, mul_one] at key
  simp only [spectralForm, hflip]
  linear_combination key

end Spectra.QuantumMechanics.SpectralTheory
