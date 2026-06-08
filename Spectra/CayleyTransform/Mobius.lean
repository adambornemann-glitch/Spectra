/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: CayleyTransform/Mobius.lean
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
/-!
# The Möbius Map from ℝ to the Unit Circle

This file develops properties of the Möbius transformation `μ ↦ (μ - i)/(μ + i)` which
maps the real line bijectively onto the unit circle minus `{1}`.

## Main statements

* `real_add_I_ne_zero`: `μ + i ≠ 0` for real `μ`
* `mobius_norm_one`: The Möbius image of a real number has norm 1
* `one_sub_mobius`: Formula for `1 - (μ - i)/(μ + i)`
* `mobius_coeff_identity`: Key algebraic identity used in spectral correspondence
-/
open Complex
namespace Spectra.Cayley

variable (μ : ℝ)

/-- `μ + i ≠ 0` for any real `μ`. -/
lemma real_add_I_ne_zero : (↑μ : ℂ) + I ≠ 0 := by
  intro h
  have : ((↑μ : ℂ) + I).im = 0 := by rw [h]; simp
  simp at this

/-- The Möbius map sends reals to the unit circle. -/
lemma mobius_norm_one (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    ‖(↑μ - I) * (↑μ + I)⁻¹‖ = 1 := by
  simp only [norm_mul, norm_inv]
  have h1 : ‖(↑μ : ℂ) - I‖ = ‖(↑μ : ℂ) + I‖ := by
    have h : starRingEnd ℂ ((↑μ : ℂ) + I) = (↑μ : ℂ) - I := by simp [Complex.ext_iff]
    rw [← h, RCLike.norm_conj]
  have h2 : ‖(↑μ : ℂ) + I‖ ≠ 0 := norm_ne_zero_iff.mpr hμ_ne
  field_simp [h2, h1]
  exact h1

/-- Variant of `mobius_norm_one` with the hypothesis inlined. -/
lemma mobius_norm_eq_one (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    ‖(↑μ - I) * (↑μ + I)⁻¹‖ = 1 :=
  mobius_norm_one μ hμ_ne

/-- Formula for `1 - w` where `w` is the Möbius image. -/
lemma one_sub_mobius (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    (1 : ℂ) - (↑μ - I) * (↑μ + I)⁻¹ = 2 * I / (↑μ + I) := by
  field_simp [hμ_ne]
  ring

/-- Formula for `1 + w` where `w` is the Möbius image. -/
lemma one_add_mobius (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    (1 : ℂ) + (↑μ - I) * (↑μ + I)⁻¹ = 2 * ↑μ / (↑μ + I) := by
  field_simp [hμ_ne]
  ring

/-- Key identity: `i(1 + w) = (1 - w)μ` for the Möbius image `w`. -/
lemma mobius_coeff_identity (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    let w := (↑μ - I) * (↑μ + I)⁻¹
    I * ((1 : ℂ) + w) = ((1 : ℂ) - w) * ↑μ := by
  simp only
  rw [one_sub_mobius μ hμ_ne, one_add_mobius μ hμ_ne]
  field_simp [hμ_ne]

/-- `1 - w ≠ 0` for the Möbius image `w` of a real. -/
lemma one_sub_mobius_ne_zero (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    (1 : ℂ) - (↑μ - I) * (↑μ + I)⁻¹ ≠ 0 := by
  rw [one_sub_mobius μ hμ_ne]
  simp [hμ_ne]

/-- `‖1 - w‖ > 0` for the Möbius image `w` of a real. -/
lemma one_sub_mobius_norm_pos (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    ‖(1 : ℂ) - (↑μ - I) * (↑μ + I)⁻¹‖ > 0 :=
  norm_pos_iff.mpr (one_sub_mobius_ne_zero μ hμ_ne)

/-- The inverse Möbius transformation, recovering μ from w. -/
noncomputable def inverseMobius (w : ℂ) : ℂ := I * (1 + w) / (1 - w)

/-- The inverse Möbius map sends the unit circle (minus 1) to reals. -/
lemma inverseMobius_real (w : ℂ) (hw_norm : ‖w‖ = 1) (hw_ne : w ≠ 1) :
    (inverseMobius w).im = 0 := by
  simp only [inverseMobius]
  have h1_sub_ne : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw_ne)
  set a := w.re with ha
  set b := w.im with hb
  have hab : a^2 + b^2 = 1 := by
    have hw_normSq : normSq w = 1 := by
      exact Real.sqrt_eq_one.mp hw_norm
    have : normSq w = a^2 + b^2 := by simp [normSq, ha, hb, sq]
    rw [hw_normSq] at this
    linarith
  have h_normSq_ne : Complex.normSq (1 - w) ≠ 0 := by exact (map_ne_zero normSq).mpr h1_sub_ne
  have h_normSq_eq : Complex.normSq (1 - w) = (1 - a)^2 + b^2 := by
    simp only [Complex.normSq,MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, sub_re, one_re,
      sub_im, one_im, zero_sub, mul_neg, neg_mul, neg_neg]
    ring
  have h_denom_pos : (1 - a)^2 + b^2 > 0 := by
    rw [← h_normSq_eq]
    exact Complex.normSq_pos.mpr h1_sub_ne
  rw [div_eq_mul_inv, Complex.mul_im]
  simp only [Complex.inv_re, Complex.inv_im, Complex.mul_re, Complex.mul_im,
             Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
             Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
             ← ha, ← hb]
  simp only [zero_mul, one_mul, zero_add, zero_sub, neg_neg]
  rw [h_normSq_eq]
  field_simp [ne_of_gt h_denom_pos]
  nlinarith [sq_nonneg a, sq_nonneg b, hab]

/-- Möbius composed with inverse Möbius is identity on unit circle minus {1}. -/
lemma mobius_inverseMobius (w : ℂ) (_ /-hw_norm-/ : ‖w‖ = 1) (hw_ne : w ≠ 1) :
    (inverseMobius w - I) * (inverseMobius w + I)⁻¹ = w := by
  simp only [inverseMobius]
  have h1_sub_ne : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw_ne)
  have hI_ne : (I : ℂ) ≠ 0 := I_ne_zero
  have h2I_ne : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero hI_ne
  have h_num : I * (1 + w) / (1 - w) - I = 2 * I * w / (1 - w) := by
    field_simp [h1_sub_ne]
    ring
  have h_denom : I * (1 + w) / (1 - w) + I = 2 * I / (1 - w) := by
    field_simp [h1_sub_ne]
    ring
  have h_denom_ne : 2 * I / (1 - w) ≠ 0 := div_ne_zero h2I_ne h1_sub_ne
  rw [h_num, h_denom]
  field_simp [h1_sub_ne, h2I_ne]

/-- Inverse Möbius composed with Möbius is identity on reals. -/
lemma inverseMobius_mobius (μ : ℝ) :
    inverseMobius ((↑μ - I) * (↑μ + I)⁻¹) = μ := by
  simp only [inverseMobius]
  have hμ_ne : (↑μ : ℂ) + I ≠ 0 := real_add_I_ne_zero μ
  have h1_sub_ne : 1 - (↑μ - I) * (↑μ + I)⁻¹ ≠ 0 := one_sub_mobius_ne_zero μ hμ_ne
  field_simp [hμ_ne, h1_sub_ne]
  ring

end Spectra.Cayley
