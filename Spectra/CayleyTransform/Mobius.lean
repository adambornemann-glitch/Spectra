/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.Complex.Basic
/-!
# The Möbius Map from ℝ to the Unit Circle

This file develops properties of the Möbius transformation `μ ↦ (μ - i)/(μ + i)` which
maps the real line bijectively onto the unit circle minus `{1}`, together with its inverse
`w ↦ i(1 + w)/(1 - w)`. This is the algebraic engine behind the Cayley transform of a
self-adjoint operator: `Eigenvalue.lean` and `BorelCalculus.lean` build the spectral
correspondence between a self-adjoint operator's real spectrum and its Cayley transform's
unitary spectrum on the circle directly on top of the identities proved here.

## Main statements

* `real_add_I_ne_zero`: `μ + i ≠ 0` for real `μ`
* `mobius_norm_one`: the Möbius image of a real number has norm 1
* `one_sub_mobius`: formula for `1 - (μ - i)/(μ + i)`
* `one_add_mobius`: formula for `1 + (μ - i)/(μ + i)`
* `mobius_coeff_identity`: key algebraic identity used in spectral correspondence
* `one_sub_mobius_ne_zero`: `1 - w ≠ 0` for the Möbius image `w`
* `one_sub_mobius_norm_pos`: `‖1 - w‖ > 0` for the Möbius image `w`
* `inverseMobius`: the inverse map `w ↦ i(1 + w)/(1 - w)`, recovering `μ` from `w`
* `inverseMobius_real`: the inverse map sends the unit circle (minus `1`) back to the reals
* `mobius_inverseMobius`: the inverse map really is a left inverse of the Möbius map

## Implementation notes

Six lemmas (`mobius_norm_one` through `one_sub_mobius_norm_pos`) take `hμ_ne : (↑μ:ℂ) + I ≠ 0`
as an explicit hypothesis even though `real_add_I_ne_zero μ` proves it unconditionally for every
real `μ`. This is deliberate, not an oversight: `Eigenvalue.lean`'s own public lemmas thread the
identical hypothesis through their signatures the same way (e.g. `cayley_shift_identity`), so
callers already carry `hμ_ne` as a named local fact from one proof step to the next rather than
re-deriving it at each call; matching that convention here keeps the two files consistent.

## References

* Reed–Simon, *Methods of Modern Mathematical Physics I*, §VIII.3 (the Cayley transform of a
  self-adjoint operator, built on this scalar Möbius correspondence)
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

/-- The inverse Möbius map sends the unit circle (minus 1) to reals.

Proof: `‖w‖ = 1` gives `conj w = w⁻¹`, from which `conj (inverseMobius w) = inverseMobius w`
follows by a direct field computation; a complex number fixed by conjugation is real. -/
lemma inverseMobius_real (w : ℂ) (hw_norm : ‖w‖ = 1) (hw_ne : w ≠ 1) :
    (inverseMobius w).im = 0 := by
  have hw_ne0 : w ≠ 0 := fun h => by simp [h] at hw_norm
  have h1_sub_ne : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw_ne)
  have hw1_ne : w - 1 ≠ 0 := sub_ne_zero.mpr hw_ne
  have h1_sub_inv_ne : (1 : ℂ) - w⁻¹ ≠ 0 := by
    have hrw : (1 : ℂ) - w⁻¹ = -(1 - w) * w⁻¹ := by field_simp; ring
    rw [hrw]
    exact mul_ne_zero (neg_ne_zero.mpr h1_sub_ne) (inv_ne_zero hw_ne0)
  rw [← Complex.conj_eq_iff_im, inverseMobius, map_div₀, map_mul, map_add, map_sub, map_one,
      Complex.conj_I, ← Complex.inv_eq_conj hw_norm]
  field_simp [h1_sub_ne, h1_sub_inv_ne, hw_ne0, hw1_ne]
  ring

/-- Möbius composed with inverse Möbius is identity on unit circle minus {1}. -/
lemma mobius_inverseMobius (w : ℂ) (hw_ne : w ≠ 1) :
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
  have _h_denom_ne : 2 * I / (1 - w) ≠ 0 := div_ne_zero h2I_ne h1_sub_ne
  rw [h_num, h_denom]
  field_simp [h1_sub_ne, h2I_ne]

end Spectra.Cayley
