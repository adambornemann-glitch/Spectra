/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Yosida/Symmetry.lean
-/
import Spectra.YosidaHille.Approximation.Bounds

/-!
# Symmetry Properties of Yosida Operators

This file proves that the symmetric Yosida approximant is self-adjoint,
and that `I • Aₙˢʸᵐ` is skew-adjoint. These properties are essential for
showing that `exp(i·Aₙˢʸᵐ·t)` is unitary.

## Main results

* `yosidaApproxSym_selfAdjoint`: `(Aₙˢʸᵐ)* = Aₙˢʸᵐ`
* `I_smul_yosidaApproxSym_skewAdjoint`: `(i·Aₙˢʸᵐ)* = -(i·Aₙˢʸᵐ)`

-/
open Complex InnerProductSpace Spectra.Resolvent
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Stone.Yosida
variable {U_grp : OneParameterUnitaryGroup (H := H)}

lemma yosidaApproxSym_selfAdjoint {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) :
    (yosidaApproxSym hsym hplus hminus n).adjoint = yosidaApproxSym hsym hplus hminus n := by
  unfold yosidaApproxSym resolventAtIn resolventAtNegIn
  ext φ
  apply ext_inner_right ℂ
  intro ψ
  -- Use ⟨T*φ, ψ⟩ = ⟨φ, Tψ⟩
  rw [ContinuousLinearMap.adjoint_inner_left]
  -- Expand the smul and add on both sides
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply]
  -- The scalar n²/2 is real
  have h_scalar_real : (starRingEnd ℂ) ((n : ℂ)^2 / 2) = (n : ℂ)^2 / 2 := by
    simp only [map_div₀, map_pow]
    congr 1
    simp
    exact conj_eq_iff_re.mpr rfl
  -- Pull scalars through inner products
  rw [inner_smul_right, inner_smul_left, h_scalar_real]
  congr 1
  -- Now show ⟨φ, (R(in) + R(-in)) ψ⟩ = ⟨(R(in) + R(-in)) φ, ψ⟩
  rw [inner_add_right, inner_add_left]
  -- Use resolvent_adjoint: ⟨φ, R(z)ψ⟩ = ⟨R(z̄)φ, ψ⟩
  have h1 : ⟪φ, resolvent (I * ↑↑n) (I_mul_pnat_im_ne_zero n) hsym hplus hminus ψ⟫_ℂ =
            ⟪resolvent (-I * ↑↑n) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus φ, ψ⟫_ℂ := by
    have hadj := resolvent_adjoint hsym hplus hminus (I * ↑↑n) (I_mul_pnat_im_ne_zero n)
    have h_conj : (starRingEnd ℂ) (I * ↑↑n) = -I * ↑↑n := by simp []
    rw [← ContinuousLinearMap.adjoint_inner_left]
    congr 1
    rw [hadj]
    congr 1
    rw [← hadj]
    simp_all only [map_div₀, map_pow, map_natCast, neg_mul, map_mul, conj_I]
  have h2 : ⟪φ, resolvent (-I * ↑↑n) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus ψ⟫_ℂ =
            ⟪resolvent (I * ↑↑n) (I_mul_pnat_im_ne_zero n) hsym hplus hminus φ, ψ⟫_ℂ := by
    have hadj := resolvent_adjoint hsym hplus hminus (-I * ↑↑n) (neg_I_mul_pnat_im_ne_zero n)
    have h_conj : (starRingEnd ℂ) (-I * ↑↑n) = I * ↑↑n := by simp []
    rw [← ContinuousLinearMap.adjoint_inner_left]
    congr 1
    rw [hadj]
    congr 1
    rw [← hadj]
    simp_all only [map_div₀, map_pow, map_natCast, neg_mul, map_neg, map_mul, conj_I, neg_neg]
  rw [h1, h2]
  ring

lemma I_smul_yosidaApproxSym_skewAdjoint {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) :
    (I • yosidaApproxSym hsym hplus hminus n).adjoint = -(I • yosidaApproxSym hsym hplus hminus n) := by
  ext φ
  apply ext_inner_right ℂ
  intro ψ
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply]
  -- LHS: ⟨φ, i • Aₙˢʸᵐ ψ⟩ = i • ⟨φ, Aₙˢʸᵐ ψ⟩
  -- RHS: ⟨-(i • Aₙˢʸᵐ φ), ψ⟩ = -⟨i • Aₙˢʸᵐ φ, ψ⟩ = -ī • ⟨Aₙˢʸᵐ φ, ψ⟩ = i • ⟨Aₙˢʸᵐ φ, ψ⟩
  rw [inner_smul_right, inner_neg_left, inner_smul_left]
  -- conj(I) = -I, so -conj(I) = I
  simp only [conj_I]
  -- Now need: I • ⟨φ, Aₙˢʸᵐ ψ⟩ = I • ⟨Aₙˢʸᵐ φ, ψ⟩
  -- This follows from self-adjointness of Aₙˢʸᵐ
  -- ⟨φ, Aₙˢʸᵐ ψ⟩ = ⟨(Aₙˢʸᵐ)* φ, ψ⟩ = ⟨Aₙˢʸᵐ φ, ψ⟩
  rw [← ContinuousLinearMap.adjoint_inner_left]
  rw [yosidaApproxSym_selfAdjoint hsym hplus hminus n]
  rw [neg_mul]
  rw [eq_neg_iff_add_eq_zero, add_eq_zero_iff_neg_eq']
  rw [neg_eq_iff_eq_neg]

end Spectra.Stone.Yosida
