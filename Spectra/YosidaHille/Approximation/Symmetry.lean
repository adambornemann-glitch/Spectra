/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.YosidaHille.Approximation.Bounds
import Spectra.Resolvent.Identities

/-!
# Symmetry properties of the Yosida operators

The symmetric Yosida approximant `Aₙˢʸᵐ` is self-adjoint, and `I • Aₙˢʸᵐ` is skew-adjoint. These are
what make `exp(i·Aₙˢʸᵐ·t)` unitary — the key step in assembling the one-parameter group.

## Main statements

* `yosidaApproxSym_selfAdjoint` — `(Aₙˢʸᵐ)* = Aₙˢʸᵐ`.
* `I_smul_yosidaApproxSym_skewAdjoint` — `(i·Aₙˢʸᵐ)* = -(i·Aₙˢʸᵐ)`.

## Implementation notes

`Aₙˢʸᵐ` is the `n²/2`-weighted average of the two resolvents `R(in)`, `R(-in)`, each other's
adjoint by `resolvent_adjoint` — averaging conjugate-paired operators symmetrizes, giving
`yosidaApproxSym_selfAdjoint`. Multiplying a self-adjoint operator by `I` always yields a
skew-adjoint one (`⟨φ, I•Tψ⟩ = I⟨φ,Tψ⟩ = I⟨Tφ,ψ⟩ = -⟨I•Tφ,ψ⟩` using `T* = T`), giving
`I_smul_yosidaApproxSym_skewAdjoint`. Self-adjoint and skew-adjoint together are exactly what
make `NormedSpace.exp (I • t • Aₙˢʸᵐ)` unitary (`expBounded_skewAdjoint_unitary` in
`ExpBounded/Unitary.lean`), the key step in assembling the one-parameter group.
-/
open Complex InnerProductSpace Spectra.Resolvent
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.YosidaHille.Approximation

/-- `⟪φ, R(z)ψ⟫ = ⟪R(z̄)φ, ψ⟫`: swapping a resolvent from one side of an inner product to the
other conjugates its spectral parameter. Repackages `resolvent_adjoint` via
`ContinuousLinearMap.adjoint_inner_left`. -/
private lemma resolvent_inner_swap {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (z : ℂ) (hz : z.im ≠ 0) (φ ψ : H) :
    ⟪φ, resolvent z hz hsym hplus hminus ψ⟫_ℂ =
    ⟪resolvent (starRingEnd ℂ z)
        (by simp only [Complex.conj_im, neg_ne_zero]; exact hz)
        hsym hplus hminus φ, ψ⟫_ℂ := by
  rw [← resolvent_adjoint hsym hplus hminus z hz, ContinuousLinearMap.adjoint_inner_left]

/-- The symmetric Yosida approximant is self-adjoint: `(Aₙˢʸᵐ)* = Aₙˢʸᵐ`. -/
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
    simp [map_div₀, map_pow, map_ofNat]
  -- Pull scalars through inner products
  rw [inner_smul_right, inner_smul_left, h_scalar_real]
  congr 1
  -- Now show ⟨φ, (R(in) + R(-in)) ψ⟩ = ⟨(R(in) + R(-in)) φ, ψ⟩
  rw [inner_add_right, inner_add_left]
  -- Use resolvent_adjoint: ⟨φ, R(z)ψ⟩ = ⟨R(z̄)φ, ψ⟩
  have h1 : ⟪φ, resolvent (I * ↑↑n) (I_mul_pnat_im_ne_zero n) hsym hplus hminus ψ⟫_ℂ =
            ⟪resolvent (-I * ↑↑n) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus φ, ψ⟫_ℂ := by
    simpa using resolvent_inner_swap hsym hplus hminus (I * ↑↑n) (I_mul_pnat_im_ne_zero n) φ ψ
  have h2 : ⟪φ, resolvent (-I * ↑↑n) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus ψ⟫_ℂ =
            ⟪resolvent (I * ↑↑n) (I_mul_pnat_im_ne_zero n) hsym hplus hminus φ, ψ⟫_ℂ := by
    simpa using resolvent_inner_swap hsym hplus hminus (-I * ↑↑n) (neg_I_mul_pnat_im_ne_zero n) φ ψ
  rw [h1, h2]
  ring

/-- `I • Aₙˢʸᵐ` is skew-adjoint: `(i·Aₙˢʸᵐ)* = -(i·Aₙˢʸᵐ)`. -/
lemma I_smul_yosidaApproxSym_skewAdjoint {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) :
    (I • yosidaApproxSym hsym hplus hminus n).adjoint =
      -(I • yosidaApproxSym hsym hplus hminus n) := by
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
  rw [← ContinuousLinearMap.adjoint_inner_left, yosidaApproxSym_selfAdjoint hsym hplus hminus n]
  ring

end Spectra.YosidaHille.Approximation
