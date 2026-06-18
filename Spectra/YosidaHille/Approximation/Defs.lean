/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Yosida/Defs.lean
-/
import Spectra.Stone.Yosida.Helpers
import Spectra.OneParameterUnitaryGroup.Basic
/-!
# Yosida Approximation Operators

This file defines the Yosida approximation operators used to construct the
exponential of a self-adjoint operator.

## Main definitions

* `resolventAtIn`: The resolvent `R(in)` at `z = in`
* `resolventAtNegIn`: The resolvent `R(-in)` at `z = -in`
* `yosidaApprox`: The Yosida approximant `Aₙ = n²R(in) - in·I`
* `yosidaApproxSym`: The symmetric Yosida approximant `(n²/2)(R(in) + R(-in))`
* `yosidaJ`: The contractive operator `Jₙ = -in·R(in)`
* `yosidaJNeg`: The contractive operator `Jₙ⁻ = in·R(-in)`
* `yosidaApproxNeg`: The approximant using `R(-in)`

## Main results

* `resolventAtIn_bound`: `‖R(in)‖ ≤ 1/n`

-/
open Complex Spectra.Resolvent
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Stone.Yosida

/-! ### Resolvent at specific points -/

/-- The resolvent at `z = in` for positive natural `n`. -/
noncomputable def resolventAtIn {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) : H →L[ℂ] H :=
  resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus

/-- The resolvent at `z = -in` for positive natural `n`. -/
noncomputable def resolventAtNegIn {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) : H →L[ℂ] H :=
  resolvent (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus

/-! ### Yosida approximation operators -/

/-- The Yosida approximant `Aₙ = n²R(in) - in·I`. -/
noncomputable def yosidaApprox {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) : H →L[ℂ] H :=
  (n : ℂ)^2 • resolventAtIn hsym hplus hminus n - (I * (n : ℂ)) • ContinuousLinearMap.id ℂ H

/-- The symmetric Yosida approximant `(n²/2)(R(in) + R(-in))`. -/
noncomputable def yosidaApproxSym {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) : H →L[ℂ] H :=
  ((n : ℂ)^2 / 2) • (resolventAtIn hsym hplus hminus n + resolventAtNegIn hsym hplus hminus n)

/-- The contractive operator `Jₙ = -in·R(in)`. -/
noncomputable def yosidaJ {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) : H →L[ℂ] H :=
  (-I * (n : ℂ)) • resolventAtIn hsym hplus hminus n

/-- The contractive operator `Jₙ⁻ = in·R(-in)`. -/
noncomputable def yosidaJNeg {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) : H →L[ℂ] H :=
  (I * (n : ℂ)) • resolventAtNegIn hsym hplus hminus n

/-- The approximant using `R(-in)`: `Aₙ⁻ = n²R(-in) + in·I`. -/
noncomputable def yosidaApproxNeg {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) : H →L[ℂ] H :=
  ((n : ℂ)^2) • resolventAtNegIn hsym hplus hminus n + (I * (n : ℂ)) • ContinuousLinearMap.id ℂ H

/-! ### Resolvent bounds -/

lemma resolventAtIn_bound {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) :
    ‖resolventAtIn hsym hplus hminus n‖ ≤ 1 / (n : ℝ) := by
  unfold resolventAtIn
  calc ‖resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus‖
      ≤ 1 / |(I * (n : ℂ)).im| :=
        resolvent_bound hsym hplus hminus (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n)
    _ = 1 / (n : ℝ) := by rw [abs_I_mul_pnat_im]

end Spectra.Stone.Yosida
