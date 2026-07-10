/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.YosidaHille.Approximation.Helpers
import Spectra.OneParameterUnitaryGroup.Basic
import Spectra.Resolvent.Range

/-!
# Yosida approximation operators

The Yosida approximation operators used to construct the exponential (one-parameter group) of a
self-adjoint operator. The construction evaluates the resolvent at the off-axis points `z = ± in`
and assembles the bounded approximants `Aₙ`, their symmetric variant, and the contractions `Jₙ`.

## Main definitions

* `resolventAtIn` / `resolventAtNegIn` — the resolvent `R(± in)` at `z = ± in`.
* `yosidaApprox` — the Yosida approximant `Aₙ = n²R(in) - in·I`.
* `yosidaApproxSym` — the symmetric Yosida approximant `(n²/2)(R(in) + R(-in))`.
* `yosidaJ` / `yosidaJNeg` — the contractive operators `Jₙ = -in·R(in)`, `Jₙ⁻ = in·R(-in)`.
* `yosidaApproxNeg` — the approximant `Aₙ⁻ = n²R(-in) + in·I` built from `R(-in)`.

## Main statements

* `resolventAtIn_bound` — `‖R(in)‖ ≤ 1/n`.
-/

open Complex Spectra.Resolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.YosidaHille.Approximation

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

/-- The resolvent at `z = in` is bounded by `1/n`: `‖R(in)‖ ≤ 1/n`. -/
lemma resolventAtIn_bound {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) :
    ‖resolventAtIn hsym hplus hminus n‖ ≤ 1 / (n : ℝ) := by
  unfold resolventAtIn
  calc ‖resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus‖
      ≤ 1 / |(I * (n : ℂ)).im| :=
        resolvent_bound (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus
    _ = 1 / (n : ℝ) := by rw [abs_I_mul_pnat_im]

end Spectra.YosidaHille.Approximation
