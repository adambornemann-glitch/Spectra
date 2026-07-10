/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.Unitary.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
/-!
# Integer powers of unitary operators

Integer powers `U^n` (`n : ℤ`) of a bounded operator `U` — `U^n` via the usual monoid power for
`n ≥ 0`, `(U*)^|n|` via the adjoint for `n < 0` — together with the algebraic law
`U^{m+n} = U^m · U^n` and the inner-product identity `⟨U^m ψ, U^n ψ⟩ = ⟨ψ, U^{n-m} ψ⟩` for
unitary `U`. These feed directly into `PositiveDefinite/Unitary.lean`'s unitary autocorrelation
sequence `c(n) = ⟨ψ, U^n ψ⟩`, the first step of that file's Herglotz-theorem construction.

## Main definitions

* `unitaryZpow`: `U^n` for `n : ℤ`.

## Main results

* `unitaryZpow_add`: `U^{m+n} = U^m · U^n` for unitary `U`.
* `unitaryZpow_inner_shift`: `⟨U^m ψ, U^n ψ⟩ = ⟨ψ, U^{n-m} ψ⟩` for unitary `U` — the identity
  `PositiveDefinite/Unitary.lean` uses to relate `unitaryCorrelation` at shifted indices.
-/
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Operator

/-! ### §1. Integer powers of unitary operators -/

section UnitaryPowers

variable (U : H →L[ℂ] H)

/-- Integer powers of a unitary operator: `U^n` for `n ≥ 0`,
`(U*)^|n|` for `n < 0`. The definition only uses the adjoint and
does not require unitarity; the algebraic laws do. -/
noncomputable def unitaryZpow : ℤ → (H →L[ℂ] H)
  | (n : ℕ)          => U ^ n
  | (Int.negSucc n)   => U.adjoint ^ (n + 1)


/-- `U^0 = 1`. -/
@[simp]
lemma unitaryZpow_zero : unitaryZpow U 0 = 1 := by
  simp [unitaryZpow]


/-- `U^1 = U`. (Currently unused.) -/
@[simp]
lemma unitaryZpow_one : unitaryZpow U 1 = U := by
  simp [unitaryZpow, pow_one]


/-- `U^{-1} = U*`. (Currently unused.) -/
@[simp]
lemma unitaryZpow_neg_one : unitaryZpow U (-1) = U.adjoint := by
  simp [unitaryZpow]
  abel

variable (hU : Operator.Unitary U)

/-- `U^{-n} = (U*)^n` for unitary `U`. (Currently unused.) -/
lemma unitaryZpow_neg (n : ℕ) (hn : 0 < n) :
    unitaryZpow U (-↑n) = U.adjoint ^ n := by
  cases n with
  | zero => omega
  | succ m => rfl

/-- The inverse of the unit corresponding to U is U.adjoint. -/
private lemma unit_inv_val :
    ((hU.isUnit.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) = U.adjoint := by
  set u := hU.isUnit.unit
  have hval : (u : H →L[ℂ] H) = U := hU.isUnit.unit_spec
  have hmul : (u : H →L[ℂ] H) * ↑(u⁻¹) = 1 := u.val_inv
  rw [hval] at hmul
  calc ((u⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)
      = U.adjoint * U * ↑(u⁻¹) := by rw [hU.1, one_mul]
    _ = U.adjoint * (U * ↑(u⁻¹)) := by rw [mul_assoc]
    _ = U.adjoint := by rw [hmul, mul_one]

/-- `unitaryZpow` agrees with `zpow` on the unit. -/
private lemma unitaryZpow_eq_unit_zpow (k : ℤ) :
    unitaryZpow U k = ↑(hU.isUnit.unit ^ k) := by
  cases k with
  | ofNat a =>
    simp [unitaryZpow, zpow_natCast, Units.val_pow_eq_pow_val]
  | negSucc a =>
    simp only [unitaryZpow, zpow_negSucc]
    congr 1
    exact Eq.symm (unit_inv_val U hU)

/-- `U^{m+n} = U^m · U^n` for unitary `U`. -/
lemma unitaryZpow_add (hU : Operator.Unitary U) (m n : ℤ) :
    unitaryZpow U (m + n) =
    (unitaryZpow U m).comp (unitaryZpow U n) := by
  rw [unitaryZpow_eq_unit_zpow U hU, unitaryZpow_eq_unit_zpow U hU,
      unitaryZpow_eq_unit_zpow U hU, zpow_add, Units.val_mul]
  rfl


/-- Natural powers of a unitary preserve inner products. -/
private lemma pow_unitary_inner (V : H →L[ℂ] H) (hV : Operator.Unitary V)
    (a : ℕ) (x y : H) :
    ⟪(V ^ a) x, (V ^ a) y⟫_ℂ = ⟪x, y⟫_ℂ := by
  induction a generalizing x y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ContinuousLinearMap.mul_apply]
    erw [ih (V x) (V y)]
    exact hV.inner_map_map x y

/-- Integer powers of a unitary preserve inner products. -/
private lemma unitaryZpow_inner_map_map (hU : Operator.Unitary U) (k : ℤ)
    (x y : H) :
    ⟪unitaryZpow U k x, unitaryZpow U k y⟫_ℂ = ⟪x, y⟫_ℂ := by
  cases k with
  | ofNat a => exact pow_unitary_inner U hU a x y
  | negSucc a =>
    have hU_adj : Operator.Unitary U.adjoint :=
      ⟨by rw [ContinuousLinearMap.adjoint_adjoint]; exact hU.2,
       by rw [ContinuousLinearMap.adjoint_adjoint]; exact hU.1⟩
    exact pow_unitary_inner U.adjoint hU_adj (a + 1) x y

/-- `⟨U^m ψ, U^n ψ⟩ = ⟨ψ, U^{n-m} ψ⟩`. -/
lemma unitaryZpow_inner_shift (hU : Operator.Unitary U) (m n : ℤ) (ψ : H) :
    ⟪unitaryZpow U m ψ, unitaryZpow U n ψ⟫_ℂ =
    ⟪ψ, unitaryZpow U (n - m) ψ⟫_ℂ := by
  have hfact : unitaryZpow U n = (unitaryZpow U m).comp (unitaryZpow U (n - m)) := by
    rw [← unitaryZpow_add U hU]; congr 1; omega
  rw [hfact, ContinuousLinearMap.comp_apply,
      unitaryZpow_inner_map_map U hU m ψ (unitaryZpow U (n - m) ψ)]


end UnitaryPowers

end Spectra.Operator
