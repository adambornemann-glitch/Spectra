/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ported from Isabelle/HOL formalization by Echenim & Mhalla, by Adam Bornemann
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Star.CHSH
import Spectra.QuantumMechanics.BellsTheorem.Basic
/-!
# The CHSH Operator Squared: S² = 4I - [A₀,A₁]·[B₀,B₁]

The algebraic engine of the whole Tsirelson chain (`Commuting.lean`,
`Tsirelson/{UnitaryBounds,CommutatorAlgebra,Basic}.lean`): a dozen small involution/commutator
identities culminating in `CHSH_op_square`, the key identity `S² = 4I - [A₀,A₁]·[B₀,B₁]` from
which both the commuting-observables bound and Tsirelson's bound are derived. Every supporting
identity is pure ring algebra and is stated for an abstract `[Ring R]`; only `CHSH_op_factor` and
`CHSH_op_square` themselves are specialized to `Matrix (Fin n) (Fin n) ℂ`, since they are stated in
terms of `chshOp`/`IsCHSHTuple`.

## Main results

* `CHSH_op_square` : `S² = 4I - [A₀,A₁]·[B₀,B₁]` for any `IsCHSHTuple` — the headline identity,
  built from the involution/commutator family below it (all stated for a general `[Ring R]`):
* `add_sq_involution`, `sub_sq_involution` : `(A±B)² = 2I ± AB ± BA` for involutions `A, B`
* `sub_mul_add_involution`, `add_mul_sub_involution` : `(A∓B)(A±B) = ±[A,B]` for involutions
* `CHSH_op_factor` : `S = (B₁-B₀)A₀ + (B₀+B₁)A₁` when the `Aᵢ` and `Bⱼ` pairwise commute
* `sub_sq_add_add_sq_involution` : `(A-B)² + (A+B)² = 4I` for involutions
* `comm_A_sub_B`, `comm_A_add_B` : `A` commutes with `B₁∓B₀` when it commutes with both `B₀, B₁`
* `sub_mul_add_comm` : `(B₁-B₀)(B₀+B₁) = -[B₀,B₁]` for involutions `B₀, B₁`
* `add_mul_sub_comm` : `(B₀+B₁)(B₁-B₀) = [B₀,B₁]` for involutions `B₀, B₁`
* `sq_sum_factor` : `(XA₀+YA₁)² = X²+Y² + XY·A₀A₁ + YX·A₁A₀` under the matching commutations
* `comm_comm_comm` : `[A₀,A₁]` and `[B₀,B₁]` commute when all `Aᵢ` commute with all `Bⱼ`

## Implementation notes

Every lemma except `CHSH_op_factor`/`CHSH_op_square` is stated for an abstract `[Ring R]` rather
than `Matrix (Fin n) (Fin n) ℂ`, matching the generality of the mathlib API this file builds on
(`Mathlib.Algebra.Star.CHSH`'s `IsCHSHTuple` is already generic over any `[Monoid R] [StarMul R]`).
`CHSH_op_factor` and `CHSH_op_square` stay matrix-specific because they are stated in terms of
`chshOp`, which is itself hardcoded to `Matrix ι ι ℂ` in `Basic.lean`; generalizing `chshOp` would
ripple into the shared foundation of the whole `BellsTheorem` tree, unlike the purely local lemmas
here. The matrix commutator used throughout is mathlib's `⁅A, B⁆` (`Ring.bracket`, an instance for
any `NonUnitalNonAssocRing` via `Ring.instBracket`, which in turn gives a `LieRing` structure on
any `Ring` via `LieRing.ofAssociativeRing`), not a bespoke definition. Since `⁅A, B⁆` is a
typeclass projection rather than a plain `def`, `unfold` does not see through it: every proof below
instead uses `Ring.lie_def : ⁅x, y⁆ = x * y - y * x` (itself `rfl`) via `rw`/`simp only`.

## References

* [Echenim, Mhalla, *A formalization of the CHSH inequality and Tsirelson's
  upper-bound in Isabelle/HOL*][echenim2023]

## Tags

chsh, commutator, tsirelson bound, quantum information
-/
namespace Spectra.QuantumInfo

/-- For involutions A² = B² = I: (A + B)² = 2I + AB + BA -/
lemma add_sq_involution {R : Type*} [Ring R] (A B : R)
    (hA : A * A = 1) (hB : B * B = 1) :
    (A + B) * (A + B) = 2 • (1 : R) + A * B + B * A := by
  rw [add_mul, mul_add, mul_add]
  rw [hA, hB]
  module

/-- For involutions A² = B² = I: (A - B)² = 2I - AB - BA -/
lemma sub_sq_involution {R : Type*} [Ring R] (A B : R)
    (hA : A * A = 1) (hB : B * B = 1) :
    (A - B) * (A - B) = 2 • (1 : R) - A * B - B * A := by
  rw [sub_mul, mul_sub, mul_sub]
  rw [hA, hB]
  module

/-- For involutions: (A - B)(A + B) = [A, B] -/
lemma sub_mul_add_involution {R : Type*} [Ring R] (A B : R)
    (hA : A * A = 1) (hB : B * B = 1) :
    (A - B) * (A + B) = ⁅A, B⁆ := by
  rw [Ring.lie_def]
  rw [sub_mul, mul_add, mul_add]
  rw [hA, hB]
  module

/-- For involutions: (A + B)(A - B) = -[A, B] -/
lemma add_mul_sub_involution {R : Type*} [Ring R] (A B : R)
    (hA : A * A = 1) (hB : B * B = 1) :
    (A + B) * (A - B) = -⁅A, B⁆ := by
  rw [Ring.lie_def]
  rw [add_mul, mul_sub, mul_sub]
  rw [hA, hB]
  module

/-- CHSH operator can be factored as (B₁ - B₀)A₀ + (B₀ + B₁)A₁ when Aᵢ commutes with Bⱼ -/
lemma CHSH_op_factor {n : ℕ}
    (A₀ A₁ B₀ B₁ : Matrix (Fin n) (Fin n) ℂ)
    (hc00 : A₀ * B₀ = B₀ * A₀) (hc01 : A₀ * B₁ = B₁ * A₀)
    (hc10 : A₁ * B₀ = B₀ * A₁) (hc11 : A₁ * B₁ = B₁ * A₁) :
    chshOp A₀ A₁ B₀ B₁ = (B₁ - B₀) * A₀ + (B₀ + B₁) * A₁ := by
  unfold chshOp
  rw [hc00, hc01, hc10, hc11]
  rw [Matrix.sub_mul, Matrix.add_mul]
  module

/-- For involutions: (A - B)² + (A + B)² = 4I -/
lemma sub_sq_add_add_sq_involution {R : Type*} [Ring R] (A B : R)
    (hA : A * A = 1) (hB : B * B = 1) :
    (A - B) * (A - B) + (A + B) * (A + B) = 4 • (1 : R) := by
  rw [sub_sq_involution A B hA hB, add_sq_involution A B hA hB]
  module

/-- A₀ commutes with B₁ - B₀. Unlike `sub_mul_add_comm`/`add_mul_sub_comm` below, this is
deliberately *not* derived from the involution lemmas above: it needs no involution hypothesis
(`B₀ * B₀ = 1`) at all, only the two cross-commutations, so it stays a direct one-line `rw`. -/
lemma comm_A_sub_B {R : Type*} [Ring R] (A B₀ B₁ : R)
    (hc0 : A * B₀ = B₀ * A) (hc1 : A * B₁ = B₁ * A) :
    A * (B₁ - B₀) = (B₁ - B₀) * A := by
  rw [mul_sub, sub_mul, hc0, hc1]

/-- A₀ commutes with B₀ + B₁. Unlike `sub_mul_add_comm`/`add_mul_sub_comm` below, this is
deliberately *not* derived from the involution lemmas above: it needs no involution hypothesis
(`B₀ * B₀ = 1`) at all, only the two cross-commutations, so it stays a direct one-line `rw`. -/
lemma comm_A_add_B {R : Type*} [Ring R] (A B₀ B₁ : R)
    (hc0 : A * B₀ = B₀ * A) (hc1 : A * B₁ = B₁ * A) :
    A * (B₀ + B₁) = (B₀ + B₁) * A := by
  rw [mul_add, add_mul, hc0, hc1]

/-- (B₁ - B₀)(B₀ + B₁) = -[B₀, B₁] for involutions, via `sub_mul_add_involution` at `(B₁, B₀)`
plus `lie_skew` antisymmetry. -/
lemma sub_mul_add_comm {R : Type*} [Ring R] (B₀ B₁ : R)
    (hB₀ : B₀ * B₀ = 1) (hB₁ : B₁ * B₁ = 1) :
    (B₁ - B₀) * (B₀ + B₁) = -⁅B₀, B₁⁆ := by
  rw [add_comm B₀ B₁, sub_mul_add_involution B₁ B₀ hB₁ hB₀, (lie_skew B₁ B₀).symm]

/-- (B₀ + B₁)(B₁ - B₀) = [B₀, B₁] for involutions, via `add_mul_sub_involution` at `(B₁, B₀)`
plus `lie_skew` antisymmetry. -/
lemma add_mul_sub_comm {R : Type*} [Ring R] (B₀ B₁ : R)
    (hB₀ : B₀ * B₀ = 1) (hB₁ : B₁ * B₁ = 1) :
    (B₀ + B₁) * (B₁ - B₀) = ⁅B₀, B₁⁆ := by
  rw [add_comm B₀ B₁, add_mul_sub_involution B₁ B₀ hB₁ hB₀, (lie_skew B₁ B₀).symm, neg_neg]

/-- Square of sum XA₀ + YA₁ when Aᵢ commutes with X, Y and Aᵢ² = I -/
lemma sq_sum_factor {R : Type*} [Ring R] (A₀ A₁ X Y : R)
    (hA₀sq : A₀ * A₀ = 1) (hA₁sq : A₁ * A₁ = 1)
    (hcX0 : A₀ * X = X * A₀) (hcX1 : A₁ * X = X * A₁)
    (hcY0 : A₀ * Y = Y * A₀) (hcY1 : A₁ * Y = Y * A₁) :
    (X * A₀ + Y * A₁) * (X * A₀ + Y * A₁) =
    X * X + Y * Y + X * Y * A₀ * A₁ + Y * X * A₁ * A₀ := by
  rw [add_mul, mul_add, mul_add]
  have h1 : X * A₀ * (X * A₀) = X * X := by
    calc X * A₀ * (X * A₀)
        = X * (A₀ * X) * A₀ := by
          simp only [mul_assoc]
      _ = X * (X * A₀) * A₀ := by rw [hcX0]
      _ = X * X * A₀ * A₀ := by rw [mul_assoc X X A₀]
      _ = X * X * (A₀ * A₀) := by rw [mul_assoc (X * X)]
      _ = X * X * 1 := by rw [hA₀sq]
      _ = X * X := mul_one _
  have h2 : Y * A₁ * (Y * A₁) = Y * Y := by
    calc Y * A₁ * (Y * A₁)
        = Y * (A₁ * Y) * A₁ := by
          simp only [mul_assoc]
      _ = Y * (Y * A₁) * A₁ := by rw [hcY1]
      _ = Y * Y * A₁ * A₁ := by rw [mul_assoc Y Y A₁]
      _ = Y * Y * (A₁ * A₁) := by rw [mul_assoc (Y * Y)]
      _ = Y * Y * 1 := by rw [hA₁sq]
      _ = Y * Y := mul_one _
  have h3 : X * A₀ * (Y * A₁) = X * Y * A₀ * A₁ := by
    calc X * A₀ * (Y * A₁)
        = X * (A₀ * Y) * A₁ := by
          simp only [mul_assoc]
      _ = X * (Y * A₀) * A₁ := by rw [hcY0]
      _ = X * Y * A₀ * A₁ := by rw [mul_assoc X Y A₀]
  have h4 : Y * A₁ * (X * A₀) = Y * X * A₁ * A₀ := by
    calc Y * A₁ * (X * A₀)
        = Y * (A₁ * X) * A₀ := by
          simp only [mul_assoc]
      _ = Y * (X * A₁) * A₀ := by rw [hcX1]
      _ = Y * X * A₁ * A₀ := by rw [mul_assoc Y X A₁]
  rw [h1, h2, h3, h4]
  module

/-- If `P`, `Q` each commute with both `X` and `Y`, then `P*Q` slides past `X*Y`. The shared
"slide a commuting factor past two others" step behind all four cases of `comm_comm_comm`. -/
private lemma slide {R : Type*} [Ring R] (P Q X Y : R)
    (hPX : P * X = X * P) (hPY : P * Y = Y * P)
    (hQX : Q * X = X * Q) (hQY : Q * Y = Y * Q) :
    P * Q * (X * Y) = X * Y * (P * Q) := by
  calc P * Q * (X * Y)
      = P * (Q * X) * Y := by simp only [mul_assoc]
    _ = P * (X * Q) * Y := by rw [hQX]
    _ = (P * X) * Q * Y := by rw [← mul_assoc P X]
    _ = (X * P) * Q * Y := by rw [hPX]
    _ = X * (P * Q) * Y := by rw [mul_assoc X]
    _ = X * (P * (Q * Y)) := by simp only [mul_assoc]
    _ = X * (P * (Y * Q)) := by rw [hQY]
    _ = X * ((P * Y) * Q) := by rw [← mul_assoc P]
    _ = X * ((Y * P) * Q) := by rw [hPY]
    _ = X * (Y * (P * Q)) := by rw [mul_assoc Y]
    _ = X * Y * (P * Q) := by rw [← mul_assoc X]

/-- Commutators [A₀,A₁] and [B₀,B₁] commute when all Aᵢ commute with all Bⱼ -/
lemma comm_comm_comm {R : Type*} [Ring R] (A₀ A₁ B₀ B₁ : R)
    (hc00 : A₀ * B₀ = B₀ * A₀) (hc01 : A₀ * B₁ = B₁ * A₀)
    (hc10 : A₁ * B₀ = B₀ * A₁) (hc11 : A₁ * B₁ = B₁ * A₁) :
    ⁅A₀, A₁⁆ * ⁅B₀, B₁⁆ = ⁅B₀, B₁⁆ * ⁅A₀, A₁⁆ := by
  simp only [Ring.lie_def, sub_mul, mul_sub]
  -- Each factored product slides past the other via `slide`, at the four sign combinations.
  have h1 := slide A₀ A₁ B₀ B₁ hc00 hc01 hc10 hc11
  have h2 := slide A₀ A₁ B₁ B₀ hc01 hc00 hc11 hc10
  have h3 := slide A₁ A₀ B₀ B₁ hc10 hc11 hc00 hc01
  have h4 := slide A₁ A₀ B₁ B₀ hc11 hc10 hc01 hc00
  rw [h1, h2, h3, h4]
  module

/-- The CHSH operator squared: S² = 4I - [A₀,A₁]·[B₀,B₁]

This is the key identity for deriving Tsirelson's bound. -/
lemma CHSH_op_square {n : ℕ}
    (A₀ A₁ B₀ B₁ : Matrix (Fin n) (Fin n) ℂ)
    (hT : IsCHSHTuple A₀ A₁ B₀ B₁) :
    chshOp A₀ A₁ B₀ B₁ * chshOp A₀ A₁ B₀ B₁ =
    4 • (1 : Matrix (Fin n) (Fin n) ℂ) - ⁅A₀, A₁⁆ * ⁅B₀, B₁⁆ := by
  -- Extract hypotheses
  have hA₀sq : A₀ * A₀ = 1 := by rw [← pow_two]; exact hT.A₀_inv
  have hA₁sq : A₁ * A₁ = 1 := by rw [← pow_two]; exact hT.A₁_inv
  have hB₀sq : B₀ * B₀ = 1 := by rw [← pow_two]; exact hT.B₀_inv
  have hB₁sq : B₁ * B₁ = 1 := by rw [← pow_two]; exact hT.B₁_inv
  have hc00 := hT.A₀B₀_commutes
  have hc01 := hT.A₀B₁_commutes
  have hc10 := hT.A₁B₀_commutes
  have hc11 := hT.A₁B₁_commutes
  -- Define X = B₁ - B₀, Y = B₀ + B₁
  let X := B₁ - B₀
  let Y := B₀ + B₁
  -- Commutativity lemmas for X, Y
  have hcX0 : A₀ * X = X * A₀ := comm_A_sub_B A₀ B₀ B₁ hc00 hc01
  have hcX1 : A₁ * X = X * A₁ := comm_A_sub_B A₁ B₀ B₁ hc10 hc11
  have hcY0 : A₀ * Y = Y * A₀ := comm_A_add_B A₀ B₀ B₁ hc00 hc01
  have hcY1 : A₁ * Y = Y * A₁ := comm_A_add_B A₁ B₀ B₁ hc10 hc11
  -- Factor CHSH operator
  have h_factor : chshOp A₀ A₁ B₀ B₁ = X * A₀ + Y * A₁ :=
    CHSH_op_factor A₀ A₁ B₀ B₁ hc00 hc01 hc10 hc11
  -- Square of factored form
  have h_sq := sq_sum_factor A₀ A₁ X Y hA₀sq hA₁sq hcX0 hcX1 hcY0 hcY1
  -- X*X + Y*Y = 4I
  have h_sum_sq : X * X + Y * Y = 4 • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have := sub_sq_add_add_sq_involution B₁ B₀ hB₁sq hB₀sq
    simp only [X, Y, add_comm B₀ B₁]
    exact this
  -- X*Y = -[B₀, B₁]
  have h_XY : X * Y = -⁅B₀, B₁⁆ := sub_mul_add_comm B₀ B₁ hB₀sq hB₁sq
  -- Y*X = [B₀, B₁]
  have h_YX : Y * X = ⁅B₀, B₁⁆ := add_mul_sub_comm B₀ B₁ hB₀sq hB₁sq
  -- Commutators commute
  have h_comm := comm_comm_comm A₀ A₁ B₀ B₁ hc00 hc01 hc10 hc11
  -- Put it together
  rw [h_factor, h_sq, h_sum_sq, h_XY, h_YX]
  -- S² = 4I + (-[B₀,B₁])*A₀*A₁ + [B₀,B₁]*A₁*A₀
  --    = 4I - [B₀,B₁]*(A₀*A₁ - A₁*A₀)
  --    = 4I - [B₀,B₁]*[A₀,A₁]
  --    = 4I - [A₀,A₁]*[B₀,B₁]  (by commutativity)
  simp only [Ring.lie_def] at h_comm ⊢
  rw [h_comm]
  rw [Matrix.mul_sub, Matrix.neg_mul, Matrix.neg_mul]
  simp only [Matrix.mul_assoc]
  module

end Spectra.QuantumInfo
