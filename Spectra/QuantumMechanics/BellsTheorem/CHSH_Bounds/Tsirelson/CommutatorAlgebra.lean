/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ported from Isabelle/HOL formalization by Echenim & Mhalla, by Adam Bornemann
-/
import Mathlib.Algebra.Lie.OfAssociative
import Spectra.QuantumMechanics.BellsTheorem.CHSH_Bounds.Tsirelson.UnitaryBounds

/-!
# Commutator Algebra for Hermitian Involutions

This file develops the algebra of commutators `[A,B] = AB - BA` for Hermitian involutions
(operators satisfying `A² = I` and `A† = A`). The bounds on commutator products
(`comm_prod_ge_neg_four`, `comm_prod_le_four`) are the algebraic heart of Tsirelson's bound,
proved in `Tsirelson/Basic.lean` via `CHSH_op_sq_le_eight`.

## Main results

* `comm_skewHermitian`, `comm_hermitian_skewHermitian` : `[A,B]† = -[A,B]` for Hermitian `A, B`
* `neg_sq_posSemidef_of_skewHermitian` : `-X² ⪰ 0` for skew-Hermitian `X`
* `comm_sq_eq` : `[A,B]² = (AB + BA)² - 4I` for dichotomic `A, B`
* `comm_sq_add_four_posSemidef`, `comm_sq_ge_neg_four` : `[A,B]² ≥ -4I`
* `comm_sq_le_four` : `[A,B]² ≤ 4I`
* `comm_eq_unitary_sub_conjTranspose` : `[A₀,A₁] = U - U†` where `U = A₀A₁`
* `mul_I_skewHermitian_isHermitian`, `neg_smul_I_skewHermitian_isHermitian`,
  `prod_skewHermitian_comm_isHermitian` : Hermitian-ness facts about skew-Hermitian matrices
* `anticomm_involution_ge_neg_two`, `anticomm_involution_le_two` : `-2I ≤ A₀A₁ + A₁A₀ ≤ 2I`
* `comm_prod_ge_neg_four`, `comm_prod_le_four` : `-4I ≤ [A₀,A₁][B₀,B₁] ≤ 4I` under pairwise
  commutativity of `{A₀,A₁}` with `{B₀,B₁}`

## Implementation notes

For Hermitian involutions `A₀, A₁` (`A₀² = A₁² = I`, `A₀† = A₀`, `A₁† = A₁`), the product
`U := A₀A₁` is unitary (`involution_mul_involution_unitary`, `UnitaryBounds.lean`), and every
bound in this file is ultimately a statement about `U + U†` or a product of two such unitaries
— `comm_eq_unitary_sub_conjTranspose` rewrites the commutator itself as `U - U†`, and
`comm_prod_eq_unitary_decomp` (private) further decomposes `[A₀,A₁][B₀,B₁]` in terms of the two
unitaries `W = U_A U_B` and `V = U_A U_B†`, reducing both `comm_prod_ge_neg_four` and
`comm_prod_le_four` to `unitary_add_conjTranspose_{ge_neg_two,le_two}` applied to `W` and `V`.

Not every declaration above is consumed elsewhere in the library: only `comm_prod_ge_neg_four`
feeds into `Tsirelson/Basic.lean`'s `CHSH_op_sq_le_eight`. The rest (`comm_sq_le_four`,
`anticomm_involution_{ge_neg_two,le_two}`, the skew-Hermitian helper lemmas, and
`comm_prod_le_four` itself) develop the full symmetric algebra for completeness rather than
because a downstream proof currently needs them.
-/

open Matrix Complex

namespace Spectra.QuantumInfo

/-! ## Basic Commutator Properties -/

/-- The commutator `[A,B]` is skew-Hermitian when `A, B` are Hermitian. -/
lemma comm_skewHermitian {n : ℕ} [NeZero n]
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ⁅A, B⁆ᴴ = -⁅A, B⁆ := by
  simp only [Ring.lie_def]
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  rw [hA.eq, hB.eq]
  module

/-- For skew-Hermitian `X` (`X† = -X`), `-X²` is positive semidefinite. -/
lemma neg_sq_posSemidef_of_skewHermitian {n : ℕ} [NeZero n]
    (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : Xᴴ = -X) :
    IsPosSemidefComplex (-X * X) := by
  intro x
  simp only [Matrix.neg_mul, Matrix.neg_mulVec, dotProduct_neg, neg_re]
  have h1 : (X * X).mulVec x = X.mulVec (X.mulVec x) := by
    rw [← Matrix.mulVec_mulVec]
  rw [h1, Matrix.dotProduct_mulVec]
  have h2 : star x ᵥ* X = -star (X.mulVec x) := by
    have := Matrix.vecMul_conjTranspose X (star x)
    rw [hX, Matrix.vecMul_neg, star_star] at this
    symm
    exact neg_eq_iff_eq_neg.mpr this.symm
  rw [h2, neg_dotProduct, neg_re]
  simp only [ge_iff_le, neg_neg]
  exact star_dotProduct_self_re_nonneg (X.mulVec x)

/-! ## Commutator Squared Identity -/

/-- `[A,B]² = (AB + BA)² - 4I` for dichotomic `A, B`. -/
lemma comm_sq_eq {n : ℕ} [NeZero n]
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA_sq : A * A = 1) (hB_sq : B * B = 1) :
    ⁅A, B⁆ * ⁅A, B⁆ = (A * B + B * A) * (A * B + B * A) - 4 • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have h2 : A * (B * (B * A)) = A * A := by rw [← Matrix.mul_assoc B B, hB_sq, Matrix.one_mul]
  have h3 : B * (A * (A * B)) = B * B := by rw [← Matrix.mul_assoc A A, hA_sq, Matrix.one_mul]
  simp only [Ring.lie_def]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.mul_assoc]
  rw [h2, h3, hA_sq, hB_sq]
  module

/-- For dichotomic `A, B`: `4I + [A,B]²` is positive semidefinite. -/
lemma comm_sq_add_four_posSemidef {n : ℕ} [NeZero n]
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA_herm : A.IsHermitian) (hB_herm : B.IsHermitian)
    (hA_sq : A * A = 1) (hB_sq : B * B = 1) :
    IsPosSemidefComplex (4 • (1 : Matrix (Fin n) (Fin n) ℂ) + ⁅A, B⁆ * ⁅A, B⁆) := by
  rw [comm_sq_eq A B hA_sq hB_sq]
  simp only [add_sub_cancel]
  have h_herm : (A * B + B * A).IsHermitian := by
    rw [Matrix.IsHermitian]
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    rw [hA_herm.eq, hB_herm.eq]
    module
  intro x
  rw [← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec]
  have h_vecmul : star x ᵥ* (A * B + B * A) = star ((A * B + B * A).mulVec x) := by
    have := Matrix.vecMul_conjTranspose (A * B + B * A) (star x)
    rw [h_herm.eq, star_star] at this
    exact this
  rw [h_vecmul]
  exact star_dotProduct_self_re_nonneg ((A * B + B * A).mulVec x)

/-! ## Commutator Representations -/

/-- For Hermitian involutions, the commutator equals `U - U†` where `U = A₀A₁`. -/
lemma comm_eq_unitary_sub_conjTranspose {n : ℕ} [NeZero n]
    (A₀ A₁ : Matrix (Fin n) (Fin n) ℂ)
    (hA₀_herm : A₀.IsHermitian) (hA₁_herm : A₁.IsHermitian) :
    ⁅A₀, A₁⁆ = A₀ * A₁ - (A₀ * A₁)ᴴ := by
  simp only [Ring.lie_def]
  rw [Matrix.conjTranspose_mul, hA₀_herm.eq, hA₁_herm.eq]

/-- Commutator of Hermitian matrices is skew-Hermitian -/
lemma comm_hermitian_skewHermitian {n : ℕ} [NeZero n]
    (A₀ A₁ : Matrix (Fin n) (Fin n) ℂ)
    (hA₀_herm : A₀.IsHermitian) (hA₁_herm : A₁.IsHermitian) :
    ⁅A₀, A₁⁆ᴴ = -⁅A₀, A₁⁆ := by
  simp only [Ring.lie_def]
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  rw [hA₀_herm.eq, hA₁_herm.eq]
  module

/-! ## Skew-Hermitian Lemmas -/

/-- i times a skew-Hermitian matrix is Hermitian -/
lemma mul_I_skewHermitian_isHermitian {n : ℕ} [NeZero n]
    (K : Matrix (Fin n) (Fin n) ℂ)
    (hK : Kᴴ = -K) :
    (Complex.I • K).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hK]
  simp only [RCLike.star_def, conj_I, smul_neg]
  ext i j : 1
  simp only [neg_apply, smul_apply, smul_eq_mul, neg_mul, neg_neg]

/-- The negative of a skew-Hermitian matrix times i is Hermitian -/
lemma neg_smul_I_skewHermitian_isHermitian {n : ℕ} [NeZero n]
    (K : Matrix (Fin n) (Fin n) ℂ)
    (hK : Kᴴ = -K) :
    ((-Complex.I) • K).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hK]
  simp only [star_neg, RCLike.star_def, conj_I, neg_neg, smul_neg]
  ext i j : 1
  simp only [neg_apply, smul_apply, smul_eq_mul, neg_mul]

/-- Product of commuting skew-Hermitian matrices is Hermitian -/
lemma prod_skewHermitian_comm_isHermitian {n : ℕ} [NeZero n]
    (K L : Matrix (Fin n) (Fin n) ℂ)
    (hK : Kᴴ = -K) (hL : Lᴴ = -L)
    (hcomm : K * L = L * K) :
    (K * L).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, hK, hL]
  simp only [neg_mul, mul_neg, neg_neg]
  exact hcomm.symm

/-! ## Anticommutator Bounds -/

/-- For Hermitian involutions, `-2I ≤ A₀A₁ + A₁A₀ ≤ 2I` (lower bound). -/
lemma anticomm_involution_ge_neg_two {n : ℕ} [NeZero n]
    (A₀ A₁ : Matrix (Fin n) (Fin n) ℂ)
    (hA₀_herm : A₀.IsHermitian) (hA₁_herm : A₁.IsHermitian)
    (hA₀_sq : A₀ * A₀ = 1) (hA₁_sq : A₁ * A₁ = 1) :
    IsPosSemidefComplex (2 • (1 : Matrix (Fin n) (Fin n) ℂ) + (A₀ * A₁ + A₁ * A₀)) := by
  let U := A₀ * A₁
  have hU : U * Uᴴ = 1 := involution_mul_involution_unitary A₀ A₁ hA₀_herm hA₁_herm hA₀_sq hA₁_sq
  have h_anticomm : A₀ * A₁ + A₁ * A₀ = U + Uᴴ := by
    simp only [U, Matrix.conjTranspose_mul, hA₀_herm.eq, hA₁_herm.eq]
  rw [h_anticomm]
  exact unitary_add_conjTranspose_ge_neg_two U hU

/-- For Hermitian involutions, `-2I ≤ A₀A₁ + A₁A₀ ≤ 2I` (upper bound). -/
lemma anticomm_involution_le_two {n : ℕ} [NeZero n]
    (A₀ A₁ : Matrix (Fin n) (Fin n) ℂ)
    (hA₀_herm : A₀.IsHermitian) (hA₁_herm : A₁.IsHermitian)
    (hA₀_sq : A₀ * A₀ = 1) (hA₁_sq : A₁ * A₁ = 1) :
    IsPosSemidefComplex (2 • (1 : Matrix (Fin n) (Fin n) ℂ) - (A₀ * A₁ + A₁ * A₀)) := by
  let U := A₀ * A₁
  have hU : U * Uᴴ = 1 := involution_mul_involution_unitary A₀ A₁ hA₀_herm hA₁_herm hA₀_sq hA₁_sq
  have h_anticomm : A₀ * A₁ + A₁ * A₀ = U + Uᴴ := by
    simp only [U, Matrix.conjTranspose_mul, hA₀_herm.eq, hA₁_herm.eq]
  rw [h_anticomm]
  exact unitary_add_conjTranspose_le_two U hU

/-! ## Commutator Squared Bounds -/

/-- For Hermitian involutions, `[A₀,A₁]² ≥ -4I` — the same fact as `comm_sq_add_four_posSemidef`
with the summands swapped. -/
lemma comm_sq_ge_neg_four {n : ℕ} [NeZero n]
    (A₀ A₁ : Matrix (Fin n) (Fin n) ℂ)
    (hA₀_herm : A₀.IsHermitian) (hA₁_herm : A₁.IsHermitian)
    (hA₀_sq : A₀ * A₀ = 1) (hA₁_sq : A₁ * A₁ = 1) :
    IsPosSemidefComplex (⁅A₀, A₁⁆ * ⁅A₀, A₁⁆ + 4 • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  rw [add_comm]
  exact comm_sq_add_four_posSemidef A₀ A₁ hA₀_herm hA₁_herm hA₀_sq hA₁_sq

/-- For Hermitian involutions, `[A₀,A₁]² ≤ 4I`. -/
lemma comm_sq_le_four {n : ℕ} [NeZero n]
    (A₀ A₁ : Matrix (Fin n) (Fin n) ℂ)
    (hA₀_herm : A₀.IsHermitian) (hA₁_herm : A₁.IsHermitian)
    (hA₀_sq : A₀ * A₀ = 1) (hA₁_sq : A₁ * A₁ = 1) :
    IsPosSemidefComplex (4 • (1 : Matrix (Fin n) (Fin n) ℂ) - ⁅A₀, A₁⁆ * ⁅A₀, A₁⁆) := by
  rw [comm_sq_eq A₀ A₁ hA₀_sq hA₁_sq]
  -- Goal: IsPosSemidefComplex (4 • 1 - ((A₀ * A₁ + A₁ * A₀) * (A₀ * A₁ + A₁ * A₀) - 4 • 1))
  -- = 8 • 1 - (A₀ * A₁ + A₁ * A₀)²
  have h_simp :
      4 • (1 : Matrix (Fin n) (Fin n) ℂ) - ((A₀ * A₁ + A₁ * A₀) * (A₀ * A₁ + A₁ * A₀) - 4 • 1) =
      8 • (1 : Matrix (Fin n) (Fin n) ℂ) - (A₀ * A₁ + A₁ * A₀) * (A₀ * A₁ + A₁ * A₀) := by
    module
  rw [h_simp]
  -- A₀ * A₁ + A₁ * A₀ = U + Uᴴ where U = A₀ * A₁
  let U := A₀ * A₁
  have hU : U * Uᴴ = 1 := involution_mul_involution_unitary A₀ A₁ hA₀_herm hA₁_herm hA₀_sq hA₁_sq
  have h_anticomm : A₀ * A₁ + A₁ * A₀ = U + Uᴴ := by
    simp only [U, Matrix.conjTranspose_mul, hA₀_herm.eq, hA₁_herm.eq]
  rw [h_anticomm]
  -- 8I - (U + Uᴴ)² ≥ 4I ≥ 0 since (U + Uᴴ)² ≤ 4I
  have h_bound := unitary_add_conjTranspose_sq_le_four U hU
  -- h_bound : IsPosSemidefComplex (4 • 1 - (U + Uᴴ) * (U + Uᴴ))
  intro x
  have hx := h_bound x
  -- Decompose: 8 • 1 - H² = (4 • 1 - H²) + 4 • 1
  have h_decomp : 8 • (1 : Matrix (Fin n) (Fin n) ℂ) - (U + Uᴴ) * (U + Uᴴ) =
      (4 • (1 : Matrix (Fin n) (Fin n) ℂ) - (U + Uᴴ) * (U + Uᴴ)) +
      4 • (1 : Matrix (Fin n) (Fin n) ℂ) := by module
  rw [h_decomp, Matrix.add_mulVec, dotProduct_add, add_re]
  have h_4I_nonneg : 0 ≤ (star x ⬝ᵥ (4 • (1 : Matrix (Fin n) (Fin n) ℂ)).mulVec x).re := by
    rw [nsmul_one_mulVec, star_dotProduct_nsmul, nsmul_eq_mul, Nat.cast_ofNat,
        mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    have := star_dotProduct_self_re_nonneg x
    linarith
  linarith

/-! ## Commutator Product Bounds -/

/-- Shared unitary-decomposition setup behind both `comm_prod_ge_neg_four` and
`comm_prod_le_four`: for `U_A = A₀A₁`, `U_B = B₀B₁`, writes `[A₀,A₁][B₀,B₁]` as `W - V - V† + W†`
for the two unitaries `W = U_A U_B` and `V = U_A U_B†`, so both bounds reduce to
`unitary_add_conjTranspose_{ge_neg_two,le_two}` applied to `W` and `V`. -/
private lemma comm_prod_eq_unitary_decomp {n : ℕ} [NeZero n]
    (A₀ A₁ B₀ B₁ : Matrix (Fin n) (Fin n) ℂ)
    (hA₀_herm : A₀.IsHermitian) (hA₁_herm : A₁.IsHermitian)
    (hB₀_herm : B₀.IsHermitian) (hB₁_herm : B₁.IsHermitian)
    (hA₀_sq : A₀ * A₀ = 1) (hA₁_sq : A₁ * A₁ = 1)
    (hB₀_sq : B₀ * B₀ = 1) (hB₁_sq : B₁ * B₁ = 1)
    (hc00 : A₀ * B₀ = B₀ * A₀) (hc01 : A₀ * B₁ = B₁ * A₀)
    (hc10 : A₁ * B₀ = B₀ * A₁) (hc11 : A₁ * B₁ = B₁ * A₁) :
    ∃ W V : Matrix (Fin n) (Fin n) ℂ,
      ⁅A₀, A₁⁆ * ⁅B₀, B₁⁆ = W - V - Vᴴ + Wᴴ ∧ W * Wᴴ = 1 ∧ V * Vᴴ = 1 := by
  let U_A := A₀ * A₁
  let U_B := B₀ * B₁
  have hU_A : U_A * U_Aᴴ = 1 :=
    involution_mul_involution_unitary A₀ A₁ hA₀_herm hA₁_herm hA₀_sq hA₁_sq
  have hU_B : U_B * U_Bᴴ = 1 :=
    involution_mul_involution_unitary B₀ B₁ hB₀_herm hB₁_herm hB₀_sq hB₁_sq
  have h_commA := comm_eq_unitary_sub_conjTranspose A₀ A₁ hA₀_herm hA₁_herm
  have h_commB := comm_eq_unitary_sub_conjTranspose B₀ B₁ hB₀_herm hB₁_herm
  have hU_comm : U_A * U_B = U_B * U_A := by
    simp only [U_A, U_B]
    calc A₀ * A₁ * (B₀ * B₁)
        = A₀ * (A₁ * B₀) * B₁ := by rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = A₀ * (B₀ * A₁) * B₁ := by rw [hc10]
      _ = (A₀ * B₀) * A₁ * B₁ := by rw [← Matrix.mul_assoc A₀]
      _ = (B₀ * A₀) * A₁ * B₁ := by rw [hc00]
      _ = B₀ * (A₀ * A₁) * B₁ := by rw [Matrix.mul_assoc B₀]
      _ = B₀ * (A₀ * (A₁ * B₁)) := by rw [Matrix.mul_assoc, Matrix.mul_assoc]
      _ = B₀ * (A₀ * (B₁ * A₁)) := by rw [hc11]
      _ = B₀ * ((A₀ * B₁) * A₁) := by rw [← Matrix.mul_assoc A₀]
      _ = B₀ * ((B₁ * A₀) * A₁) := by rw [hc01]
      _ = B₀ * (B₁ * (A₀ * A₁)) := by rw [Matrix.mul_assoc B₁]
      _ = B₀ * B₁ * (A₀ * A₁) := by rw [← Matrix.mul_assoc B₀]
  have hU_commH : U_A * U_Bᴴ = U_Bᴴ * U_A := by
    simp only [U_A, U_B, Matrix.conjTranspose_mul, hB₀_herm.eq, hB₁_herm.eq]
    calc A₀ * A₁ * (B₁ * B₀)
        = A₀ * (A₁ * B₁) * B₀ := by rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = A₀ * (B₁ * A₁) * B₀ := by rw [hc11]
      _ = (A₀ * B₁) * A₁ * B₀ := by rw [← Matrix.mul_assoc A₀]
      _ = (B₁ * A₀) * A₁ * B₀ := by rw [hc01]
      _ = B₁ * (A₀ * A₁) * B₀ := by rw [Matrix.mul_assoc B₁]
      _ = B₁ * (A₀ * (A₁ * B₀)) := by rw [Matrix.mul_assoc, Matrix.mul_assoc]
      _ = B₁ * (A₀ * (B₀ * A₁)) := by rw [hc10]
      _ = B₁ * ((A₀ * B₀) * A₁) := by rw [← Matrix.mul_assoc A₀]
      _ = B₁ * ((B₀ * A₀) * A₁) := by rw [hc00]
      _ = B₁ * (B₀ * (A₀ * A₁)) := by rw [Matrix.mul_assoc B₀]
      _ = B₁ * B₀ * (A₀ * A₁) := by rw [← Matrix.mul_assoc B₁]
  have h_prod : ⁅A₀, A₁⁆ * ⁅B₀, B₁⁆ =
      U_A * U_B - U_A * U_Bᴴ - (U_Aᴴ * U_B - U_Aᴴ * U_Bᴴ) := by
    rw [h_commA, h_commB]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  refine ⟨U_A * U_B, U_A * U_Bᴴ, ?_, ?_, ?_⟩
  · have hU_AH_comm_B : U_Aᴴ * U_B = U_B * U_Aᴴ := by
      have := congrArg Matrix.conjTranspose hU_commH
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at this
      exact this.symm
    have h1 : U_Aᴴ * U_B = (U_A * U_Bᴴ)ᴴ := by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose]
      exact hU_AH_comm_B
    have h2 : U_Aᴴ * U_Bᴴ = (U_A * U_B)ᴴ := by
      simp only [conjTranspose_mul]
      have := congrArg Matrix.conjTranspose hU_comm
      simp only [Matrix.conjTranspose_mul] at this
      exact this.symm
    rw [h_prod, h1, h2]
    module
  · have h1 : (U_A * U_B)ᴴ = U_Bᴴ * U_Aᴴ := Matrix.conjTranspose_mul U_A U_B
    rw [h1]
    have h2 : U_A * U_B * (U_Bᴴ * U_Aᴴ) = U_A * (U_B * U_Bᴴ) * U_Aᴴ := by
      rw [Matrix.mul_assoc U_A U_B, ← Matrix.mul_assoc U_B]
      exact Eq.symm (Matrix.mul_assoc U_A (U_B * U_Bᴴ) U_Aᴴ)
    rw [h2, hU_B, Matrix.mul_one, hU_A]
  · have h1 : (U_A * U_Bᴴ)ᴴ = U_B * U_Aᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [h1]
    have h2 : U_A * U_Bᴴ * (U_B * U_Aᴴ) = U_A * (U_Bᴴ * U_B) * U_Aᴴ := by
      rw [Matrix.mul_assoc U_A U_Bᴴ, ← Matrix.mul_assoc U_Bᴴ]
      exact Eq.symm (Matrix.mul_assoc U_A (U_Bᴴ * U_B) U_Aᴴ)
    rw [h2, mul_eq_one_comm.mpr hU_B, Matrix.mul_one, hU_A]

/-- Product of commutators is bounded: `-4I ≤ [A₀,A₁][B₀,B₁] ≤ 4I` (lower bound). -/
lemma comm_prod_ge_neg_four {n : ℕ} [NeZero n]
    (A₀ A₁ B₀ B₁ : Matrix (Fin n) (Fin n) ℂ)
    (hA₀_herm : A₀.IsHermitian) (hA₁_herm : A₁.IsHermitian)
    (hB₀_herm : B₀.IsHermitian) (hB₁_herm : B₁.IsHermitian)
    (hA₀_sq : A₀ * A₀ = 1) (hA₁_sq : A₁ * A₁ = 1)
    (hB₀_sq : B₀ * B₀ = 1) (hB₁_sq : B₁ * B₁ = 1)
    (hc00 : A₀ * B₀ = B₀ * A₀) (hc01 : A₀ * B₁ = B₁ * A₀)
    (hc10 : A₁ * B₀ = B₀ * A₁) (hc11 : A₁ * B₁ = B₁ * A₁) :
    IsPosSemidefComplex (4 • (1 : Matrix (Fin n) (Fin n) ℂ) + ⁅A₀, A₁⁆ * ⁅B₀, B₁⁆) := by
  obtain ⟨W, V, h_expr, hW_unitary, hV_unitary⟩ :=
    comm_prod_eq_unitary_decomp A₀ A₁ B₀ B₁ hA₀_herm hA₁_herm hB₀_herm hB₁_herm
      hA₀_sq hA₁_sq hB₀_sq hB₁_sq hc00 hc01 hc10 hc11
  rw [h_expr]
  have h_rearrange : 4 • (1 : Matrix (Fin n) (Fin n) ℂ) + (W - V - Vᴴ + Wᴴ) =
                     (2 • (1 : Matrix (Fin n) (Fin n) ℂ) + (W + Wᴴ)) +
                     (2 • (1 : Matrix (Fin n) (Fin n) ℂ) - (V + Vᴴ)) := by module
  rw [h_rearrange]
  have h_W_bound := unitary_add_conjTranspose_ge_neg_two W hW_unitary
  have h_V_bound := unitary_add_conjTranspose_le_two V hV_unitary
  intro x
  have hWx := h_W_bound x
  have hVx := h_V_bound x
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec] at hWx hVx ⊢
  simp only [dotProduct_add, dotProduct_sub] at hWx hVx ⊢
  simp only [add_re, sub_re, nsmul_eq_mul, Nat.cast_ofNat] at hWx hVx ⊢
  linarith

/-- Product of commutators is bounded: `-4I ≤ [A₀,A₁][B₀,B₁] ≤ 4I` (upper bound). -/
lemma comm_prod_le_four {n : ℕ} [NeZero n]
    (A₀ A₁ B₀ B₁ : Matrix (Fin n) (Fin n) ℂ)
    (hA₀_herm : A₀.IsHermitian) (hA₁_herm : A₁.IsHermitian)
    (hB₀_herm : B₀.IsHermitian) (hB₁_herm : B₁.IsHermitian)
    (hA₀_sq : A₀ * A₀ = 1) (hA₁_sq : A₁ * A₁ = 1)
    (hB₀_sq : B₀ * B₀ = 1) (hB₁_sq : B₁ * B₁ = 1)
    (hc00 : A₀ * B₀ = B₀ * A₀) (hc01 : A₀ * B₁ = B₁ * A₀)
    (hc10 : A₁ * B₀ = B₀ * A₁) (hc11 : A₁ * B₁ = B₁ * A₁) :
    IsPosSemidefComplex (4 • (1 : Matrix (Fin n) (Fin n) ℂ) - ⁅A₀, A₁⁆ * ⁅B₀, B₁⁆) := by
  obtain ⟨W, V, h_expr, hW_unitary, hV_unitary⟩ :=
    comm_prod_eq_unitary_decomp A₀ A₁ B₀ B₁ hA₀_herm hA₁_herm hB₀_herm hB₁_herm
      hA₀_sq hA₁_sq hB₀_sq hB₁_sq hc00 hc01 hc10 hc11
  rw [h_expr]
  have h_rearrange : 4 • (1 : Matrix (Fin n) (Fin n) ℂ) - (W - V - Vᴴ + Wᴴ) =
                     (2 • (1 : Matrix (Fin n) (Fin n) ℂ) - (W + Wᴴ)) +
                     (2 • (1 : Matrix (Fin n) (Fin n) ℂ) + (V + Vᴴ)) := by module
  rw [h_rearrange]
  have h_W_bound := unitary_add_conjTranspose_le_two W hW_unitary
  have h_V_bound := unitary_add_conjTranspose_ge_neg_two V hV_unitary
  intro x
  have hWx := h_W_bound x
  have hVx := h_V_bound x
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec] at hWx hVx ⊢
  simp only [dotProduct_add, dotProduct_sub] at hWx hVx ⊢
  simp only [add_re, sub_re, nsmul_eq_mul, Nat.cast_ofNat] at hWx hVx ⊢
  linarith

end Spectra.QuantumInfo
