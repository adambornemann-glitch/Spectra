/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: Stage_2/Algebra/TruncTensor2.lean
-/
import Spectra.Mathlib.StochasticCalc.RoughPath.Axioms.NormedTensorSquare
/-!
# The Truncated Tensor Algebra T⁽²⁾(V)

## Overview

We construct the level-2 truncated tensor algebra

    T⁽²⁾(V) = ℝ × V × (V ⊗ V)

equipped with the **truncated tensor product**: the associative multiplication
that retains only components up to tensor degree 2. This is the ambient algebra
in which rough paths take values.

## Key definitions

* `TruncTensor₂ V` — the type, a structure with fields `a₀ : ℝ`, `a₁ : V`, `a₂ : T₂ V`
* `TruncTensor₂.tmul` — the truncated multiplication
* `TruncTensor₂.one` — the unit `(1, 0, 0)`
* `TruncTensor₂.tinv` — the inverse for elements with `a₀ = 1`
* `TruncTensor₂.normT` — the sum norm `|a₀| + ‖a₁‖ + ‖a₂‖`

## Key results

* `tmul_assoc` — associativity of truncated multiplication
* `one_tmul`, `tmul_one` — unit laws
* `tmul_tinv`, `tinv_tmul` — inverse laws (for `a₀ = 1`)
* `normT_tmul_le` — submultiplicativity: `‖a · b‖ ≤ ‖a‖ · ‖b‖`

## Design notes

The normed-space structure uses the sum norm `|a₀| + ‖a₁‖ + ‖a₂‖` rather than
the homogeneous norm `max(‖a₁‖, ‖a₂‖^{1/2})`. The sum norm is easier to prove
submultiplicative (each cross-term appears in the product of sums) and defines a
genuine norm (not merely a quasi-norm). The homogeneous norm lives on `GroupLike₂`
and is defined in `HomoNorm.lean`.

The multiplication is *not* commutative: the level-2 component of `a · b` contains
`a₁ ⊗ₜ b₁`, which differs from `b₁ ⊗ₜ a₁` in general. This noncommutativity is
the algebraic shadow of the fact that iterated integrals depend on path ordering.

## References

* Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Chapter 2
* Reutenauer, C., *Free Lie Algebras*, Oxford (1993)
-/

open Spectra.Mathlib.StochCalc.NormedTensorSquare

namespace Spectra.Mathlib.StochCalc

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedTensorSquare V]

/-! ## The type -/

/-- The level-2 truncated tensor algebra T⁽²⁾(V) = ℝ × V × (V ⊗ V).

An element `(a₀, a₁, a₂)` represents the formal sum `a₀ · 1 + a₁ + a₂`
where `1` is the unit, `a₁` is a degree-1 tensor, and `a₂` is a degree-2 tensor.

The multiplication truncates all terms of degree > 2. -/
structure TruncTensor₂ (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedTensorSquare V] where
  a₀ : ℝ
  a₁ : V
  a₂ : T₂ V

namespace TruncTensor₂

/-! ## Basic algebraic instances

We give T⁽²⁾(V) its componentwise additive group structure. This is the
*additive* structure of the algebra; the *multiplicative* structure (tmul)
is defined separately because it is not componentwise. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedTensorSquare V]

instance instZero : Zero (TruncTensor₂ V) :=
  ⟨⟨0, 0, 0⟩⟩

instance instAdd : Add (TruncTensor₂ V) :=
  ⟨fun a b => ⟨a.a₀ + b.a₀, a.a₁ + b.a₁, a.a₂ + b.a₂⟩⟩

instance instNeg : Neg (TruncTensor₂ V) :=
  ⟨fun a => ⟨-a.a₀, -a.a₁, -a.a₂⟩⟩

instance instSMul : SMul ℝ (TruncTensor₂ V) :=
  ⟨fun c a => ⟨c * a.a₀, c • a.a₁, c • a.a₂⟩⟩

@[ext] lemma ext {a b : TruncTensor₂ V}
    (h₀ : a.a₀ = b.a₀) (h₁ : a.a₁ = b.a₁) (h₂ : a.a₂ = b.a₂) :
    a = b := by
  cases a; cases b; simp_all
instance instSub : Sub (TruncTensor₂ V) :=
  ⟨fun a b => ⟨a.a₀ - b.a₀, a.a₁ - b.a₁, a.a₂ - b.a₂⟩⟩

@[simp] lemma zero_a₀ : (0 : TruncTensor₂ V).a₀ = 0 := rfl
@[simp] lemma zero_a₁ : (0 : TruncTensor₂ V).a₁ = 0 := rfl
@[simp] lemma zero_a₂ : (0 : TruncTensor₂ V).a₂ = 0 := rfl
@[simp] lemma add_a₀ (a b : TruncTensor₂ V) : (a + b).a₀ = a.a₀ + b.a₀ := rfl
@[simp] lemma add_a₁ (a b : TruncTensor₂ V) : (a + b).a₁ = a.a₁ + b.a₁ := rfl
@[simp] lemma add_a₂ (a b : TruncTensor₂ V) : (a + b).a₂ = a.a₂ + b.a₂ := rfl
@[simp] lemma neg_a₀ (a : TruncTensor₂ V) : (-a).a₀ = -a.a₀ := rfl
@[simp] lemma neg_a₁ (a : TruncTensor₂ V) : (-a).a₁ = -a.a₁ := rfl
@[simp] lemma neg_a₂ (a : TruncTensor₂ V) : (-a).a₂ = -a.a₂ := rfl
@[simp] lemma smul_a₀ (c : ℝ) (a : TruncTensor₂ V) : (c • a).a₀ = c * a.a₀ := rfl
@[simp] lemma smul_a₁ (c : ℝ) (a : TruncTensor₂ V) : (c • a).a₁ = c • a.a₁ := rfl
@[simp] lemma smul_a₂ (c : ℝ) (a : TruncTensor₂ V) : (c • a).a₂ = c • a.a₂ := rfl
@[simp] lemma sub_a₀ (a b : TruncTensor₂ V) : (a - b).a₀ = a.a₀ - b.a₀ := rfl
@[simp] lemma sub_a₁ (a b : TruncTensor₂ V) : (a - b).a₁ = a.a₁ - b.a₁ := rfl
@[simp] lemma sub_a₂ (a b : TruncTensor₂ V) : (a - b).a₂ = a.a₂ - b.a₂ := rfl

instance instAddCommGroup : AddCommGroup (TruncTensor₂ V) where
  add_assoc a b c := by ext <;> simp [add_assoc]
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  neg_add_cancel a := by ext <;> simp
  add_comm a b := by ext <;> simp [add_comm]
  sub_eq_add_neg a b := by ext <;> simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

/-! ## The sum norm -/

/-- The sum norm: `‖(a₀, a₁, a₂)‖ = |a₀| + ‖a₁‖ + ‖a₂‖`.

This is a genuine norm (positive definite, homogeneous, triangle inequality)
and is submultiplicative with respect to `tmul`. -/
def normT (a : TruncTensor₂ V) : ℝ := |a.a₀| + ‖a.a₁‖ + ‖a.a₂‖

lemma normT_nonneg (a : TruncTensor₂ V) : 0 ≤ normT a := by
  unfold normT
  positivity

lemma normT_zero : normT (0 : TruncTensor₂ V) = 0 := by
  simp [normT]

lemma normT_eq_zero {a : TruncTensor₂ V} (h : normT a = 0) : a = 0 := by
  simp only [normT] at h
  have h₀ : |a.a₀| = 0 := by linarith [abs_nonneg a.a₀, norm_nonneg a.a₁, norm_nonneg a.a₂]
  have h₁ : ‖a.a₁‖ = 0 := by linarith [abs_nonneg a.a₀, norm_nonneg a.a₁, norm_nonneg a.a₂]
  have h₂ : ‖a.a₂‖ = 0 := by linarith [abs_nonneg a.a₀, norm_nonneg a.a₁, norm_nonneg a.a₂]
  ext
  · exact abs_eq_zero.mp h₀
  · exact norm_eq_zero.mp h₁
  · exact norm_eq_zero.mp h₂

lemma normT_neg (a : TruncTensor₂ V) : normT (-a) = normT a := by
  simp [normT, abs_neg, norm_neg]

lemma normT_add_le (a b : TruncTensor₂ V) :
    normT (a + b) ≤ normT a + normT b := by
  simp only [normT, add_a₀, add_a₁, add_a₂]
  have h₀ := abs_add_le a.a₀ b.a₀
  have h₁ := norm_add_le a.a₁ b.a₁
  have h₂ := norm_add_le a.a₂ b.a₂
  linarith

lemma normT_smul (c : ℝ) (a : TruncTensor₂ V) :
    normT (c • a) = |c| * normT a := by
  show |c * a.a₀| + ‖c • a.a₁‖ + ‖c • a.a₂‖ = |c| * (|a.a₀| + ‖a.a₁‖ + ‖a.a₂‖)
  rw [abs_mul, norm_smul, norm_smul, Real.norm_eq_abs]
  ring

/-- The normed additive commutative group instance.

We define the norm via `normT` and derive all the `NormedAddCommGroup` fields.
This is infrastructure — the proofs are `normT_*` above. -/
instance instNormedAddCommGroup : NormedAddCommGroup (TruncTensor₂ V) where
  norm a := normT a
  dist a b := normT (a - b)
  dist_self a := by simp [normT]
  dist_comm a b := by
    show normT (a - b) = normT (b - a)
    rw [show a - b = -(b - a) from by abel, normT_neg]
  dist_triangle a b c := by
    show normT (a - c) ≤ normT (a - b) + normT (b - c)
    calc normT (a - c) = normT ((a - b) + (b - c)) := by congr 1; abel
      _ ≤ normT (a - b) + normT (b - c) := normT_add_le _ _
  eq_of_dist_eq_zero := by
    intro a b h
    exact sub_eq_zero.mp (normT_eq_zero h)
  dist_eq a b := by
    show normT (a - b) = normT (-a + b)
    rw [show -a + b = -(a - b) from by abel, normT_neg]


instance instModule : Module ℝ (TruncTensor₂ V) where
  one_smul a := by ext <;> norm_num
  mul_smul c d a := by ext <;> simp [mul_assoc, mul_smul]
  smul_zero c := by ext <;> simp [mul_zero, smul_zero]
  smul_add c a b := by ext <;> simp [mul_add, smul_add]
  add_smul c d a := by ext <;> simp [add_mul, add_smul]
  zero_smul a := by ext <;> simp [zero_mul, zero_smul]

instance instNormedSpace : NormedSpace ℝ (TruncTensor₂ V) where
  norm_smul_le c a := by
    show normT (c • a) ≤ ‖c‖ * normT a
    rw [normT_smul, Real.norm_eq_abs]


/-! ## Truncated multiplication

The truncated product retains components up to degree 2:

  `(a₀, a₁, a₂) ⊗ₜ (b₀, b₁, b₂) = (a₀b₀, a₀b₁ + a₁b₀, a₀b₂ + a₁⊗b₁ + a₂b₀)`

where `a₁ ⊗ b₁` is the tensor product of vectors (via `NormedTensorSquare.tprod`),
and scalar-vector multiplication uses the `ℝ`-module structure.

Degree-3+ terms (like `a₁ ⊗ b₂` or `a₂ ⊗ b₁`) are discarded. This truncation
is what makes the nilpotent structure work: `n³ = 0` for elements with `a₀ = 0`. -/
noncomputable def tmul (a b : TruncTensor₂ V) : TruncTensor₂ V where
  a₀ := a.a₀ * b.a₀
  a₁ := a.a₀ • b.a₁ + b.a₀ • a.a₁
  a₂ := a.a₀ • b.a₂ + (a.a₁ ⊗ₜ b.a₁) + b.a₀ • a.a₂

scoped infixl:70 " ⊗ₜₘ " => tmul

@[simp] lemma tmul_a₀ (a b : TruncTensor₂ V) :
    (a ⊗ₜₘ b).a₀ = a.a₀ * b.a₀ := rfl

@[simp] lemma tmul_a₁ (a b : TruncTensor₂ V) :
    (a ⊗ₜₘ b).a₁ = a.a₀ • b.a₁ + b.a₀ • a.a₁ := rfl

@[simp] lemma tmul_a₂ (a b : TruncTensor₂ V) :
    (a ⊗ₜₘ b).a₂ = a.a₀ • b.a₂ + (a.a₁ ⊗ₜ b.a₁) + b.a₀ • a.a₂ := rfl

/-! ## The unit element -/

/-- The unit of the truncated tensor algebra: `𝟙 = (1, 0, 0)`. -/
def one : TruncTensor₂ V := ⟨1, 0, 0⟩

@[simp] lemma one_a₀ : (one : TruncTensor₂ V).a₀ = 1 := rfl
@[simp] lemma one_a₁ : (one : TruncTensor₂ V).a₁ = (0 : V) := rfl
@[simp] lemma one_a₂ : (one : TruncTensor₂ V).a₂ = (0 : T₂ V) := rfl

/-- Left unit law: `𝟙 · a = a`. -/
lemma one_tmul (a : TruncTensor₂ V) : one ⊗ₜₘ a = a := by
  ext
  · simp [tmul, one]
  · simp [tmul, one]
  · simp [tmul, one]

/-- Right unit law: `a · 𝟙 = a`. -/
lemma tmul_one (a : TruncTensor₂ V) : a ⊗ₜₘ one = a := by
  ext
  · simp [tmul, one]
  · simp [tmul, one]
  · simp [tmul, one]

/-! ## Associativity

This is the main algebraic result. The proof strategy: compare components
of `(a ⊗ₜₘ b) ⊗ₜₘ c` and `a ⊗ₜₘ (b ⊗ₜₘ c)` using `ext`, then simplify
using bilinearity of `⊗ₜ` and `ℝ`-module laws.

The key step is at level 2, where we need:
  `(a₀b₁ + b₀a₁) ⊗ₜ c₁ + ... = a₁ ⊗ₜ (b₀c₁ + c₀b₁) + ...`
This follows from bilinearity: `⊗ₜ` distributes over `+` and commutes with `•`. -/
theorem tmul_assoc (a b c : TruncTensor₂ V) :
    (a ⊗ₜₘ b) ⊗ₜₘ c = a ⊗ₜₘ (b ⊗ₜₘ c) := by
  ext
  -- Level 0: (a₀ * b₀) * c₀ = a₀ * (b₀ * c₀)
  · simp [mul_assoc]
  -- Level 1
  · simp only [tmul_a₀, tmul_a₁]
    simp only [smul_add, mul_smul]
    module
  -- Level 2
  · simp only [tmul_a₀, tmul_a₁, tmul_a₂]
    rw [tprod_add_left, tprod_smul_left, tprod_smul_left,
        tprod_add_right, tprod_smul_right, tprod_smul_right]
    simp only [smul_add, mul_smul]
    module

/-! ## The inverse

For elements with `a₀ = 1`, the nilpotent part `n = (0, a₁, a₂)` satisfies
`n³ = 0` (truncation kills all degree ≥ 3 terms). Therefore the Neumann
series `(1 + n)⁻¹ = 1 - n + n²` terminates, giving:

  `(1, a₁, a₂)⁻¹ = (1, -a₁, a₁ ⊗ a₁ - a₂)`

We define the inverse only for elements with `a₀ = 1`. This suffices because
rough paths always have `a₀ = 1` (they are group-like). -/

/-- The inverse of `(1, x, 𝕏)` in the truncated tensor algebra.

  `tinv(1, x, 𝕏) = (1, -x, x ⊗ x - 𝕏)`

This is defined for *any* element but only meaningful when `a₀ = 1`.
The inverse laws `tmul_tinv` and `tinv_tmul` require `a₀ = 1` as a hypothesis. -/
noncomputable def tinv (a : TruncTensor₂ V) : TruncTensor₂ V where
  a₀ := 1
  a₁ := -a.a₁
  a₂ := (a.a₁ ⊗ₜ a.a₁) - a.a₂

@[simp] lemma tinv_a₀ (a : TruncTensor₂ V) : (tinv a).a₀ = 1 := rfl
@[simp] lemma tinv_a₁ (a : TruncTensor₂ V) : (tinv a).a₁ = -a.a₁ := rfl
@[simp] lemma tinv_a₂ (a : TruncTensor₂ V) :
    (tinv a).a₂ = (a.a₁ ⊗ₜ a.a₁) - a.a₂ := rfl

/-- Right inverse law: `a · a⁻¹ = 𝟙` when `a₀ = 1`. -/
lemma tmul_tinv {a : TruncTensor₂ V} (ha : a.a₀ = 1) :
    a ⊗ₜₘ (tinv a) = one := by
  ext
  -- Level 0: a₀ * 1 = 1
  · simp [tmul, tinv, ha]
  -- Level 1: a₀ • (-a₁) + 1 • a₁ = 0
  · simp [tmul, tinv, ha]
  -- Level 2: a₀ • (a₁⊗a₁ - a₂) + a₁⊗(-a₁) + 1 • a₂ = 0
  · simp only [tmul_a₂, tinv_a₁, tinv_a₂, ha, one_smul, one_a₂]
    -- a₁⊗(-a₁) = -(a₁⊗a₁) by linearity
    rw [show a.a₁ ⊗ₜ (-a.a₁) = -(a.a₁ ⊗ₜ a.a₁) from
      by rw [map_neg]]
    -- (a₁⊗a₁ - a₂) + (-(a₁⊗a₁)) + a₂ = 0
    simp only [tinv_a₀, one_smul]
    abel_nf

/-- Left inverse law: `a⁻¹ · a = 𝟙` when `a₀ = 1`. -/
lemma tinv_tmul {a : TruncTensor₂ V} (ha : a.a₀ = 1) :
    (tinv a) ⊗ₜₘ a = one := by
  ext
  -- Level 0: 1 * a₀ = 1
  · simp [tmul, tinv, ha]
  -- Level 1: 1 • a₁ + a₀ • (-a₁) = 0
  · simp [tmul, tinv, ha]
  -- Level 2: 1 • a₂ + (-a₁)⊗a₁ + a₀ • (a₁⊗a₁ - a₂) = 0
  · simp only [tmul_a₂, tinv_a₁, tinv_a₂, tinv_a₀, ha, one_smul, one_a₂]
    rw [show (-a.a₁) ⊗ₜ a.a₁ = -(a.a₁ ⊗ₜ a.a₁) from by
      rw [show (-a.a₁) = (-1 : ℝ) • a.a₁ from by simp,
          tprod_smul_left, neg_one_smul]]
    abel

/-- The inverse is an involution when `a₀ = 1`. -/
lemma tinv_tinv {a : TruncTensor₂ V} (ha : a.a₀ = 1) :
    tinv (tinv a) = a := by
  ext
  · simp [tinv, ha]
  · simp [tinv]
  · simp only [tinv_a₁, tinv_a₂]
    -- Need: (-a₁)⊗(-a₁) - (a₁⊗a₁ - a₂) = a₂
    rw [show (-a.a₁) ⊗ₜ (-a.a₁) = a.a₁ ⊗ₜ a.a₁ from by
      rw [show (-a.a₁) = (-1 : ℝ) • a.a₁ from by simp,
          tprod_smul_left, tprod_smul_right,
          show (-1 : ℝ) • ((-1 : ℝ) • (a.a₁ ⊗ₜ a.a₁)) = a.a₁ ⊗ₜ a.a₁ from by
            simp only [neg_smul, one_smul, smul_neg, neg_neg]]]
    abel

/-! ## Nilpotency

Elements with `a₀ = 0` are nilpotent: `n² ∈ {(0, 0, *)}` and `n³ = 0`.
This is the algebraic reason the inverse formula terminates. -/

/-- The "nilpotent part" of an element: set `a₀ = 0`. -/
def nilp (a : TruncTensor₂ V) : TruncTensor₂ V := ⟨0, a.a₁, a.a₂⟩

/-- Squaring a nilpotent element kills levels 0 and 1. -/
lemma nilp_tmul_nilp_a₀ (a : TruncTensor₂ V) :
    ((nilp a) ⊗ₜₘ (nilp a)).a₀ = 0 := by simp [nilp, tmul]

lemma nilp_tmul_nilp_a₁ (a : TruncTensor₂ V) :
    ((nilp a) ⊗ₜₘ (nilp a)).a₁ = 0 := by simp [nilp, tmul]

/-- Cubing a nilpotent element gives zero (truncation at level 2). -/
lemma nilp_cube (a : TruncTensor₂ V) :
    (nilp a) ⊗ₜₘ ((nilp a) ⊗ₜₘ (nilp a)) = 0 := by
  ext
  · simp [nilp, tmul]
  · simp [nilp, tmul]
  · simp only [tmul_a₂, smul_add, tmul_a₁, map_add, map_smul, tmul_a₀, zero_a₂]
    simp [nilp]

/-! ## Submultiplicativity of the sum norm

The key estimate for the truncated product:

  `‖a · b‖ ≤ ‖a‖ · ‖b‖`

where the norm is `normT`. The proof expands both sides and matches terms.
The critical ingredient is the cross-norm `‖v ⊗ₜ w‖ ≤ ‖v‖ · ‖w‖` from
`NormedTensorSquare`. -/
lemma normT_tmul_le (a b : TruncTensor₂ V) :
    normT (a ⊗ₜₘ b) ≤ normT a * normT b := by
  simp only [normT, tmul_a₀, tmul_a₁, tmul_a₂]
  have h₁ : ‖a.a₀ • b.a₁ + b.a₀ • a.a₁‖ ≤ |a.a₀| * ‖b.a₁‖ + |b.a₀| * ‖a.a₁‖ := by
    calc ‖a.a₀ • b.a₁ + b.a₀ • a.a₁‖
        ≤ ‖a.a₀ • b.a₁‖ + ‖b.a₀ • a.a₁‖ := norm_add_le _ _
      _ = |a.a₀| * ‖b.a₁‖ + |b.a₀| * ‖a.a₁‖ := by
          simp [norm_smul, Real.norm_eq_abs]
  have h₂ : ‖a.a₀ • b.a₂ + (a.a₁ ⊗ₜ b.a₁) + b.a₀ • a.a₂‖ ≤
      |a.a₀| * ‖b.a₂‖ + ‖a.a₁‖ * ‖b.a₁‖ + |b.a₀| * ‖a.a₂‖ := by
    calc ‖a.a₀ • b.a₂ + (a.a₁ ⊗ₜ b.a₁) + b.a₀ • a.a₂‖
        ≤ ‖a.a₀ • b.a₂‖ + ‖a.a₁ ⊗ₜ b.a₁‖ + ‖b.a₀ • a.a₂‖ := by
          calc _ ≤ ‖a.a₀ • b.a₂ + (a.a₁ ⊗ₜ b.a₁)‖ + ‖b.a₀ • a.a₂‖ :=
                norm_add_le _ _
            _ ≤ (‖a.a₀ • b.a₂‖ + ‖a.a₁ ⊗ₜ b.a₁‖) + ‖b.a₀ • a.a₂‖ := by
                gcongr; exact norm_add_le _ _
      _ ≤ |a.a₀| * ‖b.a₂‖ + ‖a.a₁‖ * ‖b.a₁‖ + |b.a₀| * ‖a.a₂‖ := by
          gcongr
          · rw [norm_smul, Real.norm_eq_abs]
          · exact norm_tprod_le a.a₁ b.a₁
          · rw [norm_smul, Real.norm_eq_abs]
  have ha₀ := abs_nonneg a.a₀
  have hb₀ := abs_nonneg b.a₀
  have ha₁ := norm_nonneg a.a₁
  have hb₁ := norm_nonneg b.a₁
  have ha₂ := norm_nonneg a.a₂
  have hb₂ := norm_nonneg b.a₂
  -- Two-step: first bound norms, then pure arithmetic
  calc |a.a₀ * b.a₀| + ‖a.a₀ • b.a₁ + b.a₀ • a.a₁‖ +
        ‖a.a₀ • b.a₂ + (a.a₁ ⊗ₜ b.a₁) + b.a₀ • a.a₂‖
      ≤ |a.a₀| * |b.a₀| + (|a.a₀| * ‖b.a₁‖ + |b.a₀| * ‖a.a₁‖) +
        (|a.a₀| * ‖b.a₂‖ + ‖a.a₁‖ * ‖b.a₁‖ + |b.a₀| * ‖a.a₂‖) := by
          linarith [abs_mul a.a₀ b.a₀]
    _ ≤ (|a.a₀| + ‖a.a₁‖ + ‖a.a₂‖) * (|b.a₀| + ‖b.a₁‖ + ‖b.a₂‖) := by
          nlinarith [mul_nonneg ha₁ hb₂, mul_nonneg ha₂ hb₁, mul_nonneg ha₂ hb₂]

/-! ## Component projections as continuous linear maps

These are the "forgetful" maps π₀, π₁, π₂ that extract components.
They are continuous with norm ≤ 1 (each component's norm is ≤ normT). -/

lemma norm_a₀_le (a : TruncTensor₂ V) : |a.a₀| ≤ normT a := by
  unfold normT; linarith [norm_nonneg a.a₁, norm_nonneg a.a₂]

lemma norm_a₁_le (a : TruncTensor₂ V) : ‖a.a₁‖ ≤ normT a := by
  unfold normT; linarith [abs_nonneg a.a₀, norm_nonneg a.a₂]

lemma norm_a₂_le (a : TruncTensor₂ V) : ‖a.a₂‖ ≤ normT a := by
  unfold normT; linarith [abs_nonneg a.a₀, norm_nonneg a.a₁]

/-! ## Embedding of V into T⁽²⁾(V)

The "degree-1 embedding" sends `v ↦ (0, v, 0)`. Its image generates the
full algebra under truncated multiplication. -/

/-- Embed a vector as a degree-1 element. -/
def ofVec (v : V) : TruncTensor₂ V := ⟨0, v, 0⟩

/-- Embed a scalar as a degree-0 element. -/
def ofScalar (c : ℝ) : TruncTensor₂ V := ⟨c, 0, 0⟩

/-- Embed a degree-2 tensor as a pure degree-2 element. -/
def ofTensor (x : T₂ V) : TruncTensor₂ V := ⟨0, 0, x⟩

/-- Product of two degree-1 elements is a degree-2 element.
This is how `v ⊗ w` arises inside the algebra. -/
lemma ofVec_tmul_ofVec (v w : V) :
    (ofVec v) ⊗ₜₘ (ofVec w) = ofTensor (v ⊗ₜ w) := by
  ext <;> simp [ofVec, ofTensor, tmul]

/-! ## Useful identities for Chen's identity

These are the identities that `GroupLike.lean` and `RoughPath/Defs.lean`
will use to verify Chen's identity in components. -/

/-- Multiplication of two "group-type" elements (with `a₀ = 1`).
This is the key formula:

  `(1, x, 𝕏) · (1, y, 𝕐) = (1, x+y, 𝕏 + x⊗y + 𝕐)`

which encodes both the additivity of increments (level 1) and
Chen's identity with its cross-term (level 2). -/
lemma tmul_unit_unit (x y : V) (𝕏 𝕐 : T₂ V) :
    (⟨1, x, 𝕏⟩ : TruncTensor₂ V) ⊗ₜₘ ⟨1, y, 𝕐⟩ =
      ⟨1, x + y, 𝕏 + (x ⊗ₜ y) + 𝕐⟩ := by
  ext
  · simp [tmul]
  · simp [tmul]; abel
  · simp [tmul]; abel

/-- The inverse formula for group-type elements, spelled out:

  `(1, x, 𝕏)⁻¹ = (1, -x, x⊗x - 𝕏)` -/
lemma tinv_unit (x : V) (𝕏 : T₂ V) :
    tinv (⟨1, x, 𝕏⟩ : TruncTensor₂ V) = ⟨1, -x, (x ⊗ₜ x) - 𝕏⟩ := by
  ext <;> simp [tinv]

end TruncTensor₂

end StochCalc
