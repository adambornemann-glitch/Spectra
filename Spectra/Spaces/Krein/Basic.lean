/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Module

/-!
# Krein spaces via fundamental symmetries

The indefinite-inner-product substrate for Gupta–Bleuler quantization of the electromagnetic
field and for PT-symmetric quantum mechanics: a **Krein space** is a Hilbert space `H`
equipped with a **fundamental symmetry** `J` — a self-adjoint involutive (hence unitary)
operator — and the indefinite **Krein form** `[x, y] := ⟪J x, y⟫`.

This is the standard "fundamental decomposition first" presentation (Bognár, *Indefinite
Inner Product Spaces*, ch. V; Azizov–Iokhvidov, *Linear Operators in Spaces with an
Indefinite Metric*). Rather than axiomatizing an indefinite sesquilinear form and imposing
the existence of a maximal-definite decomposition, we take the Hilbert ambient plus `J` as
primitive; the two presentations are equivalent by the classical theory, and the operator
`J` is what every operator-theoretic development actually manipulates.

## Main definitions

* `Spectra.FundamentalSymmetry 𝕜 H` — a self-adjoint `J : H →L[𝕜] H` with `J ∘L J = 1`.
* `Spectra.FundamentalSymmetry.isometryEquiv` — `J` bundled as a unitary `H ≃ₗᵢ[𝕜] H`
  (its own inverse), with `isometryEquiv_trans_self` and `isometryEquiv_symm`.
* `Spectra.FundamentalSymmetry.kreinInner` — the Krein form `[x, y] = ⟪J x, y⟫`,
  conjugate-linear in `x` and linear in `y` (Mathlib convention).
* `Spectra.FundamentalSymmetry.posProj` / `negProj` / `posPart` / `negPart` — the spectral
  projections `½(1 ± J)` and the closed eigenspaces `ker (J ∓ 1)` they project onto.
* `Spectra.FundamentalSymmetry.kreinAdjoint` — the `J`-adjoint `A⁺ = J A† J`, and
  `IsKreinSelfAdjoint`.
* `Spectra.FundamentalSymmetry.id` — the identity fundamental symmetry: every Hilbert
  space is a Krein space with `[x, y] = ⟪x, y⟫`.
* `Spectra.FundamentalSymmetry.diagSymmetry` — the indefinite witness `diag(1, −1)` on
  `𝕜²`: the minimal Krein space whose form genuinely takes both signs.

## Main results

* `negPart_eq_orthogonal` — the fundamental decomposition is orthogonal: `H₋ = H₊ᗮ`.
* `posPart_sup_negPart` — and spanning: `H₊ ⊔ H₋ = ⊤`.
* `range_posProj` / `range_negProj` — the projections `½(1 ± J)` have ranges exactly
  `H₊` / `H₋`.
* `kreinInner_diagSymmetry_single_zero` / `kreinInner_diagSymmetry_single_one` — on the
  witness, `[e₀, e₀] = 1` and `[e₁, e₁] = −1`.
* `kreinInner_self_of_mem_posPart` / `kreinInner_self_of_mem_negPart` — the Krein form is
  positive definite on `H₊` (`[x, x] = ⟪x, x⟫`) and negative definite on `H₋`
  (`[x, x] = -⟪x, x⟫`).
* `kreinInner_map_left` — `[A x, y] = [x, A⁺ y]`: the `J`-adjoint is the adjoint for the
  Krein form.
* `kreinAdjoint_kreinAdjoint` — the `J`-adjoint is involutive: `A⁺⁺ = A`.
* `isKreinSelfAdjoint_iff_isSelfAdjoint_comp` — `A⁺ = A ↔ J A` is (Hilbert) self-adjoint.
-/

noncomputable section

namespace Spectra

variable (𝕜 H : Type*) [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- A **fundamental symmetry** on the Hilbert space `H`: a self-adjoint involution
`J : H →L[𝕜] H`. The pair `(H, J)` is a Krein space with indefinite form
`[x, y] := ⟪J x, y⟫` (`Spectra.FundamentalSymmetry.kreinInner`). -/
structure FundamentalSymmetry where
  /-- The underlying continuous linear operator. -/
  toContinuousLinearMap : H →L[𝕜] H
  /-- A fundamental symmetry is self-adjoint. -/
  isSelfAdjoint' : IsSelfAdjoint toContinuousLinearMap
  /-- A fundamental symmetry is an involution: `J ∘L J = 1`. -/
  comp_self : toContinuousLinearMap ∘L toContinuousLinearMap = 1

namespace FundamentalSymmetry

variable {𝕜 H}

instance : CoeFun (FundamentalSymmetry 𝕜 H) fun _ => H → H :=
  ⟨fun J => J.toContinuousLinearMap⟩

variable (J : FundamentalSymmetry 𝕜 H)

/-! ## Involution and unitarity -/

/-- The involution identity `J ∘L J = 1` in multiplicative form. -/
theorem mul_self : J.toContinuousLinearMap * J.toContinuousLinearMap = 1 :=
  J.comp_self

/-- Pointwise form of the involution identity: `J (J x) = x`. -/
@[simp]
theorem apply_apply (x : H) : J (J x) = x := by
  have h := DFunLike.congr_fun J.comp_self x
  rwa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at h

/-- A fundamental symmetry is an involutive function. -/
theorem involutive : Function.Involutive J.toContinuousLinearMap :=
  fun x => J.apply_apply x

/-- A fundamental symmetry is injective. -/
theorem injective : Function.Injective J.toContinuousLinearMap :=
  J.involutive.injective

/-- A fundamental symmetry is surjective. -/
theorem surjective : Function.Surjective J.toContinuousLinearMap :=
  J.involutive.surjective

/-- Restatement of self-adjointness: `J† = J`. -/
theorem adjoint_eq : ContinuousLinearMap.adjoint J.toContinuousLinearMap =
    J.toContinuousLinearMap :=
  J.isSelfAdjoint'.adjoint_eq

/-- A fundamental symmetry is unitary: `J† ∘L J = 1`, and `J` is surjective
(`J.surjective`), so `J†` is a genuine two-sided inverse. -/
theorem adjoint_comp_self :
    ContinuousLinearMap.adjoint J.toContinuousLinearMap ∘L J.toContinuousLinearMap = 1 := by
  rw [J.adjoint_eq]
  exact J.comp_self

/-- Self-adjointness pointwise: `⟪J x, y⟫ = ⟪x, J y⟫`. -/
theorem inner_map_left (x y : H) : inner 𝕜 (J x) y = inner 𝕜 x (J y) :=
  J.isSelfAdjoint'.isSymmetric x y

/-- A fundamental symmetry preserves the (Hilbert) inner product: `⟪J x, J y⟫ = ⟪x, y⟫`. -/
theorem inner_map_map (x y : H) : inner 𝕜 (J x) (J y) = inner 𝕜 x y := by
  rw [J.inner_map_left, J.apply_apply]

/-- A fundamental symmetry, bundled as a unitary (linear isometry equivalence); it is its
own inverse. -/
def isometryEquiv : H ≃ₗᵢ[𝕜] H :=
  LinearEquiv.isometryOfInner
    (LinearEquiv.ofInvolutive (J.toContinuousLinearMap : H →ₗ[𝕜] H) J.involutive)
    fun x y => J.inner_map_map x y

@[simp]
theorem isometryEquiv_apply (x : H) : J.isometryEquiv x = J x := rfl

/-- The bundled unitary is its own inverse. -/
theorem isometryEquiv_symm : J.isometryEquiv.symm = J.isometryEquiv :=
  LinearIsometryEquiv.ext fun _ => rfl

/-- The bundled unitary squares to the identity — the key identity for lifting `J` through
functorial constructions (tensor powers, Fock spaces). -/
theorem isometryEquiv_trans_self :
    J.isometryEquiv.trans J.isometryEquiv = LinearIsometryEquiv.refl 𝕜 H :=
  LinearIsometryEquiv.ext fun x => J.apply_apply x

/-- A fundamental symmetry is norm-preserving. -/
@[simp]
theorem norm_map (x : H) : ‖J x‖ = ‖x‖ :=
  J.isometryEquiv.norm_map x

/-! ## The Krein form -/

/-- The **Krein form** `[x, y] := ⟪J x, y⟫`: the indefinite inner product of the Krein
space `(H, J)`. Following the Mathlib convention it is conjugate-linear in `x` and linear
in `y`. -/
def kreinInner (x y : H) : 𝕜 := inner 𝕜 (J x) y

theorem kreinInner_def (x y : H) : J.kreinInner x y = inner 𝕜 (J x) y := rfl

/-- The Krein form can be computed with `J` acting on the right slot instead. -/
theorem kreinInner_eq_inner_right (x y : H) : J.kreinInner x y = inner 𝕜 x (J y) :=
  J.inner_map_left x y

/-- Conjugate symmetry of the Krein form. -/
theorem kreinInner_conj_symm (x y : H) :
    (starRingEnd 𝕜) (J.kreinInner y x) = J.kreinInner x y := by
  rw [kreinInner, kreinInner, inner_conj_symm, ← J.inner_map_left]

/-- The Krein form is additive in the first slot. -/
theorem kreinInner_add_left (x x' y : H) :
    J.kreinInner (x + x') y = J.kreinInner x y + J.kreinInner x' y := by
  rw [kreinInner, kreinInner, kreinInner, map_add, inner_add_left]

/-- The Krein form is additive in the second slot. -/
theorem kreinInner_add_right (x y y' : H) :
    J.kreinInner x (y + y') = J.kreinInner x y + J.kreinInner x y' := by
  rw [kreinInner, kreinInner, kreinInner, inner_add_right]

/-- The Krein form is conjugate-homogeneous in the first slot. -/
theorem kreinInner_smul_left (c : 𝕜) (x y : H) :
    J.kreinInner (c • x) y = (starRingEnd 𝕜) c * J.kreinInner x y := by
  rw [kreinInner, kreinInner, map_smul, inner_smul_left]

/-- The Krein form is homogeneous in the second slot. -/
theorem kreinInner_smul_right (c : 𝕜) (x y : H) :
    J.kreinInner x (c • y) = c * J.kreinInner x y := by
  rw [kreinInner, kreinInner, inner_smul_right]

/-- The Krein self-form `[x, x]` is conjugation-invariant. -/
theorem kreinInner_self_conj (x : H) :
    (starRingEnd 𝕜) (J.kreinInner x x) = J.kreinInner x x :=
  J.kreinInner_conj_symm x x

/-- The Krein self-form `[x, x]` is a real scalar (of arbitrary sign — the form is
indefinite). -/
theorem exists_real_kreinInner_self (x : H) : ∃ r : ℝ, J.kreinInner x x = (r : 𝕜) :=
  ⟨RCLike.re (J.kreinInner x x), (RCLike.conj_eq_iff_re.mp (J.kreinInner_self_conj x)).symm⟩

/-! ## The fundamental decomposition

The spectral projections `½(1 ± J)` decompose `H` as the orthogonal direct sum of the
`+1`- and `-1`-eigenspaces of `J`, on which the Krein form is positive (resp. negative)
definite. -/

/-- The projection `½(1 + J)` onto the positive part of the fundamental decomposition. -/
def posProj : H →L[𝕜] H := (2 : 𝕜)⁻¹ • (1 + J.toContinuousLinearMap)

/-- The projection `½(1 - J)` onto the negative part of the fundamental decomposition. -/
def negProj : H →L[𝕜] H := (2 : 𝕜)⁻¹ • (1 - J.toContinuousLinearMap)

theorem posProj_apply (x : H) : J.posProj x = (2 : 𝕜)⁻¹ • (x + J x) := by
  simp only [posProj, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply]

theorem negProj_apply (x : H) : J.negProj x = (2 : 𝕜)⁻¹ • (x - J x) := by
  simp only [negProj, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply]

/-- `posProj` is idempotent. -/
theorem isIdempotentElem_posProj : IsIdempotentElem J.posProj := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [ContinuousLinearMap.mul_apply, posProj_apply, posProj_apply, map_smul, map_add,
    apply_apply]
  module

/-- `negProj` is idempotent. -/
theorem isIdempotentElem_negProj : IsIdempotentElem J.negProj := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [ContinuousLinearMap.mul_apply, negProj_apply, negProj_apply, map_smul, map_sub,
    apply_apply]
  module

/-- `posProj` is self-adjoint. -/
theorem isSelfAdjoint_posProj : IsSelfAdjoint J.posProj := by
  have h2 : IsSelfAdjoint ((2 : 𝕜)⁻¹) := by simp [isSelfAdjoint_iff]
  exact h2.smul ((IsSelfAdjoint.one (H →L[𝕜] H)).add J.isSelfAdjoint')

/-- `negProj` is self-adjoint. -/
theorem isSelfAdjoint_negProj : IsSelfAdjoint J.negProj := by
  have h2 : IsSelfAdjoint ((2 : 𝕜)⁻¹) := by simp [isSelfAdjoint_iff]
  exact h2.smul ((IsSelfAdjoint.one (H →L[𝕜] H)).sub J.isSelfAdjoint')

/-- The two projections resolve the identity: `posProj + negProj = 1`. -/
theorem posProj_add_negProj : J.posProj + J.negProj = 1 := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [ContinuousLinearMap.add_apply, posProj_apply, negProj_apply,
    ContinuousLinearMap.one_apply]
  module

/-- Pointwise resolution of the identity: `posProj x + negProj x = x`. -/
theorem posProj_add_negProj_apply (x : H) : J.posProj x + J.negProj x = x := by
  have h := DFunLike.congr_fun J.posProj_add_negProj x
  rwa [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply] at h

/-- The two projections annihilate each other: `posProj ∘L negProj = 0`. -/
theorem posProj_comp_negProj : J.posProj ∘L J.negProj = 0 := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [ContinuousLinearMap.comp_apply, posProj_apply, negProj_apply, map_smul, map_sub,
    apply_apply, ContinuousLinearMap.zero_apply]
  module

/-- `J` fixes the range of `posProj`. -/
theorem apply_posProj (x : H) : J (J.posProj x) = J.posProj x := by
  rw [posProj_apply, map_smul, map_add, apply_apply]
  module

/-- `J` negates the range of `negProj`. -/
theorem apply_negProj (x : H) : J (J.negProj x) = -J.negProj x := by
  rw [negProj_apply, map_smul, map_sub, apply_apply]
  module

/-- Pointwise self-adjointness of `posProj`. -/
theorem inner_posProj_left (x y : H) :
    inner 𝕜 (J.posProj x) y = inner 𝕜 x (J.posProj y) :=
  J.isSelfAdjoint_posProj.isSymmetric x y

/-- Pointwise idempotency of `posProj`. -/
theorem posProj_posProj (x : H) : J.posProj (J.posProj x) = J.posProj x := by
  have h := DFunLike.congr_fun J.isIdempotentElem_posProj x
  rwa [ContinuousLinearMap.mul_apply] at h

/-- `⟪posProj y, y⟫` is already the square norm `⟪posProj y, posProj y⟫` — the standard
trick for self-adjoint idempotents. -/
theorem inner_posProj_self (y : H) :
    inner 𝕜 (J.posProj y) y = inner 𝕜 (J.posProj y) (J.posProj y) := by
  conv_lhs => rw [← J.posProj_posProj y]
  exact J.inner_posProj_left (J.posProj y) y

/-- The positive part `H₊` of the fundamental decomposition: the `+1`-eigenspace of `J`.
The Krein form is positive definite on it (`kreinInner_self_of_mem_posPart`). -/
def posPart : Submodule 𝕜 H := (J.toContinuousLinearMap - 1).ker

/-- The negative part `H₋` of the fundamental decomposition: the `-1`-eigenspace of `J`.
The Krein form is negative definite on it (`kreinInner_self_of_mem_negPart`). -/
def negPart : Submodule 𝕜 H := (J.toContinuousLinearMap + 1).ker

theorem mem_posPart_iff {x : H} : x ∈ J.posPart ↔ J x = x := by
  rw [posPart, LinearMap.mem_ker]
  simp only [ContinuousLinearMap.coe_sub, LinearMap.sub_apply, ContinuousLinearMap.coe_one,
    Module.End.one_apply, ContinuousLinearMap.coe_coe, sub_eq_zero]

theorem mem_negPart_iff {x : H} : x ∈ J.negPart ↔ J x = -x := by
  rw [negPart, LinearMap.mem_ker]
  simp only [ContinuousLinearMap.coe_add, LinearMap.add_apply, ContinuousLinearMap.coe_one,
    Module.End.one_apply, ContinuousLinearMap.coe_coe, add_eq_zero_iff_eq_neg]

/-- `posProj` lands in the positive part. -/
theorem posProj_mem_posPart (x : H) : J.posProj x ∈ J.posPart :=
  J.mem_posPart_iff.mpr (J.apply_posProj x)

/-- `negProj` lands in the negative part. -/
theorem negProj_mem_negPart (x : H) : J.negProj x ∈ J.negPart :=
  J.mem_negPart_iff.mpr (J.apply_negProj x)

/-- On the positive part, `posProj` acts as the identity. -/
theorem posProj_eq_self_of_mem_posPart {x : H} (hx : x ∈ J.posPart) :
    J.posProj x = x := by
  rw [posProj_apply, J.mem_posPart_iff.mp hx]
  module

/-- On the negative part, `negProj` acts as the identity. -/
theorem negProj_eq_self_of_mem_negPart {x : H} (hx : x ∈ J.negPart) :
    J.negProj x = x := by
  rw [negProj_apply, J.mem_negPart_iff.mp hx]
  module

/-- The range of `posProj` is exactly the positive part: `posProj` is genuinely the
projection **onto** `H₊`. -/
theorem range_posProj : (J.posProj).range = J.posPart := by
  ext x
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  constructor
  · rintro ⟨y, rfl⟩
    exact J.posProj_mem_posPart y
  · intro hx
    exact ⟨x, J.posProj_eq_self_of_mem_posPart hx⟩

/-- The range of `negProj` is exactly the negative part: `negProj` is genuinely the
projection **onto** `H₋`. -/
theorem range_negProj : (J.negProj).range = J.negPart := by
  ext x
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  constructor
  · rintro ⟨y, rfl⟩
    exact J.negProj_mem_negPart y
  · intro hx
    exact ⟨x, J.negProj_eq_self_of_mem_negPart hx⟩

theorem isClosed_posPart : IsClosed (J.posPart : Set H) :=
  (J.toContinuousLinearMap - 1).isClosed_ker

theorem isClosed_negPart : IsClosed (J.negPart : Set H) :=
  (J.toContinuousLinearMap + 1).isClosed_ker

instance : CompleteSpace J.posPart := J.isClosed_posPart.completeSpace_coe

instance : CompleteSpace J.negPart := J.isClosed_negPart.completeSpace_coe

/-- The positive and negative parts are (Hilbert-)orthogonal. -/
theorem inner_eq_zero_of_mem_posPart_of_mem_negPart {x y : H}
    (hx : x ∈ J.posPart) (hy : y ∈ J.negPart) : inner 𝕜 x y = 0 := by
  rw [mem_posPart_iff] at hx
  rw [mem_negPart_iff] at hy
  have h : inner 𝕜 x y = -inner 𝕜 x y := by
    calc inner 𝕜 x y = inner 𝕜 (J x) y := by rw [hx]
      _ = inner 𝕜 x (J y) := J.inner_map_left x y
      _ = inner 𝕜 x (-y) := by rw [hy]
      _ = -inner 𝕜 x y := inner_neg_right x y
  have h2 : (2 : 𝕜) * inner 𝕜 x y = 0 := by linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- The fundamental decomposition spans: `H₊ ⊔ H₋ = ⊤`. -/
theorem posPart_sup_negPart : J.posPart ⊔ J.negPart = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hdecomp : y = J.posProj y + J.negProj y := (J.posProj_add_negProj_apply y).symm
  rw [hdecomp]
  exact Submodule.add_mem_sup (J.posProj_mem_posPart y) (J.negProj_mem_negPart y)

/-- **The fundamental decomposition is orthogonal**: the negative part is exactly the
orthogonal complement of the positive part. Together with `posPart_sup_negPart` this is
the decomposition `H = H₊ ⊕ H₋` of Bognár, ch. V. -/
theorem negPart_eq_orthogonal : J.negPart = J.posPartᗮ := by
  refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
  · rw [Submodule.mem_orthogonal]
    exact fun x hx => J.inner_eq_zero_of_mem_posPart_of_mem_negPart hx hy
  · have h0 : inner 𝕜 (J.posProj y) y = (0 : 𝕜) :=
      (Submodule.mem_orthogonal J.posPart y).mp hy _ (J.posProj_mem_posPart y)
    have hP : J.posProj y = 0 := by
      rw [← inner_self_eq_zero (𝕜 := 𝕜), ← J.inner_posProj_self y]
      exact h0
    have hdecomp : y = J.negProj y := by
      have h1 := J.posProj_add_negProj_apply y
      rwa [hP, zero_add, eq_comm] at h1
    rw [mem_negPart_iff, hdecomp]
    exact J.apply_negProj y

/-- The Krein form is **positive definite on the positive part**: for `x ∈ H₊` it agrees
with the Hilbert inner product. -/
theorem kreinInner_self_of_mem_posPart {x : H} (hx : x ∈ J.posPart) :
    J.kreinInner x x = inner 𝕜 x x := by
  rw [kreinInner, J.mem_posPart_iff.mp hx]

/-- The Krein form is **negative definite on the negative part**: for `x ∈ H₋` it is the
negative of the Hilbert inner product. -/
theorem kreinInner_self_of_mem_negPart {x : H} (hx : x ∈ J.negPart) :
    J.kreinInner x x = -inner 𝕜 x x := by
  rw [kreinInner, J.mem_negPart_iff.mp hx, inner_neg_left]

/-- Norm-squared form of positive definiteness on `H₊`: `[x, x] = ‖x‖²`. -/
theorem kreinInner_self_eq_norm_sq_of_mem_posPart {x : H} (hx : x ∈ J.posPart) :
    J.kreinInner x x = (‖x‖ : 𝕜) ^ 2 := by
  rw [J.kreinInner_self_of_mem_posPart hx]
  exact inner_self_eq_norm_sq_to_K x

/-- Norm-squared form of negative definiteness on `H₋`: `[x, x] = -‖x‖²`. -/
theorem kreinInner_self_eq_neg_norm_sq_of_mem_negPart {x : H} (hx : x ∈ J.negPart) :
    J.kreinInner x x = -(‖x‖ : 𝕜) ^ 2 := by
  rw [J.kreinInner_self_of_mem_negPart hx, inner_self_eq_norm_sq_to_K]

/-! ## The `J`-adjoint -/

/-- The **`J`-adjoint** (Krein adjoint) of an operator: `A⁺ := J A† J`. It is the adjoint
with respect to the Krein form (`kreinInner_map_left`). -/
def kreinAdjoint (A : H →L[𝕜] H) : H →L[𝕜] H :=
  J.toContinuousLinearMap ∘L ContinuousLinearMap.adjoint A ∘L J.toContinuousLinearMap

theorem kreinAdjoint_apply (A : H →L[𝕜] H) (y : H) :
    J.kreinAdjoint A y = J (ContinuousLinearMap.adjoint A (J y)) := rfl

/-- The `J`-adjoint is the adjoint for the Krein form: `[A x, y] = [x, A⁺ y]`. -/
theorem kreinInner_map_left (A : H →L[𝕜] H) (x y : H) :
    J.kreinInner (A x) y = J.kreinInner x (J.kreinAdjoint A y) := by
  rw [kreinInner, kreinInner, kreinAdjoint_apply, J.inner_map_map,
    ContinuousLinearMap.adjoint_inner_right, ← J.inner_map_left]

/-- The Hilbert adjoint of the `J`-adjoint is the `J`-conjugate: `(A⁺)† = J A J`. -/
theorem adjoint_kreinAdjoint (A : H →L[𝕜] H) :
    ContinuousLinearMap.adjoint (J.kreinAdjoint A) =
      J.toContinuousLinearMap ∘L (A ∘L J.toContinuousLinearMap) := by
  rw [kreinAdjoint, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, J.adjoint_eq, ContinuousLinearMap.comp_assoc]

/-- The `J`-adjoint is involutive: `A⁺⁺ = A`. -/
theorem kreinAdjoint_kreinAdjoint (A : H →L[𝕜] H) :
    J.kreinAdjoint (J.kreinAdjoint A) = A := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [kreinAdjoint_apply, adjoint_kreinAdjoint, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, apply_apply, apply_apply]

/-- An operator is **`J`-self-adjoint** (Krein self-adjoint) when it equals its
`J`-adjoint. This is the symmetry notion of Gupta–Bleuler quantization and PT-symmetric
quantum mechanics: symmetric for the indefinite form, not for the Hilbert one. -/
def IsKreinSelfAdjoint (A : H →L[𝕜] H) : Prop := J.kreinAdjoint A = A

/-- `A` is `J`-self-adjoint iff `J A` is self-adjoint in the Hilbert sense. -/
theorem isKreinSelfAdjoint_iff_isSelfAdjoint_comp (A : H →L[𝕜] H) :
    J.IsKreinSelfAdjoint A ↔ IsSelfAdjoint (J.toContinuousLinearMap ∘L A) := by
  have hstar : J.kreinAdjoint A =
      J.toContinuousLinearMap * (star A * J.toContinuousLinearMap) := by
    rw [kreinAdjoint, ContinuousLinearMap.star_eq_adjoint]
    rfl
  constructor
  · intro h
    rw [IsKreinSelfAdjoint, hstar] at h
    rw [isSelfAdjoint_iff, ← ContinuousLinearMap.mul_def, star_mul,
      J.isSelfAdjoint'.star_eq]
    calc star A * J.toContinuousLinearMap
        = 1 * (star A * J.toContinuousLinearMap) := (one_mul _).symm
      _ = J.toContinuousLinearMap * J.toContinuousLinearMap *
            (star A * J.toContinuousLinearMap) := by rw [J.mul_self]
      _ = J.toContinuousLinearMap *
            (J.toContinuousLinearMap * (star A * J.toContinuousLinearMap)) := mul_assoc _ _ _
      _ = J.toContinuousLinearMap * A := by rw [h]
  · intro h
    have h' : star A * J.toContinuousLinearMap = J.toContinuousLinearMap * A := by
      have hs := h.star_eq
      rwa [← ContinuousLinearMap.mul_def, star_mul, J.isSelfAdjoint'.star_eq] at hs
    rw [IsKreinSelfAdjoint, hstar, h', ← mul_assoc, J.mul_self, one_mul]

/-! ## The identity fundamental symmetry

Every Hilbert space is a Krein space: take `J = 1`, so that the Krein form is the Hilbert
inner product and the negative part is trivial. -/

variable (𝕜 H) in
/-- The identity fundamental symmetry `J = 1`: the (trivial) Krein structure whose Krein
form is the Hilbert inner product itself. -/
protected def id : FundamentalSymmetry 𝕜 H where
  toContinuousLinearMap := 1
  isSelfAdjoint' := IsSelfAdjoint.one (H →L[𝕜] H)
  comp_self := mul_one 1

@[simp]
theorem id_apply (x : H) : FundamentalSymmetry.id 𝕜 H x = x := rfl

/-- For the identity fundamental symmetry the Krein form is the Hilbert inner product:
a Hilbert space *is* a Krein space. -/
@[simp]
theorem kreinInner_id (x y : H) :
    (FundamentalSymmetry.id 𝕜 H).kreinInner x y = inner 𝕜 x y := rfl

/-! ## An indefinite witness: `diag(1, −1)` on `𝕜²`

The minimal genuinely indefinite Krein space: on `EuclideanSpace 𝕜 (Fin 2)` the fundamental
symmetry `diag(1, −1)` yields a Krein form with `[e₀, e₀] = 1` and `[e₁, e₁] = −1`. -/

section IndefiniteWitness

variable (𝕜)

/-- The reflection `(a, b) ↦ (a, −b)` of `𝕜²`, as a linear isometry equivalence:
`diag(1, −1)` coordinatewise. -/
def negSecond : EuclideanSpace 𝕜 (Fin 2) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin 2) :=
  LinearIsometryEquiv.piLpCongrRight 2 fun i : Fin 2 =>
    if i = 0 then LinearIsometryEquiv.refl 𝕜 𝕜 else LinearIsometryEquiv.neg 𝕜

@[simp]
theorem negSecond_apply (x : EuclideanSpace 𝕜 (Fin 2)) (i : Fin 2) :
    negSecond 𝕜 x i = if i = 0 then x i else -x i := by
  rcases eq_or_ne i 0 with rfl | hi
  · simp [negSecond, PiLp.toLp_apply]
  · simp [negSecond, PiLp.toLp_apply, hi]

/-- The reflection is symmetric for the Hilbert inner product. -/
theorem inner_negSecond_left (x y : EuclideanSpace 𝕜 (Fin 2)) :
    inner 𝕜 (negSecond 𝕜 x) y = inner 𝕜 x (negSecond 𝕜 y) := by
  simp [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two]

/-- The reflection is an involution. -/
theorem negSecond_negSecond (x : EuclideanSpace 𝕜 (Fin 2)) :
    negSecond 𝕜 (negSecond 𝕜 x) = x := by
  refine PiLp.ext fun i => ?_
  rcases eq_or_ne i 0 with rfl | hi
  · simp
  · simp [hi]

/-- **The indefinite witness** `diag(1, −1)` on `𝕜²`, as a fundamental symmetry: the
minimal genuinely indefinite Krein space. Its Krein form takes the value `+1` on the first
standard basis vector and `−1` on the second (`kreinInner_diagSymmetry_single_zero`,
`kreinInner_diagSymmetry_single_one`). -/
def diagSymmetry : FundamentalSymmetry 𝕜 (EuclideanSpace 𝕜 (Fin 2)) where
  toContinuousLinearMap := (negSecond 𝕜).toLinearIsometry.toContinuousLinearMap
  isSelfAdjoint' :=
    LinearMap.IsSymmetric.isSelfAdjoint fun x y => inner_negSecond_left 𝕜 x y
  comp_self := ContinuousLinearMap.ext fun x => negSecond_negSecond 𝕜 x

@[simp]
theorem diagSymmetry_apply (x : EuclideanSpace 𝕜 (Fin 2)) :
    diagSymmetry 𝕜 x = negSecond 𝕜 x := rfl

/-- The Krein form of the witness is `+1` on the first basis vector: `[e₀, e₀] = 1`. -/
theorem kreinInner_diagSymmetry_single_zero :
    (diagSymmetry 𝕜).kreinInner (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)
      = 1 := by
  rw [kreinInner_def]
  simp [PiLp.inner_apply, RCLike.inner_apply]

/-- The Krein form of the witness is `−1` on the second basis vector: `[e₁, e₁] = −1`.
Together with `kreinInner_diagSymmetry_single_zero` this exhibits a Krein form that is
genuinely indefinite. -/
theorem kreinInner_diagSymmetry_single_one :
    (diagSymmetry 𝕜).kreinInner (EuclideanSpace.single 1 1) (EuclideanSpace.single 1 1)
      = -1 := by
  rw [kreinInner_def]
  simp [PiLp.inner_apply, RCLike.inner_apply]

end IndefiniteWitness

end FundamentalSymmetry

-- Sanity: the identity Krein structure has the expected trivial behavior, and a
-- fundamental symmetry is found to be a bundled unitary by `isometryEquiv`.
section Sanity

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

example (x y : H) : (FundamentalSymmetry.id 𝕜 H).kreinInner x y = inner 𝕜 x y :=
  FundamentalSymmetry.kreinInner_id x y

example (J : FundamentalSymmetry 𝕜 H) : H ≃ₗᵢ[𝕜] H := J.isometryEquiv

example (J : FundamentalSymmetry 𝕜 H) (A : H →L[𝕜] H) :
    J.kreinAdjoint (J.kreinAdjoint A) = A := J.kreinAdjoint_kreinAdjoint A

end Sanity

end Spectra
