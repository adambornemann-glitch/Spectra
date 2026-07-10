/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
/-!
# The conjugate Hilbert space `Conj E`

For a complex inner product space `E`, the **conjugate space** `Conj E` is the same set of vectors
with the same addition and norm, but with the *conjugated* scalar action and inner product:

  `c • x  :=  c̄ • x`        `⟪x, y⟫_{Conj E}  :=  ⟪y, x⟫_E  ( = conj ⟪x, y⟫_E )`.

This makes `Conj E` a genuine complex inner product space (complete if `E` is), and the identity
map `toConj : E → Conj E` an **antiunitary** (antilinear isometric) equivalence `E ≃ₗᵢ⋆[ℂ] Conj E`.

## Why this exists

An *antilinear* (conjugate-linear) operator `S : E → E` is exactly the same data as a *linear*
operator `E → Conj E`. This is the device that lets the unbounded **antilinear** operators of
Tomita–Takesaki theory (the Tomita operator `S : xΩ ↦ x⋆Ω` and its adjoint) be handled by
Mathlib's existing *linear* unbounded-operator machinery: the graph of an antilinear `S` is **not**
a `ℂ`-submodule of `E × E`, but the graph of its linearization `S̃ : E →ₗ.[ℂ] Conj E` **is** a
`ℂ`-submodule of `E × Conj E`, so `LinearPMap.{graph, IsClosable, closure, adjoint, IsSelfAdjoint}`
all apply verbatim. See `Spectra/Modular/TomitaTakesaki/ROADMAP.md` (milestone M0).

The bounded antiunitary case (the modular conjugation `J`) is handled separately by
`Spectra.QuantumMechanics.SpectralTheory.Conjugation`.

## Implementation

`Conj E` is the reducible-only-by-name type synonym `def Conj E := E`. The additive group, norm,
and completeness are inherited from `E` unchanged (`inferInstanceAs`); only the `ℂ`-module and inner
product are given the conjugated definitions. Because `Conj E` and `E` have distinct heads, instance
resolution never confuses the conjugated structure with the original.
-/

open scoped InnerProductSpace ComplexConjugate

namespace Spectra

/-- The conjugate space of `E`: the same underlying type, to be equipped with the conjugated
`ℂ`-scalar action and inner product. -/
def Conj (E : Type*) : Type _ := E

namespace Conj

variable {E : Type*}

/-- The identity map `E → Conj E` (antilinear once `Conj E` carries the conjugated action). -/
def toConj : E → Conj E := id

/-- The identity map `Conj E → E`. -/
def ofConj : Conj E → E := id

@[simp] lemma ofConj_toConj (x : E) : ofConj (toConj x) = x := rfl
@[simp] lemma toConj_ofConj (x : Conj E) : toConj (ofConj x) = x := rfl

lemma ofConj_injective : Function.Injective (ofConj : Conj E → E) := fun _ _ h => h

/-! ### Additive structure and norm (inherited unchanged from `E`) -/

instance [NormedAddCommGroup E] : NormedAddCommGroup (Conj E) :=
  inferInstanceAs (NormedAddCommGroup E)

@[simp] lemma ofConj_add [NormedAddCommGroup E] (x y : Conj E) :
    ofConj (x + y) = ofConj x + ofConj y := rfl
@[simp] lemma ofConj_zero [NormedAddCommGroup E] : ofConj (0 : Conj E) = 0 := rfl
@[simp] lemma ofConj_neg [NormedAddCommGroup E] (x : Conj E) : ofConj (-x) = -ofConj x := rfl
@[simp] lemma norm_ofConj [NormedAddCommGroup E] (x : Conj E) : ‖ofConj x‖ = ‖x‖ := rfl

/-! ### The conjugated `ℂ`-module structure -/

section Module
variable [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The conjugated scalar action `c • x = c̄ • x`. -/
instance instSMul : SMul ℂ (Conj E) := ⟨fun c x => toConj (starRingEnd ℂ c • ofConj x)⟩

@[simp] lemma ofConj_smul (c : ℂ) (x : Conj E) :
    ofConj (c • x) = starRingEnd ℂ c • ofConj x := rfl

instance instModule : Module ℂ (Conj E) where
  one_smul x := ofConj_injective <| by simp
  mul_smul a b x := ofConj_injective <| by simp [map_mul, mul_smul]
  smul_zero a := ofConj_injective <| by simp
  smul_add a x y := ofConj_injective <| by simp [smul_add]
  add_smul a b x := ofConj_injective <| by simp [map_add, add_smul]
  zero_smul x := ofConj_injective <| by simp

instance instNormedSpace : NormedSpace ℂ (Conj E) where
  norm_smul_le c x := by
    rw [show ‖c • x‖ = ‖ofConj (c • x)‖ from rfl, ofConj_smul, norm_smul, RCLike.norm_conj]
    exact le_of_eq rfl

end Module

/-! ### The conjugated inner product -/

section Inner
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The conjugated inner product `⟪x, y⟫_{Conj E} = ⟪y, x⟫_E`. -/
instance instInner : Inner ℂ (Conj E) := ⟨fun x y => @inner ℂ E _ (ofConj y) (ofConj x)⟩

lemma inner_def (x y : Conj E) :
    @inner ℂ (Conj E) _ x y = @inner ℂ E _ (ofConj y) (ofConj x) := rfl

instance instInnerProductSpace : InnerProductSpace ℂ (Conj E) where
  norm_sq_eq_re_inner x := by
    rw [inner_def]; exact norm_sq_eq_re_inner (𝕜 := ℂ) (ofConj x)
  conj_inner_symm x y := by
    rw [inner_def, inner_def]; exact inner_conj_symm (ofConj y) (ofConj x)
  add_left x y z := by
    simp only [inner_def, ofConj_add, inner_add_right]
  smul_left x y r := by
    simp only [inner_def, ofConj_smul, inner_smul_right]

end Inner

/-! ### Completeness -/

instance [NormedAddCommGroup E] [CompleteSpace E] : CompleteSpace (Conj E) :=
  inferInstanceAs (CompleteSpace E)

/-! ### The antiunitary equivalence `E ≃ₗᵢ⋆[ℂ] Conj E` -/

/-- The canonical **antiunitary** equivalence `E ≃ₗᵢ⋆[ℂ] Conj E`: the identity on vectors, which is
antilinear because the scalar action on `Conj E` is conjugated, and isometric because the norm is
unchanged. -/
def toConjₗᵢ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    E ≃ₗᵢ⋆[ℂ] Conj E where
  toFun := toConj
  invFun := ofConj
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := ofConj_injective <| by simp
  norm_map' _ := rfl

@[simp] lemma coe_toConjₗᵢ [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    ⇑(toConjₗᵢ E) = toConj := rfl

@[simp] lemma coe_toConjₗᵢ_symm [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    ⇑(toConjₗᵢ E).symm = ofConj := rfl

end Conj

end Spectra
