/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearPMap
/-!
# The infinitesimal generator of a one-parameter unitary group

## Design

The generator is **constructed**, not axiomatized.  We define

* `genDiffQuot U ψ`        : the difference quotient `t ↦ (U t ψ - ψ)/(it)`,
* `generatorDomain U`      : the submodule of `ψ` for which that quotient converges,
* `generator U`            : the `LinearPMap` with that domain, sending `ψ` to the limit.

Uniqueness of the generator is then *definitional* (there is one object, period), so no
separate uniqueness lemma is needed.  Linearity is forced by uniqueness of limits.

## The self-adjointness target

The substantive half of Stone's lemma is the single statement

    `IsSelfAdjoint (generator U)`      -- i.e. `(generator U)† = (generator U)`

using Mathlib's canonical self-adjointness for `LinearPMap` (`LinearPMap.isSelfAdjoint_def`).
We deliberately do NOT bundle density, symmetry, closedness, or a deficiency-index
condition into the definition:

* symmetry  (`generator_isFormalAdjoint`)  is a cheap consequence of unitarity, proved here;
* density   (`IsSelfAdjoint.dense_domain`) and
  closedness (`IsSelfAdjoint.isClosed`)    are *given by Mathlib* once self-adjointness holds.

So the only thing a downstream file must earn is surjectivity of `A ± iI`
(`ran(A + iI) = ran(A - iI) = H`, the deficiency-index-zero condition), and then invoke
von Neumann's criterion `symmetric ∧ zero deficiency → self-adjoint`.  That criterion, and
the resolvent estimates that establish surjectivity, belong in `SelfAdjoint.lean`, not here.

## References
* Stone, "On one-parameter unitary groups in Hilbert space", Ann. of Math. (1932).
-/
open InnerProductSpace Complex Filter Topology
open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

namespace Spectra

/-- A one-parameter unitary group `{U(t)}_{t∈ℝ}` on a Hilbert space `H`: a group homomorphism
from `(ℝ, +)` into the unitary operators on `H`, strongly continuous in `t`. -/
structure OneParameterUnitaryGroup (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The unitary operator at time `t`. -/
  U : ℝ → (H →L[ℂ] H)
  unitary : ∀ (t : ℝ) (ψ φ : H), ⟪U t ψ, U t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ
  group_law : ∀ s t : ℝ, U (s + t) = (U s).comp (U t)
  identity : U 0 = ContinuousLinearMap.id ℂ H
  strong_continuous : ∀ ψ : H, Continuous (fun t : ℝ => U t ψ)

namespace OneParameterUnitaryGroup

variable [CompleteSpace H]

/-! ### Basic unitarity facts (reused from the prior compiling build) -/

lemma inverse_eq_adjoint (U : OneParameterUnitaryGroup (H := H)) (t : ℝ) :
    U.U (-t) = (U.U t).adjoint := by
  have h_inv : ∀ x : H, U.U t (U.U (-t) x) = x := fun x => by
    have h := U.group_law t (-t)
    rw [show t + (-t) = 0 by ring, U.identity] at h
    simpa using DFunLike.congr_fun h.symm x
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [← U.unitary t (U.U (-t) x) y, h_inv x]

lemma norm_preserving (U : OneParameterUnitaryGroup (H := H)) (t : ℝ) (ψ : H) :
    ‖U.U t ψ‖ = ‖ψ‖ :=
  (LinearMap.norm_map_iff_inner_map_map (U.U t)).mpr (U.unitary t) ψ

lemma norm_one [Nontrivial H] (U : OneParameterUnitaryGroup (H := H)) (t : ℝ) :
    ‖U.U t‖ = 1 := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ψ => le_of_eq ?_
    rw [norm_preserving, one_mul]
  · obtain ⟨ψ, hψ⟩ := exists_ne (0 : H)
    have hpos : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
    have hle := (U.U t).le_opNorm ψ
    rw [norm_preserving] at hle
    nlinarith [hle, hpos]

/-! ### The difference quotient -/

/-- The difference quotient whose limit is the generator: `t ↦ (U t ψ - ψ)/(it)`. -/
noncomputable def genDiffQuot (U : OneParameterUnitaryGroup (H := H)) (ψ : H) : ℝ → H :=
  fun t => ((I * (t : ℂ))⁻¹) • (U.U t ψ - ψ)

@[simp] lemma genDiffQuot_apply (U : OneParameterUnitaryGroup (H := H)) (ψ : H) (t : ℝ) :
    genDiffQuot U ψ t = ((I * (t : ℂ))⁻¹) • (U.U t ψ - ψ) := rfl

@[simp] lemma genDiffQuot_zero (U : OneParameterUnitaryGroup (H := H)) :
    genDiffQuot U (0 : H) = fun _ => 0 := by
  funext t; simp [genDiffQuot]

lemma genDiffQuot_add (U : OneParameterUnitaryGroup (H := H)) (a b : H) :
    genDiffQuot U (a + b) = genDiffQuot U a + genDiffQuot U b := by
  funext t
  simp only [genDiffQuot_apply, Pi.add_apply, map_add]
  rw [show U.U t a + U.U t b - (a + b) = (U.U t a - a) + (U.U t b - b) by abel, smul_add]

lemma genDiffQuot_smul (U : OneParameterUnitaryGroup (H := H)) (c : ℂ) (a : H) :
    genDiffQuot U (c • a) = c • genDiffQuot U a := by
  funext t
  simp only [genDiffQuot_apply, Pi.smul_apply, map_smul]
  rw [← smul_sub, smul_comm]

/-! ### The domain and the generator -/

/-- The set of vectors at which the generator limit exists, as a `ℂ`-submodule. -/
def generatorDomain (U : OneParameterUnitaryGroup (H := H)) : Submodule ℂ H where
  carrier := {ψ | ∃ η, Tendsto (genDiffQuot U ψ) (𝓝[≠] 0) (𝓝 η)}
  add_mem' := by
    rintro a b ⟨ηa, ha⟩ ⟨ηb, hb⟩
    exact ⟨ηa + ηb, by rw [genDiffQuot_add]; exact ha.add hb⟩
  smul_mem' := by
    rintro c a ⟨ηa, ha⟩
    exact ⟨c • ηa, by rw [genDiffQuot_smul]; exact ha.const_smul c⟩
  zero_mem' := ⟨0, by rw [genDiffQuot_zero]; exact tendsto_const_nhds⟩

@[simp] lemma mem_generatorDomain {U : OneParameterUnitaryGroup (H := H)} {ψ : H} :
    ψ ∈ generatorDomain U ↔ ∃ η, Tendsto (genDiffQuot U ψ) (𝓝[≠] 0) (𝓝 η) := Iff.rfl

/-- The infinitesimal generator as a (generally unbounded) partial linear operator.
The value at `ψ` is the limit of the difference quotient; linearity is forced by
uniqueness of limits in the Hausdorff space `H`. -/
noncomputable def generator (U : OneParameterUnitaryGroup (H := H)) : H →ₗ.[ℂ] H where
  domain := generatorDomain U
  toFun :=
  { toFun := fun x => x.2.choose
    map_add' := by
      intro x y
      refine tendsto_nhds_unique (x + y).2.choose_spec ?_
      have h : genDiffQuot U ((x + y : generatorDomain U) : H)
             = genDiffQuot U (x : H) + genDiffQuot U (y : H) := by
        rw [Submodule.coe_add, genDiffQuot_add]
      rw [h]; exact x.2.choose_spec.add y.2.choose_spec
    map_smul' := by
      intro c x
      refine tendsto_nhds_unique (c • x).2.choose_spec ?_
      have h : genDiffQuot U ((c • x : generatorDomain U) : H)
             = c • genDiffQuot U (x : H) := by
        rw [Submodule.coe_smul, genDiffQuot_smul]
      rw [h, RingHom.id_apply]; exact x.2.choose_spec.const_smul c }

@[simp] lemma generator_domain (U : OneParameterUnitaryGroup (H := H)) :
    (generator U).domain = generatorDomain U := rfl

/-- The defining property: the generator is the limit of the difference quotient. -/
lemma generator_tendsto (U : OneParameterUnitaryGroup (H := H)) (x : (generator U).domain) :
    Tendsto (genDiffQuot U (x : H)) (𝓝[≠] 0) (𝓝 (generator U x)) :=
  x.2.choose_spec

/-! ### Symmetry -/

/-- The generator is symmetric.  This is the easy structural fact; it does NOT need
density.  Proof: `⟪genDiffQuot U x t, y⟫ = ⟪x, genDiffQuot U y (-t)⟫` pointwise (using
`U t * = U (-t)`), and `t ↦ -t` preserves `𝓝[≠] 0`, so the two limits coincide. -/
lemma generator_isFormalAdjoint (U : OneParameterUnitaryGroup (H := H)) :
    (generator U).IsFormalAdjoint (generator U) := by
  intro x y
  -- the two difference-quotient inner products and their limits
  have hgx : Tendsto (fun t : ℝ => ⟪genDiffQuot U (x : H) t, (y : H)⟫_ℂ) (𝓝[≠] 0)
      (𝓝 ⟪generator U x, (y : H)⟫_ℂ) := (generator_tendsto U x).inner tendsto_const_nhds
  have hgy : Tendsto (fun s : ℝ => ⟪(x : H), genDiffQuot U (y : H) s⟫_ℂ) (𝓝[≠] 0)
      (𝓝 ⟪(x : H), generator U y⟫_ℂ) := tendsto_const_nhds.inner (generator_tendsto U y)
  -- negation preserves the punctured neighbourhood of 0
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  have hgy' : Tendsto (fun t : ℝ => ⟪(x : H), genDiffQuot U (y : H) (-t)⟫_ℂ) (𝓝[≠] 0)
      (𝓝 ⟪(x : H), generator U y⟫_ℂ) := hgy.comp hneg
  -- pointwise identity on the punctured neighbourhood
  have key : (fun t : ℝ => ⟪genDiffQuot U (x : H) t, (y : H)⟫_ℂ)
      =ᶠ[𝓝[≠] 0] (fun t : ℝ => ⟪(x : H), genDiffQuot U (y : H) (-t)⟫_ℂ) := by
    filter_upwards with t
    simp only [genDiffQuot_apply, inner_smul_left, inner_smul_right]
    have hW : ⟪U.U t (x : H) - (x : H), (y : H)⟫_ℂ
            = ⟪(x : H), U.U (-t) (y : H) - (y : H)⟫_ℂ := by
      rw [inner_sub_left, inner_sub_right, inverse_eq_adjoint U t,
          ContinuousLinearMap.adjoint_inner_right]
    rw [hW]
    have hconj : (starRingEnd ℂ) ((I * (t : ℂ))⁻¹) = (I * ((-t : ℝ) : ℂ))⁻¹ := by
      push_cast
      rw [map_inv₀, map_mul, Complex.conj_I, Complex.conj_ofReal]
      congr 1; ring
    rw [hconj]
  exact tendsto_nhds_unique (hgx.congr' key) hgy'

/-! ### Domain invariance (and the commutation `A ∘ U s = U s ∘ A`) -/

/-- The group preserves the domain of its generator, and `A (U s ψ) = U s (A ψ)`.
This is the clean structural identity that the resolvent argument downstream relies on. -/
lemma generator_domain_invariant (U : OneParameterUnitaryGroup (H := H))
    (s : ℝ) (x : (generator U).domain) :
    U.U s (x : H) ∈ (generator U).domain := by
  refine ⟨U.U s (generator U x), ?_⟩
  have hpt : genDiffQuot U (U.U s (x : H)) = fun t => U.U s (genDiffQuot U (x : H) t) := by
    funext t
    simp only [genDiffQuot_apply, map_smul]
    congr 1
    rw [map_sub]
    have hcomm : U.U t (U.U s (x : H)) = U.U s (U.U t (x : H)) := by
      have h1 : U.U t (U.U s (x : H)) = U.U (t + s) (x : H) := by
        rw [← ContinuousLinearMap.comp_apply, ← U.group_law]
      have h2 : U.U s (U.U t (x : H)) = U.U (s + t) (x : H) := by
        rw [← ContinuousLinearMap.comp_apply, ← U.group_law]
      rw [h1, h2, add_comm]
    rw [hcomm]
  rw [hpt]
  exact ((U.U s).continuous.tendsto _).comp (generator_tendsto U x)

/-- von Neumann's criterion (absent from Mathlib 4.31): a symmetric operator whose
`A + iI` and `A − iI` are surjective is self-adjoint. -/
lemma isSelfAdjoint_of_surjective_addSub
    (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H))
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) :
    IsSelfAdjoint A := by
  rw [LinearPMap.isSelfAdjoint_def]
  refine le_antisymm ?_ (hsym.le_adjoint hdense)        -- ← feed density here
  -- ⊢ A† ≤ A.  First: ker(A† − iI) = 0, using surjectivity of A + iI.
  have hker : ∀ w : (A.adjoint).domain, A.adjoint w = I • (w : H) → (w : H) = 0 := by
    intro w hw
    obtain ⟨v, hv⟩ := hplus (w : H)                -- hv : A v + I•(v:H) = (w:H)
    have hadj : ⟪A.adjoint w, (v : H)⟫_ℂ = ⟪(w : H), A v⟫_ℂ :=
      LinearPMap.adjoint_isFormalAdjoint hdense w v      -- ← was (T := A) w v
    rw [hw, inner_smul_left, Complex.conj_I] at hadj   -- hadj : -I * ⟪w,v⟫ = ⟪w, A v⟫
    have key : ⟪(w : H), A v⟫_ℂ + I * ⟪(w : H), (v : H)⟫_ℂ = ⟪(w : H), (w : H)⟫_ℂ := by
      rw [← inner_smul_right, ← inner_add_right, hv]
    have hww : ⟪(w : H), (w : H)⟫_ℂ = 0 := by rw [← key, ← hadj]; ring
    exact inner_self_eq_zero.mp hww
  -- Now A† ≤ A via eqLocus.
  apply LinearPMap.le_of_eqLocus_ge
  intro w hw                                        -- hw : w ∈ (A.adjoint).domain
  set W : (A.adjoint).domain := ⟨w, hw⟩ with hWdef
  obtain ⟨x, hx⟩ := hminus (A.adjoint W - I • (W : H))   -- hx : A x - I•(x:H) = A† W - I•(W:H)
  have hxin : (x : H) ∈ (A.adjoint).domain := (hsym.le_adjoint hdense).1 x.2
  have hxeq : A.adjoint (⟨(x : H), hxin⟩ : (A.adjoint).domain) = A x :=
    ((hsym.le_adjoint hdense).2 (x := x) (y := ⟨(x : H), hxin⟩) rfl).symm
  set W' : (A.adjoint).domain := W - ⟨(x : H), hxin⟩ with hW'def
  have hW'val : (W' : H) = (W : H) - (x : H) := rfl
  have hrearr : A.adjoint W - A x = I • (W : H) - I • (x : H) := by
    have h2 : A.adjoint W = A x - I • (x : H) + I • (W : H) := by rw [hx]; abel
    rw [h2]; abel
  have hAW' : A.adjoint W' = I • (W' : H) := by
    have e1 : A.adjoint W' = A.adjoint W - A x := by
      rw [hW'def, LinearPMap.map_sub, hxeq]
    rw [e1, hrearr, hW'val, smul_sub]
  have hWx : (W : H) = (x : H) := sub_eq_zero.mp (hW'val ▸ hker W' hAW')
  have hwx : w = (x : H) := by
    have hWcoe : (W : H) = w := by rw [hWdef]
    rw [← hWcoe]; exact hWx
  subst hwx
  exact ⟨hw, x.2, hxeq⟩

/-! ### The time-reversed group -/

/-- The time-reversed group `U'(t) = U(-t)`. It is again a one-parameter unitary group, with
generator `-A`; this lets `A - iI` results be read off from the `A + iI` results. -/
def reversedGroup (U : OneParameterUnitaryGroup (H := H)) : OneParameterUnitaryGroup (H := H) where
  U t := U.U (-t)
  unitary t ψ φ := U.unitary (-t) ψ φ
  group_law s t := by rw [show -(s + t) = -s + -t by ring]; exact U.group_law (-s) (-t)
  identity := by simp [U.identity]
  strong_continuous ψ := (U.strong_continuous ψ).comp continuous_neg

@[simp] lemma reversedGroup_apply (U : OneParameterUnitaryGroup (H := H)) (t : ℝ) :
    (reversedGroup U).U t = U.U (-t) := rfl

/-- The reversed group's difference quotient is the negated, time-reversed original:
`genDiffQuot (reversedGroup U) ψ t = - genDiffQuot U ψ (-t)`. -/
lemma genDiffQuot_reversedGroup (U : OneParameterUnitaryGroup (H := H)) (ψ : H) (t : ℝ) :
    genDiffQuot (reversedGroup U) ψ t = - genDiffQuot U ψ (-t) := by
  simp only [genDiffQuot_apply, reversedGroup_apply]
  rw [Complex.ofReal_neg, mul_neg, inv_neg, neg_smul, neg_neg]

end OneParameterUnitaryGroup
end Spectra
