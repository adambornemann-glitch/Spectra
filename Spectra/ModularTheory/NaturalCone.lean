/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: NaturalCone.lean
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Spectra.ModularTheory.Cocycle
import Spectra.ModularTheory.RelativeModular
import Spectra.ModularTheory.TomitaTakesaki

open Spectra.QuantumMechanics.ModularTheory
namespace Spectra.ModularTheory
namespace Cone

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The dual of a cone under the real part of the inner product. -/
def coneDual (P : Set H) : Set H :=
  { ξ : H | ∀ η ∈ P, 0 ≤ (@inner ℂ H _ ξ η).re }

/-- Self-duality. -/
def IsSelfDual (P : Set H) : Prop := coneDual P = P


omit [CompleteSpace H] in
/-- The dual cone is convex. -/
lemma coneDual_isConvex (P : Set H) : Convex ℝ (coneDual P) := by
  intro ξ₁ hξ₁ ξ₂ hξ₂ a b ha hb _ η hη
  have h1 := hξ₁ η hη
  have h2 := hξ₂ η hη
  show 0 ≤ (@inner ℂ H _ (a • ξ₁ + b • ξ₂) η).re
  change 0 ≤ (@inner ℂ H _ ((↑a : ℂ) • ξ₁ + (↑b : ℂ) • ξ₂) η).re
  rw [inner_add_left, inner_smul_left, inner_smul_left, Complex.add_re]
  simp only [starRingEnd_apply, Complex.mul_re]
  simp only [RCLike.star_def, Complex.conj_ofReal, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  exact add_nonneg (mul_nonneg ha h1) (mul_nonneg hb h2)

omit [CompleteSpace H] in
/-- The dual cone is a cone. -/
lemma coneDual_isCone (P : Set H) :
    ∀ ξ ∈ coneDual P, ∀ r : ℝ, 0 ≤ r → r • ξ ∈ coneDual P := by
  intro ξ hξ r hr η hη
  have h := hξ η hη
  show 0 ≤ (@inner ℂ H _ (r • ξ) η).re
  change 0 ≤ (@inner ℂ H _ ((↑r : ℂ) • ξ) η).re
  rw [inner_smul_left]
  simp only [starRingEnd_apply, Complex.mul_re]
  simp only [RCLike.star_def, Complex.conj_ofReal, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg hr h

omit [CompleteSpace H] in
/-- The dual cone is closed. -/
lemma coneDual_isClosed (P : Set H) : IsClosed (coneDual P) := by
  have : coneDual P = ⋂ (η : ↥P), { ξ : H | 0 ≤ (@inner ℂ H _ ξ (η : H)).re } := by
    ext ξ; simp only [coneDual, Set.mem_iInter, Set.mem_setOf_eq, Subtype.forall]
  rw [this]
  apply isClosed_iInter; intro ⟨η, _⟩
  exact isClosed_le continuous_const
    (Complex.continuous_re.comp (continuous_id.inner continuous_const))

omit [CompleteSpace H] in
/-- The zero vector is in the dual cone of any set. -/
lemma zero_mem_coneDual (P : Set H) : (0 : H) ∈ coneDual P := by
  intro η _
  simp [inner_zero_left]

omit [CompleteSpace H] in
/-- Every set is contained in its double dual. -/
lemma subset_coneDual_coneDual (A : Set H) : A ⊆ coneDual (coneDual A) := by
  intro ξ hξ η hη
  have h := hη ξ hξ  -- 0 ≤ Re⟨η, ξ⟩
  have : (@inner ℂ H _ ξ η).re = (@inner ℂ H _ η ξ).re := by
    conv_lhs => rw [← inner_conj_symm]
    exact Complex.conj_re (inner ℂ η ξ)
  linarith

omit [CompleteSpace H] in
/-- Duality is anti-monotone: A ⊆ B ⟹ B* ⊆ A*. -/
lemma coneDual_antimono {A B : Set H} (h : A ⊆ B) : coneDual B ⊆ coneDual A := by
  intro ξ hξ η hη
  exact hξ η (h hη)

omit [CompleteSpace H] in
/-- Two self-dual cones that contain each other are equal — and in fact two
    self-dual cones, one contained in the other, are already equal. -/
lemma selfDual_rigidity {A B : Set H}
    (hA : IsSelfDual A) (hB : IsSelfDual B) (hAB : A ⊆ B) : A = B := by
  -- A ⊆ B  ⟹  B* ⊆ A*  ⟹  B ⊆ A   (using B = B* and A = A*)
  have h1 : coneDual B ⊆ coneDual A := coneDual_antimono hAB
  rw [hA, hB] at h1
  exact Set.Subset.antisymm hAB h1


/-!
## §1: The natural cone P♮

Everything below is rebuilt on the new modular API: the pair
`(ModularOperatorData, ModularConjugationData)` is replaced by the single
`ModularData` (flow `t ↦ Δ^{it}` as a `OneParameterUnitaryGroup`, conjugation
`J` as a `Conjugation`).  `J.toFun` becomes the `FunLike` coercion, the old
`antiunitary` field is `Conjugation.inner_map`, and `JΩ = Ω` is
`md.J_fixes_vacuum`.

The cone itself only depends on `(M, J)`, so the *definitions* take a bare
`Conjugation H`; the modular data enters through the Araki properties (A3, A4)
and the vacuum-fixing facts.
-/

open scoped InnerProductSpace
open Spectra.QuantumMechanics.SpectralTheory

/-- The generating orbit of the natural cone: `{a(J(aΩ)) : a ∈ M}`. -/
def algebraJOrbit (M : VNAlgebraWithVector H) (J : Conjugation H) : Set H :=
  { ξ | ∃ a : H →L[ℂ] H, a ∈ M.algebra ∧ ξ = a (J (a M.Ω)) }

/-- The natural positive cone P♮, the closed convex hull of the orbit. -/
def naturalCone (M : VNAlgebraWithVector H) (J : Conjugation H) : Set H :=
  closure (convexHull ℝ (algebraJOrbit M J))

/-- Araki's conditions, applied to a candidate cone over the modular data
`(Δ^{it}, J)` of `(M, Ω)`. -/
structure NaturalConePropertiesData (M : VNAlgebraWithVector H)
    (md : ModularData H M) (P : Set H) : Prop where
  /-- (A1) Closed... -/
  isClosed       : IsClosed P
  /-- ...convex... -/
  isConvex       : Convex ℝ P
  /-- ...cone. -/
  isCone         : ∀ ξ ∈ P, ∀ r : ℝ, 0 ≤ r → r • ξ ∈ P
  /-- (A2) Self-dual. -/
  selfDual       : IsSelfDual P
  /-- (A3) Pointwise J-fixed. -/
  J_fixed        : ∀ ξ ∈ P, md.J ξ = ξ
  /-- (A4) Modular-invariant: `Δ^{it} P = P`. -/
  Δ_invariant    : ∀ t : ℝ, ∀ ξ ∈ P, modularUnitary md t ξ ∈ P
  /-- (A5) Contains the generating orbit. -/
  contains_orbit : algebraJOrbit M md.J ⊆ P

/-- The natural cone is closed (it is defined as a closure). -/
lemma naturalCone_isClosed (M : VNAlgebraWithVector H) (J : Conjugation H) :
    IsClosed (naturalCone M J) :=
  isClosed_closure

/-- The natural cone is convex (closure of a convex hull is convex). -/
lemma naturalCone_isConvex (M : VNAlgebraWithVector H) (J : Conjugation H) :
    Convex ℝ (naturalCone M J) :=
  (convex_convexHull ℝ _).closure

/-- The zero vector is in the generating orbit (witness: `a = 0`). -/
lemma zero_mem_algebraJOrbit (M : VNAlgebraWithVector H) (J : Conjugation H) :
    (0 : H) ∈ algebraJOrbit M J :=
  ⟨0, M.algebra.zero_mem, by simp⟩

/-- The zero vector is in the natural cone. -/
lemma zero_mem_naturalCone (M : VNAlgebraWithVector H) (J : Conjugation H) :
    (0 : H) ∈ naturalCone M J :=
  subset_closure (subset_convexHull ℝ _ (zero_mem_algebraJOrbit M J))

/-- Ω is in the generating orbit (witness: `a = 1`, using `JΩ = Ω`). -/
lemma omega_mem_algebraJOrbit (M : VNAlgebraWithVector H) (md : ModularData H M) :
    M.Ω ∈ algebraJOrbit M md.J :=
  ⟨1, M.algebra.one_mem, by simp [md.J_fixes_vacuum]⟩

/-- Ω is in the natural cone. -/
lemma omega_mem_naturalCone (M : VNAlgebraWithVector H) (md : ModularData H M) :
    M.Ω ∈ naturalCone M md.J :=
  subset_closure (subset_convexHull ℝ _ (omega_mem_algebraJOrbit M md))

omit [CompleteSpace H] in
/-- Inner products of J-fixed vectors are real: `⟪ξ, η⟫ = ⟪Jξ, Jη⟫ = ⟪η, ξ⟫ = conj ⟪ξ, η⟫`. -/
lemma inner_real_of_J_fixed {J : Conjugation H} {ξ η : H}
    (hξ : J ξ = ξ) (hη : J η = η) :
    (⟪ξ, η⟫_ℂ).im = 0 := by
  have h1 : ⟪J ξ, J η⟫_ℂ = ⟪η, ξ⟫_ℂ := J.inner_map ξ η
  rw [hξ, hη] at h1
  have h2 : ⟪η, ξ⟫_ℂ = (starRingEnd ℂ) ⟪ξ, η⟫_ℂ := (inner_conj_symm η ξ).symm
  rw [h2] at h1
  exact Complex.conj_eq_iff_im.mp h1.symm

/-- **Existence half of Araki's theorem (bundled hypothesis).**

The natural cone `naturalCone M md.J = closure (convexHull ℝ {aJaΩ})` satisfies
the Araki properties.  The substantive content is self-duality, which needs the
polar decomposition `S = JΔ^{1/2}` — the same milestone that constructs
`ModularData` itself.  Once that lands, this becomes a theorem. -/
abbrev NaturalConeExistence (M : VNAlgebraWithVector H) (md : ModularData H M) : Prop :=
  NaturalConePropertiesData M md (naturalCone M md.J)

/-- **Araki's uniqueness theorem.**  Any two cones satisfying the Araki
conditions are equal — given the existence half.  The proof is pure cone
duality: the natural cone sits inside any candidate (A1 + A5 + minimality of
the closed convex hull), and two nested self-dual cones coincide
(`selfDual_rigidity`). -/
theorem natural_cone_unique (M : VNAlgebraWithVector H) (md : ModularData H M)
    (hExist : NaturalConeExistence M md)
    {P₁ P₂ : Set H}
    (h₁ : NaturalConePropertiesData M md P₁)
    (h₂ : NaturalConePropertiesData M md P₂) :
    P₁ = P₂ := by
  -- Step 1: the natural cone is contained in any candidate.
  have h_nat_sub : ∀ {P : Set H}, NaturalConePropertiesData M md P →
      naturalCone M md.J ⊆ P := by
    intro P hP
    have h_conv : convexHull ℝ (algebraJOrbit M md.J) ⊆ P :=
      convexHull_min hP.contains_orbit hP.isConvex
    exact closure_minimal h_conv hP.isClosed
  -- Step 2: apply rigidity twice.
  have eq₁ : naturalCone M md.J = P₁ :=
    selfDual_rigidity hExist.selfDual h₁.selfDual (h_nat_sub h₁)
  have eq₂ : naturalCone M md.J = P₂ :=
    selfDual_rigidity hExist.selfDual h₂.selfDual (h_nat_sub h₂)
  rw [← eq₁, eq₂]

/-!
## §2: Vector representatives (the φ map)
-/

/-- A vector ξ **implements the state** of Ω' on M:
`⟪ξ, aξ⟫ = ⟪Ω', aΩ'⟫` for all `a ∈ M`. -/
def ImplementsState (M : VNAlgebraWithVector H) (ξ Ω' : H) : Prop :=
  ∀ a ∈ M.algebra, ⟪ξ, a ξ⟫_ℂ = ⟪Ω', a Ω'⟫_ℂ

/-- `ImplementsState` is reflexive: any vector implements its own state. -/
lemma implementsState_self (M : VNAlgebraWithVector H) :
    ImplementsState M M.Ω M.Ω :=
  fun _ _ => rfl

/-- **Araki's vector representative theorem** (bundled as hypothesis).

Every faithful normal state on `M` — packaged as a `TwoStateData` on the same
algebra — has a unique representative in P♮ implementing it.  The construction
is `ξ = Δ_{ψ,φ}^{1/4}Ω_φ`, needing the unbounded calculus for real fractional
powers of the relative modular operator; once that lands, this becomes a
theorem. -/
structure VectorRepresentativeData (D : TwoStateData H)
    (md : ModularData H D.φ) where
  /-- The representative vector. -/
  repr : H
  /-- The representative is in the natural cone. -/
  mem_cone : repr ∈ naturalCone D.φ md.J
  /-- The representative implements the target state. -/
  implements : ImplementsState D.φ repr D.ψ.Ω
  /-- Uniqueness: the only vector in P♮ implementing ψ. -/
  unique : ∀ η ∈ naturalCone D.φ md.J, ImplementsState D.φ η D.ψ.Ω → η = repr

namespace VectorRepresentativeData

variable {D : TwoStateData H} {md : ModularData H D.φ}

/-- The representative has the same norm as the target vector
(evaluate `implements` at `a = 1`). -/
lemma repr_norm (V : VectorRepresentativeData D md) :
    ‖V.repr‖ = ‖D.ψ.Ω‖ := by
  have h := V.implements 1 D.φ.algebra.one_mem
  simp only [ContinuousLinearMap.one_apply] at h
  have h_sq : ‖V.repr‖ ^ 2 = ‖D.ψ.Ω‖ ^ 2 := by
    have h2 := congrArg Complex.re h
    simp only [inner_self_eq_norm_sq_to_K] at h2
    exact_mod_cast h2
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : 2 ≠ 0)).mp h_sq

/-- The representative is normalized. -/
lemma repr_norm_one (V : VectorRepresentativeData D md) :
    ‖V.repr‖ = 1 := by
  rw [V.repr_norm, D.ψ.Ω_norm]

/-- The representative is nonzero. -/
lemma repr_ne_zero (V : VectorRepresentativeData D md) :
    V.repr ≠ 0 :=
  norm_ne_zero_iff.mp (V.repr_norm_one ▸ one_ne_zero)

/-- The representative is J-fixed (Araki property A3). -/
lemma repr_J_fixed (hExist : NaturalConeExistence D.φ md)
    (V : VectorRepresentativeData D md) :
    md.J V.repr = V.repr :=
  hExist.J_fixed V.repr V.mem_cone

end VectorRepresentativeData

/-!
## §3: Geometry of P♮ from the Araki properties
-/

/-- Inner products between natural cone elements are real (from A3). -/
lemma inner_real_of_mem_naturalCone
    {M : VNAlgebraWithVector H} {md : ModularData H M}
    (hExist : NaturalConeExistence M md)
    {ξ η : H} (hξ : ξ ∈ naturalCone M md.J) (hη : η ∈ naturalCone M md.J) :
    (⟪ξ, η⟫_ℂ).im = 0 :=
  inner_real_of_J_fixed (hExist.J_fixed ξ hξ) (hExist.J_fixed η hη)

/-- Inner products between natural cone elements have non-negative real part —
the content of self-duality `P♮ = (P♮)*` (from A2). -/
lemma inner_nonneg_of_mem_naturalCone
    {M : VNAlgebraWithVector H} {md : ModularData H M}
    (hExist : NaturalConeExistence M md)
    {ξ η : H} (hξ : ξ ∈ naturalCone M md.J) (hη : η ∈ naturalCone M md.J) :
    0 ≤ (⟪ξ, η⟫_ℂ).re := by
  have h : ξ ∈ coneDual (naturalCone M md.J) := by rw [hExist.selfDual]; exact hξ
  exact h η hη

/-- A representative has non-negative inner product with any cone element. -/
lemma VectorRepresentativeData.inner_repr_nonneg
    {D : TwoStateData H} {md : ModularData H D.φ}
    (hExist : NaturalConeExistence D.φ md)
    (V : VectorRepresentativeData D md)
    {η : H} (hη : η ∈ naturalCone D.φ md.J) :
    0 ≤ (⟪V.repr, η⟫_ℂ).re :=
  inner_nonneg_of_mem_naturalCone hExist V.mem_cone hη

/-- **P♮ is pointed**: if ξ and −ξ are both in the natural cone, ξ = 0.
Foundation for the partial order on H induced by P♮. -/
lemma naturalCone_pointed
    {M : VNAlgebraWithVector H} {md : ModularData H M}
    (hExist : NaturalConeExistence M md)
    {ξ : H} (hξ : ξ ∈ naturalCone M md.J) (hξ_neg : -ξ ∈ naturalCone M md.J) :
    ξ = 0 := by
  -- Step 1: self-duality gives 0 ≤ Re⟪ξ, −ξ⟫, i.e. Re⟪ξ, ξ⟫ ≤ 0.
  have h_dual : ξ ∈ coneDual (naturalCone M md.J) := by
    rw [hExist.selfDual]; exact hξ
  have h := h_dual (-ξ) hξ_neg
  rw [inner_neg_right, Complex.neg_re] at h
  -- Step 2: but Re⟪ξ, ξ⟫ = ‖ξ‖² ≥ 0 always, so it vanishes.
  have h_self : 0 ≤ (⟪ξ, ξ⟫_ℂ).re :=
    inner_nonneg_of_mem_naturalCone hExist hξ hξ
  have h_zero : (⟪ξ, ξ⟫_ℂ).re = 0 := le_antisymm (by linarith) h_self
  -- Step 3: ‖ξ‖² = 0 forces ξ = 0.
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)] at h_zero
  norm_cast at h_zero
  exact norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp h_zero)

/-- P♮ is closed under addition (convexity + cone scaling). -/
lemma naturalCone_add
    {M : VNAlgebraWithVector H} {md : ModularData H M}
    (hExist : NaturalConeExistence M md)
    {ξ η : H} (hξ : ξ ∈ naturalCone M md.J) (hη : η ∈ naturalCone M md.J) :
    ξ + η ∈ naturalCone M md.J := by
  have h_mid : (1/2 : ℝ) • ξ + (1/2 : ℝ) • η ∈ naturalCone M md.J :=
    hExist.isConvex hξ hη (by norm_num) (by norm_num) (by norm_num)
  have h_scale := hExist.isCone _ h_mid 2 (by norm_num)
  convert h_scale using 1
  rw [smul_add, smul_smul, smul_smul]
  norm_num

/-!
## §4: The cone order

`ξ ≤ η ⟺ η − ξ ∈ P♮`.  Reflexivity is free; antisymmetry is pointedness;
transitivity is closure under addition.  (A genuine `PartialOrder` instance is
deliberately not declared: the order depends on `(M, J)`, so an instance on `H`
would be incoherent.)
-/

/-- The cone order: `ξ ≤ η ⟺ η − ξ ∈ P♮`. -/
def coneLE (M : VNAlgebraWithVector H) (J : Conjugation H) (ξ η : H) : Prop :=
  η - ξ ∈ naturalCone M J

/-- The cone order is reflexive. -/
lemma coneLE_refl (M : VNAlgebraWithVector H) (J : Conjugation H) (ξ : H) :
    coneLE M J ξ ξ := by
  show ξ - ξ ∈ naturalCone M J
  rw [sub_self]
  exact zero_mem_naturalCone M J

/-- The cone order is antisymmetric (from pointedness). -/
lemma coneLE_antisymm
    {M : VNAlgebraWithVector H} {md : ModularData H M}
    (hExist : NaturalConeExistence M md)
    {ξ η : H} (h₁ : coneLE M md.J ξ η) (h₂ : coneLE M md.J η ξ) :
    ξ = η := by
  have h : η - ξ = 0 := by
    apply naturalCone_pointed hExist h₁
    rw [neg_sub]
    exact h₂
  exact (sub_eq_zero.mp h).symm

/-- The cone order is transitive (from closure under addition). -/
lemma coneLE_trans
    {M : VNAlgebraWithVector H} {md : ModularData H M}
    (hExist : NaturalConeExistence M md)
    {ξ η ζ : H} (h₁ : coneLE M md.J ξ η) (h₂ : coneLE M md.J η ζ) :
    coneLE M md.J ξ ζ := by
  show ζ - ξ ∈ naturalCone M md.J
  rw [show ζ - ξ = (ζ - η) + (η - ξ) from by abel]
  exact naturalCone_add hExist h₂ h₁

end Spectra.ModularTheory.Cone
