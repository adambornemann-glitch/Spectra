/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Module.LinearMap.Star
import Spectra.YosidaHille.Basic
/-!
# Antiunitary conjugations

A `Conjugation` on a complex Hilbert space is an antiunitary involution `J`:
a conjugate-linear map with `J² = 1` and `⟪Jψ, Jφ⟫ = ⟪φ, ψ⟫`.  This is the bounded prototype
for all the antilinear machinery downstream (time reversal now; the Tomita conjugation of
`Δ^{1/2}` later).

Design notes:

* The carrier is `H →ₗ⋆[ℂ] H` (= `LinearMap (starRingEnd ℂ) H H`,
  `Mathlib/Algebra/Module/LinearMap/Star.lean:21`).  Continuity is *derived* (isometry from
  `inner_map`), not assumed — same economy as the project's `Unitary`.
* For the unbounded antilinear story: `LinearPMap` is now semilinear
  (`H →ₛₗ.[starRingEnd ℂ] H` typechecks on master), but `IsClosable`/`closure`/`adjoint` are
  still `RingHom.id`-only; see AUDIT.md §1.4 for the upstream plan.
* **Coordination**: `Mathlib/Analysis/InnerProductSpace/StandardSubspace.lean` (Yoh Tanimoto,
  2026) has standard subspaces with the Tomita conjugation as an explicit TODO.  Check Zulip
  before extending this file past time reversal (AUDIT.md §1.5).

Sorry count: 0.
-/
open Complex Filter Topology
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
open Spectra.OneParameterUnitaryGroup
namespace Spectra.QuantumMechanics.SpectralTheory


/-- An antiunitary involution on a complex inner-product space: conjugate-linear, squares to the
identity, and conjugates the inner product. -/
structure Conjugation (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The underlying conjugate-linear map. -/
  toLinearMap : H →ₗ⋆[ℂ] H
  /-- `J` is an involution. -/
  involutive : ∀ ψ, toLinearMap (toLinearMap ψ) = ψ
  /-- `J` conjugates the inner product: `⟪Jψ, Jφ⟫ = ⟪φ, ψ⟫`. -/
  inner_map : ∀ ψ φ, ⟪toLinearMap ψ, toLinearMap φ⟫_ℂ = ⟪φ, ψ⟫_ℂ

namespace Conjugation

instance : FunLike (Conjugation H) H H where
  coe J := J.toLinearMap
  coe_injective' := by
    rintro ⟨J, _, _⟩ ⟨K, _, _⟩ h
    simpa using LinearMap.ext (congrFun h)

@[simp] lemma coe_toLinearMap (J : Conjugation H) : ⇑J.toLinearMap = ⇑J := rfl

@[simp] lemma apply_apply (J : Conjugation H) (ψ : H) : J (J ψ) = ψ := J.involutive ψ

lemma map_add (J : Conjugation H) (ψ φ : H) : J (ψ + φ) = J ψ + J φ :=
  J.toLinearMap.map_add ψ φ

lemma map_smul (J : Conjugation H) (c : ℂ) (ψ : H) :
    J (c • ψ) = (starRingEnd ℂ c) • J ψ :=
  J.toLinearMap.map_smulₛₗ c ψ

lemma map_sub (J : Conjugation H) (ψ φ : H) : J (ψ - φ) = J ψ - J φ :=
  J.toLinearMap.map_sub ψ φ

@[simp] lemma map_zero (J : Conjugation H) : J (0 : H) = 0 :=
  J.toLinearMap.map_zero

/-- Antiunitarity forces isometry. -/
@[simp] lemma norm_map (J : Conjugation H) (ψ : H) : ‖J ψ‖ = ‖ψ‖ := by
  have h := J.inner_map ψ ψ
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖J ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by exact_mod_cast h
  nlinarith [norm_nonneg (J ψ), norm_nonneg ψ]

lemma isometry (J : Conjugation H) : Isometry (⇑J) :=
  AddMonoidHomClass.isometry_of_norm J.toLinearMap.toAddMonoidHom
    fun ψ => J.norm_map ψ |>.symm ▸ rfl

lemma continuous (J : Conjugation H) : Continuous (⇑J) := J.isometry.continuous

lemma injective (J : Conjugation H) : Function.Injective (⇑J) :=
  Function.LeftInverse.injective J.involutive

lemma surjective (J : Conjugation H) : Function.Surjective (⇑J) :=
  Function.RightInverse.surjective J.involutive

lemma bijective (J : Conjugation H) : Function.Bijective (⇑J) :=
  ⟨J.injective, J.surjective⟩

end Conjugation

/-! ## Time reversal: the stress test

The first physically meaningful conjugation.  `J` is a time reversal for the group `U` when it
intertwines `U(t)` with `U(-t)`; the payoff theorem is that `J` then *commutes* with the
generator `A` (the two minus signs — from `t ↦ -t` and from antilinearity acting on `i` —
cancel).  This is the dress rehearsal for `JΔJ = Δ⁻¹` in Tomita–Takesaki: if these statements
are awkward here, the abstractions are wrong and should be fixed before the modular theory. -/

variable [CompleteSpace H]


/-- `J` reverses time for `U` when `J U(t) = U(-t) J`. -/
def IsTimeReversal (J : Conjugation H) (U_grp : OneParameterUnitaryGroup (H := H)) : Prop :=
  ∀ (t : ℝ) (ψ : H), J (U_grp.U t ψ) = U_grp.U (-t) (J ψ)

namespace IsTimeReversal

variable {J : Conjugation H} {U_grp : OneParameterUnitaryGroup (H := H)}

/-- **The two-minus-signs computation, pointwise**: for a time reversal `J`, the difference
quotient of `J ψ` at `t` is `J` of the difference quotient of `ψ` at `-t` — the sign from
`t ↦ -t` cancels against the sign from antilinearity acting on the coefficient `(it)⁻¹`. -/
lemma genDiffQuot_comm (hJ : IsTimeReversal J U_grp) (ψ : H) (t : ℝ) :
    genDiffQuot U_grp (J ψ) t = J (genDiffQuot U_grp ψ (-t)) := by
  have hU : U_grp.U t (J ψ) = J (U_grp.U (-t) ψ) := by
    rw [hJ (-t) ψ, neg_neg]
  have hc : (starRingEnd ℂ) ((I * ((-t : ℝ) : ℂ))⁻¹) = (I * (t : ℂ))⁻¹ := by
    rw [Complex.ofReal_neg, map_inv₀, map_mul, Complex.conj_I, map_neg, Complex.conj_ofReal]
    congr 1
    ring
  simp only [genDiffQuot_apply]
  rw [hU, ← Conjugation.map_sub, Conjugation.map_smul, hc]

/-- Limit transport: the difference quotients of `J ψ` converge to `J (A ψ)`.  Both payoff
theorems below are immediate consequences (existence of the limit, and its identification). -/
lemma tendsto_genDiffQuot_comm (hJ : IsTimeReversal J U_grp) {ψ : H}
    (hψ : ψ ∈ generatorDomain U_grp) :
    Tendsto (genDiffQuot U_grp (J ψ)) (𝓝[≠] 0) (𝓝 (J (generator U_grp ⟨ψ, hψ⟩))) := by
  -- negation preserves the punctured neighbourhood of 0 (as in `generator_isFormalAdjoint`)
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  have hbase : Tendsto (fun t : ℝ => genDiffQuot U_grp ψ (-t)) (𝓝[≠] (0 : ℝ))
      (𝓝 (generator U_grp ⟨ψ, hψ⟩)) :=
    (generator_tendsto U_grp ⟨ψ, hψ⟩).comp hneg
  have hJlim : Tendsto (fun t : ℝ => J (genDiffQuot U_grp ψ (-t))) (𝓝[≠] (0 : ℝ))
      (𝓝 (J (generator U_grp ⟨ψ, hψ⟩))) :=
    (J.continuous.tendsto _).comp hbase
  exact hJlim.congr fun t => (hJ.genDiffQuot_comm ψ t).symm

/-- Time reversal preserves the generator's domain: the difference quotients of `J ψ`
converge (to `J (A ψ)`), by `tendsto_genDiffQuot_comm`. -/
lemma generator_mem_domain (hJ : IsTimeReversal J U_grp) {ψ : H}
    (hψ : ψ ∈ generatorDomain U_grp) :
    J ψ ∈ generatorDomain U_grp :=
  mem_generatorDomain.mpr
    ⟨J (generator U_grp ⟨ψ, hψ⟩), hJ.tendsto_genDiffQuot_comm hψ⟩

/-- **Time reversal commutes with the generator**: `A (Jψ) = J (A ψ)` on the domain.
The difference quotients of `J ψ` tend to `A (Jψ)` by definition of the generator and to
`J (A ψ)` by `tendsto_genDiffQuot_comm`; conclude by uniqueness of limits. -/
lemma generator_comm (hJ : IsTimeReversal J U_grp) {ψ : H}
    (hψ : ψ ∈ generatorDomain U_grp) :
    generator U_grp ⟨J ψ, hJ.generator_mem_domain hψ⟩
      = J (generator U_grp ⟨ψ, hψ⟩) :=
  tendsto_nhds_unique
    (generator_tendsto U_grp ⟨J ψ, hJ.generator_mem_domain hψ⟩)
    (hJ.tendsto_genDiffQuot_comm hψ)

end IsTimeReversal


end Spectra.QuantumMechanics.SpectralTheory
