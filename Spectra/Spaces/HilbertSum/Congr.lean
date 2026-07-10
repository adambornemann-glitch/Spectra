/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Componentwise congruence of `lp` spaces

A family of linear isometry equivalences `e i : E i ≃ₗᵢ[𝕜] F i` acts diagonally on the
corresponding `lp` spaces by `f ↦ fun i => e i (f i)`. Each component preserves norms, so the
diagonal map preserves membership in `lp` and the `lp` norm for **every** exponent `p : ℝ≥0∞`,
and — once `1 ≤ p`, so that Mathlib equips `lp` with its normed group structure — assembles
into a linear isometry equivalence `lp E p ≃ₗᵢ[𝕜] lp F p`.

Mathlib has no componentwise congruence API for `lp`, so this file is a Mathlib-upstream
candidate and lives in the root namespace, mirroring `LinearIsometry.completionMap` in
`Spectra/Spaces/Tensor/Hilbert.lean`.

## Main definitions

* `LinearIsometryEquiv.lpCongrRight` — the diagonal linear isometry equivalence
  `lp E p ≃ₗᵢ[𝕜] lp F p` (for `Fact (1 ≤ p)`) induced by componentwise linear isometry
  equivalences.

## Main results

* `memℓp_congr_norm` — families with equal pointwise norms are simultaneously in `ℓᵖ`.
* `lp.norm_congr` — `lp` elements with equal pointwise norms have equal `lp` norms.
* `memℓp_congrRight_iff` — `Memℓp (fun i => e i (f i)) p ↔ Memℓp f p`.
* `LinearIsometryEquiv.lpCongrRight_apply`, `lpCongrRight_symm`, `lpCongrRight_refl`,
  `lpCongrRight_trans` — the expected coherence lemmas.

## Notes

For `p = 2` the congruence is a unitary between Hilbert spaces; preservation of the inner
product needs no bespoke lemma because it is Mathlib's generic
`LinearIsometryEquiv.inner_map_map` (a sanity `example` at the bottom records this).

The scalars are only required to form a `NormedRing` acting boundedly on each component —
the same generality in which Mathlib equips `lp` with its module structure.
-/

noncomputable section

open scoped ENNReal

variable {ι 𝕜 : Type*} {E F G : ι → Type*} {p : ℝ≥0∞}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedAddCommGroup (F i)]
  [∀ i, NormedAddCommGroup (G i)]

/-! ## Norm congruence for `Memℓp` and the `lp` norm -/

/-- Two families (over possibly different fibers) with equal pointwise norms are
simultaneously in `ℓᵖ`. -/
theorem memℓp_congr_norm {f : ∀ i, E i} {g : ∀ i, F i} (h : ∀ i, ‖f i‖ = ‖g i‖) :
    Memℓp f p ↔ Memℓp g p :=
  ⟨fun hf => hf.mono' fun i => (h i).ge, fun hg => hg.mono' fun i => (h i).le⟩

/-- Two `lp` elements (over possibly different fibers) with equal pointwise norms have equal
`lp` norms, for every exponent `p : ℝ≥0∞`. -/
theorem lp.norm_congr {x : lp E p} {y : lp F p} (h : ∀ i, ‖x i‖ = ‖y i‖) : ‖x‖ = ‖y‖ := by
  rcases eq_or_ne p 0 with rfl | hp
  · have hmem : ∀ i, x i ≠ 0 ↔ y i ≠ 0 := fun i => by
      rw [← norm_pos_iff, ← norm_pos_iff, h i]
    have hfin : (lp.memℓp x).finite_dsupport.toFinset =
        (lp.memℓp y).finite_dsupport.toFinset :=
      Finset.ext fun i => by
        simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
        exact hmem i
    rw [lp.norm_eq_card_dsupport, lp.norm_eq_card_dsupport, hfin]
  · exact le_antisymm (lp.norm_mono hp fun i => (h i).le) (lp.norm_mono hp fun i => (h i).ge)

/-! ## The diagonal congruence `lp E p ≃ₗᵢ[𝕜] lp F p` -/

section Module

variable [NormedRing 𝕜]
  [∀ i, Module 𝕜 (E i)] [∀ i, Module 𝕜 (F i)] [∀ i, Module 𝕜 (G i)]

/-- Applying componentwise linear isometry equivalences preserves membership in `ℓᵖ`. -/
theorem memℓp_congrRight_iff (e : ∀ i, E i ≃ₗᵢ[𝕜] F i) {f : ∀ i, E i} :
    Memℓp (fun i => e i (f i)) p ↔ Memℓp f p :=
  memℓp_congr_norm fun i => (e i).norm_map (f i)

variable [∀ i, IsBoundedSMul 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜 (F i)]
  [∀ i, IsBoundedSMul 𝕜 (G i)] [Fact (1 ≤ p)]

namespace LinearIsometryEquiv

/-- The diagonal linear isometry equivalence `lp E p ≃ₗᵢ[𝕜] lp F p` induced by a family of
componentwise linear isometry equivalences `e i : E i ≃ₗᵢ[𝕜] F i`, for every exponent
`p : ℝ≥0∞` with `1 ≤ p`: `f ↦ fun i => e i (f i)`.

(The hypothesis `Fact (1 ≤ p)` is forced by the bundled target type: Mathlib only equips
`lp E p` with its `NormedAddCommGroup` structure for `1 ≤ p`. Membership and norm
preservation hold for every `p`; see `memℓp_congrRight_iff` and `lp.norm_congr`.) -/
def lpCongrRight (p : ℝ≥0∞) [Fact (1 ≤ p)] (e : ∀ i, E i ≃ₗᵢ[𝕜] F i) :
    lp E p ≃ₗᵢ[𝕜] lp F p where
  toLinearEquiv :=
    { toFun := fun f => ⟨fun i => e i (f i), (memℓp_congrRight_iff e).mpr (lp.memℓp f)⟩
      invFun := fun g =>
        ⟨fun i => (e i).symm (g i),
          (memℓp_congrRight_iff fun i => (e i).symm).mpr (lp.memℓp g)⟩
      map_add' := fun f g => lp.ext <| funext fun i => map_add (e i) (f i) (g i)
      map_smul' := fun c f => lp.ext <| funext fun i => (e i).map_smul c (f i)
      left_inv := fun f => lp.ext <| funext fun i => (e i).symm_apply_apply (f i)
      right_inv := fun g => lp.ext <| funext fun i => (e i).apply_symm_apply (g i) }
  norm_map' := fun f => lp.norm_congr fun i => (e i).norm_map (f i)

@[simp]
theorem lpCongrRight_apply (e : ∀ i, E i ≃ₗᵢ[𝕜] F i) (f : lp E p) (i : ι) :
    lpCongrRight p e f i = e i (f i) :=
  rfl

@[simp]
theorem lpCongrRight_symm (e : ∀ i, E i ≃ₗᵢ[𝕜] F i) :
    (lpCongrRight p e).symm = lpCongrRight p fun i => (e i).symm :=
  rfl

@[simp]
theorem lpCongrRight_refl :
    lpCongrRight p (fun i => refl 𝕜 (E i)) = refl 𝕜 (lp E p) :=
  rfl

/-- The diagonal congruence is functorial: composing componentwise equivalences composes the
induced equivalences of `lp` spaces. -/
theorem lpCongrRight_trans (e : ∀ i, E i ≃ₗᵢ[𝕜] F i) (e' : ∀ i, F i ≃ₗᵢ[𝕜] G i) :
    (lpCongrRight p e).trans (lpCongrRight p e') =
      lpCongrRight p fun i => (e i).trans (e' i) :=
  rfl

end LinearIsometryEquiv

end Module

/-! ## `p = 2`: the Hilbert space case

For `p = 2` the diagonal congruence is a unitary between the Hilbert direct sums. No bespoke
inner product lemma is stated because Mathlib's generic `LinearIsometryEquiv.inner_map_map`
already applies, as the following sanity check records. -/

section L2

variable [RCLike 𝕜] [∀ i, InnerProductSpace 𝕜 (E i)] [∀ i, InnerProductSpace 𝕜 (F i)]

example (e : ∀ i, E i ≃ₗᵢ[𝕜] F i) (f g : lp E 2) :
    inner 𝕜 (LinearIsometryEquiv.lpCongrRight 2 e f) (LinearIsometryEquiv.lpCongrRight 2 e g) =
      inner 𝕜 f g :=
  LinearIsometryEquiv.inner_map_map _ f g

end L2

end
