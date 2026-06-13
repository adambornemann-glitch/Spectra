/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: Stage_2/Axioms/TruncatedTensorData.lean
-/
import Spectra.Mathlib.StochasticCalc.RoughPath.Axioms.NormedTensorSquare
/-!
# The General Truncated Tensor Algebra Interface

## Overview

This file defines the **abstract interface** for the level-N truncated tensor
algebra `T⁽ᴺ⁾(V)` and its group-like elements `G⁽ᴺ⁾(V)`. The only constructed
instance is N = 2 (in `Algebra/Instance.lean`); this file specifies what a
future N = 3, 4, ... construction would need to provide.

## Why this exists

Rough path theory at regularity `p ∈ [N, N+1)` requires truncation at level N:

| Regularity     | Truncation | Group              | Needed for               |
|----------------|------------|--------------------|--------------------------|
| p ∈ [1, 2)     | N = 1      | V (abelian)        | Young integration        |
| p ∈ [2, 3)     | N = 2      | G⁽²⁾(V) (step-2)   | Brownian motion, fBM H>⅓ |
| p ∈ [3, 4)     | N = 3      | G⁽³⁾(V) (step-3)   | fBM H>¼, rough vol       |
| p ∈ [N, N+1)   | N          | G⁽ᴺ⁾(V) (step-N)   | general                  |

Standard Brownian motion has p > 2, so N = 2 suffices. Fractional Brownian
motion with H ≈ 0.1 (rough volatility) formally needs N = 9, though in
practice truncation at 2 or 3 captures most of the signal.

## What the interface specifies

For each `N : ℕ` and normed space `V`:

1. **The algebra** `T⁽ᴺ⁾(V)` — a normed algebra with truncated multiplication
2. **The group** `G⁽ᴺ⁾(V)` — group-like elements, a subgroup of the units
3. **Projections** `πₖ : T⁽ᴺ⁾(V) → V⊗ᵏ` for each level k ≤ N
4. **The homogeneous norm** on `G⁽ᴺ⁾(V)` — controls each level at the right scaling
5. **Graded estimates** — `‖πₖ(g)‖ ≤ ‖g‖ₕₒₘᵏ` for group-like elements

## Design decisions

**Typeclass, not structure.** We use a typeclass so that `RoughPath N V p`
can find its algebra automatically. The `outParam` on the carrier types
means the algebra and group are determined by `N` and `V`.

**Minimal axioms.** We axiomatize only what the rough path theory *uses*:
the group law, the homogeneous norm, the graded estimates, and enough of
the algebra to state Chen's identity. We do NOT axiomatize the full algebra
structure (scalar multiplication, general elements with a₀ ≠ 1, etc.)
because the rough path theory only touches group-like elements.

**Projections as data.** The level-k projection `πₖ` is a field, not derived.
For N = 2, π₁ extracts `x` and π₂ extracts `𝕏`. For N = 3, there would be
a π₃ extracting the level-3 component. Making these fields avoids the need
to construct a general tensor power `V⊗ᵏ` (which Mathlib doesn't have
with norms for general k).

## The tensor power problem

The main obstacle to constructing instances for N > 2 is the **normed tensor
power** `V⊗ᵏ` with a cross-norm satisfying `‖v₁ ⊗ ··· ⊗ vₖ‖ ≤ ∏ ‖vᵢ‖`.

For N = 2, we axiomatized this as `NormedTensorSquare V` — a single Mathlib gap.
For general N, we would need either:

(a) An iterated construction: `V⊗ᵏ⁺¹ := V ⊗ (V⊗ᵏ)` with `NormedTensorSquare`
    applied recursively. This gives the right type but the associativity
    isomorphisms are painful.

(b) A direct axiomatization `NormedTensorPower N V` with carrier, cross-norm,
    and symmetric group action. Cleaner but more axioms.

(c) For finite-dimensional V = ℝᵈ: `V⊗ᵏ ≅ (Fin d → ... → Fin d → ℝ)` (k-tensors
    as multidimensional arrays). Completely concrete, works for all applications,
    but doesn't generalize to infinite-dimensional V.

We sketch approach (b) below and leave the construction to future work.

## References

- Friz, P.; Victoir, N., *Multidimensional Stochastic Processes as Rough Paths*,
  Cambridge (2010), Chapters 7–9
- Lyons, T., *Differential equations driven by rough signals*, Rev. Mat. Iberoam.
  **14** (1998), 215–310
- Reutenauer, C., *Free Lie Algebras*, Oxford (1993)
-/
open Spectra.Mathlib.StochCalc.NormedTensorSquare

namespace Spectra.Mathlib.StochCalc

/-! ## The normed tensor power (axiomatized)

This is the generalization of `NormedTensorSquare` to arbitrary tensor degree.
For k = 2, it should be instantiable from `NormedTensorSquare`. -/

/-- Axiomatized normed tensor power `V⊗ᵏ` with cross-norm.

This is the Mathlib gap at level k. When Mathlib gains the projective
tensor product with norms, this becomes an instance. -/
class NormedTensorPower (k : ℕ) (V : Type*) [NormedAddCommGroup V]
    [NormedSpace ℝ V] where
  /-- The carrier type representing V⊗ᵏ. -/
  Tₖ : outParam Type*
  [instNACG : NormedAddCommGroup Tₖ]
  [instNS : NormedSpace ℝ Tₖ]
  [instComplete : CompleteSpace Tₖ]
  /-- The k-fold tensor product map. For k = 0 this is the unit ℝ → T₀.
  For k = 1 this is the identity V → T₁. For k ≥ 2 this is the iterated
  product. We represent it as a multilinear map. -/
  tprodₖ : ContinuousMultilinearMap ℝ (fun _ : Fin k => V) Tₖ
  /-- **Cross-norm inequality**: the fundamental estimate. -/
  cross_norm : ∀ v : Fin k → V,
    ‖tprodₖ v‖ ≤ ∏ i : Fin k, ‖v i‖


attribute [instance] NormedTensorPower.instNACG
    NormedTensorPower.instNS NormedTensorPower.instComplete

/-! ## The truncated tensor algebra interface -/

/-- The **truncated tensor algebra data** at level N over V.

This is the abstract interface that the rough path theory consumes.
It specifies the algebra, the group, the projections, the norm, and
the estimates — everything needed to define rough paths, controlled
paths, and the rough integral at truncation level N.

The only constructed instance is N = 2 (from `TruncTensor₂` and
`GroupLike₂`). Future instances for N = 3, 4, ... would be built
from `NormedTensorPower` data.

### What the rough path theory needs:

1. A **group** `Grp` with identity, multiplication, and inverse
2. **Projections** extracting the level-k component (k = 1, ..., N)
3. A **homogeneous norm** satisfying graded estimates
4. The norm being **symmetric** under inversion
5. A **quasi-triangle inequality** for the norm

### What the rough path theory does NOT need:

- The full algebra structure (only the group is used)
- The algebra multiplication on non-group-like elements
- The scalar (level-0) component (always = 1 for group-like elements)
- The universal property of the tensor algebra
- The shuffle product or other combinatorial structures -/
class TruncatedTensorData (N : ℕ) (V : Type*) [NormedAddCommGroup V]
    [NormedSpace ℝ V] where
  /-- The group of group-like elements G⁽ᴺ⁾(V). -/
  Grp : outParam Type*
  [instGrp : Group Grp]
  /-- Level-1 projection: extracts the path increment `x ∈ V`. -/
  proj₁ : Grp → V
  /-- The identity has zero level-1 component. -/
  proj₁_one : proj₁ 1 = 0
  /-- Level-1 is additive under multiplication (Chen level 1). -/
  proj₁_mul : ∀ g h : Grp, proj₁ (g * h) = proj₁ g + proj₁ h

  /-- The **homogeneous norm** on G⁽ᴺ⁾(V).
  For N = 2: `max(‖x‖, ‖A‖^{1/2})`
  For general N: `max_k(‖πₖ(g)‖^{1/k})` where the max runs over k = 1, ..., N
  and `πₖ` extracts the "free" level-k component (antisymmetric part, Lie
  algebra projection, etc. depending on the formulation). -/
  homoNorm : Grp → ℝ
  /-- Non-negativity. -/
  homoNorm_nonneg : ∀ g, 0 ≤ homoNorm g
  /-- Positive definiteness. -/
  homoNorm_eq_zero_iff : ∀ g, homoNorm g = 0 ↔ g = 1
  /-- Symmetry under inversion: `‖g⁻¹‖ = ‖g‖`. -/
  homoNorm_inv : ∀ g, homoNorm g⁻¹ = homoNorm g
  /-- Quasi-triangle inequality: `‖gh‖ ≤ C(‖g‖ + ‖h‖)`.
  The constant C depends on N but not on V. -/
  homoNorm_mul_le : ∃ C > 0, ∀ g h : Grp,
    homoNorm (g * h) ≤ C * (homoNorm g + homoNorm h)
  /-- Level-1 extraction: `‖proj₁(g)‖ ≤ ‖g‖_hom`. -/
  norm_proj₁_le : ∀ g, ‖proj₁ g‖ ≤ homoNorm g


attribute [instance] TruncatedTensorData.instGrp

namespace TruncatedTensorData

variable {N : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TruncatedTensorData N V]

/-- The left-invariant quasi-metric on G⁽ᴺ⁾(V). -/
def dist (g h : Grp N V) : ℝ := homoNorm (g⁻¹ * h)

theorem dist_self (g : Grp N V) : dist g g = 0 := by
  simp [dist, homoNorm_eq_zero_iff]

theorem dist_symm (g h : Grp N V) : dist g h = dist h g := by
  simp only [dist]
  rw [← homoNorm_inv (g⁻¹ * h), mul_inv_rev, inv_inv]

end TruncatedTensorData

/-! ## Extended interface for N ≥ 2

When the truncation level is at least 2, we have a level-2 projection
and the level-2 Chen identity with its cross-term. This is the interface
that the rough integral actually uses. -/

/-- Extended data for N ≥ 2: level-2 projection and Chen's identity. -/
class TruncatedTensorData₂ (N : ℕ) (V : Type*) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedTensorSquare V]
    extends TruncatedTensorData N V where
  /-- Level-2 projection: extracts the area `𝕏 ∈ V ⊗ V`. -/
  proj₂ : Grp → T₂ V
  /-- The identity has zero level-2 component. -/
  proj₂_one : proj₂ 1 = 0
  /-- **Level-2 Chen's identity**: the cross-term formula.
  `π₂(gh) = π₂(g) + π₁(g) ⊗ π₁(h) + π₂(h)` -/
  proj₂_mul : ∀ g h : Grp,
    proj₂ (g * h) = proj₂ g + (proj₁ g ⊗ₜ proj₁ h) + proj₂ h
  /-- Level-2 extraction: `‖π₂(g)‖ ≤ C · ‖g‖_hom²`.
  The square reflects parabolic scaling. -/
  norm_proj₂_le : ∃ C ≥ 0, ∀ g : Grp, ‖proj₂ g‖ ≤ C * homoNorm g ^ 2

/-! ## Extended interface for N ≥ 3

For rough volatility models with H ≈ 0.1, one formally needs N ≥ 3.
The level-3 data involves `V ⊗ V ⊗ V` and the level-3 Chen identity
with *two* cross-terms. -/

/-- Extended data for N ≥ 3: level-3 projection and Chen's identity.
This requires `NormedTensorPower 3 V` or an equivalent axiomatization
of `V ⊗ V ⊗ V` with a cross-norm. -/
class TruncatedTensorData₃ (N : ℕ) (V : Type*) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedTensorSquare V] [NormedTensorPower 3 V]
    extends TruncatedTensorData₂ N V where
  /-- Level-3 projection: extracts the third-order iterated integral data. -/
  proj₃ : Grp → NormedTensorPower.Tₖ 3 V
  /-- The identity has zero level-3 component. -/
  proj₃_one : proj₃ 1 = 0
  /-- **Level-3 Chen's identity**: two cross-terms.
  `π₃(gh) = π₃(g) + π₁(g) ⊗ π₂(h) + π₂(g) ⊗ π₁(h) + π₃(h)`

  The terms `π₁(g) ⊗ π₂(h)` and `π₂(g) ⊗ π₁(h)` involve the "mixed"
  tensor products `V ⊗ (V ⊗ V)` and `(V ⊗ V) ⊗ V`, which both embed
  into `V ⊗ V ⊗ V`. The precise formulation requires choosing either:
  (a) A pairing `V × T₂ V → T₃ V` (left insertion)
  (b) A pairing `T₂ V × V → T₃ V` (right insertion)
  Both are needed, and they must be consistent with the associator. -/
  proj₃_mul : ∀ _g _h : Grp, True  -- placeholder: needs the pairing infrastructure
  /-- Level-3 extraction: `‖π₃(g)‖ ≤ C · ‖g‖_hom³`. -/
  norm_proj₃_le : ∃ C ≥ 0, ∀ g : Grp,
    ‖proj₃ g‖ ≤ C * homoNorm g ^ 3

/-! ## The N = 2 instance (constructed in Algebra/Instance.lean)

This is a forward declaration showing what `Instance.lean` will provide.
The actual construction uses `GroupLike₂`, `homoNorm`, and the results
from `HomoNorm.lean`. -/

-- instance (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
--     [NormedTensorSquare V] :
--     TruncatedTensorData₂ 2 V where
--   Grp := GroupLike₂ V
--   proj₁ := GroupLike₂.x
--   proj₁_one := GroupLike₂.one_x
--   proj₁_mul := fun g h => GroupLike₂.chen₁ g h
--   homoNorm := GroupLike₂.homoNorm
--   homoNorm_nonneg := GroupLike₂.homoNorm_nonneg
--   homoNorm_eq_zero_iff := GroupLike₂.homoNorm_eq_zero_iff
--   homoNorm_inv := GroupLike₂.homoNorm_inv
--   homoNorm_mul_le := ⟨4, by norm_num, GroupLike₂.homoNorm_mul_le⟩
--   norm_proj₁_le := GroupLike₂.norm_x_le_homoNorm
--   proj₂ := GroupLike₂.𝕏
--   proj₂_one := GroupLike₂.one_𝕏
--   proj₂_mul := fun g h => GroupLike₂.chen₂ g h
--   norm_proj₂_le := ⟨1, le_refl _, fun g => GroupLike₂.norm_area_le_homoNorm_sq g⟩
--     -- Note: this uses ‖𝕏‖ ≤ ½‖x‖² + ‖A‖ ≤ ... which may need a different constant

/-! ## What a level-3 rough path theory would need

For completeness, here is the checklist for extending the formalization to N = 3:

### New axioms / constructions needed:

1. `NormedTensorPower 3 V` — the normed tensor cube V ⊗ V ⊗ V
2. Pairings `V × T₂ V → T₃ V` and `T₂ V × V → T₃ V` with cross-norm
3. The free step-3 nilpotent group `G⁽³⁾(V)`:
   - Elements: `(x, 𝕏, 𝕏³)` with x ∈ V, 𝕏 ∈ V⊗², 𝕏³ ∈ V⊗³
   - Constraints: Sym conditions at each level (generalized group-like)
   - Group law: truncated multiplication with cross-terms at levels 2 and 3
4. Homogeneous norm: `max(‖x‖, ‖𝕏‖^{1/2}, ‖𝕏³‖^{1/3})`
5. Quasi-triangle inequality for the level-3 norm

### New analytical results needed:

6. Controlled paths with a level-2 Gubinelli derivative:
   `Y_t - Y_s = Y'_s · X_{s,t} + Y''_s · 𝕏_{s,t} + R_{s,t}`
   with R of order ω^{3/p}
7. The rough integral approximation with THREE terms:
   `Ξ(s,t) = Y_s · X_{s,t} + Y'_s · 𝕏_{s,t} + Y''_s · 𝕏³_{s,t}`
8. Defect of order ω^{4/p} with 4/p > 1 requiring p < 4
9. Sewing lemma at the 4/p threshold

### What stays the same:

- The sewing lemma (Stage 0) — unchanged, just with θ = 4/p instead of 3/p
- The algebraic structure of Chen's identity — same pattern, one more level
- The Picard fixed-point scheme — same contraction argument
- The Itô-Lyons continuity estimate — same decomposition, more terms

The jump from N = 2 to N = 3 is roughly 3× the code of N = 2, mostly
because of the additional cross-terms and the need to track three levels
of regularity instead of two. The jump from N = 3 to general N would
require a recursive/inductive construction of the tensor powers and the
group law, which is a significant algebraic formalization project.
-/
end Spectra.Mathlib.StochCalc
