/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.RCLike.Basic

/-!
# The unitary group is a compact topological group

The compact matrix Lie groups `U(n)`, `SU(n)` (and, over `ℝ`, `O(n)`, `SO(n)`) are the structure
groups of gauge theories.  This file supplies the two facts a gauge-theory development needs first —
that they are **topological groups** and that they are **compact** — for `Matrix.unitaryGroup n 𝕜`
and `Matrix.specialUnitaryGroup n 𝕜` over any `RCLike` field `𝕜`.

## What Mathlib already gives (G1 is essentially free)

The Yang–Mills survey recorded "zero `TopologicalSpace`/`IsTopologicalGroup` instance for
`unitaryGroup`."  That is true only of a *named* instance: the structure is in fact fully
**derivable** from generic Mathlib machinery, and the `example`s in §1 confirm it resolves by
`inferInstance`:

* `Matrix.unitaryGroup n α = unitary (Matrix n n α)` inherits the subtype topology, and
  `Mathlib.Topology.Algebra.Star.Unitary` proves `IsTopologicalGroup (unitary R)`,
  `ContinuousInv (unitary R)`, `isClosed_unitary` for any topological monoid-with-star `R`;
* `Mathlib.Topology.Instances.Matrix` makes `Matrix n n α` a topological ring with continuous star
  (`Matrix.topologicalRing`, the `ContinuousStar`/`ContinuousMul` instances).

So the topological-group half of the "compact gauge group" lane needs no new proof — only the named
handle `isClosed_unitaryGroup` (§1).

## What is genuinely new (G2)

**Compactness is not free.**  `Matrix n n 𝕜` is not compact, so closedness alone does not suffice.
We prove `CompactSpace` by exhibiting `unitaryGroup n 𝕜` as a **closed subset of a compact box** —
the product `∏ᵢⱼ closedBall(0,1)` of unit balls — using:

* `norm_entry_le_one`: every entry of a unitary matrix has norm `≤ 1` (its columns are unit vectors,
  `∑ₖ ‖Aₖⱼ‖² = 1` from `star A * A = 1`);
* the box is compact by Tychonoff (`isCompact_univ_pi` + `isCompact_closedBall`);
* `unitaryGroup` is closed (`isClosed_unitary`), hence compact (`IsCompact.of_isClosed_subset`).

This route uses only the **product topology** on `Matrix` (the default instance), sidestepping the
matrix operator-norm/product-topology diamond entirely.  `specialUnitaryGroup` is then a closed
(`det = 1`) subset of the compact `unitaryGroup`, hence compact.

## Main results

* `Spectra.GaugeTheory.isClosed_unitaryGroup` — `unitaryGroup n α` is closed.
* `Spectra.GaugeTheory.norm_entry_le_one` — unitary matrix entries are bounded by `1`.
* `Spectra.GaugeTheory.isCompact_unitaryGroup` + the `CompactSpace` instance.
* `Spectra.GaugeTheory.isCompact_specialUnitaryGroup` + the `CompactSpace` instance.

## Tags

unitary group, special unitary group, compact Lie group, topological group, gauge group, Yang-Mills
-/

open Matrix Topology

namespace Spectra.GaugeTheory

/-! ## §1  (G1) Topological-group structure — derivable, recorded

The two `example`s verify that `TopologicalSpace` and `IsTopologicalGroup` for the unitary group
resolve automatically; `isClosed_unitaryGroup` is the one named handle worth exporting. -/

section TopologicalGroup

variable (n : Type*) [Fintype n] [DecidableEq n]
variable (α : Type*) [CommRing α] [StarRing α] [TopologicalSpace α] [IsTopologicalRing α]
  [ContinuousStar α]

example : TopologicalSpace (Matrix.unitaryGroup n α) := inferInstance
example : IsTopologicalGroup (Matrix.unitaryGroup n α) := inferInstance

/-- **The unitary group is closed** in the matrix ring, from the generic `isClosed_unitary`.
(Needs `T1Space α` so that the defining relation `star A * A = 1` cuts out a closed set.) -/
theorem isClosed_unitaryGroup [T1Space α] :
    IsClosed (Matrix.unitaryGroup n α : Set (Matrix n n α)) :=
  isClosed_unitary

/-! Unlike `unitaryGroup = unitary (Matrix n n α)`, the special unitary group is **not** an instance
of Mathlib's generic `unitary R`, so it does not inherit the topological-group structure — but its
inversion is still `star` (`specialUnitaryGroup.coe_star`), so the same three-line argument applies.
-/

instance : ContinuousStar (Matrix.specialUnitaryGroup n α) where
  continuous_star := continuous_induced_rng.mpr continuous_subtype_val.star

instance : ContinuousInv (Matrix.specialUnitaryGroup n α) where
  continuous_inv := continuous_star

/-- **The special unitary group is a topological group** (its inversion `= star` is continuous). -/
instance : IsTopologicalGroup (Matrix.specialUnitaryGroup n α) where

end TopologicalGroup

/-! ## §2  (G2) Compactness of `U(n)` and `SU(n)` over an `RCLike` field -/

section Compact

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜] [ProperSpace 𝕜]

omit [ProperSpace 𝕜] in
/-- **Entry bound.**  Every entry of a unitary matrix has norm `≤ 1`.  The `j`-th column is a unit
vector — `∑ₖ ‖Aₖⱼ‖² = 1`, read off the `(j,j)` diagonal entry of `star A * A = 1` via
`RCLike.conj_mul` — so each `‖Aᵢⱼ‖² ≤ 1`. -/
theorem norm_entry_le_one {A : Matrix n n 𝕜}
    (hA : A ∈ Matrix.unitaryGroup n 𝕜) (i j : n) : ‖A i j‖ ≤ 1 := by
  have hstar : star A * A = 1 := (Matrix.mem_unitaryGroup_iff').mp hA
  have hsum : ∑ k, ‖A k j‖ ^ 2 = 1 := by
    have h := congrFun (congrFun hstar j) j
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
    simp only [Matrix.star_apply] at h
    have h2 : ∑ k, ((‖A k j‖ ^ 2 : ℝ) : 𝕜) = 1 := by
      rw [← h]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← starRingEnd_apply, RCLike.conj_mul (A k j)]
      norm_cast
    exact_mod_cast h2
  have hle : ‖A i j‖ ^ 2 ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun k => ‖A k j‖ ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_univ i)
  nlinarith [norm_nonneg (A i j)]

/-- **`U(n)` is compact**: a closed subset of the compact box `∏ᵢⱼ closedBall(0,1)`. -/
theorem isCompact_unitaryGroup :
    IsCompact (Matrix.unitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) := by
  have hbox : IsCompact (Set.univ.pi fun _ : n => Set.univ.pi fun _ : n =>
      Metric.closedBall (0 : 𝕜) 1 : Set (Matrix n n 𝕜)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hcl : IsClosed (Matrix.unitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) := isClosed_unitary
  refine hbox.of_isClosed_subset hcl ?_
  intro A hA
  simp only [Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
  intro i j
  exact norm_entry_le_one hA i j

/-- `U(n)` is a compact space. -/
instance instCompactSpaceUnitaryGroup : CompactSpace (Matrix.unitaryGroup n 𝕜) :=
  isCompact_iff_compactSpace.mp isCompact_unitaryGroup

omit [ProperSpace 𝕜] in
/-- **`SU(n)` is closed**: it is the intersection of the (closed) unitary group with the closed set
`{A | det A = 1}` (`det` is continuous). -/
theorem isClosed_specialUnitaryGroup :
    IsClosed (Matrix.specialUnitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) := by
  have hset : (Matrix.specialUnitaryGroup n 𝕜 : Set (Matrix n n 𝕜))
      = (Matrix.unitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) ∩ {A | A.det = 1} := by
    ext A
    simp only [SetLike.mem_coe, Matrix.mem_specialUnitaryGroup_iff, Set.mem_inter_iff,
      Set.mem_setOf_eq]
  rw [hset]
  exact isClosed_unitary.inter (isClosed_eq continuous_id.matrix_det continuous_const)

/-- **`SU(n)` is compact**: a closed subset of the compact `U(n)`. -/
theorem isCompact_specialUnitaryGroup :
    IsCompact (Matrix.specialUnitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) :=
  isCompact_unitaryGroup.of_isClosed_subset isClosed_specialUnitaryGroup
    (SetLike.coe_subset_coe.mpr Matrix.specialUnitaryGroup_le_unitaryGroup)

/-- `SU(n)` is a compact space. -/
instance instCompactSpaceSpecialUnitaryGroup :
    CompactSpace (Matrix.specialUnitaryGroup n 𝕜) :=
  isCompact_iff_compactSpace.mp isCompact_specialUnitaryGroup

end Compact

end Spectra.GaugeTheory
