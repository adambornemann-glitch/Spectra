/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.GaugeTheory.UnitaryGroup.Topology
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The Haar probability measure on the compact gauge groups

A compact group carries a unique left-invariant **probability** measure — its normalized Haar
measure.  For lattice gauge theory this is the single-link integration measure: the finite-volume
Gibbs measure (Lane L3) is a product `∏ₑ dHaar` of these, reweighted by `exp(−S)` (the Wilson action
of Lane L2).  This file supplies it for `Matrix.unitaryGroup n 𝕜` and
`Matrix.specialUnitaryGroup n 𝕜` over an `RCLike` field `𝕜`, using the compactness proved in
`UnitaryGroup/Topology.lean` (Lane G2).

## What this needed

The gauge groups had no `MeasurableSpace` at all — `Matrix n n α` carries **no** measurable-space
instance in Mathlib (instances do not transfer through the `def Matrix := … → …`).  So §1 equips
each group with its **Borel** σ-algebra directly (`borel _`, with `BorelSpace` by `rfl`) — the
canonical choice, and exactly what the Haar machinery consumes.  Everything else is already in
place: `IsTopologicalGroup` (Lane G1), `CompactSpace` (Lane G2),
`T2Space`/`LocallyCompactSpace`/`Nonempty` (automatic), so Mathlib's
`Measure.haarMeasure (⊤ : PositiveCompacts G)` applies and, normalized by `haarMeasure_self` at the
top compact `⊤` (carrier `= univ`), is a probability measure.

## Main definitions and results

* `Spectra.GaugeTheory.haarUnitary` / `haarSpecialUnitary` — the Haar probability measures on `U(n)`
  and `SU(n)`.
* Instances: each is an `IsProbabilityMeasure` and an `IsHaarMeasure` (left-invariant, positive on
  opens, finite on compacts).  Regularity (`Measure.Regular`) is automatic (`inferInstance`).
* `haarUnitary_unique` / `haarSpecialUnitary_unique` — **uniqueness**: any Haar probability measure
  on the group equals it (`isHaarMeasure_eq_of_isProbabilityMeasure`, needing only local
  compactness).

## Tags

Haar measure, compact group, unitary group, gauge group, probability measure, Yang-Mills
-/

open Matrix MeasureTheory TopologicalSpace

namespace Spectra.GaugeTheory

/-! ## §1  The Borel measurable-space structure

`Matrix n n α` has no `MeasurableSpace` instance in Mathlib, so we equip the gauge groups with their
Borel σ-algebra directly.  (`Subtype`/comap constructions are unavailable precisely because the
ambient matrix ring has no measurable structure.) -/

section BorelInstances

variable (n : Type*) [Fintype n] [DecidableEq n]
variable (α : Type*) [CommRing α] [StarRing α] [TopologicalSpace α]

noncomputable instance : MeasurableSpace (Matrix.unitaryGroup n α) := borel _

instance : BorelSpace (Matrix.unitaryGroup n α) := ⟨rfl⟩

noncomputable instance : MeasurableSpace (Matrix.specialUnitaryGroup n α) := borel _

instance : BorelSpace (Matrix.specialUnitaryGroup n α) := ⟨rfl⟩

end BorelInstances

/-! ## §2  The Haar probability measures -/

section Haar

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜] [ProperSpace 𝕜]

/-- The **Haar probability measure** on the unitary group `U(n)` — the normalized left-invariant
measure, `Measure.haarMeasure` at the top compact set (the whole, compact group). -/
noncomputable def haarUnitary : Measure (Matrix.unitaryGroup n 𝕜) := Measure.haarMeasure ⊤

/-- `haarUnitary` assigns total mass `1`: it is a probability measure. -/
instance instIsProbabilityMeasureHaarUnitary :
    IsProbabilityMeasure (haarUnitary (n := n) (𝕜 := 𝕜)) := by
  constructor
  change Measure.haarMeasure ⊤ Set.univ = 1
  rw [← PositiveCompacts.coe_top (α := Matrix.unitaryGroup n 𝕜)]
  exact Measure.haarMeasure_self

/-- `haarUnitary` is a Haar measure: left-invariant, positive on opens, finite on compacts. -/
instance instIsHaarMeasureHaarUnitary : (haarUnitary (n := n) (𝕜 := 𝕜)).IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure ⊤

/-- **Uniqueness of Haar on `U(n)`.**  Any Haar probability measure on the unitary group equals
`haarUnitary`. -/
theorem haarUnitary_unique (μ : Measure (Matrix.unitaryGroup n 𝕜))
    [IsProbabilityMeasure μ] [μ.IsHaarMeasure] : μ = haarUnitary :=
  Measure.isHaarMeasure_eq_of_isProbabilityMeasure μ _

/-- The **Haar probability measure** on the special unitary group `SU(n)`. -/
noncomputable def haarSpecialUnitary : Measure (Matrix.specialUnitaryGroup n 𝕜) :=
  Measure.haarMeasure ⊤

/-- `haarSpecialUnitary` is a probability measure. -/
instance instIsProbabilityMeasureHaarSpecialUnitary :
    IsProbabilityMeasure (haarSpecialUnitary (n := n) (𝕜 := 𝕜)) := by
  constructor
  change Measure.haarMeasure ⊤ Set.univ = 1
  rw [← PositiveCompacts.coe_top (α := Matrix.specialUnitaryGroup n 𝕜)]
  exact Measure.haarMeasure_self

/-- `haarSpecialUnitary` is a Haar measure. -/
instance instIsHaarMeasureHaarSpecialUnitary :
    (haarSpecialUnitary (n := n) (𝕜 := 𝕜)).IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure ⊤

/-- **Uniqueness of Haar on `SU(n)`.** -/
theorem haarSpecialUnitary_unique (μ : Measure (Matrix.specialUnitaryGroup n 𝕜))
    [IsProbabilityMeasure μ] [μ.IsHaarMeasure] : μ = haarSpecialUnitary :=
  Measure.isHaarMeasure_eq_of_isProbabilityMeasure μ _

end Haar

end Spectra.GaugeTheory
