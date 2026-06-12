/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/PartitionDefs.lean
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Tactic

open Real Set Filter

variable {E : Type*} [NormedAddCommGroup E]

namespace Spectra.Mathlib.StochCalc

section Partition
/-- A **partition** of a real interval: a monotone sequence of `n + 1` points
`t₀ ≤ t₁ ≤ ⋯ ≤ tₙ` with `t₀ = s` and `tₙ = t`.

We use `Fin (n + 1)` indexing for clean boundary access. -/
structure Partition (s t : ℝ) where
  /-- Number of sub-intervals. -/
  n : ℕ
  /-- The partition points. -/
  pts : Fin (n + 1) → ℝ
  /-- The partition is monotone. -/
  mono : Monotone pts
  /-- The first point is `s`. -/
  first : pts ⟨0, Nat.zero_lt_succ n⟩ = s
  /-- The last point is `t`. -/
  last : pts ⟨n, Nat.lt_succ_of_le le_rfl⟩ = t

/-- The `i`-th sub-interval endpoint, for `i ≤ n`. -/
def Partition.point {s t : ℝ} (P : Partition s t) (i : Fin (P.n + 1)) : ℝ :=
  P.pts i

/-- The left endpoint of the `i`-th sub-interval (for `i < n`). -/
def Partition.left {s t : ℝ} (P : Partition s t) (i : Fin P.n) : ℝ :=
  P.pts ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩

/-- The right endpoint of the `i`-th sub-interval. -/
def Partition.right {s t : ℝ} (P : Partition s t) (i : Fin P.n) : ℝ :=
  P.pts ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

/-- The mesh of a partition: the maximum sub-interval length. -/
def Partition.mesh {s t : ℝ} (P : Partition s t) : ℝ :=
  if h : P.n = 0 then 0
  else Finset.sup' (Finset.univ (α := Fin P.n))
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩)
    (fun i => P.right i - P.left i)

/-- The trivial partition: one interval `[s, t]`. -/
def Partition.trivial (s t : ℝ) (hst : s ≤ t) : Partition s t where
  n := 1
  pts := ![s, t]
  mono := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    interval_cases i <;> interval_cases j <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
  first := by simp [Matrix.cons_val_zero]
  last := by simp [Matrix.cons_val_one]

/-- **Refinement**: partition `P'` refines `P` if every point of `P` appears in `P'`. -/
def Partition.IsRefinement {s t : ℝ} (P' P : Partition s t) : Prop :=
  ∀ i : Fin (P.n + 1), ∃ j : Fin (P'.n + 1), P'.pts j = P.pts i

/-- **The Riemann sum** of a two-parameter map `Ξ` over a partition `P`:
`RS(P) = ∑ᵢ Ξ(tᵢ, tᵢ₊₁)`. -/
def riemannSum (Ξ : ℝ → ℝ → E) {s t : ℝ} (P : Partition s t) : E :=
  ∑ i : Fin P.n, Ξ (P.left i) (P.right i)

end Partition

end Spectra.Mathlib.StochCalc
