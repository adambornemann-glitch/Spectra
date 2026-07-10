/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.GaugeTheory.Lattice.Basic
import Spectra.GaugeTheory.UnitaryGroup.Topology
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.BigOperators

/-!
# The Wilson plaquette action

The **Wilson action** of a lattice gauge configuration `U` on the finite periodic lattice
(`Lattice/Basic.lean`) with gauge group `U(n)`:
$$ S(U) \;=\; \beta \sum_{p} \operatorname{Re} \operatorname{tr}\bigl(1 - U(p)\bigr), \qquad
\beta = 2/g_0^2, $$
where the sum runs over all plaquettes `p`, `U(p)` is the plaquette holonomy
(`plaquetteHolonomy`, the elementary Wilson loop), and `β` is the inverse coupling.  This is the
weight in the finite-volume Gibbs measure `dμ ∝ exp(−S(U)) ∏ dHaar` (Lane L3).

## Design

* `plaquetteAction U p = Re tr(1 − U(p))` — the **local action density** on one plaquette, a real
  number.  The gauge group is `Matrix.unitaryGroup n ℂ`; `U(p)` is coerced to its underlying matrix
  to take the (fundamental-representation) trace.
* `wilsonAction β U = β · Σₚ plaquetteAction U p` — the total action.  `β` is a free real parameter
  (physically `2/g₀²`); leaving it abstract keeps the object honest and reusable.

## Main results

* `re_trace_le_card` — `Re tr U ≤ n` for a unitary matrix (its diagonal entries have modulus `≤ 1`,
  reusing `Spectra.GaugeTheory.norm_entry_le_one` from Lane G).  This is what makes the action
  **nonnegative**, the physical statement that the action is minimized by the flat connection.
* `plaquetteAction_nonneg`, `wilsonAction_nonneg` — `S(U) ≥ 0` for `β ≥ 0`.
* `plaquetteAction_one`, `wilsonAction_one` — the trivial (all-identity, "vacuum") configuration has
  **zero** action — the unique minimizer.

## Tags

Wilson action, lattice gauge theory, plaquette, gauge configuration, Yang-Mills
-/

open Matrix

namespace Spectra.GaugeTheory.Lattice

variable {d L : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-! ## §1  The trace bound for unitary matrices -/

/-- **`Re tr U ≤ n`** for a unitary matrix `U` (`n = Fintype.card`).  Each diagonal entry satisfies
`Re Uᵢᵢ ≤ ‖Uᵢᵢ‖ ≤ 1` (the latter is `Spectra.GaugeTheory.norm_entry_le_one`), and the trace is the
sum of the `n` diagonal entries. This is the inequality behind nonnegativity of the Wilson
action. -/
theorem re_trace_le_card {A : Matrix n n ℂ} (hA : A ∈ Matrix.unitaryGroup n ℂ) :
    (Matrix.trace A).re ≤ Fintype.card n := by
  have hbd : ∀ i, (A i i).re ≤ 1 := fun i =>
    (RCLike.re_le_norm (A i i)).trans (Spectra.GaugeTheory.norm_entry_le_one hA i i)
  have hsum : (Matrix.trace A).re = ∑ i, (A i i).re := by
    rw [Matrix.trace, Complex.re_sum]; simp only [Matrix.diag_apply]
  rw [hsum]
  calc ∑ i, (A i i).re ≤ ∑ _i : n, (1 : ℝ) := Finset.sum_le_sum fun i _ => hbd i
    _ = Fintype.card n := by simp

/-! ## §2  The Wilson action -/

/-- The **local action density** on a plaquette, `Re tr(1 − U(p))`, where `U(p)` is the plaquette
holonomy (coerced to its underlying `n × n` matrix). -/
noncomputable def plaquetteAction (U : Config d L (Matrix.unitaryGroup n ℂ)) (p : Plaquette d L) :
    ℝ :=
  (Matrix.trace ((1 : Matrix n n ℂ) - (plaquetteHolonomy U p).val)).re

/-- The **Wilson action** `S(U) = β Σₚ Re tr(1 − U(p))`, `β = 2/g₀²` the inverse coupling. -/
noncomputable def wilsonAction [NeZero L] (β : ℝ) (U : Config d L (Matrix.unitaryGroup n ℂ)) : ℝ :=
  β * ∑ p : Plaquette d L, plaquetteAction U p

/-! ## §3  Nonnegativity and the vacuum minimizer -/

/-- The local action density equals `n − Re tr U(p)`. -/
lemma plaquetteAction_eq (U : Config d L (Matrix.unitaryGroup n ℂ)) (p : Plaquette d L) :
    plaquetteAction U p
      = (Fintype.card n : ℝ) - (Matrix.trace (plaquetteHolonomy U p).val).re := by
  rw [plaquetteAction, Matrix.trace_sub, Complex.sub_re, Matrix.trace_one, Complex.natCast_re]

/-- **The local action density is nonnegative** — from `re_trace_le_card`. -/
lemma plaquetteAction_nonneg (U : Config d L (Matrix.unitaryGroup n ℂ)) (p : Plaquette d L) :
    0 ≤ plaquetteAction U p := by
  rw [plaquetteAction_eq]
  have := re_trace_le_card (plaquetteHolonomy U p).2
  linarith

/-- **The trivial (vacuum) configuration has zero density** on every plaquette. -/
@[simp] lemma plaquetteAction_one (p : Plaquette d L) :
    plaquetteAction (fun _ => (1 : Matrix.unitaryGroup n ℂ)) p = 0 := by
  simp [plaquetteAction, plaquetteHolonomy_one]

/-- **The Wilson action is nonnegative** for a nonnegative coupling `β`. -/
lemma wilsonAction_nonneg [NeZero L] {β : ℝ} (hβ : 0 ≤ β)
    (U : Config d L (Matrix.unitaryGroup n ℂ)) : 0 ≤ wilsonAction β U :=
  mul_nonneg hβ (Finset.sum_nonneg fun p _ => plaquetteAction_nonneg U p)

/-- **The trivial (vacuum) configuration is a zero of the action** — the flat connection minimizes
`S`. -/
@[simp] lemma wilsonAction_one [NeZero L] (β : ℝ) :
    wilsonAction β (fun _ : Link d L => (1 : Matrix.unitaryGroup n ℂ)) = 0 := by
  simp [wilsonAction]

/-! ## §4  Uniform upper bounds

A companion `−n ≤ Re tr U` gives a *uniform* (configuration-independent) upper bound on the action,
which is what makes the partition function `∫ exp(−S)` strictly positive (Lane L3): `exp(−S)` is
bounded below by the positive constant `exp(−M)`. -/

/-- **`−n ≤ Re tr U`** for a unitary matrix — the lower companion of `re_trace_le_card`
(`Re Uᵢᵢ ≥ −‖Uᵢᵢ‖ ≥ −1`). -/
theorem neg_card_le_re_trace {A : Matrix n n ℂ} (hA : A ∈ Matrix.unitaryGroup n ℂ) :
    (-(Fintype.card n : ℝ)) ≤ (Matrix.trace A).re := by
  have hbd : ∀ i, (-1 : ℝ) ≤ (A i i).re := fun i => by
    have h1 : -‖A i i‖ ≤ (A i i).re := (abs_le.mp (RCLike.abs_re_le_norm _)).1
    have h2 : ‖A i i‖ ≤ 1 := Spectra.GaugeTheory.norm_entry_le_one hA i i
    linarith
  have hsum : (Matrix.trace A).re = ∑ i, (A i i).re := by
    rw [Matrix.trace, Complex.re_sum]; simp only [Matrix.diag_apply]
  rw [hsum]
  calc (-(Fintype.card n : ℝ)) = ∑ _i : n, (-1 : ℝ) := by simp
    _ ≤ ∑ i, (A i i).re := Finset.sum_le_sum fun i _ => hbd i

/-- The local action density is bounded above by `2n` (`plaquetteAction = n − Re tr U(p) ≤ 2n`). -/
theorem plaquetteAction_le (U : Config d L (Matrix.unitaryGroup n ℂ)) (p : Plaquette d L) :
    plaquetteAction U p ≤ 2 * Fintype.card n := by
  rw [plaquetteAction_eq]
  have := neg_card_le_re_trace (plaquetteHolonomy U p).2
  linarith

/-- **Uniform upper bound on the Wilson action** (for `β ≥ 0`): `S(U) ≤ β · #plaquettes · 2n`,
independent of the configuration `U`. -/
theorem wilsonAction_le [NeZero L] {β : ℝ} (hβ : 0 ≤ β)
    (U : Config d L (Matrix.unitaryGroup n ℂ)) :
    wilsonAction β U ≤ β * (Fintype.card (Plaquette d L) * (2 * Fintype.card n)) := by
  rw [wilsonAction]
  apply mul_le_mul_of_nonneg_left _ hβ
  calc ∑ p : Plaquette d L, plaquetteAction U p
      ≤ ∑ _p : Plaquette d L, (2 * Fintype.card n : ℝ) :=
        Finset.sum_le_sum fun p _ => plaquetteAction_le U p
    _ = Fintype.card (Plaquette d L) * (2 * Fintype.card n) := by
        rw [Finset.sum_const]; simp [nsmul_eq_mul]

end Spectra.GaugeTheory.Lattice
