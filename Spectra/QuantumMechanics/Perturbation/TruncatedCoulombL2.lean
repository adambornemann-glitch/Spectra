/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Perturbation.CoulombBound
/-!
# The annulus-truncated Coulomb potential is `L²` (brick M3)

The Coulomb multiplier `x ↦ −Z/‖x‖` is **not** square-integrable over all of `ℝ³`: it blows up
like `‖x‖⁻¹` at the origin and decays too slowly at infinity for `∫ ‖V‖² < ∞`.  Truncating it to a
spherical **annulus** `A_n = {x : 1/(n+1) ≤ ‖x‖ ≤ n+1}` cures both defects at once:

* on `A_n` the function is **bounded** (`‖V x‖ = Z/‖x‖ ≤ Z·(n+1)`, since `‖x‖ ≥ 1/(n+1)`), and
* `A_n` has **finite volume** (it sits inside `closedBall 0 (n+1)`, which is compact in the proper
  space `ℝ³`).

A bounded measurable function supported on a finite-measure set lies in every `Lᵖ`, so the
truncation `truncCoulomb p n` is in `L²(ℝ³)`.  This is brick **M3** of the relative-compactness
thread (the truncations form an `L²` approximating sequence for the full Coulomb multiplier).

## Main definitions

* `truncCoulomb` — the Coulomb multiplier (coerced to `ℂ`) restricted to the annulus `A_n`.

## Main statements

* `truncCoulomb_memLp` — `truncCoulomb p n ∈ L²(ℝ³)`.

The key Mathlib lemma chain is
`memLp_indicator_iff_restrict` (reduce to the restricted measure) `→`
`MemLp.of_bound` (bounded on a finite measure ⟹ `Lᵖ`), with `IsFiniteMeasure (volume.restrict A)`
supplied by `isFiniteMeasure_restrict` and `IsCompact.measure_ne_top`.
-/
open MeasureTheory Metric Set
open Spectra.Sobolev
open scoped ENNReal

namespace Spectra.QuantumMechanics.Hydrogen

/-- The spherical annulus `A_n = closedBall 0 (n+1) \ ball 0 (1/(n+1))`, i.e. the set of points
with `1/(n+1) ≤ ‖x‖ ≤ n+1`.  This is where the truncated Coulomb potential is supported. -/
def coulombAnnulus (n : ℕ) : Set R3 :=
  Metric.closedBall 0 (n + 1) \ Metric.ball 0 (1 / (n + 1))

/-- The annulus is a measurable set. -/
lemma measurableSet_coulombAnnulus (n : ℕ) : MeasurableSet (coulombAnnulus n) :=
  measurableSet_closedBall.diff measurableSet_ball

/-- The annulus has finite volume: it is contained in the compact ball `closedBall 0 (n+1)`. -/
lemma volume_coulombAnnulus_ne_top (n : ℕ) : volume (coulombAnnulus n) ≠ ∞ := by
  have hsub : coulombAnnulus n ⊆ Metric.closedBall (0 : R3) (n + 1) := diff_subset
  have hle : volume (coulombAnnulus n) ≤ volume (Metric.closedBall (0 : R3) (n + 1)) :=
    measure_mono hsub
  exact ne_top_of_le_ne_top
    (isCompact_closedBall (0 : R3) (n + 1)).measure_ne_top hle

/-- The annulus-truncated Coulomb potential: the (real) Coulomb multiplier `−Z/‖x‖`, coerced to
`ℂ` and cut off to the annulus `A_n` by the set indicator. -/
noncomputable def truncCoulomb (p : CoulombParams) (n : ℕ) : R3 → ℂ :=
  (coulombAnnulus n).indicator (fun x => ((coulombMultiplier p x : ℝ) : ℂ))

/-- **Brick M3.** The annulus-truncated Coulomb potential is square-integrable over `ℝ³`.

On the annulus `A_n` the function `‖x‖ ↦ Z/‖x‖` is bounded by `Z·(n+1)` (because `‖x‖ ≥ 1/(n+1)`),
and `A_n` has finite volume, so a bounded measurable function on a finite-measure set is in `L²`. -/
theorem truncCoulomb_memLp (p : CoulombParams) (n : ℕ) :
    MemLp (truncCoulomb p n) 2 (volume : Measure R3) := by
  -- Reduce `MemLp (indicator ...) 2 volume` to `MemLp ... 2 (volume.restrict A)`.
  rw [truncCoulomb, memLp_indicator_iff_restrict (measurableSet_coulombAnnulus n)]
  -- The restricted measure is finite.
  have hfin : IsFiniteMeasure ((volume : Measure R3).restrict (coulombAnnulus n)) :=
    isFiniteMeasure_restrict.2 (volume_coulombAnnulus_ne_top n)
  -- Measurability of the coerced multiplier.
  have hmeas : AEStronglyMeasurable (fun x => ((coulombMultiplier p x : ℝ) : ℂ))
      ((volume : Measure R3).restrict (coulombAnnulus n)) :=
    ((Complex.measurable_ofReal.comp (coulombMultiplier_measurable p)).aestronglyMeasurable)
  -- Bound by `Z·(n+1)` on the annulus (a.e. on the restricted measure).
  refine MemLp.of_bound hmeas (p.Z * (n + 1)) ?_
  refine (ae_restrict_iff' (measurableSet_coulombAnnulus n)).2 ?_
  filter_upwards with x hx
  -- Unpack `x ∈ A_n`: `1/(n+1) ≤ ‖x‖`.
  rw [coulombAnnulus, mem_diff, mem_ball, dist_zero_right, not_lt] at hx
  have hlow : 1 / (n + 1 : ℝ) ≤ ‖x‖ := hx.2
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hxpos : (0 : ℝ) < ‖x‖ := lt_of_lt_of_le (by positivity) hlow
  -- `‖((coulombMultiplier p x : ℝ) : ℂ)‖ = |coulombMultiplier p x| = Z/‖x‖`.
  rw [Complex.norm_real, Real.norm_eq_abs, coulombMultiplier_abs]
  -- `inverseR x = 1/‖x‖`; bound `1/‖x‖ ≤ n+1`.
  rw [inverseR, if_neg hxpos.ne']
  have hinv : 1 / ‖x‖ ≤ (n : ℝ) + 1 := by
    rw [div_le_iff₀ hxpos]
    calc (1 : ℝ) = ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) := by field_simp
      _ ≤ ((n : ℝ) + 1) * ‖x‖ := by
          apply mul_le_mul_of_nonneg_left _ hnpos.le
          simpa using hlow
  have hgoal : p.Z * (1 / ‖x‖) ≤ p.Z * ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hinv p.hZ.le
  simpa using hgoal

end Spectra.QuantumMechanics.Hydrogen
