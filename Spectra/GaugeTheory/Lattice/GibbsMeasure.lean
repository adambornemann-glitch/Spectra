/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.GaugeTheory.Lattice.WilsonAction
import Spectra.GaugeTheory.UnitaryGroup.Haar
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The finite-volume lattice gauge Gibbs measure

The **Gibbs measure** of lattice gauge theory on the finite periodic lattice with gauge group
`U(n)`:
$$ d\mu_\beta(U) \;=\; \frac{1}{Z(\beta)}\, e^{-S(U)} \prod_{e} d\mathrm{Haar}(U_e), $$
the Wilson action `S = wilsonAction β` (Lane L2) reweighting the a priori product of Haar measures
(Lane G3) over the links (Lane L1).  This is the measure whose reflection positivity (Lane R2) and
correlation decay carry the mass gap.

## Construction

* `aprioriMeasure` — the product `∏ₑ dHaar` on the configuration space `Config = Link → U(n)`, via
  `Measure.pi`.  A probability measure (product of probability measures).
* `gibbsDensity β U = exp(−S(U))` (as an `ℝ≥0∞`) — the Boltzmann weight.
* `partitionFunction β = ∫ exp(−S) d(aprioriMeasure)` — the normalization `Z`.
* `gibbsMeasure β = Z⁻¹ • (aprioriMeasure.withDensity (gibbsDensity β))` — the normalized Gibbs
  measure.

## Main results

* `partitionFunction_ne_top` / `partitionFunction_pos` — `0 < Z ≤ 1`. Both bounds come from Lane L2:
  `0 ≤ S` gives `exp(−S) ≤ 1` hence `Z ≤ 1`; the *uniform* bound `S ≤ M` (`wilsonAction_le`) gives
  `exp(−S) ≥ exp(−M) > 0` hence `Z > 0`. This is what makes the reweighting well-defined.
* `isProbabilityMeasure_gibbsMeasure` — the normalized Gibbs measure is a **probability measure**.
* `continuous_wilsonAction` / `measurable_gibbsDensity` — the action is continuous on configuration
  space (the holonomies depend continuously on the link variables, `U(n)` being a topological
  group), so the Boltzmann weight is a genuine measurable density.

## Tags

lattice gauge theory, Gibbs measure, Wilson action, partition function, Haar measure, Yang-Mills
-/

open Matrix MeasureTheory Topology
open scoped ENNReal

namespace Spectra.GaugeTheory.Lattice

/-! ## §0  Second-countability, so configuration space is a standard Borel space

`Matrix n n ℂ` and the unitary group are second countable (finite-dimensional over `ℂ`); this makes
the configuration space `Config = Link → U(n)` a Borel space, so the Wilson action's continuity
upgrades to measurability of the Boltzmann weight. -/

instance instSecondCountableMatrix {n : Type*} [Finite n] :
    SecondCountableTopology (Matrix n n ℂ) :=
  inferInstanceAs (SecondCountableTopology (n → n → ℂ))

instance instSecondCountableUnitaryGroup {n : Type*} [Fintype n] [DecidableEq n] :
    SecondCountableTopology (Matrix.unitaryGroup n ℂ) :=
  IsInducing.subtypeVal.secondCountableTopology

variable {d L : ℕ} [NeZero L] {n : Type*} [Fintype n] [DecidableEq n]

/-! ## §1  The a priori product-Haar measure -/

/-- The **a priori measure** `∏ₑ dHaar` on configuration space: the product of the Haar probability
measure over all links, the gauge-invariant reference measure before the action weight. -/
noncomputable def aprioriMeasure : Measure (Config d L (Matrix.unitaryGroup n ℂ)) :=
  Measure.pi fun _ : Link d L => haarUnitary

instance : IsProbabilityMeasure (aprioriMeasure (d := d) (L := L) (n := n)) := by
  unfold aprioriMeasure; infer_instance

/-! ## §2  The Boltzmann weight and its regularity -/

/-- The **Boltzmann weight** `exp(−S(U))` of a configuration, as an extended nonnegative real. -/
noncomputable def gibbsDensity (β : ℝ) (U : Config d L (Matrix.unitaryGroup n ℂ)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-wilsonAction β U))

/-- **The Wilson action is continuous** on configuration space: each plaquette holonomy is a product
of link variables, depending continuously on `U` since `U(n)` is a topological group, and trace and
`Re` are continuous. -/
theorem continuous_wilsonAction (β : ℝ) :
    Continuous (wilsonAction (d := d) (L := L) (n := n) β) := by
  unfold wilsonAction
  refine (continuous_finsetSum Finset.univ fun p _ => ?_).const_mul β
  unfold plaquetteAction
  have hval : Continuous fun U : Config d L (Matrix.unitaryGroup n ℂ) =>
      (plaquetteHolonomy U p).val := by unfold plaquetteHolonomy; fun_prop
  have htr : Continuous fun A : Matrix n n ℂ => (Matrix.trace ((1 : Matrix n n ℂ) - A)).re := by
    fun_prop
  exact htr.comp hval

/-- The Boltzmann weight is a genuine measurable density (from continuity of the action). -/
theorem measurable_gibbsDensity (β : ℝ) :
    Measurable (gibbsDensity (d := d) (L := L) (n := n) β) := by
  unfold gibbsDensity
  exact (Real.continuous_exp.comp (continuous_wilsonAction β).neg).measurable.ennreal_ofReal

/-! ## §3  The partition function `Z`, bounded `0 < Z ≤ 1` -/

/-- The **partition function** `Z(β) = ∫ exp(−S) d(aprioriMeasure)`, the Gibbs normalization. -/
noncomputable def partitionFunction (β : ℝ) : ℝ≥0∞ :=
  ∫⁻ U, gibbsDensity (d := d) (L := L) (n := n) β U ∂aprioriMeasure

/-- `Z ≤ 1`, hence finite: from `0 ≤ S` (`wilsonAction_nonneg`) the weight `exp(−S) ≤ 1`. -/
theorem partitionFunction_ne_top {β : ℝ} (hβ : 0 ≤ β) :
    partitionFunction (d := d) (L := L) (n := n) β ≠ ⊤ := by
  have hle : partitionFunction (d := d) (L := L) (n := n) β ≤ 1 := by
    calc partitionFunction β ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂aprioriMeasure :=
          lintegral_mono fun U => by
            rw [gibbsDensity]
            exact ENNReal.ofReal_le_one.mpr
              (Real.exp_le_one_iff.mpr (by linarith [wilsonAction_nonneg hβ U]))
      _ = 1 := by rw [lintegral_const]; simp
  exact ne_top_of_le_ne_top ENNReal.one_ne_top hle

/-- `0 < Z`: from the **uniform** upper bound `S ≤ M` (`wilsonAction_le`) the weight is bounded
below by the positive constant `exp(−M)`. -/
theorem partitionFunction_pos {β : ℝ} (hβ : 0 ≤ β) :
    0 < partitionFunction (d := d) (L := L) (n := n) β := by
  set M : ℝ := β * (Fintype.card (Plaquette d L) * (2 * Fintype.card n)) with _hM
  calc (0 : ℝ≥0∞) < ENNReal.ofReal (Real.exp (-M)) := ENNReal.ofReal_pos.mpr (Real.exp_pos _)
    _ = ∫⁻ _, ENNReal.ofReal (Real.exp (-M)) ∂aprioriMeasure := by rw [lintegral_const]; simp
    _ ≤ partitionFunction β := lintegral_mono fun U => by
        rw [gibbsDensity]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [wilsonAction_le hβ U]))

/-! ## §4  The normalized Gibbs measure -/

/-- The **finite-volume Gibbs measure** `dμ_β = Z⁻¹ exp(−S) ∏ₑ dHaar`. -/
noncomputable def gibbsMeasure (β : ℝ) : Measure (Config d L (Matrix.unitaryGroup n ℂ)) :=
  (partitionFunction (d := d) (L := L) (n := n) β)⁻¹ •
    aprioriMeasure.withDensity (gibbsDensity β)

/-- **The Gibbs measure is a probability measure** (for `β ≥ 0`): `Z⁻¹ · Z = 1`,
using `0 < Z < ∞`. -/
theorem isProbabilityMeasure_gibbsMeasure {β : ℝ} (hβ : 0 ≤ β) :
    IsProbabilityMeasure (gibbsMeasure (d := d) (L := L) (n := n) β) := by
  constructor
  rw [gibbsMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  change (partitionFunction β)⁻¹ * partitionFunction β = 1
  exact ENNReal.inv_mul_cancel (partitionFunction_pos hβ).ne' (partitionFunction_ne_top hβ)

end Spectra.GaugeTheory.Lattice
