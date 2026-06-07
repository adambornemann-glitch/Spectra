/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: SpectralTheory/HerglotzTheorem/Stieltjes/Measure.lean
-/
import Spectra.SpectralTheory.HerglotzTheorem.Stieltjes.Hellys

namespace QuantumMechanics.SpectralTheory.HerglotzStieltjes

open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### From Helly limit to Stieltjes measure -/

section StieltjesMeasure

/-- Given the Helly limit `G` (monotone, bounded), produce a
`StieltjesFunction` and its associated measure.

The key: `Monotone.stieltjesFunction` right-regularizes `G` and
packages it as a `StieltjesFunction`. Then `.measure` gives the
Borel measure. -/
noncomputable def hellyLimitMeasure (G : ℝ → ℝ) (h_mono : Monotone G) :
    Measure ℝ :=
  (h_mono.stieltjesFunction).measure

/-- The Stieltjes measure satisfies `μ(Ioc a b) = G(b) - G(a)` at
continuity points.

More precisely, `Monotone.stieltjesFunction` right-regularizes `G`,
so `μ(Ioc a b) = ofReal (G⁺(b) - G⁺(a))` where `G⁺` is the
right-continuous version. At continuity points, `G⁺ = G`. -/
lemma hellyLimitMeasure_Ioc (G : ℝ → ℝ) (h_mono : Monotone G)
    (a b : ℝ) :
    (hellyLimitMeasure G h_mono) (Set.Ioc a b) =
    ENNReal.ofReal (h_mono.stieltjesFunction b - h_mono.stieltjesFunction a) :=
  StieltjesFunction.measure_Ioc _ a b

/-- At continuity points of `G`, the Stieltjes regularization agrees with `G`. -/
lemma stieltjes_eq_at_continuousAt (G : ℝ → ℝ) (h_mono : Monotone G)
    (x : ℝ) (hx : ContinuousAt G x) :
    h_mono.stieltjesFunction x = G x := by
  rw [h_mono.stieltjesFunction_eq]
  exact (h_mono.continuousWithinAt_Ioi_iff_rightLim_eq).mp hx.continuousWithinAt

end StieltjesMeasure

end HerglotzStieltjes
