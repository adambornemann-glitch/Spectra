/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: SpectralTheory/HerglotzTheorem/Stieltjes/Measure.lean
-/
import Spectra.Herglotz.Stieltjes.Hellys

open MeasureTheory Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Herglotz

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

/-- For a nonneg integrable density `ρ : ℝ → ℝ`, the measure
`volume.withDensity (l ↦ ofReal (ρ l))` equals the Stieltjes measure of its
cumulative distribution `F : a ↦ ∫_{(-∞,a]} ρ`. -/
lemma withDensity_ofReal_eq_stieltjes_measure
    {ρ : ℝ → ℝ} (hρ_nn : ∀ x, 0 ≤ ρ x) (hρ_int : Integrable ρ volume)
    {F : ℝ → ℝ}
    (hF : ∀ a, F a = ∫ l in Set.Iic a, ρ l ∂volume)
    (hF_mono : Monotone F)
    (hF_cont : Continuous F)
    (hF_atBot : Tendsto F atBot (𝓝 0)) :
    volume.withDensity (fun l => ENNReal.ofReal (ρ l)) =
      hF_mono.stieltjesFunction.measure := by
  -- LHS is a finite measure (total mass `= ∫ ρ < ∞`).
  haveI : IsFiniteMeasure (volume.withDensity (fun l => ENNReal.ofReal (ρ l))) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, MeasureTheory.setLIntegral_univ,
        ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hρ_int
            (Filter.Eventually.of_forall hρ_nn)]
    exact ENNReal.ofReal_lt_top
  -- Right-continuous regularization `sf` agrees with `F` everywhere — `F` is continuous.
  have hSF_eq : ∀ x, hF_mono.stieltjesFunction x = F x := fun x =>
    stieltjes_eq_at_continuousAt _ hF_mono x hF_cont.continuousAt
  -- `sf` inherits the `-∞` limit from `F`.
  have hSF_atBot : Tendsto hF_mono.stieltjesFunction atBot (𝓝 0) := by
    rw [show hF_mono.stieltjesFunction = F from funext hSF_eq]; exact hF_atBot
  -- Both measures agree on every `Iic a`; apply uniqueness.
  apply Measure.ext_of_Iic
  intro a
  have hLHS_val : (volume.withDensity (fun l => ENNReal.ofReal (ρ l))) (Set.Iic a)
      = ENNReal.ofReal (F a) := by
    rw [withDensity_apply _ measurableSet_Iic,
        ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            hρ_int.integrableOn (Filter.Eventually.of_forall hρ_nn),
        hF a]
  have hRHS_val : hF_mono.stieltjesFunction.measure (Set.Iic a)
      = ENNReal.ofReal (F a) := by
    rw [StieltjesFunction.measure_Iic _ hSF_atBot, hSF_eq, sub_zero]
  rw [hLHS_val, hRHS_val]

end StieltjesMeasure

end Spectra.Herglotz
