/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Integral.GroupIntegration

/-!
# Helper Lemmas for Generator Limits

Shared analytical lemmas used by the general-`z` resolvent-integral development
(`Resolvent.Diagonal.IntegralZ`) when proving that the resolvent integrals lie in the
generator domain. The content here is pure real-analysis and measure-theory scaffolding — nothing
from the unitary-group apparatus in `Resolvent.Integral.GroupIntegration` is used directly — but the
import is kept for the ambient `NormedAddCommGroup`/measure-space instances it brings in
transitively; narrowing it to the exact mathlib files needed is future cleanup, not done here.

## Main statements

* `tendsto_exp_sub_one_div`: `(e^h - 1)/h → 1` as `h → 0`. This is the `z = -i` specialization used
  informally by `Diagonal/IntegralZ/Tendsto.lean`'s complex generalization
  `tendsto_cexp_mul_sub_one_div`, though that lemma currently reproves the fact from scratch rather
  than invoking this one.
* `integrableOn_Ici_of_Ici_zero`: integrability on `[0,∞)` extends to every half-line `[b,∞)`.
* `integral_Ici_split_of`: split a half-line integral as `∫_{(a,b]} f + ∫_{[b,∞)} f`. Consumed by
  `integral_Ici_orbit_split_Z` in `Resolvent/Diagonal/IntegralZ/Shift.lean`.

## Tags

generator, limit, exponential, integral
-/
open MeasureTheory Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Resolvent

section Helpers

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- The difference quotient `(e^h - 1)/h → 1` as `h → 0` along `𝓝[≠] 0`. -/
lemma tendsto_exp_sub_one_div :
    Tendsto (fun h : ℝ => (Real.exp h - 1) / h) (𝓝[≠] 0) (𝓝 1) := by
  have h : HasDerivAt Real.exp 1 0 := by
    convert Real.hasDerivAt_exp 0 using 1
    exact Real.exp_zero.symm
  rw [hasDerivAt_iff_tendsto_slope] at h
  convert h using 1
  ext y
  simp only [slope, Real.exp_zero, sub_zero, vsub_eq_sub, smul_eq_mul]
  exact div_eq_inv_mul (Real.exp y - 1) y

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- A continuous `f` integrable on `[0,∞)` is integrable on every half-line `[b,∞)`. -/
lemma integrableOn_Ici_of_Ici_zero {f : ℝ → H} (hcont : Continuous f)
    (h0 : IntegrableOn f (Set.Ici 0)) (b : ℝ) :
    IntegrableOn f (Set.Ici b) := by
  rcases le_or_gt 0 b with hb | hb
  · exact h0.mono_set (Set.Ici_subset_Ici.mpr hb)
  · rw [← Set.Ico_union_Ici_eq_Ici hb.le]
    exact (hcont.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self).union h0

omit [CompleteSpace H] in
/-- For `a ≤ b`, the half-line integral of `f` splits as `∫_{(a,b]} f + ∫_{[b,∞)} f`. -/
lemma integral_Ici_split_of {f : ℝ → H} (hcont : Continuous f)
    (h0 : IntegrableOn f (Set.Ici 0)) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in Set.Ici a, f t = (∫ t in Set.Ioc a b, f t) + ∫ t in Set.Ici b, f t := by
  have h_ae_eqa : ∫ t in Set.Ici a, f t = ∫ t in Set.Ioi a, f t :=
    setIntegral_congr_set Ioi_ae_eq_Ici.symm
  have h_ae_eqb : ∫ t in Set.Ici b, f t = ∫ t in Set.Ioi b, f t :=
    setIntegral_congr_set Ioi_ae_eq_Ici.symm
  have h_union : Set.Ioi a = Set.Ioc a b ∪ Set.Ioi b := (Set.Ioc_union_Ioi_eq_Ioi hab).symm
  rw [h_ae_eqa, h_union,
      setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        ((integrableOn_Ici_of_Ici_zero hcont h0 b).mono_set Set.Ioi_subset_Ici_self),
      h_ae_eqb.symm]

end Spectra.Resolvent.Helpers
