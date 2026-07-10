/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.CayleyTransform.Generator.Resolvent
import Spectra.SpectralTheory.ResolventForm
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
/-!
# `stoneGroup hA = genToGroup hA` and `generator (stoneGroup hA) = A`

The spectral (Cayley/Borel) group and the Yosida group are identified **without** computing the
generator, closing `generator_stoneGroup` non-circularly.  The keystone
`selfAdjointResolvent_eq_borelCalculus` expresses `(A − z)⁻¹` through the Cayley Borel calculus;
a measure pushforward (`borelMeasure_stoneGroup_eq_map`, proved by matching characteristic
functions, both equal to `t ↦ ⟪ξ, e^{itA}ξ⟫`) turns this into a Cauchy-transform identity, and
`measure_ext_of_cauchyTransform` (only needing `Im z > 0`, where `i + z ≠ 0`) collapses the two
groups' spectral measures — hence the groups (`stoneGroup_eq_genToGroup`), hence the generators.
-/
open Complex MeasureTheory Filter Topology InnerProductSpace
open scoped InnerProductSpace
open Spectra.Resolvent Spectra.YosidaHille Spectra.Operator
open Spectra.QuantumMechanics.SpectralTheory Spectra.BorelCFC
open Spectra.OneParameterUnitaryGroup Spectra.Borel
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H}
namespace Spectra.Cayley

/-- Characteristic-function form of `e^{itA}` on the diagonal, against the group's own spectral
(Bochner–Herglotz) measure: `⟪ξ, stoneExp t ξ⟫ = ∫ e^{ilt} dμ_ξ(l)`.  Mirror of
`inner_genToGroup_eq_integral`, via `spectralForm_char` + `spectralForm_self`. -/
theorem inner_stoneExp_eq_integral_borelMeasure (hA : IsSelfAdjoint A) (t : ℝ) (ξ : H) :
    ⟪ξ, stoneExp hA t ξ⟫_ℂ = ∫ l, cexp (I * l * t) ∂(borelMeasure (stoneGroup hA) ξ) := by
  rw [← spectralForm_self (stoneGroup hA) ξ (char_measurable t) (char_bdd t)]
  exact (spectralForm_char (stoneGroup hA) ξ ξ t).symm

/-- The inverse Möbius value as a *real*-valued map on the Cayley spectrum (it is real there). -/
noncomputable def inverseMobiusReal (hA : IsSelfAdjoint A) : spectrum ℂ (cayley hA) → ℝ :=
  fun w => (inverseMobius (w : ℂ)).re

/-- On the Cayley spectrum the real-valued `inverseMobiusReal hA w` agrees with the complex
`inverseMobius (w : ℂ)`, since the latter is real there. -/
lemma inverseMobiusReal_coe (hA : IsSelfAdjoint A) (w : spectrum ℂ (cayley hA)) :
    ((inverseMobiusReal hA w : ℝ) : ℂ) = inverseMobius (w : ℂ) := by
  apply Complex.ext <;>
    simp only [inverseMobiusReal, Complex.ofReal_re, Complex.ofReal_im,
      inverseMobius_im_eq_zero_of_mem_spectrum hA w]

/-- The map `inverseMobiusReal hA` is measurable. -/
lemma inverseMobiusReal_measurable (hA : IsSelfAdjoint A) : Measurable (inverseMobiusReal hA) := by
  have hmob : Measurable (inverseMobius : ℂ → ℂ) := by
    unfold inverseMobius
    exact (measurable_const.mul (measurable_const.add measurable_id)).div
      (measurable_const.sub measurable_id)
  exact Complex.measurable_re.comp (hmob.comp continuous_subtype_val.measurable)

/-- **The pushforward identity.**  The group's `ℝ`-valued spectral measure is the pushforward of
the Cayley-spectrum measure under `inverseMobius`.  Both measures have characteristic function
`t ↦ ⟪ξ, stoneExp t ξ⟫` — the left by `inner_stoneExp_eq_integral_borelMeasure`, the right by
`integral_map` + `inner_stoneExp_self_eq_integral` and `inverseMobiusReal_coe` — so
`Measure.ext_of_charFun` identifies them. -/
theorem borelMeasure_stoneGroup_eq_map (hA : IsSelfAdjoint A) (ξ : H) :
    borelMeasure (stoneGroup hA) ξ
      = Measure.map (inverseMobiusReal hA)
          (Spectra.Riesz.spectralMeasure (cayley hA) (cayley_isStarNormal hA) ξ) := by
  haveI : IsFiniteMeasure (borelMeasure (stoneGroup hA) ξ) :=
    borelMeasure_isFiniteMeasure (stoneGroup hA) ξ
  haveI : IsFiniteMeasure (Measure.map (inverseMobiusReal hA)
      (Spectra.Riesz.spectralMeasure (cayley hA) (cayley_isStarNormal hA) ξ)) := by
    constructor
    rw [Measure.map_apply (inverseMobiusReal_measurable hA) MeasurableSet.univ, Set.preimage_univ]
    exact measure_lt_top _ _
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have hLHS : charFun (borelMeasure (stoneGroup hA) ξ) t = ⟪ξ, stoneExp hA t ξ⟫_ℂ := by
    rw [charFun_apply_real, inner_stoneExp_eq_integral_borelMeasure hA t ξ]
    exact integral_congr_ae (Filter.Eventually.of_forall fun l => by ring_nf)
  have hRHS : charFun (Measure.map (inverseMobiusReal hA)
      (Spectra.Riesz.spectralMeasure (cayley hA) (cayley_isStarNormal hA) ξ)) t
      = ⟪ξ, stoneExp hA t ξ⟫_ℂ := by
    rw [charFun_apply_real,
      integral_map (inverseMobiusReal_measurable hA).aemeasurable (by fun_prop),
      inner_stoneExp_self_eq_integral hA t ξ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have hexp : (↑t * (↑(inverseMobiusReal hA w) : ℂ) * I) = I * ↑t * inverseMobius (w : ℂ) := by
      rw [inverseMobiusReal_coe hA w]; ring
    simp only [stoneExpSymbol]
    rw [hexp]
  rw [hLHS, hRHS]

end Spectra.Cayley
