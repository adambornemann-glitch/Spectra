/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: CayleyTransform/GeneratorStone.lean
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
open Spectra.Resolvent Spectra.Stoneslemma Spectra.QuantumMechanics.Observable
open Spectra.QuantumMechanics.SpectralTheory Spectra.BorelCFC Spectra.StonesTheorem
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

lemma inverseMobiusReal_coe (hA : IsSelfAdjoint A) (w : spectrum ℂ (cayley hA)) :
    ((inverseMobiusReal hA w : ℝ) : ℂ) = inverseMobius (w : ℂ) := by
  apply Complex.ext <;>
    simp only [inverseMobiusReal, Complex.ofReal_re, Complex.ofReal_im,
      inverseMobius_im_eq_zero_of_mem_spectrum hA w]

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

/-- Two one-parameter groups with the same evolution `U` are equal (the other fields are Props). -/
lemma group_ext_of_U {V W : OneParameterUnitaryGroup (H := H)} (h : V.U = W.U) : V = W := by
  obtain ⟨Vu, hV1, hV2, hV3, hV4⟩ := V
  obtain ⟨Wu, hW1, hW2, hW3, hW4⟩ := W
  subst h
  rfl

/-- **The two spectral measures coincide.**  Cauchy transforms agree on `Im z > 0`: the left
equals `⟪ξ, (A − z)⁻¹ ξ⟫` by the pushforward + the keystone (`i + z ≠ 0` there), the right by
`spectralPVM_resolvent_formula`; `measure_ext_of_cauchyTransform` finishes. -/
theorem borelMeasure_stoneGroup_eq_genToGroup [Nontrivial H] (hA : IsSelfAdjoint A) (ξ : H) :
    borelMeasure (stoneGroup hA) ξ = borelMeasure (genToGroup hA) ξ := by
  haveI : IsFiniteMeasure (borelMeasure (stoneGroup hA) ξ) := borelMeasure_isFiniteMeasure _ _
  haveI : IsFiniteMeasure (borelMeasure (genToGroup hA) ξ) := borelMeasure_isFiniteMeasure _ _
  refine measure_ext_of_cauchyTransform _ _ fun z hz_pos => ?_
  have hzne : z.im ≠ 0 := hz_pos.ne'
  have hzi : I + z ≠ 0 := by
    intro h
    have him : (1 : ℝ) + z.im = 0 := by
      have h2 := congrArg Complex.im h
      simpa [Complex.add_im, Complex.I_im] using h2
    linarith
  have hzr : ∀ x : ℝ, ((x : ℂ) - z) ≠ 0 := fun x hx => by
    rw [sub_eq_zero] at hx
    exact hzne (by rw [← hx, Complex.ofReal_im])
  have hcont : Continuous (fun x : ℝ => ((x : ℂ) - z)⁻¹) :=
    (Complex.continuous_ofReal.sub continuous_const).inv₀ hzr
  have hLHS : (∫ x, ((x : ℂ) - z)⁻¹ ∂(borelMeasure (stoneGroup hA) ξ))
      = ⟪ξ, selfAdjointResolvent hA z hzne ξ⟫_ℂ := by
    rw [borelMeasure_stoneGroup_eq_map hA ξ,
      integral_map (inverseMobiusReal_measurable hA).aemeasurable hcont.aestronglyMeasurable,
      selfAdjointResolvent_eq_borelCalculus hA z hzne hzi,
      inner_borelCalculus_self (cayley hA) (cayley_isStarNormal hA) (resolventSymbol hA z)
        (resolventSymbol_measurable hA z) (resolventSymbol_bdd hA z hzne)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [resolventSymbol]
    rw [inverseMobiusReal_coe hA w]
  have hRHS : (∫ x, ((x : ℂ) - z)⁻¹ ∂(borelMeasure (genToGroup hA) ξ))
      = ⟪ξ, selfAdjointResolvent hA z hzne ξ⟫_ℂ := by
    rw [← spectralPVM_diag hA]
    exact (spectralPVM_resolvent_formula hA z hzne ξ).symm
  rw [hLHS, hRHS]

/-- **The spectral evolution equals the Yosida evolution.**  Equal spectral measures give equal
characteristic integrals `⟪ξ, e^{itA} ξ⟫`, and complex polarization (`ext_inner_map`) lifts that
to operator equality. -/
theorem stoneExp_eq_genToGroup [Nontrivial H] (hA : IsSelfAdjoint A) (t : ℝ) :
    stoneExp hA t = (genToGroup hA).U t := by
  have hdiag : ∀ ξ, ⟪ξ, stoneExp hA t ξ⟫_ℂ = ⟪ξ, (genToGroup hA).U t ξ⟫_ℂ := fun ξ => by
    rw [inner_stoneExp_eq_integral_borelMeasure hA t ξ, borelMeasure_stoneGroup_eq_genToGroup hA ξ,
      inner_genToGroup_eq_integral hA t ξ, spectralPVM_diag]
  refine ContinuousLinearMap.coe_injective ((ext_inner_map _ _).mp fun ξ => ?_)
  show ⟪stoneExp hA t ξ, ξ⟫_ℂ = ⟪(genToGroup hA).U t ξ, ξ⟫_ℂ
  rw [← inner_conj_symm (stoneExp hA t ξ) ξ, ← inner_conj_symm ((genToGroup hA).U t ξ) ξ, hdiag ξ]

/-- **The spectral group is the Yosida group.**  `stoneGroup hA = genToGroup hA`, proved with no
generator (the consistency of the two constructions of `e^{itA}`). -/
theorem stoneGroup_eq_genToGroup [Nontrivial H] (hA : IsSelfAdjoint A) : stoneGroup hA = genToGroup hA :=
  group_ext_of_U (funext (stoneExp_eq_genToGroup hA))

/-- **The generator of the spectral group is `A`.** -/
theorem generator_stoneGroup [Nontrivial H] (hA : IsSelfAdjoint A) : generator (stoneGroup hA) = A := by
  rw [stoneGroup_eq_genToGroup hA]; exact generator_genToGroup hA

/-- The difference-quotient limit defining the generator, now a corollary of
`generator_stoneGroup`. -/
theorem stoneExp_genDiffQuot_tendsto [Nontrivial H] (hA : IsSelfAdjoint A) (ψ : H) (hψ : ψ ∈ A.domain) :
    Tendsto (genDiffQuot (stoneGroup hA) ψ) (𝓝[≠] (0 : ℝ)) (𝓝 (A ⟨ψ, hψ⟩)) := by
  have hψgen : ψ ∈ (generator (stoneGroup hA)).domain := by
    rw [generator_stoneGroup hA]; exact hψ
  have hval : generator (stoneGroup hA) ⟨ψ, hψgen⟩ = A ⟨ψ, hψ⟩ :=
    (le_of_eq (generator_stoneGroup hA)).2 (x := ⟨ψ, hψgen⟩) (y := ⟨ψ, hψ⟩) rfl
  rw [← hval]
  exact generator_tendsto (stoneGroup hA) ⟨ψ, hψgen⟩

end Spectra.Cayley
