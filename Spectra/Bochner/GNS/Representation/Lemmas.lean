/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Bochner.GNS.Representation.UnitaryGroup

/-!
# Descending Translation to the GNS Quotient and its Completion

This file transports the translation action `translate t` on `ℝ →₀ ℂ` through the two stages of
the GNS construction: first to the pre-Hilbert quotient `GNSQuotient hPD hH`
(`quotientTranslate`), then to its Cauchy completion (`completionTranslate`), proving at each
stage that the result is a group action by linear isometries (group law, identity, norm/inner
preservation).

## Main definitions

* `quotientTranslate` — `translate t` descended to `GNSQuotient hPD hH` via `Submodule.mapQ`.
* `quotientTranslateLI` — `quotientTranslate t` bundled as a linear isometry.
* `completionTranslate` — `quotientTranslate t` extended to `UniformSpace.Completion` by density.

## Main statements

* `quotientTranslate_inner`, `quotientTranslate_norm` — `quotientTranslate t` preserves the
  inner product and the norm.
* `quotientTranslate_comp`, `quotientTranslate_zero` — the group law `U₀(s) ∘ U₀(t) = U₀(s+t)`
  and identity `U₀(0) = id` on the quotient.
* `completionTranslate_comp`, `completionTranslate_zero`, `completionTranslate_inner` — the same
  trio, transported to the completion.
* `completionTranslate_compat` — `U(t) ∘ embed = embed ∘ translate t`, i.e. the completion-level
  action agrees with `translate` under the GNS embedding.

## Implementation notes

The completion-level lemmas (`completionTranslate` itself and its `_comp`/`_zero`/`_inner`
companions) all follow the same pattern: prove the fact on the dense image of `GNSQuotient hPD hH`
inside `UniformSpace.Completion (GNSQuotient hPD hH)` (where it reduces to the corresponding
quotient-level lemma), then extend to the whole completion via
`UniformSpace.Completion.induction_on(₂)`, whose side goal `isClosed_eq` discharges the
"the equality locus is closed" obligation the density argument needs.

Every lemma here needs the `NormedAddCommGroup`/`InnerProductSpace` structure on
`GNSQuotient hPD hH` in scope; these are deliberately not global instances (see
`Hilbert/Constructor.lean`'s docstring on `gnsQuotientNACG`/`gnsQuotientIPS` for why), so each
statement and proof brings them into scope with `letI := gnsQuotientNACG hPD hH` /
`letI := gnsQuotientIPS hPD hH` rather than re-deriving them from `quotientCore` by hand.

## References

* Reed–Simon, *Methods of Modern Mathematical Physics I*, §VIII.5 (Gelfand–Naimark–Segal
  construction)
-/
open Spectra.PositiveDefinite
namespace Spectra.Bochner.GNS

/-- `translate t` as a ℂ-linear map on `ℝ →₀ ℂ`. -/
noncomputable def translateLM (t : ℝ) : (ℝ →₀ ℂ) →ₗ[ℂ] (ℝ →₀ ℂ) where
  toFun := translate t
  map_add' := translate_add t
  map_smul' := translate_smul t

/-- Translation preserves the null submodule (needed for `Submodule.mapQ`). -/
lemma translateLM_preserves_null {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    pdNullSubmodule hPD hH ≤ (pdNullSubmodule hPD hH).comap (translateLM t) := by
  intro α hα
  exact pdNullSpace_translate_invariant hα t

/-- Translation descended to the GNS quotient via `Submodule.mapQ`. -/
noncomputable def quotientTranslate {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    GNSQuotient hPD hH →ₗ[ℂ] GNSQuotient hPD hH :=
  Submodule.mapQ _ _ (translateLM t) (translateLM_preserves_null hPD hH t)

/-- Computation rule: `quotientTranslate` on a representative. -/
@[simp]
lemma quotientTranslate_mk {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) (α : ℝ →₀ ℂ) :
    quotientTranslate hPD hH t (Submodule.Quotient.mk α) =
    Submodule.Quotient.mk (translate t α) := rfl

/-- Isometry: `quotientTranslate t` preserves `quotientInner`. -/
lemma quotientTranslate_inner {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ)
    (x y : GNSQuotient hPD hH) :
    quotientInner hPD hH (quotientTranslate hPD hH t x)
                         (quotientTranslate hPD hH t y) =
    quotientInner hPD hH x y := by
  induction x using Submodule.Quotient.induction_on with | _ a =>
  induction y using Submodule.Quotient.induction_on with | _ b =>
  simp only [quotientTranslate_mk, quotientInner_mk]
  exact pdInner_translate t a b

/-- Group law: `U₀(s) ∘ U₀(t) = U₀(s + t)` on the quotient. -/
lemma quotientTranslate_comp {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (s t : ℝ)
    (x : GNSQuotient hPD hH) :
    quotientTranslate hPD hH s (quotientTranslate hPD hH t x) =
    quotientTranslate hPD hH (s + t) x := by
  induction x using Submodule.Quotient.induction_on with | _ a =>
  simp only [quotientTranslate_mk]
  congr 1
  exact translate_translate s t a

/-- Identity: `U₀(0) = id` on the quotient. -/
lemma quotientTranslate_zero {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f)
    (x : GNSQuotient hPD hH) :
    quotientTranslate hPD hH 0 x = x := by
  induction x using Submodule.Quotient.induction_on with | _ a =>
  simp only [quotientTranslate_mk, translate_zero]

/-- `quotientTranslate t` preserves the norm. -/
lemma quotientTranslate_norm {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ)
    (x : GNSQuotient hPD hH) :
    letI := gnsQuotientNACG hPD hH
    letI := gnsQuotientIPS hPD hH
    ‖quotientTranslate hPD hH t x‖ = ‖x‖ := by
  letI nacgV := gnsQuotientNACG hPD hH
  letI ipsV := gnsQuotientIPS hPD hH
  have h_inner : @inner ℂ _ ipsV.toInner
      (quotientTranslate hPD hH t x) (quotientTranslate hPD hH t x) =
      @inner ℂ _ ipsV.toInner x x := by
    induction x using Submodule.Quotient.induction_on with | _ a =>
    change quotientInner hPD hH _ _ = quotientInner hPD hH _ _
    simp only [quotientTranslate_mk, quotientInner_mk]
    exact pdInner_translate t a a
  have h_sq : ‖quotientTranslate hPD hH t x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ]
    exact congrArg RCLike.re h_inner
  have hfact : (‖quotientTranslate hPD hH t x‖ - ‖x‖) *
               (‖quotientTranslate hPD hH t x‖ + ‖x‖) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfact with h | h
  · linarith
  · linarith [norm_nonneg (quotientTranslate hPD hH t x), norm_nonneg x]

/-- `quotientTranslate t` as a linear isometry on the GNS quotient. -/
noncomputable def quotientTranslateLI {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    letI := gnsQuotientNACG hPD hH
    letI := gnsQuotientIPS hPD hH
    GNSQuotient hPD hH →ₗᵢ[ℂ] GNSQuotient hPD hH := by
  letI := gnsQuotientNACG hPD hH
  letI := gnsQuotientIPS hPD hH
  exact ⟨quotientTranslate hPD hH t, quotientTranslate_norm hPD hH t⟩

/-- Uniform continuity of `quotientTranslate` (isometries are uniformly continuous). -/
lemma quotientTranslate_uniformContinuous {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    letI := gnsQuotientNACG hPD hH
    letI := gnsQuotientIPS hPD hH
    UniformContinuous (quotientTranslate hPD hH t) := by
  letI := gnsQuotientNACG hPD hH
  letI := gnsQuotientIPS hPD hH
  exact (quotientTranslateLI hPD hH t).isometry.uniformContinuous

/-- `ContinuousAdd` on the completion of the GNS quotient, packaged once for reuse: every
proof that needs it would otherwise re-derive it from `IsUniformAddGroup` by hand. -/
lemma gnsCompletion_continuousAdd {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) :
    letI := gnsQuotientNACG hPD hH
    letI := gnsQuotientIPS hPD hH
    ContinuousAdd (UniformSpace.Completion (GNSQuotient hPD hH)) := by
  letI := gnsQuotientNACG hPD hH
  letI := gnsQuotientIPS hPD hH
  letI : AddGroup (UniformSpace.Completion (GNSQuotient hPD hH)) := inferInstance
  letI : IsUniformAddGroup (UniformSpace.Completion (GNSQuotient hPD hH)) := inferInstance
  exact IsTopologicalAddGroup.toContinuousAdd

/-- Translation extended to the GNS completion as a ℂ-linear map.
    Linearity proved by density: `Completion.map` preserves add/smul
    because it agrees with the linear `quotientTranslate` on the dense image. -/
noncomputable def completionTranslate {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    letI := gnsQuotientNACG hPD hH
    letI := gnsQuotientIPS hPD hH
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    UniformSpace.Completion (GNSQuotient hPD hH) →ₗ[ℂ]
    UniformSpace.Completion (GNSQuotient hPD hH) := by
  letI nacgV := gnsQuotientNACG hPD hH
  letI _ipsV := gnsQuotientIPS hPD hH
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  have huc : UniformContinuous (quotientTranslate hPD hH t) :=
    quotientTranslate_uniformContinuous hPD hH t
  -- Pre-wire the completion-level `ContinuousAdd` instance so nested by-blocks see it
  haveI := gnsCompletion_continuousAdd hPD hH
  exact {
    toFun := UniformSpace.Completion.map (quotientTranslate hPD hH t)
    map_add' := fun x y => by
      refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
      · apply isClosed_eq
        · exact UniformSpace.Completion.continuous_map.comp continuous_add
        · haveI := gnsCompletion_continuousAdd hPD hH
          exact continuous_add.comp
            ((UniformSpace.Completion.continuous_map.comp continuous_fst).prodMk
             (UniformSpace.Completion.continuous_map.comp continuous_snd))
      · intro a b
        simp only [← UniformSpace.Completion.coe_add,
                   UniformSpace.Completion.map_coe huc, map_add]
    map_smul' := fun c x => by
      refine UniformSpace.Completion.induction_on x ?_ ?_
      · apply isClosed_eq
        · exact UniformSpace.Completion.continuous_map.comp (continuous_const_smul c)
        · exact (continuous_const_smul c).comp UniformSpace.Completion.continuous_map
      · intro a
        simp only [← UniformSpace.Completion.coe_smul,
                   UniformSpace.Completion.map_coe huc, map_smul]
        rfl
  }

/-- Computation rule: `completionTranslate` on a coerced quotient element. -/
@[simp]
lemma completionTranslate_coe {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ)
    (a : GNSQuotient hPD hH) :
    letI := gnsQuotientNACG hPD hH
    letI := gnsQuotientIPS hPD hH
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    completionTranslate hPD hH t ↑a =
    ↑(quotientTranslate hPD hH t a) := by
  letI := gnsQuotientNACG hPD hH
  letI := gnsQuotientIPS hPD hH
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  change UniformSpace.Completion.map (quotientTranslate hPD hH t) ↑a = _
  exact UniformSpace.Completion.map_coe
    (quotientTranslate_uniformContinuous hPD hH t) a

/-- `completionTranslate t` is continuous, directly from `Completion.map`'s unconditional
continuity — packaged for reuse wherever a continuity side-goal needs it by name. -/
lemma completionTranslate_continuous {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    letI := gnsQuotientNACG hPD hH
    letI := gnsQuotientIPS hPD hH
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    Continuous (completionTranslate hPD hH t) := by
  letI := gnsQuotientNACG hPD hH
  letI := gnsQuotientIPS hPD hH
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  exact UniformSpace.Completion.continuous_map

/-- Group law on the completion: U(s)(U(t)(ψ)) = U(s+t)(ψ). -/
lemma completionTranslate_comp {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (s t : ℝ) :
    letI := gnsQuotientNACG hPD hH
    letI := gnsQuotientIPS hPD hH
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    ∀ (ψ : UniformSpace.Completion (GNSQuotient hPD hH)),
    completionTranslate hPD hH s (completionTranslate hPD hH t ψ) =
    completionTranslate hPD hH (s + t) ψ := by
  letI := gnsQuotientNACG hPD hH
  letI := gnsQuotientIPS hPD hH
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  intro ψ
  refine UniformSpace.Completion.induction_on ψ ?_ ?_
  · apply isClosed_eq
    · exact UniformSpace.Completion.continuous_map.comp UniformSpace.Completion.continuous_map
    · exact UniformSpace.Completion.continuous_map
  · intro a
    rw [completionTranslate_coe, completionTranslate_coe, completionTranslate_coe]
    congr 1
    exact quotientTranslate_comp hPD hH s t a

/-- Identity on the completion: U(0)(ψ) = ψ. -/
lemma completionTranslate_zero {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) :
    letI := gnsQuotientNACG hPD hH
    letI := gnsQuotientIPS hPD hH
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    ∀ (ψ : UniformSpace.Completion (GNSQuotient hPD hH)),
    completionTranslate hPD hH 0 ψ = ψ := by
  letI := gnsQuotientNACG hPD hH
  letI := gnsQuotientIPS hPD hH
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  intro ψ
  refine UniformSpace.Completion.induction_on ψ ?_ ?_
  · apply isClosed_eq
    · exact UniformSpace.Completion.continuous_map
    · exact continuous_id
  · intro a
    rw [completionTranslate_coe]
    simp only [quotientTranslate_zero]

/-- Isometry on the completion: ⟨U(t)ψ, U(t)φ⟩ = ⟨ψ, φ⟩. -/
lemma completionTranslate_inner {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    letI := gnsQuotientNACG hPD hH
    letI := gnsQuotientIPS hPD hH
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    ∀ (ψ φ : UniformSpace.Completion (GNSQuotient hPD hH)),
    @inner ℂ _ InnerProductSpace.toInner
      (completionTranslate hPD hH t ψ) (completionTranslate hPD hH t φ) =
    @inner ℂ _ InnerProductSpace.toInner ψ φ := by
  letI := gnsQuotientNACG hPD hH
  letI := gnsQuotientIPS hPD hH
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  intro ψ φ
  refine UniformSpace.Completion.induction_on₂ ψ φ ?_ ?_
  · apply isClosed_eq
    · haveI := gnsCompletion_continuousAdd hPD hH
      have hcont_pair :
          Continuous (fun (p : UniformSpace.Completion _ × UniformSpace.Completion _) =>
            (completionTranslate hPD hH t p.1, completionTranslate hPD hH t p.2)) :=
        ((completionTranslate_continuous hPD hH t).comp continuous_fst).prodMk
          ((completionTranslate_continuous hPD hH t).comp continuous_snd)
      exact (@continuous_inner ℂ _ _ _ _).comp hcont_pair
    · exact @continuous_inner ℂ _ _ _ _
  · intro a b
    rw [completionTranslate_coe, completionTranslate_coe]
    simp only [UniformSpace.Completion.inner_coe]
    exact quotientTranslate_inner hPD hH t a b

/-- Compatibility: U(t) ∘ embed = embed ∘ translate(t) on the completion. -/
lemma completionTranslate_compat {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) (α : ℝ →₀ ℂ) :
    letI := gnsQuotientNACG hPD hH
    letI := gnsQuotientIPS hPD hH
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    let emb := (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ)).toLinearMap.comp
                 (pdNullSubmodule hPD hH).mkQ
    completionTranslate hPD hH t (emb α) = emb (translate t α) := by
  letI := gnsQuotientNACG hPD hH
  letI := gnsQuotientIPS hPD hH
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  change completionTranslate hPD hH t
    (↑(Submodule.Quotient.mk (p := pdNullSubmodule hPD hH) α)) =
    ↑(Submodule.Quotient.mk (p := pdNullSubmodule hPD hH) (translate t α))
  rw [completionTranslate_coe, quotientTranslate_mk]

end Spectra.Bochner.GNS
