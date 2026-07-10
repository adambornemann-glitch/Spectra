/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Spectra.Bochner.GNS.Representation.StronglyCont

/-!
# The GNS Unitary Group

This file assembles the `GNSUnitaryGroup f` witness: the translation representation, transported
through the quotient and its completion in `Representation/Lemmas.lean`, is here upgraded to a
bundled `H →L[ℂ] H`-valued group of isometries and packaged together with the strong-continuity
and compatibility facts proved in `Representation/StronglyCont.lean`.

## Main definitions

* `gnsUnitaryConstruction` — builds the `GNSUnitaryGroup f` witness from a continuous,
  positive-definite, Hermitian-symmetric `f`.

## Implementation notes

Construction outline:
1. `translate t` preserves `N` (by `pdNullSpace_translate_invariant`),
   so it descends to a map `U₀(t)` on the quotient `V = (ℝ →₀ ℂ)/N`.
2. `U₀(t)` is an isometry of `V` (by `pdInner_translate`).
3. Every isometry of a pre-Hilbert space extends uniquely to an isometry
   of the completion (`UniformSpace.Completion.map` with uniform continuity).
4. Group law and identity follow from `translate_translate` and `translate_zero`.
5. Strong continuity is `completionTranslate_strong_continuous` (`StronglyCont.lean`).
6. Each `completionTranslate t` is already known to preserve the inner product
   (`completionTranslate_inner`), so `LinearMap.isometryOfInner` upgrades it to a
   `LinearIsometry` and `.toContinuousLinearMap` bundles it as `H →L[ℂ] H` — the type
   `GNSUnitaryGroup.unitaryAction` expects — right here at construction time.

## References

* Reed–Simon, *Methods of Modern Mathematical Physics I*, §VIII.5 (Gelfand–Naimark–Segal
  construction)
-/
namespace Spectra.Bochner.GNS

/-- **Existence of the GNS unitary group.** See the module docstring for the construction outline.
-/
noncomputable def gnsUnitaryConstruction {f : ℝ → ℂ}
    (hf : IsContinuous f) :
    GNSUnitaryGroup f := by
  set gns := gnsConstruction hf.pd hf.hermitian
  -- Same `GNSData` instance triple as `ToStone.lean`'s `toOneParameterUnitaryGroup`; both need
  -- `gns.H`'s Hilbert-space structure in scope to state and build the `GNSUnitaryGroup` fields.
  letI := gns.instNACG
  letI := gns.instIPS
  haveI := gns.instComplete
  set Uc : ℝ → (gns.H →L[ℂ] gns.H) :=
    fun t => ((completionTranslate hf.pd hf.hermitian t).isometryOfInner
      (completionTranslate_inner hf.pd hf.hermitian t)).toContinuousLinearMap
  exact {
    toGNSData := gns
    unitaryAction := Uc
    isometry := fun t ψ φ => by
      simp only [Uc, LinearIsometry.coe_toContinuousLinearMap, LinearMap.coe_isometryOfInner]
      exact completionTranslate_inner hf.pd hf.hermitian t ψ φ
    -- `completionTranslate_comp` states `U(s)(U(t)ψ) = U(s+t)ψ`; `group_law` wants
    -- `U(s+t)ψ = U(s)(U(t)ψ)`, hence the `.symm`.
    group_law := fun s t ψ => by
      simp only [Uc, LinearIsometry.coe_toContinuousLinearMap, LinearMap.coe_isometryOfInner]
      exact (completionTranslate_comp hf.pd hf.hermitian s t ψ).symm
    identity := fun ψ => by
      simp only [Uc, LinearIsometry.coe_toContinuousLinearMap, LinearMap.coe_isometryOfInner]
      exact completionTranslate_zero hf.pd hf.hermitian ψ
    strong_continuous := fun ψ => by
      exact (completionTranslate_strong_continuous hf.pd hf.hermitian hf ψ).congr fun t => by
        simp only [Uc, LinearIsometry.coe_toContinuousLinearMap, LinearMap.coe_isometryOfInner]
        rfl
    compat := fun t α => by
      simp only [Uc, LinearIsometry.coe_toContinuousLinearMap, LinearMap.coe_isometryOfInner]
      exact completionTranslate_compat hf.pd hf.hermitian t α
  }

end Spectra.Bochner.GNS
