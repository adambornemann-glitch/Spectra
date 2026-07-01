/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: StoneBridge/Basic.lean
-/
import Spectra.CayleyTransform.Generator.Stone         -- stoneGroup, stoneExp, generator_stoneGroup
import Spectra.YosidaHille.Basic                             -- genToGroup, generator_genToGroup, stoneEquiv
                                                       --   (⚠ the module with `Spectra.YosidaHille`;
                                                       --    you have been importing it as Stone.Basic)
/-!
# Stone's theorem as a bijection, spectrally — and its agreement with the Yosida bijection

`stoneEquivSpectral` is Stone's theorem stated as an equivalence

  `OneParameterUnitaryGroup H ≃ {A // IsSelfAdjoint A}`,

with the inverse map furnished by the **Cayley/Borel** construction `stoneGroup`.  It is built
from `generator_stoneGroup` alone and mentions `genToGroup` nowhere: it is a self-contained
statement of the correspondence.

The bridge proper is `§3`: the spectral equivalence is *the same* equivalence as the Yosida
`stoneEquiv`.  The forward maps are identical on the nose — both send a group to its generator —
so the equality is `Equiv.ext` with `rfl`; the content sits in the inverse maps, where their
agreement is exactly `stoneGroup_eq_genToGroup` (`§1`), itself a one-line consequence of the two
*independent* generator computations `generator_stoneGroup` and `generator_genToGroup`.

`genToGroup` appears only in `§1` and `§3` — the comparison.  `stoneEquivSpectral` itself does not
depend on it.
-/
open InnerProductSpace Complex Filter Topology
open Spectra Spectra.OneParameterUnitaryGroup Spectra.Resolvent Spectra.YosidaHille Spectra.Cayley
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H}
namespace Spectra.YosidaHille

/-! ## §1  Consistency of the two constructions of `e^{itA}` -/

/-- The spectral group equals the Yosida group, from equal generators.  No spectral-measure
comparison: both `generator_stoneGroup` and `generator_genToGroup` were established
independently, and `group_unique` does the rest. -/
theorem stoneGroup_eq_genToGroup [Nontrivial H] (hA : IsSelfAdjoint A) :
    stoneGroup hA = genToGroup hA :=
  group_unique _ _ (by rw [generator_stoneGroup hA, generator_genToGroup hA])

theorem stoneExp_eq_genToGroup [Nontrivial H] (hA : IsSelfAdjoint A) (t : ℝ) :
    stoneExp hA t = (genToGroup hA).U t := by
  rw [show stoneExp hA t = (stoneGroup hA).U t from rfl, stoneGroup_eq_genToGroup hA]

/-! ## §2  Stone's theorem as a bijection, via the spectral construction -/

/-- **Stone's theorem (spectral form).**  The bijective correspondence between strongly
continuous one-parameter unitary groups and self-adjoint operators, with the inverse map given
by the Cayley/Borel construction `stoneGroup`.  Identical shape to `stoneEquiv`, with
`genToGroup ↦ stoneGroup` and `generator_genToGroup ↦ generator_stoneGroup`.

Requires `Nontrivial H` (inherited from `generator_stoneGroup`, hence from the keystone resolvent
identity). -/
noncomputable def stoneEquivSpectral [Nontrivial H] :
    OneParameterUnitaryGroup (H := H) ≃ {A : H →ₗ.[ℂ] H // IsSelfAdjoint A} where
  toFun  U := ⟨generator U, generator_isSelfAdjoint U⟩
  invFun A := stoneGroup A.2
  left_inv  U := group_unique _ _ (generator_stoneGroup (generator_isSelfAdjoint U))
  right_inv A := Subtype.ext (generator_stoneGroup A.2)

@[simp] lemma stoneEquivSpectral_apply [Nontrivial H] (U : OneParameterUnitaryGroup (H := H)) :
    (stoneEquivSpectral U : H →ₗ.[ℂ] H) = generator U := rfl

@[simp] lemma stoneEquivSpectral_symm_apply [Nontrivial H] (hA : IsSelfAdjoint A) :
    stoneEquivSpectral.symm ⟨A, hA⟩ = stoneGroup hA := rfl

@[simp] lemma stoneEquivSpectral_symm_U [Nontrivial H] (hA : IsSelfAdjoint A) (t : ℝ) (ψ : H) :
    (stoneEquivSpectral.symm ⟨A, hA⟩).U t ψ = stoneExp hA t ψ := rfl

/-! ## §3  The spectral and Yosida bijections coincide -/

/-- **The bridge.**  `stoneEquivSpectral` and `stoneEquiv` are the *same* equivalence.  The
forward maps are definitionally equal (both `U ↦ generator U`), so `Equiv.ext` closes it; the
nontrivial half — that the two inverse constructions agree — is `stoneGroup_eq_genToGroup`,
recovered by applying `.symm` to this identity. -/
theorem stoneEquivSpectral_eq_stoneEquiv [Nontrivial H] :
    (stoneEquivSpectral : OneParameterUnitaryGroup (H := H) ≃ _) = stoneEquiv :=
  Equiv.ext fun _ => rfl

/-- The inverse maps agree — the spectral content of the bridge, read off `§3`. -/
theorem stoneEquivSpectral_symm_coe_eq [Nontrivial H] :
    (stoneEquivSpectral.symm : {A : H →ₗ.[ℂ] H // IsSelfAdjoint A} → _) = stoneEquiv.symm := by
  rw [stoneEquivSpectral_eq_stoneEquiv]

end Spectra.YosidaHille
