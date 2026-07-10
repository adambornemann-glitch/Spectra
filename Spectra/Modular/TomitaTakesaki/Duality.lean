/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.TomitaTakesaki.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Module.Submodule.Invariant
/-!
# The cyclic ↔ separating duality (hard direction)

`Spectra.Modular.TomitaTakesaki.Basic` proves the easy half of the duality between cyclic and
separating vectors (`isSeparating_commutant_of_isCyclic`). This file proves the **hard half**:

  `IsSeparating M Ω → IsCyclic M.commutant Ω`,

i.e. a vector separating for `M` is cyclic for the commutant `M'`.
Together with the easy direction (applied to `M'`, using `M'' = M`) this gives the full
equivalence `IsCyclic M' Ω ↔ IsSeparating M Ω`.

## Proof

Let `K = closure(M' Ω)` and `P` its orthogonal projection (`Submodule.starProjection`). Since `K` is
invariant under every operator of `M'` and `P` is a star projection, `IsStarProjection.mem_iff`
places `P ∈ M`. Then `1 - P ∈ M` annihilates `Ω` (because `Ω ∈ K`, so `P Ω = Ω`), and **separation**
forces `1 - P = 0`, i.e. `P = 1`, i.e. `K = ⊤` — exactly cyclicity of `Ω` for `M'`.

This unblocks closability of the Tomita operator (roadmap H2): `M' Ω` dense is the hypothesis under
which `S` is closable.
-/

open scoped InnerProductSpace

namespace Spectra.TomitaTakesaki

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Duality (hard direction): a vector separating for `M` is cyclic for the commutant `M'`.**
Via the orthogonal projection onto `closure(M' Ω)`, which lands in `M` by the bicommutant
(`IsStarProjection.mem_iff`); separation then forces it to be the identity. -/
theorem isCyclic_commutant_of_isSeparating {M : VonNeumannAlgebra H} {Ω : H}
    (hsep : IsSeparating M Ω) : IsCyclic M.commutant Ω := by
  set S := cyclicSet M.commutant Ω with hSdef
  set Kspan := Submodule.span ℂ S with _hKspandef
  haveI hcs : CompleteSpace Kspan.topologicalClosure :=
    Kspan.isClosed_topologicalClosure.completeSpace_coe
  set K := Kspan.topologicalClosure with hKdef
  set P := K.starProjection with hPdef
  -- `Ω ∈ K`  (since `Ω = 1·Ω ∈ M' Ω ⊆ K`)
  have hΩS : Ω ∈ S := ⟨1, one_mem _, ContinuousLinearMap.one_apply Ω⟩
  have hΩK : Ω ∈ K := Kspan.le_topologicalClosure (Submodule.subset_span hΩS)
  -- `K` is invariant under the commutant, hence `P ∈ M`
  have hPM : P ∈ M := by
    rw [hPdef,
      VonNeumannAlgebra.IsStarProjection.mem_iff (isStarProjection_starProjection (U := K)) M]
    intro y hy
    rw [Submodule.range_starProjection, Module.End.mem_invtSubmodule_iff_mapsTo]
    have hspan : Set.MapsTo (⇑y) (↑Kspan : Set H) (↑Kspan : Set H) := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem w hw =>
        simp only [hSdef, cyclicSet, Set.mem_image] at hw
        obtain ⟨z, hz, rfl⟩ := hw
        refine Submodule.subset_span ?_
        simp only [hSdef, cyclicSet, Set.mem_image]
        exact ⟨y * z, mul_mem hy hz, ContinuousLinearMap.mul_apply y z Ω⟩
      | zero => simp
      | add a b _ _ ha hb => simpa [map_add] using Kspan.add_mem ha hb
      | smul c a _ ha => simpa [map_smul] using Kspan.smul_mem c ha
    rw [hKdef]
    simp only [Submodule.topologicalClosure_coe]
    exact hspan.closure y.continuous
  -- `1 - P ∈ M` kills `Ω`, so separation forces `P = 1`
  have hPΩ : P Ω = Ω := by rw [hPdef]; exact Submodule.starProjection_eq_self_iff.mpr hΩK
  have hkill : (1 - P) Ω = 0 := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hPΩ, sub_self]
  have hP1 : P = 1 := by
    have h0 : (1 : H →L[ℂ] H) - P = 0 := hsep _ (sub_mem (one_mem M) hPM) hkill
    exact (sub_eq_zero.mp h0).symm
  -- hence `K = ⊤`, i.e. `Ω` is cyclic for `M'`
  change Dense (↑Kspan : Set H)
  rw [Submodule.dense_iff_topologicalClosure_eq_top, ← hKdef, Submodule.eq_top_iff']
  intro v
  rw [← Submodule.starProjection_eq_self_iff (K := K), ← hPdef, hP1,
    ContinuousLinearMap.one_apply]

/-- **The full cyclic–separating duality:** `Ω` is cyclic for `M'` iff it is separating for `M`. -/
theorem isCyclic_commutant_iff_isSeparating {M : VonNeumannAlgebra H} {Ω : H} :
    IsCyclic M.commutant Ω ↔ IsSeparating M Ω :=
  ⟨isSeparating_of_isCyclic_commutant, isCyclic_commutant_of_isSeparating⟩

end Spectra.TomitaTakesaki
