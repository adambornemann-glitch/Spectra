/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.TomitaTakesaki.Basic
import Spectra.SpectralTheory.Antilinear.ConjugateSpace
import Mathlib.Analysis.InnerProductSpace.LinearPMap
/-!
# The Tomita operator `S` and its adjoint `F`

For a von Neumann algebra `M` on `H` with a cyclic separating vector `Ω`, the **Tomita operator**
is the densely-defined *antilinear* operator `S₀ : M Ω → H`, `S₀ (x Ω) = x⋆ Ω`. Via the
conjugate-space reduction (`Spectra.Conj`), we present it as a genuine *linear* unbounded operator

  `tomitaOp M Ω : H →ₗ.[ℂ] Conj H`,   `S̃ (x Ω) = toConj (x⋆ Ω)`,

so Mathlib's linear `LinearPMap` machinery applies. It is built from its graph
`{(x Ω, x⋆ Ω) : x ∈ M} ⊆ H × Conj H` via `Submodule.toLinearPMap`; the graph is a *functional*
relation precisely because `Ω` is **separating** (`x Ω = 0 ⟹ x = 0 ⟹ x⋆ Ω = 0`).

Its domain `M Ω` is **dense** when `Ω` is **cyclic**, so the adjoint `tomitaAdjoint M Ω = S̃⋆`
(`= F`, the second Tomita operator) is genuine. The modular operator will be `Δ = F ∘ S̃ = S̃⋆ S̃`
(milestone H3).

See `Spectra/Modular/TomitaTakesaki/ROADMAP.md` (milestones H1–H2). The antilinearity of `S` is
absorbed entirely by the codomain `Conj H`: `S̃` is honestly ℂ-linear because the antilinearity of
`star` and of `toConj` cancel.
-/

open Spectra.Conj

namespace Spectra.TomitaTakesaki

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The ℂ-submodule of `M`'s operators, as a `Submodule ℂ (H →L[ℂ] H)`. -/
@[simp] lemma mem_toSubmodule {M : VonNeumannAlgebra H} {T : H →L[ℂ] H} :
    T ∈ Subalgebra.toSubmodule M.toStarSubalgebra.toSubalgebra ↔ T ∈ M := by
  simp only [Subalgebra.mem_toSubmodule, StarSubalgebra.mem_toSubalgebra,
    VonNeumannAlgebra.mem_carrier, SetLike.mem_coe]

/-! ## The building-block linear maps -/

/-- Evaluation at `Ω`: the linear map `T ↦ T Ω`. -/
def evalAt (Ω : H) : (H →L[ℂ] H) →ₗ[ℂ] H where
  toFun T := T Ω
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [CompleteSpace H] in
/-- Evaluation `evalAt Ω` applied to `T` is `T Ω`. -/
@[simp] lemma evalAt_apply (Ω : H) (T : H →L[ℂ] H) : evalAt Ω T = T Ω := rfl

/-- The pre-Tomita map `T ↦ toConj (T⋆ Ω)`, valued in the conjugate space. It is **ℂ-linear**:
the antilinearity of `star` and of `toConj` cancel. -/
noncomputable def tomitaPre (Ω : H) : (H →L[ℂ] H) →ₗ[ℂ] Conj H where
  toFun T := toConj ((star T) Ω)
  map_add' T S := by
    apply ofConj_injective
    simp only [ofConj_toConj, ofConj_add, star_add, ContinuousLinearMap.add_apply]
  map_smul' c T := by
    apply ofConj_injective
    rw [ofConj_toConj, ofConj_smul, ofConj_toConj, star_smul, ContinuousLinearMap.smul_apply,
      starRingEnd_apply, RingHom.id_apply]

/-- The pre-Tomita map `tomitaPre Ω` applied to `T` is `toConj (T⋆ Ω)`. -/
@[simp] lemma tomitaPre_apply (Ω : H) (T : H →L[ℂ] H) :
    tomitaPre Ω T = toConj ((star T) Ω) := rfl

/-! ## The Tomita operator as a `LinearPMap` -/

/-- The graph `{(x Ω, x⋆ Ω) : x ∈ M}` of the Tomita operator, as a submodule of `H × Conj H`. -/
noncomputable def tomitaGraph (M : VonNeumannAlgebra H) (Ω : H) : Submodule ℂ (H × Conj H) :=
  Submodule.map ((evalAt Ω).prod (tomitaPre Ω))
    (Subalgebra.toSubmodule M.toStarSubalgebra.toSubalgebra)

/-- **The graph is functional**, because `Ω` is separating: if `x Ω = 0` then `x = 0`, hence
`x⋆ Ω = 0`. -/
lemma tomitaGraph_functional (M : VonNeumannAlgebra H) (Ω : H) (hsep : IsSeparating M Ω) :
    ∀ x ∈ tomitaGraph M Ω, x.1 = 0 → x.2 = 0 := by
  intro x hx hx1
  rw [tomitaGraph, Submodule.mem_map] at hx
  obtain ⟨T, hT, rfl⟩ := hx
  replace hx1 : T Ω = 0 := hx1
  change tomitaPre Ω T = 0
  rw [hsep T (mem_toSubmodule.mp hT) hx1]
  exact map_zero _

/-- **The Tomita operator** `S̃ : H →ₗ.[ℂ] Conj H`, `S̃ (x Ω) = toConj (x⋆ Ω)`. (The genuine
operator when `Ω` is separating — see `tomitaOp_apply`; otherwise `toLinearPMap` falls back to the
zero map off the diagonal, which never happens here.) -/
noncomputable def tomitaOp (M : VonNeumannAlgebra H) (Ω : H) : H →ₗ.[ℂ] Conj H :=
  (tomitaGraph M Ω).toLinearPMap

/-- **The defining property** `S̃ (x Ω) = x⋆ Ω` (in `Conj H`), for `x ∈ M`, when `Ω` is
separating. -/
lemma tomitaOp_apply (M : VonNeumannAlgebra H) (Ω : H) (hsep : IsSeparating M Ω)
    {T : H →L[ℂ] H} (hT : T ∈ M) (hmem : T Ω ∈ (tomitaOp M Ω).domain) :
    tomitaOp M Ω ⟨T Ω, hmem⟩ = toConj ((star T) Ω) := by
  have hg := tomitaGraph_functional M Ω hsep
  have h1 : (T Ω, toConj ((star T) Ω)) ∈ tomitaGraph M Ω := by
    rw [tomitaGraph, Submodule.mem_map]
    exact ⟨T, mem_toSubmodule.mpr hT, rfl⟩
  have h2 := Submodule.mem_graph_toLinearPMap hg ⟨T Ω, hmem⟩
  have hsub : (T Ω, toConj ((star T) Ω)) - (T Ω, tomitaOp M Ω ⟨T Ω, hmem⟩) ∈ tomitaGraph M Ω :=
    (tomitaGraph M Ω).sub_mem h1 h2
  rw [Prod.mk_sub_mk, sub_self] at hsub
  have hz : toConj ((star T) Ω) - tomitaOp M Ω ⟨T Ω, hmem⟩ = 0 := hg _ hsub rfl
  exact (sub_eq_zero.mp hz).symm

/-! ## Domain and density -/

/-- The domain of `S̃` is `M Ω` (= the image of `M` under evaluation at `Ω`). -/
lemma tomitaOp_domain (M : VonNeumannAlgebra H) (Ω : H) :
    (tomitaOp M Ω).domain
      = Submodule.map (evalAt Ω) (Subalgebra.toSubmodule M.toStarSubalgebra.toSubalgebra) := by
  have hfc : (LinearMap.fst ℂ H (Conj H)).comp ((evalAt Ω).prod (tomitaPre Ω)) = evalAt Ω :=
    LinearMap.ext fun _ => rfl
  rw [tomitaOp, Submodule.toLinearPMap_domain, tomitaGraph, ← Submodule.map_comp, hfc]

/-- The domain of `S̃` is exactly the cyclic subspace `span (M Ω)`. -/
lemma tomitaOp_domain_eq_span (M : VonNeumannAlgebra H) (Ω : H) :
    (tomitaOp M Ω).domain = Submodule.span ℂ (cyclicSet M Ω) := by
  have himg : (evalAt Ω) '' (↑(Subalgebra.toSubmodule M.toStarSubalgebra.toSubalgebra) : Set _)
      = cyclicSet M Ω := by
    ext v
    simp only [Set.mem_image, SetLike.mem_coe, evalAt_apply, mem_toSubmodule, cyclicSet]
  rw [tomitaOp_domain, ← Submodule.span_eq (Subalgebra.toSubmodule M.toStarSubalgebra.toSubalgebra),
    Submodule.map_span, himg]

/-- The domain `M Ω` of `S̃` is **dense** when `Ω` is cyclic; hence the adjoint below is genuine. -/
lemma tomitaOp_domain_dense (M : VonNeumannAlgebra H) (Ω : H) (hcyc : IsCyclic M Ω) :
    Dense ((tomitaOp M Ω).domain : Set H) := by
  rw [tomitaOp_domain_eq_span]; exact hcyc

/-! ## The adjoint `F = S̃⋆` -/

/-- **The second Tomita operator** `F = S̃⋆ : Conj H →ₗ.[ℂ] H`, the adjoint of the Tomita operator.
It is a genuine adjoint because `S̃` has dense domain when `Ω` is cyclic (`tomitaOp_domain_dense`).
The modular operator is `Δ = F ∘ S̃` (milestone H3). -/
noncomputable def tomitaAdjoint (M : VonNeumannAlgebra H) (Ω : H) : Conj H →ₗ.[ℂ] H :=
  (tomitaOp M Ω).adjoint

end Spectra.TomitaTakesaki
