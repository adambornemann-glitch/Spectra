/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.Closable
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# The adjoint only sees the closure

`LinearPMap.adjoint` is defined purely in terms of the graph of its input, via
`Submodule.adjoint` on the ambient product space `H × H`. Since `Submodule.adjoint` is built from
an orthogonal complement, and the orthogonal complement of a submodule is insensitive to
topologically closing that submodule first, `LinearPMap.adjoint` cannot distinguish a
densely-defined, closable operator `B` from its closure `B.closure`. This file records that fact,
`closure_adjoint_eq_adjoint : B.closure.adjoint = B.adjoint`, together with the general-purpose
submodule-level infrastructure (`Submodule.adjoint_antitone`,
`Submodule.map_topologicalClosure_of_equiv`, `orthogonal_topologicalClosure_eq`,
`Submodule.adjoint_topologicalClosure_eq`) it is assembled from. None of this is currently in
Mathlib.

## Main statements

* `Submodule.adjoint_antitone` : `g₁ ≤ g₂ → g₂.adjoint ≤ g₁.adjoint`, order-reversal for
  `Submodule.adjoint`.
* `Submodule.map_topologicalClosure_of_equiv` : mapping a submodule's topological closure through
  a continuous linear equivalence commutes with taking the topological closure.
* `orthogonal_topologicalClosure_eq` : `K.topologicalClosureᗮ = Kᗮ`.
* `Submodule.adjoint_topologicalClosure_eq` : `g.topologicalClosure.adjoint = g.adjoint`.
* `closure_adjoint_eq_adjoint` : `B.closure.adjoint = B.adjoint` for densely-defined, closable
  `B : H →ₗ.[ℂ] H`.
* `adjoint_le_adjoint_of_le` : the adjoint reverses extension, `A ≤ B → B.adjoint ≤ A.adjoint`.
* `Submodule.adjoint_adjoint` : `g.adjoint.adjoint = g.topologicalClosure` — the double adjoint
  of a graph submodule is its topological closure (with `Submodule.isClosed_adjoint` as a
  corollary: adjoints are closed).
* `adjoint_adjoint_eq_closure` : **the double adjoint is the closure**, `T** = T̄`, for
  densely-defined `T` with densely-defined adjoint (Reed–Simon, Theorem VIII.1(b)); specialized
  by `adjoint_adjoint_eq_self` (closed `T`) and `adjoint_adjoint_eq_closure_of_isFormalAdjoint`
  (symmetric `T`, where adjoint-domain density is automatic).

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII.
* [Weidmann, *Linear Operators in Hilbert Spaces*][weidmann1980].
-/
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.Operator

/-! ### 1. Order-reversal of `Submodule.adjoint` -/

omit [CompleteSpace H] in
/-- `Submodule.adjoint` reverses the order on submodules of `H × H`. -/
theorem Submodule.adjoint_antitone {g₁ g₂ : Submodule ℂ (H × H)} (h : g₁ ≤ g₂) :
    g₂.adjoint ≤ g₁.adjoint := by
  unfold Submodule.adjoint
  exact Submodule.map_mono (Submodule.orthogonal_le (Submodule.map_mono h))

/-! ### 2. Closure commutes with mapping through a continuous linear equivalence -/

/-- Mapping a submodule's topological closure through a continuous linear equivalence commutes
with taking the topological closure. -/
theorem Submodule.map_topologicalClosure_of_equiv {M₁ M₂ : Type*} [NormedAddCommGroup M₁]
    [NormedAddCommGroup M₂] [NormedSpace ℂ M₁] [NormedSpace ℂ M₂] (e : M₁ ≃L[ℂ] M₂)
    (s : Submodule ℂ M₁) :
    s.topologicalClosure.map (e : M₁ →ₗ[ℂ] M₂) = (s.map (e : M₁ →ₗ[ℂ] M₂)).topologicalClosure := by
  apply SetLike.coe_injective
  rw [Submodule.map_coe, Submodule.topologicalClosure_coe, Submodule.topologicalClosure_coe,
    Submodule.map_coe]
  exact e.image_closure (s : Set M₁)

/-! ### 3. Closure does not change the orthogonal complement -/

/-- The orthogonal complement of a submodule's topological closure is the same as the orthogonal
complement of the submodule itself. -/
theorem orthogonal_topologicalClosure_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (K : Submodule ℂ E) :
    K.topologicalClosureᗮ = Kᗮ := by
  have h1 : Kᗮᗮ = K.topologicalClosure := K.orthogonal_orthogonal_eq_closure
  have h2 : Kᗮᗮᗮ = (Kᗮ : Submodule ℂ E).topologicalClosure :=
    Submodule.orthogonal_orthogonal_eq_closure (Kᗮ : Submodule ℂ E)
  have h3 : (Kᗮ : Submodule ℂ E).topologicalClosure = Kᗮ :=
    IsClosed.submodule_topologicalClosure_eq (Submodule.isClosed_orthogonal K)
  calc K.topologicalClosureᗮ = Kᗮᗮᗮ := by rw [h1]
    _ = (Kᗮ : Submodule ℂ E).topologicalClosure := h2
    _ = Kᗮ := h3

/-! ### 4. `Submodule.adjoint` only depends on the topological closure -/

/-- The skew-swap `(x, y) ↦ (-y, x)` bundled as a continuous linear equivalence: both directions
are visibly continuous (a coordinate swap composed with negation). -/
noncomputable def skewSwapCLE : (H × H) ≃L[ℂ] (H × H) :=
  { LinearEquiv.skewSwap ℂ H H with
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

/-- The first leg of `Submodule.adjoint`'s defining map, `(skewSwap H H).symm.trans
(WithLp.linearEquiv 2 ℂ (H × H)).symm`, bundled as a continuous linear equivalence. -/
noncomputable def adjointFstCLE : (H × H) ≃L[ℂ] WithLp 2 (H × H) :=
  skewSwapCLE.symm.trans (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm

/-- The second leg of `Submodule.adjoint`'s defining map, `WithLp.linearEquiv 2 ℂ (H × H)`,
bundled as a continuous linear equivalence (`WithLp.prodContinuousLinearEquiv`). -/
noncomputable def adjointSndCLE : WithLp 2 (H × H) ≃L[ℂ] (H × H) :=
  WithLp.prodContinuousLinearEquiv 2 ℂ H H

/-- `Submodule.adjoint` only depends on the topological closure of its input. -/
theorem Submodule.adjoint_topologicalClosure_eq (g : Submodule ℂ (H × H)) :
    g.topologicalClosure.adjoint = g.adjoint := by
  unfold Submodule.adjoint
  have hφeq : ((LinearEquiv.skewSwap ℂ H H).symm.trans
      (WithLp.linearEquiv 2 ℂ (H × H)).symm).toLinearMap =
      ((adjointFstCLE : (H × H) ≃L[ℂ] WithLp 2 (H × H)) : (H × H) →ₗ[ℂ] WithLp 2 (H × H)) := rfl
  have hψeq : (WithLp.linearEquiv 2 ℂ (H × H) : WithLp 2 (H × H) →ₗ[ℂ] H × H) =
      ((adjointSndCLE : WithLp 2 (H × H) ≃L[ℂ] (H × H)) :
        WithLp 2 (H × H) →ₗ[ℂ] H × H) := rfl
  rw [hφeq, hψeq, Submodule.map_topologicalClosure_of_equiv adjointFstCLE g]
  congr 1
  exact orthogonal_topologicalClosure_eq _

/-! ### 5. The payoff: `LinearPMap.adjoint` only depends on the closure -/

/-- `LinearPMap.adjoint` only depends on the closure of a densely-defined, closable operator:
`B` and `B.closure` have the same adjoint. -/
theorem closure_adjoint_eq_adjoint {B : H →ₗ.[ℂ] H} (hdense : Dense (B.domain : Set H))
    (hclosable : B.IsClosable) : B.closure.adjoint = B.adjoint := by
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (dense_closure_domain hdense),
    LinearPMap.adjoint_graph_eq_graph_adjoint hdense,
    ← hclosable.graph_closure_eq_closure_graph]
  exact Submodule.adjoint_topologicalClosure_eq B.graph

/-! ### 6. The adjoint is antitone -/

/-- **The adjoint reverses extension**: if `A ≤ B` (with `A` densely defined, so both adjoints
carry their defining property), then `B.adjoint ≤ A.adjoint`. Pure graph bookkeeping through
`Submodule.adjoint_antitone`. -/
theorem adjoint_le_adjoint_of_le {A B : H →ₗ.[ℂ] H} (hdenseA : Dense (A.domain : Set H))
    (hAB : A ≤ B) : B.adjoint ≤ A.adjoint := by
  have hdenseB : Dense (B.domain : Set H) :=
    hdenseA.mono (SetLike.coe_subset_coe.mpr hAB.1)
  apply LinearPMap.le_of_le_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hdenseA,
    LinearPMap.adjoint_graph_eq_graph_adjoint hdenseB]
  exact Submodule.adjoint_antitone (LinearPMap.le_graph_of_le hAB)

/-! ### 7. The double adjoint of a graph submodule is its topological closure

Mathlib's `Submodule.adjoint` factors as `g.adjoint = ((g.map φ)ᗮ).map ψ`, where
`φ (a, b) = toLp 2 (b, -a)` skew-swaps into the `L²` product `WithLp 2 (H × H)` and `ψ = ofLp`.
Applying the adjoint twice, the two skew-swaps meet in the middle and compose to the isometric
twist `toLp 2 (c, d) ↦ toLp 2 (d, -c)`; conjugating the orthogonal complement through that
twist (`Submodule.map_orthogonal_equiv`) and composing the swaps once more yields `-toLp`,
whose sign `Submodule.map` cannot see (`Submodule.map_neg`). The double adjoint therefore
collapses to `(g.map toLp)ᗮᗮ` read back through `ofLp`, which by
`Submodule.orthogonal_orthogonal_eq_closure` is the topological closure. -/

/-- The first leg of `Submodule.adjoint`: the skew-swap `(a, b) ↦ toLp 2 (b, -a)` into the `L²`
product, as a linear map. -/
noncomputable def adjointFstₗ : (H × H) →ₗ[ℂ] WithLp 2 (H × H) :=
  ((LinearEquiv.skewSwap ℂ H H).symm.trans (WithLp.linearEquiv 2 ℂ (H × H)).symm).toLinearMap

/-- The second leg of `Submodule.adjoint`: `ofLp`, as a linear map. -/
noncomputable def adjointSndₗ : WithLp 2 (H × H) →ₗ[ℂ] H × H :=
  (WithLp.linearEquiv 2 ℂ (H × H) : WithLp 2 (H × H) →ₗ[ℂ] H × H)

/-- The plain (un-swapped) `toLp` leg, as a linear map. -/
noncomputable def toLpₗ : (H × H) →ₗ[ℂ] WithLp 2 (H × H) :=
  ((WithLp.linearEquiv 2 ℂ (H × H)).symm : (H × H) →ₗ[ℂ] WithLp 2 (H × H))

omit [CompleteSpace H] in
/-- `Submodule.adjoint`, definitionally: an orthogonal complement in the `L²` product,
sandwiched between the two legs. -/
theorem Submodule.adjoint_def (g : Submodule ℂ (H × H)) :
    g.adjoint = ((g.map adjointFstₗ)ᗮ).map adjointSndₗ := rfl

/-- The twist `toLp 2 (c, d) ↦ toLp 2 (d, -c)` on the `L²` product — the composite
`adjointFstₗ ∘ₗ adjointSndₗ` of the two legs of `Submodule.adjoint`, taken in the wrong
order — bundled as a linear isometry equivalence. -/
noncomputable def twistLIE : WithLp 2 (H × H) ≃ₗᵢ[ℂ] WithLp 2 (H × H) :=
  LinearEquiv.isometryOfInner
    ((WithLp.linearEquiv 2 ℂ (H × H)).trans
      ((LinearEquiv.skewSwap ℂ H H).symm.trans (WithLp.linearEquiv 2 ℂ (H × H)).symm))
    (fun x y => by
      simp only [LinearEquiv.trans_apply, WithLp.coe_linearEquiv, WithLp.coe_symm_linearEquiv,
        LinearEquiv.skewSwap_symm_apply, WithLp.prod_inner_apply, inner_neg_neg]
      exact add_comm _ _)

omit [CompleteSpace H] in
/-- The composite of the two legs of `Submodule.adjoint`, in the wrong order, is the twist. -/
theorem adjointFstₗ_comp_adjointSndₗ :
    adjointFstₗ.comp adjointSndₗ =
      ((twistLIE (H := H)).toLinearEquiv : WithLp 2 (H × H) →ₗ[ℂ] WithLp 2 (H × H)) := rfl

omit [CompleteSpace H] in
/-- Twisting after skew-swapping is `-toLp`: the two skew-swaps compose to `-1`. -/
theorem twistLIE_comp_adjointFstₗ :
    (((twistLIE (H := H)).toLinearEquiv :
      WithLp 2 (H × H) →ₗ[ℂ] WithLp 2 (H × H)).comp adjointFstₗ) = -toLpₗ :=
  LinearMap.ext fun _ => rfl

/-- **The double adjoint of a graph submodule is its topological closure.** This is the
submodule-level content of the operator identity `T** = T̄`. -/
theorem Submodule.adjoint_adjoint (g : Submodule ℂ (H × H)) :
    g.adjoint.adjoint = g.topologicalClosure := by
  -- The inner map collapses through the twist: `g.adjoint.map φ = (g.map toLp)ᗮ`.
  have h1 : g.adjoint.map adjointFstₗ = (g.map toLpₗ)ᗮ := by
    rw [Submodule.adjoint_def g, ← Submodule.map_comp, adjointFstₗ_comp_adjointSndₗ,
      Submodule.map_orthogonal_equiv, ← Submodule.map_comp, twistLIE_comp_adjointFstₗ,
      Submodule.map_neg]
  -- `ofLp ∘ₗ toLp = id`, so the outer sandwich transports `Kᗮᗮ = K̄` back to `H × H`.
  have hid : (adjointSndₗ (H := H)).comp toLpₗ = LinearMap.id := LinearMap.ext fun _ => rfl
  calc g.adjoint.adjoint
      = ((g.adjoint.map adjointFstₗ)ᗮ).map adjointSndₗ := Submodule.adjoint_def _
    _ = (((g.map toLpₗ)ᗮ)ᗮ).map adjointSndₗ := by rw [h1]
    _ = ((g.map toLpₗ).topologicalClosure).map adjointSndₗ := by
          rw [Submodule.orthogonal_orthogonal_eq_closure]
    _ = ((g.map toLpₗ).map adjointSndₗ).topologicalClosure := by
          apply SetLike.coe_injective
          rw [Submodule.map_coe, Submodule.topologicalClosure_coe,
            Submodule.topologicalClosure_coe, Submodule.map_coe]
          exact adjointSndCLE.toHomeomorph.image_closure _
    _ = g.topologicalClosure := by rw [← Submodule.map_comp, hid, Submodule.map_id]

/-- The adjoint of a graph submodule is topologically closed, as a submodule. -/
theorem Submodule.topologicalClosure_adjoint_eq (g : Submodule ℂ (H × H)) :
    g.adjoint.topologicalClosure = g.adjoint := by
  rw [← Submodule.adjoint_adjoint g.adjoint, Submodule.adjoint_adjoint g,
    Submodule.adjoint_topologicalClosure_eq]

/-- The adjoint of a graph submodule is a closed set. -/
theorem Submodule.isClosed_adjoint (g : Submodule ℂ (H × H)) :
    IsClosed (g.adjoint : Set (H × H)) := by
  rw [← Submodule.topologicalClosure_adjoint_eq g]
  exact Submodule.isClosed_topologicalClosure _

/-! ### 8. The payoff: the double adjoint is the closure -/

/-- **The double adjoint is the closure** (Reed–Simon, Theorem VIII.1(b)): for a densely-defined
operator whose adjoint is also densely defined, `T** = T̄`. Both graph bridges
(`LinearPMap.adjoint_graph_eq_graph_adjoint`) reduce the statement to
`Submodule.adjoint_adjoint`, and density of `D(T*)` supplies closability
(`isClosable_of_dense_adjoint_domain`) to identify `T.graph.topologicalClosure` with the graph
of `T.closure`. -/
theorem adjoint_adjoint_eq_closure {T : H →ₗ.[ℂ] H} (hdense : Dense (T.domain : Set H))
    (hadj : Dense (T.adjoint.domain : Set H)) :
    T.adjoint.adjoint = T.closure := by
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hadj,
    LinearPMap.adjoint_graph_eq_graph_adjoint hdense,
    Submodule.adjoint_adjoint,
    (isClosable_of_dense_adjoint_domain hdense hadj).graph_closure_eq_closure_graph]

/-- For a **closed** densely-defined operator with densely-defined adjoint, `T** = T`. -/
theorem adjoint_adjoint_eq_self {T : H →ₗ.[ℂ] H} (hdense : Dense (T.domain : Set H))
    (hadj : Dense (T.adjoint.domain : Set H)) (hclosed : T.IsClosed) :
    T.adjoint.adjoint = T :=
  (adjoint_adjoint_eq_closure hdense hadj).trans (IsClosed.closure_eq_self hclosed)

/-- For a **symmetric** densely-defined operator the adjoint-domain density is automatic
(`D(T) ⊆ D(T*)`), so `T** = T̄` needs no extra hypothesis. -/
theorem adjoint_adjoint_eq_closure_of_isFormalAdjoint {T : H →ₗ.[ℂ] H}
    (hsym : T.IsFormalAdjoint T) (hdense : Dense (T.domain : Set H)) :
    T.adjoint.adjoint = T.closure :=
  adjoint_adjoint_eq_closure hdense
    (hdense.mono (SetLike.coe_subset_coe.mpr (hsym.le_adjoint hdense).1))

/-! ### 9. The closability criterion is an iff

`Spectra.Operator.isClosable_of_dense_adjoint_domain` (in `Operator/Closable.lean`) gives the
sufficiency half of the classical closability criterion. The graph machinery above yields the
necessity half: if `D(T*)` were not dense, a nonzero `ψ ⊥ D(T*)` would put `(0, ψ)` into
`Γ(T)ᵃᵃ = Γ(T)‾` (every pair in `Γ(T*)ᵃ` pairs `ψ` only against adjoint-domain vectors), so the
closure of the graph would not be a graph. -/

/-- **The classical closability criterion, necessity half** (Reed–Simon, Theorem VIII.1(a)):
a densely-defined closable operator has densely-defined adjoint. If `ψ ⊥ D(T*)`, then
`(0, ψ) ∈ Γ(T*)ᵃ = Γ(T)ᵃᵃ = Γ(T)‾ = Γ(T̄)`, forcing `ψ = T̄ 0 = 0`. -/
theorem dense_adjoint_domain_of_isClosable {T : H →ₗ.[ℂ] H}
    (hdense : Dense (T.domain : Set H)) (hclosable : T.IsClosable) :
    Dense (T.adjoint.domain : Set H) := by
  have hbot : (T.adjoint.domain : Submodule ℂ H)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro ψ hψ
    rw [Submodule.mem_orthogonal] at hψ
    -- `(0, ψ)` lies in the closure of the graph: it is `Γ(T*)ᵃ`-generic
    have hmem : ((0 : H), ψ) ∈ T.graph.topologicalClosure := by
      rw [← Submodule.adjoint_adjoint T.graph,
        ← LinearPMap.adjoint_graph_eq_graph_adjoint hdense,
        Submodule.mem_adjoint_iff]
      intro a b hab
      obtain ⟨y, hy1, _hy2⟩ := (LinearPMap.mem_graph_iff T.adjoint).mp hab
      have ha : a ∈ T.adjoint.domain := by
        have h := y.2
        rwa [hy1] at h
      rw [inner_zero_right, hψ a ha, sub_zero]
    -- … but the closure of the graph is the graph of the closure
    rw [hclosable.graph_closure_eq_closure_graph] at hmem
    obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff T.closure).mp hmem
    have hy0 : y = 0 := Subtype.ext (by simpa using hy1)
    rw [hy0, T.closure.map_zero] at hy2
    exact hy2.symm
  have htop : (T.adjoint.domain : Submodule ℂ H).topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hbot, Submodule.bot_orthogonal_eq_top]
  rw [dense_iff_closure_eq]
  have hcoe : closure (T.adjoint.domain : Set H)
      = ((T.adjoint.domain : Submodule ℂ H).topologicalClosure : Set H) :=
    (Submodule.topologicalClosure_coe _).symm
  rw [hcoe, htop]
  rfl

/-- **The classical closability criterion** (Reed–Simon, Theorem VIII.1(a)), as an iff: a
densely-defined operator is closable exactly when its adjoint is densely defined. -/
theorem isClosable_iff_dense_adjoint_domain {T : H →ₗ.[ℂ] H}
    (hdense : Dense (T.domain : Set H)) :
    T.IsClosable ↔ Dense (T.adjoint.domain : Set H) :=
  ⟨dense_adjoint_domain_of_isClosable hdense, isClosable_of_dense_adjoint_domain hdense⟩

/-- `T** = T̄` for closable `T` — `adjoint_adjoint_eq_closure` with the adjoint-domain density
supplied by the necessity half of the closability criterion. -/
theorem adjoint_adjoint_eq_closure_of_isClosable {T : H →ₗ.[ℂ] H}
    (hdense : Dense (T.domain : Set H)) (hclosable : T.IsClosable) :
    T.adjoint.adjoint = T.closure :=
  adjoint_adjoint_eq_closure hdense (dense_adjoint_domain_of_isClosable hdense hclosable)

end Spectra.Operator
