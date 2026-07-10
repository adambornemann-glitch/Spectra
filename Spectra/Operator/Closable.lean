/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.SelfAdjoint
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Closability and cores

Mathlib carries two previously-unconnected layers of `LinearPMap` theory: a **generic** one
for arbitrary topological modules (`LinearPMap.IsClosable`, `LinearPMap.closure`,
`LinearPMap.HasCore` — `Mathlib.Topology.Algebra.Module.LinearPMap`), and a **Hilbert-adjoint**
one (`LinearPMap.adjoint`, `LinearPMap.IsFormalAdjoint` — `Mathlib.Analysis.InnerProductSpace.
LinearPMap`). This file bridges them: any operator with a densely-defined formal adjoint is
closable (the adjoint is a closed extension), and for closed operators Mathlib's `HasCore` is
exactly topological density of the restricted graph.

## Main statements

* `isClosable_of_isFormalAdjoint` : an operator with a densely-defined formal adjoint is
  closable (two-Hilbert-space version — the generic backbone of every closability proof in the
  library).
* `isClosable_of_dense_adjoint_domain` : the classical criterion — densely-defined `T` with
  `D(T*)` dense is closable, via `T ≤ T**`. Extracted from
  `Spectra.TomitaTakesaki.tomitaOp_isClosable`, whose proof is this argument specialized to the
  Tomita operator.
* `symmetric_isClosable` : `A.IsFormalAdjoint A → Dense (A.domain) → A.IsClosable` — the
  diagonal case of `isClosable_of_isFormalAdjoint`.
* `IsClosed.closure_eq_self` : a closed operator equals its own closure.
* `closure_le_adjoint` : `A.closure ≤ A.adjoint` for symmetric, densely-defined `A`.
* `dense_closure_domain` : the closure of a densely-defined operator has dense domain.
* `isFormalAdjoint_of_le_adjoint` : `f ≤ f.adjoint` (with dense domain) already gives symmetry.
* `hasCore_iff_topologicalClosure_graph` : for closed `f`, Mathlib's `LinearPMap.HasCore f S`
  is exactly topological density of the graph of `f|_S` in the graph of `f`.
* `mem_closure_graph_of_hasCore` : the approximation form — every graph point of `f` is a limit
  of graph points of `f|_S` when `S` is a core.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII.
* [Weidmann, *Linear Operators in Hilbert Spaces*][weidmann1980].
-/
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.Operator

/-! ### Closability from a formal adjoint -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] in
/-- **An operator with a densely-defined formal adjoint is closable**: if `T.IsFormalAdjoint S`
with `T` densely defined, then `S ≤ T*` and `T*` is closed. This is the generic backbone behind
every closability proof in the library — `symmetric_isClosable` is the diagonal case `T = S`,
and `Spectra.TomitaTakesaki.tomitaOp_isClosable` is the case of the Tomita operator against its
formal adjoint. -/
theorem isClosable_of_isFormalAdjoint {T : F →ₗ.[ℂ] E} {S : E →ₗ.[ℂ] F}
    (h : T.IsFormalAdjoint S) (hdenseT : Dense (T.domain : Set F)) : S.IsClosable := by
  rw [LinearPMap.isClosable_iff_exists_closed_extension]
  exact ⟨T.adjoint, LinearPMap.adjoint_isClosed hdenseT, h.le_adjoint hdenseT⟩

/-- **The classical closability criterion (sufficiency half)**: a densely-defined operator
whose adjoint has dense domain is closable — `T ≤ T**` and `T**` is closed. -/
theorem isClosable_of_dense_adjoint_domain {T : E →ₗ.[ℂ] F}
    (hdense : Dense (T.domain : Set E)) (hadj : Dense (T.adjoint.domain : Set F)) :
    T.IsClosable :=
  isClosable_of_isFormalAdjoint (LinearPMap.adjoint_isFormalAdjoint hdense) hadj

/-- A symmetric, densely-defined operator is closable: its adjoint is a closed extension. -/
theorem symmetric_isClosable {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) : A.IsClosable :=
  isClosable_of_isFormalAdjoint hsym hdense

omit [CompleteSpace H] in
/-- A closed operator is its own closure. -/
theorem IsClosed.closure_eq_self {f : H →ₗ.[ℂ] H} (hf : f.IsClosed) : f.closure = f := by
  have hcl := hf.isClosable.graph_closure_eq_closure_graph
  rw [hf.submodule_topologicalClosure_eq] at hcl
  exact (LinearPMap.eq_of_eq_graph hcl.symm)

/-- The closure of a symmetric, densely-defined operator is contained in its adjoint. -/
theorem closure_le_adjoint {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) : A.closure ≤ A.adjoint := by
  have hadjclosed : A.adjoint.IsClosed := LinearPMap.adjoint_isClosed hdense
  have hmono := hadjclosed.isClosable.closure_mono (hsym.le_adjoint hdense)
  rwa [IsClosed.closure_eq_self hadjclosed] at hmono

omit [CompleteSpace H] in
/-- The closure of a densely-defined operator again has dense domain. -/
theorem dense_closure_domain {A : H →ₗ.[ℂ] H} (hdense : Dense (A.domain : Set H)) :
    Dense (A.closure.domain : Set H) :=
  hdense.mono (SetLike.coe_subset_coe.mpr (A.le_closure).1)

/-- If a densely-defined operator satisfies `f ≤ f.adjoint`, it is already symmetric. -/
theorem isFormalAdjoint_of_le_adjoint {f : H →ₗ.[ℂ] H} (hdenseF : Dense (f.domain : Set H))
    (hle : f ≤ f.adjoint) : f.IsFormalAdjoint f := by
  intro x y
  have hxdom : (x : H) ∈ f.adjoint.domain := hle.1 x.2
  have hfa := LinearPMap.adjoint_isFormalAdjoint hdenseF ⟨(x : H), hxdom⟩ y
  have heq : f.adjoint (⟨(x : H), hxdom⟩ : f.adjoint.domain) = f x :=
    (hle.2 (x := x) (y := ⟨(x : H), hxdom⟩) rfl).symm
  rwa [heq] at hfa

/-! ### Cores as graph density

Mathlib's `LinearPMap.HasCore f S` (`(f.domRestrict S).closure = f`) is used nowhere else in
the library, while "is a core for" density arguments recur informally (e.g. throughout
`Modular/Cocycle/PolarIsometry.lean`). The bridge below identifies the two: for a closed
operator, having `S` as a core is exactly topological density of the restricted graph. -/

omit [CompleteSpace H] [CompleteSpace E] [CompleteSpace F] in
/-- For a **closed** operator, Mathlib's `LinearPMap.HasCore` is precisely topological density
of the restricted graph: `S ≤ D(f)` is a core for `f` iff the graph of `f|_S` is dense in the
graph of `f`. -/
theorem hasCore_iff_topologicalClosure_graph {f : E →ₗ.[ℂ] F} (hf : f.IsClosed)
    {S : Submodule ℂ E} (hS : S ≤ f.domain) :
    f.HasCore S ↔ (f.domRestrict S).graph.topologicalClosure = f.graph := by
  have hclosable : (f.domRestrict S).IsClosable :=
    hf.isClosable.leIsClosable LinearPMap.domRestrict_le
  constructor
  · intro h
    rw [hclosable.graph_closure_eq_closure_graph, h.closure_eq]
  · intro h
    exact ⟨hS, LinearPMap.eq_of_eq_graph
      (by rw [← hclosable.graph_closure_eq_closure_graph, h])⟩

omit [CompleteSpace H] [CompleteSpace E] [CompleteSpace F] in
/-- **Approximation form of the core property**: if `S` is a core for the closed operator `f`,
every graph point `(x, f x)` of `f` is a limit of graph points of the restriction `f|_S` — the
usable statement behind "graph-norm density of a core". -/
theorem mem_closure_graph_of_hasCore {f : E →ₗ.[ℂ] F} (hf : f.IsClosed)
    {S : Submodule ℂ E} (h : f.HasCore S) (x : f.domain) :
    ((x : E), f x) ∈ closure ((f.domRestrict S).graph : Set (E × F)) := by
  rw [← Submodule.topologicalClosure_coe,
    (hasCore_iff_topologicalClosure_graph hf h.le_domain).mp h]
  exact f.mem_graph x

end Spectra.Operator
