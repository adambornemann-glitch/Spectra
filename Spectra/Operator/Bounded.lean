/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.SelfAdjoint
/-!
# Bounded vs. unbounded self-adjoint operators

`SelfAdjointOperator.IsBounded` marks the operators whose domain is all of `H`. By the
**Hellinger–Toeplitz theorem** this is not an ad-hoc notion: a self-adjoint (indeed, merely
symmetric) operator defined on all of a complete inner product space is automatically bounded, so
`IsBounded` genuinely means "extends to a bounded self-adjoint operator" — the extension is built
here as `boundedExtension`, via Mathlib's `LinearMap.IsSymmetric.continuous` /
`LinearMap.IsSymmetric.toSelfAdjoint`.

## Main definitions

* `SelfAdjointOperator.IsBounded` — `A.domain = ⊤`.
* `SelfAdjointOperator.boundedExtension` — the bounded self-adjoint operator a bounded
  `SelfAdjointOperator` extends to (Hellinger–Toeplitz).
* `SelfAdjointOperator.ofBounded` — the converse: every bounded self-adjoint operator gives a
  `SelfAdjointOperator` with domain `⊤`.

## Main results

* `SelfAdjointOperator.isSelfAdjoint_boundedExtension` — the extension is self-adjoint.
* `SelfAdjointOperator.boundedExtension_apply` — the extension agrees with `A` on `A`'s domain.
* `isClosed_of_bound_of_isClosed_domain` — a norm-bounded operator with closed domain is closed.
* `isClosed_of_bound_of_domain_eq_top` — an everywhere-defined bounded operator is closed
  (Reed–Simon, Theorem VIII.1).
* `exists_bound_of_isClosed_of_domain_eq_top` — the converse: an everywhere-defined closed
  operator is bounded, via the closed graph theorem.

## References

* E. Hellinger, O. Toeplitz, "Grundlagen für eine Theorie der unendlichen Matrizen" (1910).
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I*, Theorem VIII.2.

## Tags

bounded operator, unbounded operator, Hellinger-Toeplitz theorem
-/
open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Operator.SelfAdjointOperator

/-- A `SelfAdjointOperator` is **bounded** when its domain is all of `H`. By the
Hellinger–Toeplitz theorem (`boundedExtension` below) this is equivalent to genuinely extending
to a bounded self-adjoint operator, so this is not a weaker notion than boundedness. -/
def IsBounded (A : SelfAdjointOperator H) : Prop := A.domain = ⊤

lemma mem_domain_of_isBounded (A : SelfAdjointOperator H) (hA : A.IsBounded) (x : H) :
    x ∈ A.domain := by rw [hA]; exact Submodule.mem_top

/-- The linear equivalence `H ≃ₗ[ℂ] A.domain` witnessing that a bounded `SelfAdjointOperator`'s
domain is all of `H`. -/
noncomputable def boundedEquiv (A : SelfAdjointOperator H) (hA : A.IsBounded) :
    H ≃ₗ[ℂ] A.domain :=
  Submodule.topEquiv.symm.trans (LinearEquiv.ofEq ⊤ A.domain hA.symm)

@[simp] lemma coe_boundedEquiv_apply (A : SelfAdjointOperator H) (hA : A.IsBounded) (x : H) :
    (A.boundedEquiv hA x : H) = x := by
  simp [boundedEquiv]

/-- The totalization of a bounded `SelfAdjointOperator` as a genuine `H →ₗ[ℂ] H`. -/
noncomputable def toLinearMap (A : SelfAdjointOperator H) (hA : A.IsBounded) : H →ₗ[ℂ] H :=
  A.toLinearPMap.toFun.comp (A.boundedEquiv hA).toLinearMap

lemma toLinearMap_apply (A : SelfAdjointOperator H) (hA : A.IsBounded) (x : H) :
    A.toLinearMap hA x = A.toLinearPMap ⟨x, A.mem_domain_of_isBounded hA x⟩ := by
  simp only [toLinearMap, LinearMap.comp_apply]
  rfl

lemma isSymmetric_toLinearMap (A : SelfAdjointOperator H) (hA : A.IsBounded) :
    LinearMap.IsSymmetric (A.toLinearMap hA) := by
  intro x y
  simp only [A.toLinearMap_apply hA]
  exact A.symmetric' _ _

/-- **Hellinger–Toeplitz.** The bounded self-adjoint operator that a bounded `SelfAdjointOperator`
extends to. -/
noncomputable def boundedExtension (A : SelfAdjointOperator H) (hA : A.IsBounded) : H →L[ℂ] H :=
  ((A.isSymmetric_toLinearMap hA).toSelfAdjoint : H →L[ℂ] H)

lemma isSelfAdjoint_boundedExtension (A : SelfAdjointOperator H) (hA : A.IsBounded) :
    IsSelfAdjoint (A.boundedExtension hA) :=
  (A.isSymmetric_toLinearMap hA).toSelfAdjoint.2

/-- The extension agrees with `A` on `A`'s domain — this is what makes `boundedExtension`
usable rather than a black box. -/
lemma boundedExtension_apply (A : SelfAdjointOperator H) (hA : A.IsBounded) (x : H) :
    A.boundedExtension hA x = A.toLinearPMap ⟨x, A.mem_domain_of_isBounded hA x⟩ := by
  rw [← A.toLinearMap_apply hA x]
  exact (A.isSymmetric_toLinearMap hA).toSelfAdjoint_apply

/-- The converse of Hellinger–Toeplitz: every bounded self-adjoint operator gives a
`SelfAdjointOperator` with domain `⊤`. -/
noncomputable def ofBounded (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) : SelfAdjointOperator H where
  toLinearPMap := (T : H →ₗ[ℂ] H).toPMap ⊤
  selfAdjoint := by
    have hdense : Dense ((⊤ : Submodule ℂ H) : Set H) := by
      rw [Submodule.top_coe]; exact dense_univ
    have hTadj : T.adjoint = T := (ContinuousLinearMap.star_eq_adjoint T).symm.trans hT
    rw [LinearPMap.isSelfAdjoint_def,
      ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense T hdense, hTadj]

@[simp] lemma domain_ofBounded (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    (ofBounded T hT).domain = ⊤ :=
  LinearMap.toPMap_domain _ _

lemma isBounded_ofBounded (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    (ofBounded T hT).IsBounded :=
  domain_ofBounded T hT

end Spectra.Operator.SelfAdjointOperator

/-! ### The bounded ⟺ closed loop for general `LinearPMap`s

The symmetry-free layer relating norm bounds to closedness of the graph, for operators between
two (possibly different) Hilbert spaces. A norm bound on a closed domain forces a closed graph —
specialized to `domain = ⊤` this is Reed–Simon, Theorem VIII.1 — and conversely an
everywhere-defined closed operator is bounded by the **closed graph theorem**, imported from
Mathlib via `ContinuousLinearMap.ofIsClosedGraph` after totalizing the `LinearPMap` exactly as
in `SelfAdjointOperator.toLinearMap` above. -/

namespace Spectra.Operator

open Filter Topology

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- A norm-bounded operator with **closed domain** is closed — no symmetry or completeness
required. A graph sequence `(xₙ, f xₙ) → (x, y)` has `x ∈ f.domain` since the domain is closed,
and the bound squeezes `‖f xₙ - f x‖ ≤ C * ‖xₙ - x‖ → 0`, so `y = f x` by uniqueness of
limits. -/
theorem isClosed_of_bound_of_isClosed_domain {f : E →ₗ.[ℂ] F} (C : ℝ)
    (hC : ∀ x : f.domain, ‖f x‖ ≤ C * ‖(x : E)‖)
    (hdom : IsClosed (f.domain : Set E)) : f.IsClosed := by
  apply IsSeqClosed.isClosed
  rintro φ ⟨x, y⟩ hmem hlim
  choose xn hxn1 hxn2 using fun n => f.mem_graph_iff.mp (hmem n)
  have hx1 : Tendsto (fun n => ((xn n : E))) atTop (𝓝 x) := by
    simpa only [hxn1] using hlim.fst_nhds
  have hy1 : Tendsto (fun n => f (xn n)) atTop (𝓝 y) := by
    simpa only [hxn2] using hlim.snd_nhds
  have hxdom : x ∈ f.domain :=
    hdom.mem_of_tendsto hx1 (Eventually.of_forall fun n => (xn n).2)
  have hnorm : ∀ n, ‖f (xn n) - f ⟨x, hxdom⟩‖ ≤ C * ‖((xn n : E)) - x‖ := fun n => by
    have h := hC (xn n - ⟨x, hxdom⟩)
    rwa [f.map_sub, Submodule.coe_sub] at h
  have hrhs : Tendsto (fun n => C * ‖((xn n : E)) - x‖) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n => ((xn n : E)) - x) atTop (𝓝 0) :=
      tendsto_sub_nhds_zero_iff.mpr hx1
    simpa using h0.norm.const_mul C
  have hfx : Tendsto (fun n => f (xn n)) atTop (𝓝 (f ⟨x, hxdom⟩)) :=
    tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm hnorm hrhs)
  have hyeq : y = f ⟨x, hxdom⟩ := tendsto_nhds_unique hy1 hfx
  exact f.mem_graph_iff.mpr ⟨⟨x, hxdom⟩, rfl, hyeq.symm⟩

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Reed–Simon, Theorem VIII.1 (bounded ⟹ closed).** An everywhere-defined norm-bounded
operator is closed. -/
theorem isClosed_of_bound_of_domain_eq_top {f : E →ₗ.[ℂ] F} (C : ℝ)
    (hC : ∀ x : f.domain, ‖f x‖ ≤ C * ‖(x : E)‖) (hdom : f.domain = ⊤) : f.IsClosed := by
  have htop : IsClosed (f.domain : Set E) := by
    rw [hdom, Submodule.top_coe]
    exact isClosed_univ
  exact isClosed_of_bound_of_isClosed_domain C hC htop

/-- **Closed graph theorem for `LinearPMap`s (closed ⟹ bounded).** An everywhere-defined closed
operator between Hilbert spaces is bounded: totalize `f` to a genuine linear map with the same
graph, upgrade it through Mathlib's `ContinuousLinearMap.ofIsClosedGraph`, and read off the
operator-norm bound. Together with `isClosed_of_bound_of_domain_eq_top` this closes the
bounded ⟺ closed loop for everywhere-defined operators. -/
theorem exists_bound_of_isClosed_of_domain_eq_top {f : E →ₗ.[ℂ] F}
    (hf : f.IsClosed) (hdom : f.domain = ⊤) :
    ∃ C : ℝ, ∀ x : f.domain, ‖f x‖ ≤ C * ‖(x : E)‖ := by
  set g : E →ₗ[ℂ] F := f.toFun.comp
    (Submodule.topEquiv.symm.trans (LinearEquiv.ofEq ⊤ f.domain hdom.symm)).toLinearMap
    with hgdef
  have hgapply : ∀ x : f.domain, g (x : E) = f x := fun x => by
    simp only [hgdef, LinearMap.comp_apply]
    rfl
  have hgraph : (g.graph : Set (E × F)) = (f.graph : Set (E × F)) := by
    ext p
    simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, LinearPMap.mem_graph_iff]
    constructor
    · intro hp
      have hp1 : p.1 ∈ f.domain := by rw [hdom]; exact Submodule.mem_top
      exact ⟨⟨p.1, hp1⟩, rfl, (hgapply ⟨p.1, hp1⟩).symm.trans hp.symm⟩
    · rintro ⟨z, hz1, hz2⟩
      rw [← hz1, ← hz2]
      exact (hgapply z).symm
  have hgclosed : IsClosed (g.graph : Set (E × F)) := by
    rw [hgraph]
    exact hf
  refine ⟨‖ContinuousLinearMap.ofIsClosedGraph hgclosed‖, fun x => ?_⟩
  have hTx : ContinuousLinearMap.ofIsClosedGraph hgclosed (x : E) = f x := by
    rw [ContinuousLinearMap.coeFn_ofIsClosedGraph]
    exact hgapply x
  rw [← hTx]
  exact (ContinuousLinearMap.ofIsClosedGraph hgclosed).le_opNorm (x : E)

end Spectra.Operator
