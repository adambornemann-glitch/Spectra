/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Reflection positivity (Osterwalder–Schrader positivity)

**Reflection positivity** is the one Euclidean axiom (Osterwalder–Schrader OS3) that carries the
physical content — it is what lets one reconstruct a genuine quantum theory (a Hilbert space with a
positive Hamiltonian) from a Euclidean/statistical-mechanics measure. For lattice gauge theory it is
the Osterwalder–Seiler property of the Wilson-action Gibbs measure; downstream it produces the
physical Hilbert space (GNS-style, Lane R3), the transfer operator `0 < T ≤ 1` (R4), and the
self-adjoint Hamiltonian `H = −log T` (R5).

This file states the **abstract predicate**, generically — nothing here is Gaussian-, lattice-, or
gauge-specific.  (It reads OS-axiom *shapes* off the free-field template `mrdouglasny/OSforGFF`; it
does **not** port that development's Gaussian-specific proofs.)

## The mathematics

On the Euclidean Hilbert space `E = L²(μ)` (states/observables weighted by the Euclidean measure
`μ`), a **reflection** `θ` is a self-adjoint linear involution — the operator implementing time
reflection `t ↦ −t`. Writing `E₊ ⊆ E` for the **positive-time** subspace (observables supported at
`t ≥ 0`), reflection positivity is the statement that the **reflected form**
`⟨a, b⟩_θ := ⟪θ a, b⟫` is positive semidefinite on `E₊`:
$$ \forall a \in E_+, \qquad 0 \le \operatorname{Re}\,\langle \theta a, a\rangle. $$
Self-adjointness of `θ` makes `⟨θ a, a⟩` real, so this is a genuine nonnegativity; the reflected
form is then a positive-semidefinite Hermitian form on `E₊`, and its GNS completion (quotient by the
null space, then complete) is the physical Hilbert space.

## Main definitions

* `Spectra.QuantumFieldTheory.OsterwalderSchrader.IsReflectionPositive` — the predicate.
* `Spectra.QuantumFieldTheory.OsterwalderSchrader.ReflectionData` — bundled reflection data (a
  self-adjoint involution `θ`, a positive-time subspace `E₊`, and the reflection-positivity axiom),
  the honest hypothesis object a downstream OS reconstruction consumes.

Unlike a Wightman/mass-gap bundle, this structure is genuinely **inhabited**:
`ReflectionData.trivial` (the identity reflection on all of `E`) witnesses consistency
(`Inhabited`), so the axiom is not vacuous — its content is producing an interesting reflection for
a *specific* measure (Lane R2).

## References

* K. Osterwalder, R. Schrader, *Axioms for Euclidean Green's functions* (1973/1975).
* J. Glimm, A. Jaffe, *Quantum Physics: A Functional Integral Point of View*, §6.2 (reflection
  positivity and reconstruction).
* K. Osterwalder, E. Seiler, *Gauge field theories on a lattice* (1978).

## Tags

reflection positivity, Osterwalder-Schrader, Euclidean quantum field theory, GNS, transfer matrix
-/

namespace Spectra.QuantumFieldTheory.OsterwalderSchrader

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Reflection positivity** of a reflection `θ` relative to a positive-time subspace `E₊`: the
reflected form `⟨θ a, a⟩` is nonnegative for every positive-time vector `a`.  This is the abstract
Osterwalder–Schrader positivity condition. -/
def IsReflectionPositive (θ : E →ₗ[𝕜] E) (Epos : Submodule 𝕜 E) : Prop :=
  ∀ a ∈ Epos, 0 ≤ RCLike.re (inner 𝕜 (θ a) a)

/-- **Bundled reflection-positivity data** on a `𝕜`-inner-product space `E`.

The fields are the defining properties an Osterwalder–Schrader/Osterwalder–Seiler datum supplies: a
self-adjoint linear involution `reflection` (time reflection), a `positiveTime` subspace, and the
reflection-positivity axiom. A downstream reconstruction (Lane R3+) takes a `ReflectionData` as a
hypothesis and builds the physical Hilbert space from the reflected form. See
`ReflectionData.trivial` for a witness that the bundle is consistent (inhabited). -/
structure ReflectionData (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] where
  /-- The reflection operator `θ` implementing time reflection. -/
  reflection : E →ₗ[𝕜] E
  /-- `θ` is an involution: `θ² = id`. -/
  involutive : Function.Involutive reflection
  /-- `θ` is self-adjoint (`⟪θ a, b⟫ = ⟪a, θ b⟫`), which makes the reflected form Hermitian. -/
  symmetric : reflection.IsSymmetric
  /-- The positive-time subspace `E₊` of observables supported at `t ≥ 0`. -/
  positiveTime : Submodule 𝕜 E
  /-- **Reflection positivity (OS3):** the reflected form is positive semidefinite on `E₊`. -/
  reflection_positive : IsReflectionPositive reflection positiveTime

namespace ReflectionData

variable (D : ReflectionData 𝕜 E)

/-- The reflected diagonal `⟪θ a, a⟫` is **real** (its complex conjugate is itself), because `θ` is
self-adjoint.  Together with `reflection_positive` this makes it a genuine nonnegative real. -/
theorem reflected_inner_conj_eq (a : E) :
    (starRingEnd 𝕜) (inner 𝕜 (D.reflection a) a) = inner 𝕜 (D.reflection a) a := by
  rw [inner_conj_symm]
  exact (D.symmetric a a).symm

/-- The reflection-positivity value, extracted: `0 ≤ Re ⟪θ a, a⟫` for positive-time `a`. -/
theorem reflection_positive_apply {a : E} (ha : a ∈ D.positiveTime) :
    0 ≤ RCLike.re (inner 𝕜 (D.reflection a) a) :=
  D.reflection_positive a ha

/-- **Consistency / non-vacuity witness.**  The identity reflection on all of `E` is reflection
positive (`⟪a, a⟫ ≥ 0`), so `ReflectionData` is inhabited: the axiom is satisfiable, and its real
content lies in supplying a nontrivial reflection for a specific measure. -/
def trivial : ReflectionData 𝕜 E where
  reflection := LinearMap.id
  involutive := fun _ => rfl
  symmetric := fun _ _ => rfl
  positiveTime := ⊤
  reflection_positive := fun _ _ => inner_self_nonneg

instance : Inhabited (ReflectionData 𝕜 E) := ⟨trivial⟩

end ReflectionData

end Spectra.QuantumFieldTheory.OsterwalderSchrader
