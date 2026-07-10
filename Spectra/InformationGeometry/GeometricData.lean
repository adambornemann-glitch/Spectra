/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Flow.Basic

/-!
# Abstract Geometric Data

The key observation behind this file: `InfoGeometricGenerator` never
touches the statistical model.  Its two defining conditions (Killing,
cubic preservation) mention only three things — the parameter domain,
the Fisher matrix, and the Amari–Chentsov cubic tensor.  The measure
space, the densities, the score, the integrability side conditions: all
of it enters only as the *source* of `(domain, g, C)`.

So we factor the generator through that interface.  `GeometricData n`
is a bare triple `(domain, g, C)`; `GeometricData.Generator` repeats the
two Lie-derivative conditions verbatim over it.  Every
`TwiceDifferentiableModel` forgets to a `GeometricData`
(`TwiceDifferentiableModel.geometricData`), and over that data the
abstract generators coincide with the concrete ones *definitionally*
(`InfoGeometricGenerator.equivAbstract` — both round trips are `rfl`).

## Why bother

Because the quantum state space is **not** a classical statistical
model, yet carries exactly this kind of data.  Pure-state quantum
relative entropy is `+∞` between distinct states, so the KL-based
classical hierarchy cannot host it; but the pure-state manifold has a
perfectly good metric (the quantum Fisher / Fubini–Study metric) and
cubic tensor (which vanishes, by unitary isotropy).  Abstracting over
`(domain, g, C)` lets the classical bit and the qubit be compared
inside one definition — which is what `Dichotomy.lean` does.

**Not formalized here, and out of scope for this file** — two
motivating directions for later work, recorded so the abstraction's
target shape is on record:

1. Eguchi's contrast function formalism: carry an abstract divergence
   `D` and *derive* `g` and `C` from its 2- and 3-jets at the diagonal
   (KL recovers the classical case; `1 - F²` or `-log F²` the quantum
   pure-state case).
2. A symplectic form `ω` — the field that `RLDFisherModel` already
   carries — added alongside `(g, C)` so the data becomes the full
   pre-Kähler triple `(g, C, ω)`.

Everything actually defined and proved in this file is listed under
"Main definitions" below; this file itself only assembles the bare
`(domain, g, C)` interface and the concrete/abstract generator
equivalence.

## Main definitions

* `GeometricData` — a parameter domain with a metric-shaped and a
  cubic-shaped coefficient array.
* `GeometricData.Generator` — vector fields satisfying `L_X g = 0` and
  `L_X C = 0` on the domain, in coordinates.
* `TwiceDifferentiableModel.geometricData` — the forgetful map.
* `InfoGeometricGenerator.equivAbstract` — concrete generators of a
  model ≃ abstract generators of its data, definitionally.

## Tags

information geometry, Killing field, Amari–Chentsov tensor, abstraction
-/

open Finset

namespace Spectra.InformationGeometry

variable {n : ℕ}

/-- **Bare geometric data**: a parameter domain together with
metric-shaped and cubic-shaped coefficient arrays.

No regularity, symmetry, or positivity is assumed at this level; each
concrete instance carries whatever it can prove, and the generator
conditions are meaningful (if possibly vacuous) regardless.  In the
intended instances `metric` is a Riemannian metric in a chart and
`cubic` a totally symmetric (0,3)-tensor in the same chart. -/
structure GeometricData (n : ℕ) where
  /-- The open region of `ℝⁿ` where the data is meaningful. -/
  domain : Set (ParamSpace n)
  /-- Metric coefficients `g_{ij}(θ)`. -/
  metric : ParamSpace n → Fin n → Fin n → ℝ
  /-- Cubic tensor coefficients `C_{ijk}(θ)`. -/
  cubic : ParamSpace n → Fin n → Fin n → Fin n → ℝ

namespace GeometricData

/-- An **infinitesimal symmetry of geometric data**: a smooth vector
field whose Lie derivative annihilates both the metric and the cubic
tensor on the domain.  The two conditions are copied character-for-
character from `InfoGeometricGenerator`, with the model projections
replaced by the data fields. -/
structure Generator (Γ : GeometricData n) where
  /-- The vector field `X : Θ → ℝⁿ` in coordinates. -/
  vectorField : ParamSpace n → ParamSpace n
  /-- Smoothness of the field. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) vectorField
  /-- **Killing's equation**: `L_X g = 0`.  In coordinates:
  `∑ₖ Xᵏ ∂ₖg_{ij} + g_{kj} ∂ᵢXᵏ + g_{ik} ∂ⱼXᵏ = 0`. -/
  killing : ∀ θ ∈ Γ.domain, ∀ i j : Fin n,
    ∑ k : Fin n,
      (vectorField θ k *
        fderiv ℝ (fun θ' => Γ.metric θ' i j) θ
          (EuclideanSpace.single k 1) +
      Γ.metric θ k j *
        fderiv ℝ (fun θ' => vectorField θ' k) θ
          (EuclideanSpace.single i 1) +
      Γ.metric θ i k *
        fderiv ℝ (fun θ' => vectorField θ' k) θ
          (EuclideanSpace.single j 1)) = 0
  /-- **Cubic preservation**: `L_X C = 0`.  In coordinates:
  `∑ₗ Xˡ ∂ₗC_{ijk} + C_{ljk} ∂ᵢXˡ + C_{ilk} ∂ⱼXˡ + C_{ijl} ∂ₖXˡ = 0`. -/
  preserves_cubic : ∀ θ ∈ Γ.domain, ∀ i j k : Fin n,
    ∑ l : Fin n,
      (vectorField θ l *
        fderiv ℝ (fun θ' => Γ.cubic θ' i j k) θ
          (EuclideanSpace.single l 1) +
      Γ.cubic θ l j k *
        fderiv ℝ (fun θ' => vectorField θ' l) θ
          (EuclideanSpace.single i 1) +
      Γ.cubic θ i l k *
        fderiv ℝ (fun θ' => vectorField θ' l) θ
          (EuclideanSpace.single j 1) +
      Γ.cubic θ i j l *
        fderiv ℝ (fun θ' => vectorField θ' l) θ
          (EuclideanSpace.single k 1)) = 0

/-- Two generators with the same vector field are equal (the remaining
fields are propositions). -/
@[ext] lemma Generator.ext_vectorField {Γ : GeometricData n}
    {G₁ G₂ : Γ.Generator} (h : G₁.vectorField = G₂.vectorField) :
    G₁ = G₂ := by
  cases G₁; cases G₂; cases h; rfl

/-- Each coordinate component of a generator's field is smooth. -/
lemma Generator.contDiff_component {Γ : GeometricData n} (G : Γ.Generator)
    (k : Fin n) : ContDiff ℝ (⊤ : ℕ∞) fun θ => G.vectorField θ k := by
  have h : (fun θ => G.vectorField θ k)
      = ⇑(EuclideanSpace.proj k : ParamSpace n →L[ℝ] ℝ) ∘ G.vectorField := by
    funext θ
    simp [EuclideanSpace.coe_proj]
  rw [h]
  exact (EuclideanSpace.proj k : ParamSpace n →L[ℝ] ℝ).contDiff.comp G.smooth

end GeometricData

/-! ### The forgetful map from statistical models -/

namespace TwiceDifferentiableModel

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The geometric data of a twice differentiable statistical model:
forget everything except the parameter domain, the Fisher matrix, and
the cubic tensor. -/
noncomputable def geometricData (M : TwiceDifferentiableModel n Ω) : GeometricData n where
  domain := M.paramDomain
  metric := fun θ i j => M.toRegularStatisticalModel.fisherMatrix θ i j
  cubic := fun θ i j k => M.cubicTensor θ i j k

variable {M : TwiceDifferentiableModel n Ω}

/-- A concrete generator of a model is an abstract generator of its
geometric data.  All four fields transport unchanged: the proposition
types are definitionally equal after unfolding `geometricData`. -/
def InfoGeometricGenerator.toAbstract (G : InfoGeometricGenerator M) :
    M.geometricData.Generator :=
  ⟨G.vectorField, G.smooth, G.killing, G.preserves_cubic⟩

/-- An abstract generator of a model's geometric data is a concrete
generator of the model. -/
def InfoGeometricGenerator.ofAbstract (G : M.geometricData.Generator) :
    InfoGeometricGenerator M :=
  ⟨G.vectorField, G.smooth, G.killing, G.preserves_cubic⟩

/-- **The abstraction is lossless**: concrete generators of `M`
correspond definitionally to abstract generators of `M.geometricData`.
This is the license to prove theorems about `GeometricData.Generator`
and read them back on statistical models. -/
def InfoGeometricGenerator.equivAbstract (M : TwiceDifferentiableModel n Ω) :
    InfoGeometricGenerator M ≃ M.geometricData.Generator where
  toFun := InfoGeometricGenerator.toAbstract
  invFun := InfoGeometricGenerator.ofAbstract
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

end TwiceDifferentiableModel

end Spectra.InformationGeometry
