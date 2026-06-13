/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: Stage_2/Algebra/TensorLift.lean
-/
import Spectra.Mathlib.StochasticCalc.RoughPath.Integral.Defect
import Spectra.Mathlib.StochasticCalc.YoungIntegration.Defect
import Spectra.Mathlib.StochasticCalc.RoughPath.Axioms.NormedTensorSquare
import Spectra.Mathlib.StochasticCalc.RoughPath.Axioms.TruncatedTensorData
import Spectra.Mathlib.StochasticCalc.RoughPath.Algebra.TruncTensor2
import Spectra.Mathlib.StochasticCalc.RoughPath.Algebra.GroupLike
import Spectra.Mathlib.StochasticCalc.RoughPath.Algebra.HomoNorm
import Spectra.Mathlib.StochasticCalc.RoughPath.Defs
/-!
# Universal property of the normed tensor square and the evaluation pairing

## Overview

This file axiomatizes the **universal property** of `T₂ V`: every continuous
bilinear map `V →L[ℝ] V →L[ℝ] W` factors uniquely through `T₂ V` via `lift`.

It then constructs the **evaluation pairing** — the canonical
`RoughIntegralPairing (V →L[ℝ] W) V W` used for the rough differential
equation `dY = f(Y) d𝐗`.

## Why axioms?

The universal property of the tensor product is a theorem for any concrete
model (projective tensor product, Hilbert-Schmidt, etc.). However,
`NormedTensorSquare` is axiomatized as a typeclass with an abstract type
`T₂ V`, and Lean 4's universe polymorphism makes it difficult to add
`lift` as a class field — the target space `W` would need to be
universe-polymorphic within the class, creating universe variable mismatches.

The cleanest solution: axiomatize `lift` externally. The three axioms
(`lift`, `lift_tprod`, `lift_norm_le`) are satisfied by every concrete
model of `NormedTensorSquare` and are mathematically unimpeachable.

## What depends on this file

* **`Picard/Map.lean`** — the evaluation pairing is the `RoughIntegralPairing`
  used to define the Picard map `𝓜(Y) = y₀ + ∫ f(Y) d𝐗`.

* **Phase 4.5 (Chain rule)** — the Itô formula involves `D²φ(Y)` acting
  on `f(Y) ⊗ f(Y) ∈ T₂ V`, which is exactly `lift (D²φ(Y))`.

* **Any future bilinear-on-tensor construction** — `lift` is the universal
  interface for extending bilinear maps to `T₂ V`.

## The axioms

| Axiom | Statement | Mathematical content |
|-------|-----------|---------------------|
| `lift` | `(V →L[ℝ] V →L[ℝ] W) → (T₂ V →L[ℝ] W)` | Universal property (existence) |
| `lift_tprod` | `lift φ (v ⊗ₜ w) = φ v w` | Factors through tprod |
| `lift_norm_le` | `‖lift φ‖ ≤ ‖φ‖` | Cross-norm property |
| `lift_comp_tprod` | `(lift φ) ∘L (tprod v) = φ v` | CLM-level factoring |

## References

* Ryan, R., *Introduction to Tensor Products of Banach Spaces*, Springer (2002)
* Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., §2.1
-/
open Real
open Spectra.Mathlib.StochCalc
open NormedTensorSquare
open TruncTensor₂ GroupLike₂ RoughPath

namespace Spectra.Mathlib.StochCalc
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedTensorSquare V]

namespace NormedTensorSquare
/-! ### The universal property of T₂ V -/

/-- **Universal property (existence)**: every continuous bilinear map
`φ : V →L[ℝ] V →L[ℝ] W` lifts to a continuous linear map `T₂ V →L[ℝ] W`.

This is the defining property of the tensor product: bilinear maps on `V × V`
correspond to linear maps on `V ⊗ V`. The normed version adds the continuity
and norm bound. -/
axiom lift
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : V →L[ℝ] V →L[ℝ] W) : (T₂ V) →L[ℝ] W

/-- **Factoring property**: `lift φ` agrees with `φ` on pure tensors.

    `lift φ (v ⊗ₜ w) = φ v w`

This is the universal property: `lift` is the unique extension of `φ`
from `V × V` to `T₂ V`. -/
@[simp] axiom lift_tprod
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : V →L[ℝ] V →L[ℝ] W) (v w : V) :
    lift φ ((tprod v) w) = φ v w

/-- **Norm bound**: the lift does not amplify norms.

    `‖lift φ‖ ≤ ‖φ‖`

This is the cross-norm property: the tensor product norm is defined so that
the canonical map `V × V → T₂ V` has norm ≤ 1, which dualizes to
`‖lift φ‖ ≤ ‖φ‖`. -/
axiom lift_norm_le
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : V →L[ℝ] V →L[ℝ] W) :
    ‖lift φ‖ ≤ ‖φ‖

/-- **CLM-level factoring**: `lift φ ∘ tprod(v) = φ(v)` as continuous
linear maps `V →L[ℝ] W`.

This is the pointwise factoring property promoted to an equality of CLMs.
Useful when manipulating compositions of linear maps (e.g., in the chain
rule, where you need `(lift D²φ) ∘ (tprod (f(Y))) = D²φ(f(Y))`). -/
axiom lift_comp_tprod
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : V →L[ℝ] V →L[ℝ] W) (v : V) :
    (lift φ).comp (tprod v) = φ v

end NormedTensorSquare

/-! ### The evaluation pairing -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedTensorSquare V]
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The level-2 pairing `τ` as a continuous linear map.

    `τ(φ)(𝕏) = lift(φ)(𝕏)`

where `φ : V →L[ℝ] (V →L[ℝ] W)` and `𝕏 ∈ T₂ V`.

On pure tensors: `τ(φ)(v ⊗ₜ w) = φ(v)(w)`.

This extends a "doubly-linear" map `φ` — which takes a `V` and
produces a linear map `V → W` — to act on the full tensor product. -/
axiom evalPairing_τ
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedTensorSquare V]
    (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W] :
    (V →L[ℝ] (V →L[ℝ] W)) →L[ℝ] (T₂ V) →L[ℝ] W

/-- `τ(φ)` acts on pure tensors by double evaluation. -/
@[simp] axiom evalPairing_τ_tprod
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedTensorSquare V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : V →L[ℝ] (V →L[ℝ] W)) (v w : V) :
    evalPairing_τ V W φ ((tprod v) w) = φ v w

/-- Norm bound on `τ`: `‖τ(φ)‖ ≤ ‖φ‖` for all `φ`.

This implies `‖τ‖ ≤ 1` but is stated in a form that avoids
the double-CLM norm instance synthesis issue. -/
axiom evalPairing_τ_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedTensorSquare V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : V →L[ℝ] (V →L[ℝ] W)) :
    ‖evalPairing_τ V W φ‖ ≤ ‖φ‖

/-- **The evaluation pairing**: the canonical `RoughIntegralPairing`
for the RDE `dY = f(Y) d𝐗`.

- `σ(L, v) = L(v)` — evaluate the linear map at the increment
- `τ(φ, 𝕏)` — extend φ through the tensor product

The compatibility condition `σ(φ(v), w) = τ(φ, v ⊗ₜ w)` says:
    `φ(v)(w) = τ(φ)(v ⊗ₜ w)`
which is the defining property of `τ`. -/
noncomputable def evalPairing : RoughIntegralPairing (V →L[ℝ] W) V W where
  σ := ContinuousLinearMap.id ℝ (V →L[ℝ] W)
  τ := evalPairing_τ V W
  compat := fun φ v w => by
    simp only [ContinuousLinearMap.id_apply, evalPairing_τ_tprod]

/-! ### Norm bounds on the evaluation pairing

These feed into the contraction constant in Phase 4.2. -/

/-- `‖σ‖ ≤ 1` for the evaluation pairing.

    `‖σ(L, v)‖ = ‖L(v)‖ ≤ ‖L‖ · ‖v‖`

so the operator norm of σ is at most 1. -/
theorem evalPairing_σ_norm_le :
    ‖(evalPairing (V := V) (W := W)).σ‖ ≤ 1 := by
  simp only [evalPairing]
  exact ContinuousLinearMap.norm_id_le

/-- `‖τ‖ ≤ 1` for the evaluation pairing. -/
theorem evalPairing_τ_norm_le' :
    ‖(evalPairing (V := V) (W := W)).τ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun φ => by rw [one_mul]; exact evalPairing_τ_bound φ)
/-- Combined: both pairing norms are at most 1.

This simplifies the contraction constant: wherever `‖P.σ‖` or `‖P.τ‖`
appears, it can be bounded by 1 when using the evaluation pairing. -/
theorem evalPairing_norms_le_one :
    ‖(evalPairing (V := V) (W := W)).σ‖ ≤ 1 ∧
    ‖(evalPairing (V := V) (W := W)).τ‖ ≤ 1 :=
  ⟨evalPairing_σ_norm_le, evalPairing_τ_norm_le'⟩

end Spectra.Mathlib.StochCalc
