/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.SchrodingerEquation
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Ehrenfest's Theorem

Ehrenfest's theorem: the time-derivative of the expectation value of a bounded observable
`B` in the state `ψ(t) = U(t)ψ₀` evolving under a one-parameter unitary group `U_grp` with
generator `A`, for `ψ₀ ∈ dom(A)`.

## Main results

* `ehrenfest_theorem`: `d/dt ⟪ψ(t), Bψ(t)⟫ = ⟪iAψ(t), Bψ(t)⟫ + ⟪ψ(t), B(iAψ(t))⟫`.

## Implementation notes

`B` is required to be a bounded (continuous) operator so that `ψ ↦ Bψ` is differentiable
in `t` for free via `ContinuousLinearMap.hasFDerivAt`, composed with the Schrödinger equation
for `ψ(t)`. The dynamics enters only through `schrodingerEquation`; the product rule for the
`ℂ`-inner product is mathlib's `HasDerivAt.inner`. When `B` additionally preserves `dom(A)`,
the right-hand side collapses to the more familiar commutator form `i⟪ψ(t), [A,B]ψ(t)⟫`, but
that specialization is not needed to state or prove the result below.

## References
* Ehrenfest, "Bemerkung über die angenäherte Gültigkeit der klassischen Mechanik innerhalb der
  Quantenmechanik" (1927)
-/

open InnerProductSpace Complex
open Spectra.OneParameterUnitaryGroup
open Spectra.QuantumMechanics.Schrodinger

namespace Spectra.QuantumMechanics.Ehrenfest

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Ehrenfest's theorem.** For a bounded observable `B` and `ψ₀ ∈ dom(A)` (with
`A := generator U_grp`), the expectation value `⟪ψ(t), B ψ(t)⟫` evolves by

  `d/dt ⟪ψ(t), B ψ(t)⟫ = ⟪i A ψ(t), B ψ(t)⟫ + ⟪ψ(t), B (i A ψ(t))⟫`,

which equals `i⟪ψ(t), [A,B]ψ(t)⟫` when `B` preserves `dom(A)`. -/
theorem ehrenfest_theorem (U_grp : OneParameterUnitaryGroup (H := H))
    (B : H →L[ℂ] H) (ψ₀ : H) (hψ₀ : ψ₀ ∈ (generator U_grp).domain) (t₀ : ℝ) :
    let ψ_t  := U_grp.U t₀ ψ₀
    let Aψ_t := generator U_grp ⟨ψ_t, generator_domain_invariant U_grp t₀ ⟨ψ₀, hψ₀⟩⟩
    HasDerivAt (fun t => ⟪U_grp.U t ψ₀, B (U_grp.U t ψ₀)⟫_ℂ)
               (⟪I • Aψ_t, B ψ_t⟫_ℂ + ⟪ψ_t, B (I • Aψ_t)⟫_ℂ) t₀ := by
  intro ψ_t Aψ_t
  -- Schrödinger gives ψ'(t₀) = i A ψ(t₀)
  have hf := schrodingerEquation U_grp ψ₀ hψ₀ t₀
  -- push through the bounded operator B
  have hg : HasDerivAt (fun t => B (U_grp.U t ψ₀)) (B (I • Aψ_t)) t₀ := by
    have h := (B.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t₀ hf
    simp only [map_smul]
    simp only [ContinuousLinearMap.coe_restrictScalars', generator_domain, map_smul] at h
    exact HasDerivAt.congr_deriv h rfl
  -- product rule for the ℂ-inner product (mathlib's `HasDerivAt.inner`, reordered to match)
  have h := hf.inner ℂ hg
  rw [add_comm] at h
  exact h

end Spectra.QuantumMechanics.Ehrenfest
