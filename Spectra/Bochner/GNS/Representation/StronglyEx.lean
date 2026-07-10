/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Strong Continuity Extension from a Dense Set

An abstract 3ε argument: if a family of isometries `U t` is strongly continuous on a dense
subset `D` of a Hilbert space `H`, it is strongly continuous on all of `H`.

## Main statements

* `strong_continuity_extends` — strong continuity on a dense set, plus isometry, extends to the
  whole space.

## Implementation notes

The proof is the standard 3ε argument (approximate, use continuity on the dense set, use
isometry to transport the bound back), needing only `hiso` (each `U t` preserves norms) and
`hD_cont` (continuity on `D`) — no group-law or identity hypothesis is needed. This lemma is
deliberately import-light (only Mathlib, no Spectra-internal dependency) so that any file in the
project can call it without risking an import cycle.

This exact 3ε extension shape is now also used by
`Bochner/GNS/Representation/StronglyCont.lean`'s `completionTranslate_strong_continuous` and
`Modular/KMS/UnitaryGroup.lean`'s `invariantUnitaryGroup` (via its `strong_continuous` field),
both of which call this lemma directly instead of re-proving the argument.

`StronglyCont.lean`'s `quotientTranslate_continuous` and `UnitaryGroup.lean`'s
`evolveU_continuous_coe` look similar (same ε/δ vocabulary) but solve a different sub-problem:
establishing continuity *at a single already-fixed dense-set point*, via a parallelogram/cross-term
identity (`‖x - y‖² = ‖x‖² + ‖y‖² - 2 Re⟨x,y⟩`) driven by a concrete inner-product formula specific
to their domain. That's the `hD_cont` *input* this lemma consumes, not an instance of its
conclusion, so it doesn't fit `strong_continuity_extends`'s signature and is intentionally left
alone.

## Tags

strong continuity, dense set, GNS construction, unitary group
-/

namespace Spectra.Bochner.GNS

/-- **Strong continuity extends to all of H.**

Given:
- Strong continuity on a dense set D ⊆ H
- Each U(t) is an isometry
Then U(t) is strongly continuous on all of H.

Standard 3ε argument: for ψ ∈ H and ε > 0,
1. Pick φ ∈ D with ‖ψ - φ‖ < ε/3
2. Pick δ so |t| < δ ⟹ ‖U(t)φ - φ‖ < ε/3
3. Then ‖U(t)ψ - ψ‖ ≤ ‖U(t)(ψ-φ)‖ + ‖U(t)φ - φ‖ + ‖φ - ψ‖
                       = ‖ψ-φ‖ + ‖U(t)φ - φ‖ + ‖φ - ψ‖ < ε -/
lemma strong_continuity_extends {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : ℝ → H →ₗ[ℂ] H)
    (hiso : ∀ t ψ, ‖U t ψ‖ = ‖ψ‖)
    (D : Set H) (hD : Dense D)
    (hD_cont : ∀ φ ∈ D, Continuous (fun t => U t φ)) :
    ∀ ψ, Continuous (fun t => U t ψ) := by
  -- Key lemma: U(t) preserves distances (from norm preservation + linearity)
  have hdist_iso : ∀ (s : ℝ) (a b : H), dist (U s a) (U s b) = dist a b := by
    intro s a b; simp only [dist_eq_norm, ← map_sub, hiso]
  intro ψ
  rw [continuous_iff_continuousAt]; intro t₀
  rw [Metric.continuousAt_iff]; intro ε hε
  -- Step 1: Approximate ψ by φ ∈ D with ‖ψ - φ‖ < ε/3
  obtain ⟨φ, hφD, hφ_close⟩ :=
    Metric.mem_closure_iff.mp (hD ψ) (ε / 3) (by positivity)
  -- Step 2: From continuity of t ↦ U(t)φ at t₀, get δ
  obtain ⟨δ, hδ, hδ_spec⟩ := Metric.continuousAt_iff.mp
    (hD_cont φ hφD).continuousAt (ε / 3) (by positivity)
  -- Step 3: The 3ε argument
  refine ⟨δ, hδ, fun {t} ht => ?_⟩
  calc dist (U t ψ) (U t₀ ψ)
      ≤ dist (U t ψ) (U t φ) +
        dist (U t φ) (U t₀ φ) +
        dist (U t₀ φ) (U t₀ ψ) := by
          linarith [dist_triangle (U t ψ) (U t φ) (U t₀ ψ),
                    dist_triangle (U t φ) (U t₀ φ) (U t₀ ψ)]
    _ < ε / 3 + ε / 3 + ε / 3 := by
          -- Term 1: dist(U(t)ψ, U(t)φ) = dist(ψ, φ) < ε/3
          have h1 : dist (U t ψ) (U t φ) < ε / 3 := by
            rw [hdist_iso]; exact hφ_close
          -- Term 2: dist(U(t)φ, U(t₀)φ) < ε/3 by continuity on D
          have h2 : dist (U t φ) (U t₀ φ) < ε / 3 := hδ_spec ht
          -- Term 3: dist(U(t₀)φ, U(t₀)ψ) = dist(φ, ψ) < ε/3
          have h3 : dist (U t₀ φ) (U t₀ ψ) < ε / 3 := by
            rw [hdist_iso, dist_comm]; exact hφ_close
          linarith
    _ = ε := by ring

end Spectra.Bochner.GNS
