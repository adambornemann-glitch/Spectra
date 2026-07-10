/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ported from Isabelle/HOL formalization by Echenim & Mhalla, by Adam Bornemann
-/
import Mathlib.Algebra.Star.CHSH
import Spectra.QuantumMechanics.BellsTheorem.QuantumCHSH.Violation
import Spectra.QuantumMechanics.BellsTheorem.CHSH_Bounds.Tsirelson.Basic
/-!
# Tsirelson's Bound (front-door restatement)

`tsirelson_bound` (`CHSH_Bounds/Tsirelson/Basic.lean`) is stated over a bundled `IsCHSHTuple`
structure. This file re-exposes it with the eight `IsCHSHTuple` fields unpacked as plain
hypotheses, so callers building `A₀, A₁, B₀, B₁` directly (rather than already holding an
`IsCHSHTuple` term) don't have to construct the record by hand — hence the trailing `'`, marking
this as the unpacked-hypothesis sibling of the original.

## Main results

* `tsirelson_bound'` : `‖Tr(Sρ)‖ ≤ 2√2` for any `A₀, A₁, B₀, B₁` satisfying the CHSH
  Hermitian/involution/commutation conditions individually, no `IsCHSHTuple` construction required
-/
open Spectra.QuantumInfo
namespace Spectra.QuantumCHSH

/-- **Tsirelson's Bound**: No quantum state can achieve `|S| > 2√2`.

The proof uses `S² = 4I - [A₀,A₁]·[B₀,B₁]` and operator norm bounds. -/
lemma tsirelson_bound' {n : ℕ} [NeZero n]
    (A₀' A₁' B₀' B₁' : Matrix (Fin n) (Fin n) ℂ)
    (hA₀ : A₀'.IsHermitian) (hA₁ : A₁'.IsHermitian)
    (hB₀ : B₀'.IsHermitian) (hB₁ : B₁'.IsHermitian)
    (hA₀_sq : A₀' * A₀' = 1) (hA₁_sq : A₁' * A₁' = 1)
    (hB₀_sq : B₀' * B₀' = 1) (hB₁_sq : B₁' * B₁' = 1)
    (hcomm₀₀ : A₀' * B₀' = B₀' * A₀') (hcomm₀₁ : A₀' * B₁' = B₁' * A₀')
    (hcomm₁₀ : A₁' * B₀' = B₀' * A₁') (hcomm₁₁ : A₁' * B₁' = B₁' * A₁')
    (ρ : DensityMatrix n) :
    ‖(((A₀' * B₁' - A₀' * B₀' + A₁' * B₀' + A₁' * B₁') * ρ.toMatrix).trace)‖
      ≤ 2 * Real.sqrt 2 := by
  have hA₀_inv : A₀' ^ 2 = 1 := by rw [pow_two]; exact hA₀_sq
  have hA₁_inv : A₁' ^ 2 = 1 := by rw [pow_two]; exact hA₁_sq
  have hB₀_inv : B₀' ^ 2 = 1 := by rw [pow_two]; exact hB₀_sq
  have hB₁_inv : B₁' ^ 2 = 1 := by rw [pow_two]; exact hB₁_sq
  have hT : IsCHSHTuple A₀' A₁' B₀' B₁' :=
    ⟨hA₀_inv, hA₁_inv, hB₀_inv, hB₁_inv, hA₀, hA₁, hB₀, hB₁,
      hcomm₀₀, hcomm₀₁, hcomm₁₀, hcomm₁₁⟩
  have h := tsirelson_bound A₀' A₁' B₀' B₁' hT ρ
  simp only [chshExpect, chshOp] at h
  exact h

end Spectra.QuantumCHSH
