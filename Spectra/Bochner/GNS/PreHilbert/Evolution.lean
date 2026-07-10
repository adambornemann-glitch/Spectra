/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Bochner.GNS.PreHilbert.Defs

/-!
# Evaluating the GNS Pre-Inner Product on Point Masses

Evaluates `pdInner` on basis elements `Finsupp.single a c`, culminating in the embryonic
GNS key identity `⟨δₐ, δ_b⟩_f = f(b - a)`, which specializes (with `a = 0`, `b = t`) to
`⟨ξ, U(t)ξ⟩_f = f(t)` as advertised in `Defs.lean`.

## Main statements

* `pdInner_single_single` — `⟨cₐ · δₐ, c_b · δ_b⟩_f = c̄ₐ · c_b · f(b - a)`.
* `pdInner_single_one` — the unit-mass specialization `⟨δₐ, δ_b⟩_f = f(b - a)`.
-/

open Finsupp

namespace Spectra.Bochner.GNS

-- §2  Evaluation on basis elements

/-- The zero-at-zero side condition required by `Finsupp.sum_single_index`. -/
private lemma pdInner_aux_zero (f : ℝ → ℂ) (β : ℝ →₀ ℂ) (t : ℝ) :
    (β.sum fun s ds => starRingEnd ℂ (0 : ℂ) * ds * f (s - t)) = 0 := by
  simp [map_zero, zero_mul, Finsupp.sum]

/-- Inner product of two point masses.

`⟨cₐ · δₐ, c_b · δ_b⟩_f = c̄ₐ · c_b · f(b - a)` -/
@[simp]
lemma pdInner_single_single (f : ℝ → ℂ) (a b : ℝ) (ca cb : ℂ) :
    pdInner f (Finsupp.single a ca) (Finsupp.single b cb) =
    starRingEnd ℂ ca * cb * f (b - a) := by
  unfold pdInner
  rw [Finsupp.sum_single_index (pdInner_aux_zero f _ a)]
  rw [Finsupp.sum_single_index (by simp [mul_zero])]

/-- Specialization to unit point masses: `⟨δₐ, δ_b⟩_f = f(b - a)`. This is the GNS key
identity `⟨ξ, U(t)ξ⟩_f = f(t)` in embryonic form, obtained by taking `a = 0`, `b = t`. -/
lemma pdInner_single_one (f : ℝ → ℂ) (a b : ℝ) :
    pdInner f (Finsupp.single a 1) (Finsupp.single b 1) = f (b - a) := by
  simp [map_one]

end Spectra.Bochner.GNS
