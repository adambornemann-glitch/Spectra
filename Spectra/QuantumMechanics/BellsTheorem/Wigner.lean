/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-!
# Wigner's (1970) Set-Theoretic Form of Bell's Theorem

This file formalizes E.P. Wigner's 1970 reformulation of Bell's inequality as an elementary
consequence of finite set theory: partition an ensemble of hidden-variable classes by the sign each
class would give at each of three measurement settings, and read off a Boole/Bonferroni-type
inequality among the resulting joint frequencies. It reaches essentially the same physical
conclusion as `Bell1964.lean`'s `bell_1964_inequality`, but via a genuinely different route: no
measure theory, integration, or real-analytic machinery anywhere — the whole argument lives in
`Finset.card` and subset/union reasoning over a finite population.

## Main definitions/results

* `wigner_subset` : `A \ B ⊆ (A \ C) ∪ (C \ B)` for any three finite sets — a case split on
  membership in `C` (excluded middle), the combinatorial engine behind everything else here.
* `wigner_card_le` : `|A \ B| ≤ |A \ C| + |C \ B|`, via monotonicity and subadditivity of
  `Finset.card`.
* `wigner_inequality` : the physical form — for three sign functions `σa, σb, σc : Ω → Bool`
  recording a finite ensemble's would-be outcome at each of three settings, the fraction with
  `σa = true, σb = false` is at most the sum of the fractions with (`σa = true, σc = false`) and
  (`σc = true, σb = false`).

## Implementation notes

`σa, σb, σc` play exactly the role of `Bell1964.lean`'s single reduced response family
`Aa, Ab, Ac` (the perfect-anti-correlation argument that lets one function describe both Alice's
and Bob's outcomes is not re-derived here; see `perfect_anticorrelation_forces_determinism`) — but
this file works with a *finite* population and exact `Bool` values rather than a general
`ProbabilityMeasure` and `±1`-a.e.-valued `ResponseFunction`s, so nothing from `LHV.lean` is
imported or reused.

## References

E.P. Wigner, *"On Hidden Variables and Quantum Mechanical Probabilities,"* Am. J. Phys. 38, 1005
(1970).
-/

namespace Spectra.BellTheorem

/-! ## The Combinatorial Core -/

/-- For any three finite subsets `A, B, C` of a common type: an element of `A` but not `B` is
either in `C` (hence in `C \ B`) or not in `C` (hence in `A \ C`) — the whole content is a case
split on membership in `C`, via excluded middle. -/
lemma wigner_subset {Ω : Type*} [DecidableEq Ω] (A B C : Finset Ω) :
    A \ B ⊆ (A \ C) ∪ (C \ B) := by
  intro ω hω
  simp only [Finset.mem_sdiff] at hω
  obtain ⟨hA, hB⟩ := hω
  by_cases hC : ω ∈ C
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hC, hB⟩)
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hA, hC⟩)

/-- **Wigner's (1970) counting inequality.** `|A \ B| ≤ |A \ C| + |C \ B|`, an elementary
consequence of `wigner_subset` via monotonicity (`Finset.card_le_card`) and subadditivity
(`Finset.card_union_le`) of `Finset.card` — pure finite combinatorics, no measure theory. -/
lemma wigner_card_le {Ω : Type*} [DecidableEq Ω] (A B C : Finset Ω) :
    (A \ B).card ≤ (A \ C).card + (C \ B).card :=
  (Finset.card_le_card (wigner_subset A B C)).trans (Finset.card_union_le _ _)

/-! ## The Physical Inequality -/

/-- **Wigner's inequality, physical form.** For a finite ensemble `Ω` of hidden-variable classes
and three sign functions `σa, σb, σc : Ω → Bool` recording each class's would-be outcome at each of
three measurement settings, the fraction of the ensemble with `σa = true` and `σb = false` is at
most the sum of the fractions with (`σa = true`, `σc = false`) and (`σc = true`, `σb = false`). -/
theorem wigner_inequality {Ω : Type*} [Fintype Ω] (σa σb σc : Ω → Bool) :
    (Finset.univ.filter (fun ω => σa ω = true ∧ σb ω = false)).card / (Fintype.card Ω : ℝ)
      ≤ (Finset.univ.filter (fun ω => σa ω = true ∧ σc ω = false)).card / (Fintype.card Ω : ℝ)
        + (Finset.univ.filter (fun ω => σc ω = true ∧ σb ω = false)).card
          / (Fintype.card Ω : ℝ) := by
  classical
  set A := Finset.univ.filter (fun ω => σa ω = true) with hA
  set B := Finset.univ.filter (fun ω => σb ω = true) with hB
  set C := Finset.univ.filter (fun ω => σc ω = true) with hC
  have eAB : Finset.univ.filter (fun ω => σa ω = true ∧ σb ω = false) = A \ B := by
    ext ω; simp [hA, hB, Bool.not_eq_true]
  have eAC : Finset.univ.filter (fun ω => σa ω = true ∧ σc ω = false) = A \ C := by
    ext ω; simp [hA, hC, Bool.not_eq_true]
  have eCB : Finset.univ.filter (fun ω => σc ω = true ∧ σb ω = false) = C \ B := by
    ext ω; simp [hC, hB, Bool.not_eq_true]
  rw [eAB, eAC, eCB, ← add_div]
  gcongr
  exact_mod_cast wigner_card_le A B C

end Spectra.BellTheorem
