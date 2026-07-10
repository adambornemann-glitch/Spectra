/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
/-!
# The Popescu–Rohrlich Box

This file formalizes the Popescu–Rohrlich (PR) box (Popescu–Rohrlich, 1994): an explicit, finite
bipartite correlation table that satisfies the no-signaling constraint exactly, yet hits the
*algebraic maximum* CHSH value of `4` — strictly beyond both the classical local-hidden-variable
bound of `2` (`Spectra.BellTheorem.lhv_chsh_bound`, `LHV.lean`) and Tsirelson's quantum bound of
`2√2` (`Spectra.QuantumCHSH.tsirelson_bound'`). It is a standalone finite object: unlike
`Bell1964.lean`/`Wigner.lean`, it shares no machinery with the rest of this project, since a PR box
is not (and provably cannot be) realized by any quantum state or local hidden-variable model — it
lives in the strictly larger world of abstract no-signaling correlations.

## Main definitions/results

* `IsNoSignalingAlice`, `IsNoSignalingBob` : Alice's (resp. Bob's) marginal outcome distribution is
  independent of the other party's choice of setting.
* `IsProbabilityTable` : nonnegativity and normalization of a correlation table `P x y a b`.
* `PRbox` : the table `P(a,b|x,y) = 1/2` if `a ⊕ b = x ∧ y`, else `0`.
* `prBox_isProbabilityTable`, `prBox_isNoSignalingAlice`, `prBox_isNoSignalingBob` : the PR box is a
  genuine no-signaling probability table.
* `PRbox_correlation` : the `±1`-valued correlation `E(x,y) := Σ (-1)^(a⊕b) P(a,b|x,y)`.
* `prBox_chsh_eq_four` : **the headline fact** — the CHSH combination
  `E(0,0) + E(0,1) + E(1,0) - E(1,1)` equals `4`, the algebraic maximum.
* `prBox_chsh_exceeds_tsirelson` : `2 * √2 < 4`, so the PR box's value exceeds even the quantum
  Tsirelson bound (and, a fortiori, the classical bound of `2`).

## References

S. Popescu, D. Rohrlich, *"Quantum nonlocality as an axiom,"* Found. Phys. 24, 379 (1994).
-/

namespace Spectra.BellTheorem

/-! ## No-Signaling Correlation Tables -/

/-- Alice's marginal outcome distribution (summed over Bob's outcome) does not depend on Bob's
setting `y`. -/
def IsNoSignalingAlice (P : Bool → Bool → Bool → Bool → ℝ) : Prop :=
  ∀ x a y y', P x y a true + P x y a false = P x y' a true + P x y' a false

/-- Bob's marginal outcome distribution (summed over Alice's outcome) does not depend on Alice's
setting `x`. -/
def IsNoSignalingBob (P : Bool → Bool → Bool → Bool → ℝ) : Prop :=
  ∀ y b x x', P x y true b + P x y false b = P x' y true b + P x' y false b

/-- A genuine correlation table: nonnegative entries, normalized for each choice of settings. -/
def IsProbabilityTable (P : Bool → Bool → Bool → Bool → ℝ) : Prop :=
  (∀ x y a b, 0 ≤ P x y a b) ∧
    ∀ x y, P x y true true + P x y true false + P x y false true + P x y false false = 1

/-! ## The PR Box -/

/-- The Popescu–Rohrlich box: outcomes `a, b` are equally likely to be `(same, same)` or
`(different, different)` — whichever parity matches `x ∧ y` — and impossible otherwise. -/
noncomputable def PRbox (x y a b : Bool) : ℝ :=
  if a.xor b = (x && y) then (1 / 2 : ℝ) else 0

lemma prBox_isProbabilityTable : IsProbabilityTable PRbox := by
  constructor
  · intro x y a b
    unfold PRbox
    split <;> norm_num
  · intro x y
    rcases x with _ | _ <;> rcases y with _ | _ <;> simp [PRbox] <;> norm_num

lemma prBox_isNoSignalingAlice : IsNoSignalingAlice PRbox := by
  intro x a y y'
  rcases x with _ | _ <;> rcases a with _ | _ <;> rcases y with _ | _ <;> rcases y' with _ | _ <;>
    simp [PRbox]

lemma prBox_isNoSignalingBob : IsNoSignalingBob PRbox := by
  intro y b x x'
  rcases y with _ | _ <;> rcases b with _ | _ <;> rcases x with _ | _ <;> rcases x' with _ | _ <;>
    simp [PRbox]

/-! ## The CHSH Correlation, and the Algebraic Maximum -/

/-- The `±1`-valued correlation `E(x, y) := P(same|x,y) - P(different|x,y)`, i.e.
`Σ_{a,b} (-1)^(a ⊕ b) P(a,b|x,y)`. -/
noncomputable def PRbox_correlation (x y : Bool) : ℝ :=
  PRbox x y true true - PRbox x y true false - PRbox x y false true + PRbox x y false false

/-- The PR box gives perfect correlation (`E = 1`) at every setting pair except `(true, true)`,
where it gives perfect *anti*-correlation (`E = -1`). -/
lemma PRbox_correlation_eq (x y : Bool) : PRbox_correlation x y = if x && y then -1 else 1 := by
  rcases x with _ | _ <;> rcases y with _ | _ <;> simp [PRbox_correlation, PRbox] <;> norm_num

/-- **The PR box hits the algebraic maximum.** The CHSH combination
`E(0,0) + E(0,1) + E(1,0) - E(1,1)` equals `4` — the largest value algebraically possible for a
sum of four `±1`-bounded terms, strictly beyond both the classical bound `2`
(`Spectra.BellTheorem.lhv_chsh_bound`) and Tsirelson's quantum bound `2√2`
(`Spectra.QuantumCHSH.tsirelson_bound'`). -/
theorem prBox_chsh_eq_four :
    PRbox_correlation false false + PRbox_correlation false true +
        PRbox_correlation true false - PRbox_correlation true true = 4 := by
  simp [PRbox_correlation_eq]; norm_num

/-- `2√2 < 4`: the PR box's algebraic maximum strictly exceeds Tsirelson's quantum bound (and,
since `2 < 2√2`, the classical local-hidden-variable bound as well). -/
theorem prBox_chsh_exceeds_tsirelson : (2 : ℝ) * Real.sqrt 2 < 4 := by
  have h : Real.sqrt 2 < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith

end Spectra.BellTheorem
