/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Quantum.Entropy.Spectral

/-!
# Classical Shannon entropy

The **Shannon entropy** `H(p) = ∑ᵢ negMulLog pᵢ = -∑ᵢ pᵢ log pᵢ` of a discrete probability
distribution `p`, valued in `ℝ≥0∞` (so it is `+∞` for slowly-decaying distributions, in step with
the von Neumann entropy).  Working over an arbitrary index type `ι` and `ℝ≥0∞`-valued weights lets
this single definition serve both the classical index of an ensemble (`DensityOperator.weight`) and
the eigen-index of a quantum state (`QState.eigenvalue`).

For a genuine probability distribution (`∑ᵢ pᵢ = 1`, so each `pᵢ ≤ 1`) every summand
`negMulLog (pᵢ) ≥ 0`, so the `ENNReal.ofReal` truncation is lossless — the same discipline as
`vonNeumannEntropy_eq_tsum` and `measuredCrossEntropy`.

The headline connection: **the von Neumann entropy of a state is exactly the Shannon entropy of its
eigenvalue distribution**, `S(ρ) = H(λ(ρ))` (`vonNeumannEntropy_eq_shannonEntropy`).  This is the
precise sense in which "quantum entropy is classical entropy in the eigenbasis", and it is the
bridge on which the Holevo bound `S(ρ) ≤ H(ensemble weights)` will rest.

## Main definitions

* `shannonEntropy p` — `H(p) = ∑ᵢ negMulLog pᵢ`, valued in `ℝ≥0∞`.

## Main results

* `shannonEntropy_nonneg` — `0 ≤ H(p)`.
* `vonNeumannEntropy_eq_shannonEntropy` — `S(ρ) = H(λ(ρ))`, the von Neumann entropy is the Shannon
  entropy of the eigenvalue distribution.
-/

open scoped ENNReal NNReal

namespace Spectra.InformationGeometry.Quantum

/-- The **Shannon entropy** `H(p) = ∑ᵢ negMulLog pᵢ` of a discrete weight family `p : ι → ℝ≥0∞`,
valued in `ℝ≥0∞`.  For a probability distribution each summand is `≥ 0`, so the `ENNReal.ofReal` is
lossless; the codomain `ℝ≥0∞` allows `H(p) = +∞`. -/
noncomputable def shannonEntropy {ι : Type*} (p : ι → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (Real.negMulLog (p i).toReal)

/-- The Shannon entropy is nonnegative. -/
lemma shannonEntropy_nonneg {ι : Type*} (p : ι → ℝ≥0∞) : 0 ≤ shannonEntropy p := zero_le

/-- **The Shannon entropy vanishes exactly at a point mass.**  For a distribution (`pᵢ ≤ 1`),
`H(p) = 0` iff every `pᵢ ∈ {0, 1}` — i.e. all the mass sits on a single outcome.  (`negMulLog` is
`> 0` strictly inside `(0,1)`, so a vanishing entropy forces each weight to a corner.) -/
lemma shannonEntropy_eq_zero_iff {ι : Type*} (p : ι → ℝ≥0∞) (hp : ∀ i, p i ≤ 1) :
    shannonEntropy p = 0 ↔ ∀ i, p i = 0 ∨ p i = 1 := by
  rw [shannonEntropy, ENNReal.tsum_eq_zero]
  refine forall_congr' fun i => ?_
  have hne : p i ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hp i)
  have h0 : 0 ≤ (p i).toReal := ENNReal.toReal_nonneg
  have h1 : (p i).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top (hp i)
  rw [ENNReal.ofReal_eq_zero]
  constructor
  · intro hle
    have _hz : Real.negMulLog (p i).toReal = 0 := le_antisymm hle (Real.negMulLog_nonneg h0 h1)
    have hxreal : (p i).toReal = 0 ∨ (p i).toReal = 1 := by
      by_contra hc
      push Not at hc
      have hpos : 0 < (p i).toReal := h0.lt_of_ne (Ne.symm hc.1)
      have hlt : (p i).toReal < 1 := h1.lt_of_ne hc.2
      have : 0 < Real.negMulLog (p i).toReal := by
        rw [Real.negMulLog_eq_neg]
        exact neg_pos.mpr (mul_neg_of_pos_of_neg hpos (Real.log_neg hpos hlt))
      linarith
    rcases hxreal with hx | hx
    · rcases (ENNReal.toReal_eq_zero_iff (p i)).mp hx with h | h
      · exact Or.inl h
      · exact absurd h hne
    · exact Or.inr (by rw [← ENNReal.ofReal_toReal hne, hx, ENNReal.ofReal_one])
  · rintro (h | h) <;> rw [h] <;> simp

/-- **Concavity of the Shannon entropy.**  Mixing two distributions never decreases entropy:
`t·H(p) + (1−t)·H(q) ≤ H(t·p + (1−t)·q)`.  The engine is the concavity of `negMulLog`
(`Real.concaveOn_negMulLog`), lifted termwise through `ENNReal.ofReal` and summed. -/
lemma shannonEntropy_concave {ι : Type*} (p q : ι → ℝ≥0∞) (hp : ∀ i, p i ≤ 1) (hq : ∀ i, q i ≤ 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ENNReal.ofReal t * shannonEntropy p + ENNReal.ofReal (1 - t) * shannonEntropy q
      ≤ shannonEntropy (fun i => ENNReal.ofReal t * p i + ENNReal.ofReal (1 - t) * q i) := by
  set s := 1 - t with hs
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hts : t + s = 1 := by rw [hs]; ring
  have h1p : ∀ i, (p i).toReal ≤ 1 := fun i => by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top (hp i)
  have h1q : ∀ i, (q i).toReal ≤ 1 := fun i => by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top (hq i)
  -- the termwise concavity bound
  have hpt : ∀ i, ENNReal.ofReal t * ENNReal.ofReal (Real.negMulLog (p i).toReal)
      + ENNReal.ofReal s * ENNReal.ofReal (Real.negMulLog (q i).toReal)
      ≤ ENNReal.ofReal
          (Real.negMulLog (ENNReal.ofReal t * p i + ENNReal.ofReal s * q i).toReal) := by
    intro i
    have hpne : p i ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hp i)
    have hqne : q i ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hq i)
    have hnA : 0 ≤ Real.negMulLog (p i).toReal :=
      Real.negMulLog_nonneg ENNReal.toReal_nonneg (h1p i)
    have hnB : 0 ≤ Real.negMulLog (q i).toReal :=
      Real.negMulLog_nonneg ENNReal.toReal_nonneg (h1q i)
    have hmtoReal : (ENNReal.ofReal t * p i + ENNReal.ofReal s * q i).toReal
        = t * (p i).toReal + s * (q i).toReal := by
      rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpne)
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hqne),
        ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht0,
        ENNReal.toReal_ofReal hs0]
    have hconc := Real.concaveOn_negMulLog.2 (Set.mem_Ici.mpr (ENNReal.toReal_nonneg (a := p i)))
      (Set.mem_Ici.mpr (ENNReal.toReal_nonneg (a := q i))) ht0 hs0 hts
    rw [← ENNReal.ofReal_mul ht0, ← ENNReal.ofReal_mul hs0,
      ← ENNReal.ofReal_add (mul_nonneg ht0 hnA) (mul_nonneg hs0 hnB)]
    apply ENNReal.ofReal_le_ofReal
    rw [hmtoReal]
    calc t * Real.negMulLog (p i).toReal + s * Real.negMulLog (q i).toReal
        = t • Real.negMulLog (p i).toReal + s • Real.negMulLog (q i).toReal := by
          rw [smul_eq_mul, smul_eq_mul]
      _ ≤ Real.negMulLog (t • (p i).toReal + s • (q i).toReal) := hconc
      _ = Real.negMulLog (t * (p i).toReal + s * (q i).toReal) := by rw [smul_eq_mul, smul_eq_mul]
  calc ENNReal.ofReal t * shannonEntropy p + ENNReal.ofReal s * shannonEntropy q
      = (∑' i, ENNReal.ofReal t * ENNReal.ofReal (Real.negMulLog (p i).toReal))
        + ∑' i, ENNReal.ofReal s * ENNReal.ofReal (Real.negMulLog (q i).toReal) := by
        rw [shannonEntropy, shannonEntropy, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    _ = ∑' i, (ENNReal.ofReal t * ENNReal.ofReal (Real.negMulLog (p i).toReal)
        + ENNReal.ofReal s * ENNReal.ofReal (Real.negMulLog (q i).toReal)) :=
        (ENNReal.tsum_add).symm
    _ ≤ shannonEntropy (fun i => ENNReal.ofReal t * p i + ENNReal.ofReal s * q i) :=
        ENNReal.tsum_le_tsum hpt

/-- **Additivity of the Shannon entropy under independent (product) distributions** — the chain rule
for independent variables: `H(p ⊗ q) = H(p) + H(q)`, where `(p⊗q)(i,j) = pᵢ·qⱼ`.  The engine is the
grouping identity `negMulLog(xy) = y·negMulLog x + x·negMulLog y` summed over the product, using
`∑ᵢ pᵢ = ∑ⱼ qⱼ = 1`. -/
lemma shannonEntropy_prod {ι κ : Type*} (p : ι → ℝ≥0∞) (q : κ → ℝ≥0∞)
    (hp1 : ∀ i, p i ≤ 1) (hq1 : ∀ j, q j ≤ 1) (hp : ∑' i, p i = 1) (hq : ∑' j, q j = 1) :
    shannonEntropy (fun ij : ι × κ => p ij.1 * q ij.2) = shannonEntropy p + shannonEntropy q := by
  have hpne : ∀ i, p i ≠ ⊤ := fun i => ne_top_of_le_ne_top ENNReal.one_ne_top (hp1 i)
  have hqne : ∀ j, q j ≠ ⊤ := fun j => ne_top_of_le_ne_top ENNReal.one_ne_top (hq1 j)
  have h1p : ∀ i, (p i).toReal ≤ 1 := fun i => by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top (hp1 i)
  have h1q : ∀ j, (q j).toReal ≤ 1 := fun j => by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top (hq1 j)
  have hpsum : ∑' i, ENNReal.ofReal (p i).toReal = 1 := by
    rw [← hp]; exact tsum_congr fun i => ENNReal.ofReal_toReal (hpne i)
  have hqsum : ∑' j, ENNReal.ofReal (q j).toReal = 1 := by
    rw [← hq]; exact tsum_congr fun j => ENNReal.ofReal_toReal (hqne j)
  have hterm : ∀ ij : ι × κ, ENNReal.ofReal (Real.negMulLog (p ij.1 * q ij.2).toReal)
      = ENNReal.ofReal (q ij.2).toReal * ENNReal.ofReal (Real.negMulLog (p ij.1).toReal)
        + ENNReal.ofReal (p ij.1).toReal * ENNReal.ofReal (Real.negMulLog (q ij.2).toReal) := by
    rintro ⟨i, j⟩
    have hnA : 0 ≤ Real.negMulLog (p i).toReal :=
      Real.negMulLog_nonneg ENNReal.toReal_nonneg (h1p i)
    have hnB : 0 ≤ Real.negMulLog (q j).toReal :=
      Real.negMulLog_nonneg ENNReal.toReal_nonneg (h1q j)
    rw [ENNReal.toReal_mul, Real.negMulLog_mul,
      ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg hnA)
        (mul_nonneg ENNReal.toReal_nonneg hnB),
      ENNReal.ofReal_mul (show (0:ℝ) ≤ (q j).toReal from ENNReal.toReal_nonneg),
      ENNReal.ofReal_mul (show (0:ℝ) ≤ (p i).toReal from ENNReal.toReal_nonneg)]
  have hinner :
      ∀ i, (∑' j, (ENNReal.ofReal (q j).toReal * ENNReal.ofReal (Real.negMulLog (p i).toReal)
      + ENNReal.ofReal (p i).toReal * ENNReal.ofReal (Real.negMulLog (q j).toReal)))
      = ENNReal.ofReal (Real.negMulLog (p i).toReal)
        + ENNReal.ofReal (p i).toReal * ∑' j, ENNReal.ofReal (Real.negMulLog (q j).toReal) := by
    intro i
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, hqsum, one_mul]
  simp only [shannonEntropy]
  rw [ENNReal.tsum_prod',
    tsum_congr (fun i => tsum_congr (fun j => hterm (i, j))), tsum_congr hinner,
    ENNReal.tsum_add, ENNReal.tsum_mul_right, hpsum, one_mul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The von Neumann entropy is the Shannon entropy of the eigenvalue distribution**:
`S(ρ) = H(λ(ρ))`.  Since `ρ`'s eigenvalues `λᵢ ∈ [0,1]` form a probability distribution
(`hasSum_eigenvalue`), the operator entropy `tr(-ρ log ρ)` reads off in the eigenbasis as the
classical Shannon entropy of `λ`.  This is the entry point for the Holevo bound. -/
theorem vonNeumannEntropy_eq_shannonEntropy (ρ : QState H) :
    vonNeumannEntropy ρ = shannonEntropy (fun i => ENNReal.ofReal (ρ.eigenvalue i)) := by
  rw [ρ.vonNeumannEntropy_eq_tsum, shannonEntropy]
  refine tsum_congr fun i => ?_
  rw [ENNReal.toReal_ofReal (ρ.eigenvalue_nonneg i)]

end Spectra.InformationGeometry.Quantum
