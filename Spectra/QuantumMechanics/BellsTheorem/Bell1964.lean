/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.BellsTheorem.LHV
/-!
# Bell's Original (1964) Inequality

This file formalizes Bell's original 1964 inequality, the historical precursor to CHSH
(`Spectra.QuantumMechanics.BellsTheorem.LHV`). Unlike CHSH, which needs no assumption about how
close the observed correlations are to `±1`, Bell's 1964 argument is conditioned on the *perfect
anti-correlation* the singlet state produces at matching measurement settings: if Alice and Bob
both measure along the same direction `x`, the outcomes are always opposite. This extra hypothesis
is what lets Bell eliminate Bob's response function entirely, reducing the argument to a single
family of `±1`-valued functions evaluated at three settings.

## Main definitions/results

* `bell1964_pointwise_eq` : for `a, b, c ∈ {-1, 1}`, `|a*b - a*c| = 1 - b*c` — an *equality*, not
  merely a bound (contrast `chsh_pointwise_bound`, whose CHSH combination only has a `≤ 2` bound).
* `perfect_anticorrelation_forces_determinism` : if two `±1`-a.e. response functions `F, G` have
  correlation exactly `-1`, they must agree a.e. as `G = -F` — the specifically Bell-1964 step that
  CHSH's own derivation never needs.
* `bell1964_correlation_bound` : the abstract three-point inequality
  `|∫A·B - ∫A·C| ≤ 1 - ∫B·C` for any three response functions on a shared probability space.
* `bell_1964_inequality` : **Bell's theorem (1964 form)** — given perfect anti-correlation at
  settings `b` and `c`, the physical correlations satisfy `|E(a,b) - E(a,c)| ≤ 1 + E(b,c)`.

## Implementation notes

Unlike `LHVModel` (which bundles exactly two named settings per party, `A₀`/`A₁`/`B₀`/`B₁`, for
CHSH), this file does not introduce an analogous three-setting bundled structure: the five
`ResponseFunction`s and two anti-correlation hypotheses are taken directly as arguments to
`bell_1964_inequality`, since nothing downstream in this project needs a reusable three-setting
model type the way CHSH's four-setting shape is reused across the whole `CHSH_Bounds`/`QuantumCHSH`
tree.

`bell_1964_inequality` only hypothesizes perfect anti-correlation at settings `b` and `c`, not at
`a` — Bob's setting-`a` response function plays no role in this particular three-term combination
(see that theorem's docstring), so it is omitted from the statement entirely rather than carried as
an unused hypothesis.

## References

J.S. Bell, *"On the Einstein Podolsky Rosen Paradox,"* Physics 1, 195 (1964).
-/
open MeasureTheory ProbabilityTheory

namespace Spectra.BellTheorem

variable {Λ : Type*} [MeasurableSpace Λ]

/-! ## The Algebraic Core of Bell's 1964 Inequality -/

/-- For values in `{-1, +1}`, `a*b - a*c` factors as `a*(b-c)`; since `|a| = 1` and `b, c ∈ {-1,1}`
force `|b - c| = 1 - b*c` exactly, the whole quantity's absolute value equals `1 - b*c`. -/
lemma bell1964_pointwise_eq (a b c : ℝ)
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (hc : c = 1 ∨ c = -1) :
    |a * b - a * c| = 1 - b * c := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> norm_num

/-- The Bell-1964 integrand identity holds almost everywhere for any three response functions. -/
lemma bell1964_integrand_eq {μ : Measure Λ} (A B C : ResponseFunction Λ μ) :
    ∀ᵐ ω ∂μ, |A ω * B ω - A ω * C ω| = 1 - B ω * C ω := by
  filter_upwards [A.ae_pm_one, B.ae_pm_one, C.ae_pm_one] with ω ha hb hc
  exact bell1964_pointwise_eq (A ω) (B ω) (C ω) ha hb hc

/-- A product of two `±1`-a.e. response functions is integrable (duplicated from `LHV.lean`'s
`private` lemma of the same name, which is not visible outside that file). -/
private lemma responseProd_integrable {μ : ProbabilityMeasure Λ} (f g : ResponseFunction Λ μ) :
    Integrable (fun ω => f ω * g ω) (μ : Measure Λ) := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
  · exact (f.measurable.mul g.measurable).aestronglyMeasurable
  · filter_upwards [f.ae_pm_one, g.ae_pm_one] with ω hf hg
    simp only [Real.norm_eq_abs, abs_mul]
    have hf' : |f ω| = 1 := by rcases hf with h | h <;> simp [h]
    have hg' : |g ω| = 1 := by rcases hg with h | h <;> simp [h]
    rw [hf', hg']
    norm_num

/-- **Abstract Bell-1964 correlation bound.** For any three response functions `A, B, C` sharing a
probability space, `|∫A·B - ∫A·C| ≤ 1 - ∫B·C`. This is the pure-integration content of Bell's
argument, prior to any physical two-party interpretation: it is literally the same conclusion
Wigner's (1970) set-theoretic proof reaches by a wholly different (finite counting-measure)
route. -/
lemma bell1964_correlation_bound {μ : ProbabilityMeasure Λ}
    (A B C : ResponseFunction Λ μ) :
    |(∫ ω, A ω * B ω ∂(μ : Measure Λ)) - ∫ ω, A ω * C ω ∂(μ : Measure Λ)|
      ≤ 1 - ∫ ω, B ω * C ω ∂(μ : Measure Λ) := by
  have hAB : Integrable (fun ω => A ω * B ω) (μ : Measure Λ) := responseProd_integrable A B
  have hAC : Integrable (fun ω => A ω * C ω) (μ : Measure Λ) := responseProd_integrable A C
  have hBC : Integrable (fun ω => B ω * C ω) (μ : Measure Λ) := responseProd_integrable B C
  calc |(∫ ω, A ω * B ω ∂(μ : Measure Λ)) - ∫ ω, A ω * C ω ∂(μ : Measure Λ)|
      = |∫ ω, (A ω * B ω - A ω * C ω) ∂(μ : Measure Λ)| := by rw [integral_sub hAB hAC]
    _ ≤ ∫ ω, |A ω * B ω - A ω * C ω| ∂(μ : Measure Λ) := abs_integral_le_integral_abs
    _ = ∫ ω, (1 - B ω * C ω) ∂(μ : Measure Λ) :=
        integral_congr_ae (bell1964_integrand_eq A B C)
    _ = 1 - ∫ ω, B ω * C ω ∂(μ : Measure Λ) := by
        rw [integral_sub (integrable_const 1) hBC, integral_const]
        simp only [MeasureTheory.probReal_univ, smul_eq_mul, one_mul]

/-! ## Determinism from Perfect Anti-Correlation -/

/-- **Perfect anti-correlation forces determinism.** If two `±1`-a.e.-valued response functions
have correlation exactly `-1` (the value the singlet state forces at matching settings), they must
agree, almost everywhere, as `F = -G`. This is the specifically Bell-1964 step that CHSH's own
derivation avoids by never assuming perfect (anti-)correlation at any setting. -/
lemma perfect_anticorrelation_forces_determinism {μ : ProbabilityMeasure Λ}
    (F G : ResponseFunction Λ μ)
    (hcorr : ∫ ω, F ω * G ω ∂(μ : Measure Λ) = -1) :
    G =ᵐ[(μ : Measure Λ)] (fun ω => - F ω) := by
  have hFG : Integrable (fun ω => F ω * G ω) (μ : Measure Λ) := responseProd_integrable F G
  have hsq_eq : (fun ω => (F ω + G ω) ^ 2) =ᵐ[(μ : Measure Λ)] fun ω => 2 + 2 * (F ω * G ω) := by
    filter_upwards [F.ae_pm_one, G.ae_pm_one] with ω hf hg
    have hF2 : F ω ^ 2 = 1 := by rcases hf with h | h <;> rw [h] <;> ring
    have hG2 : G ω ^ 2 = 1 := by rcases hg with h | h <;> rw [h] <;> ring
    have hexpand : (F ω + G ω) ^ 2 = F ω ^ 2 + 2 * (F ω * G ω) + G ω ^ 2 := by ring
    rw [hexpand, hF2, hG2]; ring
  have hsq_int : Integrable (fun ω => (F ω + G ω) ^ 2) (μ : Measure Λ) := by
    apply Integrable.congr (f := fun ω => 2 + 2 * (F ω * G ω))
    · exact (integrable_const 2).add (hFG.const_mul 2)
    · exact hsq_eq.symm
  have hzero : ∫ ω, (F ω + G ω) ^ 2 ∂(μ : Measure Λ) = 0 := by
    rw [integral_congr_ae hsq_eq, integral_add (integrable_const 2) (hFG.const_mul 2),
      integral_const, integral_const_mul, hcorr]
    simp only [MeasureTheory.probReal_univ, smul_eq_mul, one_mul]
    ring
  have hnonneg : (0 : Λ → ℝ) ≤ fun ω => (F ω + G ω) ^ 2 := fun ω => sq_nonneg _
  have hae_zero := (integral_eq_zero_iff_of_nonneg hnonneg hsq_int).mp hzero
  filter_upwards [hae_zero] with ω hω
  have hsum : F ω + G ω = 0 := by
    have : (F ω + G ω) ^ 2 = 0 := hω
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  linarith

/-! ## The Physical Bell Inequality -/

/-- **Bell's original (1964) theorem.** Given a shared hidden-variable probability space, three
measurement settings `a, b, c` for Alice (response functions `Aa, Ab, Ac`) and Bob's response
functions `Bb, Bc` at settings `b, c`, if the singlet's perfect anti-correlation holds at both of
those two settings (`E(x,x) = -1` for `x ∈ {b, c}`), the physical correlations
`E(a,b) := ∫Aa·Bb`, `E(a,c) := ∫Aa·Bc`, `E(b,c) := ∫Ab·Bc` satisfy
`|E(a,b) - E(a,c)| ≤ 1 + E(b,c)`.

Bob's setting-`a` response function and its anti-correlation with Alice's `Aa` play no role in this
particular three-term combination (they would matter for a *different* combination, e.g. one
involving `E(b,a)`), so — unlike the informal physical picture, which has perfect anti-correlation
at all three settings — the formal statement only assumes anti-correlation at `b` and `c`. -/
theorem bell_1964_inequality {μ : ProbabilityMeasure Λ}
    (Aa Ab Ac Bb Bc : ResponseFunction Λ μ)
    (hbb : ∫ ω, Ab ω * Bb ω ∂(μ : Measure Λ) = -1)
    (hcc : ∫ ω, Ac ω * Bc ω ∂(μ : Measure Λ) = -1) :
    |(∫ ω, Aa ω * Bb ω ∂(μ : Measure Λ)) - ∫ ω, Aa ω * Bc ω ∂(μ : Measure Λ)|
      ≤ 1 + ∫ ω, Ab ω * Bc ω ∂(μ : Measure Λ) := by
  have hBb : Bb =ᵐ[(μ : Measure Λ)] (fun ω => - Ab ω) :=
    perfect_anticorrelation_forces_determinism Ab Bb hbb
  have hBc : Bc =ᵐ[(μ : Measure Λ)] (fun ω => - Ac ω) :=
    perfect_anticorrelation_forces_determinism Ac Bc hcc
  have eAB : ∫ ω, Aa ω * Bb ω ∂(μ : Measure Λ) = - ∫ ω, Aa ω * Ab ω ∂(μ : Measure Λ) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hBb] with ω hω
    have hω' : Bb ω = - Ab ω := hω
    rw [hω']; ring
  have eAC : ∫ ω, Aa ω * Bc ω ∂(μ : Measure Λ) = - ∫ ω, Aa ω * Ac ω ∂(μ : Measure Λ) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hBc] with ω hω
    have hω' : Bc ω = - Ac ω := hω
    rw [hω']; ring
  have eBC : ∫ ω, Ab ω * Bc ω ∂(μ : Measure Λ) = - ∫ ω, Ab ω * Ac ω ∂(μ : Measure Λ) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hBc] with ω hω
    have hω' : Bc ω = - Ac ω := hω
    rw [hω']; ring
  rw [eAB, eAC, eBC]
  have key := bell1964_correlation_bound Aa Ab Ac
  have hrw : (-(∫ ω, Aa ω * Ab ω ∂(μ : Measure Λ)) - -(∫ ω, Aa ω * Ac ω ∂(μ : Measure Λ)))
      = -((∫ ω, Aa ω * Ab ω ∂(μ : Measure Λ)) - ∫ ω, Aa ω * Ac ω ∂(μ : Measure Λ)) := by ring
  rw [hrw, abs_neg]
  linarith [key]

end Spectra.BellTheorem
