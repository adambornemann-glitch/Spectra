/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
/-!
# The Clauser–Horne (1974) Inequality

This file formalizes the Clauser–Horne (CH) inequality, the historically and logically prior
generalization of CHSH (`Spectra.QuantumMechanics.BellsTheorem.LHV`): instead of dichotomic
`±1`-valued response functions describing a *complete* two-outcome measurement, CH works with
sub-normalized *detection probabilities* `p ∈ [0, 1]` — the probability a given detector fires at
all, allowing "no click" as a genuine third possibility rather than forcing every trial into `±1`.
This is a strictly more general, and more experimentally realistic, hypothesis than CHSH's implicit
perfect-detection assumption.

## Main definitions/results

* `DetectionResponse` : a measurable, integrable, `[0,1]`-a.e.-valued function of the hidden
  variable — the detection-probability analogue of `ResponseFunction`.
* `CHModel` : a local hidden variable model for a CH experiment: a probability space `Λ` and four
  detection responses `A₀, A₁, B₀, B₁`.
* `CHModel.CH` : the CH quantity
  `P(0,0) - P(0,1) + P(1,0) + P(1,1) - P_A(1) - P_B(0)`.
* `ch_pointwise_bound` : the algebraic identity behind the bound, for values in `[0, 1]`.
* `ch_bound` : under any `CHModel`, `-1 ≤ CH ≤ 0`.

## Implementation notes

Unlike `chsh_pointwise_bound` (`LHV.lean`), which is a short case-bash on `±1` values,
`ch_pointwise_bound`'s proof is a genuinely different (and less immediately obvious) fact about
`[0,1]`-bounded reals: it is closed by `nlinarith` given the twelve pairwise products of the four
variables' `≥0`/`≤1` slack terms, rather than by a direct sign-case factorization. This is the
"interesting reduction lemma" flagged as CH's main added cost over CHSH.

CHSH itself is recoverable from CH via a no-enhancement/normalization hypothesis relating detection
probabilities to `±1` correlation coefficients; that reduction is not formalized here (this file
develops CH on its own terms, as the more fundamental of the two).

## References

J.F. Clauser, M.A. Horne, *"Experimental consequences of objective local theories,"* Phys. Rev. D
10, 526 (1974).
-/
open MeasureTheory ProbabilityTheory

namespace Spectra.BellTheorem

variable {Λ : Type*} [MeasurableSpace Λ]

/-! ## Detection-Probability Response Functions -/

/-- A detection response maps a hidden variable to a detection *probability* in `[0, 1]` — the
chance a given detector fires at all, as opposed to `ResponseFunction`'s forced `±1` outcome. -/
structure DetectionResponse (Λ : Type*) [MeasurableSpace Λ] (μ : Measure Λ) where
  /-- The function from hidden variables to detection probabilities. -/
  toFun : Λ → ℝ
  /-- The function is measurable. -/
  measurable : Measurable toFun
  /-- Values lie in `[0, 1]` almost everywhere. -/
  ae_mem_Icc : ∀ᵐ ω ∂μ, 0 ≤ toFun ω ∧ toFun ω ≤ 1
  /-- The function is integrable (needed for expectation). -/
  integrable : Integrable toFun μ

instance {μ : Measure Λ} : CoeFun (DetectionResponse Λ μ) (fun _ => Λ → ℝ) where
  coe f := f.toFun

/-- A product of two `[0,1]`-a.e.-valued detection responses is integrable. -/
private lemma detectionProd_integrable {μ : ProbabilityMeasure Λ} (f g : DetectionResponse Λ μ) :
    Integrable (fun ω => f ω * g ω) (μ : Measure Λ) := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
  · exact (f.measurable.mul g.measurable).aestronglyMeasurable
  · filter_upwards [f.ae_mem_Icc, g.ae_mem_Icc] with ω ⟨hf0, hf1⟩ ⟨hg0, hg1⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hf0 hg0)]
    nlinarith

/-! ## The Clauser–Horne Model -/

/-- A Clauser–Horne local hidden variable model: a probability space of hidden variables together
with four detection responses, two settings per party. -/
structure CHModel (Λ : Type*) [MeasurableSpace Λ] where
  /-- The probability measure on hidden variables. -/
  μ : ProbabilityMeasure Λ
  /-- Alice's detection response for setting `0`. -/
  A₀ : DetectionResponse Λ μ
  /-- Alice's detection response for setting `1`. -/
  A₁ : DetectionResponse Λ μ
  /-- Bob's detection response for setting `0`. -/
  B₀ : DetectionResponse Λ μ
  /-- Bob's detection response for setting `1`. -/
  B₁ : DetectionResponse Λ μ

/-- The joint detection probability `P(a,b) = ∫ A(a,ω)·B(b,ω) dμ(ω)`. -/
noncomputable def CHModel.jointProb (M : CHModel Λ)
    (A B : DetectionResponse Λ M.μ) : ℝ :=
  ∫ ω, A ω * B ω ∂(M.μ : Measure Λ)

/-- Alice's single-detector marginal `P_A(a) = ∫ A(a,ω) dμ(ω)`. -/
noncomputable def CHModel.marginalA (M : CHModel Λ) (A : DetectionResponse Λ M.μ) : ℝ :=
  ∫ ω, A ω ∂(M.μ : Measure Λ)

/-- Bob's single-detector marginal `P_B(b) = ∫ B(b,ω) dμ(ω)`. -/
noncomputable def CHModel.marginalB (M : CHModel Λ) (B : DetectionResponse Λ M.μ) : ℝ :=
  ∫ ω, B ω ∂(M.μ : Measure Λ)

/-- The Clauser–Horne quantity: `P(0,0) - P(0,1) + P(1,0) + P(1,1) - P_A(1) - P_B(0)`. -/
noncomputable def CHModel.CH (M : CHModel Λ) : ℝ :=
  M.jointProb M.A₀ M.B₀ - M.jointProb M.A₀ M.B₁ + M.jointProb M.A₁ M.B₀ +
    M.jointProb M.A₁ M.B₁ - M.marginalA M.A₁ - M.marginalB M.B₀

/-! ## The Algebraic Core -/

/-- **The Clauser–Horne pointwise bound.** For `u, u', v, v' ∈ [0,1]`,
`-1 ≤ u*v - u*v' + u'*v + u'*v' - u' - v ≤ 0`.
Unlike CHSH's `±1` case, this is not a short sign-case
factorization; it is closed here by `nlinarith` given the twelve pairwise products of the four
variables' `≥ 0` / `≤ 1` slack terms. -/
lemma ch_pointwise_bound (u u' v v' : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hu'0 : 0 ≤ u')
    (hu'1 : u' ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hv'0 : 0 ≤ v') (hv'1 : v' ≤ 1) :
    -1 ≤ u * v - u * v' + u' * v + u' * v' - u' - v ∧
      u * v - u * v' + u' * v + u' * v' - u' - v ≤ 0 := by
  constructor <;>
    nlinarith [mul_nonneg hu0 hv0, mul_nonneg hu0 hv'0, mul_nonneg hu'0 hv0,
      mul_nonneg hu'0 hv'0, mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr hv1),
      mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr hv'1),
      mul_nonneg (sub_nonneg.mpr hu'1) (sub_nonneg.mpr hv1),
      mul_nonneg (sub_nonneg.mpr hu'1) (sub_nonneg.mpr hv'1),
      mul_nonneg hu0 (sub_nonneg.mpr hv1), mul_nonneg hu0 (sub_nonneg.mpr hv'1),
      mul_nonneg hu'0 (sub_nonneg.mpr hv1), mul_nonneg hu'0 (sub_nonneg.mpr hv'1),
      mul_nonneg (sub_nonneg.mpr hu1) hv0, mul_nonneg (sub_nonneg.mpr hu1) hv'0,
      mul_nonneg (sub_nonneg.mpr hu'1) hv0, mul_nonneg (sub_nonneg.mpr hu'1) hv'0]

/-- The CH integrand is bounded pointwise, almost everywhere. -/
lemma ch_integrand_bound (M : CHModel Λ) :
    ∀ᵐ ω ∂(M.μ : Measure Λ),
      -1 ≤ M.A₀ ω * M.B₀ ω - M.A₀ ω * M.B₁ ω + M.A₁ ω * M.B₀ ω +
            M.A₁ ω * M.B₁ ω - M.A₁ ω - M.B₀ ω ∧
      M.A₀ ω * M.B₀ ω - M.A₀ ω * M.B₁ ω + M.A₁ ω * M.B₀ ω +
            M.A₁ ω * M.B₁ ω - M.A₁ ω - M.B₀ ω ≤ 0 := by
  filter_upwards [M.A₀.ae_mem_Icc, M.A₁.ae_mem_Icc, M.B₀.ae_mem_Icc, M.B₁.ae_mem_Icc]
    with ω ⟨ha00, ha01⟩ ⟨ha10, ha11⟩ ⟨hb00, hb01⟩ ⟨hb10, hb11⟩
  exact ch_pointwise_bound (M.A₀ ω) (M.A₁ ω) (M.B₀ ω) (M.B₁ ω) ha00 ha01 ha10 ha11 hb00 hb01
    hb10 hb11

/-- The CH value can be expressed as a single integral. -/
lemma ch_as_integral (M : CHModel Λ) :
    M.CH = ∫ ω, (M.A₀ ω * M.B₀ ω - M.A₀ ω * M.B₁ ω + M.A₁ ω * M.B₀ ω +
                 M.A₁ ω * M.B₁ ω - M.A₁ ω - M.B₀ ω) ∂(M.μ : Measure Λ) := by
  unfold CHModel.CH CHModel.jointProb CHModel.marginalA CHModel.marginalB
  have h00 : Integrable (fun ω => M.A₀ ω * M.B₀ ω) (M.μ : Measure Λ) :=
    detectionProd_integrable M.A₀ M.B₀
  have h01 : Integrable (fun ω => M.A₀ ω * M.B₁ ω) (M.μ : Measure Λ) :=
    detectionProd_integrable M.A₀ M.B₁
  have h10 : Integrable (fun ω => M.A₁ ω * M.B₀ ω) (M.μ : Measure Λ) :=
    detectionProd_integrable M.A₁ M.B₀
  have h11 : Integrable (fun ω => M.A₁ ω * M.B₁ ω) (M.μ : Measure Λ) :=
    detectionProd_integrable M.A₁ M.B₁
  -- Each combined integrability fact below is explicitly ascribed the *pointwise* lambda form
  -- (rather than left as a `Pi.sub`/`Pi.add` function difference/sum), so that the subsequent
  -- `rw` steps match the goal's literal `∫ ω, (pointwise expr) ∂μ` shape syntactically.
  have h0001 : Integrable (fun ω => M.A₀ ω * M.B₀ ω - M.A₀ ω * M.B₁ ω) (M.μ : Measure Λ) :=
    h00.sub h01
  have h000110 : Integrable (fun ω => M.A₀ ω * M.B₀ ω - M.A₀ ω * M.B₁ ω + M.A₁ ω * M.B₀ ω)
      (M.μ : Measure Λ) := h0001.add h10
  have h00011011 : Integrable
      (fun ω => M.A₀ ω * M.B₀ ω - M.A₀ ω * M.B₁ ω + M.A₁ ω * M.B₀ ω + M.A₁ ω * M.B₁ ω)
      (M.μ : Measure Λ) := h000110.add h11
  have h000110111 : Integrable
      (fun ω => M.A₀ ω * M.B₀ ω - M.A₀ ω * M.B₁ ω + M.A₁ ω * M.B₀ ω + M.A₁ ω * M.B₁ ω - M.A₁ ω)
      (M.μ : Measure Λ) := h00011011.sub M.A₁.integrable
  rw [← integral_sub h00 h01, ← integral_add h0001 h10, ← integral_add h000110 h11,
    ← integral_sub h00011011 M.A₁.integrable, ← integral_sub h000110111 M.B₀.integrable]

/-! ## The Main Theorem -/

/-- **The Clauser–Horne inequality.** Under any `CHModel`, `-1 ≤ CH ≤ 0`. -/
theorem ch_bound (M : CHModel Λ) : -1 ≤ M.CH ∧ M.CH ≤ 0 := by
  rw [ch_as_integral]
  have hint : Integrable (fun ω => M.A₀ ω * M.B₀ ω - M.A₀ ω * M.B₁ ω + M.A₁ ω * M.B₀ ω +
      M.A₁ ω * M.B₁ ω - M.A₁ ω - M.B₀ ω) (M.μ : Measure Λ) := by
    have h00 := detectionProd_integrable M.A₀ M.B₀
    have h01 := detectionProd_integrable M.A₀ M.B₁
    have h10 := detectionProd_integrable M.A₁ M.B₀
    have h11 := detectionProd_integrable M.A₁ M.B₁
    exact ((((h00.sub h01).add h10).add h11).sub M.A₁.integrable).sub M.B₀.integrable
  constructor
  · calc (-1 : ℝ) = ∫ _ : Λ, (-1 : ℝ) ∂(M.μ : Measure Λ) := by
          rw [integral_const]; simp only [MeasureTheory.probReal_univ, smul_eq_mul, one_mul]
      _ ≤ _ := integral_mono_ae (integrable_const (-1)) hint
          (ch_integrand_bound M |>.mono fun ω h => h.1)
  · calc _ ≤ ∫ _ : Λ, (0 : ℝ) ∂(M.μ : Measure Λ) :=
          integral_mono_ae hint (integrable_const 0) (ch_integrand_bound M |>.mono fun ω h => h.2)
      _ = 0 := integral_zero Λ ℝ

end Spectra.BellTheorem
