/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ported from Isabelle/HOL formalization by Echenim & Mhalla, by Adam Bornemann
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Spectra.QuantumMechanics.BellsTheorem.CHSH_Bounds.CHSH_Basic
/-!
# Local Hidden Variable Models

This file formalizes the measure-theoretic foundation for Bell's lemma:
the local hidden variable (LHV) hypothesis as formulated by Bell.

## Main definitions

* `ResponseFunction` : a measurable, integrable, ±1-a.e.-valued function of the hidden variable
* `LHVModel` : a local hidden variable model with probability space `Λ` and four such functions
* `LHVModel.correlation`, `LHVModel.CHSH` : the correlation `E(a,b)` and the CHSH quantity
  `S = E(0,1) - E(0,0) + E(1,0) + E(1,1)`

## Main results

* `chsh_pointwise_bound` : the algebraic identity behind the bound, for values in `{-1,+1}`
* `lhv_chsh_bound` : under any LHV model, `|S| ≤ 2`
* `no_lhv_if_violation` : a correlation with `|S| > 2` cannot be reproduced by any LHV model
* `bell_theorem` : no LHV model achieves the numeric value `2√2`

## Implementation notes

`chsh_pointwise_bound` restates `Spectra.QuantumInfo.chsh_expectation_algebraic_bound`
(`CHSH_Bounds/CHSH_Basic.lean`) at the special case `a = ±1` (as opposed to that lemma's general
`|a| ≤ 1`); its proof is a direct application, not an independent re-derivation of the same
`a(b'-b) + a'(b+b')` factorization.

`bell_theorem` proves only the numeric corollary `¬∃ LHV model, M.CHSH = 2√2` — this file has no
quantum state, observable, or Tsirelson-bound computation anywhere in it (those live in the
sibling `Basic.lean`/`QuantumCHSH` files), so it does not itself establish that quantum mechanics
*achieves* `2√2`; it only rules out the LHV explanation for that specific value once something
else supplies it.

## References

Following the Isabelle formalization by Echenim & Mhalla, the LHV hypothesis
is formalized using measure theory where properties hold almost everywhere,
which is more general than assuming a density exists.
-/
open MeasureTheory ProbabilityTheory

/-! ## Setting: A Bipartite Bell Experiment

Consider an experiment where:
- A source emits pairs of particles
- Alice receives one particle, Bob receives the other
- Alice chooses measurement setting a ∈ {0, 1}
- Bob chooses measurement setting b ∈ {0, 1}
- Each outputs a result in {-1, +1}

The LHV hypothesis: There exists a "hidden variable" ω that
predetermines all outcomes, such that:
- Alice's outcome depends only on her setting and ω (not Bob's setting)
- Bob's outcome depends only on his setting and ω (not Alice's setting)
-/

namespace Spectra.BellTheorem

variable {Λ : Type*} [MeasurableSpace Λ]

/-- A response function maps a hidden variable to an output in {-1, +1}.
    We model this as a function to ℝ constrained to take values ±1 a.e. -/
structure ResponseFunction (Λ : Type*) [MeasurableSpace Λ] (μ : Measure Λ) where
  /-- The function from hidden variables to outputs -/
  toFun : Λ → ℝ
  /-- The function is measurable -/
  measurable : Measurable toFun
  /-- Outputs are ±1 almost everywhere -/
  ae_pm_one : ∀ᵐ ω ∂μ, toFun ω = 1 ∨ toFun ω = -1
  /-- The function is integrable (needed for expectation) -/
  integrable : Integrable toFun μ

instance {μ : Measure Λ} : CoeFun (ResponseFunction Λ μ) (fun _ => Λ → ℝ) where
  coe f := f.toFun

/-- A Local Hidden Variable Model for a Bell experiment -/
structure LHVModel (Λ : Type*) [MeasurableSpace Λ] where
  /-- The probability measure on hidden variables -/
  μ : ProbabilityMeasure Λ
  /-- Alice's response function for setting 0 -/
  A₀ : ResponseFunction Λ μ
  /-- Alice's response function for setting 1 -/
  A₁ : ResponseFunction Λ μ
  /-- Bob's response function for setting 0 -/
  B₀ : ResponseFunction Λ μ
  /-- Bob's response function for setting 1 -/
  B₁ : ResponseFunction Λ μ

variable (M : LHVModel Λ)

/-- The correlation E(a,b) = ∫ A(a,ω)·B(b,ω) dμ(ω) -/
noncomputable def LHVModel.correlation (M : LHVModel Λ)
    (A : ResponseFunction Λ M.μ) (B : ResponseFunction Λ M.μ) : ℝ :=
  ∫ ω, A ω * B ω ∂(M.μ : Measure Λ)

/-- E(0,0) = ∫ A₀·B₀ dμ -/
noncomputable def LHVModel.E₀₀ (M : LHVModel Λ) : ℝ := M.correlation M.A₀ M.B₀

/-- E(0,1) = ∫ A₀·B₁ dμ -/
noncomputable def LHVModel.E₀₁ (M : LHVModel Λ) : ℝ := M.correlation M.A₀ M.B₁

/-- E(1,0) = ∫ A₁·B₀ dμ -/
noncomputable def LHVModel.E₁₀ (M : LHVModel Λ) : ℝ := M.correlation M.A₁ M.B₀

/-- E(1,1) = ∫ A₁·B₁ dμ -/
noncomputable def LHVModel.E₁₁ (M : LHVModel Λ) : ℝ := M.correlation M.A₁ M.B₁

/-- The CHSH value: S = E(0,1) - E(0,0) + E(1,0) + E(1,1)

Note: Different sign conventions exist. This follows the formulation where
the classical bound is 2 and the quantum maximum is 2√2. -/
noncomputable def LHVModel.CHSH (M : LHVModel Λ) : ℝ :=
  M.E₀₁ - M.E₀₀ + M.E₁₀ + M.E₁₁

/-! ## The Algebraic Core of the CHSH Bound -/

/-- For values in {-1, +1}, this quantity is always ≤ 2 in absolute value.

The key insight: a(b' - b) + a'(b + b')
- If b = b', then b' - b = 0 and b + b' = ±2, giving |a'| · 2 = 2
- If b = -b', then b' - b = ±2 and b + b' = 0, giving |a| · 2 = 2

This factorization is what makes Bell's lemma work — it is the same one behind
`Spectra.QuantumInfo.chsh_expectation_algebraic_bound`, applied here at the special case where
`a`, `a'`, `b`, `b'` are each exactly `±1` rather than merely bounded by `1` in absolute value. -/
lemma chsh_pointwise_bound (a₀ a₁ b₀ b₁ : ℝ)
    (ha₀ : a₀ = 1 ∨ a₀ = -1) (ha₁ : a₁ = 1 ∨ a₁ = -1)
    (hb₀ : b₀ = 1 ∨ b₀ = -1) (hb₁ : b₁ = 1 ∨ b₁ = -1) :
    |a₀ * b₁ - a₀ * b₀ + a₁ * b₀ + a₁ * b₁| ≤ 2 :=
  Spectra.QuantumInfo.chsh_expectation_algebraic_bound a₀ a₁ b₀ b₁
    (by rcases ha₀ with rfl | rfl <;> norm_num)
    (by rcases ha₁ with rfl | rfl <;> norm_num)
    (by rcases hb₀ with rfl | rfl <;> norm_num)
    (by rcases hb₁ with rfl | rfl <;> norm_num)

/-- The CHSH integrand is bounded by 2 almost everywhere -/
lemma chsh_integrand_bound (M : LHVModel Λ) :
    ∀ᵐ ω ∂(M.μ : Measure Λ), |M.A₀ ω * M.B₁ ω - M.A₀ ω * M.B₀ ω +
               M.A₁ ω * M.B₀ ω + M.A₁ ω * M.B₁ ω| ≤ 2 := by
  have hA₀ := M.A₀.ae_pm_one
  have hA₁ := M.A₁.ae_pm_one
  have hB₀ := M.B₀.ae_pm_one
  have hB₁ := M.B₁.ae_pm_one
  filter_upwards [hA₀, hA₁, hB₀, hB₁] with ω ha₀ ha₁ hb₀ hb₁
  exact chsh_pointwise_bound (M.A₀ ω) (M.A₁ ω) (M.B₀ ω) (M.B₁ ω) ha₀ ha₁ hb₀ hb₁

/-- A product of two ±1-a.e. response functions is integrable — the shared step behind
`chsh_as_integral` and `lhv_chsh_bound`. -/
private lemma responseProd_integrable {M : LHVModel Λ} (f g : ResponseFunction Λ M.μ) :
    Integrable (fun ω => f ω * g ω) (M.μ : Measure Λ) := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
  · exact (f.measurable.mul g.measurable).aestronglyMeasurable
  · filter_upwards [f.ae_pm_one, g.ae_pm_one] with ω hf hg
    simp only [Real.norm_eq_abs, abs_mul]
    have hf' : |f ω| = 1 := by rcases hf with h | h <;> simp [h]
    have hg' : |g ω| = 1 := by rcases hg with h | h <;> simp [h]
    rw [hf', hg']
    norm_num

/-- The CHSH value can be expressed as a single integral -/
lemma chsh_as_integral (M : LHVModel Λ) :
    M.CHSH = ∫ ω, (M.A₀ ω * M.B₁ ω - M.A₀ ω * M.B₀ ω +
                   M.A₁ ω * M.B₀ ω + M.A₁ ω * M.B₁ ω) ∂(M.μ : Measure Λ) := by
  unfold LHVModel.CHSH LHVModel.E₀₁ LHVModel.E₀₀ LHVModel.E₁₀ LHVModel.E₁₁
  unfold LHVModel.correlation
  have int_A₀B₀ : Integrable (fun ω => M.A₀ ω * M.B₀ ω) (M.μ : Measure Λ) :=
    responseProd_integrable M.A₀ M.B₀
  have int_A₀B₁ : Integrable (fun ω => M.A₀ ω * M.B₁ ω) (M.μ : Measure Λ) :=
    responseProd_integrable M.A₀ M.B₁
  have int_A₁B₀ : Integrable (fun ω => M.A₁ ω * M.B₀ ω) (M.μ : Measure Λ) :=
    responseProd_integrable M.A₁ M.B₀
  have int_A₁B₁ : Integrable (fun ω => M.A₁ ω * M.B₁ ω) (M.μ : Measure Λ) :=
    responseProd_integrable M.A₁ M.B₁
  rw [← integral_sub int_A₀B₁ int_A₀B₀]
  rw [add_assoc]
  rw [← integral_add int_A₁B₀ int_A₁B₁]
  rw [← integral_add]
  · apply integral_congr_ae
    filter_upwards with ω
    ring
  · exact int_A₀B₁.sub int_A₀B₀
  · exact int_A₁B₀.add int_A₁B₁

/-! ## The Main Theorem -/

/-- **Bell's Theorem (CHSH form)**: Under any local hidden variable model, |S| ≤ 2. -/
lemma lhv_chsh_bound (M : LHVModel Λ) : |M.CHSH| ≤ 2 := by
  rw [chsh_as_integral]
  have chsh_integrable : Integrable (fun ω => M.A₀ ω * M.B₁ ω - M.A₀ ω * M.B₀ ω +
      M.A₁ ω * M.B₀ ω + M.A₁ ω * M.B₁ ω) (M.μ : Measure Λ) := by
    apply Integrable.add
    · apply Integrable.add
      · apply Integrable.sub
        · exact responseProd_integrable M.A₀ M.B₁
        · exact responseProd_integrable M.A₀ M.B₀
      · exact responseProd_integrable M.A₁ M.B₀
    · exact responseProd_integrable M.A₁ M.B₁
  calc |∫ ω, (M.A₀ ω * M.B₁ ω - M.A₀ ω * M.B₀ ω +
              M.A₁ ω * M.B₀ ω + M.A₁ ω * M.B₁ ω) ∂(M.μ : Measure Λ)|
      ≤ ∫ ω, |M.A₀ ω * M.B₁ ω - M.A₀ ω * M.B₀ ω +
              M.A₁ ω * M.B₀ ω + M.A₁ ω * M.B₁ ω| ∂(M.μ : Measure Λ) :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _ : Λ, (2 : ℝ) ∂(M.μ : Measure Λ) := by
        apply integral_mono_ae
        · exact Integrable.abs chsh_integrable
        · exact integrable_const 2
        · exact chsh_integrand_bound M
      _ = 2 := by
        rw [integral_const]
        simp only [MeasureTheory.probReal_univ, smul_eq_mul, one_mul]

/-! ## Corollary: Violation Implies No LHV -/

/-- If a correlation violates |S| ≤ 2, no LHV model can reproduce it.

This is the logical contrapositive of `lhv_chsh_bound`:
- ∀ LHV models M, |M.CHSH| ≤ 2
- Therefore: |S| > 2 ⟹ ¬∃ LHV model with CHSH = S
-/
lemma no_lhv_if_violation (S : ℝ) (hS : |S| > 2) :
    ¬∃ (M : LHVModel Λ), M.CHSH = S := by
  intro ⟨M, hM⟩
  have := lhv_chsh_bound M
  rw [hM] at this
  linarith

/-- Quantum mechanics predicts S = 2√2 for the Bell state with optimal settings.
    Since 2√2 > 2, this proves quantum mechanics is incompatible with LHV. -/
lemma quantum_violation_exists : (2 : ℝ) * Real.sqrt 2 > 2 := by
  have h : Real.sqrt 2 > 1 := Real.one_lt_sqrt_two
  linarith

/-- **Bell's Theorem**: no local hidden variable model reproduces the value `2√2` — the numeric
corollary of `no_lhv_if_violation` at the specific value `quantum_violation_exists` shows exceeds
the classical bound. This file does not itself derive that quantum mechanics *achieves* `2√2`
(see the module docstring); that additional step lives in `Basic.lean`/`QuantumCHSH`. -/
theorem bell_theorem :
    ¬∃ (Λ : Type*) (_ : MeasurableSpace Λ) (M : LHVModel Λ),
      M.CHSH = 2 * Real.sqrt 2 := by
  rintro ⟨Λ, _, M, hM⟩
  have h2 : |(2 : ℝ) * Real.sqrt 2| > 2 := by
    rw [abs_of_pos (by positivity)]
    exact quantum_violation_exists
  exact no_lhv_if_violation (2 * Real.sqrt 2) h2 ⟨M, hM⟩

end Spectra.BellTheorem
