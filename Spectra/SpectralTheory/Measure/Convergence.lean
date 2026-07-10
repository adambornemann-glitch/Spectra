/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/

/-
Spectra: Convergence.lean
Strong convergence of the bounded functional calculus, and spectral projections.

-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Spectra.SpectralTheory.Calculus.Bounded
/-!
# Strong convergence and spectral projections

Two payloads, both consequences of the `L²` identity
`norm_sq_spectralCalculus_apply : ‖Φ(g)ξ‖² = ∫ ‖g‖² dμ_ξ`.

* **Strong convergence** (`tendsto_spectralCalculus_apply`): if symbols `Gₙ → g` pointwise
  with a uniform bound, then `Φ(Gₙ)ξ → Φ(g)ξ` in `H`, since
  `‖Φ(Gₙ)ξ − Φ(g)ξ‖² = ∫ ‖Gₙ − g‖² dμ_ξ → 0` by dominated convergence (the constant
  dominates because `μ_ξ` is finite).  Stated for a general countably-generated filter:
  the generator stage applies it along `𝓝[≠] (0 : ℝ)` with symbols
  `(e^{iλt} − 1)/(it) · 1_B(λ)`, not along a sequence.

* **Spectral projections** (`spectralProjection`): `E(B) := Φ(1_B)` is an idempotent,
  self-adjoint operator with `⟪ξ, E(B)ξ⟫ = μ_ξ(B)` — the projection-valued measure whose
  diagonal is the scalar spectral measure.  These replace the old axiomatized
  `IsSpectralMeasure` interface.


* `spectralCalculus_congr`, `spectralCalculus_sub` — symbol-algebra glue.
* `tendsto_spectralCalculus_apply` — strong convergence under dominated symbols.
* `spectralProjection` — with `_idem`, `_adjoint`, and `inner_spectralProjection_self`.
-/
open Complex MeasureTheory Filter Topology Set
open scoped InnerProductSpace
open Spectra.Borel
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.QuantumMechanics
variable (U_grp : OneParameterUnitaryGroup (H := H))
namespace SpectralTheory

/-! ## Symbol algebra -/

/-- Sums of bounded functions are bounded. -/
lemma bounded_add {g₁ g₂ : ℝ → ℂ} (h₁ : ∃ C, ∀ ω, ‖g₁ ω‖ ≤ C) (h₂ : ∃ C, ∀ ω, ‖g₂ ω‖ ≤ C) :
    ∃ C, ∀ ω, ‖g₁ ω + g₂ ω‖ ≤ C := by
  obtain ⟨C₁, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  exact ⟨C₁ + C₂, fun ω => (norm_add_le _ _).trans (add_le_add (hC₁ ω) (hC₂ ω))⟩

/-- Differences of bounded functions are bounded. -/
lemma bounded_sub {g₁ g₂ : ℝ → ℂ} (h₁ : ∃ C, ∀ ω, ‖g₁ ω‖ ≤ C) (h₂ : ∃ C, ∀ ω, ‖g₂ ω‖ ≤ C) :
    ∃ C, ∀ ω, ‖g₁ ω - g₂ ω‖ ≤ C := by
  obtain ⟨C₁, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  exact ⟨C₁ + C₂, fun ω => (norm_sub_le _ _).trans (add_le_add (hC₁ ω) (hC₂ ω))⟩

/-- `Φ` respects equality of symbols, with arbitrary proofs on each side — proof irrelevance
makes this `rfl` after substitution.  The tool for rewriting a symbol underneath the
dependent hypothesis arguments (where a bare `rw` would produce an ill-typed motive). -/
theorem spectralCalculus_congr {g₁ g₂ : ℝ → ℂ} (h : g₁ = g₂)
    (h₁m : Measurable g₁) (h₁b : ∃ C, ∀ ω, ‖g₁ ω‖ ≤ C)
    (h₂m : Measurable g₂) (h₂b : ∃ C, ∀ ω, ‖g₂ ω‖ ≤ C) :
    spectralCalculus U_grp g₁ h₁m h₁b = spectralCalculus U_grp g₂ h₂m h₂b := by
  subst h
  rfl

/-- Subtractivity in the symbol: `Φ(g₁ − g₂) = Φ(g₁) − Φ(g₂)`.  From
`spectralCalculus_add` at `(g₁ − g₂, g₂)` and the congruence `(g₁ − g₂) + g₂ = g₁`. -/
theorem spectralCalculus_sub (g₁ g₂ : ℝ → ℂ)
    (h₁m : Measurable g₁) (h₁b : ∃ C, ∀ ω, ‖g₁ ω‖ ≤ C)
    (h₂m : Measurable g₂) (h₂b : ∃ C, ∀ ω, ‖g₂ ω‖ ≤ C)
    (hm : Measurable fun l => g₁ l - g₂ l) (hb : ∃ C, ∀ ω, ‖g₁ ω - g₂ ω‖ ≤ C) :
    spectralCalculus U_grp (fun l => g₁ l - g₂ l) hm hb
      = spectralCalculus U_grp g₁ h₁m h₁b - spectralCalculus U_grp g₂ h₂m h₂b := by
  have hfun : (fun l => (g₁ l - g₂ l) + g₂ l) = g₁ := funext fun l => by ring
  have key := spectralCalculus_add U_grp (fun l => g₁ l - g₂ l) g₂ hm hb h₂m h₂b
    (hm.add h₂m) (bounded_add hb h₂b)
  rw [spectralCalculus_congr U_grp hfun (hm.add h₂m) (bounded_add hb h₂b) h₁m h₁b] at key
  exact eq_sub_of_add_eq key.symm

/-! ## Strong convergence -/

/-- **Strong convergence of the calculus.**  If the symbols `G n → g` pointwise along a
countably generated filter `l`, with a bound uniform in `n` and `ω`, then
`Φ(G n)ξ → Φ(g)ξ` in `H`.

Proof: `‖Φ(G n)ξ − Φ(g)ξ‖ = (∫ ‖G n − g‖² dμ_ξ)^{1/2}` by `spectralCalculus_sub` and the
`L²` identity; the integral tends to `0` by `tendsto_integral_filter_of_dominated_convergence`
with the constant dominating function `(C + C_g)²`, integrable since `μ_ξ` is finite. -/
theorem tendsto_spectralCalculus_apply {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {G : ι → ℝ → ℂ} {g : ℝ → ℂ}
    (hG_meas : ∀ n, Measurable (G n)) (hG_bdd : ∀ n, ∃ C, ∀ ω, ‖G n ω‖ ≤ C)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C)
    {C : ℝ} (hunif : ∀ n ω, ‖G n ω‖ ≤ C)
    (hlim : ∀ ω, Tendsto (fun n => G n ω) l (𝓝 (g ω))) (ξ : H) :
    Tendsto (fun n => spectralCalculus U_grp (G n) (hG_meas n) (hG_bdd n) ξ) l
      (𝓝 (spectralCalculus U_grp g hg_meas hg_bdd ξ)) := by
  haveI : IsFiniteMeasure (borelMeasure U_grp ξ) := borelMeasure_isFiniteMeasure U_grp ξ
  obtain ⟨Cg, hCg⟩ := id hg_bdd
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- Step 1: `‖Φ(G n)ξ − Φ(g)ξ‖ = √(∫ ‖G n − g‖² dμ_ξ)`.
  have hnorm : ∀ n, ‖spectralCalculus U_grp (G n) (hG_meas n) (hG_bdd n) ξ
      - spectralCalculus U_grp g hg_meas hg_bdd ξ‖
      = Real.sqrt (∫ ω, ‖G n ω - g ω‖ ^ 2 ∂(borelMeasure U_grp ξ)) := by
    intro n
    have h1 : spectralCalculus U_grp (G n) (hG_meas n) (hG_bdd n) ξ
        - spectralCalculus U_grp g hg_meas hg_bdd ξ
        = spectralCalculus U_grp (fun ω => G n ω - g ω)
            ((hG_meas n).sub hg_meas) (bounded_sub (hG_bdd n) hg_bdd) ξ := by
      rw [← ContinuousLinearMap.sub_apply,
        ← spectralCalculus_sub U_grp (G n) g (hG_meas n) (hG_bdd n) hg_meas hg_bdd
          ((hG_meas n).sub hg_meas) (bounded_sub (hG_bdd n) hg_bdd)]
    rw [h1, ← Real.sqrt_sq (norm_nonneg (spectralCalculus U_grp (fun ω => G n ω - g ω)
        ((hG_meas n).sub hg_meas) (bounded_sub (hG_bdd n) hg_bdd) ξ)),
      norm_sq_spectralCalculus_apply]
  -- Step 2: dominated convergence for `∫ ‖G n − g‖² dμ_ξ → 0`.
  have hDCT : Tendsto (fun n => ∫ ω, ‖G n ω - g ω‖ ^ 2 ∂(borelMeasure U_grp ξ)) l (𝓝 0) := by
    have hmeas : ∀ n, AEStronglyMeasurable (fun ω => ‖G n ω - g ω‖ ^ 2)
        (borelMeasure U_grp ξ) := fun n =>
      (((hG_meas n).sub hg_meas).norm.pow_const 2).aestronglyMeasurable
    have hbd : ∀ n, ∀ᵐ ω ∂(borelMeasure U_grp ξ), ‖‖G n ω - g ω‖ ^ 2‖ ≤ (C + Cg) ^ 2 :=
      fun n => Eventually.of_forall fun ω => by
        have h1 : ‖G n ω - g ω‖ ≤ C + Cg :=
          (norm_sub_le _ _).trans (add_le_add (hunif n ω) (hCg ω))
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [norm_nonneg (G n ω - g ω)]
    have hptlim : ∀ᵐ ω ∂(borelMeasure U_grp ξ),
        Tendsto (fun n => ‖G n ω - g ω‖ ^ 2) l (𝓝 0) :=
      Eventually.of_forall fun ω => by
        have hsub : Tendsto (fun n => G n ω - g ω) l (𝓝 0) := by
          have h := (hlim ω).sub_const (g ω)
          rwa [sub_self] at h
        have h := hsub.norm.pow 2
        simpa using h
    have h := tendsto_integral_filter_of_dominated_convergence
      (μ := borelMeasure U_grp ξ) (F := fun n ω => ‖G n ω - g ω‖ ^ 2)
      (f := fun _ => (0 : ℝ)) (fun _ => (C + Cg) ^ 2)
      (Eventually.of_forall hmeas) (Eventually.of_forall hbd) (integrable_const _) hptlim
    simpa using h
  -- Step 3: compose with `√` and rewrite along Step 1.
  have hsqrt : Tendsto (fun n => Real.sqrt (∫ ω, ‖G n ω - g ω‖ ^ 2 ∂(borelMeasure U_grp ξ)))
      l (𝓝 0) := by
    have h := hDCT.sqrt
    rwa [Real.sqrt_zero] at h
  exact hsqrt.congr fun n => (hnorm n).symm

/-! ## Spectral projections -/

/-- Canonical boundedness proof for indicator symbols. -/
lemma indicator_one_bdd (B : Set ℝ) :
    ∃ C, ∀ ω, ‖Set.indicator B (fun _ => (1 : ℂ)) ω‖ ≤ C := by
  classical
  refine ⟨1, fun ω => ?_⟩
  rw [Set.indicator_apply]
  split_ifs <;> simp

/-- **The spectral projection** `E(B) := Φ(1_B)`. -/
noncomputable def spectralProjection (B : Set ℝ) (hB : MeasurableSet B) : H →L[ℂ] H :=
  spectralCalculus U_grp (Set.indicator B fun _ => (1 : ℂ))
    (measurable_const.indicator hB) (indicator_one_bdd B)

/-- `E(B)` is idempotent: `1_B · 1_B = 1_B` under the calculus. -/
theorem spectralProjection_idem (B : Set ℝ) (hB : MeasurableSet B) :
    spectralProjection U_grp B hB * spectralProjection U_grp B hB
      = spectralProjection U_grp B hB := by
  have hfun : (fun l => Set.indicator B (fun _ => (1 : ℂ)) l
      * Set.indicator B (fun _ => (1 : ℂ)) l) = Set.indicator B (fun _ => (1 : ℂ)) := by
    classical
    funext l
    rw [Set.indicator_apply]
    split_ifs <;> simp
  simp only [spectralProjection]
  rw [spectralCalculus_mul U_grp _ _ (measurable_const.indicator hB) (indicator_one_bdd B)
      (measurable_const.indicator hB) (indicator_one_bdd B)
      ((measurable_const.indicator hB).mul (measurable_const.indicator hB))
      (bounded_mul (indicator_one_bdd B) (indicator_one_bdd B)),
    spectralCalculus_congr U_grp hfun]

/-- `E(B)` is self-adjoint: the indicator symbol is real. -/
theorem spectralProjection_adjoint (B : Set ℝ) (hB : MeasurableSet B) :
    ContinuousLinearMap.adjoint (spectralProjection U_grp B hB)
      = spectralProjection U_grp B hB := by
  have hcm : Measurable fun l : ℝ => (starRingEnd ℂ) (Set.indicator B (fun _ => (1 : ℂ)) l) :=
    Complex.continuous_conj.measurable.comp (measurable_const.indicator hB)
  have hcb : ∃ C, ∀ ω, ‖(starRingEnd ℂ) (Set.indicator B (fun _ => (1 : ℂ)) ω)‖ ≤ C := by
    obtain ⟨C, hC⟩ := indicator_one_bdd B
    exact ⟨C, fun ω => by rw [RCLike.norm_conj]; exact hC ω⟩
  have hfun : (fun l => (starRingEnd ℂ) (Set.indicator B (fun _ => (1 : ℂ)) l))
      = Set.indicator B (fun _ => (1 : ℂ)) := by
    classical
    funext l
    rw [Set.indicator_apply]
    split_ifs <;> simp
  simp only [spectralProjection]
  rw [spectralCalculus_adjoint U_grp _ (measurable_const.indicator hB) (indicator_one_bdd B)
      hcm hcb, spectralCalculus_congr U_grp hfun]

/-- **The diagonal of the projection-valued measure is the scalar spectral measure**:
`⟪ξ, E(B) ξ⟫ = μ_ξ(B)`.  In particular `E` inherits countable additivity (weakly, hence
strongly via idempotence) from `μ_ξ` — the reason the PVM never needs its own σ-additivity
development. -/
theorem inner_spectralProjection_self (B : Set ℝ) (hB : MeasurableSet B) (ξ : H) :
    ⟪ξ, spectralProjection U_grp B hB ξ⟫_ℂ
      = (((borelMeasure U_grp ξ) B).toReal : ℂ) := by
  simp only [spectralProjection]
  rw [inner_spectralCalculus, spectralForm_self U_grp ξ (measurable_const.indicator hB)
      (indicator_one_bdd B), integral_indicator_const (1 : ℂ) hB, Complex.real_smul, mul_one]
  rfl

end SpectralTheory
end Spectra.QuantumMechanics
