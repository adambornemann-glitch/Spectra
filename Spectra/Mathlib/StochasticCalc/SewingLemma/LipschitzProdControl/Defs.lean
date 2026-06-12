/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/Defs.lean
-/
import Spectra.Mathlib.StochasticCalc.SewingLemma.IntervalLengthControl.Defs

open Real Set Filter
variable {E : Type*} [NormedAddCommGroup E]

namespace Spectra.Mathlib.StochCalc


/-! ### The Sewing Condition (Layer 2) -/

/-- **Sewing Condition, Layer 2**: the defect is controlled by a *product* of two
Lipschitz controls.

`‖δΞ(s, u, t)‖ ≤ K · ω₁(s, u)^α · ω₂(u, t)^β`

with `α + β > 1` and each `ωᵢ` Lipschitz in interval length.

The product structure is not a mere generalization — it's the *natural* form of the
defect in integration theory. When you write `Ξ(s,t) = Y(s) · (X(t) - X(s))`, the
defect `δΞ(s,u,t) = -(Y(u) - Y(s)) · (X(t) - X(u))` separates into a factor
depending on `[s, u]` (the integrand's variation) and a factor depending on `[u, t]`
(the integrator's variation). -/
structure SewingCondition₂ (Ξ : ℝ → ℝ → E)
    (ω₁ ω₂ : ℝ → ℝ → ℝ) (α β K L₁ L₂ : ℝ) (a b : ℝ) : Prop where
  vanish_diag : ∀ s, Ξ s s = 0
  one_lt_exp : 1 < α + β
  α_nonneg : 0 ≤ α
  β_nonneg : 0 ≤ β
  K_nonneg : 0 ≤ K
  hab : a ≤ b
  ω₁_nonneg : ∀ s t, a ≤ s → s ≤ t → t ≤ b → 0 ≤ ω₁ s t
  ω₁_diag : ∀ s, ω₁ s s = 0
  ω₁_superadd : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
    ω₁ s u + ω₁ u t ≤ ω₁ s t
  ω₁_lip : ∀ s t, a ≤ s → s ≤ t → t ≤ b → ω₁ s t ≤ L₁ * (t - s)
  defect_bound : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
    ‖sewingDefect₁ Ξ s u t‖ ≤ K * ω₁ s u ^ α * ω₂ u t ^ β
  L₁_nonneg : 0 ≤ L₁
  L₂_nonneg : 0 ≤ L₂
  ω₂_nonneg : ∀ s t, a ≤ s → s ≤ t → t ≤ b → 0 ≤ ω₂ s t
  ω₂_diag : ∀ s, ω₂ s s = 0
  ω₂_superadd : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
    ω₂ s u + ω₂ u t ≤ ω₂ s t
  ω₂_lip : ∀ s t, a ≤ s → s ≤ t → t ≤ b → ω₂ s t ≤ L₂ * (t - s)


/-- The geometric ratio for Layer 2: `r₂(α, β) = 2^{-(α+β-1)}`. -/
noncomputable def sewingRatio₂ (α β : ℝ) : ℝ := (2 : ℝ)⁻¹ ^ (α + β - 1)


/-- The sewing constant for Layer 2. -/
noncomputable def sewingConst₂ (α β : ℝ) : ℝ := 1 / (1 - sewingRatio₂ α β)

/-- **The sewn map (Layer 2)**: same construction, different hypotheses. -/
noncomputable def sewingMap₂ (Ξ : ℝ → ℝ → E) [CompleteSpace E]
    (ω₁ ω₂ : ℝ → ℝ → ℝ) (α β K L₁ L₂ a b : ℝ)
    (_hΞ : SewingCondition₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b) (s t : ℝ) : E :=
  if _h : a ≤ s ∧ s ≤ t ∧ t ≤ b then
    limUnder atTop (fun n => dyadicSum₁ Ξ s t n)
  else
    0



end Spectra.Mathlib.StochCalc
