/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: LayerTwo/Map/Specialize.lean
-/
import Spectra.Mathlib.StochasticCalc.SewingLemma.LipschitzProdControl.Map.Additive

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace Spectra.Mathlib.StochCalc

section Specialization

/-- The Layer 1 and Layer 2 sewn maps agree when both conditions hold.
Both are `limUnder atTop (dyadicSum₁ Ξ s t)` — literally the same sequence. -/
theorem sewingMap₁_eq_sewingMap₂ [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {θ K a b : ℝ}
    (hΞ₁ : SewingCondition₁ Ξ θ K a b)
    {ω₁ ω₂ : ℝ → ℝ → ℝ} {α β K₂ L₁ L₂ : ℝ}
    (hΞ₂ : SewingCondition₂ Ξ ω₁ ω₂ α β K₂ L₁ L₂ a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    sewingMap₁ Ξ θ K a b hΞ₁ s t =
      sewingMap₂ Ξ ω₁ ω₂ α β K₂ L₁ L₂ a b hΞ₂ s t := by
  have hcond : a ≤ s ∧ s ≤ t ∧ t ≤ b := ⟨has, hst, htb⟩
  simp only [sewingMap₁, sewingMap₂, dif_pos hcond]



end Specialization

end Spectra.Mathlib.StochCalc
