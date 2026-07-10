/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Summable families of inner products

General `ℓ²`-pairing estimates for `∑ᵢ ⟪p i, q i⟫` when the families `p, q` have square-summable
norms, on any inner product space over `RCLike 𝕜`.  These carry no trace-class content — they are
the underlying inner-product facts behind bounds such as `|tr T| ≤ ‖T‖₁`.

## Main results

* `Spectra.QuantumMechanics.Channels.summable_inner_of_summable_sq` — `i ↦ ⟪p i, q i⟫` is summable
  when both `i ↦ ‖p i‖²` and `i ↦ ‖q i‖²` are.
* `Spectra.QuantumMechanics.Channels.weighted_norm_tsum_inner_le` — the weighted
  arithmetic–geometric bound `β · ‖∑ᵢ ⟪p i, q i⟫‖ ≤ (∑ᵢ ‖p i‖² + β² ∑ᵢ ‖q i‖²) / 2` for `β ≥ 0`.
  Choosing the weight `β` recovers the sharp Cauchy–Schwarz constant without any `Lᵖ`/Hölder
  machinery.
-/

open RCLike
open scoped InnerProductSpace

namespace Spectra.QuantumMechanics.Channels

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*}

/-- The inner-product family `i ↦ ⟪p i, q i⟫` is summable whenever both `i ↦ ‖p i‖²` and
`i ↦ ‖q i‖²` are (comparison against `(‖p i‖² + ‖q i‖²) / 2`). -/
lemma summable_inner_of_summable_sq {p q : ι → E}
    (hp : Summable fun i => ‖p i‖ ^ 2) (hq : Summable fun i => ‖q i‖ ^ 2) :
    Summable (fun i => ⟪p i, q i⟫_𝕜) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) ((hp.add hq).div_const 2)
  have h1 : ‖⟪p i, q i⟫_𝕜‖ ≤ ‖p i‖ * ‖q i‖ := norm_inner_le_norm _ _
  nlinarith [sq_nonneg (‖p i‖ - ‖q i‖), norm_nonneg (p i), norm_nonneg (q i)]

/-- **Weighted arithmetic–geometric estimate.** For families `p, q` with square-summable norms and a
weight `β ≥ 0`, `β · ‖∑ᵢ ⟪p i, q i⟫‖ ≤ (∑ᵢ ‖p i‖² + β² ∑ᵢ ‖q i‖²) / 2`.  The weight `β` is chosen at
the call site to hit the sharp constant (`β = 1` gives `‖∑ ⟪p, q⟫‖ ≤ (∑‖p‖² + ∑‖q‖²)/2`), so no
`Lᵖ`/Hölder Cauchy–Schwarz is needed. -/
lemma weighted_norm_tsum_inner_le {p q : ι → E} (β : ℝ) (hβ : 0 ≤ β)
    (hp : Summable fun i => ‖p i‖ ^ 2) (hq : Summable fun i => ‖q i‖ ^ 2) :
    β * ‖∑' i, ⟪p i, q i⟫_𝕜‖ ≤ (∑' i, ‖p i‖ ^ 2 + β ^ 2 * ∑' i, ‖q i‖ ^ 2) / 2 := by
  have hterm : ∀ i, β * ‖⟪p i, q i⟫_𝕜‖ ≤ (‖p i‖ ^ 2 + β ^ 2 * ‖q i‖ ^ 2) / 2 := by
    intro i
    have h1 : ‖⟪p i, q i⟫_𝕜‖ ≤ ‖p i‖ * ‖q i‖ := norm_inner_le_norm _ _
    nlinarith [sq_nonneg (‖p i‖ - β * ‖q i‖), norm_nonneg (p i), norm_nonneg (q i),
      mul_le_mul_of_nonneg_left h1 hβ]
  have hbound0 : ∀ i, ‖⟪p i, q i⟫_𝕜‖ ≤ (‖p i‖ ^ 2 + ‖q i‖ ^ 2) / 2 := by
    intro i
    have h1 : ‖⟪p i, q i⟫_𝕜‖ ≤ ‖p i‖ * ‖q i‖ := norm_inner_le_norm _ _
    nlinarith [sq_nonneg (‖p i‖ - ‖q i‖), norm_nonneg (p i), norm_nonneg (q i)]
  have hsum_norm : Summable (fun i => ‖⟪p i, q i⟫_𝕜‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hbound0 ((hp.add hq).div_const 2)
  calc β * ‖∑' i, ⟪p i, q i⟫_𝕜‖
      ≤ β * ∑' i, ‖⟪p i, q i⟫_𝕜‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsum_norm) hβ
    _ = ∑' i, β * ‖⟪p i, q i⟫_𝕜‖ := (Summable.tsum_mul_left β hsum_norm).symm
    _ ≤ ∑' i, (‖p i‖ ^ 2 + β ^ 2 * ‖q i‖ ^ 2) / 2 :=
        Summable.tsum_le_tsum hterm (hsum_norm.mul_left β)
          (((hp.add (hq.mul_left (β ^ 2)))).div_const 2)
    _ = (∑' i, ‖p i‖ ^ 2 + β ^ 2 * ∑' i, ‖q i‖ ^ 2) / 2 := by
        rw [tsum_div_const, Summable.tsum_add hp (hq.mul_left (β ^ 2)), hq.tsum_mul_left]

/-- The family of norms `i ↦ ‖⟪p i, q i⟫‖` is summable when both `i ↦ ‖p i‖²` and `i ↦ ‖q i‖²` are.
-/
lemma summable_norm_inner {p q : ι → E}
    (hp : Summable fun i => ‖p i‖ ^ 2) (hq : Summable fun i => ‖q i‖ ^ 2) :
    Summable (fun i => ‖⟪p i, q i⟫_𝕜‖) := by
  refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) ((hp.add hq).div_const 2)
  have h1 : ‖⟪p i, q i⟫_𝕜‖ ≤ ‖p i‖ * ‖q i‖ := norm_inner_le_norm _ _
  nlinarith [sq_nonneg (‖p i‖ - ‖q i‖), norm_nonneg (p i), norm_nonneg (q i)]

/-- **Sum-of-norms bound.** `∑ᵢ ‖⟪p i, q i⟫‖ ≤ (∑ᵢ ‖p i‖² + ∑ᵢ ‖q i‖²) / 2`.  (The `‖·‖`-of-the-sum
form is `weighted_norm_tsum_inner_le`; this is the sum-of-`‖·‖`s form, used where a *termwise*
absolute bound is needed.) -/
lemma tsum_norm_inner_le {p q : ι → E}
    (hp : Summable fun i => ‖p i‖ ^ 2) (hq : Summable fun i => ‖q i‖ ^ 2) :
    ∑' i, ‖⟪p i, q i⟫_𝕜‖ ≤ (∑' i, ‖p i‖ ^ 2 + ∑' i, ‖q i‖ ^ 2) / 2 := by
  have hbound0 : ∀ i, ‖⟪p i, q i⟫_𝕜‖ ≤ (‖p i‖ ^ 2 + ‖q i‖ ^ 2) / 2 := by
    intro i
    have h1 : ‖⟪p i, q i⟫_𝕜‖ ≤ ‖p i‖ * ‖q i‖ := norm_inner_le_norm _ _
    nlinarith [sq_nonneg (‖p i‖ - ‖q i‖), norm_nonneg (p i), norm_nonneg (q i)]
  calc ∑' i, ‖⟪p i, q i⟫_𝕜‖
      ≤ ∑' i, (‖p i‖ ^ 2 + ‖q i‖ ^ 2) / 2 :=
        Summable.tsum_le_tsum hbound0 (summable_norm_inner hp hq) ((hp.add hq).div_const 2)
    _ = (∑' i, ‖p i‖ ^ 2 + ∑' i, ‖q i‖ ^ 2) / 2 := by
        rw [tsum_div_const, Summable.tsum_add hp hq]

end Spectra.QuantumMechanics.Channels
