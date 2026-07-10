/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.InnerProductSpace.Dual
import Spectra.Mathlib.CharFunBridge
/-!
# Translation-invariant product kernels are `L²`

A *convolution-type* integral operator `T f(x) = ∫ b(x − y) f(y) dy` multiplied by a potential
`a(x)` has kernel `K(x, y) = a(x) · b(x − y)`. This file proves the membership and exact-norm
facts for such kernels:

* `memLp_kernel_mul_sub` — if `a, b ∈ L²(μ)` (with `μ` a two-sided-invariant Haar measure on a
  measurable additive group) then `(x, y) ↦ a x · b (x − y) ∈ L²(μ × μ)`.
* `eLpNorm_kernel_mul_sub` — the exact tensor-norm identity
  `‖(x, y) ↦ a x · b (x − y)‖₂ = ‖a‖₂ · ‖b‖₂`.

These are the engine for the Coulomb relative-compactness program (Track A, hydrogen continuous
spectrum): the truncated resolvent kernel `Kₙ(x, y) = Vⁿ(x) · G_z(x − y)` is exactly of this
shape, so `memLp_kernel_mul_sub` puts it in `L²(ℝ³ × ℝ³)` — feeding
`Spectra.CompactOperator.isCompactOperator_integralOperator` — and `eLpNorm_kernel_mul_sub`
supplies the `‖Kₙ‖₂ = ‖Vⁿ‖₂ · ‖G_z‖₂` identity that controls the operator-norm limit.

The statements are deliberately general (any `NormedAddCommGroup` with a measurable group
structure and a two-sided-invariant `SFinite` Haar measure); typeclass inference specialises them
to `EuclideanSpace ℝ (Fin 3)` with `volume` with no extra glue.
-/

open MeasureTheory ENNReal
open scoped ENNReal NNReal

namespace Spectra.CompactOperator

variable {E : Type*}
  [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableAdd₂ E] [MeasurableNeg E]
  {μ : Measure E}
  [μ.IsAddLeftInvariant] [μ.IsAddRightInvariant] [μ.IsNegInvariant] [SFinite μ]

/-- The product (translation-invariant) kernel `(x, y) ↦ a x * b (x - y)` lies in `L²` of the
product measure whenever `a, b ∈ L²`. -/
theorem memLp_kernel_mul_sub {a b : E → ℂ}
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    MemLp (fun p : E × E => a p.1 * b (p.1 - p.2)) 2 (μ.prod μ) := by
  -- measurability of the kernel
  have _hmeas_sub : Measurable (fun p : E × E => p.1 - p.2) :=
    measurable_fst.sub measurable_snd
  have hae_a : AEStronglyMeasurable (fun p : E × E => a p.1) (μ.prod μ) :=
    ha.aestronglyMeasurable.comp_fst
  have hae_b : AEStronglyMeasurable (fun p : E × E => b (p.1 - p.2)) (μ.prod μ) := by
    -- b ∘ (sub) where sub is measure-preserving onto μ.prod μ
    have hmp : MeasurePreserving (fun p : E × E => (p.1 - p.2, p.2)) (μ.prod μ) (μ.prod μ) :=
      measurePreserving_sub_prod μ μ
    have : AEStronglyMeasurable (fun q : E × E => b q.1) (μ.prod μ) :=
      hb.aestronglyMeasurable.comp_fst
    exact this.comp_measurePreserving hmp
  have hae : AEStronglyMeasurable (fun p : E × E => a p.1 * b (p.1 - p.2)) (μ.prod μ) :=
    hae_a.mul hae_b
  refine ⟨hae, ?_⟩
  -- reduce eLpNorm < ∞ to a lintegral being finite
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  -- the integrand: ‖a p.1 * b (p.1 - p.2)‖ₑ ^ 2 = ‖a p.1‖ₑ^2 * ‖b (p.1 - p.2)‖ₑ^2
  have hint :
      (∫⁻ p : E × E, ‖a p.1 * b (p.1 - p.2)‖ₑ ^ (2 : ℝ) ∂(μ.prod μ))
        = ∫⁻ p : E × E, ‖a p.1‖ₑ ^ (2 : ℝ) * ‖b (p.1 - p.2)‖ₑ ^ (2 : ℝ) ∂(μ.prod μ) := by
    apply lintegral_congr
    intro p
    rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  rw [hint]
  -- Tonelli
  have htonelli :
      (∫⁻ p : E × E, ‖a p.1‖ₑ ^ (2 : ℝ) * ‖b (p.1 - p.2)‖ₑ ^ (2 : ℝ) ∂(μ.prod μ))
        = ∫⁻ x, ‖a x‖ₑ ^ (2 : ℝ) * (∫⁻ y, ‖b (x - y)‖ₑ ^ (2 : ℝ) ∂μ) ∂μ := by
    rw [lintegral_prod]
    · -- pull the x-constant out of the inner integral
      apply lintegral_congr
      intro x
      simp only []
      rw [lintegral_const_mul' (‖a x‖ₑ ^ (2 : ℝ)) (fun y => ‖b (x - y)‖ₑ ^ (2 : ℝ))
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) enorm_ne_top)]
    · -- AEMeasurable of the integrand
      exact (hae_a.enorm.pow_const _).mul (hae_b.enorm.pow_const _)
  rw [htonelli]
  -- inner integral: translation invariance ∫⁻ y, ‖b (x - y)‖² = ∫⁻ y, ‖b y‖²
  have hinner : ∀ x : E,
      (∫⁻ y, ‖b (x - y)‖ₑ ^ (2 : ℝ) ∂μ) = ∫⁻ y, ‖b y‖ₑ ^ (2 : ℝ) ∂μ := by
    intro x
    exact lintegral_sub_left_eq_self (fun y => ‖b y‖ₑ ^ (2 : ℝ)) x
  simp_rw [hinner]
  -- pull the (now constant) ∫⁻ ‖b‖² out
  rw [lintegral_mul_const'' _ (ha.aestronglyMeasurable.enorm.pow_const (2 : ℝ))]
  -- now product of two finite lintegrals
  apply ENNReal.mul_lt_top
  · have := ha.eLpNorm_lt_top
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)] at this
    simpa using this
  · have := hb.eLpNorm_lt_top
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)] at this
    simpa using this

/-- The exact `L²` tensor-norm identity for the translation-invariant product kernel:
`‖(x,y) ↦ a x · b (x-y)‖₂ = ‖a‖₂ · ‖b‖₂`. -/
theorem eLpNorm_kernel_mul_sub {a b : E → ℂ}
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    eLpNorm (fun p : E × E => a p.1 * b (p.1 - p.2)) 2 (μ.prod μ)
      = eLpNorm a 2 μ * eLpNorm b 2 μ := by
  have hae_a : AEStronglyMeasurable (fun p : E × E => a p.1) (μ.prod μ) :=
    ha.aestronglyMeasurable.comp_fst
  have hae_b : AEStronglyMeasurable (fun p : E × E => b (p.1 - p.2)) (μ.prod μ) := by
    have hmp : MeasurePreserving (fun p : E × E => (p.1 - p.2, p.2)) (μ.prod μ) (μ.prod μ) :=
      measurePreserving_sub_prod μ μ
    exact (hb.aestronglyMeasurable.comp_fst).comp_measurePreserving hmp
  -- the squared L²-norm lintegral of the kernel factors as a product
  have hlint :
      (∫⁻ p : E × E, ‖a p.1 * b (p.1 - p.2)‖ₑ ^ (2 : ℝ) ∂(μ.prod μ))
        = (∫⁻ x, ‖a x‖ₑ ^ (2 : ℝ) ∂μ) * (∫⁻ y, ‖b y‖ₑ ^ (2 : ℝ) ∂μ) := by
    have hint :
        (∫⁻ p : E × E, ‖a p.1 * b (p.1 - p.2)‖ₑ ^ (2 : ℝ) ∂(μ.prod μ))
          = ∫⁻ p : E × E, ‖a p.1‖ₑ ^ (2 : ℝ) * ‖b (p.1 - p.2)‖ₑ ^ (2 : ℝ) ∂(μ.prod μ) := by
      apply lintegral_congr; intro p
      rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    rw [hint, lintegral_prod _ ((hae_a.enorm.pow_const _).mul (hae_b.enorm.pow_const _))]
    have : (∫⁻ x, ∫⁻ y, ‖a x‖ₑ ^ (2 : ℝ) * ‖b (x - y)‖ₑ ^ (2 : ℝ) ∂μ ∂μ)
        = ∫⁻ x, ‖a x‖ₑ ^ (2 : ℝ) * (∫⁻ y, ‖b y‖ₑ ^ (2 : ℝ) ∂μ) ∂μ := by
      apply lintegral_congr; intro x
      rw [lintegral_const_mul' (‖a x‖ₑ ^ (2 : ℝ)) (fun y => ‖b (x - y)‖ₑ ^ (2 : ℝ))
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) enorm_ne_top)]
      rw [lintegral_sub_left_eq_self (fun y => ‖b y‖ₑ ^ (2 : ℝ)) x]
    rw [this, lintegral_mul_const'' _ (ha.aestronglyMeasurable.enorm.pow_const (2 : ℝ))]
  -- assemble: eLpNorm = (lintegral)^(1/2) = ((∫‖a‖²)(∫‖b‖²))^(1/2) = ‖a‖₂‖b‖₂
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  rw [hlint, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]

end Spectra.CompactOperator
