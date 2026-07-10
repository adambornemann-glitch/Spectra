/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Channels.TraceClass.Product
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Stage H — the Hilbert–Schmidt norm and the sharp Schatten–Hölder inequality

The **Hilbert–Schmidt norm** `‖A‖₂ = (∑ᵢ ‖A eᵢ‖²)^{1/2}` and the **sharp Schatten–Hölder bound**

  `‖X ∘L Y‖₁ ≤ ‖X‖₂ · ‖Y‖₂`

for Hilbert–Schmidt `X, Y`.  Combined with `Product.lean`'s membership statement (`X ∘L Y` is trace
class), this is the quantitative half of the Schatten `1 = 2 + 2` duality.

The proof is the diagonal Cauchy–Schwarz.  With `T = X ∘L Y`, polar factor `U = polarIsometry T`,
and `e` a fixed Hilbert basis, the identity `U⋆ T = |T|` gives `⟪eᵢ, |T| eᵢ⟫ = ⟪X⋆ U eᵢ, Y eᵢ⟫`, so

  `‖T‖₁ = ∑ᵢ re ⟪X⋆ U eᵢ, Y eᵢ⟫ ≤ ∑ᵢ ‖X⋆ U eᵢ‖ · ‖Y eᵢ‖ ≤ ‖X⋆ U‖₂ · ‖Y‖₂ ≤ ‖X‖₂ · ‖Y‖₂`,

the middle step being the `ℓ²`-Cauchy–Schwarz on the diagonal, and the last using `‖X⋆ U‖₂ ≤ ‖X‖₂`
(from `‖U‖ ≤ 1` and the adjoint-invariance of `‖·‖₂`).

## Main definitions

* `hsNorm A` — the Hilbert–Schmidt norm `‖A‖₂ = (∑ᵢ ‖A eᵢ‖²)^{1/2}` (junk value `0` off the
  Hilbert–Schmidt operators), packaged over `stdHilbertBasis H`.

## Main results

* `hsNorm_adjoint` — `‖A⋆‖₂ = ‖A‖₂`.
* `hsNorm_comp_le` — `‖A ∘L B‖₂ ≤ ‖A‖ · ‖B‖₂` for Hilbert–Schmidt `B` (the operator ideal bound).
* `traceNorm_comp_le` — **`‖X ∘L Y‖₁ ≤ ‖X‖₂ · ‖Y‖₂`**, the sharp Schatten–Hölder inequality.

## Context

Eighth brick of the trace-class / von Neumann predual development, building on the qualitative
Schatten–Hölder membership (`Product.lean`).  The Hilbert–Schmidt norm and this bound feed the
Bures / Uhlmann fidelity `F(ρ, σ) = ‖√ρ √σ‖₁` (with the continuity estimate `≤ ‖√ρ‖₂ ‖√σ‖₂`) and the
BKM metric.
-/

open ContinuousLinearMap RCLike
open scoped InnerProductSpace InnerProduct ENNReal NNReal

namespace Spectra.QuantumMechanics.Channels

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## An `ℓ²`-Cauchy–Schwarz for `tsum` -/

/-- **Cauchy–Schwarz for `ℓ²` sums.**  For nonnegative real sequences `a, b` with `a²`, `b²`
summable, `∑ᵢ aᵢ bᵢ ≤ (∑ᵢ aᵢ²)^{1/2} (∑ᵢ bᵢ²)^{1/2}`.  Each finite partial sum obeys the finite
Cauchy–Schwarz `Finset.sum_mul_sq_le_sq_mul_sq`, bounded above by the full sums; taking the supremum
over finite sets (`Real.tsum_le_of_sum_le`) gives the tsum bound. -/
private lemma tsum_mul_le_sqrt_mul_sqrt {ι : Type*} {a b : ι → ℝ} (hna : ∀ i, 0 ≤ a i)
    (hnb : ∀ i, 0 ≤ b i) (ha : Summable (fun i => a i ^ 2)) (hb : Summable (fun i => b i ^ 2)) :
    ∑' i, a i * b i ≤ Real.sqrt (∑' i, a i ^ 2) * Real.sqrt (∑' i, b i ^ 2) := by
  refine Real.tsum_le_of_sum_le (fun i => mul_nonneg (hna i) (hnb i)) fun s => ?_
  have hcs : (∑ i ∈ s, a i * b i) ^ 2 ≤ (∑ i ∈ s, a i ^ 2) * ∑ i ∈ s, b i ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq s a b
  have hsa : ∑ i ∈ s, a i ^ 2 ≤ ∑' i, a i ^ 2 := Summable.sum_le_tsum s (fun i _ => sq_nonneg _) ha
  have hsb : ∑ i ∈ s, b i ^ 2 ≤ ∑' i, b i ^ 2 := Summable.sum_le_tsum s (fun i _ => sq_nonneg _) hb
  have hprod : (∑ i ∈ s, a i * b i) ^ 2 ≤ (∑' i, a i ^ 2) * ∑' i, b i ^ 2 :=
    hcs.trans (mul_le_mul hsa hsb (Finset.sum_nonneg fun i _ => sq_nonneg _)
      (tsum_nonneg fun i => sq_nonneg _))
  calc ∑ i ∈ s, a i * b i
      = Real.sqrt ((∑ i ∈ s, a i * b i) ^ 2) :=
        (Real.sqrt_sq (Finset.sum_nonneg fun i _ => mul_nonneg (hna i) (hnb i))).symm
    _ ≤ Real.sqrt ((∑' i, a i ^ 2) * ∑' i, b i ^ 2) := Real.sqrt_le_sqrt hprod
    _ = Real.sqrt (∑' i, a i ^ 2) * Real.sqrt (∑' i, b i ^ 2) :=
        Real.sqrt_mul (tsum_nonneg fun i => sq_nonneg _) _

/-! ## The Hilbert–Schmidt norm -/

/-- The **Hilbert–Schmidt norm** `‖A‖₂ = (∑ᵢ ‖A eᵢ‖²)^{1/2}`, valued in `ℝ` (junk value `0` when `A`
is not Hilbert–Schmidt).  Defined through the `ℝ≥0∞` sum (so that adjoint-invariance is inherited
from `tsum_enorm_apply_sq_adjoint`); on Hilbert–Schmidt operators it is the honest square root
(`hsNorm_of_isHilbertSchmidt`). -/
noncomputable def hsNorm (A : H →L[ℂ] H) : ℝ :=
  Real.sqrt (∑' i, (‖A (stdHilbertBasis H i)‖₊ : ℝ≥0∞) ^ 2).toReal

/-- The Hilbert–Schmidt norm is nonnegative. -/
lemma hsNorm_nonneg (A : H →L[ℂ] H) : 0 ≤ hsNorm A := Real.sqrt_nonneg _

/-- On a Hilbert–Schmidt operator, `‖A‖₂ = (∑ᵢ ‖A eᵢ‖²)^{1/2}` with the honest real sum. -/
lemma hsNorm_of_isHilbertSchmidt {A : H →L[ℂ] H} (hA : IsHilbertSchmidt A) :
    hsNorm A = Real.sqrt (∑' i, ‖A (stdHilbertBasis H i)‖ ^ 2) := by
  have hsummable : Summable (fun i => ‖A (stdHilbertBasis H i)‖ ^ 2) := by
    have h := (isHilbertSchmidt_iff_summable (stdHilbertBasis H) A).mp hA
    simpa only [NNReal.coe_pow, coe_nnnorm] using NNReal.summable_coe.mpr h
  rw [hsNorm]
  congr 1
  rw [funext fun i => enorm_sq_eq_ofReal_norm_sq (A (stdHilbertBasis H i)),
    ← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hsummable,
    ENNReal.toReal_ofReal (tsum_nonneg fun i => sq_nonneg _)]

/-- **Adjoint-invariance** of the Hilbert–Schmidt norm: `‖A⋆‖₂ = ‖A‖₂`. -/
@[simp] lemma hsNorm_adjoint (A : H →L[ℂ] H) : hsNorm (A†) = hsNorm A := by
  rw [hsNorm, hsNorm, ← tsum_enorm_apply_sq_adjoint A (stdHilbertBasis H)]

/-- The real sum `∑ᵢ ‖A eᵢ‖²` is summable when `A` is Hilbert–Schmidt. -/
private lemma summable_norm_sq_of_hs {A : H →L[ℂ] H} (hA : IsHilbertSchmidt A) :
    Summable (fun i => ‖A (stdHilbertBasis H i)‖ ^ 2) := by
  have h := (isHilbertSchmidt_iff_summable (stdHilbertBasis H) A).mp hA
  simpa only [NNReal.coe_pow, coe_nnnorm] using NNReal.summable_coe.mpr h

/-- **The operator-ideal bound** `‖A ∘L B‖₂ ≤ ‖A‖ · ‖B‖₂` for Hilbert–Schmidt `B` (and bounded `A`).
Termwise `‖A (B eᵢ)‖² ≤ ‖A‖² ‖B eᵢ‖²`, summed and rooted. -/
lemma hsNorm_comp_le (A : H →L[ℂ] H) {B : H →L[ℂ] H} (hB : IsHilbertSchmidt B) :
    hsNorm (A ∘L B) ≤ ‖A‖ * hsNorm B := by
  rw [hsNorm_of_isHilbertSchmidt (hB.comp_left A), hsNorm_of_isHilbertSchmidt hB,
    show ‖A‖ * Real.sqrt (∑' i, ‖B (stdHilbertBasis H i)‖ ^ 2)
      = Real.sqrt (‖A‖ ^ 2 * ∑' i, ‖B (stdHilbertBasis H i)‖ ^ 2) from by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg A)]]
  apply Real.sqrt_le_sqrt
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun i => ?_) (summable_norm_sq_of_hs (hB.comp_left A))
    ((summable_norm_sq_of_hs hB).mul_left _)
  rw [ContinuousLinearMap.comp_apply]
  nlinarith [A.le_opNorm (B (stdHilbertBasis H i)), norm_nonneg (A (B (stdHilbertBasis H i))),
    norm_nonneg (B (stdHilbertBasis H i)), norm_nonneg A]

/-- **The other-sided operator-ideal bound** `‖A ∘L B‖₂ ≤ ‖A‖₂ · ‖B‖` for Hilbert–Schmidt `A` (and
bounded `B`), by adjoint-invariance from `hsNorm_comp_le`. -/
lemma hsNorm_comp_le' {A : H →L[ℂ] H} (hA : IsHilbertSchmidt A) (B : H →L[ℂ] H) :
    hsNorm (A ∘L B) ≤ hsNorm A * ‖B‖ :=
  calc hsNorm (A ∘L B) = hsNorm ((A ∘L B)†) := (hsNorm_adjoint _).symm
    _ = hsNorm (B† ∘L A†) := by rw [ContinuousLinearMap.adjoint_comp]
    _ ≤ ‖B†‖ * hsNorm (A†) := hsNorm_comp_le _ ((isHilbertSchmidt_adjoint A).mpr hA)
    _ = hsNorm A * ‖B‖ := by rw [ContinuousLinearMap.adjoint.norm_map, hsNorm_adjoint, mul_comm]

/-! ## The sharp Schatten–Hölder inequality -/

/-- **The sharp Schatten–Hölder inequality** `‖X ∘L Y‖₁ ≤ ‖X‖₂ · ‖Y‖₂` for Hilbert–Schmidt `X, Y`.

Diagonal Cauchy–Schwarz: with `T = X ∘L Y` and polar factor `U`, the identity `U⋆ T = |T|` gives
`re ⟪eᵢ, |T| eᵢ⟫ = re ⟪X⋆ U eᵢ, Y eᵢ⟫ ≤ ‖X⋆ U eᵢ‖ ‖Y eᵢ‖`, and summing with the `ℓ²`-Cauchy–Schwarz
bounds `‖T‖₁ ≤ ‖X⋆ U‖₂ ‖Y‖₂ ≤ ‖X‖₂ ‖Y‖₂` (the last using `‖U‖ ≤ 1` and adjoint-invariance). -/
theorem traceNorm_comp_le {X Y : H →L[ℂ] H} (hX : IsHilbertSchmidt X) (hY : IsHilbertSchmidt Y) :
    traceNorm (X ∘L Y) ≤ hsNorm X * hsNorm Y := by
  have hTC : IsTraceClass (X ∘L Y) := hX.isTraceClass_comp hY
  -- The polar factor and the diagonal identity `⟪eᵢ, |T| eᵢ⟫ = ⟪X⋆ U eᵢ, Y eᵢ⟫`.
  have hdiag : ∀ i, ⟪stdHilbertBasis H i, absOp (X ∘L Y) (stdHilbertBasis H i)⟫_ℂ
      = ⟪(X†) (polarIsometry (X ∘L Y) (stdHilbertBasis H i)), Y (stdHilbertBasis H i)⟫_ℂ := by
    intro i
    rw [← polarIsometry_adjoint_comp (X ∘L Y), ContinuousLinearMap.comp_apply, adjoint_inner_right,
      ContinuousLinearMap.comp_apply, ← adjoint_inner_left X]
  -- The diagonal `cᵢ = re ⟪eᵢ, |T| eᵢ⟫` is a summable sequence of nonnegative reals.
  have hc_eq : ∀ i, re ⟪stdHilbertBasis H i, absOp (X ∘L Y) (stdHilbertBasis H i)⟫_ℂ
      = ‖sqrtOp (absOp (X ∘L Y)) (stdHilbertBasis H i)‖ ^ 2 :=
    fun i => (norm_sqrtOp_sq (absOp (X ∘L Y)) (absOp_nonneg _) (stdHilbertBasis H i)).symm
  have hc_nonneg : ∀ i, 0 ≤ re ⟪stdHilbertBasis H i, absOp (X ∘L Y) (stdHilbertBasis H i)⟫_ℂ :=
    fun i => by rw [hc_eq i]; positivity
  have hc_summable :
      Summable (fun i => re ⟪stdHilbertBasis H i, absOp (X ∘L Y) (stdHilbertBasis H i)⟫_ℂ) := by
    refine (?_ : Summable (fun i => ‖sqrtOp (absOp (X ∘L Y)) (stdHilbertBasis H i)‖ ^ 2)).congr
      (fun i => (hc_eq i).symm)
    have h := (isTraceClass_iff_summable (stdHilbertBasis H) (X ∘L Y)).mp hTC
    simpa only [NNReal.coe_pow, coe_nnnorm] using NNReal.summable_coe.mpr h
  -- `‖T‖₁` as the honest real sum of the diagonal.
  have htn : traceNorm (X ∘L Y)
      = ∑' i, re ⟪stdHilbertBasis H i, absOp (X ∘L Y) (stdHilbertBasis H i)⟫_ℂ := by
    rw [traceNorm_eq (stdHilbertBasis H),
      posTrace_eq_tsum_ofReal (stdHilbertBasis H) (absOp_nonneg _),
      ← ENNReal.ofReal_tsum_of_nonneg hc_nonneg hc_summable,
      ENNReal.toReal_ofReal (tsum_nonneg hc_nonneg)]
  -- `X⋆ U` is Hilbert–Schmidt; the two diagonal `ℓ²` sequences are summable.
  have hXU : IsHilbertSchmidt ((X†) ∘L polarIsometry (X ∘L Y)) :=
    ((isHilbertSchmidt_adjoint X).mpr hX).comp_right (polarIsometry (X ∘L Y))
  have ha : Summable (fun i => ‖((X†) ∘L polarIsometry (X ∘L Y)) (stdHilbertBasis H i)‖ ^ 2) :=
    summable_norm_sq_of_hs hXU
  have hb : Summable (fun i => ‖Y (stdHilbertBasis H i)‖ ^ 2) := summable_norm_sq_of_hs hY
  have hab : Summable
      (fun i => ‖((X†) ∘L polarIsometry (X ∘L Y)) (stdHilbertBasis H i)‖
        * ‖Y (stdHilbertBasis H i)‖) := by
    refine Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun i => ?_) ((ha.add hb).div_const 2)
    nlinarith [sq_nonneg (‖((X†) ∘L polarIsometry (X ∘L Y)) (stdHilbertBasis H i)‖
      - ‖Y (stdHilbertBasis H i)‖),
      norm_nonneg (((X†) ∘L polarIsometry (X ∘L Y)) (stdHilbertBasis H i)),
      norm_nonneg (Y (stdHilbertBasis H i))]
  -- Termwise `re ⟪X⋆ U eᵢ, Y eᵢ⟫ ≤ ‖X⋆ U eᵢ‖ ‖Y eᵢ‖`.
  have hterm : ∀ i, re ⟪stdHilbertBasis H i, absOp (X ∘L Y) (stdHilbertBasis H i)⟫_ℂ
      ≤ ‖((X†) ∘L polarIsometry (X ∘L Y)) (stdHilbertBasis H i)‖ * ‖Y (stdHilbertBasis H i)‖ := by
    intro i
    rw [hdiag i, show ((X†) ∘L polarIsometry (X ∘L Y)) (stdHilbertBasis H i)
      = (X†) (polarIsometry (X ∘L Y) (stdHilbertBasis H i)) from rfl]
    exact ((le_abs_self _).trans (abs_re_le_norm _)).trans (norm_inner_le_norm _ _)
  -- `‖X⋆ U‖₂ ≤ ‖X‖₂` (from `‖U‖ ≤ 1` and the other-sided ideal bound).
  have hbound : hsNorm ((X†) ∘L polarIsometry (X ∘L Y)) ≤ hsNorm X :=
    calc hsNorm ((X†) ∘L polarIsometry (X ∘L Y))
        ≤ hsNorm (X†) * ‖polarIsometry (X ∘L Y)‖ :=
          hsNorm_comp_le' ((isHilbertSchmidt_adjoint X).mpr hX) _
      _ = hsNorm X * ‖polarIsometry (X ∘L Y)‖ := by rw [hsNorm_adjoint]
      _ ≤ hsNorm X * 1 := mul_le_mul_of_nonneg_left (norm_polarIsometry_le_one _) (hsNorm_nonneg X)
      _ = hsNorm X := mul_one _
  -- Assemble.
  rw [htn]
  calc ∑' i, re ⟪stdHilbertBasis H i, absOp (X ∘L Y) (stdHilbertBasis H i)⟫_ℂ
      ≤ ∑' i, ‖((X†) ∘L polarIsometry (X ∘L Y)) (stdHilbertBasis H i)‖
          * ‖Y (stdHilbertBasis H i)‖ :=
        Summable.tsum_le_tsum hterm hc_summable hab
    _ ≤ Real.sqrt (∑' i, ‖((X†) ∘L polarIsometry (X ∘L Y)) (stdHilbertBasis H i)‖ ^ 2)
          * Real.sqrt (∑' i, ‖Y (stdHilbertBasis H i)‖ ^ 2) :=
        tsum_mul_le_sqrt_mul_sqrt (fun i => norm_nonneg _) (fun i => norm_nonneg _) ha hb
    _ = hsNorm ((X†) ∘L polarIsometry (X ∘L Y)) * hsNorm Y := by
        rw [hsNorm_of_isHilbertSchmidt hXU, hsNorm_of_isHilbertSchmidt hY]
    _ ≤ hsNorm X * hsNorm Y := mul_le_mul_of_nonneg_right hbound (hsNorm_nonneg Y)

end Spectra.QuantumMechanics.Channels
