/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Channels.TraceClass.Norm
import Spectra.QuantumMechanics.Channels.TraceClass.PartialIsometry
import Spectra.QuantumMechanics.Channels.TsumInner

/-!
# Stage B — the complex trace functional and `|tr T| ≤ ‖T‖₁`

For a bounded operator `T : H →L[ℂ] H` on a complex Hilbert space, the **trace** is
`tr T = ∑ᵢ ⟪eᵢ, T eᵢ⟫` (complex-valued), over the canonical Hilbert basis `stdHilbertBasis H`. Using
the bounded polar decomposition `T = U |T|` and the factorization `|T| = |T|^{1/2} · |T|^{1/2}`,
each summand rewrites as a *twisted* inner product `⟪eᵢ, T eᵢ⟫ = ⟪|T|^{1/2} (U⋆ eᵢ), |T|^{1/2} eᵢ⟫`,
whose two families are both `ℓ²` with square-sum `≤ tr |T| = ‖T‖₁`. A weighted arithmetic–geometric
estimate then gives absolute summability of the trace and the bound `|tr T| ≤ ‖T‖₁`.

## Main definitions

* `Spectra.QuantumMechanics.Channels.trace T` — the complex trace `∑ᵢ ⟪eᵢ, T eᵢ⟫`.

## Main results

* `trace_summand_polar` — the twisted-inner-product identity behind every estimate.
* `trace_summable` — for trace-class `T` the diagonal `i ↦ ⟪eᵢ, T eᵢ⟫` is summable.
* `trace_zero`, `trace_add`, `trace_smul` — linearity (the additive law needs trace-class summands).
* `norm_trace_le_traceNorm` — **`|tr T| ≤ ‖T‖₁`**.
* `norm_trace_comp_le` — **`|tr (B T)| ≤ ‖B‖ · ‖T‖₁`**, the boundedness of the duality functional
  `B ↦ tr (B T)` consumed by the trace-class predual duality `B(H) = (TraceClass H)⋆`.
* `trace_of_nonneg` — for `0 ≤ S` the complex trace is the honest real trace `((tr S).toReal : ℂ)`.

## Context

Third brick of the trace-class / von Neumann predual development (the discharge-first route to the
Tomita–Takesaki fundamental theorem), building on Stage A (`PartialIsometry.lean`) and the trace
norm (`Norm.lean`). Cyclicity `tr (AB) = tr (BA)`, the triangle inequality, and Banach completeness
are the next bricks.
-/

open ContinuousLinearMap RCLike Spectra.QuantumMechanics.Channels
open scoped InnerProductSpace InnerProduct ENNReal NNReal

namespace Spectra.QuantumMechanics.Channels

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

/-! ## `ℝ≥0∞ → ℝ` bridges for square-summable families -/

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- If `∑ᵢ ‖p i‖²` is finite in `ℝ≥0∞`, then `i ↦ ‖p i‖²` is summable in `ℝ`. -/
private lemma summable_sq_of_ne_top {p : ι → H} (hfin : ∑' i, (‖p i‖₊ : ℝ≥0∞) ^ 2 ≠ ⊤) :
    Summable (fun i => ‖p i‖ ^ 2) := by
  have h1 : Summable (fun i => ‖p i‖₊ ^ 2) := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable]
    simpa only [ENNReal.coe_pow] using hfin
  simpa only [NNReal.coe_pow, coe_nnnorm] using NNReal.summable_coe.mpr h1

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- The real square-sum is the `toReal` of the `ℝ≥0∞` square-sum (unconditionally: both are `0` in
the non-summable case). -/
private lemma tsum_sq_eq_toReal (p : ι → H) :
    ∑' i, ‖p i‖ ^ 2 = (∑' i, (‖p i‖₊ : ℝ≥0∞) ^ 2).toReal := by
  rw [ENNReal.tsum_toReal_eq (fun i => ENNReal.pow_ne_top ENNReal.coe_ne_top)]
  refine tsum_congr fun i => ?_
  rw [← ENNReal.coe_pow, ENNReal.coe_toReal]
  push_cast
  ring

/-! ## The twisted family and its square-sum bound

The weighted Cauchy–Schwarz estimate `weighted_norm_tsum_inner_le` and the inner-summability lemma
`summable_inner_of_summable_sq` used below are the general `ℓ²`-pairing facts, kept in
`Spectra.QuantumMechanics.Channels` (`Spectra/QuantumMechanics/Channels/TsumInner.lean`). -/

/-- **The twist identity.** With `S = |T|^{1/2}` and `U = polarIsometry T`,
`⟪(S ∘ U⋆) x, S y⟫ = ⟪x, T y⟫` — the reduction of a diagonal entry to a `|T|^{1/2}`-twisted pairing.
-/
lemma trace_summand_polar (T : H →L[ℂ] H) (x y : H) :
    ⟪(sqrtOp (absOp T) ∘L (polarIsometry T)†) x, sqrtOp (absOp T) y⟫_ℂ = ⟪x, T y⟫_ℂ := by
  have hSadj : (sqrtOp (absOp T))† = sqrtOp (absOp T) := by
    rw [← star_eq_adjoint]; exact (sqrtOp_isSelfAdjoint (absOp T)).star_eq
  have hM : (sqrtOp (absOp T) ∘L (polarIsometry T)†)† = polarIsometry T ∘L sqrtOp (absOp T) := by
    rw [adjoint_comp, adjoint_adjoint, hSadj]
  have hSS : sqrtOp (absOp T) (sqrtOp (absOp T) y) = absOp T y := by
    rw [← ContinuousLinearMap.mul_apply, sqrtOp_mul_self (absOp T) (absOp_nonneg T)]
  rw [← adjoint_inner_right (sqrtOp (absOp T) ∘L (polarIsometry T)†) x (sqrtOp (absOp T) y)]
  congr 1
  rw [hM, ContinuousLinearMap.comp_apply, hSS, polarIsometry_absOp]

/-- **Square-sum bound for the twisted family.** For trace-class `T`, `∑ᵢ ‖(S ∘ D⋆) eᵢ‖²` is
summable and bounded by `c² · ‖T‖₁`, whenever `D` shrinks `S eᵢ` by a factor `c`
(`‖D (S x)‖ ≤ c ‖S x‖`). Instantiated at `D = U` (`c = 1`) for `tr` and `D = B U` (`c = ‖B‖`) for
`tr (B T)`. -/
private lemma sqrtOp_comp_adjoint_bound (T D : H →L[ℂ] H) {c : ℝ≥0}
    (hc : ∀ x, ‖D (sqrtOp (absOp T) x)‖₊ ≤ c * ‖sqrtOp (absOp T) x‖₊) (hT : IsTraceClass T) :
    Summable (fun i => ‖(sqrtOp (absOp T) ∘L D†) (stdHilbertBasis H i)‖ ^ 2) ∧
      ∑' i, ‖(sqrtOp (absOp T) ∘L D†) (stdHilbertBasis H i)‖ ^ 2 ≤ (c : ℝ) ^ 2 * traceNorm T := by
  have hSadj : (sqrtOp (absOp T))† = sqrtOp (absOp T) := by
    rw [← star_eq_adjoint]; exact (sqrtOp_isSelfAdjoint (absOp T)).star_eq
  have hadj : (sqrtOp (absOp T) ∘L D†)† = D ∘L sqrtOp (absOp T) := by
    rw [adjoint_comp, adjoint_adjoint, hSadj]
  have hposT : posTrace (stdHilbertBasis H) (absOp T)
      = ∑' i, (‖sqrtOp (absOp T) (stdHilbertBasis H i)‖₊ : ℝ≥0∞) ^ 2 := rfl
  have key : ∑' i, (‖(sqrtOp (absOp T) ∘L D†) (stdHilbertBasis H i)‖₊ : ℝ≥0∞) ^ 2
      ≤ (c : ℝ≥0∞) ^ 2 * posTrace (stdHilbertBasis H) (absOp T) := by
    rw [hposT, ← ENNReal.tsum_mul_left]
    calc ∑' i, (‖(sqrtOp (absOp T) ∘L D†) (stdHilbertBasis H i)‖₊ : ℝ≥0∞) ^ 2
        = ∑' i, (‖(D ∘L sqrtOp (absOp T)) (stdHilbertBasis H i)‖₊ : ℝ≥0∞) ^ 2 := by
          rw [tsum_enorm_apply_sq_adjoint (sqrtOp (absOp T) ∘L D†) (stdHilbertBasis H), hadj]
      _ ≤ ∑' i, (c : ℝ≥0∞) ^ 2 * (‖sqrtOp (absOp T) (stdHilbertBasis H i)‖₊ : ℝ≥0∞) ^ 2 := by
          apply ENNReal.tsum_le_tsum
          intro i
          rw [ContinuousLinearMap.comp_apply, ← mul_pow]
          gcongr
          exact_mod_cast hc (stdHilbertBasis H i)
  have hmul_ne : (c : ℝ≥0∞) ^ 2 * posTrace (stdHilbertBasis H) (absOp T) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hT
  have hfin : ∑' i, (‖(sqrtOp (absOp T) ∘L D†) (stdHilbertBasis H i)‖₊ : ℝ≥0∞) ^ 2 ≠ ⊤ :=
    ne_top_of_le_ne_top hmul_ne key
  refine ⟨summable_sq_of_ne_top hfin, ?_⟩
  rw [tsum_sq_eq_toReal]
  calc (∑' i, (‖(sqrtOp (absOp T) ∘L D†) (stdHilbertBasis H i)‖₊ : ℝ≥0∞) ^ 2).toReal
      ≤ ((c : ℝ≥0∞) ^ 2 * posTrace (stdHilbertBasis H) (absOp T)).toReal :=
        ENNReal.toReal_mono hmul_ne key
    _ = (c : ℝ) ^ 2 * traceNorm T := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal]; rfl

/-! ## The complex trace and its estimates -/

/-- The **complex trace** `tr T = ∑ᵢ ⟪eᵢ, T eᵢ⟫` over the canonical Hilbert basis. -/
noncomputable def trace (T : H →L[ℂ] H) : ℂ :=
  ∑' i, ⟪stdHilbertBasis H i, T (stdHilbertBasis H i)⟫_ℂ

/-- **The Hilbert–Schmidt sum of `|T|^{1/2}` is square-summable** for trace-class `T`. -/
lemma summable_sqrtOp_absOp_sq {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    Summable (fun i => ‖sqrtOp (absOp T) (stdHilbertBasis H i)‖ ^ 2) :=
  summable_sq_of_ne_top hT

/-- **The Hilbert–Schmidt sum of `|T|^{1/2}` equals the trace norm**: `∑ᵢ ‖|T|^{1/2} eᵢ‖² = ‖T‖₁`.
-/
lemma tsum_sqrtOp_absOp_sq (T : H →L[ℂ] H) :
    ∑' i, ‖sqrtOp (absOp T) (stdHilbertBasis H i)‖ ^ 2 = traceNorm T := by
  rw [tsum_sq_eq_toReal]; rfl

/-- For trace-class `T` the diagonal `i ↦ ⟪eᵢ, T eᵢ⟫` is summable. -/
theorem trace_summable (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    Summable (fun i => ⟪stdHilbertBasis H i, T (stdHilbertBasis H i)⟫_ℂ) := by
  have hp := (sqrtOp_comp_adjoint_bound T (polarIsometry T)
    (fun x => by
      rw [one_mul]; exact_mod_cast norm_polarIsometry_apply_le T (sqrtOp (absOp T) x)) hT).1
  exact (summable_inner_of_summable_sq hp (summable_sqrtOp_absOp_sq hT)).congr
    (fun i => trace_summand_polar T (stdHilbertBasis H i) (stdHilbertBasis H i))

@[simp] theorem trace_zero : trace (0 : H →L[ℂ] H) = 0 := by
  simp [trace]

theorem trace_add {S T : H →L[ℂ] H} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    trace (S + T) = trace S + trace T := by
  simp only [trace, ContinuousLinearMap.add_apply, inner_add_right]
  exact Summable.tsum_add (trace_summable S hS) (trace_summable T hT)

theorem trace_smul (c : ℂ) (T : H →L[ℂ] H) : trace (c • T) = c * trace T := by
  simp only [trace, ContinuousLinearMap.smul_apply, inner_smul_right]
  exact tsum_mul_left

/-- **`|tr T| ≤ ‖T‖₁`.** -/
theorem norm_trace_le_traceNorm (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    ‖trace T‖ ≤ traceNorm T := by
  obtain ⟨hp_sum, hp_le⟩ := sqrtOp_comp_adjoint_bound T (polarIsometry T)
    (fun x => by rw [one_mul]; exact_mod_cast norm_polarIsometry_apply_le T (sqrtOp (absOp T) x)) hT
  have hq_sum := summable_sqrtOp_absOp_sq hT
  have hq_tsum := tsum_sqrtOp_absOp_sq T
  have htr : trace T = ∑' i, ⟪(sqrtOp (absOp T) ∘L (polarIsometry T)†) (stdHilbertBasis H i),
      sqrtOp (absOp T) (stdHilbertBasis H i)⟫_ℂ := by
    rw [trace]
    exact tsum_congr fun i =>
      (trace_summand_polar T (stdHilbertBasis H i) (stdHilbertBasis H i)).symm
  rw [htr]
  have hmaster := weighted_norm_tsum_inner_le (𝕜 := ℂ) (p := fun i =>
      (sqrtOp (absOp T) ∘L (polarIsometry T)†) (stdHilbertBasis H i))
    (q := fun i => sqrtOp (absOp T) (stdHilbertBasis H i)) 1 zero_le_one hp_sum hq_sum
  simp only [one_mul, one_pow] at hmaster
  rw [hq_tsum] at hmaster
  have hp_le' : ∑' i, ‖(sqrtOp (absOp T) ∘L (polarIsometry T)†) (stdHilbertBasis H i)‖ ^ 2
      ≤ traceNorm T := by simpa using hp_le
  linarith [hmaster, hp_le']

/-- **`|tr (B T)| ≤ ‖B‖ · ‖T‖₁`** — the boundedness of the duality functional `B ↦ tr (B T)`. -/
theorem norm_trace_comp_le (B T : H →L[ℂ] H) (hT : IsTraceClass T) :
    ‖trace (B ∘L T)‖ ≤ ‖B‖ * traceNorm T := by
  rcases eq_or_lt_of_le (norm_nonneg B) with hB | hB
  · have hB0 : B = 0 := norm_eq_zero.mp hB.symm
    subst hB0
    simp [trace]
  · obtain ⟨hp_sum, hp_le⟩ := sqrtOp_comp_adjoint_bound T (B ∘L polarIsometry T) (c := ‖B‖₊)
      (fun x => by
        rw [ContinuousLinearMap.comp_apply]
        calc ‖B (polarIsometry T (sqrtOp (absOp T) x))‖₊
            ≤ ‖B‖₊ * ‖polarIsometry T (sqrtOp (absOp T) x)‖₊ := by exact_mod_cast B.le_opNorm _
          _ ≤ ‖B‖₊ * ‖sqrtOp (absOp T) x‖₊ := by
              gcongr
              exact_mod_cast norm_polarIsometry_apply_le T (sqrtOp (absOp T) x)) hT
    have hq_sum := summable_sqrtOp_absOp_sq hT
    have hq_tsum := tsum_sqrtOp_absOp_sq T
    have htr : trace (B ∘L T) = ∑' i, ⟪(sqrtOp (absOp T) ∘L (B ∘L polarIsometry T)†)
        (stdHilbertBasis H i), sqrtOp (absOp T) (stdHilbertBasis H i)⟫_ℂ := by
      rw [trace]
      refine tsum_congr fun i => ?_
      rw [ContinuousLinearMap.comp_apply B T,
        ← adjoint_inner_left B (T (stdHilbertBasis H i)) (stdHilbertBasis H i), adjoint_comp]
      exact (trace_summand_polar T ((B†) (stdHilbertBasis H i)) (stdHilbertBasis H i)).symm
    rw [htr]
    have hmaster := weighted_norm_tsum_inner_le (𝕜 := ℂ) (p := fun i =>
        (sqrtOp (absOp T) ∘L (B ∘L polarIsometry T)†) (stdHilbertBasis H i))
      (q := fun i => sqrtOp (absOp T) (stdHilbertBasis H i)) ‖B‖ (norm_nonneg B) hp_sum hq_sum
    rw [hq_tsum] at hmaster
    have hp_le' : ∑' i, ‖(sqrtOp (absOp T) ∘L (B ∘L polarIsometry T)†) (stdHilbertBasis H i)‖ ^ 2
        ≤ ‖B‖ ^ 2 * traceNorm T := by simpa only [coe_nnnorm] using hp_le
    have hfinal : ‖B‖ * ‖∑' i, ⟪(sqrtOp (absOp T) ∘L (B ∘L polarIsometry T)†) (stdHilbertBasis H i),
        sqrtOp (absOp T) (stdHilbertBasis H i)⟫_ℂ‖ ≤ ‖B‖ * (‖B‖ * traceNorm T) := by
      nlinarith [hmaster, hp_le']
    exact le_of_mul_le_mul_left hfinal hB

/-- **`tr S = ((tr |S|).toReal : ℂ)` for `0 ≤ S`** — the complex trace of a positive operator is its
honest real trace. -/
theorem trace_of_nonneg {S : H →L[ℂ] H} (hS : 0 ≤ S) (b : HilbertBasis ι ℂ H) :
    trace S = ((posTrace b S).toReal : ℂ) := by
  rw [posTrace_indep b (stdHilbertBasis H) S, trace]
  have hterm : ∀ i, ⟪stdHilbertBasis H i, S (stdHilbertBasis H i)⟫_ℂ
      = ((‖sqrtOp S (stdHilbertBasis H i)‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    have hSe : S (stdHilbertBasis H i) = ((sqrtOp S)†) (sqrtOp S (stdHilbertBasis H i)) := by
      rw [← ContinuousLinearMap.comp_apply, sqrtOp_comp_self S hS]
    rw [hSe, adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [tsum_congr hterm, ← Complex.ofReal_tsum]
  congr 1
  exact tsum_sq_eq_toReal fun i => sqrtOp S (stdHilbertBasis H i)

/-! ## The contraction–trace bound `∑ᵢ ‖⟪W eᵢ, S eᵢ⟫‖ ≤ ‖S‖₁` (feeds the triangle inequality) -/

/-- The twisted family `(|S|^{1/2} ∘ (polarIsometry S)⋆ ∘ W) eᵢ` pairs back to `⟪W eᵢ, S eᵢ⟫`. -/
private lemma inner_comp_twist (W S : H →L[ℂ] H) (i : (exists_hilbertBasis ℂ H).choose) :
    ⟪(sqrtOp (absOp S) ∘L (W† ∘L polarIsometry S)†) (stdHilbertBasis H i),
        sqrtOp (absOp S) (stdHilbertBasis H i)⟫_ℂ
      = ⟪W (stdHilbertBasis H i), S (stdHilbertBasis H i)⟫_ℂ := by
  rw [show (sqrtOp (absOp S) ∘L (W† ∘L polarIsometry S)†) (stdHilbertBasis H i)
      = (sqrtOp (absOp S) ∘L (polarIsometry S)†) (W (stdHilbertBasis H i)) by
    rw [adjoint_comp, adjoint_adjoint]; rfl]
  exact trace_summand_polar S (W (stdHilbertBasis H i)) (stdHilbertBasis H i)

/-- Square-summability of the twisted family, for any bounded `W` and trace-class `S`. -/
private lemma summable_inner_comp_family {W S : H →L[ℂ] H} (hS : IsTraceClass S) :
    Summable (fun i =>
      ‖(sqrtOp (absOp S) ∘L (W† ∘L polarIsometry S)†) (stdHilbertBasis H i)‖ ^ 2) :=
  (sqrtOp_comp_adjoint_bound S (W† ∘L polarIsometry S) (c := ‖W‖₊)
    (fun x => by
      rw [ContinuousLinearMap.comp_apply]
      have hR : ‖(W†) (polarIsometry S (sqrtOp (absOp S) x))‖ ≤ ‖W‖ * ‖sqrtOp (absOp S) x‖ :=
        calc ‖(W†) (polarIsometry S (sqrtOp (absOp S) x))‖
            ≤ ‖(W†)‖ * ‖polarIsometry S (sqrtOp (absOp S) x)‖ := (W†).le_opNorm _
          _ = ‖W‖ * ‖polarIsometry S (sqrtOp (absOp S) x)‖ := by
              rw [ContinuousLinearMap.adjoint.norm_map]
          _ ≤ ‖W‖ * ‖sqrtOp (absOp S) x‖ := by gcongr; exact norm_polarIsometry_apply_le S _
      exact_mod_cast hR) hS).1

/-- Summability of `i ↦ ‖⟪W eᵢ, S eᵢ⟫‖` for trace-class `S` (any bounded `W`). -/
theorem summable_norm_inner_comp (W : H →L[ℂ] H) {S : H →L[ℂ] H} (hS : IsTraceClass S) :
    Summable (fun i => ‖⟪W (stdHilbertBasis H i), S (stdHilbertBasis H i)⟫_ℂ‖) :=
  (summable_norm_inner (summable_inner_comp_family (W := W) hS) (summable_sqrtOp_absOp_sq hS)).congr
    (fun i => congrArg (‖·‖) (inner_comp_twist W S i))

/-- **The contraction–trace bound.** For a contraction `W` (`‖W‖ ≤ 1`) and trace-class `S`,
`∑ᵢ ‖⟪W eᵢ, S eᵢ⟫‖ ≤ ‖S‖₁`.  The single-fixed-`W` estimate behind the triangle inequality. -/
theorem tsum_norm_inner_comp_le {W S : H →L[ℂ] H} (hW : ‖W‖ ≤ 1) (hS : IsTraceClass S) :
    ∑' i, ‖⟪W (stdHilbertBasis H i), S (stdHilbertBasis H i)⟫_ℂ‖ ≤ traceNorm S := by
  have hWadj : ∀ z, ‖(W†) z‖ ≤ ‖z‖ := fun z =>
    calc ‖(W†) z‖ ≤ ‖(W†)‖ * ‖z‖ := (W†).le_opNorm _
      _ ≤ 1 * ‖z‖ := by
          gcongr
          rw [ContinuousLinearMap.adjoint.norm_map]; exact hW
      _ = ‖z‖ := one_mul _
  obtain ⟨hp_sum, hp_le⟩ := sqrtOp_comp_adjoint_bound S (W† ∘L polarIsometry S) (c := 1)
    (fun x => by
      rw [ContinuousLinearMap.comp_apply, one_mul]
      calc ‖(W†) (polarIsometry S (sqrtOp (absOp S) x))‖₊
          ≤ ‖polarIsometry S (sqrtOp (absOp S) x)‖₊ := by exact_mod_cast hWadj _
        _ ≤ ‖sqrtOp (absOp S) x‖₊ := by exact_mod_cast norm_polarIsometry_apply_le S _) hS
  have hq_tsum := tsum_sqrtOp_absOp_sq S
  have hp_le' : ∑' i, ‖(sqrtOp (absOp S) ∘L (W† ∘L polarIsometry S)†) (stdHilbertBasis H i)‖ ^ 2
      ≤ traceNorm S := by simpa using hp_le
  calc ∑' i, ‖⟪W (stdHilbertBasis H i), S (stdHilbertBasis H i)⟫_ℂ‖
      = ∑' i, ‖⟪(sqrtOp (absOp S) ∘L (W† ∘L polarIsometry S)†) (stdHilbertBasis H i),
          sqrtOp (absOp S) (stdHilbertBasis H i)⟫_ℂ‖ :=
        tsum_congr fun i => (congrArg (‖·‖) (inner_comp_twist W S i)).symm
    _ ≤ (∑' i, ‖(sqrtOp (absOp S) ∘L (W† ∘L polarIsometry S)†) (stdHilbertBasis H i)‖ ^ 2
          + ∑' i, ‖sqrtOp (absOp S) (stdHilbertBasis H i)‖ ^ 2) / 2 :=
        tsum_norm_inner_le hp_sum (summable_sqrtOp_absOp_sq hS)
    _ ≤ traceNorm S := by rw [hq_tsum]; linarith

end Spectra.QuantumMechanics.Channels
