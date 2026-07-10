/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Sobolev.WeakDerivative
import Spectra.Spaces.Sobolev.IntegrationByParts
import Spectra.Spaces.Sobolev.MeyersMulti
import Spectra.Spaces.Sobolev.Density
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete
/-!
# The Sobolev embedding H¹(ℝ³) ↪ L⁶(ℝ³)

This file proves the Gagliardo–Nirenberg–Sobolev inequality for the weak-derivative
Sobolev space `MemSobolevH1` of this development:

  `‖f‖_{L⁶} ≤ C · ‖∇f‖_{L²}`   for all `f ∈ H¹(ℝ³)`,

with the critical exponent `2* = 2d/(d−2) = 6` for `d = 3`.

## ⚠️ The statement this file replaces is FALSE

The original `sobolev_embedding_L6` in the monolith claimed

  `∃ C > 0, ∀ f ∈ H¹(ℝ³), ‖f‖_{L²} ≤ C · ‖∇f‖_{L²}`.

No such constant exists. Scaling refutes it: for `0 ≠ f ∈ C_c^∞` and `f_λ(x) := f(x/λ)`,

  `‖f_λ‖_{L²} = λ^{3/2} ‖f‖_{L²}`,   `‖∇f_λ‖_{L²} = λ^{1/2} ‖∇f‖_{L²}`,

so `‖f_λ‖₂ / ‖∇f_λ‖₂ = λ · ‖f‖₂/‖∇f‖₂ → ∞` as `λ → ∞`. The L² norm on the left
must be replaced by the L⁶ norm (the unique exponent allowed by scaling), which is
what we prove here. **Delete the old `sorry`'d statement from the monolith**; this
file claims its name.

The Kato–Rellich argument for the hydrogen atom does *not* need this lemma: relative
boundedness of the Coulomb potential is already supplied by the Hardy inequality
(`hardy_operator_bound` / `coulomb_relative_bound_zero` in `Hardy/Inequality/Basic.lean`),
whose proof is scaling-critical in exactly the right way. The L⁶ embedding proved
here is forward-looking infrastructure for variational and spectral arguments.

## Main results

* `exists_smooth_approx_H1`: public restatement of Meyers–Serrin H¹-density in
  terms of `weakGradient`.
* `opNorm_le_sqrt_sum_sq`: `‖T‖ ≤ (∑ᵢ ‖T eᵢ‖²)^{1/2}` for `T : ℝ³ →L[ℝ] ℂ`.
* `smoothGradNormSq`: `∑ᵢ ‖∂ᵢφ‖²_{L²}` for smooth compactly supported `φ`, the
  shared building block of the next two results.
* `eLpNorm_fderiv_le_sqrt_sum_partialDeriv`: `‖Dφ‖_{L²} ≤ (∑ᵢ ‖∂ᵢφ‖²_{L²})^{1/2}`.
* `sobolev_embedding_L6_smooth`: GNS for smooth compactly supported functions,
  via `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq_inner`.
* `sobolev_embedding_L6`: GNS for all of H¹, by Meyers–Serrin approximation,
  passage to an a.e.-convergent subsequence, and Fatou for `eLpNorm`.
* `memLp_six_of_memSobolevH1`: every H¹ function lies in L⁶.
* `sobolev_embedding_L6_norm`: the same bound for the norm of the `Lp 6` element.

## Proof of the main theorem

Fix `f ∈ H¹` and pick `φₙ ∈ C_c^∞` with `‖f − φₙ‖₂ < 1/(n+1)` and
`‖∂ᵢf − ∂ᵢφₙ‖₂ < 1/(n+1)` (Meyers–Serrin). The smooth GNS inequality bounds
`‖φₙ‖₆` by `C·(∑ᵢ(‖∂ᵢf‖₂ + 1/(n+1))²)^{1/2}`. Since `φₙ → f` in L², a subsequence
converges a.e., so Fatou (`eLpNorm_lim_le_liminf_eLpNorm` at `p = 6`) gives
`‖f‖₆ ≤ liminf ‖φ_{n_k}‖₆ ≤ C·√(gradientNormSq f)`.
-/
open MeasureTheory Filter Topology MeasureTheory.Lp
open scoped Topology NNReal ENNReal ContDiff

namespace Spectra.Sobolev

/-! ### Meyers–Serrin density, restated for the weak gradient -/

/-- **Smooth approximation in H¹.** Every `f ∈ H¹(ℝ³)` is approximated to any
    accuracy `ε > 0` by a smooth compactly supported `φ`, simultaneously in the
    L² norm and in the L² norms of all three first-order derivatives.

    This is `meyers_serrin_approx_multi` (`MeyersMulti.lean`) specialised to the
    canonical weak gradient. -/
theorem exists_smooth_approx_H1 (f : l2R3) (hf : MemSobolevH1 f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (φ : R3 → ℂ) (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ),
      ‖f - (memLp_of_smooth_compactSupport φ hφ hsupp).toLp φ‖ < ε ∧
      ∀ i, ‖weakGradient f hf i - (memLp_partialDeriv φ i hφ hsupp).toLp
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))‖ < ε :=
  meyers_serrin_approx_multi f (weakGradient f hf) (weakGradient_spec f hf) ε hε

/-! ### From the Fréchet derivative to the coordinate partials -/

/-- The operator norm of a continuous linear map `ℝ³ →L[ℝ] ℂ` is bounded by the
    ℓ² norm of its values on the standard basis (Cauchy–Schwarz). -/
lemma opNorm_le_sqrt_sum_sq (T : R3 →L[ℝ] ℂ) :
    ‖T‖ ≤ Real.sqrt (∑ i : Fin 3, ‖T (EuclideanSpace.single i 1)‖ ^ 2) := by
  refine ContinuousLinearMap.opNorm_le_bound T (Real.sqrt_nonneg _) fun v => ?_
  -- Expand `v` in the standard orthonormal basis.
  have hv : ∑ i : Fin 3, v i • (EuclideanSpace.single i 1 : R3) = v := by
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]
      using (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  -- Triangle inequality on the expansion.
  have hexp : ‖T v‖ ≤ ∑ i : Fin 3, |v i| * ‖T (EuclideanSpace.single i 1)‖ := by
    conv_lhs => rw [← hv]
    rw [map_sum]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, norm_smul, Real.norm_eq_abs]
  -- Cauchy–Schwarz on the finite sum.
  have hCS : ∑ i : Fin 3, |v i| * ‖T (EuclideanSpace.single i 1)‖ ≤
      Real.sqrt ((∑ i : Fin 3, |v i| ^ 2) *
        ∑ i : Fin 3, ‖T (EuclideanSpace.single i 1)‖ ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => |v i|) (fun i => ‖T (EuclideanSpace.single i 1)‖)
    have hnn : (0:ℝ) ≤ ∑ i : Fin 3, |v i| * ‖T (EuclideanSpace.single i 1)‖ :=
      Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)
    calc ∑ i : Fin 3, |v i| * ‖T (EuclideanSpace.single i 1)‖
        = Real.sqrt ((∑ i : Fin 3, |v i| * ‖T (EuclideanSpace.single i 1)‖) ^ 2) :=
          (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt ((∑ i : Fin 3, |v i| ^ 2) *
            ∑ i : Fin 3, ‖T (EuclideanSpace.single i 1)‖ ^ 2) :=
          Real.sqrt_le_sqrt h
  -- Identify `√(∑ᵢ |vᵢ|²)` with the Euclidean norm of `v`.
  have hnormv : Real.sqrt (∑ i : Fin 3, |v i| ^ 2) = ‖v‖ := by
    rw [EuclideanSpace.norm_eq]
    congr 1
  calc ‖T v‖ ≤ ∑ i : Fin 3, |v i| * ‖T (EuclideanSpace.single i 1)‖ := hexp
    _ ≤ Real.sqrt ((∑ i : Fin 3, |v i| ^ 2) *
          ∑ i : Fin 3, ‖T (EuclideanSpace.single i 1)‖ ^ 2) := hCS
    _ = Real.sqrt (∑ i : Fin 3, ‖T (EuclideanSpace.single i 1)‖ ^ 2) * ‖v‖ := by
        rw [Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _), hnormv, mul_comm]

/-- The ℓ² combination of the L² norms of the three coordinate partial derivatives of a
    smooth compactly supported `φ : ℝ³ → ℂ`: `∑ᵢ ‖∂ᵢφ‖²_{L²}`. This is the smooth-function
    analogue of `gradientNormSq` (`Submodules.lean`), shared between
    `eLpNorm_fderiv_le_sqrt_sum_partialDeriv` and `sobolev_embedding_L6_smooth` so the sum is
    written out only once. -/
noncomputable def smoothGradNormSq (φ : R3 → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hsupp : HasCompactSupport φ) : ℝ :=
  ∑ i : Fin 3, ‖(memLp_partialDeriv φ i hφ hsupp).toLp
    (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))‖ ^ 2

/-- The L² norm of the full Fréchet derivative of a smooth compactly supported
    function is controlled by the ℓ² combination of the L² norms of its three
    coordinate partial derivatives:

      `‖Dφ‖_{L²} ≤ ( ∑ᵢ ‖∂ᵢφ‖²_{L²} )^{1/2}`.

    At `p = 2` this is an identity-level estimate: square both sides and use
    Tonelli to exchange the sum and the integral. -/
lemma eLpNorm_fderiv_le_sqrt_sum_partialDeriv (φ : R3 → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) :
    eLpNorm (fderiv ℝ φ) 2 (volume : Measure R3) ≤
      ENNReal.ofReal (Real.sqrt (smoothGradNormSq φ hφ hsupp)) := by
  set S : ℝ := smoothGradNormSq φ hφ hsupp with hS
  have hS_nonneg : 0 ≤ S :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hp_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  -- `(eLpNorm u 2)² = ∫⁻ ‖u‖ₑ²`, uniformly in the codomain.
  have hpow : ∀ {ε : Type} [NormedAddCommGroup ε] (u : R3 → ε),
      eLpNorm u 2 (volume : Measure R3) ^ (2:ℝ) =
        ∫⁻ x, ‖u x‖ₑ ^ (2:ℝ) ∂(volume : Measure R3) := by
    intro ε _ u
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top]
    simp only [ENNReal.toReal_ofNat]
    rw [← ENNReal.rpow_mul, show (1/2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
  -- `‖w‖ₑ² = ofReal (‖w‖²)`, uniformly in the codomain.
  have henorm : ∀ {ε : Type} [NormedAddCommGroup ε] (w : ε),
      ‖w‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖w‖ ^ 2) := by
    intro ε _ w
    rw [← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_two]
  -- Pointwise: `‖Dφ(x)‖² ≤ ∑ᵢ ‖∂ᵢφ(x)‖²` by `opNorm_le_sqrt_sum_sq`.
  have pointwise : ∀ x : R3, ‖fderiv ℝ φ x‖ₑ ^ (2:ℝ) ≤
      ∑ i : Fin 3, ‖fderiv ℝ φ x (EuclideanSpace.single i 1)‖ₑ ^ (2:ℝ) := by
    intro x
    have hop := opNorm_le_sqrt_sum_sq (fderiv ℝ φ x)
    have hsq' : ‖fderiv ℝ φ x‖ ^ 2 ≤
        ∑ i : Fin 3, ‖fderiv ℝ φ x (EuclideanSpace.single i 1)‖ ^ 2 := by
      have h2 := pow_le_pow_left₀ (norm_nonneg _) hop 2
      rwa [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)] at h2
    calc ‖fderiv ℝ φ x‖ₑ ^ (2:ℝ)
        = ENNReal.ofReal (‖fderiv ℝ φ x‖ ^ 2) := henorm _
      _ ≤ ENNReal.ofReal (∑ i : Fin 3,
            ‖fderiv ℝ φ x (EuclideanSpace.single i 1)‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal hsq'
      _ = ∑ i : Fin 3, ‖fderiv ℝ φ x (EuclideanSpace.single i 1)‖ₑ ^ (2:ℝ) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
          exact Finset.sum_congr rfl fun i _ => (henorm _).symm
  -- Square both sides, exchange sum and integral, and identify Lp norms.
  have hsq : eLpNorm (fderiv ℝ φ) 2 (volume : Measure R3) ^ (2:ℝ) ≤
      ENNReal.ofReal S := by
    calc eLpNorm (fderiv ℝ φ) 2 (volume : Measure R3) ^ (2:ℝ)
        = ∫⁻ x, ‖fderiv ℝ φ x‖ₑ ^ (2:ℝ) ∂(volume : Measure R3) := hpow _
      _ ≤ ∫⁻ x, ∑ i : Fin 3,
            ‖fderiv ℝ φ x (EuclideanSpace.single i 1)‖ₑ ^ (2:ℝ)
              ∂(volume : Measure R3) :=
          lintegral_mono pointwise
      _ = ∑ i : Fin 3, ∫⁻ x,
            ‖fderiv ℝ φ x (EuclideanSpace.single i 1)‖ₑ ^ (2:ℝ)
              ∂(volume : Measure R3) :=
          lintegral_finsetSum _ fun i _ => by
            have hmeas := (contDiff_partialDeriv φ i hφ).continuous.measurable
            exact (hmeas.nnnorm.coe_nnreal_ennreal).pow_const _
      _ = ∑ i : Fin 3, eLpNorm
            (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) 2
            (volume : Measure R3) ^ (2:ℝ) :=
          Finset.sum_congr rfl fun i _ => (hpow _).symm
      _ = ∑ i : Fin 3, ENNReal.ofReal (‖(memLp_partialDeriv φ i hφ hsupp).toLp
            (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))‖ ^ 2) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Lp.norm_toLp, ← Real.rpow_two,
            ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
              (by norm_num : (0:ℝ) ≤ 2),
            ENNReal.ofReal_toReal (memLp_partialDeriv φ i hφ hsupp).eLpNorm_ne_top]
      _ = ENNReal.ofReal S := by
          rw [hS, smoothGradNormSq, ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
  -- Take square roots (rpow at exponent 2 is order-reflecting on ℝ≥0∞).
  have hfinal : eLpNorm (fderiv ℝ φ) 2 (volume : Measure R3) ^ (2:ℝ) ≤
      ENNReal.ofReal (Real.sqrt S) ^ (2:ℝ) := by
    calc eLpNorm (fderiv ℝ φ) 2 (volume : Measure R3) ^ (2:ℝ)
        ≤ ENNReal.ofReal S := hsq
      _ = ENNReal.ofReal (Real.sqrt S ^ 2) := by rw [Real.sq_sqrt hS_nonneg]
      _ = ENNReal.ofReal (Real.sqrt S) ^ (2:ℝ) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _)
            (by norm_num : (0:ℝ) ≤ 2), Real.rpow_two]
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0:ℝ) < 2)).mp hfinal

/-! ### The Gagliardo–Nirenberg–Sobolev inequality for smooth functions -/

/-- **GNS inequality, smooth case.** There is a constant `C > 0` such that for
    every smooth compactly supported `φ : ℝ³ → ℂ`,

      `‖φ‖_{L⁶} ≤ C · ( ∑ᵢ ‖∂ᵢφ‖²_{L²} )^{1/2}`.

    The critical exponent satisfies `1/6 = 1/2 − 1/3`. The heavy lifting is
    Mathlib's `eLpNorm_le_eLpNorm_fderiv_of_eq_inner` (the codomain `ℂ` is a
    Hilbert space over `ℝ`, as required there). -/
theorem sobolev_embedding_L6_smooth :
    ∃ C : ℝ, 0 < C ∧ ∀ (φ : R3 → ℂ) (hφ : ContDiff ℝ ∞ φ)
      (hsupp : HasCompactSupport φ),
      eLpNorm φ 6 (volume : Measure R3) ≤
        ENNReal.ofReal (C * Real.sqrt (smoothGradNormSq φ hφ hsupp)) := by
  haveI : (volume : Measure R3).IsAddHaarMeasure := by
    infer_instance
  have hrank : Module.finrank ℝ R3 = 3 := finrank_euclideanSpace_fin
  -- Mathlib's GNS inequality, packaged with an abstract ℝ≥0 constant.
  obtain ⟨C₀, hkey⟩ : ∃ C₀ : ℝ≥0, ∀ (ψ : R3 → ℂ), ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ →
      eLpNorm ψ 6 (volume : Measure R3) ≤
        (C₀ : ℝ≥0∞) * eLpNorm (fderiv ℝ ψ) 2 (volume : Measure R3) := by
    refine ⟨eLpNormLESNormFDerivOfEqInnerConst (volume : Measure R3) 2,
      fun ψ hψ hs => ?_⟩
    exact_mod_cast eLpNorm_le_eLpNorm_fderiv_of_eq_inner (volume : Measure R3)
      (hψ.of_le (mod_cast le_top)) hs (p := 2) (p' := 6)
      (by norm_num) (by rw [hrank]; norm_num)
      (by rw [hrank]; push_cast; norm_num)
  -- `max (C₀ : ℝ) 1` only pads `C₀` up to guarantee positivity (`0 < C`); it is not
  -- claimed to be the sharp Gagliardo–Nirenberg–Sobolev constant.
  refine ⟨max (C₀ : ℝ) 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    fun φ hφ hsupp => ?_⟩
  set S : ℝ := smoothGradNormSq φ hφ hsupp with hS
  have hgrad := eLpNorm_fderiv_le_sqrt_sum_partialDeriv φ hφ hsupp
  rw [← hS] at hgrad
  calc eLpNorm φ 6 (volume : Measure R3)
      ≤ (C₀ : ℝ≥0∞) * eLpNorm (fderiv ℝ φ) 2 (volume : Measure R3) :=
        hkey φ hφ hsupp
    _ ≤ (C₀ : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt S) := mul_le_mul_right hgrad _
    _ = ENNReal.ofReal ((C₀ : ℝ) * Real.sqrt S) := by
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C₀.coe_nonneg]
    _ ≤ ENNReal.ofReal (max (C₀ : ℝ) 1 * Real.sqrt S) :=
        ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))

/-! ### The Sobolev embedding for H¹ -/

/-- **Sobolev embedding in 3D**: `H¹(ℝ³) ↪ L⁶(ℝ³)`.

    There is a constant `C > 0` such that for every `f ∈ H¹(ℝ³)`,

      `‖f‖_{L⁶} ≤ C · √(gradientNormSq f) = C · ‖∇f‖_{L²}`,

    stated via `eLpNorm` at the critical exponent `2* = 2d/(d−2) = 6` for `d = 3`.
    Note the L⁶ (not L²!) norm on the left: by the scaling `f_λ(x) = f(x/λ)`,
    `6` is the only exponent for which such an inequality can hold on all of ℝ³.

    Proof: approximate `f` in H¹ by `φₙ ∈ C_c^∞` (Meyers–Serrin), apply the
    smooth GNS inequality to each `φₙ`, pass to an a.e.-convergent subsequence
    of the L²-convergent sequence `φₙ → f`, and conclude with Fatou's lemma for
    `eLpNorm` at `p = 6`. -/
theorem sobolev_embedding_L6 :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : l2R3) (hf : MemSobolevH1 f),
      eLpNorm (f : R3 → ℂ) 6 (volume : Measure R3) ≤
        ENNReal.ofReal (C * Real.sqrt (gradientNormSq f hf)) := by
  obtain ⟨C, hC, hsmooth⟩ := sobolev_embedding_L6_smooth
  refine ⟨C, hC, fun f hf => ?_⟩
  -- Meyers–Serrin approximants at accuracy 1/(n+1).
  have hεpos : ∀ n : ℕ, (0:ℝ) < 1 / (n + 1) := fun n => by positivity
  choose φ hφ hsupp hclose hgrad using fun n : ℕ =>
    exists_smooth_approx_H1 f hf (1 / (n + 1)) (hεpos n)
  -- L⁶ bound for each approximant, with the gradient measured at `f`.
  have hL6 : ∀ n : ℕ, eLpNorm (φ n) 6 (volume : Measure R3) ≤
      ENNReal.ofReal (C * Real.sqrt (∑ i : Fin 3,
        (‖weakGradient f hf i‖ + 1 / (n + 1)) ^ 2)) := by
    intro n
    refine (hsmooth (φ n) (hφ n) (hsupp n)).trans (ENNReal.ofReal_le_ofReal ?_)
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hC.le
    refine Finset.sum_le_sum fun i _ => ?_
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    have h2 := norm_sub_norm_le
      ((memLp_partialDeriv (φ n) i (hφ n) (hsupp n)).toLp
        (fun x => fderiv ℝ (φ n) x (EuclideanSpace.single i 1)))
      (weakGradient f hf i)
    rw [norm_sub_rev] at h2
    linarith [hgrad n i]
  -- L² convergence `φₙ → f`.
  have hbound : ∀ n : ℕ,
      eLpNorm ((φ n) - (f : R3 → ℂ)) 2 (volume : Measure R3) ≤
        ENNReal.ofReal (1 / (n + 1)) := by
    intro n
    have he : ((φ n) - (f : R3 → ℂ)) =ᵐ[(volume : Measure R3)]
        ⇑((memLp_of_smooth_compactSupport (φ n) (hφ n) (hsupp n)).toLp (φ n) - f) := by
      filter_upwards [(memLp_of_smooth_compactSupport (φ n) (hφ n) (hsupp n)).coeFn_toLp,
        Lp.coeFn_sub
          ((memLp_of_smooth_compactSupport (φ n) (hφ n) (hsupp n)).toLp (φ n)) f]
        with x hx1 hx2
      simp only [hx1, hx2, Pi.sub_apply]
    rw [eLpNorm_congr_ae he, ← Lp.enorm_def, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_sub_rev]
    exact (hclose n).le
  have hL2_tendsto :
      Tendsto (fun n => eLpNorm ((φ n) - (f : R3 → ℂ)) 2 (volume : Measure R3))
        atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ?_ (fun n => zero_le) hbound
    simpa using ENNReal.tendsto_ofReal
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  -- Pass to an a.e.-convergent subsequence.
  have hmeas : TendstoInMeasure (volume : Measure R3)
      (fun n => (φ n)) atTop ((f : R3 → ℂ)) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (fun n => (hφ n).continuous.aestronglyMeasurable)
      (Lp.aestronglyMeasurable f) hL2_tendsto
  obtain ⟨ns, hns_mono, hns_ae⟩ := hmeas.exists_seq_tendsto_ae
  -- Fatou for `eLpNorm` at p = 6 along the subsequence.
  have hfatou : eLpNorm (f : R3 → ℂ) 6 (volume : Measure R3) ≤
      atTop.liminf (fun k => eLpNorm (φ (ns k)) 6 (volume : Measure R3)) :=
    eLpNorm_lim_le_liminf_eLpNorm
      (fun k => (hφ (ns k)).continuous.aestronglyMeasurable) _ hns_ae
  -- The bounding sequence converges to the gradient bound.
  have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal (C * Real.sqrt (∑ i : Fin 3,
      (‖weakGradient f hf i‖ + 1 / (ns k + 1)) ^ 2))) atTop
      (𝓝 (ENNReal.ofReal (C * Real.sqrt (gradientNormSq f hf)))) := by
    have ht : Tendsto (fun k : ℕ => 1 / ((ns k : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        hns_mono.tendsto_atTop
      simpa [Function.comp_def] using this
    have hsum : Tendsto (fun k : ℕ => ∑ i : Fin 3,
        (‖weakGradient f hf i‖ + 1 / (ns k + 1)) ^ 2) atTop
        (𝓝 (∑ i : Fin 3, ‖weakGradient f hf i‖ ^ 2)) := by
      refine tendsto_finsetSum _ fun i _ => ?_
      have hadd : Tendsto (fun k : ℕ => ‖weakGradient f hf i‖ + 1 / ((ns k : ℝ) + 1))
          atTop (𝓝 (‖weakGradient f hf i‖ + 0)) :=
        tendsto_const_nhds.add ht
      simpa using hadd.pow 2
    have := ENNReal.tendsto_ofReal ((hsum.sqrt).const_mul C)
    simpa [gradientNormSq] using this
  -- Assemble.
  calc eLpNorm (f : R3 → ℂ) 6 (volume : Measure R3)
      ≤ atTop.liminf (fun k => eLpNorm (φ (ns k)) 6 (volume : Measure R3)) :=
        hfatou
    _ ≤ atTop.liminf (fun k => ENNReal.ofReal (C * Real.sqrt (∑ i : Fin 3,
          (‖weakGradient f hf i‖ + 1 / (ns k + 1)) ^ 2))) :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall fun k => hL6 (ns k))
    _ = ENNReal.ofReal (C * Real.sqrt (gradientNormSq f hf)) := hlim.liminf_eq

/-! ### Consequences -/

/-- Every H¹ function on ℝ³ lies in L⁶. -/
theorem memLp_six_of_memSobolevH1 (f : l2R3) (hf : MemSobolevH1 f) :
    MemLp (f : R3 → ℂ) 6 (volume : Measure R3) := by
  obtain ⟨C, _, hbound⟩ := sobolev_embedding_L6
  exact ⟨Lp.aestronglyMeasurable f,
    lt_of_le_of_lt (hbound f hf) ENNReal.ofReal_lt_top⟩

/-- **Sobolev embedding, norm form.** The norm of the `Lp 6` element associated
    to an H¹ function is bounded by `C · √(gradientNormSq f) = C · ‖∇f‖_{L²}`. -/
theorem sobolev_embedding_L6_norm :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : l2R3) (hf : MemSobolevH1 f),
      ‖(memLp_six_of_memSobolevH1 f hf).toLp (f : R3 → ℂ)‖ ≤
        C * Real.sqrt (gradientNormSq f hf) := by
  obtain ⟨C, hC, hbound⟩ := sobolev_embedding_L6
  refine ⟨C, hC, fun f hf => ?_⟩
  rw [Lp.norm_toLp]
  have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound f hf)
  rwa [ENNReal.toReal_ofReal
    (mul_nonneg hC.le (Real.sqrt_nonneg _))] at h1

end Spectra.Sobolev
