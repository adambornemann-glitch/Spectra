/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.YosidaHille.Approximation.Commutation
import Spectra.YosidaHille.Approximation.Symmetry
/-!
# The Exponential Map and Stone's lemma (Converse)

This file constructs the exponential `exp(itA)` of a self-adjoint operator `A`
as the limit of Yosida approximants, and proves it forms a strongly continuous
one-parameter unitary group whose generator is `iA`.

This completes the converse direction of Stone's lemma: every self-adjoint
operator generates a strongly continuous unitary group.

## Main definitions

* `exponential`: The unitary group `exp(itA)` defined as the limit of `exp(it·Aₙˢʸᵐ)`

## Main statements

* `exponential_unitary` — `exp(itA)` preserves inner products.
* `exponential_group_law` — `exp(i(s+t)A) = exp(isA) ∘ exp(itA)`.
* `exponential_identity` — `exp(i·0·A) = I`.
* `exponential_strong_continuous` — `t ↦ exp(itA)ψ` is continuous.
* `exponential_sub_eq_integral` — the Duhamel integral identity for `exp(itA)`.
* `exponential_generator_eq` / `exponential_generator_eq'` — the generator of `exp(itA)` is `iA`.

## References

* [Kato, *Perturbation Theory*][kato1995], Section IX.1
* [Reed-Simon, *Methods of Modern Mathematical Physics I*][reed1980], lemma VIII.7

-/
open Complex Filter Topology InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.YosidaHille.Approximation

/-! ### Definition of the exponential -/

variable {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
  (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
  (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)

/-- The exponential `exp(itA)ψ` as a bare vector: the limit of the Yosida approximant evolutions. -/
private noncomputable def exponentialFun
    (_hdense : Dense (A.domain : Set H)) (t : ℝ) (ψ : H) : H :=
  limUnder atTop (fun n => expBounded (I • yosidaApproxSym hsym hplus hminus n) t ψ)

/-- The Yosida approximant evolutions `exp(it·Aₙˢʸᵐ)ψ` converge to `exponentialFun`. -/
lemma exponentialFun_tendsto
    (hdense : Dense (A.domain : Set H)) (t : ℝ) (ψ : H) :
    Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym hsym hplus hminus n) t ψ) atTop
      (𝓝 (exponentialFun hsym hplus hminus hdense t ψ)) :=
  tendsto_nhds_limUnder
    (cauchySeq_tendsto_of_complete
      (expBounded_yosidaApproxSym_cauchy_intrinsic hsym hplus hminus hdense t ψ))

/-- `exponentialFun` is additive in `ψ`. -/
private lemma exponentialFun_add
    (h_dense : Dense (A.domain : Set H)) (t : ℝ) (ψ₁ ψ₂ : H) :
    exponentialFun hsym hplus hminus h_dense t (ψ₁ + ψ₂)
      = exponentialFun hsym hplus hminus h_dense t ψ₁
        + exponentialFun hsym hplus hminus h_dense t ψ₂ := by
  have h₁  := exponentialFun_tendsto hsym hplus hminus h_dense t ψ₁
  have h₂  := exponentialFun_tendsto hsym hplus hminus h_dense t ψ₂
  have h₁₂ := exponentialFun_tendsto hsym hplus hminus h_dense t (ψ₁ + ψ₂)
  have hadd : (fun n : ℕ+ => expBounded (I • yosidaApproxSym hsym hplus hminus n) t (ψ₁ + ψ₂))
      = (fun n : ℕ+ => expBounded (I • yosidaApproxSym hsym hplus hminus n) t ψ₁
                     + expBounded (I • yosidaApproxSym hsym hplus hminus n) t ψ₂) :=
    funext fun n => map_add _ ψ₁ ψ₂
  rw [hadd] at h₁₂
  exact tendsto_nhds_unique h₁₂ (h₁.add h₂)

/-- `exponentialFun` is `ℂ`-homogeneous in `ψ`. -/
private lemma exponentialFun_smul
    (h_dense : Dense (A.domain : Set H)) (t : ℝ) (c : ℂ) (ψ : H) :
    exponentialFun hsym hplus hminus h_dense t (c • ψ)
      = c • exponentialFun hsym hplus hminus h_dense t ψ := by
  have h  := exponentialFun_tendsto hsym hplus hminus h_dense t ψ
  have hc := exponentialFun_tendsto hsym hplus hminus h_dense t (c • ψ)
  have hsmul : (fun n : ℕ+ => expBounded (I • yosidaApproxSym hsym hplus hminus n) t (c • ψ))
      = (fun n : ℕ+ => c • expBounded (I • yosidaApproxSym hsym hplus hminus n) t ψ) :=
    funext fun n => map_smul _ c ψ
  rw [hsmul] at hc
  exact tendsto_nhds_unique hc (tendsto_const_nhds.smul h)

/-- `exponentialFun` is norm-nonexpansive: `‖exp(itA)ψ‖ ≤ ‖ψ‖`. -/
private lemma exponentialFun_norm_le
    (h_dense : Dense (A.domain : Set H)) (t : ℝ) (ψ : H) :
    ‖exponentialFun hsym hplus hminus h_dense t ψ‖ ≤ 1 * ‖ψ‖ := by
  rw [one_mul]
  have h := exponentialFun_tendsto hsym hplus hminus h_dense t ψ
  have h_norm : ∀ n : ℕ+, ‖expBounded (I • yosidaApproxSym hsym hplus hminus n) t ψ‖ = ‖ψ‖ := by
    intro n
    have h_sa : ContinuousLinearMap.adjoint (yosidaApproxSym hsym hplus hminus n)
        = yosidaApproxSym hsym hplus hminus n :=
      yosidaApproxSym_selfAdjoint hsym hplus hminus n
    have h_skew : ContinuousLinearMap.adjoint (I • yosidaApproxSym hsym hplus hminus n)
        = -(I • yosidaApproxSym hsym hplus hminus n) :=
      smul_I_skewSelfAdjoint (A := yosidaApproxSym hsym hplus hminus n) h_sa
    exact Unitary.norm_map
      ⟨_, expBounded_mem_unitary (I • yosidaApproxSym hsym hplus hminus n) h_skew t⟩ ψ
  have h_tendsto_norm :
      Tendsto (fun n : ℕ+ => ‖expBounded (I • yosidaApproxSym hsym hplus hminus n) t ψ‖)
        atTop (𝓝 ‖exponentialFun hsym hplus hminus h_dense t ψ‖) := h.norm
  simp_rw [h_norm] at h_tendsto_norm
  exact le_of_eq (tendsto_nhds_unique h_tendsto_norm tendsto_const_nhds)

/-- The exponential `exp(itA)` as a bounded operator: the strong limit of `exp(it·Aₙˢʸᵐ)`. -/
noncomputable def exponential
    (hdense : Dense (A.domain : Set H)) (t : ℝ) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := exponentialFun hsym hplus hminus hdense t
      map_add' := exponentialFun_add hsym hplus hminus hdense t
      map_smul' := fun c ψ => by simpa using exponentialFun_smul hsym hplus hminus hdense t c ψ }
    1
    (exponentialFun_norm_le hsym hplus hminus hdense t)

/-! ### Unitarity -/

/-- `exp(itA)` preserves the inner product. -/
lemma exponential_unitary
    (h_dense : Dense (A.domain : Set H))
    (t : ℝ) (ψ φ : H) :
    ⟪exponential hsym hplus hminus h_dense t ψ,
     exponential hsym hplus hminus h_dense t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ := by
  have h_conv_ψ : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym hsym hplus hminus n) t ψ)
                          atTop (𝓝 (exponential hsym hplus hminus h_dense t ψ)) :=
    exponentialFun_tendsto hsym hplus hminus h_dense t ψ
  have h_conv_φ : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym hsym hplus hminus n) t φ)
                          atTop (𝓝 (exponential hsym hplus hminus h_dense t φ)) :=
    exponentialFun_tendsto hsym hplus hminus h_dense t φ
  have h_approx_unitary : ∀ n : ℕ+,
      ⟪expBounded (I • yosidaApproxSym hsym hplus hminus n) t ψ,
       expBounded (I • yosidaApproxSym hsym hplus hminus n) t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ :=
    fun n => expBounded_yosidaApproxSym_unitary hsym hplus hminus n t ψ φ
  have h_inner_cont : Tendsto (fun n : ℕ+ =>
      ⟪expBounded (I • yosidaApproxSym hsym hplus hminus n) t ψ,
       expBounded (I • yosidaApproxSym hsym hplus hminus n) t φ⟫_ℂ)
      atTop (𝓝 ⟪exponential hsym hplus hminus h_dense t ψ,
                exponential hsym hplus hminus h_dense t φ⟫_ℂ) :=
    Filter.Tendsto.inner h_conv_ψ h_conv_φ
  have h_const : Tendsto (fun _n : ℕ+ => ⟪ψ, φ⟫_ℂ) atTop (𝓝 ⟪ψ, φ⟫_ℂ) := tendsto_const_nhds
  exact tendsto_nhds_unique h_inner_cont (h_const.congr (fun n => (h_approx_unitary n).symm))

/-! ### Group law -/

/-- The group law: `exp(i(s+t)A) = exp(isA) ∘ exp(itA)`. -/
lemma exponential_group_law
    (h_dense : Dense (A.domain : Set H))
    (s t : ℝ) (ψ : H) :
    exponential hsym hplus hminus h_dense (s + t) ψ =
    exponential hsym hplus hminus h_dense s (exponential hsym hplus hminus h_dense t ψ) := by
  have h_approx_group : ∀ n : ℕ+,
      expBounded (I • yosidaApproxSym hsym hplus hminus n) (s + t) ψ =
      expBounded (I • yosidaApproxSym hsym hplus hminus n) s
        (expBounded (I • yosidaApproxSym hsym hplus hminus n) t ψ) := by
    intro n
    rw [expBounded_add_smul]
    rfl
  have h_conv_lhs : Tendsto
      (fun n : ℕ+ => expBounded (I • yosidaApproxSym hsym hplus hminus n) (s + t) ψ)
      atTop (𝓝 (exponential hsym hplus hminus h_dense (s + t) ψ)) :=
   exponentialFun_tendsto hsym hplus hminus h_dense (s + t) ψ
  have h_conv_rhs : Tendsto (fun n : ℕ+ =>
      expBounded (I • yosidaApproxSym hsym hplus hminus n) s
        (expBounded (I • yosidaApproxSym hsym hplus hminus n) t ψ))
      atTop (𝓝 (exponential hsym hplus hminus h_dense s
                (exponential hsym hplus hminus h_dense t ψ))) := by
    have h_inner := exponentialFun_tendsto hsym hplus hminus h_dense t ψ
    have h_outer : ∀ χ : H, Tendsto
        (fun n : ℕ+ => expBounded (I • yosidaApproxSym hsym hplus hminus n) s χ)
        atTop (𝓝 (exponential hsym hplus hminus h_dense s χ)) :=
      fun χ => exponentialFun_tendsto hsym hplus hminus h_dense s χ
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hε2 : ε / 2 > 0 := by linarith
    rw [Metric.tendsto_atTop] at h_inner
    obtain ⟨N₁, hN₁⟩ := h_inner (ε / 2) hε2
    have h_outer_limit := h_outer (exponential hsym hplus hminus h_dense t ψ)
    rw [Metric.tendsto_atTop] at h_outer_limit
    obtain ⟨N₂, hN₂⟩ := h_outer_limit (ε / 2) hε2
    use max N₁ N₂
    intro n hn
    rw [dist_eq_norm]
    calc ‖expBounded (I • yosidaApproxSym hsym hplus hminus n) s
            (expBounded (I • yosidaApproxSym hsym hplus hminus n) t ψ) -
          exponential hsym hplus hminus h_dense s (exponential hsym hplus hminus h_dense t ψ)‖
        = ‖(expBounded (I • yosidaApproxSym hsym hplus hminus n) s
              (expBounded (I • yosidaApproxSym hsym hplus hminus n) t ψ) -
            expBounded (I • yosidaApproxSym hsym hplus hminus n) s
              (exponential hsym hplus hminus h_dense t ψ)) +
           (expBounded (I • yosidaApproxSym hsym hplus hminus n) s
              (exponential hsym hplus hminus h_dense t ψ) -
            exponential hsym hplus hminus h_dense s (exponential hsym hplus hminus h_dense t ψ))‖
            := by
              congr 1; abel
      _ ≤ ‖expBounded (I • yosidaApproxSym hsym hplus hminus n) s
              (expBounded (I • yosidaApproxSym hsym hplus hminus n) t ψ) -
            expBounded (I • yosidaApproxSym hsym hplus hminus n) s
              (exponential hsym hplus hminus h_dense t ψ)‖ +
          ‖expBounded (I • yosidaApproxSym hsym hplus hminus n) s
              (exponential hsym hplus hminus h_dense t ψ) -
            exponential hsym hplus hminus h_dense s (exponential hsym hplus hminus h_dense t ψ)‖ :=
          norm_add_le _ _
      _ = ‖expBounded (I • yosidaApproxSym hsym hplus hminus n) s
              (expBounded (I • yosidaApproxSym hsym hplus hminus n) t ψ
                - exponential hsym hplus hminus h_dense t ψ)‖ +
          ‖expBounded (I • yosidaApproxSym hsym hplus hminus n) s
              (exponential hsym hplus hminus h_dense t ψ) -
            exponential hsym hplus hminus h_dense s (exponential hsym hplus hminus h_dense t ψ)‖
            := by
          rw [← map_sub]
      _ = ‖expBounded (I • yosidaApproxSym hsym hplus hminus n) t ψ
              - exponential hsym hplus hminus h_dense t ψ‖ +
          ‖expBounded (I • yosidaApproxSym hsym hplus hminus n) s
              (exponential hsym hplus hminus h_dense t ψ) -
            exponential hsym hplus hminus h_dense s (exponential hsym hplus hminus h_dense t ψ)‖
            := by
          rw [expBounded_yosidaApproxSym_isometry hsym hplus hminus n s _]
      _ < ε / 2 + ε / 2 := by
          apply add_lt_add
          · rw [← dist_eq_norm]; exact hN₁ n (le_of_max_le_left hn)
          · rw [← dist_eq_norm]; exact hN₂ n (le_of_max_le_right hn)
      _ = ε := by ring
  exact tendsto_nhds_unique h_conv_lhs (h_conv_rhs.congr (fun n => (h_approx_group n).symm))

/-! ### Identity -/
/-- At `t = 0`, `exp(itA)` is the identity. -/
lemma exponential_identity
    (h_dense : Dense (A.domain : Set H))
    (ψ : H) :
    exponential hsym hplus hminus h_dense 0 ψ = ψ := by
  have h_approx_zero : ∀ n : ℕ+, expBounded (I • yosidaApproxSym hsym hplus hminus n) 0 ψ = ψ :=
    fun n => expBounded_at_zero _ ψ
  have h_const : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym hsym hplus hminus n) 0 ψ)
                         atTop (𝓝 ψ) := by
    simp_rw [h_approx_zero]
    exact tendsto_const_nhds
  have h_conv : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym hsym hplus hminus n) 0 ψ)
                        atTop (𝓝 (exponential hsym hplus hminus h_dense 0 ψ)) :=
    exponentialFun_tendsto hsym hplus hminus h_dense 0 ψ
  exact tendsto_nhds_unique h_conv h_const

/-! ### Strong continuity -/

/-- Strong continuity: `t ↦ exp(itA)ψ` is continuous. -/
lemma exponential_strong_continuous
    (h_dense : Dense (A.domain : Set H))
    (ψ : H) :
    Continuous (fun t : ℝ => exponential hsym hplus hminus h_dense t ψ) := by
  -- continuity on the domain, intrinsically from the pairwise estimate (no group)
  have h_cont_domain : ∀ (φ : H), φ ∈ A.domain →
      Continuous (fun t : ℝ => exponential hsym hplus hminus h_dense t φ) := by
    intro φ hφ
    obtain ⟨L, hL⟩ : ∃ L : H,
        Tendsto (fun n : ℕ+ => yosidaApproxSym hsym hplus hminus n φ) atTop (𝓝 L) :=
      ⟨_, yosidaApproxSym_tendsto_on_domain hsym hplus hminus h_dense φ hφ⟩
    have hcont_n : ∀ n : ℕ+,
        Continuous (fun s : ℝ => expBounded (I • yosidaApproxSym hsym hplus hminus n) s φ) := by
      intro n
      have hc : Continuous (fun s : ℝ => expBounded (I • yosidaApproxSym hsym hplus hminus n) s) :=
        Differentiable.continuous fun s =>
          (expBounded_hasDerivAt (I • yosidaApproxSym hsym hplus hminus n) s).differentiableAt
      exact hc.clm_apply continuous_const
    have hbound : ∀ (n : ℕ+) (s : ℝ),
        ‖exponential hsym hplus hminus h_dense s φ
          - expBounded (I • yosidaApproxSym hsym hplus hminus n) s φ‖
        ≤ |s| * ‖L - yosidaApproxSym hsym hplus hminus n φ‖ := by
      intro n s
      have hconv_m : Tendsto
          (fun m : ℕ+ => expBounded (I • yosidaApproxSym hsym hplus hminus m) s φ)
          atTop (𝓝 (exponential hsym hplus hminus h_dense s φ)) :=
        exponentialFun_tendsto hsym hplus hminus h_dense s φ
      have hpair_m : ∀ m : ℕ+,
          ‖expBounded (I • yosidaApproxSym hsym hplus hminus m) s φ
            - expBounded (I • yosidaApproxSym hsym hplus hminus n) s φ‖
          ≤ |s| * ‖yosidaApproxSym hsym hplus hminus m φ
                    - yosidaApproxSym hsym hplus hminus n φ‖ := by
        intro m
        have hcomm : Commute (I • yosidaApproxSym hsym hplus hminus m)
            (I • yosidaApproxSym hsym hplus hminus n) :=
          ((yosidaApproxSym_commute hsym hplus hminus m n).smul_left I).smul_right I
        have h := norm_expBounded_pairwise_le
          (I • yosidaApproxSym hsym hplus hminus m) (I • yosidaApproxSym hsym hplus hminus n)
          hcomm (I_smul_yosidaApproxSym_skewAdjoint hsym hplus hminus m)
          (I_smul_yosidaApproxSym_skewAdjoint hsym hplus hminus n) s φ
        calc ‖expBounded (I • yosidaApproxSym hsym hplus hminus m) s φ
                - expBounded (I • yosidaApproxSym hsym hplus hminus n) s φ‖
            ≤ |s| * ‖(I • yosidaApproxSym hsym hplus hminus m
                      - I • yosidaApproxSym hsym hplus hminus n) φ‖ := h
          _ = |s| * ‖yosidaApproxSym hsym hplus hminus m φ
                      - yosidaApproxSym hsym hplus hminus n φ‖ := by
              rw [← smul_sub, ContinuousLinearMap.smul_apply, norm_smul, Complex.norm_I,
                  one_mul, ContinuousLinearMap.sub_apply]
      have hlhs : Tendsto
          (fun m : ℕ+ => ‖expBounded (I • yosidaApproxSym hsym hplus hminus m) s φ
            - expBounded (I • yosidaApproxSym hsym hplus hminus n) s φ‖)
          atTop (𝓝 ‖exponential hsym hplus hminus h_dense s φ
            - expBounded (I • yosidaApproxSym hsym hplus hminus n) s φ‖) :=
        (hconv_m.sub tendsto_const_nhds).norm
      have hrhs : Tendsto
          (fun m : ℕ+ => |s| * ‖yosidaApproxSym hsym hplus hminus m φ
            - yosidaApproxSym hsym hplus hminus n φ‖)
          atTop (𝓝 (|s| * ‖L - yosidaApproxSym hsym hplus hminus n φ‖)) :=
        ((hL.sub tendsto_const_nhds).norm).const_mul |s|
      exact le_of_tendsto_of_tendsto' hlhs hrhs hpair_m
    have hbasis : Tendsto (fun n : ℕ+ => ‖L - yosidaApproxSym hsym hplus hminus n φ‖)
        atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ+ => L - yosidaApproxSym hsym hplus hminus n φ)
          atTop (𝓝 0) := by simpa using hL.const_sub L
      simpa using h0.norm
    rw [Metric.continuous_iff]
    intro t₀ ε hε
    have hε3 : (0:ℝ) < ε / 3 := by linarith
    have htail : Tendsto (fun n : ℕ+ => (|t₀| + 1) * ‖L - yosidaApproxSym hsym hplus hminus n φ‖)
        atTop (𝓝 0) := by simpa using hbasis.const_mul (|t₀| + 1)
    obtain ⟨n, hn⟩ := (Metric.tendsto_atTop.mp htail) (ε / 3) hε3
    have hn0 : (|t₀| + 1) * ‖L - yosidaApproxSym hsym hplus hminus n φ‖ < ε / 3 := by
      have hnn : (0:ℝ) ≤ (|t₀| + 1) * ‖L - yosidaApproxSym hsym hplus hminus n φ‖ := by positivity
      have hd := hn n le_rfl
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hd
    have hcn := hcont_n n
    rw [Metric.continuous_iff] at hcn
    obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := hcn t₀ (ε / 3) hε3
    refine ⟨min δ₀ 1, lt_min hδ₀_pos one_pos, fun t ht => ?_⟩
    have htδ₀ : dist t t₀ < δ₀ := lt_of_lt_of_le ht (min_le_left _ _)
    have ht1  : dist t t₀ < 1  := lt_of_lt_of_le ht (min_le_right _ _)
    have htT : |t| ≤ |t₀| + 1 := by
      rw [Real.dist_eq] at ht1
      have := abs_sub_abs_le_abs_sub t t₀
      linarith
    rw [dist_eq_norm]
    calc ‖exponential hsym hplus hminus h_dense t φ
            - exponential hsym hplus hminus h_dense t₀ φ‖
        = ‖(exponential hsym hplus hminus h_dense t φ
              - expBounded (I • yosidaApproxSym hsym hplus hminus n) t φ)
            + (expBounded (I • yosidaApproxSym hsym hplus hminus n) t φ
              - expBounded (I • yosidaApproxSym hsym hplus hminus n) t₀ φ)
            + (expBounded (I • yosidaApproxSym hsym hplus hminus n) t₀ φ
              - exponential hsym hplus hminus h_dense t₀ φ)‖ := by abel_nf
      _ ≤ ‖exponential hsym hplus hminus h_dense t φ
              - expBounded (I • yosidaApproxSym hsym hplus hminus n) t φ‖
          + ‖expBounded (I • yosidaApproxSym hsym hplus hminus n) t φ
              - expBounded (I • yosidaApproxSym hsym hplus hminus n) t₀ φ‖
          + ‖expBounded (I • yosidaApproxSym hsym hplus hminus n) t₀ φ
              - exponential hsym hplus hminus h_dense t₀ φ‖ := by
            apply le_trans (norm_add_le _ _)
            gcongr
            exact norm_add_le _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by
            apply add_lt_add
            · apply add_lt_add
              · calc ‖exponential hsym hplus hminus h_dense t φ
                        - expBounded (I • yosidaApproxSym hsym hplus hminus n) t φ‖
                    ≤ |t| * ‖L - yosidaApproxSym hsym hplus hminus n φ‖ := hbound n t
                  _ ≤ (|t₀| + 1) * ‖L - yosidaApproxSym hsym hplus hminus n φ‖ :=
                      mul_le_mul_of_nonneg_right htT (norm_nonneg _)
                  _ < ε / 3 := hn0
              · rw [← dist_eq_norm]; exact hδ₀ t htδ₀
            · rw [norm_sub_rev]
              calc ‖exponential hsym hplus hminus h_dense t₀ φ
                      - expBounded (I • yosidaApproxSym hsym hplus hminus n) t₀ φ‖
                  ≤ |t₀| * ‖L - yosidaApproxSym hsym hplus hminus n φ‖ := hbound n t₀
                _ ≤ (|t₀| + 1) * ‖L - yosidaApproxSym hsym hplus hminus n φ‖ :=
                    mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
                _ < ε / 3 := hn0
      _ = ε := by ring
  -- ‖exp t χ‖ = ‖χ‖, from unitarity (general, unchanged)
  have h_isometry : ∀ t : ℝ, ∀ (χ : H),
      ‖exponential hsym hplus hminus h_dense t χ‖ = ‖χ‖ := by
    intro t χ
    have h_inner := exponential_unitary hsym hplus hminus h_dense t χ χ
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h_inner
    have h_sq : ‖exponential hsym hplus hminus h_dense t χ‖^2 = ‖χ‖^2 := by
      have h_eq : (‖exponential hsym hplus hminus h_dense t χ‖ : ℂ)^2 = (‖χ‖ : ℂ)^2 := h_inner
      exact_mod_cast h_eq
    rw [← Real.sqrt_sq (norm_nonneg (exponential hsym hplus hminus h_dense t χ)),
        ← Real.sqrt_sq (norm_nonneg χ), h_sq]
  -- general χ: 3ε against a dense domain point (unchanged but prefixed)
  rw [Metric.continuous_iff]
  intro t ε hε
  have hε3 : ε / 3 > 0 := by linarith
  obtain ⟨φ, hφ_mem, hφ_close⟩ := Metric.mem_closure_iff.mp (h_dense ψ) (ε / 3) hε3
  rw [dist_eq_norm] at hφ_close
  have h_cont_φ := h_cont_domain φ hφ_mem
  rw [Metric.continuous_iff] at h_cont_φ
  obtain ⟨δ, hδ_pos, hδ⟩ := h_cont_φ t (ε / 3) hε3
  use δ, hδ_pos
  intro s hs
  rw [dist_eq_norm]
  calc ‖exponential hsym hplus hminus h_dense s ψ - exponential hsym hplus hminus h_dense t ψ‖
      = ‖(exponential hsym hplus hminus h_dense s ψ - exponential hsym hplus hminus h_dense s φ) +
         (exponential hsym hplus hminus h_dense s φ - exponential hsym hplus hminus h_dense t φ) +
         (exponential hsym hplus hminus h_dense t φ - exponential hsym hplus hminus h_dense t ψ)‖
         := by
            abel_nf
    _ ≤ ‖exponential hsym hplus hminus h_dense s ψ - exponential hsym hplus hminus h_dense s φ‖ +
        ‖exponential hsym hplus hminus h_dense s φ - exponential hsym hplus hminus h_dense t φ‖ +
        ‖exponential hsym hplus hminus h_dense t φ - exponential hsym hplus hminus h_dense t ψ‖
        := by
          apply le_trans (norm_add_le _ _)
          gcongr
          exact norm_add_le _ _
    _ = ‖exponential hsym hplus hminus h_dense s (ψ - φ)‖ +
        ‖exponential hsym hplus hminus h_dense s φ - exponential hsym hplus hminus h_dense t φ‖ +
        ‖exponential hsym hplus hminus h_dense t (φ - ψ)‖ := by
          rw [← map_sub (exponential hsym hplus hminus h_dense s),
              ← map_sub (exponential hsym hplus hminus h_dense t)]
    _ = ‖ψ - φ‖ + ‖exponential hsym hplus hminus h_dense s φ
                    - exponential hsym hplus hminus h_dense t φ‖ + ‖φ - ψ‖ := by
          rw [h_isometry s (ψ - φ), h_isometry t (φ - ψ)]
    _ < ε / 3 + ε / 3 + ε / 3 := by
          apply add_lt_add
          · apply add_lt_add
            · exact hφ_close
            · rw [← dist_eq_norm]; exact hδ s hs
          · rw [norm_sub_rev]; exact hφ_close
    _ = ε := by ring

/-- Bounded Duhamel identity for the Yosida approximant:
`e^{itAₙ}φ - φ = ∫₀ᵗ e^{isAₙ}(I·Aₙφ) ds`. -/
lemma expBounded_yosidaApproxSym_duhamel
    (n : ℕ+) (t : ℝ) (φ : H) :
    expBounded (I • yosidaApproxSym hsym hplus hminus n) t φ - φ
      = ∫ s in (0:ℝ)..t,
          expBounded (I • yosidaApproxSym hsym hplus hminus n) s
            (I • yosidaApproxSym hsym hplus hminus n φ) := by
  have hderiv : ∀ s : ℝ, HasDerivAt
      (fun s => expBounded (I • yosidaApproxSym hsym hplus hminus n) s φ)
      (expBounded (I • yosidaApproxSym hsym hplus hminus n) s
        (I • yosidaApproxSym hsym hplus hminus n φ)) s := by
    intro s
    have hbase : HasDerivAt
        (fun s => expBounded (I • yosidaApproxSym hsym hplus hminus n) s φ)
        ((I • yosidaApproxSym hsym hplus hminus n)
          (expBounded (I • yosidaApproxSym hsym hplus hminus n) s φ)) s := by
      simpa [Function.comp_def] using
        ((ContinuousLinearMap.apply ℂ H φ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
          (expBounded_hasDerivAt (I • yosidaApproxSym hsym hplus hminus n) s)
    have hcomm : (I • yosidaApproxSym hsym hplus hminus n)
          (expBounded (I • yosidaApproxSym hsym hplus hminus n) s φ)
        = expBounded (I • yosidaApproxSym hsym hplus hminus n) s
            (I • yosidaApproxSym hsym hplus hminus n φ) := by
      have h := congrArg (fun T : H →L[ℂ] H => T φ)
        (B_commute_expBounded (I • yosidaApproxSym hsym hplus hminus n) s)
      simpa [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply] using h
    rwa [hcomm] at hbase
  have hcont : Continuous (fun s : ℝ =>
      expBounded (I • yosidaApproxSym hsym hplus hminus n) s
        (I • yosidaApproxSym hsym hplus hminus n φ)) := by
    have hc : Continuous (fun s : ℝ => expBounded (I • yosidaApproxSym hsym hplus hminus n) s) :=
      Differentiable.continuous fun s =>
        (expBounded_hasDerivAt (I • yosidaApproxSym hsym hplus hminus n) s).differentiableAt
    exact hc.clm_apply continuous_const
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hderiv s) (hcont.intervalIntegrable 0 t)
  rw [expBounded_at_zero] at h
  exact h.symm

/-- Integral identity for the abstract exponential: `exp(itA)φ - φ = ∫₀ᵗ I·exp(isA)(Aφ) ds`. -/
lemma exponential_sub_eq_integral
    (h_dense : Dense (A.domain : Set H))
    (φ : H) (hφ : φ ∈ A.domain) (t : ℝ) :
    exponential hsym hplus hminus h_dense t φ - φ
      = ∫ s in (0:ℝ)..t, I • exponential hsym hplus hminus h_dense s (A ⟨φ, hφ⟩) := by
  set Aφ := A ⟨φ, hφ⟩ with _hAφ
  have htend : Tendsto (fun n : ℕ+ => yosidaApproxSym hsym hplus hminus n φ) atTop (𝓝 Aφ) :=
    yosidaApproxSym_tendsto_on_domain hsym hplus hminus h_dense φ hφ
  -- each bounded integrand is continuous (for measurability/integrability)
  have hcontGn : ∀ n : ℕ+, Continuous (fun s : ℝ =>
      expBounded (I • yosidaApproxSym hsym hplus hminus n) s
        (I • yosidaApproxSym hsym hplus hminus n φ)) := by
    intro n
    have hc : Continuous (fun s : ℝ => expBounded (I • yosidaApproxSym hsym hplus hminus n) s) :=
      Differentiable.continuous fun s =>
        (expBounded_hasDerivAt (I • yosidaApproxSym hsym hplus hminus n) s).differentiableAt
    exact hc.clm_apply continuous_const
  -- pointwise convergence of the integrand to `I·exp(isA)(Aφ)`
  have hptwise : ∀ s : ℝ, Tendsto (fun n : ℕ+ =>
      expBounded (I • yosidaApproxSym hsym hplus hminus n) s
        (I • yosidaApproxSym hsym hplus hminus n φ))
      atTop (𝓝 (I • exponential hsym hplus hminus h_dense s Aφ)) := by
    intro s
    rw [(map_smul (exponential hsym hplus hminus h_dense s) I Aφ).symm]
    have he : Tendsto (fun n : ℕ+ =>
        expBounded (I • yosidaApproxSym hsym hplus hminus n) s (I • Aφ))
        atTop (𝓝 (exponential hsym hplus hminus h_dense s (I • Aφ))) :=
      exponentialFun_tendsto hsym hplus hminus h_dense s (I • Aφ)
    have hd : Tendsto (fun n : ℕ+ =>
        expBounded (I • yosidaApproxSym hsym hplus hminus n) s
            (I • yosidaApproxSym hsym hplus hminus n φ)
          - expBounded (I • yosidaApproxSym hsym hplus hminus n) s (I • Aφ))
        atTop (𝓝 0) := by
      have hnorm : ∀ n : ℕ+,
          ‖expBounded (I • yosidaApproxSym hsym hplus hminus n) s
              (I • yosidaApproxSym hsym hplus hminus n φ)
            - expBounded (I • yosidaApproxSym hsym hplus hminus n) s (I • Aφ)‖
          = ‖yosidaApproxSym hsym hplus hminus n φ - Aφ‖ := by
        intro n
        rw [← map_sub, ← smul_sub,
            expBounded_yosidaApproxSym_isometry hsym hplus hminus n s _,
            norm_smul, Complex.norm_I, one_mul]
      have hto0 : Tendsto (fun n : ℕ+ => ‖yosidaApproxSym hsym hplus hminus n φ - Aφ‖)
          atTop (𝓝 0) := by
        have h0 : Tendsto (fun n : ℕ+ => yosidaApproxSym hsym hplus hminus n φ - Aφ)
            atTop (𝓝 0) := by simpa using htend.sub_const Aφ
        simpa using h0.norm
      exact squeeze_zero_norm (fun n => le_of_eq (hnorm n)) hto0
    have hcombine := hd.add he
    have hfun : (fun n : ℕ+ =>
        (expBounded (I • yosidaApproxSym hsym hplus hminus n) s
            (I • yosidaApproxSym hsym hplus hminus n φ)
          - expBounded (I • yosidaApproxSym hsym hplus hminus n) s (I • Aφ))
          + expBounded (I • yosidaApproxSym hsym hplus hminus n) s (I • Aφ))
        = (fun n : ℕ+ => expBounded (I • yosidaApproxSym hsym hplus hminus n) s
            (I • yosidaApproxSym hsym hplus hminus n φ)) := by
      funext n; abel
    rw [hfun, zero_add] at hcombine
    exact hcombine
  -- eventual uniform bound ‖e^{isAₙ}(I·Aₙφ)‖ = ‖Aₙφ‖ ≤ ‖Aφ‖+1
  have hev : ∀ᶠ n : ℕ+ in atTop, ∀ s : ℝ,
      ‖expBounded (I • yosidaApproxSym hsym hplus hminus n) s
        (I • yosidaApproxSym hsym hplus hminus n φ)‖ ≤ ‖Aφ‖ + 1 := by
    have hb : ∀ᶠ n : ℕ+ in atTop, ‖yosidaApproxSym hsym hplus hminus n φ‖ ≤ ‖Aφ‖ + 1 :=
      (htend.norm.eventually_lt_const (by linarith)).mono fun n hn => le_of_lt hn
    refine hb.mono fun n hn s => ?_
    rw [expBounded_yosidaApproxSym_isometry hsym hplus hminus n s _, norm_smul,
        Complex.norm_I, one_mul]
    exact hn
  -- the limit under the integral  ⟨the one external dependency⟩
  have hlim : Tendsto (fun n : ℕ+ => ∫ s in (0:ℝ)..t,
      expBounded (I • yosidaApproxSym hsym hplus hminus n) s
        (I • yosidaApproxSym hsym hplus hminus n φ))
      atTop (𝓝 (∫ s in (0:ℝ)..t, I • exponential hsym hplus hminus h_dense s Aφ)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => ‖Aφ‖ + 1) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards with n
      exact (hcontGn n).aestronglyMeasurable
    · filter_upwards [hev] with n hn
      filter_upwards with s
      intro _hs
      exact hn s
    · filter_upwards with s
      intro _hs
      exact hptwise s
  -- assemble: piece 1 + def of exp + uniqueness of limits
  have hbddFTC : ∀ n : ℕ+,
      expBounded (I • yosidaApproxSym hsym hplus hminus n) t φ - φ
        = ∫ s in (0:ℝ)..t, expBounded (I • yosidaApproxSym hsym hplus hminus n) s
            (I • yosidaApproxSym hsym hplus hminus n φ) :=
    fun n => expBounded_yosidaApproxSym_duhamel hsym hplus hminus n t φ
  have hlhs : Tendsto (fun n : ℕ+ =>
      expBounded (I • yosidaApproxSym hsym hplus hminus n) t φ - φ)
      atTop (𝓝 (exponential hsym hplus hminus h_dense t φ - φ)) :=
    (exponentialFun_tendsto hsym hplus hminus h_dense t φ).sub_const φ
  exact tendsto_nhds_unique (hlhs.congr hbddFTC) hlim

/-- Honest generator characterization: `(1/t)(exp(itA)φ - φ) → i·Aφ` as `t → 0`, for `φ ∈ dom A`. -/
lemma exponential_generator_eq
    (h_dense : Dense (A.domain : Set H))
    (φ : H) (hφ : φ ∈ A.domain) :
    Tendsto (fun t : ℝ => (t⁻¹ : ℂ) • (exponential hsym hplus hminus h_dense t φ - φ))
            (𝓝[≠] 0) (𝓝 (I • A ⟨φ, hφ⟩)) := by
  set Aφ := A ⟨φ, hφ⟩ with _hAφ
  -- reduce the complex difference-quotient scalar to the real one the slope produces
  have hreal : (fun t : ℝ => (t⁻¹ : ℂ) • (exponential hsym hplus hminus h_dense t φ - φ))
      = (fun t : ℝ => (t⁻¹ : ℝ) • (exponential hsym hplus hminus h_dense t φ - φ)) := by
    funext t; simp only [← Complex.ofReal_inv, Complex.coe_smul]
  rw [hreal]
  -- the integrand g(s) = I·exp(isA)(Aφ) is continuous, and measurable at 𝓝 0
  have hgcont : Continuous (fun s : ℝ => I • exponential hsym hplus hminus h_dense s Aφ) :=
    (exponential_strong_continuous hsym hplus hminus h_dense Aφ).const_smul I
  have hmeas : StronglyMeasurableAtFilter
      (fun s : ℝ => I • exponential hsym hplus hminus h_dense s Aφ) (𝓝 (0:ℝ)) :=
    ⟨Set.univ, Filter.univ_mem, by
      rw [MeasureTheory.Measure.restrict_univ];
      exact hgcont.aestronglyMeasurable⟩
  -- FTC at the right endpoint, evaluated at 0:  d/dt ∫₀ᵗ g = g 0
  have hFTC : HasDerivAt
      (fun t : ℝ => ∫ s in (0:ℝ)..t, I • exponential hsym hplus hminus h_dense s Aφ)
      ((I : ℂ) • exponential hsym hplus hminus h_dense 0 Aφ) 0 :=
    intervalIntegral.integral_hasDerivAt_right
      (hgcont.intervalIntegrable 0 0) hmeas hgcont.continuousAt
  -- g 0 = I·Aφ
  rw [exponential_identity hsym hplus hminus h_dense Aφ] at hFTC
  -- and ∫₀ᵗ g = exp(itA)φ − φ, so the curve being differentiated is exp(·A)φ − φ
  have hfun : (fun t : ℝ => ∫ s in (0:ℝ)..t, I • exponential hsym hplus hminus h_dense s Aφ)
      = (fun t : ℝ => exponential hsym hplus hminus h_dense t φ - φ) := by
    funext t; exact (exponential_sub_eq_integral hsym hplus hminus h_dense φ hφ t).symm
  rw [hfun] at hFTC
  -- read off the slope
  have hslope := hasDerivAt_iff_tendsto_slope.mp hFTC
  refine hslope.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t _
  rw [slope_def_module, exponential_identity hsym hplus hminus h_dense φ, sub_self,
      sub_zero, sub_zero]

/-- The generator difference-quotient form: `(it)⁻¹(exp(itA)φ - φ) → Aφ`, matching `generator`. -/
lemma exponential_generator_eq'
    (h_dense : Dense (A.domain : Set H))
    (φ : H) (hφ : φ ∈ A.domain) :
    Tendsto (fun t : ℝ => (I * (t : ℂ))⁻¹ • (exponential hsym hplus hminus h_dense t φ - φ))
            (𝓝[≠] 0) (𝓝 (A ⟨φ, hφ⟩)) := by
  have h := (exponential_generator_eq hsym hplus hminus h_dense φ hφ).const_smul (-I)
  rw [show (-I : ℂ) • (I • A ⟨φ, hφ⟩) = A ⟨φ, hφ⟩ by
        rw [smul_smul, neg_mul, Complex.I_mul_I]; simp] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t _
  rw [smul_smul]
  congr 1
  rw [mul_inv, Complex.inv_I]


end Spectra.YosidaHille.Approximation
