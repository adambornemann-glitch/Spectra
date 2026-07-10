/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Finite-rank operators are compact

Toward the gating fact "an integral operator with an `L²(α×β)` kernel is compact" (which Mathlib
lacks entirely), this file proves the foundational, reusable piece: **finite-rank continuous
linear maps are compact operators**, via rank-one maps factoring through the locally compact
field `ℂ`.
-/

noncomputable section

namespace Spectra.CompactOperator

open ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **A rank-one operator `f ↦ φ(f) • g` is compact.** It factors as `(c ↦ c • g) ∘ φ`, and
`c ↦ c • g : ℂ →L F` is compact because its domain `ℂ` is locally compact. -/
theorem isCompactOperator_smulRight (φ : E →L[ℂ] ℂ) (g : F) :
    IsCompactOperator ⇑(φ.smulRight g) := by
  have key : ⇑(φ.smulRight g) = ⇑((1 : ℂ →L[ℂ] ℂ).smulRight g) ∘ ⇑φ := by
    ext f; simp
  rw [key]
  exact (isCompactOperator_of_locallyCompactSpace_rng ((1 : ℂ →L[ℂ] ℂ).smulRight g)).comp_clm φ

/-- **A finite sum of rank-one operators is compact.**  This is the shape produced by an integral
operator with a finite-rank kernel `K(x,y) = Σ_i (φ_i y) · g_i x`. -/
theorem isCompactOperator_sum_smulRight {ι : Type*} (s : Finset ι)
    (φ : ι → E →L[ℂ] ℂ) (g : ι → F) :
    IsCompactOperator ⇑(∑ i ∈ s, (φ i).smulRight (g i)) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]; exact isCompactOperator_zero
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (isCompactOperator_smulRight (φ i) (g i)).add ih

/-! ## Integral operators with an `L²` kernel

The gating fact (`L²(α×β)` kernel ⟹ compact integral operator) is built here in pieces.  First:
the sections `y ↦ K(x,y)` of an `L²` kernel are themselves `L²` for a.e. `x` — the foundation for
the well-definedness of `T_K f (x) = ∫ K(x,y) f(y) dy`. -/

section Kernel

open MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

/-- **The sections of an `L²` kernel are `L²` a.e.**  If `K ∈ L²(μ × ν)`, then for a.e. `x` the
section `y ↦ K(x,y)` lies in `L²(ν)`. -/
theorem memLp_section_ae (K : α × β → ℂ) (hK : MemLp K 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y => K (x, y)) 2 ν := by
  have hsq : Integrable (fun z => ‖K z‖ ^ 2) (μ.prod ν) :=
    (memLp_two_iff_integrable_sq_norm hK.aestronglyMeasurable).1 hK
  filter_upwards [hsq.prod_right_ae, hK.aestronglyMeasurable.prodMk_left] with x hx hxm
  exact (memLp_two_iff_integrable_sq_norm hxm).2 hx

omit [SFinite ν] in
/-- **Per-section Cauchy–Schwarz.**  `‖∫ k·f‖² ≤ (∫‖k‖²)(∫‖f‖²)` for `k, f ∈ L²(ν)`. -/
theorem norm_integral_mul_sq_le (k f : β → ℂ) (hk : MemLp k 2 ν) (hf : MemLp f 2 ν) :
    ‖∫ y, k y * f y ∂ν‖ ^ 2 ≤ (∫ y, ‖k y‖ ^ 2 ∂ν) * (∫ y, ‖f y‖ ^ 2 ∂ν) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  have he2 : ENNReal.ofReal 2 = 2 := by norm_num
  have hMemk : MemLp (fun y => ‖k y‖) (ENNReal.ofReal 2) ν := by rw [he2]; exact hk.norm
  have hMemf : MemLp (fun y => ‖f y‖) (ENNReal.ofReal 2) ν := by rw [he2]; exact hf.norm
  have hhold := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall fun y => norm_nonneg (k y))
    (Filter.Eventually.of_forall fun y => norm_nonneg (f y)) hMemk hMemf
  have hpow : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ 2 := fun x => by
    rw [← Real.rpow_natCast x 2, Nat.cast_ofNat]
  simp_rw [hpow] at hhold
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hhold
  have hbound : ‖∫ y, k y * f y ∂ν‖
      ≤ Real.sqrt (∫ y, ‖k y‖ ^ 2 ∂ν) * Real.sqrt (∫ y, ‖f y‖ ^ 2 ∂ν) :=
    calc ‖∫ y, k y * f y ∂ν‖ ≤ ∫ y, ‖k y * f y‖ ∂ν := norm_integral_le_integral_norm _
      _ = ∫ y, ‖k y‖ * ‖f y‖ ∂ν := by simp_rw [norm_mul]
      _ ≤ _ := hhold
  calc ‖∫ y, k y * f y ∂ν‖ ^ 2
        ≤ (Real.sqrt (∫ y, ‖k y‖ ^ 2 ∂ν) * Real.sqrt (∫ y, ‖f y‖ ^ 2 ∂ν)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = (∫ y, ‖k y‖ ^ 2 ∂ν) * (∫ y, ‖f y‖ ^ 2 ∂ν) := by
        rw [mul_pow, Real.sq_sqrt (integral_nonneg fun y => sq_nonneg _),
          Real.sq_sqrt (integral_nonneg fun y => sq_nonneg _)]

/-- **The integrated `L²` bound** `∫ₓ‖∫ K(x,y)f(y)dy‖² ≤ (∫‖K‖²)(∫‖f‖²)`. -/
theorem integral_norm_integralKernel_sq_le (K : α × β → ℂ) (hK : MemLp K 2 (μ.prod ν))
    (f : β → ℂ) (hf : MemLp f 2 ν) :
    (∫ x, ‖∫ y, K (x, y) * f y ∂ν‖ ^ 2 ∂μ)
      ≤ (∫ z, ‖K z‖ ^ 2 ∂(μ.prod ν)) * (∫ y, ‖f y‖ ^ 2 ∂ν) := by
  set C : ℝ := ∫ y, ‖f y‖ ^ 2 ∂ν with _hC
  have hKsq : Integrable (fun z => ‖K z‖ ^ 2) (μ.prod ν) :=
    (memLp_two_iff_integrable_sq_norm hK.aestronglyMeasurable).1 hK
  -- `x ↦ ∫_y ‖K(x,y)‖²` is integrable (Tonelli).
  have hsecInt : Integrable (fun x => ∫ y, ‖K (x, y)‖ ^ 2 ∂ν) μ := hKsq.integral_prod_left
  -- per-section Cauchy–Schwarz.
  have hpt : ∀ᵐ x ∂μ, ‖∫ y, K (x, y) * f y ∂ν‖ ^ 2 ≤ (∫ y, ‖K (x, y)‖ ^ 2 ∂ν) * C := by
    filter_upwards [memLp_section_ae K hK] with x hx
    exact norm_integral_mul_sq_le (fun y => K (x, y)) f hx hf
  have hdomInt : Integrable (fun x => (∫ y, ‖K (x, y)‖ ^ 2 ∂ν) * C) μ := hsecInt.mul_const C
  -- a.e. measurability of the partial integral.
  have hmeas : AEStronglyMeasurable (fun x => ∫ y, K (x, y) * f y ∂ν) μ :=
    (hK.aestronglyMeasurable.mul (hf.aestronglyMeasurable.comp_snd)).integral_prod_right'
  have hLHSint : Integrable (fun x => ‖∫ y, K (x, y) * f y ∂ν‖ ^ 2) μ := by
    refine Integrable.mono' hdomInt (hmeas.norm.pow 2) ?_
    filter_upwards [hpt] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hx
  calc ∫ x, ‖∫ y, K (x, y) * f y ∂ν‖ ^ 2 ∂μ
      ≤ ∫ x, (∫ y, ‖K (x, y)‖ ^ 2 ∂ν) * C ∂μ := integral_mono_ae hLHSint hdomInt hpt
    _ = (∫ x, ∫ y, ‖K (x, y)‖ ^ 2 ∂ν ∂μ) * C := integral_mul_const C _
    _ = (∫ z, ‖K z‖ ^ 2 ∂(μ.prod ν)) * C := by rw [integral_integral hKsq]

/-- The kernel integral `x ↦ ∫ K(x,y) f(y) dy` is in `L²(μ)`. -/
theorem memLp_kernelIntegral (K : α × β → ℂ) (hK : MemLp K 2 (μ.prod ν))
    (f : β → ℂ) (hf : MemLp f 2 ν) :
    MemLp (fun x => ∫ y, K (x, y) * f y ∂ν) 2 μ := by
  have hmeas : AEStronglyMeasurable (fun x => ∫ y, K (x, y) * f y ∂ν) μ :=
    (hK.aestronglyMeasurable.mul (hf.aestronglyMeasurable.comp_snd)).integral_prod_right'
  refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  have hKsq : Integrable (fun z => ‖K z‖ ^ 2) (μ.prod ν) :=
    (memLp_two_iff_integrable_sq_norm hK.aestronglyMeasurable).1 hK
  have hdomInt : Integrable (fun x => (∫ y, ‖K (x, y)‖ ^ 2 ∂ν) * (∫ y, ‖f y‖ ^ 2 ∂ν)) μ :=
    hKsq.integral_prod_left.mul_const _
  refine Integrable.mono' hdomInt (hmeas.norm.pow 2) ?_
  filter_upwards [memLp_section_ae K hK] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact norm_integral_mul_sq_le (fun y => K (x, y)) f hx hf

omit [SFinite μ] in
/-- The square of the `L²` norm is the integral of the squared norm. -/
theorem L2_norm_sq_eq (f : Lp ℂ 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖(f : α → ℂ) x‖ ^ 2 ∂μ := by
  have hsqint : Integrable (fun x => ‖(f : α → ℂ) x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)
  have hint : Integrable (fun x => (inner ℂ ((f : α → ℂ) x) ((f : α → ℂ) x) : ℂ)) μ :=
    hsqint.ofReal.congr (Filter.Eventually.of_forall fun x => by
      simp only [inner_self_eq_norm_sq_to_K]; push_cast; ring)
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) f, L2.inner_def, ← integral_re hint]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => inner_self_eq_norm_sq (𝕜 := ℂ) _)

/-! ### The integral operator as a continuous linear map -/

variable (K : Lp ℂ 2 (μ.prod ν))

/-- For a.e. `x`, the section times `f` is integrable. -/
theorem integrable_kernel_mul (f : Lp ℂ 2 ν) :
    ∀ᵐ x ∂μ, Integrable (fun y => (K : α × β → ℂ) (x, y) * (f : β → ℂ) y) ν := by
  filter_upwards [memLp_section_ae (K : α × β → ℂ) (Lp.memLp K)] with x hx
  exact hx.integrable_mul (Lp.memLp f)

/-- The integral operator `T_K f (x) = ∫ K(x,y) f(y) dy` as a `ℂ`-linear map `L²(ν) → L²(μ)`. -/
noncomputable def integralOperatorLM : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (memLp_kernelIntegral (K : α × β → ℂ) (Lp.memLp K) (f : β → ℂ) (Lp.memLp f)).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [integrable_kernel_mul K f, integrable_kernel_mul K g] with x hxf hxg
    simp only [Pi.add_apply]
    rw [← integral_add hxf hxg]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add f g] with y hy
    rw [hy, Pi.add_apply]; ring
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [integrable_kernel_mul K f] with x _hxf
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c f] with y hy
    rw [hy, Pi.smul_apply, smul_eq_mul]; ring

/-- The operator-norm bound `‖T_K f‖ ≤ ‖K‖·‖f‖`. -/
theorem integralOperatorLM_norm_le (f : Lp ℂ 2 ν) :
    ‖integralOperatorLM K f‖ ≤ ‖K‖ * ‖f‖ := by
  have hcoe : (integralOperatorLM K f : α → ℂ) =ᵐ[μ]
      fun x => ∫ y, (K : α × β → ℂ) (x, y) * (f : β → ℂ) y ∂ν :=
    MemLp.coeFn_toLp (memLp_kernelIntegral (K : α × β → ℂ) (Lp.memLp K) (f : β → ℂ) (Lp.memLp f))
  have hLHS : ‖integralOperatorLM K f‖ ^ 2
      = ∫ x, ‖∫ y, (K : α × β → ℂ) (x, y) * (f : β → ℂ) y ∂ν‖ ^ 2 ∂μ := by
    rw [L2_norm_sq_eq]
    exact integral_congr_ae (hcoe.mono fun x hx => by simp only [hx])
  have hsq : ‖integralOperatorLM K f‖ ^ 2 ≤ (‖K‖ * ‖f‖) ^ 2 := by
    rw [hLHS, mul_pow, L2_norm_sq_eq K, L2_norm_sq_eq f]
    exact integral_norm_integralKernel_sq_le _ (Lp.memLp K) _ (Lp.memLp f)
  calc ‖integralOperatorLM K f‖ = Real.sqrt (‖integralOperatorLM K f‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((‖K‖ * ‖f‖) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖K‖ * ‖f‖ := Real.sqrt_sq (by positivity)

/-- **The integral operator with an `L²(μ×ν)` kernel**, as a continuous linear map with
`‖T_K‖ ≤ ‖K‖_{L²}`. -/
noncomputable def integralOperator : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous (integralOperatorLM K) ‖K‖ (integralOperatorLM_norm_le K)

theorem norm_integralOperator_le : ‖integralOperator K‖ ≤ ‖K‖ :=
  LinearMap.mkContinuous_norm_le (integralOperatorLM K) (norm_nonneg K)
    (integralOperatorLM_norm_le K)

/-- The representative of `integralOperator K f` is the kernel integral. -/
theorem integralOperator_coeFn (f : Lp ℂ 2 ν) :
    (integralOperator K f : α → ℂ) =ᵐ[μ]
      fun x => ∫ y, (K : α × β → ℂ) (x, y) * (f : β → ℂ) y ∂ν :=
  MemLp.coeFn_toLp (memLp_kernelIntegral (K : α × β → ℂ) (Lp.memLp K) (f : β → ℂ) (Lp.memLp f))

variable {K}

/-- The kernel integral is additive in the kernel (a.e.). -/
theorem integralOperator_add (K₁ K₂ : Lp ℂ 2 (μ.prod ν)) :
    integralOperator (K₁ + K₂) = integralOperator K₁ + integralOperator K₂ := by
  ext f
  have heq : (fun x => ∫ y, (↑(K₁ + K₂) : α × β → ℂ) (x, y) * (f : β → ℂ) y ∂ν) =ᵐ[μ]
      (fun x => ∫ y, (K₁ : α × β → ℂ) (x, y) * (f : β → ℂ) y ∂ν)
        + fun x => ∫ y, (K₂ : α × β → ℂ) (x, y) * (f : β → ℂ) y ∂ν := by
    filter_upwards [integrable_kernel_mul K₁ f, integrable_kernel_mul K₂ f,
      Measure.ae_ae_of_ae_prod (Lp.coeFn_add K₁ K₂)] with x hi1 hi2 hsec
    change (∫ y, (↑(K₁ + K₂) : α × β → ℂ) (x, y) * (f : β → ℂ) y ∂ν)
        = (∫ y, _ ∂ν) + ∫ y, _ ∂ν
    rw [← integral_add hi1 hi2]
    refine integral_congr_ae ?_
    filter_upwards [hsec] with y hy
    rw [show (↑(K₁ + K₂) : α × β → ℂ) (x, y)
        = (K₁ : α × β → ℂ) (x, y) + (K₂ : α × β → ℂ) (x, y) from
      by simpa using hy]; ring
  exact ((integralOperator_coeFn (K₁ + K₂) f).trans (heq.trans
    ((integralOperator_coeFn K₁ f).add (integralOperator_coeFn K₂ f)).symm)).trans
    (Lp.coeFn_add (integralOperator K₁ f) (integralOperator K₂ f)).symm

/-- The kernel integral is `ℂ`-homogeneous in the kernel (a.e.). -/
theorem integralOperator_smul (c : ℂ) (K : Lp ℂ 2 (μ.prod ν)) :
    integralOperator (c • K) = c • integralOperator K := by
  ext f
  have heq : (fun x => ∫ y, (↑(c • K) : α × β → ℂ) (x, y) * (f : β → ℂ) y ∂ν) =ᵐ[μ]
      c • fun x => ∫ y, (K : α × β → ℂ) (x, y) * (f : β → ℂ) y ∂ν := by
    filter_upwards [Measure.ae_ae_of_ae_prod (Lp.coeFn_smul c K)] with x hsec
    change (∫ y, (↑(c • K) : α × β → ℂ) (x, y) * (f : β → ℂ) y ∂ν) = c • ∫ y, _ ∂ν
    rw [smul_eq_mul, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hsec] with y hy
    rw [show (↑(c • K) : α × β → ℂ) (x, y) = c * (K : α × β → ℂ) (x, y) from
      by simpa using hy]; ring
  exact ((integralOperator_coeFn (c • K) f).trans
    (heq.trans ((integralOperator_coeFn K f).symm.const_smul c))).trans
    (Lp.coeFn_smul c (integralOperator K f)).symm

/-- **`K ↦ T_K` as a continuous linear map** into the operator space, with norm `≤ 1`. -/
noncomputable def integralOperatorCLM :
    Lp ℂ 2 (μ.prod ν) →L[ℂ] (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) :=
  LinearMap.mkContinuous
    { toFun := integralOperator
      map_add' := integralOperator_add
      map_smul' := fun c K => integralOperator_smul c K } 1 fun K => by
    rw [one_mul]; exact norm_integralOperator_le K

@[simp] theorem integralOperatorCLM_apply (K : Lp ℂ 2 (μ.prod ν)) :
    integralOperatorCLM K = integralOperator K := rfl

/-! ### Rank-one kernels give compact (rank-one) operators -/

omit [SFinite μ] [SFinite ν] in
/-- A tensor `g(x)·h(y)` of `L²` functions is in `L²(μ×ν)`. -/
theorem memLp_tensor (g : Lp ℂ 2 μ) (h : Lp ℂ 2 ν) :
    MemLp (fun p : α × β => (g : α → ℂ) p.1 * (h : β → ℂ) p.2) 2 (μ.prod ν) := by
  have hmeas : AEStronglyMeasurable
      (fun p : α × β => (g : α → ℂ) p.1 * (h : β → ℂ) p.2) (μ.prod ν) :=
    (Lp.aestronglyMeasurable g).comp_fst.mul (Lp.aestronglyMeasurable h).comp_snd
  refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  have hg : Integrable (fun x => ‖(g : α → ℂ) x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).1 (Lp.memLp g)
  have hh : Integrable (fun y => ‖(h : β → ℂ) y‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable h)).1 (Lp.memLp h)
  refine (hg.mul_prod hh).congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [norm_mul, mul_pow]

/-- **A finite-rectangle-indicator kernel gives a rank-one (compact) operator.** -/
theorem isCompactOperator_integralOperator_indicatorRect
    {A : Set α} {B : Set β} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμA : μ A ≠ ⊤) (hνB : ν B ≠ ⊤) (hAB : (μ.prod ν) (A ×ˢ B) ≠ ⊤) :
    IsCompactOperator (integralOperator (indicatorConstLp 2 (hA.prod hB) hAB (1 : ℂ))) := by
  classical
  have hop : integralOperator (indicatorConstLp 2 (hA.prod hB) hAB 1)
      = (innerSL ℂ (indicatorConstLp 2 hB hνB 1)).smulRight (indicatorConstLp 2 hA hμA 1) := by
    ext f
    -- value of the rank-one functional `innerSL 𝟙_B`.
    have hinner : (innerSL ℂ (indicatorConstLp 2 hB hνB (1 : ℂ))) f
        = ∫ y, B.indicator (fun _ => (1 : ℂ)) y * (f : β → ℂ) y ∂ν := by
      rw [innerSL_apply_apply, L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [indicatorConstLp_coeFn (μ := ν) (hs := hB) (hμs := hνB) (c := (1 : ℂ))]
        with y hy
      rw [RCLike.inner_apply, hy]
      by_cases hyB : y ∈ B
      · simp [Set.indicator_of_mem hyB]
      · simp [Set.indicator_of_notMem hyB]
    -- the RHS representative.
    have hrhs : (((innerSL ℂ (indicatorConstLp 2 hB hνB (1 : ℂ))).smulRight
          (indicatorConstLp 2 hA hμA 1)) f : α → ℂ)
        =ᵐ[μ] fun x => (∫ y, B.indicator (fun _ => (1 : ℂ)) y * (f : β → ℂ) y ∂ν)
          * A.indicator (fun _ => (1 : ℂ)) x := by
      rw [ContinuousLinearMap.smulRight_apply, hinner]
      filter_upwards [Lp.coeFn_smul (∫ y, B.indicator (fun _ => (1 : ℂ)) y * (f : β → ℂ) y ∂ν)
          (indicatorConstLp 2 hA hμA (1 : ℂ)),
        indicatorConstLp_coeFn (μ := μ) (hs := hA) (hμs := hμA) (c := (1 : ℂ))] with x hx hxA
      rw [hx, Pi.smul_apply, smul_eq_mul, hxA, mul_comm]
    -- the LHS representative is `x ↦ 𝟙_A(x)·∫ 𝟙_B(y) f(y)`.
    refine (integralOperator_coeFn _ f).trans (Filter.EventuallyEq.trans ?_ hrhs.symm)
    filter_upwards [Measure.ae_ae_of_ae_prod
      (indicatorConstLp_coeFn (μ := μ.prod ν) (hs := hA.prod hB) (hμs := hAB) (c := (1 : ℂ)))]
      with x hx
    change (∫ y, (↑(indicatorConstLp 2 (hA.prod hB) hAB (1 : ℂ)) : α × β → ℂ) (x, y)
        * (f : β → ℂ) y ∂ν)
        = (∫ y, B.indicator (fun _ => (1 : ℂ)) y * (f : β → ℂ) y ∂ν) * A.indicator (fun _ => 1) x
    rw [← integral_mul_const]
    refine integral_congr_ae ?_
    filter_upwards [hx] with y hy
    rw [hy]
    by_cases hxA : x ∈ A <;> by_cases hyB : y ∈ B <;>
      simp [Set.mem_prod, hxA, hyB]
  rw [hop]
  exact isCompactOperator_smulRight _ _

end Kernel

end Spectra.CompactOperator
