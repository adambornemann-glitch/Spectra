/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Flow.CubicInvariance
/-!
# Infinitesimal Generator and Flow Equation

The infinitesimal generator of a divergence-preserving family is a
vector field on the parameter space — the analogue of Stone's generator
A defined by Aψ = lim_{t→0} (it)⁻¹(U(t)ψ - ψ).

Differentiating the structure-preservation laws of the family yields
the infinitesimal conditions:

  L_X g = 0     (Killing equation — Fisher metric is infinitesimally preserved)
  L_X C = 0     (cubic tensor is infinitesimally preserved)

The family is recovered from its generator by the flow equation

  d/dt φ_t(θ) = X(φ_t(θ))

— the information-geometric analogue of dψ/dt = iAψ.

## Main statements

* `generator` — the infinitesimal generator X(θ) = d/dt φ_t(θ)|_{t=0}
* `generator_killing` — infinitesimal Fisher preservation
* `generator_preserves_cubic` — infinitesimal cubic preservation
* `flow_equation` — autonomous ODE satisfied by the family
-/

open MeasureTheory Finset Filter Topology TopologicalSpace
open Spectra.InformationGeometry.TwiceDifferentiableModel
namespace Spectra.InformationGeometry
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
open ThriceDifferentiableModel.DivergencePreservingFamily
namespace TwiceDifferentiableModel.DivergencePreservingFamily

variable {M : TwiceDifferentiableModel n Ω}
variable (F : M.DivergencePreservingFamily)

-- ============================================================================
-- §4b. The infinitesimal generator
-- ============================================================================

/-- The **infinitesimal generator** of a divergence-preserving family:
  X(θ) = d/dt φ_t(θ) |_{t=0}

This is a vector field on the parameter space — the analogue of Stone's
generator A defined by Aψ = lim_{t→0} (it)⁻¹(U(t)ψ - ψ). -/
noncomputable def generator (θ : ParamSpace n) : ParamSpace n :=
  fderiv ℝ (fun t => F.φ t θ) 0 1

/-- The generator is well-defined (the derivative exists). -/
lemma generator_exists (θ : ParamSpace n) :
    DifferentiableAt ℝ (fun t => F.φ t θ) 0 := by
  change DifferentiableAt ℝ (Function.uncurry F.φ ∘ (fun t => (t, θ))) 0
  exact DifferentiableAt.comp 0
    ((F.smooth.differentiable (by simp)).differentiableAt)
    (DifferentiableAt.prodMk differentiableAt_id (differentiableAt_const θ))

/-- The generator satisfies the Killing equation L_X g = 0.

This is the infinitesimal form of `preserves_fisher`: differentiating
g(dφ_t · v, dφ_t · w) = g(v, w) in t at t = 0 gives the Killing
equation. -/
lemma generator_killing {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) :
    ∀ v w : ParamSpace n,
    fderiv ℝ (fun t =>
      M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
        (fderiv ℝ (F.φ t) θ v) (fderiv ℝ (F.φ t) θ w)) 0 1 = 0 := by
  intro v w
  have hconst : (fun t => M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
      (fderiv ℝ (F.φ t) θ v) (fderiv ℝ (F.φ t) θ w)) =
    fun _ => M.toRegularStatisticalModel.fisherBilin θ v w := by
    ext t; exact F.preserves_fisher hθ t v w
  rw [hconst]
  simp [ContinuousLinearMap.zero_apply]

/-- The generator preserves the cubic tensor: L_X C = 0.

Infinitesimal form of `preserves_cubic`. -/
lemma generator_preserves_cubic
    (M₃ : ThriceDifferentiableModel n Ω)
    (hM₃ : M₃.toTwiceDifferentiableModel = M)
    (F : M.DivergencePreservingFamily)
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) :
    ∀ u v w : ParamSpace n,
    fderiv ℝ (fun t =>
      M.cubicTrilin (F.φ t θ)
        (fderiv ℝ (F.φ t) θ u) (fderiv ℝ (F.φ t) θ v)
        (fderiv ℝ (F.φ t) θ w)) 0 1 = 0 := by
  intro u v w
  have hconst : (fun t =>
      M.cubicTrilin (F.φ t θ)
        (fderiv ℝ (F.φ t) θ u) (fderiv ℝ (F.φ t) θ v)
        (fderiv ℝ (F.φ t) θ w)) =
    fun _ => M.cubicTrilin θ u v w := by
    ext t
    exact preserves_cubic M M₃ hM₃ F hθ t u v w
  rw [hconst]
  simp [ContinuousLinearMap.zero_apply]

-- ============================================================================
-- §4c. Recovery: the flow from the generator
-- ============================================================================

/-- The family is recovered from its generator by the flow equation:
  d/dt φ_t(θ) = X(φ_t(θ))

This is the ODE that the generator satisfies — the analogue of
the Schrödinger equation dψ/dt = iAψ. -/
lemma flow_equation (θ : ParamSpace n) (t : ℝ) :
    fderiv ℝ (fun s => F.φ s θ) t 1 = F.generator (F.φ t θ) := by
  -- ── Step 1: HasDerivAt at 0 for the trajectory starting at φ_t(θ) ──
  have h₀ : HasDerivAt (fun u => F.φ u (F.φ t θ)) (F.generator (F.φ t θ)) 0 :=
    (F.generator_exists (F.φ t θ)).hasFDerivAt.hasDerivAt
  -- ── Step 2: Group law identifies the trajectories ──
  have h_eq : (fun s => F.φ s θ) = (fun s => F.φ (s - t) (F.φ t θ)) := by
    ext s; rw [← F.group_law (s - t) t θ, sub_add_cancel]
  -- ── Step 3: Chain rule shifts derivative from 0 to t ──
  set g := fun u => F.φ u (F.φ t θ)
  set f := fun s : ℝ => s - t
  have hg : HasFDerivAt g
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (F.generator (F.φ t θ)))
      (f t) := by
    simp only [f, sub_self]; exact h₀.hasFDerivAt
  have hf : HasFDerivAt f (ContinuousLinearMap.id ℝ ℝ) t :=
    hasFDerivAt_sub_const t
  have h_comp := hg.comp t hf
  rw [ContinuousLinearMap.comp_id] at h_comp
  -- ── Step 4: Extract fderiv and evaluate at 1 ──
  rw [h_eq, show (fun s => F.φ (s - t) (F.φ t θ)) = g ∘ f from rfl,
      h_comp.fderiv, ContinuousLinearMap.smulRight_apply]
  simp

/-
  Strategy: t ↦ ∑_{a,b} (dφ_t·eᵢ)_a · (dφ_t·eⱼ)_b · g_{ab}(φ_t θ) is a
  finite sum of products of smooth functions of t. Product rule + chain
  rule, then evaluate at t = 0 where φ₀ = id.

  Term 1: ∑_k X^k ∂_k g_{ij}   (from g_{ab}(φ_t θ), chain rule via the
          Thrice-level Leibniz field `fisherMatrix_hasFDerivAt`)
  Term 2: ∑_k g_{kj} ∂_i X^k   (from (dφ_t·eᵢ)_k — the identification
          d/dt|₀ ∂_θφ = ∂_θ d/dt|₀φ = ∂X is Schwarz symmetry of the
          second derivative of the uncurried φ at (0, θ))
  Term 3: ∑_k g_{ik} ∂_j X^k   (from (dφ_t·eⱼ)_k, same)

  At t = 0: (dφ_0·eᵢ)_a = δ_{ai}, collapsing the (a,b)-sum.
-/

/-- Component expansion: the coordinate-free derivative equals the
Killing sum. Requires product + chain rule, plus the third-order
Leibniz data (hence the `ThriceDifferentiableModel` hypothesis). -/
lemma killing_expansion
    (M₃ : ThriceDifferentiableModel n Ω)
    (hM₃ : M₃.toTwiceDifferentiableModel = M)
    (F : M.DivergencePreservingFamily)
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (i j : Fin n) :
    fderiv ℝ (fun t =>
      M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single i 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single j 1))) 0 1 =
    ∑ k : Fin n,
      (F.generator θ k *
        fderiv ℝ (fun θ' =>
          M.toRegularStatisticalModel.fisherMatrix θ' i j) θ
          (EuclideanSpace.single k 1) +
      M.toRegularStatisticalModel.fisherMatrix θ k j *
        fderiv ℝ (fun θ' => F.generator θ' k) θ
          (EuclideanSpace.single i 1) +
      M.toRegularStatisticalModel.fisherMatrix θ i k *
        fderiv ℝ (fun θ' => F.generator θ' k) θ
          (EuclideanSpace.single j 1)) := by
  subst hM₃
  -- ════════════════════════════════════════════════════════════════
  -- §0. Smoothness infrastructure for Φ := uncurry φ
  -- ════════════════════════════════════════════════════════════════
  have hΦd : ∀ p : ℝ × ParamSpace n,
      HasFDerivAt (Function.uncurry F.φ)
        (fderiv ℝ (Function.uncurry F.φ) p) p :=
    fun p => ((F.smooth.differentiable (by simp)) p).hasFDerivAt
  have hΨs : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (Function.uncurry F.φ)) :=
    F.smooth.fderiv_right (m := (⊤ : ℕ∞)) (by exact_mod_cast le_top)
  have hΨd : HasFDerivAt (fderiv ℝ (Function.uncurry F.φ))
      (fderiv ℝ (fderiv ℝ (Function.uncurry F.φ)) ((0:ℝ), θ)) ((0:ℝ), θ) :=
    ((hΨs.differentiable (by simp)) ((0:ℝ), θ)).hasFDerivAt
  -- Schwarz: the second derivative of Φ at (0, θ) is symmetric
  have hsymm : ∀ v w : ℝ × ParamSpace n,
      fderiv ℝ (fderiv ℝ (Function.uncurry F.φ)) ((0:ℝ), θ) v w =
      fderiv ℝ (fderiv ℝ (Function.uncurry F.φ)) ((0:ℝ), θ) w v :=
    fun v w => second_derivative_symmetric_of_eventually_of_real
      (Filter.Eventually.of_forall fun p => hΦd p) hΨd v w
  -- ════════════════════════════════════════════════════════════════
  -- §1. Partial derivatives of Φ vs. derivatives of the slices
  -- ════════════════════════════════════════════════════════════════
  -- θ-slice: dφ_s(θ)·v = dΦ(s,θ)·(0,v)
  have hpartial : ∀ (s : ℝ) (v : ParamSpace n),
      fderiv ℝ (F.φ s) θ v =
      fderiv ℝ (Function.uncurry F.φ) (s, θ) ((0:ℝ), v) := by
    intro s v
    have hmk : HasFDerivAt (fun θ'' : ParamSpace n => ((s, θ'') : ℝ × ParamSpace n))
        ((0 : ParamSpace n →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ParamSpace n))) θ :=
      (hasFDerivAt_const s θ).prodMk (hasFDerivAt_id θ)
    have hcomp : HasFDerivAt (F.φ s)
        ((fderiv ℝ (Function.uncurry F.φ) (s, θ)).comp
          ((0 : ParamSpace n →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ParamSpace n)))) θ :=
      (hΦd (s, θ)).comp θ hmk
    rw [hcomp.fderiv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply]
  -- t-slice at any base point: X(θ') = dΦ(0,θ')·(1,0)
  have hgen : ∀ θ' : ParamSpace n,
      F.generator θ' =
      fderiv ℝ (Function.uncurry F.φ) ((0:ℝ), θ') ((1:ℝ), (0:ParamSpace n)) := by
    intro θ'
    have hline' : HasDerivAt (fun t : ℝ => ((t, θ') : ℝ × ParamSpace n))
        ((1:ℝ), (0:ParamSpace n)) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 θ')
    have h := (hΦd ((0:ℝ), θ')).comp_hasDerivAt 0 hline'
    have h2 : deriv (fun t => F.φ t θ') 0 =
        fderiv ℝ (Function.uncurry F.φ) ((0:ℝ), θ') ((1:ℝ), (0:ParamSpace n)) :=
      h.deriv
    change fderiv ℝ (fun t => F.φ t θ') 0 1 =
      fderiv ℝ (Function.uncurry F.φ) ((0:ℝ), θ') ((1:ℝ), (0:ParamSpace n))
    rw [fderiv_apply_one_eq_deriv]; exact h2
  have hgen_eq : (fun θ' : ParamSpace n => F.generator θ') =
      fun θ' : ParamSpace n =>
        fderiv ℝ (Function.uncurry F.φ) ((0:ℝ), θ') ((1:ℝ), (0:ParamSpace n)) :=
    funext hgen
  -- ════════════════════════════════════════════════════════════════
  -- §2. The mixed second derivatives, both ways round
  -- ════════════════════════════════════════════════════════════════
  have hline : HasDerivAt (fun t : ℝ => ((t, θ) : ℝ × ParamSpace n))
      ((1:ℝ), (0:ParamSpace n)) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 θ)
  -- t-derivative of t ↦ dΦ(t,θ)·(0,e_c)
  have hvec : ∀ c : Fin n, HasDerivAt
      (fun t : ℝ => fderiv ℝ (Function.uncurry F.φ) (t, θ)
        ((0:ℝ), EuclideanSpace.single c 1))
      (fderiv ℝ (fderiv ℝ (Function.uncurry F.φ)) ((0:ℝ), θ)
        ((1:ℝ), (0:ParamSpace n)) ((0:ℝ), EuclideanSpace.single c 1)) 0 := by
    intro c
    have h := (hΨd.clm_apply (hasFDerivAt_const
      ((0:ℝ), EuclideanSpace.single c 1) ((0:ℝ), θ))).comp_hasDerivAt 0 hline
    simp only [Function.comp_def, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.comp_zero, zero_add] at h
    exact h
  -- θ-derivative of the generator field
  have hemb : HasFDerivAt (fun θ' : ParamSpace n => (((0:ℝ), θ') : ℝ × ParamSpace n))
      ((0 : ParamSpace n →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ParamSpace n))) θ :=
    (hasFDerivAt_const (0:ℝ) θ).prodMk (hasFDerivAt_id θ)
  have hgen_hasF : HasFDerivAt (fun θ' : ParamSpace n => F.generator θ')
      ((((fderiv ℝ (Function.uncurry F.φ) ((0:ℝ), θ)).comp
          (0 : ℝ × ParamSpace n →L[ℝ] ℝ × ParamSpace n)) +
        (fderiv ℝ (fderiv ℝ (Function.uncurry F.φ)) ((0:ℝ), θ)).flip
          ((1:ℝ), (0:ParamSpace n))).comp
        ((0 : ParamSpace n →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ParamSpace n)))) θ := by
    rw [hgen_eq]
    exact (hΨd.clm_apply (hasFDerivAt_const
      ((1:ℝ), (0:ParamSpace n)) ((0:ℝ), θ))).comp θ hemb
  -- components of ∂X, expressed through the second derivative of Φ
  have hbridge : ∀ a c : Fin n,
      fderiv ℝ (fun θ' => F.generator θ' a) θ (EuclideanSpace.single c 1) =
      (fderiv ℝ (fderiv ℝ (Function.uncurry F.φ)) ((0:ℝ), θ)
        ((0:ℝ), EuclideanSpace.single c 1) ((1:ℝ), (0:ParamSpace n))).ofLp a := by
    intro a c
    have hfn : (fun θ' => F.generator θ' a)
        = ⇑(EuclideanSpace.proj a : ParamSpace n →L[ℝ] ℝ) ∘
          (fun θ' : ParamSpace n => F.generator θ') := by
      funext θ'
      simp [EuclideanSpace.coe_proj]
    have hcomp :=
      (EuclideanSpace.proj a : ParamSpace n →L[ℝ] ℝ).hasFDerivAt.comp θ hgen_hasF
    rw [hfn, hcomp.fderiv]
    simp [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_zero, zero_add]
  -- the key Schwarz consequence: d/dt|₀ (dφ_t·e_c)_a = (∂X·e_c)_a
  have hA : ∀ a c : Fin n, HasDerivAt
      (fun t : ℝ => (fderiv ℝ (Function.uncurry F.φ) (t, θ)
        ((0:ℝ), EuclideanSpace.single c 1)).ofLp a)
      (fderiv ℝ (fun θ' => F.generator θ' a) θ (EuclideanSpace.single c 1)) 0 := by
    intro a c
    have hfn : (fun t : ℝ => (fderiv ℝ (Function.uncurry F.φ) (t, θ)
          ((0:ℝ), EuclideanSpace.single c 1)).ofLp a)
        = ⇑(EuclideanSpace.proj a : ParamSpace n →L[ℝ] ℝ) ∘
          (fun t : ℝ => fderiv ℝ (Function.uncurry F.φ) (t, θ)
            ((0:ℝ), EuclideanSpace.single c 1)) := by
      funext t
      simp [EuclideanSpace.coe_proj]
    have base := (EuclideanSpace.proj a : ParamSpace n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt
      0 (hvec c)
    simp only [EuclideanSpace.coe_proj] at base
    rw [hfn, hbridge a c,
      hsymm ((0:ℝ), EuclideanSpace.single c 1) ((1:ℝ), (0:ParamSpace n))]
    exact base
  -- ════════════════════════════════════════════════════════════════
  -- §3. Chain rule for the metric coefficients along the flow
  -- ════════════════════════════════════════════════════════════════
  choose Lg hLg _hLg_eval using M₃.fisherMatrix_hasFDerivAt θ hθ
  have hflow : HasDerivAt (fun t => F.φ t θ) (F.generator θ) 0 :=
    (F.generator_exists θ).hasFDerivAt.hasDerivAt
  have hGd : ∀ a b : Fin n, HasDerivAt
      (fun t => M₃.toTwiceDifferentiableModel.toRegularStatisticalModel.fisherMatrix
        (F.φ t θ) a b)
      (Lg a b (F.generator θ)) 0 := by
    intro a b
    have h1 : HasFDerivAt
        (fun θ' => M₃.toTwiceDifferentiableModel.toRegularStatisticalModel.fisherMatrix
          θ' a b)
        (Lg a b) (F.φ 0 θ) := by
      rw [F.identity θ]; exact hLg a b
    exact h1.comp_hasDerivAt 0 hflow
  -- evaluation of the Leibniz derivative on coordinate directions
  have hLfd : ∀ k : Fin n,
      fderiv ℝ (fun θ' =>
        M₃.toTwiceDifferentiableModel.toRegularStatisticalModel.fisherMatrix θ' i j) θ
        (EuclideanSpace.single k 1) = Lg i j (EuclideanSpace.single k 1) :=
    fun k => DFunLike.congr_fun (hLg i j).fderiv _
  -- ════════════════════════════════════════════════════════════════
  -- §4. Scalar helpers: basis expansion and δ-collapse
  -- ════════════════════════════════════════════════════════════════
  have hlinR : ∀ (L : ParamSpace n →L[ℝ] ℝ) (x : ParamSpace n),
      L x = ∑ k : Fin n, x.ofLp k * L (EuclideanSpace.single k 1) := by
    intro L x
    have hbasis : x = ∑ k : Fin n, x.ofLp k • EuclideanSpace.single k 1 := by
      ext p; simp only [WithLp.ofLp_sum, WithLp.ofLp_smul,
        PiLp.ofLp_single, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]
    conv_lhs => rw [hbasis, map_sum]
    simp only [map_smul, smul_eq_mul]
  have hcollapse : ∀ (f : Fin n → ℝ) (c : Fin n),
      (∑ b : Fin n, (EuclideanSpace.single c 1).ofLp b * f b) = f c := by
    intro f c
    simp only [PiLp.ofLp_single, Pi.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  -- the abstract product-rule-with-deltas collapse
  have halg : ∀ (P Q : Fin n → ℝ) (R G : Fin n → Fin n → ℝ),
      (∑ a : Fin n, ∑ b : Fin n,
        ((P a * (EuclideanSpace.single j 1).ofLp b
            + (EuclideanSpace.single i 1).ofLp a * Q b) * G a b
          + (EuclideanSpace.single i 1).ofLp a
              * (EuclideanSpace.single j 1).ofLp b * R a b))
      = (∑ k : Fin n, G i k * Q k) + (∑ k : Fin n, G k j * P k) + R i j := by
    intro P Q R G
    have inner : ∀ a : Fin n,
        (∑ b : Fin n,
          ((P a * (EuclideanSpace.single j 1).ofLp b
              + (EuclideanSpace.single i 1).ofLp a * Q b) * G a b
            + (EuclideanSpace.single i 1).ofLp a
                * (EuclideanSpace.single j 1).ofLp b * R a b))
        = P a * G a j
          + (EuclideanSpace.single i 1).ofLp a * (∑ b : Fin n, Q b * G a b)
          + (EuclideanSpace.single i 1).ofLp a * R a j := by
      intro a
      have hsplit : ∀ b : Fin n,
          ((P a * (EuclideanSpace.single j 1).ofLp b
              + (EuclideanSpace.single i 1).ofLp a * Q b) * G a b
            + (EuclideanSpace.single i 1).ofLp a
                * (EuclideanSpace.single j 1).ofLp b * R a b)
          = (EuclideanSpace.single j 1).ofLp b * (P a * G a b)
            + (EuclideanSpace.single i 1).ofLp a * (Q b * G a b)
            + (EuclideanSpace.single j 1).ofLp b
                * ((EuclideanSpace.single i 1).ofLp a * R a b) :=
        fun b => by ring
      refine (Finset.sum_congr rfl fun b _ => hsplit b).trans ?_
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        hcollapse (fun b => P a * G a b) j, ← Finset.mul_sum,
        hcollapse (fun b => (EuclideanSpace.single i 1).ofLp a * R a b) j]
    refine (Finset.sum_congr rfl fun a _ => inner a).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      hcollapse (fun a => ∑ b : Fin n, Q b * G a b) i,
      hcollapse (fun a => R a j) i,
      show (∑ a : Fin n, P a * G a j) = ∑ k : Fin n, G k j * P k from
        Finset.sum_congr rfl fun k _ => mul_comm _ _,
      show (∑ b : Fin n, Q b * G i b) = ∑ k : Fin n, G i k * Q k from
        Finset.sum_congr rfl fun k _ => mul_comm _ _]
    ring
  -- ════════════════════════════════════════════════════════════════
  -- §5. The function in canonical form, its derivative, and assembly
  -- ════════════════════════════════════════════════════════════════
  -- expand fisherBilin into the matrix double sum, at every t
  have hG : ∀ s : ℝ,
      M₃.toTwiceDifferentiableModel.toRegularStatisticalModel.fisherBilin (F.φ s θ)
        (fderiv ℝ (F.φ s) θ (EuclideanSpace.single i 1))
        (fderiv ℝ (F.φ s) θ (EuclideanSpace.single j 1)) =
      ∑ a : Fin n, ∑ b : Fin n,
        (fderiv ℝ (F.φ s) θ (EuclideanSpace.single i 1)).ofLp a *
        (fderiv ℝ (F.φ s) θ (EuclideanSpace.single j 1)).ofLp b *
        M₃.toTwiceDifferentiableModel.toRegularStatisticalModel.fisherMatrix
          (F.φ s θ) a b := by
    intro s
    have hβ := F.maps_domain s θ hθ
    rw [M₃.toTwiceDifferentiableModel.toRegularStatisticalModel.fisherBilin_eq_sum_fisherMatrix
      hβ (M₃.toTwiceDifferentiableModel.scoreSqIntegrable (F.φ s θ) hβ)]
  have hfun : (fun t =>
      M₃.toTwiceDifferentiableModel.toRegularStatisticalModel.fisherBilin (F.φ t θ)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single i 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single j 1)))
      = ∑ a : Fin n, ∑ b : Fin n,
        (fun t : ℝ => (fderiv ℝ (Function.uncurry F.φ) (t, θ)
          ((0:ℝ), EuclideanSpace.single i 1)).ofLp a) *
        (fun t : ℝ => (fderiv ℝ (Function.uncurry F.φ) (t, θ)
          ((0:ℝ), EuclideanSpace.single j 1)).ofLp b) *
        (fun t => M₃.toTwiceDifferentiableModel.toRegularStatisticalModel.fisherMatrix
          (F.φ t θ) a b) := by
    funext s
    rw [hG s, hpartial s (EuclideanSpace.single i 1),
      hpartial s (EuclideanSpace.single j 1)]
    simp only [Finset.sum_apply, Pi.mul_apply]
  -- the derivative of the canonical form, by the product rule
  have key : HasDerivAt
      (∑ a : Fin n, ∑ b : Fin n,
        (fun t : ℝ => (fderiv ℝ (Function.uncurry F.φ) (t, θ)
          ((0:ℝ), EuclideanSpace.single i 1)).ofLp a) *
        (fun t : ℝ => (fderiv ℝ (Function.uncurry F.φ) (t, θ)
          ((0:ℝ), EuclideanSpace.single j 1)).ofLp b) *
        (fun t => M₃.toTwiceDifferentiableModel.toRegularStatisticalModel.fisherMatrix
          (F.φ t θ) a b))
      (∑ a : Fin n, ∑ b : Fin n,
        ((fderiv ℝ (fun θ' => F.generator θ' a) θ (EuclideanSpace.single i 1) *
            (fderiv ℝ (Function.uncurry F.φ) ((0:ℝ), θ)
              ((0:ℝ), EuclideanSpace.single j 1)).ofLp b +
          (fderiv ℝ (Function.uncurry F.φ) ((0:ℝ), θ)
            ((0:ℝ), EuclideanSpace.single i 1)).ofLp a *
            fderiv ℝ (fun θ' => F.generator θ' b) θ (EuclideanSpace.single j 1)) *
          M₃.toTwiceDifferentiableModel.toRegularStatisticalModel.fisherMatrix
            (F.φ 0 θ) a b +
        (fderiv ℝ (Function.uncurry F.φ) ((0:ℝ), θ)
          ((0:ℝ), EuclideanSpace.single i 1)).ofLp a *
          (fderiv ℝ (Function.uncurry F.φ) ((0:ℝ), θ)
            ((0:ℝ), EuclideanSpace.single j 1)).ofLp b *
          Lg a b (F.generator θ))) 0 :=
    HasDerivAt.sum fun a _ => HasDerivAt.sum fun b _ =>
      ((hA a i).mul (hA b j)).mul (hGd a b)
  -- at t = 0 the flow is the identity
  have hid : F.φ 0 = (id : ParamSpace n → ParamSpace n) := funext F.identity
  have hA0 : ∀ v : ParamSpace n,
      fderiv ℝ (Function.uncurry F.φ) ((0:ℝ), θ) ((0:ℝ), v) = v := by
    intro v
    rw [← hpartial 0 v, hid, fderiv_id, ContinuousLinearMap.id_apply]
  -- assemble
  rw [hfun, fderiv_apply_one_eq_deriv, key.deriv, hA0 (EuclideanSpace.single i 1),
    hA0 (EuclideanSpace.single j 1), F.identity θ]
  refine (halg _ _ _ _).trans ?_
  rw [hlinR (Lg i j) (F.generator θ),
    show (∑ k : Fin n, (F.generator θ).ofLp k * Lg i j (EuclideanSpace.single k 1)) =
      ∑ k : Fin n, F.generator θ k *
        fderiv ℝ (fun θ' =>
          M₃.toTwiceDifferentiableModel.toRegularStatisticalModel.fisherMatrix θ' i j) θ
          (EuclideanSpace.single k 1) from
      Finset.sum_congr rfl fun k _ => by rw [← hLfd k],
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

end TwiceDifferentiableModel.DivergencePreservingFamily

end Spectra.InformationGeometry
