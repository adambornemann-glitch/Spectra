/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: InformationGeometry/Dynamics/Stone.lean
-/
import Spectra.InformationGeometry.Stone.Generator

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Algebra.BigOperators.WithTop
-- For Stone Uniqueness --
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Topology.Order.Compact

/-!
# The Information-Geometric Stone's Theorem

The bijection between divergence-preserving one-parameter families and
their infinitesimal generators (Killing + cubic-preserving vector fields).

## Design notes

* `InfoGeometricGenerator.killing` and `.preserves_cubic` state the Lie
  derivative conditions `L_X g = 0` and `L_X C = 0` in coordinates.
  Note the index placement in `preserves_cubic`: the displacement terms
  are `C_{ljk} ∂_i X^l` (derivative of the field component `X^l` in the
  direction `e_i`), matching the Lie derivative of a (0,3)-tensor.

* `DivergencePreservingFamily.toGenerator` requires a
  `ThriceDifferentiableModel` refinement (for the Leibniz derivative of
  the Fisher matrix, exactly as in `killing_expansion`) and, in
  addition, differentiability of `θ ↦ cubicTensor θ a b c` (`hC`).
  The latter is genuinely extra data: a `ThriceDifferentiableModel`
  guarantees the *existence* of the cubic tensor, but its
  θ-differentiability is a fourth-order regularity statement that the
  model hierarchy does not carry.  Following the bundled-regularity
  design of the library, it is taken as a hypothesis.

* The completeness hypothesis is `FlowComplete`, which asserts directly
  that every info-geometric generator integrates to a global
  divergence-preserving flow.  This replaces an earlier
  `GeodesicallyComplete` class whose statement was vacuous (it was
  satisfied by constant curves) and which could not support the
  surjectivity direction: deriving divergence preservation of the flow
  from `L_X g = L_X C = 0` is a rigidity theorem (the divergence is an
  integral functional, not yet known *in this development* to be
  determined by `g` and `C`).  Deriving `FlowComplete` from genuine
  Fisher geodesic completeness (Picard–Lindelöf, conservation of
  `‖X‖_g` along flow lines, divergence rigidity) is future work; the
  hypothesis isolates exactly what the theorem needs.
-/

open MeasureTheory Finset Filter Topology TopologicalSpace
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
namespace Spectra.InformationGeometry
namespace TwiceDifferentiableModel

variable {M : TwiceDifferentiableModel n Ω}

-- ============================================================================
-- §5. The Generator Structure (Standalone)
-- ============================================================================

/-! ### Information-geometric generators

A standalone structure for vector fields satisfying the Killing and
cubic-preservation conditions.  The **information-geometric Stone's theorem**
establishes a bijection between `DivergencePreservingFamily` and
`InfoGeometricGenerator`, under a completeness hypothesis. -/

/-- An **information-geometric generator** is a vector field on the
parameter space that preserves both the Fisher metric and the
Amari–Chentsov tensor infinitesimally.

This is the analogue of Stone's `Generator` structure, which carries
a self-adjoint operator with domain conditions. -/
structure InfoGeometricGenerator (M : TwiceDifferentiableModel n Ω) where
  /-- The vector field X : Θ → T_θΘ ≅ ℝⁿ. -/
  vectorField : ParamSpace n → ParamSpace n
  /-- X is smooth. -/
  smooth : ContDiff ℝ ⊤ vectorField
  /-- **Killing condition**: L_X g = 0.
  In coordinates: ∑ₖ Xᵏ ∂ₖg_{ij} + g_{kj} ∂ᵢXᵏ + g_{ik} ∂ⱼXᵏ = 0. -/
  killing : ∀ θ ∈ M.paramDomain, ∀ i j : Fin n,
    ∑ k : Fin n,
      (vectorField θ k *
        fderiv ℝ (fun θ' => M.toRegularStatisticalModel.fisherMatrix θ' i j) θ
          (EuclideanSpace.single k 1) +
      M.toRegularStatisticalModel.fisherMatrix θ k j *
        fderiv ℝ (fun θ' => vectorField θ' k) θ
          (EuclideanSpace.single i 1) +
      M.toRegularStatisticalModel.fisherMatrix θ i k *
        fderiv ℝ (fun θ' => vectorField θ' k) θ
          (EuclideanSpace.single j 1)) = 0
  /-- **Cubic preservation**: L_X C = 0.
  In coordinates:
  ∑ₗ Xˡ ∂ₗC_{ijk} + C_{ljk} ∂ᵢXˡ + C_{ilk} ∂ⱼXˡ + C_{ijl} ∂ₖXˡ = 0.
  Note: the displacement terms differentiate the field component `Xˡ` in
  the tensor-index direction (`∂ᵢXˡ`), as required for the Lie derivative
  of a (0,3)-tensor. -/
  preserves_cubic : ∀ θ ∈ M.paramDomain, ∀ i j k : Fin n,
    ∑ l : Fin n,
      (vectorField θ l *
        fderiv ℝ (fun θ' => M.cubicTensor θ' i j k) θ
          (EuclideanSpace.single l 1) +
      M.cubicTensor θ l j k *
        fderiv ℝ (fun θ' => vectorField θ' l) θ
          (EuclideanSpace.single i 1) +
      M.cubicTensor θ i l k *
        fderiv ℝ (fun θ' => vectorField θ' l) θ
          (EuclideanSpace.single j 1) +
      M.cubicTensor θ i j l *
        fderiv ℝ (fun θ' => vectorField θ' l) θ
          (EuclideanSpace.single k 1)) = 0

/-- Two generators with the same vector field are equal: the remaining
fields are propositions, so proof irrelevance applies. -/
lemma InfoGeometricGenerator.ext_vectorField
    {G₁ G₂ : InfoGeometricGenerator M}
    (h : G₁.vectorField = G₂.vectorField) : G₁ = G₂ := by
  cases G₁; cases G₂; cases h; rfl

-- ============================================================================
-- §6. Toward the Bijection (Forward Map)
-- ============================================================================

/-- At t = 0 the Jacobian of φ_t is the identity. -/
private lemma fderiv_φ_at_zero (F : M.DivergencePreservingFamily)
    (θ : ParamSpace n) :
    fderiv ℝ (F.φ 0) θ = ContinuousLinearMap.id ℝ (ParamSpace n) := by
  have h_eq : F.φ 0 = id := funext F.identity
  rw [h_eq, fderiv_id]

/-- The component (dφ_t · eₐ)_k at t = 0 is δ_{ak}. -/
private lemma fderiv_φ_component_at_zero (F : M.DivergencePreservingFamily)
    (θ : ParamSpace n) (a k : Fin n) :
    (fderiv ℝ (F.φ 0) θ (EuclideanSpace.single a 1)).ofLp k =
    if a = k then 1 else 0 := by
  rw [fderiv_φ_at_zero F θ, ContinuousLinearMap.id_apply]
  simp only [PiLp.single_apply]
  grind only

/-- The generator of a divergence-preserving family is a smooth vector
field: X(θ) = D(uncurry φ)(0,θ)(1,0) is the composition of the C^∞ map
`fderiv ℝ (uncurry φ)` with smooth injections and evaluations. -/
lemma DivergencePreservingFamily.generator_smooth
    (F : M.DivergencePreservingFamily) :
    ContDiff ℝ ⊤ F.generator := by
  -- F.generator θ = D(uncurry φ)(0,θ)(1,0) by the chain rule.
  -- This is eval_{(1,0)} ∘ fderiv(uncurry φ) ∘ (0,·), a composition of C^∞ maps.
  suffices h_eq : F.generator =
      fun θ => fderiv ℝ (Function.uncurry F.φ) (0, θ)
        ((1 : ℝ), (0 : ParamSpace n)) by
    rw [h_eq]
    -- fderiv of a C^∞ function is C^∞
    have hDg : ContDiff ℝ ⊤ (fderiv ℝ (Function.uncurry F.φ)) :=
      F.smooth.fderiv_right le_top
    -- Compose: eval ∘ Dg ∘ inject
    exact (ContinuousLinearMap.apply ℝ (ParamSpace n)
          ((1 : ℝ), (0 : ParamSpace n))).contDiff |>.comp
      (hDg.comp (contDiff_const.prodMk contDiff_id))
  -- Pointwise equality via chain rule
  funext θ
  simp only [DivergencePreservingFamily.generator]
  have h_diff_g : DifferentiableAt ℝ (Function.uncurry F.φ) (0, θ) :=
    (F.smooth.differentiable (by simp)).differentiableAt
  have h_inj : HasFDerivAt (fun t : ℝ => (t, θ))
      ((ContinuousLinearMap.id ℝ ℝ).prod
        (0 : ℝ →L[ℝ] ParamSpace n)) 0 :=
    (hasFDerivAt_id 0).prodMk (hasFDerivAt_const θ 0)
  have h_chain : HasFDerivAt (Function.uncurry F.φ ∘ (fun t => (t, θ)))
      ((fderiv ℝ (Function.uncurry F.φ) (0, θ)).comp
        ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ParamSpace n))) 0 :=
    h_diff_g.hasFDerivAt.comp 0 h_inj
  rw [show (fun t => F.φ t θ) =
      Function.uncurry F.φ ∘ (fun t => (t, θ)) from rfl,
    h_chain.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply]
  simp

/-
  Strategy for the cubic expansion (mirrors `killing_expansion`):
  t ↦ ∑_{a,b,c} (dφ_t·eᵢ)_a (dφ_t·eⱼ)_b (dφ_t·eₖ)_c · C_{abc}(φ_t θ) is a
  finite sum of products of differentiable functions of t.  Product rule +
  chain rule, then evaluate at t = 0 where φ₀ = id:

  Term 1: ∑_l X^l ∂_l C_{ijk}   (from C_{abc}(φ_t θ), chain rule via hC)
  Terms 2–4: ∑_l C_{ljk} ∂_i X^l etc.  (from the (dφ_t·e)_· factors —
          d/dt|₀ ∂_θφ = ∂_θ d/dt|₀φ = ∂X is Schwarz symmetry of the
          second derivative of the uncurried φ at (0, θ))

  At t = 0: (dφ_0·eᵢ)_a = δ_{ai}, collapsing the (a,b,c)-sum.

  Unlike the metric case, no Leibniz field is needed: `cubicTrilin` is a
  plain finite sum, and the θ-derivative of the cubic tensor enters as
  the hypothesis `hC` (see the module docstring).  No domain hypothesis
  is needed either.
-/

/-- Component expansion: the coordinate-free t-derivative of the pulled-back
cubic form equals the Lie-derivative sum `∑_l X^l ∂_l C_{ijk} + C_{ljk} ∂_i X^l
+ C_{ilk} ∂_j X^l + C_{ijl} ∂_k X^l`. -/
private lemma DivergencePreservingFamily.cubic_expansion
    (F : M.DivergencePreservingFamily)
    {θ : ParamSpace n}
    (hC : ∀ a b c : Fin n,
      DifferentiableAt ℝ (fun θ' => M.cubicTensor θ' a b c) θ)
    (i j k : Fin n) :
    fderiv ℝ (fun t =>
      M.cubicTrilin (F.φ t θ)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single i 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single j 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single k 1))) 0 1 =
    ∑ l : Fin n,
      (F.generator θ l *
        fderiv ℝ (fun θ' => M.cubicTensor θ' i j k) θ
          (EuclideanSpace.single l 1) +
      M.cubicTensor θ l j k *
        fderiv ℝ (fun θ' => F.generator θ' l) θ
          (EuclideanSpace.single i 1) +
      M.cubicTensor θ i l k *
        fderiv ℝ (fun θ' => F.generator θ' l) θ
          (EuclideanSpace.single j 1) +
      M.cubicTensor θ i j l *
        fderiv ℝ (fun θ' => F.generator θ' l) θ
          (EuclideanSpace.single k 1)) := by
  -- ════════════════════════════════════════════════════════════════
  -- §0. Smoothness infrastructure for Φ := uncurry φ
  -- ════════════════════════════════════════════════════════════════
  have hΦd : ∀ p : ℝ × ParamSpace n,
      HasFDerivAt (Function.uncurry F.φ)
        (fderiv ℝ (Function.uncurry F.φ) p) p :=
    fun p => ((F.smooth.differentiable (by simp)) p).hasFDerivAt
  have hΨs : ContDiff ℝ ⊤ (fderiv ℝ (Function.uncurry F.φ)) :=
    F.smooth.fderiv_right le_top
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
    show fderiv ℝ (fun t => F.φ t θ') 0 1 =
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
  -- §3. Chain rule for the cubic tensor along the flow
  -- ════════════════════════════════════════════════════════════════
  have hflow : HasDerivAt (fun t => F.φ t θ) (F.generator θ) 0 :=
    (F.generator_exists θ).hasFDerivAt.hasDerivAt
  have hEd : ∀ a b c : Fin n, HasDerivAt
      (fun t => M.cubicTensor (F.φ t θ) a b c)
      (fderiv ℝ (fun θ' => M.cubicTensor θ' a b c) θ (F.generator θ)) 0 := by
    intro a b c
    have h1 : HasFDerivAt (fun θ' => M.cubicTensor θ' a b c)
        (fderiv ℝ (fun θ' => M.cubicTensor θ' a b c) θ) (F.φ 0 θ) := by
      rw [F.identity θ]
      exact (hC a b c).hasFDerivAt
    exact h1.comp_hasDerivAt 0 hflow
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
  -- the abstract product-rule-with-deltas collapse, three levels deep
  have halg : ∀ (P Q R : Fin n → ℝ) (S E : Fin n → Fin n → Fin n → ℝ),
      (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
        (((P a * (EuclideanSpace.single j 1).ofLp b
              + (EuclideanSpace.single i 1).ofLp a * Q b)
                * (EuclideanSpace.single k 1).ofLp c
            + (EuclideanSpace.single i 1).ofLp a
                * (EuclideanSpace.single j 1).ofLp b * R c)
          * E a b c
          + (EuclideanSpace.single i 1).ofLp a
              * (EuclideanSpace.single j 1).ofLp b
              * (EuclideanSpace.single k 1).ofLp c * S a b c))
      = (∑ l : Fin n, E i l k * Q l) + (∑ l : Fin n, E l j k * P l)
          + (∑ l : Fin n, E i j l * R l) + S i j k := by
    intro P Q R S E
    -- collapse the innermost (c) sum
    have inner1 : ∀ a b : Fin n,
        (∑ c : Fin n,
          (((P a * (EuclideanSpace.single j 1).ofLp b
                + (EuclideanSpace.single i 1).ofLp a * Q b)
                  * (EuclideanSpace.single k 1).ofLp c
              + (EuclideanSpace.single i 1).ofLp a
                  * (EuclideanSpace.single j 1).ofLp b * R c)
            * E a b c
            + (EuclideanSpace.single i 1).ofLp a
                * (EuclideanSpace.single j 1).ofLp b
                * (EuclideanSpace.single k 1).ofLp c * S a b c))
        = (P a * (EuclideanSpace.single j 1).ofLp b
              + (EuclideanSpace.single i 1).ofLp a * Q b) * E a b k
          + (EuclideanSpace.single i 1).ofLp a
              * (EuclideanSpace.single j 1).ofLp b * (∑ c : Fin n, R c * E a b c)
          + (EuclideanSpace.single i 1).ofLp a
              * (EuclideanSpace.single j 1).ofLp b * S a b k := by
      intro a b
      have hsplit : ∀ c : Fin n,
          (((P a * (EuclideanSpace.single j 1).ofLp b
                + (EuclideanSpace.single i 1).ofLp a * Q b)
                  * (EuclideanSpace.single k 1).ofLp c
              + (EuclideanSpace.single i 1).ofLp a
                  * (EuclideanSpace.single j 1).ofLp b * R c)
            * E a b c
            + (EuclideanSpace.single i 1).ofLp a
                * (EuclideanSpace.single j 1).ofLp b
                * (EuclideanSpace.single k 1).ofLp c * S a b c)
          = (EuclideanSpace.single k 1).ofLp c *
              ((P a * (EuclideanSpace.single j 1).ofLp b
                + (EuclideanSpace.single i 1).ofLp a * Q b) * E a b c)
            + (EuclideanSpace.single i 1).ofLp a
                * (EuclideanSpace.single j 1).ofLp b * (R c * E a b c)
            + (EuclideanSpace.single k 1).ofLp c *
                ((EuclideanSpace.single i 1).ofLp a
                  * (EuclideanSpace.single j 1).ofLp b * S a b c) :=
        fun c => by ring
      refine (Finset.sum_congr rfl fun c _ => hsplit c).trans ?_
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        hcollapse (fun c => (P a * (EuclideanSpace.single j 1).ofLp b
          + (EuclideanSpace.single i 1).ofLp a * Q b) * E a b c) k,
        ← Finset.mul_sum,
        hcollapse (fun c => (EuclideanSpace.single i 1).ofLp a
          * (EuclideanSpace.single j 1).ofLp b * S a b c) k]
    -- collapse the middle (b) sum
    have inner2 : ∀ a : Fin n,
        (∑ b : Fin n,
          ((P a * (EuclideanSpace.single j 1).ofLp b
              + (EuclideanSpace.single i 1).ofLp a * Q b) * E a b k
            + (EuclideanSpace.single i 1).ofLp a
                * (EuclideanSpace.single j 1).ofLp b * (∑ c : Fin n, R c * E a b c)
            + (EuclideanSpace.single i 1).ofLp a
                * (EuclideanSpace.single j 1).ofLp b * S a b k))
        = P a * E a j k
          + (EuclideanSpace.single i 1).ofLp a * (∑ b : Fin n, Q b * E a b k)
          + (EuclideanSpace.single i 1).ofLp a * (∑ c : Fin n, R c * E a j c)
          + (EuclideanSpace.single i 1).ofLp a * S a j k := by
      intro a
      have hsplit2 : ∀ b : Fin n,
          ((P a * (EuclideanSpace.single j 1).ofLp b
              + (EuclideanSpace.single i 1).ofLp a * Q b) * E a b k
            + (EuclideanSpace.single i 1).ofLp a
                * (EuclideanSpace.single j 1).ofLp b * (∑ c : Fin n, R c * E a b c)
            + (EuclideanSpace.single i 1).ofLp a
                * (EuclideanSpace.single j 1).ofLp b * S a b k)
          = (EuclideanSpace.single j 1).ofLp b * (P a * E a b k)
            + (EuclideanSpace.single i 1).ofLp a * (Q b * E a b k)
            + (EuclideanSpace.single j 1).ofLp b *
                ((EuclideanSpace.single i 1).ofLp a * (∑ c : Fin n, R c * E a b c))
            + (EuclideanSpace.single j 1).ofLp b *
                ((EuclideanSpace.single i 1).ofLp a * S a b k) :=
        fun b => by ring
      refine (Finset.sum_congr rfl fun b _ => hsplit2 b).trans ?_
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        hcollapse (fun b => P a * E a b k) j,
        ← Finset.mul_sum,
        hcollapse (fun b => (EuclideanSpace.single i 1).ofLp a
          * (∑ c : Fin n, R c * E a b c)) j,
        hcollapse (fun b => (EuclideanSpace.single i 1).ofLp a * S a b k) j]
    -- collapse the outer (a) sum and reorder
    refine (Finset.sum_congr rfl fun a _ =>
      ((Finset.sum_congr rfl fun b _ => inner1 a b).trans (inner2 a))).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      hcollapse (fun a => ∑ b : Fin n, Q b * E a b k) i,
      hcollapse (fun a => ∑ c : Fin n, R c * E a j c) i,
      hcollapse (fun a => S a j k) i,
      show (∑ a : Fin n, P a * E a j k) = ∑ l : Fin n, E l j k * P l from
        Finset.sum_congr rfl fun l _ => mul_comm _ _,
      show (∑ b : Fin n, Q b * E i b k) = ∑ l : Fin n, E i l k * Q l from
        Finset.sum_congr rfl fun l _ => mul_comm _ _,
      show (∑ c : Fin n, R c * E i j c) = ∑ l : Fin n, E i j l * R l from
        Finset.sum_congr rfl fun l _ => mul_comm _ _]
    ring
  -- ════════════════════════════════════════════════════════════════
  -- §5. The function in canonical form, its derivative, and assembly
  -- ════════════════════════════════════════════════════════════════
  -- expand cubicTrilin into the triple sum, at every t (definitional)
  have hcube : ∀ s : ℝ,
      M.cubicTrilin (F.φ s θ)
        (fderiv ℝ (F.φ s) θ (EuclideanSpace.single i 1))
        (fderiv ℝ (F.φ s) θ (EuclideanSpace.single j 1))
        (fderiv ℝ (F.φ s) θ (EuclideanSpace.single k 1)) =
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
        (fderiv ℝ (F.φ s) θ (EuclideanSpace.single i 1)).ofLp a *
        (fderiv ℝ (F.φ s) θ (EuclideanSpace.single j 1)).ofLp b *
        (fderiv ℝ (F.φ s) θ (EuclideanSpace.single k 1)).ofLp c *
        M.cubicTensor (F.φ s θ) a b c :=
    fun s => rfl
  have hfun : (fun t =>
      M.cubicTrilin (F.φ t θ)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single i 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single j 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single k 1)))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
        (fun t : ℝ => (fderiv ℝ (Function.uncurry F.φ) (t, θ)
          ((0:ℝ), EuclideanSpace.single i 1)).ofLp a) *
        (fun t : ℝ => (fderiv ℝ (Function.uncurry F.φ) (t, θ)
          ((0:ℝ), EuclideanSpace.single j 1)).ofLp b) *
        (fun t : ℝ => (fderiv ℝ (Function.uncurry F.φ) (t, θ)
          ((0:ℝ), EuclideanSpace.single k 1)).ofLp c) *
        (fun t => M.cubicTensor (F.φ t θ) a b c) := by
    funext s
    rw [hcube s, hpartial s (EuclideanSpace.single i 1),
      hpartial s (EuclideanSpace.single j 1),
      hpartial s (EuclideanSpace.single k 1)]
    simp only [Finset.sum_apply, Pi.mul_apply]
  -- the derivative of the canonical form, by the product rule
  have key : HasDerivAt
      (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
        (fun t : ℝ => (fderiv ℝ (Function.uncurry F.φ) (t, θ)
          ((0:ℝ), EuclideanSpace.single i 1)).ofLp a) *
        (fun t : ℝ => (fderiv ℝ (Function.uncurry F.φ) (t, θ)
          ((0:ℝ), EuclideanSpace.single j 1)).ofLp b) *
        (fun t : ℝ => (fderiv ℝ (Function.uncurry F.φ) (t, θ)
          ((0:ℝ), EuclideanSpace.single k 1)).ofLp c) *
        (fun t => M.cubicTensor (F.φ t θ) a b c))
      (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
        (((fderiv ℝ (fun θ' => F.generator θ' a) θ (EuclideanSpace.single i 1) *
              (fderiv ℝ (Function.uncurry F.φ) ((0:ℝ), θ)
                ((0:ℝ), EuclideanSpace.single j 1)).ofLp b +
            (fderiv ℝ (Function.uncurry F.φ) ((0:ℝ), θ)
              ((0:ℝ), EuclideanSpace.single i 1)).ofLp a *
              fderiv ℝ (fun θ' => F.generator θ' b) θ (EuclideanSpace.single j 1)) *
            (fderiv ℝ (Function.uncurry F.φ) ((0:ℝ), θ)
              ((0:ℝ), EuclideanSpace.single k 1)).ofLp c +
          (fderiv ℝ (Function.uncurry F.φ) ((0:ℝ), θ)
            ((0:ℝ), EuclideanSpace.single i 1)).ofLp a *
            (fderiv ℝ (Function.uncurry F.φ) ((0:ℝ), θ)
              ((0:ℝ), EuclideanSpace.single j 1)).ofLp b *
            fderiv ℝ (fun θ' => F.generator θ' c) θ (EuclideanSpace.single k 1)) *
          M.cubicTensor (F.φ 0 θ) a b c +
        (fderiv ℝ (Function.uncurry F.φ) ((0:ℝ), θ)
          ((0:ℝ), EuclideanSpace.single i 1)).ofLp a *
          (fderiv ℝ (Function.uncurry F.φ) ((0:ℝ), θ)
            ((0:ℝ), EuclideanSpace.single j 1)).ofLp b *
          (fderiv ℝ (Function.uncurry F.φ) ((0:ℝ), θ)
            ((0:ℝ), EuclideanSpace.single k 1)).ofLp c *
          fderiv ℝ (fun θ' => M.cubicTensor θ' a b c) θ (F.generator θ))) 0 :=
    HasDerivAt.sum fun a _ => HasDerivAt.sum fun b _ => HasDerivAt.sum fun c _ =>
      (((hA a i).mul (hA b j)).mul (hA c k)).mul (hEd a b c)
  -- at t = 0 the flow is the identity
  have hid : F.φ 0 = (id : ParamSpace n → ParamSpace n) := funext F.identity
  have hA0 : ∀ v : ParamSpace n,
      fderiv ℝ (Function.uncurry F.φ) ((0:ℝ), θ) ((0:ℝ), v) = v := by
    intro v
    rw [← hpartial 0 v, hid, fderiv_id, ContinuousLinearMap.id_apply]
  -- assemble
  rw [hfun, fderiv_apply_one_eq_deriv, key.deriv, hA0 (EuclideanSpace.single i 1),
    hA0 (EuclideanSpace.single j 1), hA0 (EuclideanSpace.single k 1), F.identity θ]
  refine (halg _ _ _ _ _).trans ?_
  rw [hlinR (fderiv ℝ (fun θ' => M.cubicTensor θ' i j k) θ) (F.generator θ),
    show (∑ l : Fin n, (F.generator θ).ofLp l *
        fderiv ℝ (fun θ' => M.cubicTensor θ' i j k) θ (EuclideanSpace.single l 1)) =
      ∑ l : Fin n, F.generator θ l *
        fderiv ℝ (fun θ' => M.cubicTensor θ' i j k) θ (EuclideanSpace.single l 1) from
      Finset.sum_congr rfl fun l _ => rfl,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- Every divergence-preserving family has a generator that is an
information-geometric generator.

The hypotheses beyond `F` itself:
* `M₃`, `hM₃` — a third-order refinement of the model, needed for the
  Leibniz derivative of the Fisher matrix in the Killing expansion
  (exactly as in `killing_expansion` / `generator_preserves_cubic`);
* `hC` — differentiability of `θ ↦ cubicTensor θ a b c` on the domain.
  This is fourth-order regularity data that the model hierarchy does not
  provide, so it is bundled as a hypothesis. -/
noncomputable def DivergencePreservingFamily.toGenerator
    (F : M.DivergencePreservingFamily)
    (M₃ : ThriceDifferentiableModel n Ω)
    (hM₃ : M₃.toTwiceDifferentiableModel = M)
    (hC : ∀ θ ∈ M.paramDomain, ∀ a b c : Fin n,
      DifferentiableAt ℝ (fun θ' => M.cubicTensor θ' a b c) θ) :
    InfoGeometricGenerator M where
  vectorField := F.generator
  smooth := F.generator_smooth
  killing := fun _θ hθ i j =>
    (killing_expansion M₃ hM₃ F hθ i j).symm.trans
      (F.generator_killing hθ (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
  preserves_cubic := fun θ hθ i j k =>
    (cubic_expansion F (hC θ hθ) i j k).symm.trans
      (generator_preserves_cubic M₃ hM₃ F hθ
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
        (EuclideanSpace.single k 1))

-- ============================================================================
-- §7. Toward the Bijection (Reverse Map): Existence of the Flow
-- ============================================================================

/-! ### Integrating the generator

Given an `InfoGeometricGenerator`, the ODE dθ/dt = X(θ) must have a
global solution which, moreover, preserves the divergence.

**This is where completeness enters.** In Stone's theorem,
self-adjointness of A guarantees that exp(itA) exists globally as a
unitary operator — essential self-adjointness prevents "escape to
infinity."  The expected information-geometric analogue is Fisher
geodesic completeness: the Killing condition L_X g = 0 makes ‖X‖_g
constant along flow lines, so bounded speed plus completeness prevents
finite-time blowup, and a rigidity theorem ("the divergence is
determined by g and C") should upgrade the infinitesimal conditions
L_X g = L_X C = 0 to divergence preservation of the flow.

Neither the geodesic machinery (Christoffel symbols, the geodesic
equation) nor the rigidity theorem is formalized at this point of the
development, so the completeness hypothesis is stated *extrinsically*:
`FlowComplete` asserts exactly the conclusion of that future chain of
arguments — every generator integrates to a global divergence-preserving
flow.  (An earlier `GeodesicallyComplete` class asserted only the
existence of continuous curves through each point, which is vacuous —
constant curves satisfy it — and cannot support the theorem.) -/

/-- **Flow-completeness hypothesis.**

Every information-geometric generator integrates to a global,
divergence-preserving, smooth one-parameter flow whose velocity at
t = 0 is the given vector field.  This is the information-geometric
analogue of essential self-adjointness in Stone's theorem; deriving it
from Fisher geodesic completeness is future work (see the section
docstring). -/
class FlowComplete (M : TwiceDifferentiableModel n Ω) : Prop where
  complete : ∀ G : InfoGeometricGenerator M,
    ∃ φ : ℝ → ParamSpace n → ParamSpace n,
      (∀ t, ∀ θ ∈ M.paramDomain, φ t θ ∈ M.paramDomain) ∧
      (∀ t, ∀ θ₁ ∈ M.paramDomain, ∀ θ₂ ∈ M.paramDomain,
        M.klDiv (φ t θ₁) (φ t θ₂) = M.klDiv θ₁ θ₂) ∧
      (∀ s t θ, φ (s + t) θ = φ s (φ t θ)) ∧
      (∀ θ, φ 0 θ = θ) ∧
      ContDiff ℝ ⊤ (Function.uncurry φ) ∧
      ∀ θ, HasDerivAt (fun t => φ t θ) (G.vectorField θ) 0

/-- Under flow-completeness, every information-geometric generator
integrates to a global divergence-preserving family whose generator is
the given vector field. -/
theorem generator_integrates_to_family
    [FlowComplete M]
    (M₃ : ThriceDifferentiableModel n Ω)
    (hM₃ : M₃.toTwiceDifferentiableModel = M)
    (hC : ∀ θ ∈ M.paramDomain, ∀ a b c : Fin n,
      DifferentiableAt ℝ (fun θ' => M.cubicTensor θ' a b c) θ)
    (G : InfoGeometricGenerator M) :
    ∃ F : M.DivergencePreservingFamily, F.toGenerator M₃ hM₃ hC = G := by
  obtain ⟨φ, hdom, hdiv, hgrp, hid, hsm, hflow⟩ := FlowComplete.complete G
  refine ⟨⟨φ, hdom, hdiv, hgrp, hid, hsm⟩, ?_⟩
  apply InfoGeometricGenerator.ext_vectorField
  funext θ
  -- the generator of the constructed family is d/dt φ_t(θ)|₀ = X(θ)
  show fderiv ℝ (fun t => φ t θ) 0 1 = G.vectorField θ
  rw [fderiv_apply_one_eq_deriv]
  exact (hflow θ).deriv

-- ============================================================================
-- §8. The Information-Geometric Stone's Theorem
-- ============================================================================

/-- **The Information-Geometric Stone's Theorem (weak form).**

| Stone's Theorem                     | IG Stone's Theorem                      |
|-------------------------------------|-----------------------------------------|
| One-parameter unitary groups        | Divergence-preserving families          |
| Self-adjoint operators              | Info-geometric generators (L_Xg=L_XC=0) |
| Essential self-adjointness          | Flow completeness                       |
| U(t) = e^{itA}                      | φ_t = flow of X                         |
| Schrödinger equation                | Flow equation dθ/dt = X(θ)              |

When the statistical manifold is the pure state space of a Hilbert space
(with Fisher metric = 4 × Fubini-Study metric), this reduces to Stone's
theorem for one-parameter unitary groups. -/
theorem infoGeometric_stone_weak
    (M₃ : ThriceDifferentiableModel n Ω)
    (hM₃ : M₃.toTwiceDifferentiableModel = M)
    (hC : ∀ θ ∈ M.paramDomain, ∀ a b c : Fin n,
      DifferentiableAt ℝ (fun θ' => M.cubicTensor θ' a b c) θ) :
    ∀ F : M.DivergencePreservingFamily,
    ∃! G : InfoGeometricGenerator M,
      F.toGenerator M₃ hM₃ hC = G ∧
      (∃ F' : M.DivergencePreservingFamily,
        F'.toGenerator M₃ hM₃ hC = G ∧ ∀ t θ, F'.φ t θ = F.φ t θ) := by
  intro F
  refine ⟨F.toGenerator M₃ hM₃ hC, ⟨rfl, F, rfl, fun _ _ => rfl⟩, ?_⟩
  intro G ⟨hG, _⟩
  exact hG.symm

/-- Two smooth solutions of γ' = X(γ) with the same initial condition
    agree on a neighborhood of 0. Uses Grönwall via
    `dist_le_of_trajectories_ODE_of_mem` with δ = 0. -/
private lemma smooth_ode_local_unique
    {X : ParamSpace n → ParamSpace n} (hX : ContDiff ℝ ⊤ X)
    {γ₁ γ₂ : ℝ → ParamSpace n}
    (hγ₁ : ContDiff ℝ ⊤ γ₁) (hγ₂ : ContDiff ℝ ⊤ γ₂)
    (h_ode₁ : ∀ s, HasDerivAt γ₁ (X (γ₁ s)) s)
    (h_ode₂ : ∀ s, HasDerivAt γ₂ (X (γ₂ s)) s)
    (h₀ : γ₁ 0 = γ₂ 0) :
    ∃ ε > 0, ∀ s, |s| < ε → γ₁ s = γ₂ s := by
  set θ₀ := γ₁ 0
  -- ═══ Step 1: X is Lipschitz on closedBall θ₀ 1 ═══
  -- Smooth ⟹ fderiv continuous ⟹ ‖fderiv‖ bounded on compact ball ⟹ MVT
  obtain ⟨K, hK⟩ : ∃ K : NNReal, LipschitzOnWith K X (Metric.closedBall θ₀ 1) := by
    have h_diff : ∀ x ∈ Metric.closedBall θ₀ 1, DifferentiableAt ℝ X x :=
      fun x _ => (hX.differentiable (by simp)).differentiableAt
    have h_bdd : BddAbove ((fun x => ‖fderiv ℝ X x‖₊) '' Metric.closedBall θ₀ 1) :=
      (isCompact_closedBall θ₀ 1).bddAbove_image
        ((hX.continuous_fderiv (by simp)).nnnorm).continuousOn
    obtain ⟨C, hC⟩ := h_bdd
    exact ⟨C, Convex.lipschitzOnWith_of_nnnorm_fderiv_le h_diff
      (fun x hx => hC ⟨x, hx, rfl⟩) (convex_closedBall θ₀ 1)⟩
  -- ═══ Step 2: Both curves stay in the ball for small time ═══
  obtain ⟨ε₁, hε₁, h_stay₁⟩ : ∃ ε₁ > 0,
      ∀ s, |s| ≤ ε₁ → γ₁ s ∈ Metric.closedBall θ₀ 1 := by
    obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp
      hγ₁.continuous.continuousAt 1 one_pos
    refine ⟨δ / 2, by positivity, fun s hs => ?_⟩
    apply Metric.mem_closedBall.mpr
    -- θ₀ = γ₁ 0 by `set`, so goal is already dist (γ₁ s) (γ₁ 0) ≤ 1
    exact le_of_lt (hball (by rw [Real.dist_eq, sub_zero]; linarith))
  obtain ⟨ε₂, hε₂, h_stay₂⟩ : ∃ ε₂ > 0,
      ∀ s, |s| ≤ ε₂ → γ₂ s ∈ Metric.closedBall θ₀ 1 := by
    obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp
      hγ₂.continuous.continuousAt 1 one_pos
    -- hball : ∀ x, dist x 0 < δ → dist (γ₂ x) (γ₂ 0) < 1
    refine ⟨δ / 2, by positivity, fun s hs => ?_⟩
    -- Goal: γ₂ s ∈ closedBall θ₀ 1, i.e., dist (γ₂ s) θ₀ ≤ 1
    -- After `set θ₀ := γ₁ 0`, h₀ became θ₀ = γ₂ 0
    rw [Metric.mem_closedBall, h₀]
    -- Goal: dist (γ₂ s) (γ₂ 0) ≤ 1
    exact le_of_lt (hball (by rw [Real.dist_eq, sub_zero]; linarith))
  set ε := min ε₁ ε₂ with hε_def
  have hε : 0 < ε := lt_min hε₁ hε₂
  -- ═══ Step 3: Forward uniqueness on [0, ε] via Grönwall ═══
  have h_fwd : ∀ s ∈ Set.Icc 0 ε, γ₁ s = γ₂ s := by
    intro s hs
    have h_dist := dist_le_of_trajectories_ODE_of_mem
      (v := fun _ => X) (s := fun _ => Metric.closedBall θ₀ 1)
      (K := K) (δ := 0)
      (hv := fun _ _ => hK)
      (hf := hγ₁.continuous.continuousOn)
      (hf' := fun t _ => (h_ode₁ t).hasDerivWithinAt)
      (hfs := fun t ht => h_stay₁ t (by rw [abs_of_nonneg ht.1]; exact ht.2.le.trans (min_le_left _ _)))
      (hg := hγ₂.continuous.continuousOn)
      (hg' := fun t _ => (h_ode₂ t).hasDerivWithinAt)
      (hgs := fun t ht => h_stay₂ t (by rw [abs_of_nonneg ht.1]; exact ht.2.le.trans (min_le_right _ _)))
      (ha := by rw [← h₀, dist_self])
      s hs
    -- h_dist : dist (γ₁ s) (γ₂ s) ≤ 0 * exp(...) = 0
    simp only [zero_mul] at h_dist
    exact dist_eq_zero.mp (le_antisymm h_dist dist_nonneg)
  -- ═══ Step 4: Backward uniqueness on [0, ε] for reversed curves ═══
  have h_bwd : ∀ s ∈ Set.Icc 0 ε, γ₁ (-s) = γ₂ (-s) := by
    -- γ̃ᵢ(t) := γᵢ(-t) solves γ̃' = -X(γ̃), γ̃(0) = θ₀
    -- -X is Lipschitz on the same ball with same K
    -- Same Grönwall argument
    intro s hs
    set f := γ₁ ∘ Neg.neg
    set g := γ₂ ∘ Neg.neg
    have hf_ode : ∀ t, HasDerivAt f (-X (f t)) t := by
      intro t
      have h := (h_ode₁ (-t)).scomp t (hasDerivAt_neg t)
      simp only [neg_one_smul] at h
      exact h
    have hg_ode : ∀ t, HasDerivAt g (-X (g t)) t := by
      intro t
      have h := (h_ode₂ (-t)).scomp t (hasDerivAt_neg t)
      simp only [neg_one_smul] at h
      exact h
    have hK_neg : LipschitzOnWith K (fun x => -X x) (Metric.closedBall θ₀ 1) := by
      intro x hx y hy
      calc edist (-X x) (-X y)
          = edist (X x) (X y) := by rw [edist_neg_neg]
        _ ≤ K * edist x y := hK hx hy
    have h_dist := dist_le_of_trajectories_ODE_of_mem
      (v := fun _ x => -X x) (s := fun _ => Metric.closedBall θ₀ 1)
      (K := K) (δ := 0)
      (hv := fun _ _ => hK_neg)
      (hf := (hγ₁.comp contDiff_neg).continuous.continuousOn)
      (hf' := fun t _ => (hf_ode t).hasDerivWithinAt)
      (hfs := fun t ht => h_stay₁ (-t) (by rw [abs_neg, abs_of_nonneg ht.1]; exact ht.2.le.trans (min_le_left _ _)))
      (hg := (hγ₂.comp contDiff_neg).continuous.continuousOn)
      (hg' := fun t _ => (hg_ode t).hasDerivWithinAt)
      (hgs := fun t ht => h_stay₂ (-t) (by rw [abs_neg, abs_of_nonneg ht.1]; exact ht.2.le.trans (min_le_right _ _)))
      (ha := by simp [← h₀]; rfl)
      s hs
    simp only [zero_mul, Function.comp] at h_dist
    exact dist_eq_zero.mp (le_antisymm h_dist dist_nonneg)
  -- ═══ Combine forward and backward ═══
  exact ⟨ε, hε, fun s hs => by
    by_cases h : 0 ≤ s
    · exact h_fwd s ⟨h, (abs_lt.mp hs).2.le⟩
    · simp only [not_le] at h
      have := h_bwd (-s) ⟨by linarith, by linarith [(abs_lt.mp hs).1]⟩
      rwa [neg_neg] at this⟩


/-- **Uniqueness of the flow**: Two divergence-preserving families with
the same infinitesimal generator have identical flows.

This is ODE uniqueness (Picard–Lindelöf) applied to dθ/dt = X(θ):
both families solve the same smooth ODE with the same initial condition
φ_0 = id, so they agree for all time. No completeness hypothesis needed. -/
lemma infoGeometric_stone_unique
    (F₁ F₂ : M.DivergencePreservingFamily)
    (M₃ : ThriceDifferentiableModel n Ω)
    (hM₃ : M₃.toTwiceDifferentiableModel = M)
    (hC : ∀ θ ∈ M.paramDomain, ∀ a b c : Fin n,
      DifferentiableAt ℝ (fun θ' => M.cubicTensor θ' a b c) θ)
    (h : F₁.toGenerator M₃ hM₃ hC = F₂.toGenerator M₃ hM₃ hC) :
    ∀ t θ, F₁.φ t θ = F₂.φ t θ := by
  have hgen : ∀ θ, F₁.generator θ = F₂.generator θ :=
    fun θ => congr_fun (congr_arg InfoGeometricGenerator.vectorField h) θ
  intro t θ
  set S := {t : ℝ | F₁.φ t θ = F₂.φ t θ}
  suffices hS : S = Set.univ from Set.eq_univ_iff_forall.mp hS t
  -- 0 ∈ S
  have h0 : (0 : ℝ) ∈ S := by
    simp only [S, Set.mem_setOf_eq, F₁.identity, F₂.identity]
  -- S is closed: both sides are continuous in t
  have hclosed : IsClosed S :=
    isClosed_eq
      (F₁.smooth.comp (contDiff_id.prodMk contDiff_const)).continuous
      (F₂.smooth.comp (contDiff_id.prodMk contDiff_const)).continuous
  -- S is open: local ODE uniqueness at each point of S
  have hopen : IsOpen S := by
      rw [isOpen_iff_forall_mem_open]
      intro t₀ ht₀
      -- At t₀, both flows pass through θ₀ := F₁.φ t₀ θ = F₂.φ t₀ θ
      set θ₀ := F₁.φ t₀ θ
      have h_ode_unique : ∃ ε > 0, ∀ s, |s| < ε →
          F₁.φ s θ₀ = F₂.φ s θ₀ := by
        apply smooth_ode_local_unique (X := F₁.generator)
        -- hX: generator is smooth
        · exact F₁.generator_smooth
        -- hγ₁: s ↦ F₁.φ s θ₀ is smooth
        · exact F₁.smooth.comp (contDiff_id.prodMk contDiff_const)
        -- hγ₂: s ↦ F₂.φ s θ₀ is smooth
        · exact F₂.smooth.comp (contDiff_id.prodMk contDiff_const)
        -- h_ode₁: F₁ solves γ' = X(γ)
        · intro s
          have h_diff : DifferentiableAt ℝ (fun t => F₁.φ t θ₀) s :=
            ((F₁.smooth.comp (contDiff_id.prodMk contDiff_const)).differentiable
              (by simp)).differentiableAt
          have h := h_diff.hasFDerivAt.hasDerivAt
          rwa [F₁.flow_equation θ₀ s] at h
        -- h_ode₂: F₂ solves the SAME ODE (generator = F₁.generator by hgen)
        · intro s
          have h_diff : DifferentiableAt ℝ (fun t => F₂.φ t θ₀) s :=
            ((F₂.smooth.comp (contDiff_id.prodMk contDiff_const)).differentiable
              (by simp)).differentiableAt
          have h := h_diff.hasFDerivAt.hasDerivAt
          rw [F₂.flow_equation θ₀ s] at h
          rwa [← hgen] at h
        -- h₀: same initial condition
        · rw [F₁.identity, F₂.identity]
      obtain ⟨ε, hε, h_agree⟩ := h_ode_unique
      refine ⟨Set.Ioo (t₀ - ε) (t₀ + ε), fun t' ht' => ?_, isOpen_Ioo,
        Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩⟩
      -- Show t' ∈ S, i.e., F₁.φ t' θ = F₂.φ t' θ
      show F₁.φ t' θ = F₂.φ t' θ
      have h_abs : |t' - t₀| < ε := by
        rw [abs_lt]; constructor <;> linarith [(Set.mem_Ioo.mp ht').1,
                                               (Set.mem_Ioo.mp ht').2]
      -- Group law: Fᵢ.φ t' θ = Fᵢ.φ (t'-t₀) θ₀
      have h1 : F₁.φ t' θ = F₁.φ (t' - t₀) θ₀ := by
        have := F₁.group_law (t' - t₀) t₀ θ
        simp only [sub_add_cancel] at this; exact this
      have h2 : F₂.φ t' θ = F₂.φ (t' - t₀) θ₀ := by
        have := F₂.group_law (t' - t₀) t₀ θ
        simp only [sub_add_cancel] at this; rwa [← ht₀] at this
      rw [h1, h2]; exact h_agree _ h_abs
  -- S is clopen and nonempty in the connected space ℝ, hence S = univ
  exact (isClopen_iff.mp ⟨hclosed, hopen⟩).resolve_left
    (Set.Nonempty.ne_empty ⟨0, h0⟩)

/-- **Existence of the flow**: Under flow-completeness, every
info-geometric generator integrates to a global divergence-preserving
family. -/
lemma infoGeometric_stone_exists
    [FlowComplete M]
    (M₃ : ThriceDifferentiableModel n Ω)
    (hM₃ : M₃.toTwiceDifferentiableModel = M)
    (hC : ∀ θ ∈ M.paramDomain, ∀ a b c : Fin n,
      DifferentiableAt ℝ (fun θ' => M.cubicTensor θ' a b c) θ)
    (G : InfoGeometricGenerator M) :
    ∃ F : M.DivergencePreservingFamily, F.toGenerator M₃ hM₃ hC = G :=
  generator_integrates_to_family M₃ hM₃ hC G

/-- **The Information-Geometric Stone's Theorem.**

Under flow-completeness, the map `toGenerator` is a bijection
(up to pointwise flow equality) between divergence-preserving
one-parameter families and info-geometric generators.

| Direction   | Content                        | Analogue in Stone's theorem     |
|-------------|--------------------------------|---------------------------------|
| Surjective  | Every generator has a flow     | e^{itA} exists (self-adjoint A) |
| Injective   | Generator determines the flow  | A determines U(t) uniquely      |
-/
theorem infoGeometric_stone [FlowComplete M]
    (M₃ : ThriceDifferentiableModel n Ω)
    (hM₃ : M₃.toTwiceDifferentiableModel = M)
    (hC : ∀ θ ∈ M.paramDomain, ∀ a b c : Fin n,
      DifferentiableAt ℝ (fun θ' => M.cubicTensor θ' a b c) θ) :
    (∀ G : InfoGeometricGenerator M,
      ∃ F : M.DivergencePreservingFamily, F.toGenerator M₃ hM₃ hC = G) ∧
    (∀ F₁ F₂ : M.DivergencePreservingFamily,
      F₁.toGenerator M₃ hM₃ hC = F₂.toGenerator M₃ hM₃ hC →
      ∀ t θ, F₁.φ t θ = F₂.φ t θ) :=
  ⟨fun G => infoGeometric_stone_exists M₃ hM₃ hC G,
   fun F₁ F₂ h => infoGeometric_stone_unique F₁ F₂ M₃ hM₃ hC h⟩

end TwiceDifferentiableModel

end Spectra.InformationGeometry
