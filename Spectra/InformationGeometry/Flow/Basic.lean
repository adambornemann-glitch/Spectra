/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Flow.Generator

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Algebra.BigOperators.WithTop
-- For Stone-Like Uniqueness --
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Topology.Order.Compact
-- For the bounded-domain refutation of global flow-completeness --
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The Information-Geometric Stone's Theorem

The correspondence between divergence-preserving one-parameter families and
their infinitesimal generators (Killing + cubic-preserving vector fields).
The generator direction is unconditional (`DivergencePreservingFamily.toGenerator`);
the integration direction holds under the `FlowComplete` hypothesis, and is
unique on the domain regardless (`infoGeometric_stone`).

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

* Smoothness throughout is `ContDiff ℝ (⊤ : ℕ∞)`, i.e. `C^∞`.  (In
  current mathlib the bare exponent `⊤` is `ω`, *analyticity* — not what
  these structures mean.)

* The completeness hypothesis is `FlowComplete` (a `Prop`-valued `def`,
  taken as an explicit hypothesis): every info-geometric generator
  integrates to a global divergence-preserving family whose generator
  agrees with the given field *on the parameter domain*.  The
  domain-relative form is forced: a generator's field is constrained
  only on the domain, and demanding a global flow with prescribed
  velocity at every point of `ℝⁿ` is not merely unprovable but
  *refutable* once the domain is bounded —
  `not_forall_hasGlobalFlow_of_isBounded` constructs a generator that
  vanishes near the domain (Killing and cubic conditions hold for free)
  yet grows quadratically far out, so its trajectories blow up in
  finite time.  `FlowComplete` remains a genuine hypothesis, the
  analogue of essential self-adjointness in Stone's theorem: the
  flat location model on a bounded interval with `X = d/dθ` — the
  mirror of the momentum operator on `(0,1)`, symmetric with no
  self-adjoint extension — is Killing and cubic-preserving but
  generates no domain-preserving family.  Deriving `FlowComplete` for
  concrete models from Fisher geodesic completeness (conservation of
  `‖X‖_g` along flow lines, divergence rigidity) is future work; the
  definition isolates exactly what the surjectivity half of the Stone
  correspondence needs.  (It replaces an earlier vacuous
  `GeodesicallyComplete` class — satisfied by constant curves — and an
  earlier global `FlowComplete` class, unsatisfiable as above.)
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
  smooth : ContDiff ℝ (⊤ : ℕ∞) vectorField
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

/-- The generator is the derivative of the uncurried flow in the time direction. -/
private lemma DivergencePreservingFamily.generator_eq_fderiv_uncurry
    (F : M.DivergencePreservingFamily) :
    F.generator =
      fun θ => fderiv ℝ (Function.uncurry F.φ) (0, θ)
        ((1 : ℝ), (0 : ParamSpace n)) := by
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

/-- The parameter derivative of a time-slice is the uncurried derivative
applied to the parameter-direction vector. -/
private lemma DivergencePreservingFamily.fderiv_phi_eq_fderiv_uncurry
    (F : M.DivergencePreservingFamily) (s : ℝ) {θ : ParamSpace n}
    (v : ParamSpace n) :
    fderiv ℝ (F.φ s) θ v =
      fderiv ℝ (Function.uncurry F.φ) (s, θ) ((0 : ℝ), v) := by
  have hmk : HasFDerivAt (fun θ'' : ParamSpace n => ((s, θ'') : ℝ × ParamSpace n))
      ((0 : ParamSpace n →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ParamSpace n))) θ :=
    (hasFDerivAt_const s θ).prodMk (hasFDerivAt_id θ)
  have hcomp : HasFDerivAt (F.φ s)
      ((fderiv ℝ (Function.uncurry F.φ) (s, θ)).comp
        ((0 : ParamSpace n →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ParamSpace n)))) θ :=
    (((F.smooth.differentiable (by simp)) (s, θ)).hasFDerivAt).comp θ hmk
  rw [hcomp.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply]

/-- The generator of a divergence-preserving family is a smooth vector
field: X(θ) = D(uncurry φ)(0,θ)(1,0) is the composition of the C^∞ map
`fderiv ℝ (uncurry φ)` with smooth injections and evaluations. -/
lemma DivergencePreservingFamily.generator_smooth
    (F : M.DivergencePreservingFamily) :
    ContDiff ℝ (⊤ : ℕ∞) F.generator := by
  rw [DivergencePreservingFamily.generator_eq_fderiv_uncurry F]
  have hDg : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (Function.uncurry F.φ)) :=
    F.smooth.fderiv_right (m := (⊤ : ℕ∞)) (by exact_mod_cast le_top)
  exact (ContinuousLinearMap.apply ℝ (ParamSpace n)
        ((1 : ℝ), (0 : ParamSpace n))).contDiff |>.comp
    (hDg.comp (contDiff_const.prodMk contDiff_id))

/-- Expand a continuous linear functional on `ParamSpace n` in the standard basis. -/
private lemma continuousLinearMap_apply_eq_sum_single
    (L : ParamSpace n →L[ℝ] ℝ) (x : ParamSpace n) :
    L x = ∑ k : Fin n, x.ofLp k * L (EuclideanSpace.single k 1) := by
  have hbasis : x = ∑ k : Fin n, x.ofLp k • EuclideanSpace.single k 1 := by
    ext p
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  conv_lhs => rw [hbasis, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- The standard-basis delta collapses a finite coordinate sum. -/
private lemma sum_single_ofLp_mul (f : Fin n → ℝ) (c : Fin n) :
    (∑ b : Fin n, (EuclideanSpace.single c 1 : ParamSpace n).ofLp b * f b) = f c := by
  simp only [PiLp.ofLp_single, Pi.single_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- Algebraic collapse for the derivative of a pulled-back cubic form at the identity.

The three basis vectors contribute Kronecker deltas, reducing the product-rule triple sum to
the three derivative-of-the-Jacobian terms plus the derivative of the tensor coefficient. -/
private lemma cubic_delta_product_rule_collapse
    (i j k : Fin n) (P Q R : Fin n → ℝ) (S E : Fin n → Fin n → Fin n → ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
      (((P a * (EuclideanSpace.single j 1 : ParamSpace n).ofLp b
            + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a * Q b)
              * (EuclideanSpace.single k 1 : ParamSpace n).ofLp c
          + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a
              * (EuclideanSpace.single j 1 : ParamSpace n).ofLp b * R c)
        * E a b c
        + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a
            * (EuclideanSpace.single j 1 : ParamSpace n).ofLp b
            * (EuclideanSpace.single k 1 : ParamSpace n).ofLp c * S a b c))
    = (∑ l : Fin n, E i l k * Q l) + (∑ l : Fin n, E l j k * P l)
        + (∑ l : Fin n, E i j l * R l) + S i j k := by
  have inner1 : ∀ a b : Fin n,
      (∑ c : Fin n,
        (((P a * (EuclideanSpace.single j 1 : ParamSpace n).ofLp b
              + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a * Q b)
                * (EuclideanSpace.single k 1 : ParamSpace n).ofLp c
            + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a
                * (EuclideanSpace.single j 1 : ParamSpace n).ofLp b * R c)
          * E a b c
          + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a
              * (EuclideanSpace.single j 1 : ParamSpace n).ofLp b
              * (EuclideanSpace.single k 1 : ParamSpace n).ofLp c * S a b c))
      = (P a * (EuclideanSpace.single j 1 : ParamSpace n).ofLp b
            + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a * Q b) * E a b k
        + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a
            * (EuclideanSpace.single j 1 : ParamSpace n).ofLp b * (∑ c : Fin n, R c * E a b c)
        + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a
            * (EuclideanSpace.single j 1 : ParamSpace n).ofLp b * S a b k := by
    intro a b
    have hsplit : ∀ c : Fin n,
        (((P a * (EuclideanSpace.single j 1 : ParamSpace n).ofLp b
              + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a * Q b)
                * (EuclideanSpace.single k 1 : ParamSpace n).ofLp c
            + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a
                * (EuclideanSpace.single j 1 : ParamSpace n).ofLp b * R c)
          * E a b c
          + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a
              * (EuclideanSpace.single j 1 : ParamSpace n).ofLp b
              * (EuclideanSpace.single k 1 : ParamSpace n).ofLp c * S a b c)
        = (EuclideanSpace.single k 1 : ParamSpace n).ofLp c *
            ((P a * (EuclideanSpace.single j 1 : ParamSpace n).ofLp b
              + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a * Q b) * E a b c)
          + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a
              * (EuclideanSpace.single j 1 : ParamSpace n).ofLp b * (R c * E a b c)
          + (EuclideanSpace.single k 1 : ParamSpace n).ofLp c *
              ((EuclideanSpace.single i 1 : ParamSpace n).ofLp a
                * (EuclideanSpace.single j 1 : ParamSpace n).ofLp b * S a b c) :=
      fun c => by ring
    refine (Finset.sum_congr rfl fun c _ => hsplit c).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_single_ofLp_mul (fun c => (P a * (EuclideanSpace.single j 1 : ParamSpace n).ofLp b
        + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a * Q b) * E a b c) k,
      ← Finset.mul_sum,
      sum_single_ofLp_mul (fun c => (EuclideanSpace.single i 1 : ParamSpace n).ofLp a
        * (EuclideanSpace.single j 1 : ParamSpace n).ofLp b * S a b c) k]
  have inner2 : ∀ a : Fin n,
      (∑ b : Fin n,
        ((P a * (EuclideanSpace.single j 1 : ParamSpace n).ofLp b
            + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a * Q b) * E a b k
          + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a
              * (EuclideanSpace.single j 1 : ParamSpace n).ofLp b * (∑ c : Fin n, R c * E a b c)
          + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a
              * (EuclideanSpace.single j 1 : ParamSpace n).ofLp b * S a b k))
      = P a * E a j k
        + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a * (∑ b : Fin n, Q b * E a b k)
        + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a * (∑ c : Fin n, R c * E a j c)
        + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a * S a j k := by
    intro a
    have hsplit2 : ∀ b : Fin n,
        ((P a * (EuclideanSpace.single j 1 : ParamSpace n).ofLp b
            + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a * Q b) * E a b k
          + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a
              * (EuclideanSpace.single j 1 : ParamSpace n).ofLp b * (∑ c : Fin n, R c * E a b c)
          + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a
              * (EuclideanSpace.single j 1 : ParamSpace n).ofLp b * S a b k)
        = (EuclideanSpace.single j 1 : ParamSpace n).ofLp b * (P a * E a b k)
          + (EuclideanSpace.single i 1 : ParamSpace n).ofLp a * (Q b * E a b k)
          + (EuclideanSpace.single j 1 : ParamSpace n).ofLp b *
              ((EuclideanSpace.single i 1 : ParamSpace n).ofLp a * (∑ c : Fin n, R c * E a b c))
          + (EuclideanSpace.single j 1 : ParamSpace n).ofLp b *
              ((EuclideanSpace.single i 1 : ParamSpace n).ofLp a * S a b k) :=
      fun b => by ring
    refine (Finset.sum_congr rfl fun b _ => hsplit2 b).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_single_ofLp_mul (fun b => P a * E a b k) j,
      ← Finset.mul_sum,
      sum_single_ofLp_mul (fun b => (EuclideanSpace.single i 1 : ParamSpace n).ofLp a
        * (∑ c : Fin n, R c * E a b c)) j,
      sum_single_ofLp_mul (fun b => (EuclideanSpace.single i 1 : ParamSpace n).ofLp a
        * S a b k) j]
  refine (Finset.sum_congr rfl fun a _ =>
    ((Finset.sum_congr rfl fun b _ => inner1 a b).trans (inner2 a))).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_single_ofLp_mul (fun a => ∑ b : Fin n, Q b * E a b k) i,
    sum_single_ofLp_mul (fun a => ∑ c : Fin n, R c * E a j c) i,
    sum_single_ofLp_mul (fun a => S a j k) i,
    show (∑ a : Fin n, P a * E a j k) = ∑ l : Fin n, E l j k * P l from
      Finset.sum_congr rfl fun l _ => mul_comm _ _,
    show (∑ b : Fin n, Q b * E i b k) = ∑ l : Fin n, E i l k * Q l from
      Finset.sum_congr rfl fun l _ => mul_comm _ _,
    show (∑ c : Fin n, R c * E i j c) = ∑ l : Fin n, E i j l * R l from
      Finset.sum_congr rfl fun l _ => mul_comm _ _]
  ring

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
    exact DivergencePreservingFamily.fderiv_phi_eq_fderiv_uncurry
      (M := M) F s (θ := θ) v
  -- t-slice at any base point: X(θ') = dΦ(0,θ')·(1,0)
  have _hgen : ∀ θ' : ParamSpace n,
      F.generator θ' =
      fderiv ℝ (Function.uncurry F.φ) ((0:ℝ), θ') ((1:ℝ), (0:ParamSpace n)) := by
    intro θ'
    exact congr_fun
      (DivergencePreservingFamily.generator_eq_fderiv_uncurry (M := M) F) θ'
  have hgen_eq : (fun θ' : ParamSpace n => F.generator θ') =
      fun θ' : ParamSpace n =>
        fderiv ℝ (Function.uncurry F.φ) ((0:ℝ), θ') ((1:ℝ), (0:ParamSpace n)) :=
    DivergencePreservingFamily.generator_eq_fderiv_uncurry (M := M) F
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
  -- §4. Canonical-form derivative and assembly
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
  refine (cubic_delta_product_rule_collapse i j k _ _ _ _ _).trans ?_
  rw [continuousLinearMap_apply_eq_sum_single
      (fderiv ℝ (fun θ' => M.cubicTensor θ' i j k) θ) (F.generator θ),
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

**This is where completeness enters — and where a subtlety lives.**  In
Stone's theorem, self-adjointness of A guarantees that exp(itA) exists
globally as a unitary operator — essential self-adjointness prevents
"escape to infinity."  The expected information-geometric analogue is
Fisher geodesic completeness: the Killing condition L_X g = 0 makes
‖X‖_g constant along flow lines, so bounded speed plus completeness
prevents finite-time blowup, and a rigidity theorem ("the divergence is
determined by g and C") should upgrade the infinitesimal conditions
L_X g = L_X C = 0 to divergence preservation of the flow.

The subtlety: a generator's vector field carries geometric content only
*on* `M.paramDomain`; off the domain it is arbitrary smooth data.  So
the completeness hypothesis must not demand anything of the flow off the
domain.  Demanding a global flow with velocity `X θ` at *every*
`θ : ℝⁿ` — as an earlier `class FlowComplete` did — is not merely
unprovable but false whenever the domain is bounded:
`not_forall_hasGlobalFlow_of_isBounded` below refutes it by exhibiting a
generator that vanishes on a neighborhood of the domain (so the Killing
and cubic conditions hold for free) but grows quadratically far out
along a coordinate axis, so that its trajectories blow up in finite
time.  Hypotheses over such a class would have been vacuous for every
bounded-domain model.

`FlowComplete` therefore asks only for what the geometry can see:
a global divergence-preserving family whose generator agrees with the
given field on the domain.  Neither the geodesic machinery (Christoffel
symbols, the geodesic equation) nor the rigidity theorem is formalized
at this point of the development, so this remains an *extrinsic*
hypothesis — and a genuine one, not a theorem-in-waiting for arbitrary
`M`: the flat location model on a bounded interval with `X = d/dθ` (the
information-geometric mirror of the momentum operator on `(0,1)`,
symmetric with no self-adjoint extension) is Killing and
cubic-preserving, but no domain-preserving family realizes it.  (An
earlier `GeodesicallyComplete` class asserted only the existence of
continuous curves through each point, which is vacuous — constant curves
satisfy it — and cannot support the theorem.) -/

/-- **Global integration of generators is impossible for bounded domains.**

If `0 < n` and the parameter domain is bounded, there is *no* assignment,
to every info-geometric generator, of a global flow (group law, identity,
prescribed velocity at every point of `ℝⁿ`): the witness generator
vanishes on a neighborhood of the domain — hence is Killing and
cubic-preserving for trivial reasons — and equals `(θ 0)² • e₀` far out
along the `0`-th axis, where its trajectories blow up in finite time.

This is why `FlowComplete` constrains the flow's generator only on the
parameter domain: the conjunction refuted here is (a weakening of) the
earlier global formulation of flow-completeness, which was therefore
unsatisfiable for every bounded-domain model. -/
theorem not_forall_hasGlobalFlow_of_isBounded
    (hn : 0 < n) (hbdd : Bornology.IsBounded M.paramDomain) :
    ¬ ∀ G : InfoGeometricGenerator M,
        ∃ φ : ℝ → ParamSpace n → ParamSpace n,
          (∀ s t θ, φ (s + t) θ = φ s (φ t θ)) ∧
          (∀ θ, φ 0 θ = θ) ∧
          (∀ θ, HasDerivAt (fun t => φ t θ) (G.vectorField θ) 0) := by
  intro hall
  -- ═══ Step 0: a nonnegative radius bounding the domain ═══
  obtain ⟨R₀, hR₀⟩ := hbdd.subset_closedBall 0
  set R : ℝ := max R₀ 0 with _hR_def
  have hR0 : (0 : ℝ) ≤ R := le_max_right _ _
  have hsub : M.paramDomain ⊆ Metric.closedBall 0 R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  set i₀ : Fin n := ⟨0, hn⟩ with _hi₀_def
  -- ═══ Step 1: the field X θ = f(θ i₀) • e₀; f vanishes on (-∞, R+1],
  --     equals s² on [R+2, ∞) ═══
  set f : ℝ → ℝ := fun s => Real.smoothTransition (s - (R + 1)) * s ^ 2 with hf_def
  have hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) fun s : ℝ => Real.smoothTransition (s - (R + 1)) :=
      Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)
    exact h1.mul (contDiff_id.pow 2)
  have hf_nonneg : ∀ s, 0 ≤ f s := fun s =>
    mul_nonneg (Real.smoothTransition.nonneg _) (sq_nonneg s)
  have hf_zero : ∀ s ≤ R + 1, f s = 0 := fun s hs => by
    simp [hf_def, Real.smoothTransition.zero_of_nonpos
      (by linarith : s - (R + 1) ≤ 0)]
  have hf_sq : ∀ s, R + 2 ≤ s → f s = s ^ 2 := fun s hs => by
    simp [hf_def, Real.smoothTransition.one_of_one_le
      (by linarith : 1 ≤ s - (R + 1))]
  set X : ParamSpace n → ParamSpace n :=
    fun θ => f (θ i₀) • EuclideanSpace.single i₀ 1 with hX_def
  -- X vanishes on the open half-space U ⊇ paramDomain
  have hU_open : IsOpen {θ : ParamSpace n | θ i₀ < R + 1} := by
    have : {θ : ParamSpace n | θ i₀ < R + 1} =
        (⇑(EuclideanSpace.proj i₀ : ParamSpace n →L[ℝ] ℝ)) ⁻¹' Set.Iio (R + 1) := by
      ext θ; simp [EuclideanSpace.coe_proj]
    rw [this]
    exact isOpen_Iio.preimage (EuclideanSpace.proj i₀ :
      ParamSpace n →L[ℝ] ℝ).continuous
  have hXU : ∀ θ : ParamSpace n, θ i₀ < R + 1 → X θ = 0 := fun θ hθ => by
    rw [hX_def]; dsimp only
    rw [hf_zero (θ i₀) hθ.le, zero_smul]
  have hdomU : ∀ θ ∈ M.paramDomain, θ i₀ < R + 1 := by
    intro θ hθ
    have hnorm : ‖θ‖ ≤ R := by
      have := hsub hθ
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    have habs : |θ i₀| ≤ ‖θ‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le θ i₀
    linarith [le_trans (le_abs_self (θ i₀)) (habs.trans hnorm)]
  have hXval : ∀ θ ∈ M.paramDomain, ∀ k : Fin n, X θ k = 0 := by
    intro θ hθ k
    rw [hXU θ (hdomU θ hθ)]; rfl
  have hXfderiv : ∀ θ ∈ M.paramDomain, ∀ k : Fin n,
      fderiv ℝ (fun θ' => X θ' k) θ = 0 := by
    intro θ hθ k
    have hev : (fun θ' => X θ' k) =ᶠ[𝓝 θ] fun _ => (0 : ℝ) := by
      filter_upwards [hU_open.mem_nhds (hdomU θ hθ)] with θ' hθ'
      rw [hXU θ' hθ']; rfl
    rw [hev.fderiv_eq, (hasFDerivAt_const (0 : ℝ) θ).fderiv]
  -- ═══ Step 2: X is an info-geometric generator ═══
  have hX_smooth : ContDiff ℝ (⊤ : ℕ∞) X := by
    have hproj : ContDiff ℝ (⊤ : ℕ∞) fun θ : ParamSpace n => θ i₀ := by
      simpa [EuclideanSpace.coe_proj] using
        (EuclideanSpace.proj i₀ : ParamSpace n →L[ℝ] ℝ).contDiff
    exact (hf_smooth.comp hproj).smul contDiff_const
  obtain ⟨φ, hgrp, hid, hvel₀⟩ := hall
    { vectorField := X
      smooth := hX_smooth
      killing := by
        intro θ hθ i j
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hXval θ hθ k, hXfderiv θ hθ k]
        simp
      preserves_cubic := by
        intro θ hθ i j k
        refine Finset.sum_eq_zero fun l _ => ?_
        rw [hXval θ hθ l, hXfderiv θ hθ l]
        simp }
  have hvel : ∀ θ : ParamSpace n, HasDerivAt (fun t => φ t θ) (X θ) 0 := hvel₀
  -- ═══ Step 3: velocity at all times, via the group law ═══
  have hvel_all : ∀ (θ' : ParamSpace n) (t : ℝ),
      HasDerivAt (fun s => φ s θ') (X (φ t θ')) t := by
    intro θ' t
    have h_eq : (fun s => φ s θ') = fun s => φ (s - t) (φ t θ') := by
      funext s; rw [← hgrp (s - t) t θ', sub_add_cancel]
    rw [h_eq]
    set g := fun s => φ s (φ t θ') with _hg_def
    set fs := fun s : ℝ => s - t with hfs_def
    have hg : HasFDerivAt g
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (X (φ t θ'))) (fs t) := by
      simp only [hfs_def, sub_self]
      exact (hvel (φ t θ')).hasFDerivAt
    have hf : HasFDerivAt fs (ContinuousLinearMap.id ℝ ℝ) t :=
      hasFDerivAt_sub_const t
    have h_comp := hg.comp t hf
    rw [show g ∘ fs = fun s => φ (s - t) (φ t θ') from rfl] at h_comp
    rwa [ContinuousLinearMap.comp_id] at h_comp
  -- ═══ Step 4: the escaping trajectory u(t) = φ_t(θ₀) · e₀ ═══
  set θ₀ : ParamSpace n := (R + 2) • EuclideanSpace.single i₀ 1 with hθ₀_def
  have hθ₀i : θ₀ i₀ = R + 2 := by
    rw [hθ₀_def]
    simp [PiLp.smul_apply, PiLp.single_eq_same]
  set u : ℝ → ℝ := fun t => φ t θ₀ i₀ with hu_def
  have hXi : ∀ p : ParamSpace n, X p i₀ = f (p i₀) := by
    intro p
    rw [hX_def]; dsimp only
    simp [PiLp.smul_apply, PiLp.single_eq_same]
  have hu_deriv : ∀ t, HasDerivAt u (f (u t)) t := by
    intro t
    have h := (EuclideanSpace.proj i₀ :
      ParamSpace n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t (hvel_all θ₀ t)
    have hfn : (⇑(EuclideanSpace.proj i₀ : ParamSpace n →L[ℝ] ℝ) ∘
        fun s => φ s θ₀) = u := by
      funext s; simp [EuclideanSpace.coe_proj, hu_def]
    have hval : (EuclideanSpace.proj i₀ : ParamSpace n →L[ℝ] ℝ) (X (φ t θ₀))
        = f (u t) := by
      simp [hXi, hu_def]
    rw [hfn, hval] at h
    exact h
  -- monotonicity and lower bound: u(t) ≥ R+2 for t ≥ 0
  have humono : Monotone u :=
    monotone_of_deriv_nonneg (fun t => (hu_deriv t).differentiableAt)
      (fun t => by rw [(hu_deriv t).deriv]; exact hf_nonneg _)
  have hu0 : u 0 = R + 2 := by
    rw [hu_def]; dsimp only
    rw [hid θ₀, hθ₀i]
  have hu_ge : ∀ t, 0 ≤ t → R + 2 ≤ u t := fun t ht => hu0 ▸ humono ht
  have hR2 : (0 : ℝ) < R + 2 := by linarith
  -- on [0, (R+2)⁻¹] the quantity (u t)⁻¹ + t has derivative 0 …
  set T : ℝ := (R + 2)⁻¹ with hT_def
  have hT_pos : 0 < T := inv_pos.mpr hR2
  have hH_deriv : ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivAt (fun s => (u s)⁻¹ + s) 0 t := by
    intro t ht
    have hut : R + 2 ≤ u t := hu_ge t ht.1
    have hut_pos : 0 < u t := lt_of_lt_of_le hR2 hut
    have hinv : HasDerivAt (fun s => (u s)⁻¹)
        (-(f (u t)) / u t ^ 2) t := (hu_deriv t).inv hut_pos.ne'
    have hne : -(f (u t)) / u t ^ 2 = -1 := by
      rw [hf_sq (u t) hut]
      field_simp
    rw [hne] at hinv
    have hsum := hinv.add (hasDerivAt_id t)
    rw [show (-1 : ℝ) + 1 = 0 by norm_num] at hsum
    exact hsum
  -- … so it is constant there, forcing (u T)⁻¹ = 0: absurd.
  have hconst := constant_of_has_deriv_right_zero
    (f := fun s => (u s)⁻¹ + s) (a := (0 : ℝ)) (b := T)
    (fun t ht => (hH_deriv t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hH_deriv t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
  have hend := hconst T (Set.right_mem_Icc.mpr hT_pos.le)
  have huT_pos : 0 < u T := lt_of_lt_of_le hR2 (hu_ge T hT_pos.le)
  have hzero : (u T)⁻¹ = 0 := by
    have h0 : (u 0)⁻¹ + 0 = T := by rw [hu0, hT_def, add_zero]
    rw [h0] at hend
    linarith
  exact absurd hzero (inv_pos.mpr huT_pos).ne'

/-- **Flow-completeness hypothesis.**

Every information-geometric generator integrates to a global,
divergence-preserving, smooth one-parameter family whose infinitesimal
generator agrees with the given vector field **on the parameter domain**.

The agreement is required only on the domain because that is where — and
only where — the generator structure carries geometric content: demanding
it globally is unsatisfiable once the domain is bounded
(`not_forall_hasGlobalFlow_of_isBounded`).

This is the information-geometric analogue of essential self-adjointness
in Stone's theorem, and like it, a genuine hypothesis: the flat location
model on a bounded interval with `X = d/dθ` — mirroring the momentum
operator on `(0,1)`, symmetric with no self-adjoint extension — is
Killing and cubic-preserving, but no domain-preserving family realizes
it.  Deriving `FlowComplete` for concrete models from Fisher geodesic
completeness and divergence rigidity is future work (see the section
docstring). -/
def FlowComplete (M : TwiceDifferentiableModel n Ω) : Prop :=
  ∀ G : InfoGeometricGenerator M, ∃ F : M.DivergencePreservingFamily,
    ∀ θ ∈ M.paramDomain, F.generator θ = G.vectorField θ

-- ============================================================================
-- §8. The Information-Geometric Stone's Theorem
-- ============================================================================

/-- **Grönwall uniqueness on a ball.** Two trajectories of the same ODE `γ' = X'(γ)` that stay
in a common closed ball and share an initial value agree on `[0, ε]`. This is the one Grönwall
call (`dist_le_of_trajectories_ODE_of_mem` with `δ = 0`) shared by the forward and backward
halves of `smooth_ode_local_unique` below — the backward half applies it to the negated field
and the time-reversed curves. -/
private lemma gronwall_uniqueness_on_ball
    {X' : ParamSpace n → ParamSpace n} {K : NNReal} {θ₀ : ParamSpace n}
    (hK : LipschitzOnWith K X' (Metric.closedBall θ₀ 1))
    {γ₁' γ₂' : ℝ → ParamSpace n} {ε : ℝ}
    (hγ₁' : Continuous γ₁') (hγ₂' : Continuous γ₂')
    (h_ode₁' : ∀ s, HasDerivAt γ₁' (X' (γ₁' s)) s)
    (h_ode₂' : ∀ s, HasDerivAt γ₂' (X' (γ₂' s)) s)
    (h_stay₁' : ∀ s, |s| ≤ ε → γ₁' s ∈ Metric.closedBall θ₀ 1)
    (h_stay₂' : ∀ s, |s| ≤ ε → γ₂' s ∈ Metric.closedBall θ₀ 1)
    (h₀' : γ₁' 0 = γ₂' 0) :
    ∀ s ∈ Set.Icc (0 : ℝ) ε, γ₁' s = γ₂' s := by
  intro s hs
  have h_dist := dist_le_of_trajectories_ODE_of_mem
    (v := fun _ => X') (s := fun _ => Metric.closedBall θ₀ 1)
    (K := K) (δ := 0)
    (hv := fun _ _ => hK)
    (hf := hγ₁'.continuousOn)
    (hf' := fun t _ => (h_ode₁' t).hasDerivWithinAt)
    (hfs := fun t ht => h_stay₁' t (by rw [abs_of_nonneg ht.1]; exact ht.2.le))
    (hg := hγ₂'.continuousOn)
    (hg' := fun t _ => (h_ode₂' t).hasDerivWithinAt)
    (hgs := fun t ht => h_stay₂' t (by rw [abs_of_nonneg ht.1]; exact ht.2.le))
    (ha := by rw [← h₀', dist_self])
    s hs
  simp only [zero_mul] at h_dist
  exact dist_eq_zero.mp (le_antisymm h_dist dist_nonneg)

/-- Two smooth solutions of γ' = X(γ) with the same initial condition
    agree on a neighborhood of 0. Uses Grönwall via
    `dist_le_of_trajectories_ODE_of_mem` with δ = 0. -/
private lemma smooth_ode_local_unique
    {X : ParamSpace n → ParamSpace n} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    {γ₁ γ₂ : ℝ → ParamSpace n}
    (hγ₁ : ContDiff ℝ (⊤ : ℕ∞) γ₁) (hγ₂ : ContDiff ℝ (⊤ : ℕ∞) γ₂)
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
  set ε := min ε₁ ε₂ with _hε_def
  have hε : 0 < ε := lt_min hε₁ hε₂
  -- ═══ Step 3: Forward uniqueness on [0, ε] via Grönwall ═══
  have h_fwd : ∀ s ∈ Set.Icc 0 ε, γ₁ s = γ₂ s :=
    gronwall_uniqueness_on_ball hK hγ₁.continuous hγ₂.continuous h_ode₁ h_ode₂
      (fun s hs => h_stay₁ s (hs.trans (min_le_left _ _)))
      (fun s hs => h_stay₂ s (hs.trans (min_le_right _ _)))
      h₀
  -- ═══ Step 4: Backward uniqueness on [0, ε] for reversed curves ═══
  -- γ̃ᵢ(t) := γᵢ(-t) solves γ̃' = -X(γ̃), γ̃(0) = θ₀; -X is Lipschitz on the same ball with the
  -- same K, so the same Grönwall call applies to the negated field and reversed curves.
  have h_bwd : ∀ s ∈ Set.Icc 0 ε, γ₁ (-s) = γ₂ (-s) := by
    have hf_ode : ∀ t, HasDerivAt (γ₁ ∘ Neg.neg) (-X ((γ₁ ∘ Neg.neg) t)) t := by
      intro t
      have h := (h_ode₁ (-t)).scomp t (hasDerivAt_neg t)
      simp only [neg_one_smul] at h
      exact h
    have hg_ode : ∀ t, HasDerivAt (γ₂ ∘ Neg.neg) (-X ((γ₂ ∘ Neg.neg) t)) t := by
      intro t
      have h := (h_ode₂ (-t)).scomp t (hasDerivAt_neg t)
      simp only [neg_one_smul] at h
      exact h
    have hK_neg : LipschitzOnWith K (fun x => -X x) (Metric.closedBall θ₀ 1) := by
      intro x hx y hy
      calc edist (-X x) (-X y)
          = edist (X x) (X y) := by rw [edist_neg_neg]
        _ ≤ K * edist x y := hK hx hy
    exact gronwall_uniqueness_on_ball hK_neg
      (hγ₁.comp contDiff_neg).continuous (hγ₂.comp contDiff_neg).continuous
      hf_ode hg_ode
      (fun s hs => h_stay₁ (-s) (by rw [abs_neg]; exact hs.trans (min_le_left _ _)))
      (fun s hs => h_stay₂ (-s) (by rw [abs_neg]; exact hs.trans (min_le_right _ _)))
      (by simp only [neg_zero]; exact h₀)
  -- ═══ Combine forward and backward ═══
  exact ⟨ε, hε, fun s hs => by
    by_cases h : 0 ≤ s
    · exact h_fwd s ⟨h, (abs_lt.mp hs).2.le⟩
    · simp only [not_le] at h
      have := h_bwd (-s) ⟨by linarith, by linarith [(abs_lt.mp hs).1]⟩
      rwa [neg_neg] at this⟩


/-- **Uniqueness of flows on an invariant set.**  Two divergence-preserving
families whose generators agree on a set `D` invariant under both flows
have identical flows on `D`.

This is ODE uniqueness (Grönwall plus a clopen argument in `t`) applied to
dθ/dt = X(θ): both trajectories through a point of `D` stay in `D`, where
they solve the *same* smooth ODE with the same initial condition.  Note the
hypotheses — no completeness, and none of the third-order model data that
the forward map `toGenerator` needs. -/
lemma flow_eqOn_of_generator_eqOn
    (F₁ F₂ : M.DivergencePreservingFamily) {D : Set (ParamSpace n)}
    (hD₁ : ∀ t, Set.MapsTo (F₁.φ t) D D) (hD₂ : ∀ t, Set.MapsTo (F₂.φ t) D D)
    (hgen : ∀ θ ∈ D, F₁.generator θ = F₂.generator θ) :
    ∀ t, ∀ θ ∈ D, F₁.φ t θ = F₂.φ t θ := by
  intro t θ hθ
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
      -- At t₀, both flows pass through θ₀ := F₁.φ t₀ θ = F₂.φ t₀ θ ∈ D
      set θ₀ := F₁.φ t₀ θ with _hθ₀_def
      have hθ₀ : θ₀ ∈ D := hD₁ t₀ hθ
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
        -- h_ode₂: F₂ solves the SAME ODE on D (generators agree there, and
        -- F₂'s trajectory through θ₀ ∈ D stays in D)
        · intro s
          have h_diff : DifferentiableAt ℝ (fun t => F₂.φ t θ₀) s :=
            ((F₂.smooth.comp (contDiff_id.prodMk contDiff_const)).differentiable
              (by simp)).differentiableAt
          have h := h_diff.hasFDerivAt.hasDerivAt
          rw [F₂.flow_equation θ₀ s] at h
          rwa [← hgen _ (hD₂ s hθ₀)] at h
        -- h₀: same initial condition
        · rw [F₁.identity, F₂.identity]
      obtain ⟨ε, hε, h_agree⟩ := h_ode_unique
      refine ⟨Set.Ioo (t₀ - ε) (t₀ + ε), fun t' ht' => ?_, isOpen_Ioo,
        Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩⟩
      -- Show t' ∈ S, i.e., F₁.φ t' θ = F₂.φ t' θ
      change F₁.φ t' θ = F₂.φ t' θ
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

/-- **Uniqueness of the flow.**  Two divergence-preserving families whose
generators agree on the parameter domain have identical flows on the
domain: the instance of `flow_eqOn_of_generator_eqOn` for
`D = M.paramDomain`, which is invariant under both flows by
`maps_domain`.  No completeness hypothesis needed. -/
lemma infoGeometric_stone_unique
    (F₁ F₂ : M.DivergencePreservingFamily)
    (h : ∀ θ ∈ M.paramDomain, F₁.generator θ = F₂.generator θ) :
    ∀ t, ∀ θ ∈ M.paramDomain, F₁.φ t θ = F₂.φ t θ :=
  flow_eqOn_of_generator_eqOn F₁ F₂
    (fun t _ hθ => F₁.maps_domain t _ hθ)
    (fun t _ hθ => F₂.maps_domain t _ hθ) h

/-- **The Information-Geometric Stone's Theorem.**

Under flow-completeness, every information-geometric generator integrates
to a divergence-preserving family realizing its field on the parameter
domain — and the family is unique there: any other family realizing the
same field on the domain has the same flow on the domain.

| Stone's Theorem                     | IG Stone's Theorem                       |
|-------------------------------------|------------------------------------------|
| One-parameter unitary groups        | Divergence-preserving families           |
| Self-adjoint operators              | Info-geometric generators (L_Xg=L_XC=0)  |
| Essential self-adjointness          | Flow completeness                        |
| U(t) = e^{itA}                      | φ_t = flow of X                          |
| A determines U(t) uniquely          | X on the domain determines φ_t there     |

The forward direction — the generator of every family is itself an
info-geometric generator — is `DivergencePreservingFamily.toGenerator`;
it needs third-order model regularity, which this statement does not.
When the statistical manifold is the pure state space of a Hilbert space
(with Fisher metric = 4 × Fubini–Study metric), this reduces to Stone's
theorem for one-parameter unitary groups. -/
theorem infoGeometric_stone (hM : FlowComplete M) (G : InfoGeometricGenerator M) :
    ∃ F : M.DivergencePreservingFamily,
      (∀ θ ∈ M.paramDomain, F.generator θ = G.vectorField θ) ∧
      ∀ F' : M.DivergencePreservingFamily,
        (∀ θ ∈ M.paramDomain, F'.generator θ = G.vectorField θ) →
        ∀ t, ∀ θ ∈ M.paramDomain, F'.φ t θ = F.φ t θ := by
  obtain ⟨F, hF⟩ := hM G
  exact ⟨F, hF, fun F' hF' =>
    infoGeometric_stone_unique F' F fun θ hθ => (hF' θ hθ).trans (hF θ hθ).symm⟩

end TwiceDifferentiableModel

end Spectra.InformationGeometry
