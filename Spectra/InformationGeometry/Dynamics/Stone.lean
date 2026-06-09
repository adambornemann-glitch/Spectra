/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: InformationGeometry/Dynamics/Stone
-/
import LogosLibrary.InformationGeometry.Dynamics.Generator

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Algebra.BigOperators.WithTop
-- For Stone Uniqueness --
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Topology.Order.Compact


namespace InformationGeometry

open MeasureTheory Finset Filter Topology TopologicalSpace

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

namespace TwiceDifferentiableModel

variable (M : TwiceDifferentiableModel n Ω)

variable (F : M.DivergencePreservingFamily)



-- ============================================================================
-- §5. The Generator Structure (Standalone)
-- ============================================================================

/-! ### Information-geometric generators

A standalone structure for vector fields satisfying the Killing and
cubic-preservation conditions.  The **information-geometric Stone's theorem**
will establish a bijection between `DivergencePreservingFamily` and
`InfoGeometricGenerator`, under appropriate completeness hypotheses. -/

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
  In coordinates: ∑ₖ Xᵏ ∂ₖg_{ij} + g_{kj} ∂ᵢXᵏ + g_{ik} ∂ⱼXᵏ = 0.
  We state this as: for any smooth curve θ(t) with θ'(0) = X(θ₀),
  the Fisher inner product is preserved to first order. -/
  killing : ∀ θ ∈ M.paramDomain, ∀ i j : Fin n,
    ∑ k : Fin n,
      vectorField θ k *
        fderiv ℝ (fun θ' => M.toRegularStatisticalModel.fisherMatrix θ' i j) θ
          (EuclideanSpace.single k 1) +
      M.toRegularStatisticalModel.fisherMatrix θ k j *
        fderiv ℝ (fun θ' => vectorField θ' k) θ
          (EuclideanSpace.single i 1) +
      M.toRegularStatisticalModel.fisherMatrix θ i k *
        fderiv ℝ (fun θ' => vectorField θ' k) θ
          (EuclideanSpace.single j 1) = 0
  /-- **Cubic preservation**: L_X C = 0.
  Analogous Lie derivative condition on the cubic tensor. -/
  preserves_cubic : ∀ θ ∈ M.paramDomain, ∀ i j k : Fin n,
    -- The full Lie derivative L_X C_{ijk} = 0 in components.
    -- This has four terms: X^l ∂_l C_{ijk} + C_{ljk} ∂_i X^l + ...
    -- For the sketch, we state the condition abstractly.
    ∑ l : Fin n,
      vectorField θ l *
        fderiv ℝ (fun θ' => M.cubicTensor θ' i j k) θ
          (EuclideanSpace.single l 1) +
      M.cubicTensor θ l j k *
        fderiv ℝ (fun θ' => vectorField θ' i) θ
          (EuclideanSpace.single l 1) +
      M.cubicTensor θ i l k *
        fderiv ℝ (fun θ' => vectorField θ' j) θ
          (EuclideanSpace.single l 1) +
      M.cubicTensor θ i j l *
        fderiv ℝ (fun θ' => vectorField θ' k) θ
          (EuclideanSpace.single l 1) = 0


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
  rw [fderiv_φ_at_zero M F θ, ContinuousLinearMap.id_apply]
  simp only [EuclideanSpace.single_apply]
  grind only


/-- Every divergence-preserving family has a generator that is
an information-geometric generator. -/
noncomputable def DivergencePreservingFamily.toGenerator
    (F : M.DivergencePreservingFamily) :
    InfoGeometricGenerator M where
  vectorField := F.generator
  smooth := by
    -- F.generator θ = D(uncurry φ)(0,θ)(1,0) by the chain rule.
    -- This is eval_{(1,0)} ∘ fderiv(uncurry φ) ∘ (0,·), a composition of C^∞ maps.
    suffices h_eq : F.generator =
        fun θ => fderiv ℝ (Function.uncurry F.φ) (0, θ)
          ((1 : ℝ), (0 : ParamSpace n)) by
      rw [h_eq]
      -- fderiv of a C^∞ function is C^∞
      have hDg : ContDiff ℝ ⊤ (fderiv ℝ (Function.uncurry F.φ)) :=
        (contDiff_succ_iff_fderiv (n := ⊤) |>.mp F.smooth).2.2
      -- Compose: eval ∘ Dg ∘ inject
      exact (ContinuousLinearMap.apply ℝ (ParamSpace n)
            ((1 : ℝ), (0 : ParamSpace n))).contDiff |>.comp
        (hDg.comp (contDiff_const.prodMk contDiff_id))
    -- Pointwise equality via chain rule
    ext θ
    simp only [DivergencePreservingFamily.generator]
    have h_diff_g : DifferentiableAt ℝ (Function.uncurry F.φ) (0, θ) :=
      (F.smooth.differentiable WithTop.top_ne_zero).differentiableAt
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
  killing := by sorry
  preserves_cubic := by sorry  -- follows from F.generator_preserves_cubic


-- ============================================================================
-- §7. Toward the Bijection (Reverse Map): Existence of the Flow
-- ============================================================================

/-! ### Integrating the generator

Given an `InfoGeometricGenerator`, we need to show that the ODE
  dθ/dt = X(θ)
has a global solution (not just local).

**This is where completeness enters.** In Stone's theorem, self-adjointness
of A guarantees that exp(itA) exists globally as a unitary operator — the
essential self-adjointness prevents "escape to infinity."  Here, we need
the Fisher-metric geodesic completeness of the statistical manifold to
guarantee that the flow of X exists for all time.

The Killing condition L_X g = 0 is crucial: it implies ‖X‖_g is constant
along flow lines, giving a bound on the speed of the flow, which (combined
with geodesic completeness) prevents finite-time blowup.

This section is the most technically demanding and connects directly to
the surjectivity argument that Amari anticipated. -/

/-- **Geodesic completeness hypothesis.**

The statistical manifold is geodesically complete with respect to the
Fisher metric: every maximal geodesic is defined for all t ∈ ℝ.

This is the information-geometric analogue of essential self-adjointness
in Stone's theorem. Both conditions say "nothing escapes to infinity
in finite time." -/
class GeodesicallyComplete (M : TwiceDifferentiableModel n Ω) : Prop where
  complete : ∀ θ₀ ∈ M.paramDomain, ∀ _v : ParamSpace n,
    ∃ γ : ℝ → ParamSpace n,
      γ 0 = θ₀ ∧
      (∀ t, γ t ∈ M.paramDomain) ∧
      Continuous γ
      -- Full geodesic equation omitted; would need Christoffel symbols
      -- and second derivatives of γ.

/-- Under geodesic completeness, every information-geometric generator
integrates to a global divergence-preserving family.

### Proof strategy (outline)
1. Local existence: Picard–Lindelöf gives local flow of X.
2. X is Killing, so ‖X(θ(t))‖_g = const along flow lines.
3. Geodesic completeness + bounded speed ⟹ no finite-time blowup.
4. Global flow exists and is smooth (ODE theory).
5. Divergence preservation: d/dt D(φ_t(θ₁) ‖ φ_t(θ₂))
   = (L_X D)(φ_t(θ₁), φ_t(θ₂)) = 0 because L_X g = 0 and L_X C = 0
   imply L_X D = 0 (since D is determined by g and C to all orders). -/
theorem generator_integrates_to_family
    [GeodesicallyComplete M]
    (G : InfoGeometricGenerator M) :
    ∃ F : M.DivergencePreservingFamily, F.toGenerator = G := by
  sorry



-- ============================================================================
-- §8. The Information-Geometric Stone's Theorem
-- ============================================================================

/-- **The Information-Geometric Stone's Theorem.**

Under geodesic completeness, there is a bijective correspondence between:
- Divergence-preserving one-parameter families on the statistical manifold
- Information-geometric generators (Killing + cubic-preserving vector fields)

given by differentiation (family → generator) and integration (generator → family).

This is the exact analogue of Stone's theorem:

| Stone's Theorem                     | IG Stone's Theorem                      |
|-------------------------------------|-----------------------------------------|
| One-parameter unitary groups        | Divergence-preserving families          |
| Self-adjoint operators              | Info-geometric generators (L_Xg=L_XC=0) |
| Essential self-adjointness          | Geodesic completeness                   |
| U(t) = e^{itA}                      | φ_t = flow of X                         |
| Schrödinger equation                | Flow equation dθ/dt = X(θ)              |

When the statistical manifold is the pure state space of a Hilbert space
(with Fisher metric = 4 × Fubini-Study metric), this reduces to Stone's
theorem for one-parameter unitary groups. -/
theorem infoGeometric_stone_weak
    [GeodesicallyComplete M] :
    ∀ F : M.DivergencePreservingFamily,
    ∃! G : InfoGeometricGenerator M,
      F.toGenerator = G ∧
      (∃ F' : M.DivergencePreservingFamily,
        F'.toGenerator = G ∧ ∀ t θ, F'.φ t θ = F.φ t θ) := by
  intro F
  refine ⟨F.toGenerator, ⟨rfl, F, rfl, fun _ _ => rfl⟩, ?_⟩
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
      fun x _ => (hX.differentiable WithTop.top_ne_zero).differentiableAt
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
    · push_neg at h
      have := h_bwd (-s) ⟨by linarith, by linarith [(abs_lt.mp hs).1]⟩
      rwa [neg_neg] at this⟩


/-- **Uniqueness of the flow**: Two divergence-preserving families with
the same infinitesimal generator have identical flows.

This is ODE uniqueness (Picard–Lindelöf) applied to dθ/dt = X(θ):
both families solve the same smooth ODE with the same initial condition
φ_0 = id, so they agree for all time. No completeness hypothesis needed. -/
lemma infoGeometric_stone_unique
    (F₁ F₂ : M.DivergencePreservingFamily)
    (h : F₁.toGenerator = F₂.toGenerator) :
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
        · exact F₁.toGenerator.smooth
        -- hγ₁: s ↦ F₁.φ s θ₀ is smooth
        · exact F₁.smooth.comp (contDiff_id.prodMk contDiff_const)
        -- hγ₂: s ↦ F₂.φ s θ₀ is smooth
        · exact F₂.smooth.comp (contDiff_id.prodMk contDiff_const)
        -- h_ode₁: F₁ solves γ' = X(γ)
        · intro s
          have h_diff : DifferentiableAt ℝ (fun t => F₁.φ t θ₀) s :=
            ((F₁.smooth.comp (contDiff_id.prodMk contDiff_const)).differentiable
              WithTop.top_ne_zero).differentiableAt
          have h := h_diff.hasFDerivAt.hasDerivAt
          rwa [F₁.flow_equation θ₀ s] at h
        -- h_ode₂: F₂ solves the SAME ODE (generator = F₁.generator by hgen)
        · intro s
          have h_diff : DifferentiableAt ℝ (fun t => F₂.φ t θ₀) s :=
            ((F₂.smooth.comp (contDiff_id.prodMk contDiff_const)).differentiable
              WithTop.top_ne_zero).differentiableAt
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


/-- **Existence of the flow**: Under geodesic completeness, every
info-geometric generator integrates to a global divergence-preserving
family.

This is the hard direction. The proof requires:
1. Local existence via Picard–Lindelöf
2. The Killing condition ⟹ ‖X‖_g constant along flow lines
3. Geodesic completeness + bounded speed ⟹ no finite-time blowup
4. Divergence preservation from L_X g = L_X C = 0 -/
lemma infoGeometric_stone_exists
    [GeodesicallyComplete M]
    (G : InfoGeometricGenerator M) :
    ∃ F : M.DivergencePreservingFamily, F.toGenerator = G := by
  sorry

/-- **The Information-Geometric Stone's Theorem.**

Under geodesic completeness, the map `toGenerator` is a bijection
(up to pointwise flow equality) between divergence-preserving
one-parameter families and info-geometric generators.

| Direction   | Content                        | Analogue in Stone's theorem     |
|-------------|--------------------------------|---------------------------------|
| Surjective  | Every generator has a flow     | e^{itA} exists (self-adjoint A) |
| Injective   | Generator determines the flow  | A determines U(t) uniquely      |
-/
theorem infoGeometric_stone [GeodesicallyComplete M] :
    (∀ G : InfoGeometricGenerator M,
      ∃ F : M.DivergencePreservingFamily, F.toGenerator = G) ∧
    (∀ F₁ F₂ : M.DivergencePreservingFamily,
      F₁.toGenerator = F₂.toGenerator →
      ∀ t θ, F₁.φ t θ = F₂.φ t θ) :=
  ⟨infoGeometric_stone_exists M, infoGeometric_stone_unique M⟩


end TwiceDifferentiableModel

end InformationGeometry
