/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.StatisticalManifold
import Spectra.InformationGeometry.CramerRao.Quantum
import Spectra.InformationGeometry.Divergence
import Spectra.InformationGeometry.Connection.AmariChentsov
import Spectra.InformationGeometry.Connection.Basic
import Spectra.InformationGeometry.Flow.Family
import Spectra.InformationGeometry.Flow.FaaDiBruno
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Algebra.BigOperators.WithTop
-- For Stone Uniqueness --
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Topology.Order.Compact

/-!
# Symmetry and relabeling lemmas for the m-connection cluster

This is the first of four files proving the m-connection transformation law (the
information-geometric analogue of parallel transport tensoriality). See
`MixtureConnection.lean`'s module docstring for the full mathematical roadmap; this file supplies
its algebraic foundation:

* the a.e. Schwarz symmetry of `scorePartial`, and the resulting symmetry of the m-connection
  coefficient `mConnectionCoeff` and trilinear form `mConnectionTrilin` in their first two slots;
* the four triple-sum "relabeling" lemmas identifying `∑ xᵢyⱼzₖ Γ_{σ(i,j,k)}` with
  `mConnectionTrilin` on a permuted argument triple, for each `σ` reachable from the
  `Γ`-symmetry above;
* the analogous relabeling/swap lemmas for the cubic tensor `cubicTensor`, and the algebraic
  split `cubic_connection_split_kij` combining both;
* the expected log-likelihood Hessian identity `integral_scorePartial_eq_neg_fisherMatrix`
  (`∫ (∂ⱼsₖ)·p dμ = −g_{jk}`);
* Schwarz symmetry of the flow's second derivative, `secondDerivPhi_symm`.

## Main statements

* `scorePartial_symm_ae`, `mConnectionCoeff_symm₁₂`, `mConnectionTrilin_symm₁₂`
* `trilin_relabel_ikj`, `trilin_relabel_jki`, `trilin_relabel_kij`, `trilin_relabel_kji`
* `cubic_relabel_kij`, `cubic_sum_swap₁₂`, `cubic_sum_swap₂₃`, `cubic_connection_split_kij`
* `integral_scorePartial_eq_neg_fisherMatrix`
* `DivergencePreservingFamily.secondDerivPhi_symm`

Downstream: `ThirdDerivative.lean` → `PullbackIdentities.lean` → `MixtureConnection.lean`.
-/

open MeasureTheory Finset Filter Topology TopologicalSpace
namespace Spectra.InformationGeometry

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- For a differentiable CLM-valued map, the derivative of the scalar map
`y ↦ c y w` (frozen vector `w`) is the second-derivative operator with the
slots in the canonical order.  This is the `clm_apply`-with-constant
bridge used throughout the codebase, packaged once. -/
private lemma fderiv_clm_apply_const {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {c : ParamSpace n → ParamSpace n →L[ℝ] E}
    {x : ParamSpace n} (hc : DifferentiableAt ℝ c x) (w v : ParamSpace n) :
    fderiv ℝ (fun y => c y w) x v = fderiv ℝ c x v w := by
  have h := (hc.hasFDerivAt.clm_apply (hasFDerivAt_const w x)).fderiv
  simp only [ContinuousLinearMap.comp_zero, zero_add] at h
  rw [h, ContinuousLinearMap.flip_apply]

/-- The standard-coordinate expansion in `ParamSpace n`.  Public: shared with
`ThirdDerivative.lean` and `PullbackIdentities.lean`. -/
lemma paramSpace_eq_sum_single (u : ParamSpace n) :
    u = ∑ i : Fin n, u.ofLp i • EuclideanSpace.single i 1 := by
  ext p
  simp [Pi.single, Function.update_apply, Finset.mem_univ]

namespace TwiceDifferentiableModel

variable (M : TwiceDifferentiableModel n Ω)

-- ════════════════════════════════════════════════════════════════════
-- §1. Symmetry lemmas for scorePartial, Γᵐ, and the trilinear forms
-- ════════════════════════════════════════════════════════════════════

/-- The score derivative is a.e. symmetric in its two indices:
`∂ₐsᵦ = ∂ᵦsₐ` wherever the log-density is `C²` (Schwarz). -/
lemma scorePartial_symm_ae {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (a b : Fin n) :
    ∀ᵐ ω ∂M.refMeasure, M.scorePartial θ a b ω = M.scorePartial θ b a ω := by
  filter_upwards [M.logDensity_twice_diff θ hθ, M.density_pos_ae θ hθ]
    with ω hlog hpos
  have hC2 : ContDiffAt ℝ 2 (fun θ' => Real.log (M.density θ' ω)) θ :=
    hlog hpos
  -- the density stays positive near θ
  have hp_cont : ContinuousAt (fun θ' => M.density θ' ω) θ :=
    (M.toStatisticalModel.density_differentiableAt hθ ω).continuousAt
  -- the scores agree with the log-density partials near θ
  have hscore_ev : ∀ x : Fin n,
      (fun θ' => M.toRegularStatisticalModel.score θ' x ω) =ᶠ[𝓝 θ]
      (fun θ' => fderiv ℝ (fun θ'' => Real.log (M.density θ'' ω)) θ'
        (EuclideanSpace.single x 1)) := by
    intro x
    filter_upwards [hp_cont.eventually (isOpen_Ioi.mem_nhds hpos),
      M.isOpen_paramDomain.mem_nhds hθ] with θ' hθ'pos hθ'dom
    have h_diff := M.toStatisticalModel.density_differentiableAt hθ'dom ω
    have h_ne : M.density θ' ω ≠ 0 := ne_of_gt hθ'pos
    rw [(h_diff.hasFDerivAt.log h_ne).fderiv,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
    unfold RegularStatisticalModel.score RegularStatisticalModel.partialDensity
    field_simp
  -- second-derivative differentiability of the log-density at θ
  have hℓ' : DifferentiableAt ℝ
      (fderiv ℝ (fun θ'' => Real.log (M.density θ'' ω))) θ :=
    (hC2.fderiv_right le_rfl).differentiableAt one_ne_zero
  -- Schwarz: the Hessian of the log-density is symmetric at θ
  have hev : ∀ᶠ θ' in 𝓝 θ,
      HasFDerivAt (fun θ'' => Real.log (M.density θ'' ω))
        (fderiv ℝ (fun θ'' => Real.log (M.density θ'' ω)) θ') θ' := by
    -- (the side goal is `(2 : WithTop ℕ∞) ≠ ∞`; if `simp` misses it,
    -- try `by norm_num` or `WithTop.natCast_ne_top _`)
    filter_upwards [hC2.eventually (by simp)] with θ' hθ'
    exact (hθ'.differentiableAt two_ne_zero).hasFDerivAt
  have hsymm := second_derivative_symmetric_of_eventually_of_real hev
    hℓ'.hasFDerivAt (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)
  -- transfer to scorePartial via the eventual identification of scores
  have h_ab : M.scorePartial θ a b ω =
      fderiv ℝ (fderiv ℝ (fun θ'' => Real.log (M.density θ'' ω))) θ
        (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) := by
    change fderiv ℝ (fun θ' => M.toRegularStatisticalModel.score θ' b ω) θ
      (EuclideanSpace.single a 1) = _
    rw [DFunLike.congr_fun (Filter.EventuallyEq.fderiv_eq (hscore_ev b))
      (EuclideanSpace.single a 1)]
    exact fderiv_clm_apply_const hℓ' _ _
  have h_ba : M.scorePartial θ b a ω =
      fderiv ℝ (fderiv ℝ (fun θ'' => Real.log (M.density θ'' ω))) θ
        (EuclideanSpace.single b 1) (EuclideanSpace.single a 1) := by
    change fderiv ℝ (fun θ' => M.toRegularStatisticalModel.score θ' a ω) θ
      (EuclideanSpace.single b 1) = _
    rw [DFunLike.congr_fun (Filter.EventuallyEq.fderiv_eq (hscore_ev a))
      (EuclideanSpace.single b 1)]
    exact fderiv_clm_apply_const hℓ' _ _
  rw [h_ab, h_ba, hsymm]

/-- `Γᵐ_{ab,c} = Γᵐ_{ba,c}`: the m-connection coefficient is symmetric
in its first two (lower) indices. -/
lemma mConnectionCoeff_symm₁₂ {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (a b c : Fin n) :
    M.mConnectionCoeff θ a b c = M.mConnectionCoeff θ b a c := by
  unfold mConnectionCoeff
  apply integral_congr_ae
  filter_upwards [M.scorePartial_symm_ae hθ a b] with ω hω
  rw [hω]

/-- `mConnectionTrilin` unfolded as the canonical triple sum. -/
lemma mConnectionTrilin_eq_sum (θ : ParamSpace n) (u v w : ParamSpace n) :
    M.mConnectionTrilin θ u v w =
    ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      u i * v j * w k * M.mConnectionCoeff θ i j k := rfl

/-- The trilinear m-connection form is symmetric in its first two slots. -/
lemma mConnectionTrilin_symm₁₂ {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (u v w : ParamSpace n) :
    M.mConnectionTrilin θ u v w = M.mConnectionTrilin θ v u w := by
  unfold mConnectionTrilin
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun r _ => ?_
  rw [M.mConnectionCoeff_symm₁₂ hθ q p r]
  ring

-- ── Triple-sum relabeling: ∑ xᵢyⱼzₖ Γ_{σ(i,j,k)} as a `mConnectionTrilin` ──

/-- `∑ᵢⱼₖ xᵢ yⱼ zₖ Γ_{ik,j} = Γᵗʳⁱ(x, z, y)`. -/
lemma trilin_relabel_ikj (θ : ParamSpace n) (x y z : ParamSpace n) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      x i * y j * z k * M.mConnectionCoeff θ i k j) =
    M.mConnectionTrilin θ x z y := by
  unfold mConnectionTrilin
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

/-- `∑ᵢⱼₖ xᵢ yⱼ zₖ Γ_{jk,i} = Γᵗʳⁱ(y, z, x)`. -/
lemma trilin_relabel_jki (θ : ParamSpace n) (x y z : ParamSpace n) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      x i * y j * z k * M.mConnectionCoeff θ j k i) =
    M.mConnectionTrilin θ y z x := by
  unfold mConnectionTrilin
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

/-- `∑ᵢⱼₖ xᵢ yⱼ zₖ Γ_{ki,j} = Γᵗʳⁱ(z, x, y)`. -/
lemma trilin_relabel_kij (θ : ParamSpace n) (x y z : ParamSpace n) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      x i * y j * z k * M.mConnectionCoeff θ k i j) =
    M.mConnectionTrilin θ z x y := by
  unfold mConnectionTrilin
  have h1 : (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      x i * y j * z k * M.mConnectionCoeff θ k i j) =
      ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n,
        x i * y j * z k * M.mConnectionCoeff θ k i j :=
    Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [h1, Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by ring

/-- `∑ᵢⱼₖ xᵢ yⱼ zₖ Γ_{kj,i} = Γᵗʳⁱ(z, y, x)`. -/
lemma trilin_relabel_kji (θ : ParamSpace n) (x y z : ParamSpace n) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      x i * y j * z k * M.mConnectionCoeff θ k j i) =
    M.mConnectionTrilin θ z y x := by
  unfold mConnectionTrilin
  have h1 : (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      x i * y j * z k * M.mConnectionCoeff θ k j i) =
      ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n,
        x i * y j * z k * M.mConnectionCoeff θ k j i :=
    Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

-- ── Cubic-tensor entry relabeling inside triple sums ──

/-- Entry permutation `C_{kij} → C_{ijk}` inside a weighted triple sum. -/
lemma cubic_relabel_kij {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (x y z : ParamSpace n) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      x i * y j * z k * M.cubicTensor θ k i j) =
    ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      x i * y j * z k * M.cubicTensor θ i j k :=
  Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => by
      rw [M.cubicTensor_symm₁₃ hθ k i j, M.cubicTensor_symm₁₂ hθ j i k]

/-- Swapping the first two vector slots of the pulled-back cubic form. -/
lemma cubic_sum_swap₁₂ {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (x y z : ParamSpace n) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      x i * y j * z k * M.cubicTensor θ i j k) =
    ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      y i * x j * z k * M.cubicTensor θ i j k := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun k _ => ?_
  rw [M.cubicTensor_symm₁₂ hθ q p k]
  ring

/-- Swapping the last two vector slots of the pulled-back cubic form. -/
lemma cubic_sum_swap₂₃ {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (x y z : ParamSpace n) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      x i * y j * z k * M.cubicTensor θ i j k) =
    ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      x i * z j * y k * M.cubicTensor θ i j k := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [M.cubicTensor_symm₂₃ hθ i q p]
  ring

/-- Split the `C_{kij} + Γᵐ_{ki,j} + Γᵐ_{kj,i}` triple sum into the
pulled-back cubic tensor and the two trilinear m-connection terms.  Public:
shared with `PullbackIdentities.lean`'s `fisher_derivative_identity`. -/
lemma cubic_connection_split_kij {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain) (x y z : ParamSpace n) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      x i * y j * z k *
        (M.cubicTensor θ k i j + M.mConnectionCoeff θ k i j +
         M.mConnectionCoeff θ k j i)) =
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      x i * y j * z k * M.cubicTensor θ i j k) +
    M.mConnectionTrilin θ z x y + M.mConnectionTrilin θ z y x := by
  simp only [mul_add, Finset.sum_add_distrib]
  rw [M.cubic_relabel_kij hθ x y z, M.trilin_relabel_kij θ x y z,
    M.trilin_relabel_kji θ x y z]

-- ════════════════════════════════════════════════════════════════════
-- §2. The expected log-likelihood Hessian is −g  (integrated Bartlett-2)
-- ════════════════════════════════════════════════════════════════════

/-- `∫ (∂ⱼsₖ)·p dμ = −g_{jk}`: the expected Hessian of the log-likelihood
is minus the Fisher information.  Proof: the cross-score integral
`θ' ↦ −∫ p(θ)·sₖ(θ') dμ` has derivative components `g_{jk}` at the
diagonal (`cross_score_hasFDerivAt`) and `−∫ p·∂ⱼsₖ(θ₀)` at any `θ₀`
(`cross_score_hasFDerivAt'`); uniqueness of the derivative at `θ₀ = θ`
identifies the two. -/
lemma integral_scorePartial_eq_neg_fisherMatrix
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (j k : Fin n) :
    ∫ ω, M.scorePartial θ j k ω * M.density θ ω ∂M.refMeasure =
      -M.toRegularStatisticalModel.fisherMatrix θ j k := by
  obtain ⟨g₁, hg₁, hg₁_eval⟩ := M.cross_score_hasFDerivAt hθ k
  obtain ⟨g₁', hg₁', hg₁'_eval⟩ := M.cross_score_hasFDerivAt' hθ hθ k
  have h : M.toRegularStatisticalModel.fisherMatrix θ j k =
      -∫ ω, M.density θ ω * M.scorePartial θ j k ω ∂M.refMeasure := by
    rw [← hg₁_eval j,
        DFunLike.congr_fun (hg₁.unique hg₁') (EuclideanSpace.single j 1),
        hg₁'_eval j]
  rw [h, neg_neg]
  congr 1
  funext ω
  ring

namespace DivergencePreservingFamily

variable {M : TwiceDifferentiableModel n Ω}
variable (F : M.DivergencePreservingFamily)

/-- Schwarz symmetry of the flow: `d²φ_t(θ)(eₐ, eᵦ) = d²φ_t(θ)(eᵦ, eₐ)`. -/
lemma secondDerivPhi_symm (t : ℝ) (θ : ParamSpace n) (a b : Fin n) :
    F.secondDerivPhi t θ a b = F.secondDerivPhi t θ b a := by
  have hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) (F.φ t) :=
    F.smooth.comp (contDiff_const.prodMk contDiff_id)
  have h1 : DifferentiableAt ℝ (fderiv ℝ (F.φ t)) θ :=
    ((hφ_smooth.fderiv_right (m := (⊤ : ℕ∞)) (by exact_mod_cast le_top)).differentiable
      (by simp)).differentiableAt
  have hev : ∀ᶠ y in 𝓝 θ, HasFDerivAt (F.φ t) (fderiv ℝ (F.φ t) y) y := by
    filter_upwards with y
    exact ((hφ_smooth.differentiable (by simp)) y).hasFDerivAt
  have hsymm := second_derivative_symmetric_of_eventually_of_real hev
    h1.hasFDerivAt (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)
  unfold secondDerivPhi
  rw [fderiv_clm_apply_const h1 (EuclideanSpace.single b 1)
        (EuclideanSpace.single a 1),
      fderiv_clm_apply_const h1 (EuclideanSpace.single a 1)
        (EuclideanSpace.single b 1),
      hsymm]

end DivergencePreservingFamily

end TwiceDifferentiableModel

end Spectra.InformationGeometry
