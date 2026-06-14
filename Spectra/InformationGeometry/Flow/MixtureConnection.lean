/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
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
# The m-connection transformation law and cubic-tensor preservation

This file proves that a divergence-preserving family transforms the
m-connection coefficients tensorially-with-correction, and — as the key
intermediate step — that it preserves the Amari–Chentsov cubic tensor.

## The mathematical shape of the argument

Write `α := φ_t θ`, `uₓ := dφ_t(θ)·eₓ`, `w_{xy} := d²φ_t(θ)(eₓ, e_y)`,
`g := fisherBilin`, `Γ := mConnectionCoeff`, `C := cubicTensor`, and let
`T := D'''(α‖·)(α)[u_a, u_b, u_c]` denote the third KL derivative at the
diagonal, evaluated on the pushed-forward basis.  Two independent
families of identities are available:

1. **Transfer at one base point** (`third_deriv_transfer` +
   `kl_faa_di_bruno` + the diagonal third-derivative formula):

     `T + g(w_ab,u_c) + g(w_ac,u_b) + g(u_a,w_bc)
        = C(θ)_{abc} + Γ(θ)_{ac,b} + Γ(θ)_{bc,a} + Γ(θ)_{ab,c}`.   (M1)

2. **Differentiating `preserves_fisher` across base points** (three
   instances, one per choice of differentiated pair):

     `Γᵗʳⁱ(α)(u_c,u_a,u_b) + Γᵗʳⁱ(α)(u_c,u_b,u_a) + C(α)[u³]
        + g(w_ca,u_b) + g(u_a,w_cb)
        = Γ(θ)_{ca,b} + Γ(θ)_{cb,a} + C(θ)_{cab}`,                   (I)

   and its `(a,c,b)`, `(b,c,a)` permutations.

The diagonal formula also gives the trilinear decomposition

     `T = C(α)[u³] + Γᵗʳⁱ(α)(u_a,u_c,u_b) + Γᵗʳⁱ(α)(u_b,u_c,u_a)
                   + Γᵗʳⁱ(α)(u_a,u_b,u_c)`.                          (M3)

Summing the three instances of (I), substituting (M3), and comparing
with (M1) yields **cubic preservation** `C(α)[u³] = C(θ)_{abc}`
(`preserves_cubic_basis`), and then (M1) minus cubic preservation is
exactly the m-connection transformation law (`mConnection_correction`).

Note the law is *equivalent* to cubic preservation given (M1): it
cannot be obtained from the transfer identities at the single base
point `θ` alone, because the order-3 transfer only constrains the
totally symmetric combination `C + ΓΣ`.  The cross-base-point
information of (I) is what separates `C` from `Γ`.

## Analytic inputs

(I) requires differentiating `θ' ↦ g_{ij}(θ')` — a Leibniz interchange
with *live* density.  This is supplied by the new
`ThriceDifferentiableModel.fisherMatrix_hasFDerivAt` field (see the
design note in `Regularity.lean`).  Everything else is assembled from
`cross_score_hasFDerivAt'`, `klDiv_third_partial`,
`klDiv_third_deriv_decomposition`, `bartlett2_hasFDerivAt`,
`kl_faa_di_bruno`, and `third_deriv_transfer`.

## Main statements

* `bartlett_second`, `bartlett_third` — the integrated Bartlett identities
* `klDiv_third_deriv_eval`, `klDiv_third_deriv_trilin` — the diagonal
  third KL derivative, componentwise and as a trilinear form
* `fisher_derivative_identity` — identity (I)
* `third_deriv_pullback` — identity (M1)
* `preserves_cubic_basis` — `C(α)` pulled back through `dφ_t` is `C(θ)`
* `mConnection_correction` — the m-connection transformation law
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
    show fderiv ℝ (fun θ' => M.toRegularStatisticalModel.score θ' b ω) θ
      (EuclideanSpace.single a 1) = _
    rw [DFunLike.congr_fun (Filter.EventuallyEq.fderiv_eq (hscore_ev b))
      (EuclideanSpace.single a 1)]
    exact fderiv_clm_apply_const hℓ' _ _
  have h_ba : M.scorePartial θ b a ω =
      fderiv ℝ (fderiv ℝ (fun θ'' => Real.log (M.density θ'' ω))) θ
        (EuclideanSpace.single b 1) (EuclideanSpace.single a 1) := by
    show fderiv ℝ (fun θ' => M.toRegularStatisticalModel.score θ' a ω) θ
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
  have hφ_smooth : ContDiff ℝ ⊤ (F.φ t) :=
    F.smooth.comp (contDiff_const.prodMk contDiff_id)
  have h1 : DifferentiableAt ℝ (fderiv ℝ (F.φ t)) θ :=
    ((hφ_smooth.fderiv_right le_rfl).differentiable
      WithTop.top_ne_zero).differentiableAt
  have hev : ∀ᶠ y in 𝓝 θ, HasFDerivAt (F.φ t) (fderiv ℝ (F.φ t) y) y := by
    filter_upwards with y
    exact ((hφ_smooth.differentiable WithTop.top_ne_zero) y).hasFDerivAt
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

namespace ThriceDifferentiableModel

variable (M : ThriceDifferentiableModel n Ω)
open TwiceDifferentiableModel

-- ════════════════════════════════════════════════════════════════════
-- §3. The Bartlett identities, integrated
-- ════════════════════════════════════════════════════════════════════

/-- **Bartlett-2**: `∫ (∂ⱼsₖ + sⱼsₖ)·p dμ = 0` at every domain point. -/
lemma bartlett_second {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (j k : Fin n) :
    ∫ ω, (M.scorePartial θ j k ω +
        M.toRegularStatisticalModel.score θ j ω *
        M.toRegularStatisticalModel.score θ k ω) *
      M.density θ ω ∂M.refMeasure = 0 := by
  have h1 : Integrable
      (fun ω => M.scorePartial θ j k ω * M.density θ ω) M.refMeasure :=
    (M.scorePartial_density_integrable θ hθ j k).congr
      (by filter_upwards with ω; exact mul_comm _ _)
  have h2 : Integrable (fun ω =>
      M.toRegularStatisticalModel.score θ j ω *
      M.toRegularStatisticalModel.score θ k ω *
      M.density θ ω) M.refMeasure :=
    M.toRegularStatisticalModel.fisherEntry_integrable hθ
      (M.scoreSqIntegrable θ hθ) j k
  have hsplit : (fun ω => (M.scorePartial θ j k ω +
      M.toRegularStatisticalModel.score θ j ω *
      M.toRegularStatisticalModel.score θ k ω) * M.density θ ω) =
      fun ω => M.scorePartial θ j k ω * M.density θ ω +
        M.toRegularStatisticalModel.score θ j ω *
        M.toRegularStatisticalModel.score θ k ω * M.density θ ω := by
    funext ω; ring
  rw [hsplit, integral_add h1 h2,
      M.integral_scorePartial_eq_neg_fisherMatrix hθ j k]
  have hg : (∫ ω, M.toRegularStatisticalModel.score θ j ω *
      M.toRegularStatisticalModel.score θ k ω *
      M.density θ ω ∂M.refMeasure) =
      M.toRegularStatisticalModel.fisherMatrix θ j k := rfl
  rw [hg]
  ring

/-- **Bartlett-3**: the five-term derivative of the Bartlett-2 integral
vanishes.  This is precisely the `h_B` hypothesis of
`klDiv_third_deriv_decomposition`. -/
lemma bartlett_third {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (i j k : Fin n) :
    ∫ ω,
      (fderiv ℝ (fun θ'' => M.scorePartial θ'' j k ω) θ
          (EuclideanSpace.single i 1) +
       M.toRegularStatisticalModel.score θ j ω *
         M.scorePartial θ i k ω +
       M.toRegularStatisticalModel.score θ i ω *
         M.scorePartial θ j k ω +
       M.toRegularStatisticalModel.score θ k ω *
         M.scorePartial θ i j ω +
       M.toRegularStatisticalModel.score θ i ω *
         M.toRegularStatisticalModel.score θ j ω *
         M.toRegularStatisticalModel.score θ k ω) *
      M.density θ ω ∂M.refMeasure = 0 := by
  obtain ⟨L, hL, hL_eval⟩ := M.bartlett2_hasFDerivAt θ hθ i j k
  -- the Bartlett-2 integral is the zero function on the (open) domain
  have hzero : HasFDerivAt
      (fun θ' => ∫ ω, (M.scorePartial θ' j k ω +
        M.toRegularStatisticalModel.score θ' j ω *
        M.toRegularStatisticalModel.score θ' k ω) *
        M.density θ' ω ∂M.refMeasure)
      (0 : ParamSpace n →L[ℝ] ℝ) θ := by
    refine (hasFDerivAt_const (0 : ℝ) θ).congr_of_eventuallyEq ?_
    filter_upwards [M.isOpen_paramDomain.mem_nhds hθ] with θ' hθ'
    exact M.bartlett_second hθ' j k
  have h0 : L (EuclideanSpace.single i 1) = 0 := by
    rw [hL.unique hzero]
    exact ContinuousLinearMap.zero_apply _
  exact hL_eval.symm.trans h0

-- ════════════════════════════════════════════════════════════════════
-- §4. The derivative of the Fisher matrix along the parameter
-- ════════════════════════════════════════════════════════════════════

/-- `θ' ↦ g_{jk}(θ')` is differentiable, with components
`∂ᵢg_{jk} = C_{ijk} + Γᵐ_{ij,k} + Γᵐ_{ik,j}`.  Post-processed form of
the `fisherMatrix_hasFDerivAt` structure field. -/
lemma fisherMatrix_hasFDerivAt' {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain) (j k : Fin n) :
    ∃ L : ParamSpace n →L[ℝ] ℝ,
      HasFDerivAt
        (fun θ' => M.toRegularStatisticalModel.fisherMatrix θ' j k) L θ ∧
      ∀ i : Fin n,
        L (EuclideanSpace.single i 1) =
          M.cubicTensor θ i j k + M.mConnectionCoeff θ i j k +
          M.mConnectionCoeff θ i k j := by
  obtain ⟨L, hL, hL_eval⟩ := M.fisherMatrix_hasFDerivAt θ hθ j k
  refine ⟨L, hL, fun i => ?_⟩
  rw [hL_eval i]
  have h1 : Integrable (fun ω =>
      M.toRegularStatisticalModel.score θ i ω *
      M.toRegularStatisticalModel.score θ j ω *
      M.toRegularStatisticalModel.score θ k ω *
      M.density θ ω) M.refMeasure := M.tripleScore_integrable θ hθ i j k
  have h2 : Integrable (fun ω =>
      M.toRegularStatisticalModel.score θ k ω *
      M.scorePartial θ i j ω * M.density θ ω) M.refMeasure :=
    M.score_scorePartial_integrable θ hθ k i j
  have h3 : Integrable (fun ω =>
      M.toRegularStatisticalModel.score θ j ω *
      M.scorePartial θ i k ω * M.density θ ω) M.refMeasure :=
    M.score_scorePartial_integrable θ hθ j i k
  have hsplit : (fun ω =>
      (M.toRegularStatisticalModel.score θ i ω *
        M.toRegularStatisticalModel.score θ j ω *
        M.toRegularStatisticalModel.score θ k ω +
      M.toRegularStatisticalModel.score θ k ω *
        M.scorePartial θ i j ω +
      M.toRegularStatisticalModel.score θ j ω *
        M.scorePartial θ i k ω) * M.density θ ω) =
      fun ω =>
        (M.toRegularStatisticalModel.score θ i ω *
          M.toRegularStatisticalModel.score θ j ω *
          M.toRegularStatisticalModel.score θ k ω *
          M.density θ ω +
        M.toRegularStatisticalModel.score θ k ω *
          M.scorePartial θ i j ω * M.density θ ω) +
        M.toRegularStatisticalModel.score θ j ω *
          M.scorePartial θ i k ω * M.density θ ω := by
    funext ω; ring
  rw [hsplit]
  erw [integral_add (h1.add h2) h3, integral_add h1 h2]
  rfl

/-- `∂ᵢ g_{jk}(θ) = C_{ijk} + Γᵐ_{ij,k} + Γᵐ_{ik,j}` as a statement
about the canonical `fderiv`. -/
lemma fisherMatrix_fderiv_single {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain) (i j k : Fin n) :
    fderiv ℝ (fun θ' => M.toRegularStatisticalModel.fisherMatrix θ' j k) θ
      (EuclideanSpace.single i 1) =
    M.cubicTensor θ i j k + M.mConnectionCoeff θ i j k +
    M.mConnectionCoeff θ i k j := by
  obtain ⟨L, hL, hL_eval⟩ := M.fisherMatrix_hasFDerivAt' hθ j k
  rw [hL.fderiv]
  exact hL_eval i

-- ════════════════════════════════════════════════════════════════════
-- §5. The third KL derivative at the diagonal
-- ════════════════════════════════════════════════════════════════════

/-- **Componentwise diagonal third derivative.**  At any diagonal point
`β` of the domain,

  `∂ᵢ∂ⱼ∂ₖ D(β‖·)|_β = C_{ijk} + Γᵐ_{ik,j} + Γᵐ_{jk,i} + Γᵐ_{ij,k}`.

This packages `klDiv_third_partial` and
`klDiv_third_deriv_decomposition` with all hypotheses discharged from
the `ThriceDifferentiableModel` fields and the Bartlett identities. -/
lemma klDiv_third_deriv_eval {β : ParamSpace n} (hβ : β ∈ M.paramDomain)
    (i j k : Fin n) :
    fderiv ℝ (fun θ₁ =>
      fderiv ℝ (fun θ₂ =>
        fderiv ℝ (M.klDiv β) θ₂ (EuclideanSpace.single k 1)) θ₁
        (EuclideanSpace.single j 1)) β (EuclideanSpace.single i 1) =
    M.cubicTensor β i j k + M.mConnectionCoeff β i k j +
    M.mConnectionCoeff β j k i + M.mConnectionCoeff β i j k := by
  -- the second partial agrees near β with the scorePartial integral
  have h_ev2 : ∀ᶠ θ' in 𝓝 β,
      fderiv ℝ (fun θ₂ =>
        fderiv ℝ (M.klDiv β) θ₂ (EuclideanSpace.single k 1)) θ'
        (EuclideanSpace.single j 1) =
      -∫ ω, M.density β ω * M.scorePartial θ' j k ω ∂M.refMeasure := by
    filter_upwards [M.isOpen_paramDomain.mem_nhds hβ] with θ' hθ'
    obtain ⟨g₁, hg₁, hg₁_eval⟩ := M.cross_score_hasFDerivAt' hβ hθ' k
    have hg₁' : HasFDerivAt (fun θ₂ =>
        fderiv ℝ (M.klDiv β) θ₂ (EuclideanSpace.single k 1)) g₁ θ' :=
      hg₁.congr_of_eventuallyEq (by
        filter_upwards [M.isOpen_paramDomain.mem_nhds hθ'] with θ₂ hθ₂
        exact M.klDiv_partial_j hβ hθ₂ k)
    rw [hg₁'.fderiv]
    exact hg₁_eval j
  -- the third Leibniz interchange at β
  obtain ⟨g₂, hg₂, _⟩ := M.klDiv_third_partial hβ j k
    (M.scorePartial_fderiv_bound β hβ β hβ j k)
    (M.scorePartial_density_integrable β hβ j k)
    (M.scorePartial_deriv_aestronglyMeasurable β hβ j k)
    (M.scorePartial_density_aestronglyMeasurable β hβ j k)
  have hg₂' : HasFDerivAt (fun θ' =>
      fderiv ℝ (fun θ₂ =>
        fderiv ℝ (M.klDiv β) θ₂ (EuclideanSpace.single k 1)) θ'
        (EuclideanSpace.single j 1)) g₂ β :=
    hg₂.congr_of_eventuallyEq h_ev2
  rw [hg₂'.fderiv]
  exact M.klDiv_third_deriv_decomposition hβ i j k
    (fun j' k' => M.klDiv_third_partial hβ j' k'
      (M.scorePartial_fderiv_bound β hβ β hβ j' k')
      (M.scorePartial_density_integrable β hβ j' k')
      (M.scorePartial_deriv_aestronglyMeasurable β hβ j' k')
      (M.scorePartial_density_aestronglyMeasurable β hβ j' k'))
    (fun i' j' k' => M.bartlett_third hβ i' j' k')
    h_ev2
    (M.scorePartial_deriv_integrable β hβ i j k)
    (M.score_scorePartial_integrable β hβ j i k)
    (M.score_scorePartial_integrable β hβ i j k)
    (M.score_scorePartial_integrable β hβ k i j)
    (M.tripleScore_integrable β hβ i j k)
    g₂ hg₂'

/-- **Trilinear diagonal third derivative.**  The third Fréchet
derivative of `D(β‖·)` at `β` is the trilinear form whose entries are
given by `klDiv_third_deriv_eval`:

  `D'''(β‖·)(β)[x, y, z]
     = ∑ᵢⱼₖ xᵢ yⱼ zₖ (C_{ijk} + Γᵐ_{ik,j} + Γᵐ_{jk,i} + Γᵐ_{ij,k})`. -/
lemma klDiv_third_deriv_trilin {β : ParamSpace n} (hβ : β ∈ M.paramDomain)
    (x y z : ParamSpace n) :
    fderiv ℝ (fun θ₁ =>
      fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv β) θ₂ z) θ₁ y) β x =
    ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      x i * y j * z k *
        (M.cubicTensor β i j k + M.mConnectionCoeff β i k j +
         M.mConnectionCoeff β j k i + M.mConnectionCoeff β i j k) := by
  -- derivative data for the scalar second partials at every domain point
  have hS : ∀ θ₁ ∈ M.paramDomain, ∀ k : Fin n,
      ∃ g : ParamSpace n →L[ℝ] ℝ,
        HasFDerivAt (fun θ₂ =>
          fderiv ℝ (M.klDiv β) θ₂ (EuclideanSpace.single k 1)) g θ₁ := by
    intro θ₁ hθ₁ k
    obtain ⟨g₁, hg₁, _⟩ := M.cross_score_hasFDerivAt' hβ hθ₁ k
    exact ⟨g₁, hg₁.congr_of_eventuallyEq (by
      filter_upwards [M.isOpen_paramDomain.mem_nhds hθ₁] with θ₂ hθ₂
      exact M.klDiv_partial_j hβ hθ₂ k)⟩
  -- (i) innermost slot: expand z over the basis (pointwise CLM linearity)
  have hz : (fun θ₂ => fderiv ℝ (M.klDiv β) θ₂ z) =
      fun θ₂ => ∑ k : Fin n, z.ofLp k *
        fderiv ℝ (M.klDiv β) θ₂ (EuclideanSpace.single k 1) := by
    funext θ₂
    conv_lhs => rw [show z = ∑ k : Fin n, z.ofLp k •
        EuclideanSpace.single k 1 from by ext p; simp [Pi.single,
          Function.update_apply, Finset.mem_univ]]
    rw [map_sum]; simp_rw [map_smul, smul_eq_mul]
  -- (ii) middle slot: differentiate the k-sum on the domain, expand y
  have h_mid : ∀ θ₁ ∈ M.paramDomain,
      fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv β) θ₂ z) θ₁ y =
      ∑ k : Fin n, ∑ j : Fin n, z.ofLp k * y.ofLp j *
        fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv β) θ₂
          (EuclideanSpace.single k 1)) θ₁ (EuclideanSpace.single j 1) := by
    intro θ₁ hθ₁
    rw [hz]
    have hsum : HasFDerivAt (fun θ₂ => ∑ k : Fin n, z.ofLp k *
        fderiv ℝ (M.klDiv β) θ₂ (EuclideanSpace.single k 1))
        (∑ k : Fin n, z.ofLp k • (hS θ₁ hθ₁ k).choose) θ₁ :=
      HasFDerivAt.fun_sum fun k _ =>
        ((hS θ₁ hθ₁ k).choose_spec).const_mul (z.ofLp k)
    rw [hsum.fderiv]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← ((hS θ₁ hθ₁ k).choose_spec).fderiv]
    conv_lhs => rw [show y = ∑ j : Fin n, y.ofLp j •
        EuclideanSpace.single j 1 from by ext p; simp [Pi.single,
          Function.update_apply, Finset.mem_univ]]
    rw [map_sum]
    simp_rw [map_smul, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- (iii) outermost slot
  have h_mid_ev : (fun θ₁ => fderiv ℝ (fun θ₂ =>
      fderiv ℝ (M.klDiv β) θ₂ z) θ₁ y) =ᶠ[𝓝 β]
      (fun θ₁ => ∑ k : Fin n, ∑ j : Fin n, z.ofLp k * y.ofLp j *
        fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv β) θ₂
          (EuclideanSpace.single k 1)) θ₁ (EuclideanSpace.single j 1)) := by
    filter_upwards [M.isOpen_paramDomain.mem_nhds hβ] with θ₁ hθ₁
    exact h_mid θ₁ hθ₁
  rw [DFunLike.congr_fun h_mid_ev.fderiv_eq x]
  -- derivative data for the scalar third partials at β
  have hT : ∀ j k : Fin n,
      ∃ g₂ : ParamSpace n →L[ℝ] ℝ,
        HasFDerivAt (fun θ₁ =>
          fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv β) θ₂
            (EuclideanSpace.single k 1)) θ₁
            (EuclideanSpace.single j 1)) g₂ β := by
    intro j k
    obtain ⟨g₂, hg₂, _⟩ := M.klDiv_third_partial hβ j k
      (M.scorePartial_fderiv_bound β hβ β hβ j k)
      (M.scorePartial_density_integrable β hβ j k)
      (M.scorePartial_deriv_aestronglyMeasurable β hβ j k)
      (M.scorePartial_density_aestronglyMeasurable β hβ j k)
    refine ⟨g₂, hg₂.congr_of_eventuallyEq ?_⟩
    filter_upwards [M.isOpen_paramDomain.mem_nhds hβ] with θ' hθ'
    obtain ⟨g₁, hg₁, hg₁_eval⟩ := M.cross_score_hasFDerivAt' hβ hθ' k
    have hg₁' : HasFDerivAt (fun θ₂ =>
        fderiv ℝ (M.klDiv β) θ₂ (EuclideanSpace.single k 1)) g₁ θ' :=
      hg₁.congr_of_eventuallyEq (by
        filter_upwards [M.isOpen_paramDomain.mem_nhds hθ'] with θ₂ hθ₂
        exact M.klDiv_partial_j hβ hθ₂ k)
    rw [hg₁'.fderiv]
    exact hg₁_eval j
  have hsum2 : HasFDerivAt (fun θ₁ => ∑ k : Fin n, ∑ j : Fin n,
      z.ofLp k * y.ofLp j *
      fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv β) θ₂
        (EuclideanSpace.single k 1)) θ₁ (EuclideanSpace.single j 1))
      (∑ k : Fin n, ∑ j : Fin n,
        (z.ofLp k * y.ofLp j) • (hT j k).choose) β :=
    HasFDerivAt.fun_sum fun k _ => HasFDerivAt.fun_sum fun j _ =>
      ((hT j k).choose_spec).const_mul (z.ofLp k * y.ofLp j)
  rw [hsum2.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  -- evaluate each (hT j k).choose at x componentwise
  have hT_eval : ∀ j k : Fin n, (hT j k).choose x =
      ∑ i : Fin n, x.ofLp i *
        (M.cubicTensor β i j k + M.mConnectionCoeff β i k j +
         M.mConnectionCoeff β j k i + M.mConnectionCoeff β i j k) := by
    intro j k
    conv_lhs => rw [show x = ∑ i : Fin n, x.ofLp i •
        EuclideanSpace.single i 1 from by ext p; simp [Pi.single,
          Function.update_apply, Finset.mem_univ]]
    rw [map_sum]
    simp_rw [map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [show (hT j k).choose (EuclideanSpace.single i 1) =
        fderiv ℝ (fun θ₁ => fderiv ℝ (fun θ₂ =>
          fderiv ℝ (M.klDiv β) θ₂ (EuclideanSpace.single k 1)) θ₁
          (EuclideanSpace.single j 1)) β (EuclideanSpace.single i 1) from by
      rw [((hT j k).choose_spec).fderiv]]
    exact M.klDiv_third_deriv_eval hβ i j k
  -- assemble and reorder (k, j, i) → (i, j, k)
  calc (∑ k : Fin n, ∑ j : Fin n,
        z.ofLp k * y.ofLp j * (hT j k).choose x)
      = ∑ k : Fin n, ∑ j : Fin n, ∑ i : Fin n,
          x.ofLp i * y.ofLp j * z.ofLp k *
          (M.cubicTensor β i j k + M.mConnectionCoeff β i k j +
           M.mConnectionCoeff β j k i + M.mConnectionCoeff β i j k) := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hT_eval j k, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin n,
          x.ofLp i * y.ofLp j * z.ofLp k *
          (M.cubicTensor β i j k + M.mConnectionCoeff β i k j +
           M.mConnectionCoeff β j k i + M.mConnectionCoeff β i j k) :=
        Finset.sum_comm
    _ = ∑ j : Fin n, ∑ i : Fin n, ∑ k : Fin n,
          x.ofLp i * y.ofLp j * z.ofLp k *
          (M.cubicTensor β i j k + M.mConnectionCoeff β i k j +
           M.mConnectionCoeff β j k i + M.mConnectionCoeff β i j k) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          x.ofLp i * y.ofLp j * z.ofLp k *
          (M.cubicTensor β i j k + M.mConnectionCoeff β i k j +
           M.mConnectionCoeff β j k i + M.mConnectionCoeff β i j k) :=
        Finset.sum_comm
    _ = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          x i * y j * z k *
          (M.cubicTensor β i j k + M.mConnectionCoeff β i k j +
           M.mConnectionCoeff β j k i + M.mConnectionCoeff β i j k) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => by ring

namespace DivergencePreservingFamily

variable {M : ThriceDifferentiableModel n Ω}
variable (F : M.toTwiceDifferentiableModel.DivergencePreservingFamily)
open TwiceDifferentiableModel ThriceDifferentiableModel
open TwiceDifferentiableModel.DivergencePreservingFamily

-- ════════════════════════════════════════════════════════════════════
-- §6. Differentiating `preserves_fisher` across base points
-- ════════════════════════════════════════════════════════════════════

/-- The pulled-back metric on the moving frame and the Fisher matrix
agree as functions on the domain, hence their derivatives at `θ` agree.
(Steps 1–2 of the original skeleton.) -/
lemma pullback_fisher_fderiv_eq
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (t : ℝ) (a b c : Fin n) :
    fderiv ℝ (fun θ' =>
      M.toRegularStatisticalModel.fisherBilin (F.φ t θ')
        (fderiv ℝ (F.φ t) θ' (EuclideanSpace.single a 1))
        (fderiv ℝ (F.φ t) θ' (EuclideanSpace.single b 1))) θ
      (EuclideanSpace.single c 1) =
    fderiv ℝ (fun θ' =>
      M.toRegularStatisticalModel.fisherMatrix θ' a b) θ
      (EuclideanSpace.single c 1) := by
  have h_ev : (fun θ' =>
      M.toRegularStatisticalModel.fisherBilin (F.φ t θ')
        (fderiv ℝ (F.φ t) θ' (EuclideanSpace.single a 1))
        (fderiv ℝ (F.φ t) θ' (EuclideanSpace.single b 1))) =ᶠ[𝓝 θ]
      (fun θ' => M.toRegularStatisticalModel.fisherMatrix θ' a b) := by
    filter_upwards [M.isOpen_paramDomain.mem_nhds hθ] with θ' hθ'
    rw [F.preserves_fisher hθ' t _ _,
        M.toRegularStatisticalModel.fisherBilin_single]
  exact DFunLike.congr_fun h_ev.fderiv_eq (EuclideanSpace.single c 1)

/-- **Product rule for the pulled-back metric on the moving frame.**
Differentiating `θ' ↦ g_{φθ'}(dφ(θ')eₐ, dφ(θ')eᵦ)` in direction `e_c`
splits into the metric variation on frozen vectors plus the two
second-derivative corrections:

  `∂_c [g_{φ(·)}(dφ·eₐ, dφ·eᵦ)](θ)
     = ∑ᵢⱼ (uₐ)ᵢ(uᵦ)ⱼ · ∑ₖ (u_c)ₖ (C(α)ₖᵢⱼ + Γᵐ(α)_{ki,j} + Γᵐ(α)_{kj,i})
       + g_α(d²φ_{ca}, uᵦ) + g_α(uₐ, d²φ_{cb})`. -/
lemma pullback_metric_fderiv_split
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (t : ℝ) (a b c : Fin n) :
    fderiv ℝ (fun θ' =>
      M.toRegularStatisticalModel.fisherBilin (F.φ t θ')
        (fderiv ℝ (F.φ t) θ' (EuclideanSpace.single a 1))
        (fderiv ℝ (F.φ t) θ' (EuclideanSpace.single b 1))) θ
      (EuclideanSpace.single c 1) =
    (∑ i : Fin n, ∑ j : Fin n,
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) i *
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) j *
      ∑ k : Fin n,
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)).ofLp k *
        (M.cubicTensor (F.φ t θ) k i j +
         M.mConnectionCoeff (F.φ t θ) k i j +
         M.mConnectionCoeff (F.φ t θ) k j i))
    + M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
        (F.secondDerivPhi t θ c a)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
    + M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
        (F.secondDerivPhi t θ c b) := by
  have hα : F.φ t θ ∈ M.paramDomain := F.maps_domain t θ hθ
  have hSq : M.toRegularStatisticalModel.ScoreSqIntegrableModel (F.φ t θ) :=
    M.scoreSqIntegrable _ hα
  have hφ_smooth : ContDiff ℝ ⊤ (F.φ t) :=
    F.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hφ_diff : ∀ θ', DifferentiableAt ℝ (F.φ t) θ' := fun θ' =>
    (hφ_smooth.differentiable WithTop.top_ne_zero).differentiableAt
  have hV_diff : ∀ x : Fin n, DifferentiableAt ℝ
      (fun θ' => fderiv ℝ (F.φ t) θ' (EuclideanSpace.single x 1)) θ :=
    fun x => ((hφ_smooth.fderiv_right le_rfl).differentiable
      WithTop.top_ne_zero).differentiableAt.clm_apply (differentiableAt_const _)
  -- coordinates of the moving frame, with explicit derivatives
  -- NOTE: if `EuclideanSpace.proj`/`EuclideanSpace.proj_apply` are named
  -- differently in your Mathlib pin, `innerSL ℝ (EuclideanSpace.single i 1)`
  -- together with `EuclideanSpace.inner_single_left` is the fallback.
  have hA : ∀ x i : Fin n, HasFDerivAt
      (fun θ' => (fderiv ℝ (F.φ t) θ' (EuclideanSpace.single x 1)) i)
      ((EuclideanSpace.proj i).comp
        (fderiv ℝ (fun θ' =>
          fderiv ℝ (F.φ t) θ' (EuclideanSpace.single x 1)) θ)) θ := by
    intro x i
    refine HasFDerivAt.congr_of_eventuallyEq
      ((EuclideanSpace.proj i).hasFDerivAt.comp θ (hV_diff x).hasFDerivAt) ?_
    filter_upwards with θ'
    simp only [EuclideanSpace.coe_proj, Function.comp_apply]
  -- Fisher entries along the flow, via the new structure field
  have hG : ∀ i j : Fin n, ∃ L : ParamSpace n →L[ℝ] ℝ,
      HasFDerivAt (fun θ' =>
        M.toRegularStatisticalModel.fisherMatrix (F.φ t θ') i j)
        (L.comp (fderiv ℝ (F.φ t) θ)) θ ∧
      ∀ k : Fin n, L (EuclideanSpace.single k 1) =
        M.cubicTensor (F.φ t θ) k i j +
        M.mConnectionCoeff (F.φ t θ) k i j +
        M.mConnectionCoeff (F.φ t θ) k j i := by
    intro i j
    obtain ⟨L, hL, hL_eval⟩ := M.fisherMatrix_hasFDerivAt' hα i j
    refine ⟨L, ?_, hL_eval⟩
    have h₀ := hL.comp θ (hφ_diff θ).hasFDerivAt
    convert h₀ using 1
  -- the pulled-back metric agrees near θ with the coordinate sum
  have hH_ev : (fun θ' =>
      M.toRegularStatisticalModel.fisherBilin (F.φ t θ')
        (fderiv ℝ (F.φ t) θ' (EuclideanSpace.single a 1))
        (fderiv ℝ (F.φ t) θ' (EuclideanSpace.single b 1))) =ᶠ[𝓝 θ]
      (fun θ' => ∑ i : Fin n, ∑ j : Fin n,
        (fderiv ℝ (F.φ t) θ' (EuclideanSpace.single a 1)) i *
        (fderiv ℝ (F.φ t) θ' (EuclideanSpace.single b 1)) j *
        M.toRegularStatisticalModel.fisherMatrix (F.φ t θ') i j) := by
    filter_upwards [M.isOpen_paramDomain.mem_nhds hθ] with θ' hθ'
    have hβ : F.φ t θ' ∈ M.paramDomain := F.maps_domain t θ' hθ'
    exact M.toRegularStatisticalModel.fisherBilin_eq_sum_fisherMatrix hβ
      (M.scoreSqIntegrable _ hβ) _ _
  rw [DFunLike.congr_fun hH_ev.fderiv_eq (EuclideanSpace.single c 1)]
  -- product rule on each coordinate triple product, summed
  have hsum : HasFDerivAt (fun θ' => ∑ i : Fin n, ∑ j : Fin n,
      (fderiv ℝ (F.φ t) θ' (EuclideanSpace.single a 1)) i *
      (fderiv ℝ (F.φ t) θ' (EuclideanSpace.single b 1)) j *
      M.toRegularStatisticalModel.fisherMatrix (F.φ t θ') i j)
      (∑ i : Fin n, ∑ j : Fin n,
        (((fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) i *
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) j) •
          ((hG i j).choose.comp (fderiv ℝ (F.φ t) θ)) +
        M.toRegularStatisticalModel.fisherMatrix (F.φ t θ) i j •
          ((fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) i •
            ((EuclideanSpace.proj j).comp
              (fderiv ℝ (fun θ' => fderiv ℝ (F.φ t) θ'
                (EuclideanSpace.single b 1)) θ)) +
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) j •
            ((EuclideanSpace.proj i).comp
              (fderiv ℝ (fun θ' => fderiv ℝ (F.φ t) θ'
                (EuclideanSpace.single a 1)) θ))))) θ :=
    HasFDerivAt.fun_sum fun i _ => HasFDerivAt.fun_sum fun j _ =>
      ((hA a i).mul (hA b j)).mul (hG i j).choose_spec.1
  rw [hsum.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul]
  -- evaluate the metric-variation factor on dφ(e_c) componentwise
  have hLval : ∀ i j : Fin n,
      (hG i j).choose (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) =
      ∑ k : Fin n,
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)).ofLp k *
        (M.cubicTensor (F.φ t θ) k i j +
         M.mConnectionCoeff (F.φ t θ) k i j +
         M.mConnectionCoeff (F.φ t θ) k j i) := by
    intro i j
    conv_lhs => rw [show fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1) =
        ∑ k : Fin n,
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)).ofLp k •
          EuclideanSpace.single k 1 from by ext p; simp [Pi.single,
            Function.update_apply, Finset.mem_univ]]
    rw [map_sum]
    simp_rw [map_smul, smul_eq_mul, (hG i j).choose_spec.2]
  -- identify the second-derivative coordinates and assemble
  have hw : ∀ x : Fin n,
      fderiv ℝ (fun θ' => fderiv ℝ (F.φ t) θ' (EuclideanSpace.single x 1)) θ
        (EuclideanSpace.single c 1) = F.secondDerivPhi t θ c x :=
    fun _ => rfl
  simp only [hLval, EuclideanSpace.coe_proj, hw]
  -- expand the two correction bilinear forms and close entrywise
  rw [M.toRegularStatisticalModel.fisherBilin_eq_sum_fisherMatrix hα hSq
        (F.secondDerivPhi t θ c a)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)),
      M.toRegularStatisticalModel.fisherBilin_eq_sum_fisherMatrix hα hSq
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
        (F.secondDerivPhi t θ c b),
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Identity (I): the differentiated isometry equation.**  For the
pair `(a, b)` differentiated in direction `c`:

  `Γᵗʳⁱ(α)(u_c,u_a,u_b) + Γᵗʳⁱ(α)(u_c,u_b,u_a) + C(α)[uₐ,uᵦ,u_c]
     + g_α(d²φ_{ca}, uᵦ) + g_α(uₐ, d²φ_{cb})
   = Γᵐ(θ)_{ca,b} + Γᵐ(θ)_{cb,a} + C(θ)_{cab}`. -/
lemma fisher_derivative_identity
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (t : ℝ) (a b c : Fin n) :
    M.mConnectionTrilin (F.φ t θ)
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) +
    M.mConnectionTrilin (F.φ t θ)
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) +
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) i *
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) j *
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) k *
      M.cubicTensor (F.φ t θ) i j k) +
    M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
      (F.secondDerivPhi t θ c a)
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) +
    M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
      (F.secondDerivPhi t θ c b)
    = M.mConnectionCoeff θ c a b + M.mConnectionCoeff θ c b a +
      M.cubicTensor θ c a b := by
  have hα : F.φ t θ ∈ M.paramDomain := F.maps_domain t θ hθ
  -- the three evaluations of the same derivative
  have hkey : (∑ i : Fin n, ∑ j : Fin n,
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) i *
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) j *
      ∑ k : Fin n,
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)).ofLp k *
        (M.cubicTensor (F.φ t θ) k i j +
         M.mConnectionCoeff (F.φ t θ) k i j +
         M.mConnectionCoeff (F.φ t θ) k j i))
      + M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
          (F.secondDerivPhi t θ c a)
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
      + M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
          (F.secondDerivPhi t θ c b)
      = M.cubicTensor θ c a b + M.mConnectionCoeff θ c a b +
        M.mConnectionCoeff θ c b a :=
    (pullback_metric_fderiv_split F hθ t a b c).symm.trans
      ((pullback_fisher_fderiv_eq F hθ t a b c).trans
        (M.fisherMatrix_fderiv_single hθ c a b))
  -- split the nested sum into cubic + the two trilinear pieces
  have hflat : (∑ i : Fin n, ∑ j : Fin n,
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) i *
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) j *
      ∑ k : Fin n,
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)).ofLp k *
        (M.cubicTensor (F.φ t θ) k i j +
         M.mConnectionCoeff (F.φ t θ) k i j +
         M.mConnectionCoeff (F.φ t θ) k j i)) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) i *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) j *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) k *
        (M.cubicTensor (F.φ t θ) k i j +
         M.mConnectionCoeff (F.φ t θ) k i j +
         M.mConnectionCoeff (F.φ t θ) k j i) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
  have hsplit : (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) i *
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) j *
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) k *
      (M.cubicTensor (F.φ t θ) k i j +
       M.mConnectionCoeff (F.φ t θ) k i j +
       M.mConnectionCoeff (F.φ t θ) k j i)) =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) i *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) j *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) k *
        M.cubicTensor (F.φ t θ) i j k) +
      M.mConnectionTrilin (F.φ t θ)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) +
      M.mConnectionTrilin (F.φ t θ)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) := by
    simp only [mul_add, Finset.sum_add_distrib]
    rw [M.cubic_relabel_kij hα
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)),
        M.trilin_relabel_kij (F.φ t θ)
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)),
        M.trilin_relabel_kji (F.φ t θ)
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))]
  rw [hflat, hsplit] at hkey
  linarith [hkey]

-- ════════════════════════════════════════════════════════════════════
-- §7. The transfer identity (M1), cubic preservation, and the main law
-- ════════════════════════════════════════════════════════════════════

/-- **Identity (M1): pullback of the diagonal third derivative.**
Combining `kl_faa_di_bruno`, `third_deriv_transfer`, and the diagonal
formula `klDiv_third_deriv_eval`:

  `T + g_α(d²φ_{ab},u_c) + g_α(d²φ_{ac},uᵦ) + g_α(uₐ,d²φ_{bc})
     = C(θ)_{abc} + Γᵐ(θ)_{ac,b} + Γᵐ(θ)_{bc,a} + Γᵐ(θ)_{ab,c}`. -/
lemma third_deriv_pullback
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (t : ℝ) (a b c : Fin n) :
    fderiv ℝ (fun θ₁ =>
      fderiv ℝ (fun θ₂ =>
        fderiv ℝ (M.klDiv (F.φ t θ)) θ₂
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))) θ₁
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))) (F.φ t θ)
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
    + M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
        (F.secondDerivPhi t θ a b)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
    + M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
        (F.secondDerivPhi t θ a c)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
    + M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
        (F.secondDerivPhi t θ b c)
    = M.cubicTensor θ a b c + M.mConnectionCoeff θ a c b +
      M.mConnectionCoeff θ b c a + M.mConnectionCoeff θ a b c := by
  have hFdB :
      fderiv ℝ (fun θ₁ =>
        fderiv ℝ (fun θ₂ =>
          fderiv ℝ (fun θ₃ => M.klDiv (F.φ t θ) (F.φ t θ₃)) θ₂
            (EuclideanSpace.single c 1)) θ₁
          (EuclideanSpace.single b 1)) θ
        (EuclideanSpace.single a 1) =
      fderiv ℝ (fun θ₁ =>
        fderiv ℝ (fun θ₂ =>
          fderiv ℝ (M.klDiv (F.φ t θ)) θ₂
            (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))) θ₁
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))) (F.φ t θ)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
      + M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
          (F.secondDerivPhi t θ a b)
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
      + M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
          (F.secondDerivPhi t θ a c)
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
      + M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
          (F.secondDerivPhi t θ b c) :=
    kl_faa_di_bruno F hθ t a b c
  have hTrans := F.third_deriv_transfer hθ t a b c
  have hEval := M.klDiv_third_deriv_eval hθ a b c
  linarith [hFdB, hTrans, hEval]

/-- **Cubic-tensor preservation on the moving frame.**  The pullback of
`C(α)` through `dφ_t(θ)` on basis vectors recovers `C(θ)`:

  `∑ᵢⱼₖ (uₐ)ᵢ(uᵦ)ⱼ(u_c)ₖ C(φ_tθ)ᵢⱼₖ = C(θ)_{abc}`. -/
lemma preserves_cubic_basis
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (t : ℝ) (a b c : Fin n) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) i *
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) j *
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) k *
      M.cubicTensor (F.φ t θ) i j k) = M.cubicTensor θ a b c := by
  have hα : F.φ t θ ∈ M.paramDomain := F.maps_domain t θ hθ
  -- the three differentiated-isometry identities
  have hI₁ := fisher_derivative_identity F hθ t a b c
  have hI₂ := fisher_derivative_identity F hθ t a c b
  have hI₃ := fisher_derivative_identity F hθ t b c a
  -- the transfer identity
  have hD1 := third_deriv_pullback F hθ t a b c
  -- the trilinear decomposition of the tensorial term
  have hM3 :
      fderiv ℝ (fun θ₁ =>
        fderiv ℝ (fun θ₂ =>
          fderiv ℝ (M.klDiv (F.φ t θ)) θ₂
            (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))) θ₁
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))) (F.φ t θ)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) i *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) j *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) k *
        M.cubicTensor (F.φ t θ) i j k) +
      M.mConnectionTrilin (F.φ t θ)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) +
      M.mConnectionTrilin (F.φ t θ)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) +
      M.mConnectionTrilin (F.φ t θ)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) := by
    rw [M.klDiv_third_deriv_trilin hα
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [M.trilin_relabel_ikj (F.φ t θ)
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)),
        M.trilin_relabel_jki (F.φ t θ)
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)),
        ← M.mConnectionTrilin_eq_sum (F.φ t θ)
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))]
  -- ── normalize hI₁: sort the trilinear slots, the d²φ indices,
  --    and the θ-side tensor indices ──
  rw [M.mConnectionTrilin_symm₁₂ hα
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)),
      M.mConnectionTrilin_symm₁₂ hα
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)),
      F.secondDerivPhi_symm t θ c a, F.secondDerivPhi_symm t θ c b,
      M.mConnectionCoeff_symm₁₂ hθ c a b,
      M.mConnectionCoeff_symm₁₂ hθ c b a,
      M.cubicTensor_symm₁₂ hθ c a b,
      M.cubicTensor_symm₂₃ hθ a c b] at hI₁
  -- ── normalize hI₂ ──
  have hQ₂ : (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) i *
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) j *
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) k *
      M.cubicTensor (F.φ t θ) i j k) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) i *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) j *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) k *
        M.cubicTensor (F.φ t θ) i j k :=
    (M.cubic_sum_swap₂₃ hα
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))).symm
  rw [M.mConnectionTrilin_symm₁₂ hα
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)),
      hQ₂,
      F.secondDerivPhi_symm t θ b a,
      M.mConnectionCoeff_symm₁₂ hθ b a c,
      M.cubicTensor_symm₁₂ hθ b a c] at hI₂
  -- ── normalize hI₃ ──
  have hQ₃ : (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) i *
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) j *
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) k *
      M.cubicTensor (F.φ t θ) i j k) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) i *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) j *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) k *
        M.cubicTensor (F.φ t θ) i j k := by
    rw [M.cubic_sum_swap₂₃ hα
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)),
        M.cubic_sum_swap₁₂ hα
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))]
  rw [hQ₃,
      M.toRegularStatisticalModel.fisherBilin_symm (F.φ t θ)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
        (F.secondDerivPhi t θ a c)] at hI₃
  -- ── solve the linear system ──
  linarith [hI₁, hI₂, hI₃, hD1, hM3]

/-- **m-Connection transformation law.**  Differentiating the isometry
identity `g(φ_tθ')(dφ·eₐ, dφ·eᵦ) = g(θ')_{ab}` from `preserves_fisher`
in direction `e_c`, combined with the Faà di Bruno expansion of the
transferred third derivative, gives

  `[D'''(α‖·)(α)(uₐ,uᵦ,u_c) − C(α)(uₐ,uᵦ,u_c)]
     + g_α(d²φ_{ab}, u_c) + g_α(d²φ_{ac}, uᵦ) + g_α(uₐ, d²φ_{bc})
   = Γᵐ(θ)_{ac,b} + Γᵐ(θ)_{bc,a} + Γᵐ(θ)_{ab,c}`,

i.e. the m-connection of the image point, pulled back through `dφ_t`
and corrected by the metric-paired second derivatives of the flow, is
the m-connection at the source.  Equivalently (given
`third_deriv_pullback`): the cubic tensor is preserved. -/
theorem mConnection_correction
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (t : ℝ) (a b c : Fin n) :
    (fderiv ℝ (fun θ₁ =>
      fderiv ℝ (fun θ₂ =>
        fderiv ℝ (M.klDiv (F.φ t θ)) θ₂
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))) θ₁
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))) (F.φ t θ)
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
    - ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) i *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) j *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) k *
        M.cubicTensor (F.φ t θ) i j k)
    + M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
        (F.secondDerivPhi t θ a b)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
    + M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
        (F.secondDerivPhi t θ a c)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
    + M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
        (F.secondDerivPhi t θ b c)
    = M.mConnectionCoeff θ a c b + M.mConnectionCoeff θ b c a +
      M.mConnectionCoeff θ a b c := by
  have hD1 := third_deriv_pullback F hθ t a b c
  have hQ := preserves_cubic_basis F hθ t a b c
  linarith [hD1, hQ]

end DivergencePreservingFamily

end ThriceDifferentiableModel

end Spectra.InformationGeometry
