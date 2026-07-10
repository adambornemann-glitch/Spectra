/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Flow.MixtureSymmetry
import Spectra.InformationGeometry.Flow.ThirdDerivative
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
# Identity (I): differentiating `preserves_fisher` across base points

Third of four files proving the m-connection transformation law (see
`MixtureConnection.lean`'s module docstring for the full roadmap). Builds on
`MixtureSymmetry.lean` and `ThirdDerivative.lean` to differentiate the isometry equation
`preserves_fisher` across base points, giving identity (I):

  `Γᵗʳⁱ(α)(u_c,u_a,u_b) + Γᵗʳⁱ(α)(u_c,u_b,u_a) + C(α)[uₐ,uᵦ,u_c]
     + g_α(d²φ_{ca}, uᵦ) + g_α(uₐ, d²φ_{cb})
   = Γᵐ(θ)_{ca,b} + Γᵐ(θ)_{cb,a} + C(θ)_{cab}`,

and its `(a,c,b)`, `(b,c,a)` permutations (used by `MixtureConnection.lean`'s
`preserves_cubic_basis`).

## Main statements

* `pullback_fisher_fderiv_eq` — the pulled-back metric and the Fisher matrix agree as functions
  of the base point, hence so do their derivatives
* `pullback_metric_fderiv_split` — the product-rule expansion of that derivative into the
  metric-variation term plus the two second-derivative corrections
* `fisher_derivative_identity` — identity (I)

Downstream: `MixtureConnection.lean`.
-/

open MeasureTheory Finset Filter Topology TopologicalSpace
namespace Spectra.InformationGeometry

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

namespace ThriceDifferentiableModel

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
  have hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) (F.φ t) :=
    F.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hφ_diff : ∀ θ', DifferentiableAt ℝ (F.φ t) θ' := fun θ' =>
    (hφ_smooth.differentiable (by simp)).differentiableAt
  have hV_diff : ∀ x : Fin n, DifferentiableAt ℝ
      (fun θ' => fderiv ℝ (F.φ t) θ' (EuclideanSpace.single x 1)) θ :=
    fun x => ((hφ_smooth.fderiv_right (m := (⊤ : ℕ∞)) (by exact_mod_cast le_top)).differentiable
      (by simp)).differentiableAt.clm_apply (differentiableAt_const _)
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
    conv_lhs => rw [paramSpace_eq_sum_single
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))]
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
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) :=
    M.cubic_connection_split_kij hα
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
  rw [hflat, hsplit] at hkey
  linarith [hkey]

end DivergencePreservingFamily

end ThriceDifferentiableModel

end Spectra.InformationGeometry
