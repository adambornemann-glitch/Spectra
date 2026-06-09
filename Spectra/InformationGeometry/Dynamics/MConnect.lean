/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: InformationGeometry/DivergenceDynamics.lean
-/
import LogosLibrary.InformationGeometry.Fisher.StatisticalManifold
import LogosLibrary.InformationGeometry.CramerRao.SchrodingerRLD
import LogosLibrary.InformationGeometry.Dynamics.Hessian
import LogosLibrary.InformationGeometry.Dynamics.CubicTensor
import LogosLibrary.InformationGeometry.Dynamics.AlphaConnect
import LogosLibrary.InformationGeometry.Dynamics.Family
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
variable (M : TwiceDifferentiableModel n Ω)        -- keep explicit at TDM level
namespace DivergencePreservingFamily
variable {M : TwiceDifferentiableModel n Ω}        -- shadow as implicit here
variable (F : M.DivergencePreservingFamily)



/-- **m-Connection transformation law.** Differentiating the identity
  g(φ_t(θ))(dφ_t·eₐ, dφ_t·eᵦ) = g(θ)_{ab}
from `preserves_fisher` in direction ec:

  [Γᵐ-type terms at α, pulled back through dφ]
  + g(α)(d²φ(eₐ,ec), dφ·eᵦ) + g(α)(dφ·eₐ, d²φ(eᵦ,ec))
  = [derivative of g(θ)_{ab} in direction ec]

Combined with the analogous identity for cyclic permutations of the
g·d²φ Faà di Bruno corrections, this shows:

  ∑_{i,j,k} Γᵐ(α)_{ik,j} (dφⁱₐ)(dφᵏc)(dφʲᵦ)
  + ∑_{i,j,k} Γᵐ(α)_{jk,i} (dφʲᵦ)(dφᵏc)(dφⁱₐ)
  + ∑_{i,j,k} Γᵐ(α)_{ij,k} (dφⁱₐ)(dφʲᵦ)(dφᵏc)
  + [three g·d²φ terms from Faà di Bruno]
  = Γᵐ(θ)_{ac,b} + Γᵐ(θ)_{bc,a} + Γᵐ(θ)_{ab,c} -/
lemma mConnection_correction
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (t : ℝ)
    (a b c : Fin n) :
    let α := F.φ t θ
    let dφ := fderiv ℝ (F.φ t) θ
    (fderiv ℝ (fun θ₁ =>
      fderiv ℝ (fun θ₂ =>
        fderiv ℝ (M.klDiv α) θ₂
          (dφ (EuclideanSpace.single c 1))) θ₁
        (dφ (EuclideanSpace.single b 1))) α
      (dφ (EuclideanSpace.single a 1))
    - ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (dφ (EuclideanSpace.single a 1)) i *
        (dφ (EuclideanSpace.single b 1)) j *
        (dφ (EuclideanSpace.single c 1)) k *
        M.cubicTensor α i j k)
    + M.toRegularStatisticalModel.fisherBilin α
        (F.secondDerivPhi t θ a b) (dφ (EuclideanSpace.single c 1))
    + M.toRegularStatisticalModel.fisherBilin α
        (F.secondDerivPhi t θ a c) (dφ (EuclideanSpace.single b 1))
    + M.toRegularStatisticalModel.fisherBilin α
        (dφ (EuclideanSpace.single a 1)) (F.secondDerivPhi t θ b c)
    = M.mConnectionCoeff θ a c b + M.mConnectionCoeff θ b c a +
      M.mConnectionCoeff θ a b c := by
  -- ═══════════════════════════════════════════════════════════════════
  -- Setup
  -- ═══════════════════════════════════════════════════════════════════
  set α := F.φ t θ with hα_def
  set dφ := fderiv ℝ (F.φ t) θ with hdφ_def
  have hα : α ∈ M.paramDomain := F.maps_domain t θ hθ
  have hφ_smooth : ContDiff ℝ ⊤ (F.φ t) :=
    F.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hSq_α := M.scoreSqIntegrable α hα
  have hSq_θ := M.scoreSqIntegrable θ hθ
  -- ═══════════════════════════════════════════════════════════════════
  -- Step 1: preserves_fisher on basis vectors as function equality
  -- ═══════════════════════════════════════════════════════════════════
  -- For θ' ∈ paramDomain:
  --   fisherBilin(φ_t(θ'))(dφ(θ')·eₐ, dφ(θ')·eᵦ) = fisherMatrix(θ')_{ab}
  have h_fisher_fn : ∀ θ' ∈ M.paramDomain,
      M.toRegularStatisticalModel.fisherBilin (F.φ t θ')
        (fderiv ℝ (F.φ t) θ' (EuclideanSpace.single a 1))
        (fderiv ℝ (F.φ t) θ' (EuclideanSpace.single b 1)) =
      M.toRegularStatisticalModel.fisherMatrix θ' a b := by
    intro θ' hθ'
    rw [F.preserves_fisher hθ' t _ _,
        M.toRegularStatisticalModel.fisherBilin_single]
  -- ═══════════════════════════════════════════════════════════════════
  -- Step 2: EventuallyEq near θ → fderivs at θ agree in direction eᶜ
  -- ═══════════════════════════════════════════════════════════════════
  have h_ev : (fun θ' =>
      M.toRegularStatisticalModel.fisherBilin (F.φ t θ')
        (fderiv ℝ (F.φ t) θ' (EuclideanSpace.single a 1))
        (fderiv ℝ (F.φ t) θ' (EuclideanSpace.single b 1))) =ᶠ[𝓝 θ]
      (fun θ' => M.toRegularStatisticalModel.fisherMatrix θ' a b) := by
    filter_upwards [M.isOpen_paramDomain.mem_nhds hθ] with θ' hθ'
    exact h_fisher_fn θ' hθ'
  have h_deriv_eq :
      fderiv ℝ (fun θ' =>
        M.toRegularStatisticalModel.fisherBilin (F.φ t θ')
          (fderiv ℝ (F.φ t) θ' (EuclideanSpace.single a 1))
          (fderiv ℝ (F.φ t) θ' (EuclideanSpace.single b 1))) θ
        (EuclideanSpace.single c 1) =
      fderiv ℝ (fun θ' =>
        M.toRegularStatisticalModel.fisherMatrix θ' a b) θ
        (EuclideanSpace.single c 1) :=
    DFunLike.congr_fun h_ev.fderiv_eq (EuclideanSpace.single c 1)
  -- ═══════════════════════════════════════════════════════════════════
  -- Step 3: Compute RHS = ∂ᶜ g_{ab}(θ)
  -- Decompose via cross_score / Bartlett identities:
  --   ∂ᶜ g_{ab}(θ) = Γᵐ_{ca,b} + Γᵐ_{cb,a} + C_{cab}
  --                  + Γᵐ_{ab,c} + ... (Christoffel identity)
  -- ═══════════════════════════════════════════════════════════════════
  -- The derivative of fisherMatrix(θ')_{ab} in direction eᶜ at θ relates
  -- to the derivative of ∫ sₐ sᵦ p dμ, which via product rule on
  -- sₐ(θ') sᵦ(θ') p(θ',ω) gives:
  --   ∂ᶜ g_{ab} = ∫(∂ᶜsₐ · sᵦ + sₐ · ∂ᶜsᵦ + sₐ sᵦ sᶜ)p dμ
  --             = Γᵐ_{ca,b} + Γᵐ_{cb,a} + C_{abc}
  -- (using the Bartlett-2 identity to convert ∂ᶜp = sᶜ·p terms)
  have h_RHS_decomp :
      fderiv ℝ (fun θ' =>
        M.toRegularStatisticalModel.fisherMatrix θ' a b) θ
        (EuclideanSpace.single c 1) =
      M.mConnectionCoeff θ c a b +
      M.mConnectionCoeff θ c b a +
      M.cubicTensor θ c a b := by
    sorry -- Leibniz + product rule on ∫ sₐ sᵦ p dμ, Bartlett-2
  -- ═══════════════════════════════════════════════════════════════════
  -- Step 4: Compute LHS via product rule
  -- The function θ' ↦ fisherBilin(φ_t(θ'))(dφ(θ')·eₐ, dφ(θ')·eᵦ)
  -- depends on θ' through three factors. Product rule gives:
  --
  -- (A) Metric variation: ∂ᶜ[fisherBilin(φ_t(·))](θ) applied to
  --     frozen vectors uₐ, uᵦ at θ
  -- (B) First vector variation: fisherBilin(α)(d²φ_{ca}, uᵦ)
  -- (C) Second vector variation: fisherBilin(α)(uₐ, d²φ_{cb})
  -- ═══════════════════════════════════════════════════════════════════
  -- Abbreviate pushed-forward basis vectors
  set uₐ := dφ (EuclideanSpace.single a 1) with huₐ_def
  set uᵦ := dφ (EuclideanSpace.single b 1) with huᵦ_def
  set u_c := dφ (EuclideanSpace.single c 1) with hu_c_def
  -- The LHS splits into A + B + C
  have h_LHS_split :
      fderiv ℝ (fun θ' =>
        M.toRegularStatisticalModel.fisherBilin (F.φ t θ')
          (fderiv ℝ (F.φ t) θ' (EuclideanSpace.single a 1))
          (fderiv ℝ (F.φ t) θ' (EuclideanSpace.single b 1))) θ
        (EuclideanSpace.single c 1) =
      -- (A) Metric variation with frozen vectors
      fderiv ℝ (fun θ' =>
        M.toRegularStatisticalModel.fisherBilin (F.φ t θ') uₐ uᵦ) θ
        (EuclideanSpace.single c 1)
      -- (B) First vector variation
      + M.toRegularStatisticalModel.fisherBilin α
          (F.secondDerivPhi t θ c a) uᵦ
      -- (C) Second vector variation
      + M.toRegularStatisticalModel.fisherBilin α uₐ
          (F.secondDerivPhi t θ c b) := by
    sorry -- Product rule for trilinear evaluation + evaluate at eᶜ
  -- ═══════════════════════════════════════════════════════════════════
  -- Step 5: Compute the metric variation term (A)
  -- fisherBilin(φ_t(θ'))(uₐ, uᵦ) = ∑ᵢⱼ (uₐ)ᵢ(uᵦ)ⱼ g(φ_t(θ'))ᵢⱼ
  -- So ∂ᶜ of this = ∑ᵢⱼ (uₐ)ᵢ(uᵦ)ⱼ · ∂ᶜ[g(φ_t(·))ᵢⱼ](θ)
  -- By chain rule: ∂ᶜ[g(φ_t(·))ᵢⱼ](θ) = ∑ₖ (u_c)ₖ · ∂ₖg(α)ᵢⱼ
  -- And ∂ₖg(α)ᵢⱼ decomposes like Step 3 but at α.
  -- ═══════════════════════════════════════════════════════════════════
  have h_metric_var :
      fderiv ℝ (fun θ' =>
        M.toRegularStatisticalModel.fisherBilin (F.φ t θ') uₐ uᵦ) θ
        (EuclideanSpace.single c 1) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        uₐ i * uᵦ j * u_c k *
        (M.mConnectionCoeff α k i j +
         M.mConnectionCoeff α k j i +
         M.cubicTensor α k i j) := by
    sorry -- Chain rule through φ_t + decomposition of ∂ₖg(α) as in Step 3
  -- ═══════════════════════════════════════════════════════════════════
  -- Step 6: Identify the tensorial third KL derivative at α
  -- The triple sum ∑ᵢⱼₖ (uₐ)ᵢ(uᵦ)ⱼ(u_c)ₖ [Γᵐ(α)_{ki,j} + Γᵐ(α)_{kj,i}]
  -- is exactly mConnectionTrilin(α)(u_c, uₐ, uᵦ) + mConnectionTrilin(α)(u_c, uᵦ, uₐ)
  --
  -- And the third KL derivative at α evaluated on (uₐ, uᵦ, u_c):
  --   = ∑ᵢⱼₖ (uₐ)ᵢ(uᵦ)ⱼ(u_c)ₖ [C(α)ᵢⱼₖ + Γᵐ terms]
  -- by klDiv_third_deriv_decomposition (generalized to arbitrary vectors)
  -- ═══════════════════════════════════════════════════════════════════
  -- The first big term in the goal is:
  --   fderiv³(klDiv α)(α)(uₐ, uᵦ, u_c) - C(α)(dφ³)
  -- By klDiv_third_deriv_decomposition at α (on pushed-forward basis),
  -- this equals the m-connection part of the third KL derivative:
  --   ∑ᵢⱼₖ (uₐ)ᵢ(uᵦ)ⱼ(u_c)ₖ [Γᵐ(α)_{ic,j} + Γᵐ(α)_{jc,i} + Γᵐ(α)_{ij,k}]
  have h_third_KL_minus_cubic :
      fderiv ℝ (fun θ₁ =>
        fderiv ℝ (fun θ₂ =>
          fderiv ℝ (M.klDiv α) θ₂ u_c) θ₁ uᵦ) α uₐ
      - ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          uₐ i * uᵦ j * u_c k * M.cubicTensor α i j k =
      M.mConnectionTrilin α uₐ u_c uᵦ +
      M.mConnectionTrilin α uᵦ u_c uₐ +
      M.mConnectionTrilin α uₐ uᵦ u_c := by
    sorry -- klDiv_third_deriv_decomposition at α, expanded on pushed-forward vectors
  -- ═══════════════════════════════════════════════════════════════════
  -- Step 7: Assemble
  -- From h_deriv_eq:  LHS = RHS
  -- From h_LHS_split: LHS = (A) + correction_B + correction_C
  -- From h_metric_var: (A) = ∑ [Γᵐ(α) + Γᵐ(α) + C(α)] · dφ³
  --
  -- The goal's LHS is:
  --   (third_KL - C(α)·dφ³) + correction_{ab} + correction_{ac} + correction_{bc}
  --
  -- Expanding (A) = [C(α)·dφ³] + [Γᵐ(α) terms]:
  --   (A) + corr_B + corr_C = C(α)·dφ³ + [Γᵐ(α) terms] + corr_B + corr_C
  --
  -- And from third_KL_minus_cubic:
  --   third_KL - C(α)·dφ³ = [Γᵐ(α) terms']
  --
  -- The goal becomes: show that [Γᵐ(α) terms'] + corrections_{ab,ac,bc}
  --   equals the RHS.
  --
  -- Meanwhile h_deriv_eq + h_LHS_split + h_metric_var + h_RHS_decomp
  -- relate these to Γᵐ(θ) + C(θ).
  -- ═══════════════════════════════════════════════════════════════════
  -- Rewrite the metric variation using cubic + m-connection split
  have h_A_split :
      fderiv ℝ (fun θ' =>
        M.toRegularStatisticalModel.fisherBilin (F.φ t θ') uₐ uᵦ) θ
        (EuclideanSpace.single c 1) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        uₐ i * uᵦ j * u_c k * M.cubicTensor α k i j
      + M.mConnectionTrilin α u_c uₐ uᵦ
      + M.mConnectionTrilin α u_c uᵦ uₐ := by
    rw [h_metric_var]
    -- Separate the cubic and m-connection parts of the sum
    simp only [mul_add, Finset.sum_add_distrib]
    -- The m-connection sums are mConnectionTrilin by definition
    unfold mConnectionTrilin
    ring_nf
    sorry
  -- ═══════════════════════════════════════════════════════════════════
  -- Now combine everything:
  -- From h_deriv_eq: LHS_full = RHS
  -- h_LHS_split: LHS_full = (A) + corr_B + corr_C
  -- h_A_split:   (A) = C(α)·dφ³(kij) + Γᵐ_tri(α)(u_c,uₐ,uᵦ) + Γᵐ_tri(α)(u_c,uᵦ,uₐ)
  -- h_RHS_decomp: RHS = Γᵐ(θ)_{ca,b} + Γᵐ(θ)_{cb,a} + C(θ)_{cab}
  --
  -- So: C(α)·dφ³(kij) + Γᵐ_tri(α)(u_c,uₐ,uᵦ) + Γᵐ_tri(α)(u_c,uᵦ,uₐ)
  --     + fisherBilin(α)(d²φ_{ca}, uᵦ) + fisherBilin(α)(uₐ, d²φ_{cb})
  --     = Γᵐ(θ)_{ca,b} + Γᵐ(θ)_{cb,a} + C(θ)_{cab}
  --
  -- This is an identity linking:
  -- [Γᵐ(α) pulled through dφ] + [d²φ corrections]
  --   to [Γᵐ(θ)] + [C(θ) - C(α)·dφ³]
  --
  -- But we can't separate C(θ) from C(α)·dφ³ yet (that's what
  -- preserves_cubic proves!). Instead, use h_deriv_eq to eliminate one side.
  -- ═══════════════════════════════════════════════════════════════════
  -- The GOAL is an equation about (third_KL - C(α)·dφ³) + corrections = 3Γᵐ(θ)
  -- We prove this by:
  -- (i)  h_deriv_eq gives: (A) + corr_B + corr_C = RHS_deriv
  -- (ii) h_third_KL_minus_cubic: third_KL - C(α)·dφ³ = Γᵐ_tri' terms
  -- (iii) h_A_split: (A) = C(α)·dφ³(kij) + Γᵐ_tri(α)(c,a,b) + Γᵐ_tri(α)(c,b,a)
  -- (iv)  h_RHS_decomp: RHS_deriv = Γᵐ(θ)_{ca,b} + Γᵐ(θ)_{cb,a} + C(θ)_{cab}
  --
  -- From (i)+(iii)+(iv):
  --   C(α)·dφ³(kij) + Γᵐ_tri(α)(c,a,b) + Γᵐ_tri(α)(c,b,a) + corr_B + corr_C
  --   = Γᵐ(θ)_{ca,b} + Γᵐ(θ)_{cb,a} + C(θ)_{cab}
  --
  -- From (ii): third_KL - C(α)·dφ³ = Γᵐ_tri(α)(a,c,b) + Γᵐ_tri(α)(b,c,a) + Γᵐ_tri(α)(a,b,c)
  --
  -- Goal: (third_KL - C(α)·dφ³) + corr_{ab} + corr_{ac} + corr_{bc}
  --       = Γᵐ(θ)_{ac,b} + Γᵐ(θ)_{bc,a} + Γᵐ(θ)_{ab,c}
  -- i.e.: Γᵐ_tri(α)(a,c,b) + Γᵐ_tri(α)(b,c,a) + Γᵐ_tri(α)(a,b,c)
  --       + corr_{ab} + corr_{ac} + corr_{bc}
  --       = Γᵐ(θ)_{ac,b} + Γᵐ(θ)_{bc,a} + Γᵐ(θ)_{ab,c}
  --
  -- This follows from the identity (i)+(iii)+(iv) applied with THREE
  -- different permutations of (a,b,c) and combined. Specifically:
  -- Apply h_deriv_eq with (a,b,c), (a,c,b), and (b,c,a), solve the
  -- resulting 3×3 system for the three terms in the goal.
  --
  -- Actually, more directly: instantiate h_deriv_eq for three choices
  -- of the pair (a',b') being differentiated, with direction c':
  -- (a',b',c') = (a,c,c) gets Γᵐ_tri(α)(c,a,c) + ... = Γᵐ(θ)_{ca,c} + ...
  -- This is getting complicated. Let's leave this algebraic assembly as sorry.
  sorry


end DivergencePreservingFamily
end TwiceDifferentiableModel
end InformationGeometry
