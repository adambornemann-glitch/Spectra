/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: InformationGeometry/DivergenceDynamics.lean
-/
import LogosLibrary.InformationGeometry.Dynamics.BartlettIdentities
import LogosLibrary.InformationGeometry.Dynamics.FaaDiBruno
import LogosLibrary.InformationGeometry.Dynamics.MConnect

namespace InformationGeometry

open MeasureTheory Finset Filter Topology TopologicalSpace

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

namespace TwiceDifferentiableModel
variable (M : TwiceDifferentiableModel n Ω)

variable (F : M.DivergencePreservingFamily)

set_option maxHeartbeats 400000 in
/-- Divergence preservation implies cubic tensor preservation.

Differentiating `preserves_divergence` three times and using
`cubicTensor_eq_klDiv_third_deriv`: φ_t preserves C.

This is the key result showing that divergence preservation captures
the *full* information-geometric structure, not just the metric. -/
lemma preserves_cubic
    (M₃ : ThriceDifferentiableModel n Ω)
    (hM₃ : M₃.toTwiceDifferentiableModel = M)
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (t : ℝ) (u v w : ParamSpace n) :
    M.cubicTrilin (F.φ t θ)
      (fderiv ℝ (F.φ t) θ u) (fderiv ℝ (F.φ t) θ v) (fderiv ℝ (F.φ t) θ w) =
    M.cubicTrilin θ u v w := by
  subst hM₃
  set M := M₃.toTwiceDifferentiableModel with hM_def
  set α := F.φ t θ with hα_def
  have hα : α ∈ M.paramDomain := F.maps_domain t θ hθ
  -- ═══ Step 1: Prove componentwise identity on basis triples ═══
  have h_comp : ∀ a b c : Fin n,
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)).ofLp i *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)).ofLp j *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)).ofLp k *
        M.cubicTensor α i j k =
      M.cubicTensor θ a b c := by
    intro a b c
    -- ═══ Step 1a: Third KL derivatives agree ═══
    have h_third_eq := F.third_deriv_transfer hθ t a b c
    -- ═══ Step 1b: RHS decomposition ═══
    have h_A_θ : ∀ j' k' : Fin n,
        ∃ g₂ : ParamSpace n →L[ℝ] ℝ,
          HasFDerivAt
            (fun θ' => -∫ ω, M.density θ ω *
              M.scorePartial θ' j' k' ω ∂M.refMeasure) g₂ θ ∧
          ∀ i' : Fin n,
            g₂ (EuclideanSpace.single i' 1) =
              -∫ ω, M.density θ ω *
                fderiv ℝ (fun θ'' => M.scorePartial θ'' j' k' ω) θ
                  (EuclideanSpace.single i' 1) ∂M.refMeasure := by
      intro j' k'
      exact M.klDiv_third_partial
        hθ j' k'
        (M₃.scorePartial_fderiv_bound θ hθ θ hθ j' k')
        (M₃.scorePartial_density_integrable θ hθ j' k')
        (M₃.scorePartial_deriv_aestronglyMeasurable θ hθ j' k')
        (M₃.scorePartial_density_aestronglyMeasurable θ hθ j' k')
    have h_B_θ : ∀ i' j' k' : Fin n,
        ∫ ω,
          (fderiv ℝ (fun θ'' => M.scorePartial θ'' j' k' ω) θ
              (EuclideanSpace.single i' 1) +
           M.toRegularStatisticalModel.score θ j' ω *
             M.scorePartial θ i' k' ω +
           M.toRegularStatisticalModel.score θ i' ω *
             M.scorePartial θ j' k' ω +
           M.toRegularStatisticalModel.score θ k' ω *
             M.scorePartial θ i' j' ω +
           M.toRegularStatisticalModel.score θ i' ω *
             M.toRegularStatisticalModel.score θ j' ω *
             M.toRegularStatisticalModel.score θ k' ω) *
          M.density θ ω ∂M.refMeasure = 0 := by
      intro i' j' k'
      exact M.bartlett_third hθ i' j' k'
        (by -- five-term integrability
          have h1 := M₃.scorePartial_deriv_integrable θ hθ i' j' k'
          have h2 := M₃.score_scorePartial_integrable θ hθ j' i' k'
          have h3 := M₃.score_scorePartial_integrable θ hθ i' j' k'
          have h4 := M₃.score_scorePartial_integrable θ hθ k' i' j'
          have h5 := M₃.tripleScore_integrable θ hθ i' j' k'
          exact ((((h1.add h2).add h3).add h4).add h5).congr
            (by filter_upwards with ω; ring_nf; simp only [Pi.add_apply]; grind only))
        (fun θ' hθ' => M.bartlett_second hθ' j' k'
          (M₃.bartlett2_integrable θ' hθ' j' k'))
        (M₃.bartlett2_hasFDerivAt θ hθ i' j' k')
    have h_ev2_θ : ∀ᶠ θ' in 𝓝 θ,
        fderiv ℝ (fun θ₂ =>
          fderiv ℝ (M.klDiv θ) θ₂ (EuclideanSpace.single c 1))
            θ' (EuclideanSpace.single b 1) =
          -∫ ω, M.density θ ω *
            M.scorePartial θ' b c ω ∂M.refMeasure := by
      have h_inner : ∀ᶠ θ₂ in 𝓝 θ,
          fderiv ℝ (M.klDiv θ) θ₂ (EuclideanSpace.single c 1) =
          -∫ ω, M.density θ ω *
            M.toRegularStatisticalModel.score θ₂ c ω ∂M.refMeasure := by
        filter_upwards [M.isOpen_paramDomain.mem_nhds hθ] with θ₂ hθ₂
        exact klDiv_partial_j M hθ hθ₂ c
      filter_upwards [M.isOpen_paramDomain.mem_nhds hθ] with θ' hθ'
      have h_clm := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (by
        filter_upwards [M.isOpen_paramDomain.mem_nhds hθ'] with θ₂ hθ₂
        exact klDiv_partial_j M hθ hθ₂ c)
      have := DFunLike.congr_fun h_clm (EuclideanSpace.single b 1)
      rw [this]
      sorry -- Leibniz identification of fderiv(-∫ p score) with -∫ p scorePartial
    -- ═══ Step 1c: Construct HasFDerivAt for the RHS function ═══
    obtain ⟨g₂, hg₂_fderiv, hg₂_eval⟩ := h_A_θ b c
    have h_rhs_hasFDerivAt : HasFDerivAt (fun θ' =>
        fderiv ℝ (fun θ₂ =>
          fderiv ℝ (M.klDiv θ) θ₂ (EuclideanSpace.single c 1))
            θ' (EuclideanSpace.single b 1))
        g₂ θ :=
      hg₂_fderiv.congr_of_eventuallyEq h_ev2_θ
    -- ═══ Step 1d: Apply klDiv_third_deriv_decomposition ═══
    have h_rhs_val := M.klDiv_third_deriv_decomposition hθ a b c
        h_A_θ h_B_θ h_ev2_θ
        (M₃.scorePartial_deriv_integrable θ hθ a b c)
        (M₃.score_scorePartial_integrable θ hθ b a c)
        (M₃.score_scorePartial_integrable θ hθ a b c)
        (M₃.score_scorePartial_integrable θ hθ c a b)
        (M₃.tripleScore_integrable θ hθ a b c)
        g₂ h_rhs_hasFDerivAt
    -- ═══ Step 1e: LHS via Faà di Bruno ═══
    have h_fdb := F.kl_faa_di_bruno hθ t a b c
    -- ═══ Step 1f: Connection correction ═══
    have h_conn := F.mConnection_correction hθ t a b c
    -- ═══ Step 1g: Assembly — the four-equation chain ═══
    set T := fderiv ℝ (fun θ₁ =>
        fderiv ℝ (fun θ₂ =>
          fderiv ℝ (M.klDiv α) θ₂
            (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))) θ₁
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))) α
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
    set C₁ := M.toRegularStatisticalModel.fisherBilin α
        (F.secondDerivPhi t θ a b)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
    set C₂ := M.toRegularStatisticalModel.fisherBilin α
        (F.secondDerivPhi t θ a c)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
    set C₃ := M.toRegularStatisticalModel.fisherBilin α
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
        (F.secondDerivPhi t θ b c)
    set S := ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)).ofLp i *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)).ofLp j *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)).ofLp k *
        M.cubicTensor α i j k
    set Γ₁ := M.mConnectionCoeff θ a c b
    set Γ₂ := M.mConnectionCoeff θ b c a
    set Γ₃ := M.mConnectionCoeff θ a b c
    have eq_conn : (T - S) + C₁ + C₂ + C₃ = Γ₁ + Γ₂ + Γ₃ := h_conn
    have eq_fdb_rearranged : T + C₁ + C₂ + C₃ = S + Γ₁ + Γ₂ + Γ₃ := by linarith
    have eq_LHS : T + C₁ + C₂ + C₃ =
        fderiv ℝ (fun θ₁ =>
          fderiv ℝ (fun θ₂ =>
            fderiv ℝ (fun θ₃ => M.klDiv (F.φ t θ) (F.φ t θ₃)) θ₂
              (EuclideanSpace.single c 1)) θ₁
            (EuclideanSpace.single b 1)) θ
          (EuclideanSpace.single a 1) := h_fdb.symm
    have eq_transfer :
        fderiv ℝ (fun θ₁ =>
          fderiv ℝ (fun θ₂ =>
            fderiv ℝ (fun θ₃ => M.klDiv (F.φ t θ) (F.φ t θ₃)) θ₂
              (EuclideanSpace.single c 1)) θ₁
            (EuclideanSpace.single b 1)) θ
          (EuclideanSpace.single a 1) =
        fderiv ℝ (fun θ₁ =>
          fderiv ℝ (fun θ₂ =>
            fderiv ℝ (M.klDiv θ) θ₂
              (EuclideanSpace.single c 1)) θ₁
            (EuclideanSpace.single b 1)) θ
          (EuclideanSpace.single a 1) := h_third_eq
    have h_bridge :
        fderiv ℝ (fun θ₁ =>
          fderiv ℝ (fun θ₂ =>
            fderiv ℝ (M.klDiv θ) θ₂ (EuclideanSpace.single c 1))
              θ₁ (EuclideanSpace.single b 1)) θ
          (EuclideanSpace.single a 1) =
        g₂ (EuclideanSpace.single a 1) := by
      rw [h_rhs_hasFDerivAt.fderiv]
    linarith [eq_fdb_rearranged, eq_LHS, eq_transfer, h_rhs_val, h_bridge]
  -- ═══ Step 2: Trilinearity reduction ═══
  -- Helper: 6-fold sum reordering (bubble sort, 9 adjacent transpositions)
  have sum6_comm : ∀ (f : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℝ),
      ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c, f i j k a b c =
      ∑ a, ∑ b, ∑ c, ∑ i, ∑ j, ∑ k, f i j k a b c := by
    intro f
    -- Move a past k, j, i
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    -- Move b past k, j, i (now at positions 2,3,4 under a)
    conv_lhs => arg 2; ext a; arg 2; ext i; arg 2; ext j; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext a; arg 2; ext i; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    -- Move c past k, j, i (now at positions 3,4,5 under a,b)
    conv_lhs => arg 2; ext a; arg 2; ext b; arg 2; ext i; arg 2; ext j; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext a; arg 2; ext b; arg 2; ext i; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext a; arg 2; ext b; rw [Finset.sum_comm]
  -- Generic linearity of CL map evaluation in EuclideanSpace
  have hlin : ∀ (L : ParamSpace n →L[ℝ] ParamSpace n) (x : ParamSpace n) (i : Fin n),
      (L x).ofLp i = ∑ a : Fin n, x.ofLp a *
        (L (EuclideanSpace.single a 1)).ofLp i := by
    intro L x i
    have hbasis : x = ∑ a : Fin n, x.ofLp a • EuclideanSpace.single a 1 := by
      ext p; simp only [WithLp.ofLp_sum, WithLp.ofLp_smul,
        EuclideanSpace.ofLp_single, sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_apply, mul_ite, mul_one, mul_zero, sum_ite_eq,
        mem_univ, ↓reduceIte]
    conv_lhs => rw [hbasis, map_sum]
    simp only [map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul,
      Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  -- Main proof
  unfold cubicTrilin
  -- Replace C(θ, a, b, c) with h_comp on RHS
  conv_rhs => arg 2; ext a; arg 2; ext b; arg 2; ext c; rw [← h_comp a b c]
  -- Distribute on RHS: uₐ vᵦ wc * (∑ i j k ...) → ∑ i j k, uₐ vᵦ wc * ...
  simp only [Finset.mul_sum]
  -- Expand dφ(u), dφ(v), dφ(w) on LHS
  simp_rw [hlin _ u, hlin _ v, hlin _ w]
  -- Distribute products of sums on LHS
  simp only [Finset.sum_mul, Finset.mul_sum]
  -- Both sides are now 6-fold sums with ring-equal summands in different order.
  -- Reorder LHS: (i,j,k,a,b,c) → (a,b,c,i,j,k)
  rw [sum6_comm]
  -- Now both sides have the same summation order. Close pointwise.
  congr 1; ext a; congr 1; ext b; congr 1; ext c
  congr 1; ext i; congr 1; ext j; congr 1; ext k
  field_simp; ring_nf
  /-⊢ u.ofLp c * ((fderiv ℝ (F✝.φ t) θ) (EuclideanSpace.single c 1)).ofLp i * v.ofLp b *
          ((fderiv ℝ (F✝.φ t) θ) (EuclideanSpace.single b 1)).ofLp j *
        w.ofLp a *
      ((fderiv ℝ (F✝.φ t) θ) (EuclideanSpace.single a 1)).ofLp k *
    M₃.cubicTensor (F✝.φ t θ) i j k =
  v.ofLp b * u.ofLp a * w.ofLp c * ((fderiv ℝ (F.φ t) θ) (EuclideanSpace.single a 1)).ofLp i *
        ((fderiv ℝ (F.φ t) θ) (EuclideanSpace.single b 1)).ofLp j *
      ((fderiv ℝ (F.φ t) θ) (EuclideanSpace.single c 1)).ofLp k *
    M.cubicTensor α i j k-/
  sorry


end TwiceDifferentiableModel

end InformationGeometry
