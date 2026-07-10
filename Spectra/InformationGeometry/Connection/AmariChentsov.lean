/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Divergence

/-!
# The Amari–Chentsov Cubic Tensor

The totally symmetric `(0,3)`-tensor `C_{ijk}(θ) = E_θ[sᵢ sⱼ sₖ]`, the third cumulant of the
score vector. Together with the Fisher metric it determines the family of α-connections
(`Basic.lean`). This file defines the tensor, its trilinear form, and the intrinsic
m-connection coefficient, and decomposes the third derivative of the KL divergence at the
diagonal into the cubic tensor plus m-connection terms.

## Main definitions

* `cubicTensor` — the Amari–Chentsov tensor `C_{ijk}(θ) = E_θ[sᵢ sⱼ sₖ]`.
* `cubicTrilin` — `C` as a trilinear form on tangent vectors.
* `mConnectionCoeff` — the intrinsic mixture-connection coefficient `Γ^(m)_{ab,c}`.

## Main statements

* `cubicTensor_symm₁₂`, `cubicTensor_symm₂₃`, `cubicTensor_symm₁₃` — total symmetry of `C`.
* `klDiv_third_deriv_decomposition` — `∂³D = C_{ijk} + Γ^(m)_{ik,j} + Γ^(m)_{jk,i} + Γ^(m)_{ij,k}`.

## References

* S. Amari, H. Nagaoka, *Methods of Information Geometry*, AMS, 2000.
-/
open MeasureTheory Finset Filter Topology TopologicalSpace
namespace Spectra.InformationGeometry
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

namespace TwiceDifferentiableModel

variable (M : TwiceDifferentiableModel n Ω)


-- ============================================================================
-- §2. The Amari–Chentsov Cubic Tensor
-- ============================================================================

/-! ### The cubic tensor C_{ijk}

The third derivative of the KL divergence at the diagonal, or equivalently,
E[sᵢ sⱼ sₖ] where sᵢ is the i-th score function. This is the totally
symmetric (0,3)-tensor that, together with the Fisher metric, determines
the full family of α-connections.

In the quantum setting, when the inner product ⟨Õᵢψ, Õⱼψ⟩ is complex,
the cubic tensor acquires an imaginary part that encodes the symplectic
form ω. Classically, C is purely real. -/

/-- The Amari–Chentsov cubic tensor: C_{ijk}(θ) = E_θ[sᵢ sⱼ sₖ].

This is the third cumulant of the score vector.  Its total symmetry
follows from the symmetry of the product sᵢsⱼsₖ. -/
noncomputable def cubicTensor
    (θ : ParamSpace n) (i j k : Fin n) : ℝ :=
  ∫ ω, M.toRegularStatisticalModel.score θ i ω *
       M.toRegularStatisticalModel.score θ j ω *
       M.toRegularStatisticalModel.score θ k ω *
       M.density θ ω ∂M.refMeasure

/-- The cubic tensor is totally symmetric. -/
lemma cubicTensor_symm₁₂ {θ : ParamSpace n} (_hθ : θ ∈ M.paramDomain)
    (i j k : Fin n) :
    M.cubicTensor θ i j k = M.cubicTensor θ j i k := by
  unfold cubicTensor; congr 1; ext ω; ring

/-- Symmetry of the cubic tensor under swapping the last two indices:
`C_{ijk} = C_{ikj}`. -/
lemma cubicTensor_symm₂₃ {θ : ParamSpace n} (_hθ : θ ∈ M.paramDomain)
    (i j k : Fin n) :
    M.cubicTensor θ i j k = M.cubicTensor θ i k j := by
  unfold cubicTensor; congr 1; ext ω; ring

/-- Symmetry of the cubic tensor under swapping the outer indices:
`C_{ijk} = C_{kji}`. -/
lemma cubicTensor_symm₁₃ {θ : ParamSpace n} (_hθ : θ ∈ M.paramDomain)
    (i j k : Fin n) :
    M.cubicTensor θ i j k = M.cubicTensor θ k j i := by
  unfold cubicTensor; congr 1; ext ω; ring


/-- The cubic tensor as a trilinear form on tangent vectors. -/
noncomputable def cubicTrilin
    (θ : ParamSpace n) (u v w : ParamSpace n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
    u i * v j * w k * M.cubicTensor θ i j k


-- ════════════════════════════════════════════════════════════════════
-- §2a. the m-connection (intrinsic definitions)
-- ════════════════════════════════════════════════════════════════════


/-- The **m-connection coefficient** Γ^(m)_{ab,c}(θ) = E_θ[sᶜ · ∂ₐsᵦ].

Defined intrinsically as the expected product of the c-th score with
the (a,b)-th score derivative, weighted by the density.

This is the connection coefficient of the **mixture connection**
(α = −1), but we define it without reference to the α-connection
machinery. The identification `mConnectionCoeff = alphaConnectionCoeff (-1)`
is proved separately in §3. -/
noncomputable def mConnectionCoeff
    (θ : ParamSpace n) (a b c : Fin n) : ℝ :=
  ∫ ω, M.toRegularStatisticalModel.score θ c ω *
       M.scorePartial θ a b ω *
       M.density θ ω ∂M.refMeasure


-- ════════════════════════════════════════════════════════════════════
-- §2b. The three lemmas replacing cubicTensor_eq_neg_klDiv_third_deriv
-- ════════════════════════════════════════════════════════════════════

/-! ### Lemma A: Third KL derivative via Leibniz

One Leibniz interchange beyond `cross_score_hasFDerivAt`. The function

  θ' ↦ −∫ p(θ,ω) · (∂ⱼsₖ)(θ', ω) dμ

is Fréchet differentiable at θ, and its i-th component equals

  −∫ p(θ,ω) · (∂ᵢ∂ⱼsₖ)(θ, ω) dμ

Proof: identical template to `cross_score_hasFDerivAt`, using
`hasFDerivAt_integral_of_dominated_of_fderiv_le` with the
domination hypothesis `h_dom`. -/
/-- **Lemma A (Leibniz).** The map `θ' ↦ −∫ p(θ,ω)·(∂ⱼsₖ)(θ',ω) dμ` is Fréchet
differentiable at `θ`, and the `i`-th component of its derivative is
`−∫ p(θ,ω)·(∂ᵢ∂ⱼsₖ)(θ,ω) dμ`, under the stated domination, integrability, and
measurability hypotheses. -/
lemma klDiv_third_partial
    {θ : ParamSpace n} (_hθ : θ ∈ M.paramDomain) (j k : Fin n)
    (h_dom : ∃ ε > 0, ∃ bound : Ω → ℝ, Integrable bound M.refMeasure ∧
      (∀ᵐ ω ∂M.refMeasure, ∀ θ' ∈ Metric.ball θ ε,
        HasFDerivAt
          (fun θ'' => M.density θ ω * M.scorePartial θ'' j k ω)
          (M.density θ ω •
            fderiv ℝ (fun θ'' => M.scorePartial θ'' j k ω) θ') θ' ∧
        ‖M.density θ ω •
          fderiv ℝ (fun θ'' => M.scorePartial θ'' j k ω) θ'‖ ≤
          bound ω))
    (h_int : Integrable
      (fun ω => M.density θ ω * M.scorePartial θ j k ω) M.refMeasure)
    (h_meas : AEStronglyMeasurable
      (fun ω => M.density θ ω •
        fderiv ℝ (fun θ'' => M.scorePartial θ'' j k ω) θ) M.refMeasure)
    (h_meas_near : ∀ᶠ θ' in 𝓝 θ, AEStronglyMeasurable
      (fun ω => M.density θ ω * M.scorePartial θ' j k ω) M.refMeasure) :
    ∃ g₂ : ParamSpace n →L[ℝ] ℝ,
      HasFDerivAt
        (fun θ' => -∫ ω, M.density θ ω *
          M.scorePartial θ' j k ω ∂M.refMeasure) g₂ θ ∧
      ∀ i : Fin n,
        g₂ (EuclideanSpace.single i 1) =
          -∫ ω, M.density θ ω *
            fderiv ℝ (fun θ'' => M.scorePartial θ'' j k ω) θ
              (EuclideanSpace.single i 1) ∂M.refMeasure := by
  obtain ⟨ε, hε, bound, hbound_int, h_ae⟩ := h_dom
  have hLeibniz : HasFDerivAt
      (fun θ' => ∫ ω, M.density θ ω *
        M.scorePartial θ' j k ω ∂M.refMeasure)
      (∫ ω, M.density θ ω •
        fderiv ℝ (fun θ'' => M.scorePartial θ'' j k ω) θ ∂M.refMeasure)
      θ := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (s := Metric.ball θ ε)
      (F' := fun θ' ω => M.density θ ω •
        fderiv ℝ (fun θ'' => M.scorePartial θ'' j k ω) θ')
      (bound := bound)
      (Metric.ball_mem_nhds θ hε)
    · -- (1) AEStronglyMeasurable F(θ', ·) near θ
      exact h_meas_near
    · -- (2) Integrable F(θ, ·) at the basepoint
      exact h_int
    · -- (3) AEStronglyMeasurable F'(θ, ·)
      exact h_meas
    · -- (4) Derivative norm bound: ‖F'(θ', ω)‖ ≤ bound(ω)
      filter_upwards [h_ae] with ω hω θ' hθ'
      exact (hω θ' hθ').2
    · -- (5) Bound integrable
      exact hbound_int
    · -- (6) Pointwise HasFDerivAt in the ball
      filter_upwards [h_ae] with ω hω θ' hθ'
      exact (hω θ' hθ').1
  set L := ∫ ω, M.density θ ω •
    fderiv ℝ (fun θ'' => M.scorePartial θ'' j k ω) θ ∂M.refMeasure
  have hL_int : Integrable
      (fun ω => M.density θ ω •
        fderiv ℝ (fun θ'' => M.scorePartial θ'' j k ω) θ)
      M.refMeasure := by
    apply Integrable.mono hbound_int.norm h_meas
    filter_upwards [h_ae] with ω hω
    calc ‖M.density θ ω •
            fderiv ℝ (fun θ'' => M.scorePartial θ'' j k ω) θ‖
        ≤ bound ω := (hω θ (Metric.mem_ball_self hε)).2
      _ ≤ ‖bound ω‖ := Real.le_norm_self _
    exact Real.le_norm_self ‖bound ω‖
  refine ⟨-L, hLeibniz.neg, fun i => ?_⟩
  -- Goal: (-L)(eᵢ) = −∫ p(θ) · fderiv(scorePartial(·,j,k))(θ)(eᵢ) dμ
  simp only [ContinuousLinearMap.neg_apply, neg_inj]
  -- Goal: L(eᵢ) = ∫ p(θ) · fderiv(scorePartial(·,j,k))(θ)(eᵢ) dμ
  rw [ContinuousLinearMap.integral_apply hL_int]
  -- Goal: ∫ (p(θ) • fderiv(...))(eᵢ) dμ = ∫ p(θ) * fderiv(...)(eᵢ) dμ
  congr 1


/-! ### Lemma C: Third KL derivative decomposition

Combining Lemma A with the Bartlett identity (Lemma B) gives the
correct decomposition of the third KL derivative at the diagonal:

  ∂³D(θ‖θ')/∂θ'ⁱ∂θ'ʲ∂θ'ᵏ|_{θ'=θ}
    = C_{ijk}(θ) + Γ^(m)_{ik,j}(θ) + Γ^(m)_{jk,i}(θ) + Γ^(m)_{ij,k}(θ)

For exponential families, Γ^(m) = 0 and this reduces to ∂³D = C.
In general, the m-connection terms do not vanish. -/
/-- **Lemma C (third-derivative decomposition).** At the diagonal,
`∂³D(θ‖θ')/∂θ'ⁱ∂θ'ʲ∂θ'ᵏ|_{θ'=θ} = C_{ijk} + Γ^(m)_{ik,j} + Γ^(m)_{jk,i} + Γ^(m)_{ij,k}`,
obtained by combining Lemma A with the order-3 Bartlett identity (`h_B`). For
exponential families the m-connection terms vanish and this reduces to `∂³D = C`. -/
lemma klDiv_third_deriv_decomposition
    {θ : ParamSpace n} (_hθ : θ ∈ M.paramDomain) (i j k : Fin n)
    (h_A : ∀ j' k' : Fin n,
      ∃ g₂ : ParamSpace n →L[ℝ] ℝ,
        HasFDerivAt
          (fun θ' => -∫ ω, M.density θ ω *
            M.scorePartial θ' j' k' ω ∂M.refMeasure) g₂ θ ∧
        ∀ i' : Fin n,
          g₂ (EuclideanSpace.single i' 1) =
            -∫ ω, M.density θ ω *
              fderiv ℝ (fun θ'' => M.scorePartial θ'' j' k' ω) θ
                (EuclideanSpace.single i' 1) ∂M.refMeasure)
    (h_B : ∀ i' j' k' : Fin n,
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
        M.density θ ω ∂M.refMeasure = 0)
    (h_ev2 : ∀ᶠ θ' in 𝓝 θ,
      fderiv ℝ (fun θ₂ =>
        fderiv ℝ (M.klDiv θ) θ₂ (EuclideanSpace.single k 1))
          θ' (EuclideanSpace.single j 1) =
        -∫ ω, M.density θ ω *
          M.scorePartial θ' j k ω ∂M.refMeasure)
    /- Integrability: the ∂ᵢ(∂ⱼsₖ) term can be separated from the Bartlett sum. -/
    (h_int_deriv : Integrable (fun ω =>
      fderiv ℝ (fun θ'' => M.scorePartial θ'' j k ω) θ
        (EuclideanSpace.single i 1) * M.density θ ω) M.refMeasure)
    /- Integrability of each constituent, for splitting ∫(B+C+D+E). -/
    (h_int_m₁ : Integrable (fun ω =>
      M.toRegularStatisticalModel.score θ j ω *
      M.scorePartial θ i k ω * M.density θ ω) M.refMeasure)
    (h_int_m₂ : Integrable (fun ω =>
      M.toRegularStatisticalModel.score θ i ω *
      M.scorePartial θ j k ω * M.density θ ω) M.refMeasure)
    (h_int_m₃ : Integrable (fun ω =>
      M.toRegularStatisticalModel.score θ k ω *
      M.scorePartial θ i j ω * M.density θ ω) M.refMeasure)
    (h_int_cubic : Integrable (fun ω =>
      M.toRegularStatisticalModel.score θ i ω *
      M.toRegularStatisticalModel.score θ j ω *
      M.toRegularStatisticalModel.score θ k ω *
      M.density θ ω) M.refMeasure) :
    ∀ f₃ : ParamSpace n →L[ℝ] ℝ,
      HasFDerivAt (fun θ' =>
        fderiv ℝ (fun θ₂ =>
          fderiv ℝ (M.klDiv θ) θ₂ (EuclideanSpace.single k 1))
            θ' (EuclideanSpace.single j 1))
        f₃ θ →
      f₃ (EuclideanSpace.single i 1) =
        M.cubicTensor θ i j k +
        M.mConnectionCoeff θ i k j +
        M.mConnectionCoeff θ j k i +
        M.mConnectionCoeff θ i j k := by
  intro f₃ hf₃
  -- Step 1: Get g₂ from Lemma A at indices j, k
  obtain ⟨g₂, hg₂_fderiv, hg₂_eval⟩ := h_A j k
  -- Step 2: Transfer — the KL expression agrees with the
  --   scorePartial integral near θ (h_ev2), so their derivatives
  --   at θ coincide.  By uniqueness: f₃ = g₂.
  have hg₂' : HasFDerivAt (fun θ' =>
      fderiv ℝ (fun θ₂ =>
        fderiv ℝ (M.klDiv θ) θ₂ (EuclideanSpace.single k 1))
          θ' (EuclideanSpace.single j 1))
      g₂ θ :=
    hg₂_fderiv.congr_of_eventuallyEq h_ev2
  rw [hf₃.unique hg₂']
  -- Step 3: Evaluate g₂(eᵢ) via Lemma A's component formula
  rw [hg₂_eval i]
  -- Step 4: Abbreviate the five Bartlett-3 terms
  set A : Ω → ℝ := fun ω =>
    fderiv ℝ (fun θ'' => M.scorePartial θ'' j k ω) θ
      (EuclideanSpace.single i 1) * M.density θ ω
  set B : Ω → ℝ := fun ω =>
    M.toRegularStatisticalModel.score θ j ω *
    M.scorePartial θ i k ω * M.density θ ω
  set C : Ω → ℝ := fun ω =>
    M.toRegularStatisticalModel.score θ i ω *
    M.scorePartial θ j k ω * M.density θ ω
  set D : Ω → ℝ := fun ω =>
    M.toRegularStatisticalModel.score θ k ω *
    M.scorePartial θ i j ω * M.density θ ω
  set E : Ω → ℝ := fun ω =>
    M.toRegularStatisticalModel.score θ i ω *
    M.toRegularStatisticalModel.score θ j ω *
    M.toRegularStatisticalModel.score θ k ω *
    M.density θ ω
  -- Step 5: Bartlett-3 says ∫ (A + B + C + D + E) = 0
  have h_five : ∫ ω, (A ω + B ω + C ω + D ω + E ω) ∂M.refMeasure = 0 := by
    have := h_B i j k
    refine (this.symm ▸ ?_)
    congr 1; ext ω; simp only [A, B, C, D, E]; ring
  -- Step 6: Split ∫(A + BCDE) and rearrange: -∫A = ∫(B+C+D+E)
  have _hB_int : Integrable B M.refMeasure := h_int_m₁
  have _hC_int : Integrable C M.refMeasure := h_int_m₂
  have _hD_int : Integrable D M.refMeasure := h_int_m₃
  have _hE_int : Integrable E M.refMeasure := h_int_cubic
  have h_int_BCDE : Integrable (fun ω => B ω + C ω + D ω + E ω) M.refMeasure :=
    ((h_int_m₁.add h_int_m₂).add h_int_m₃).add h_int_cubic
  have h_split : ∫ ω, A ω ∂M.refMeasure +
      ∫ ω, (B ω + C ω + D ω + E ω) ∂M.refMeasure = 0 := by
    rw [← integral_add h_int_deriv h_int_BCDE]
    have : (fun ω => A ω + (B ω + C ω + D ω + E ω)) =
        fun ω => A ω + B ω + C ω + D ω + E ω := by ext ω; ring
    rw [this]; exact h_five
  have h_neg : -∫ ω, A ω ∂M.refMeasure =
      ∫ ω, (B ω + C ω + D ω + E ω) ∂M.refMeasure := by linarith
  -- Step 7: Split ∫(B+C+D+E) = ∫B + ∫C + ∫D + ∫E
  have h_four : ∫ ω, (B ω + C ω + D ω + E ω) ∂M.refMeasure =
      ∫ ω, B ω ∂M.refMeasure + ∫ ω, C ω ∂M.refMeasure +
      ∫ ω, D ω ∂M.refMeasure + ∫ ω, E ω ∂M.refMeasure := by
    have e1 : ∫ ω, (B ω + C ω + D ω + E ω) ∂M.refMeasure =
        ∫ ω, (B ω + C ω + D ω) ∂M.refMeasure +
        ∫ ω, E ω ∂M.refMeasure :=
      integral_add ((h_int_m₁.add h_int_m₂).add h_int_m₃) h_int_cubic
    have e2 : ∫ ω, (B ω + C ω + D ω) ∂M.refMeasure =
        ∫ ω, (B ω + C ω) ∂M.refMeasure +
        ∫ ω, D ω ∂M.refMeasure :=
      integral_add (h_int_m₁.add h_int_m₂) h_int_m₃
    have e3 : ∫ ω, (B ω + C ω) ∂M.refMeasure =
        ∫ ω, B ω ∂M.refMeasure +
        ∫ ω, C ω ∂M.refMeasure :=
      integral_add h_int_m₁ h_int_m₂
    linarith
  -- Step 8: Identify each integral with its definition
  have hB : ∫ ω, B ω ∂M.refMeasure = M.mConnectionCoeff θ i k j := by
    simp only [B, mConnectionCoeff]
  have hC : ∫ ω, C ω ∂M.refMeasure = M.mConnectionCoeff θ j k i := by
    simp only [C, mConnectionCoeff]
  have hD : ∫ ω, D ω ∂M.refMeasure = M.mConnectionCoeff θ i j k := by
    simp only [D, mConnectionCoeff]
  have hE : ∫ ω, E ω ∂M.refMeasure = M.cubicTensor θ i j k := by
    simp only [E, cubicTensor]
  -- Step 9: Assemble
  -- Goal after rw [hg₂_eval i]:
  -- -∫ ω, p(θ,ω) * fderiv(scorePartial(·,j,k))(θ)(eᵢ) ∂μ = cubic + Γ + Γ + Γ
  have hA_eq : ∫ ω, M.density θ ω *
      fderiv ℝ (fun θ'' => M.scorePartial θ'' j k ω) θ
        (EuclideanSpace.single i 1) ∂M.refMeasure =
      ∫ ω, A ω ∂M.refMeasure := by
    congr 1; ext ω; simp only [A]; ring
  rw [hA_eq, h_neg, h_four, hB, hC, hD, hE]; ring

end TwiceDifferentiableModel
end Spectra.InformationGeometry
