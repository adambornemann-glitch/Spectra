/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Dynamics.CubicTensor
open MeasureTheory Finset Filter Topology TopologicalSpace
namespace Spectra.InformationGeometry
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

namespace TwiceDifferentiableModel

variable (M : TwiceDifferentiableModel n Ω)


-- ============================================================================
-- §3. The α-Connection Coefficients
-- ============================================================================

/-! ### Connection coefficients from the metric and cubic tensor

The Christoffel symbols of the Levi-Civita connection Γ^(0) and the
α-connection Γ^(α) are defined in terms of g and C.  For α = 1 we get
the exponential (e-)connection; for α = -1, the mixture (m-)connection.

The duality ∇^(α) ↔ ∇^(-α) with respect to g is the **dualistic structure**
— the heart of information geometry. -/

/-- The Christoffel symbols of the first kind for the Fisher metric:
  Γ_{ij,k}(θ) = ½(∂ᵢg_{jk} + ∂ⱼg_{ik} - ∂ₖg_{ij})

Requires differentiability of the Fisher matrix entries. -/
noncomputable def christoffelFirstKind
    (θ : ParamSpace n) (i j k : Fin n)
    (_h_deriv : ∀ a b, DifferentiableAt ℝ
      (fun θ' => M.toRegularStatisticalModel.fisherMatrix θ' a b) θ) : ℝ :=
  (1/2) * (fderiv ℝ (fun θ' => M.toRegularStatisticalModel.fisherMatrix θ' j k) θ
              (EuclideanSpace.single i 1) +
           fderiv ℝ (fun θ' => M.toRegularStatisticalModel.fisherMatrix θ' i k) θ
              (EuclideanSpace.single j 1) -
           fderiv ℝ (fun θ' => M.toRegularStatisticalModel.fisherMatrix θ' i j) θ
              (EuclideanSpace.single k 1))

/-- The α-connection coefficients:
  Γ^(α)_{ij,k}(θ) = Γ^(0)_{ij,k}(θ) − (α/2) C_{ijk}(θ)  -/
noncomputable def alphaConnectionCoeff
    (α : ℝ) (θ : ParamSpace n) (i j k : Fin n)
    (h_deriv : ∀ a b, DifferentiableAt ℝ
      (fun θ' => M.toRegularStatisticalModel.fisherMatrix θ' a b) θ) : ℝ :=
  M.christoffelFirstKind θ i j k h_deriv - (α / 2) * M.cubicTensor θ i j k

/-- The e-connection (α = 1) and m-connection (α = -1) are dual
with respect to the Fisher metric:
  Γ^(1)_{ij,k} + Γ^(-1)_{ij,k} = 2 Γ^(0)_{ij,k} = ∂ᵢg_{jk}

This is a direct consequence of the definition. -/
lemma alpha_connection_duality
    (θ : ParamSpace n) (i j k : Fin n)
    (h_deriv : ∀ a b, DifferentiableAt ℝ
      (fun θ' => M.toRegularStatisticalModel.fisherMatrix θ' a b) θ) :
    M.alphaConnectionCoeff 1 θ i j k h_deriv +
    M.alphaConnectionCoeff (-1) θ i j k h_deriv =
    2 * M.christoffelFirstKind θ i j k h_deriv := by
  unfold alphaConnectionCoeff
  ring

end TwiceDifferentiableModel

end Spectra.InformationGeometry
