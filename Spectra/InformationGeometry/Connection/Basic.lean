/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Connection.AmariChentsov

/-!
# The α-Connections

The one-parameter family of affine connections on a statistical manifold, built from the Fisher
metric `g` and the Amari–Chentsov cubic tensor `C` (`AmariChentsov.lean`). The Levi-Civita
Christoffel symbols `Γ^(0)` are corrected by `−(α/2)·C` to give `Γ^(α)`; `α = 1` is the
exponential connection, `α = −1` the mixture connection. The dual pair `∇^(α)`, `∇^(−α)` with
respect to `g` is the dualistic structure at the heart of information geometry.

## Main definitions

* `christoffelFirstKind` — Christoffel symbols of the first kind for the Fisher metric, `Γ^(0)`.
* `alphaConnectionCoeff` — the α-connection coefficients `Γ^(α) = Γ^(0) − (α/2)·C`.

## Main statements

* `alpha_connection_duality` — the duality relation between the `α`- and `(−α)`-connections.

## Implementation notes

This file defines only coefficient-level data: `christoffelFirstKind` and
`alphaConnectionCoeff` are functions `ParamSpace n → Fin n → Fin n → Fin n → ℝ`,
not bundled affine connections or a covariant-derivative operator. In particular
`alpha_connection_duality` proves just the algebraic identity
`Γ^(1) + Γ^(-1) = 2Γ^(0)` (the `∓(α/2)·C` terms cancel); it does not establish
`2Γ^(0)_{ij,k} = ∂ᵢg_{jk}` or state duality for a `∇`-operator. The metric
identity is available separately via
`TwiceDifferentiableModel.fisherMatrix_hasFDerivAt` (`Regularity.lean`), and the
identification `mConnectionCoeff = alphaConnectionCoeff (-1)` promised in
`AmariChentsov.lean`'s docstring is not yet proved anywhere in the library.

## References

* S. Amari, H. Nagaoka, *Methods of Information Geometry*, AMS, 2000.
-/
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

The Fisher matrix entries are differentiable at every `θ` in the domain
(`TwiceDifferentiableModel.fisherMatrix_hasFDerivAt`), so no differentiability
hypothesis is needed here: `fderiv` computes the genuine derivative wherever
the model is defined, and this is the only place it is evaluated. -/
noncomputable def christoffelFirstKind
    (θ : ParamSpace n) (i j k : Fin n) : ℝ :=
  (1/2) * (fderiv ℝ (fun θ' => M.toRegularStatisticalModel.fisherMatrix θ' j k) θ
              (EuclideanSpace.single i 1) +
           fderiv ℝ (fun θ' => M.toRegularStatisticalModel.fisherMatrix θ' i k) θ
              (EuclideanSpace.single j 1) -
           fderiv ℝ (fun θ' => M.toRegularStatisticalModel.fisherMatrix θ' i j) θ
              (EuclideanSpace.single k 1))

/-- The α-connection coefficients:
  Γ^(α)_{ij,k}(θ) = Γ^(0)_{ij,k}(θ) − (α/2) C_{ijk}(θ) -/
noncomputable def alphaConnectionCoeff
    (α : ℝ) (θ : ParamSpace n) (i j k : Fin n) : ℝ :=
  M.christoffelFirstKind θ i j k - (α / 2) * M.cubicTensor θ i j k

/-- The e-connection (α = 1) and m-connection (α = -1) coefficients sum to
twice the Christoffel symbol, i.e. the `(α/2)·C` correction terms cancel:
  Γ^(1)_{ij,k} + Γ^(-1)_{ij,k} = 2 Γ^(0)_{ij,k}

This is the algebraic cancellation underlying dual affine connections; it is
purely a consequence of the definitions and does not by itself establish
metric-compatibility (`2Γ^(0)_{ij,k} = ∂ᵢg_{jk}`, which needs
`fisherMatrix_hasFDerivAt`) or the full dualistic structure `∇^(α)+∇^(-α)=2∇^(0)`
on covariant derivatives (`Connection` is not yet bundled in this file; see
module docstring). -/
lemma alpha_connection_duality
    (θ : ParamSpace n) (i j k : Fin n) :
    M.alphaConnectionCoeff 1 θ i j k +
    M.alphaConnectionCoeff (-1) θ i j k =
    2 * M.christoffelFirstKind θ i j k := by
  unfold alphaConnectionCoeff
  ring

end TwiceDifferentiableModel

end Spectra.InformationGeometry
