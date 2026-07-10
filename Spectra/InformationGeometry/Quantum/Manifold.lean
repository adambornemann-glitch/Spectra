/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Quantum.State
import Spectra.InformationGeometry.StatisticalModel

/-!
# The quantum statistical manifold

The operator-valued analogue of `StatisticalModel`: a smooth family `θ ↦ ρ_θ` of faithful quantum
states, indexed by a finite-dimensional real parameter. This is the **point-set carrier of the
information-geometric second view of quantum theory** — the object on which the quantum Fisher/SLD,
BKM/Kubo–Mori metric, and the Petz recovery story are all built, exactly as the classical
`StatisticalModel` carries `klDiv`, `Fisher`, and the dual `e/m` connections.

The design mirrors `StatisticalModel` field-for-field:

| classical `StatisticalModel` | quantum `QuantumStatisticalModel` |
| --- | --- |
| `density : ParamSpace n → Ω → ℝ`     | `ρ : ParamSpace n → QState H` |
| `density_pos_ae` (faithfulness a.e.) | `faithful` (trivial kernel) |
| `density_smooth` (`ContDiffOn ℝ ⊤`)  | `smooth` (`ContDiffOn ℝ ⊤` in trace norm) |

Smoothness is taken in the **trace-norm** topology (`TraceClass H`), the natural home of the state
and of its tangent vectors `∂_i ρ_θ` (self-adjoint trace-class operators).

## Main definitions

* `QuantumStatisticalModel n H` — a smooth family of faithful quantum states over `ParamSpace n`.
* `QuantumStatisticalModel.op` — the underlying bounded operator `ρ_θ` at a parameter `θ`.
-/

namespace Spectra.InformationGeometry.Quantum

open Spectra.QuantumMechanics.Channels

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A **quantum statistical model**: a smooth family `θ ↦ ρ_θ` of faithful quantum states on `H`,
indexed by an open parameter domain in `ParamSpace n = EuclideanSpace ℝ (Fin n)`. The
operator-valued analogue of `StatisticalModel`; the carrier of the information-geometric second
view. -/
structure QuantumStatisticalModel (n : ℕ) (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The parameter domain `Θ ⊆ ParamSpace n`. -/
  paramDomain : Set (ParamSpace n)
  /-- The parameter domain is open (so derivatives in `θ` make sense). -/
  isOpen_paramDomain : IsOpen paramDomain
  /-- The parameter domain is nonempty. -/
  nonempty_paramDomain : paramDomain.Nonempty
  /-- The state `ρ_θ` at each parameter. -/
  ρ : ParamSpace n → QState H
  /-- Every state in the family is faithful (full-rank / trivial kernel). -/
  faithful : ∀ θ ∈ paramDomain, (ρ θ).Faithful
  /-- The family is smooth in the trace-norm topology. -/
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ => (ρ θ).toTraceClass) paramDomain

namespace QuantumStatisticalModel

variable {n : ℕ} (M : QuantumStatisticalModel n H)

/-- The bounded operator `ρ_θ` at a parameter `θ`. -/
def op (θ : ParamSpace n) : H →L[ℂ] H := (M.ρ θ).toOp

@[simp] lemma op_eq (θ : ParamSpace n) : M.op θ = (M.ρ θ).toOp := rfl

lemma op_nonneg (θ : ParamSpace n) : 0 ≤ M.op θ := (M.ρ θ).nonneg

@[simp] lemma trace_op (θ : ParamSpace n) : trace (M.op θ) = 1 := (M.ρ θ).trace_one

/-- The state at a parameter in the domain is faithful. -/
lemma faithful_of_mem {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) : (M.ρ θ).Faithful :=
  M.faithful θ hθ

end QuantumStatisticalModel

end Spectra.InformationGeometry.Quantum
