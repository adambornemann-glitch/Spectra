/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: InformationGeometry/Dynamics/Schrodinger.lean
-/
import Spectra.InformationGeometry.Stone.Basic
open MeasureTheory Finset Filter Topology TopologicalSpace
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
namespace Spectra.InformationGeometry
variable (M : TwiceDifferentiableModel n Ω)
namespace TwiceDifferentiableModel
variable (F : M.DivergencePreservingFamily)



-- ============================================================================
-- # The Information-Geometric Schrödinger Equations
-- ============================================================================

/-! ### IG Schrödinger equations

Three forms of the evolution equation for divergence-preserving flows,
mirroring the three Schrödinger equations in `UnitaryEvo/Schrodinger.lean`.

| Quantum (Schrödinger.lean)           | Statistical (this section)                  |
|--------------------------------------|---------------------------------------------|
| `schrödinger_equation₁` (at t = 0)   | `infoGeometric_schrodinger₁` (at t = 0)     |
| `schrödinger_equation₂` (at time t)  | `infoGeometric_schrodinger₂` (at time t)    |
| `schrödinger_equation₃` (integral)   | `infoGeometric_schrodinger₃` (conservation) |

| Symbol            | Quantum                  | Statistical              |
|-------------------|--------------------------|--------------------------|
| State             | ψ(t) = U(t)ψ₀            | θ(t) = φ_t(θ₀)           |
| Generator         | A (self-adjoint)         | X (Killing + ∇C = 0)     |
| Evolution eqn     | dψ/dt = iAψ              | dθ/dt = X(θ)             |
| Conserved qty     | ⟨ψ,φ⟩                    | D(θ₁ ‖ θ₂)               |
| Conservation law  | d/dt⟨U(t)ψ,U(t)φ⟩ = 0    | d/dt D(φ_t θ₁‖φ_t θ₂)=0  |
-/


/-- **IG Schrödinger Equation (Form 1): Initial velocity.**

  d/dt φ_t(θ) |_{t=0} = X(θ)

The generator X gives the initial velocity of every parameter
trajectory. This is the analogue of `schrödinger_equation₁`:

  d/dt U(t)ψ |_{t=0} = iAψ  -/
theorem infoGeometric_schrodinger₁
    (F : M.DivergencePreservingFamily)
    (θ : ParamSpace n) :
    HasDerivAt (fun t => F.φ t θ) (F.generator θ) 0 := by
  have h_diff := F.generator_exists θ
  rw [DivergencePreservingFamily.generator]
  exact h_diff.hasFDerivAt.hasDerivAt


/-- **IG Schrödinger Equation (Form 2): Evolution at time t.**

  d/dt φ_t(θ) = X(φ_t(θ))      ∀ t

The parameter trajectory satisfies an autonomous ODE determined
by the generator at the current state. This is the analogue of
`schrödinger_equation₂`:

  d/dt U(t)ψ = iA · U(t)ψ      ∀ t -/
theorem infoGeometric_schrodinger₂
    (F : M.DivergencePreservingFamily)
    (θ : ParamSpace n) (t : ℝ) :
    HasDerivAt (fun s => F.φ s θ) (F.generator (F.φ t θ)) t := by
  have h₀ : HasDerivAt (fun u => F.φ u (F.φ t θ)) (F.generator (F.φ t θ)) 0 :=
    infoGeometric_schrodinger₁ M F (F.φ t θ)
  have h_eq : (fun s => F.φ s θ) = (fun s => F.φ (s - t) (F.φ t θ)) := by
    ext s; rw [← F.group_law (s - t) t θ, sub_add_cancel]
  rw [h_eq]
  set g := fun u => F.φ u (F.φ t θ)
  set f := fun s : ℝ => s - t
  have hg : HasFDerivAt g
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (F.generator (F.φ t θ)))
      (f t) := by
    simp only [f, sub_self]; exact h₀.hasFDerivAt
  have hf : HasFDerivAt f (ContinuousLinearMap.id ℝ ℝ) t := by
    exact hasFDerivAt_sub_const t
  have h_comp := hg.comp t hf
  rw [show g ∘ f = fun s => F.φ (s - t) (F.φ t θ) from rfl] at h_comp
  rwa [ContinuousLinearMap.comp_id] at h_comp

/-- **IG Schrödinger Equation (Form 3): Divergence conservation.**

  d/dt D(φ_t(θ₁) ‖ φ_t(θ₂)) = 0      ∀ t

The infinitesimal form of divergence preservation. This is the
analogue of `schrödinger_equation₃` / inner product conservation:

  d/dt ⟨U(t)ψ, U(t)φ⟩ = 0      ∀ t  -/
theorem infoGeometric_schrodinger₃
    (F : M.DivergencePreservingFamily)
    {θ₁ θ₂ : ParamSpace n} (hθ₁ : θ₁ ∈ M.paramDomain)
    (hθ₂ : θ₂ ∈ M.paramDomain) (t : ℝ) :
    HasDerivAt (fun s => M.klDiv (F.φ s θ₁) (F.φ s θ₂)) 0 t := by
  have hconst : (fun s => M.klDiv (F.φ s θ₁) (F.φ s θ₂)) =
      fun _ => M.klDiv θ₁ θ₂ := by
    ext s; exact F.preserves_divergence s θ₁ hθ₁ θ₂ hθ₂
  rw [hconst]; exact hasDerivAt_const t _


/-- **IG Schrödinger Equation (Form 4): Observable evolution (IG Ehrenfest).**

  d/dt f(φ_t(θ)) = df(X(φ_t(θ)))      ∀ t

The time derivative of any smooth observable along the flow equals
the directional derivative of f in the generator direction at the
current state. This is the analogue of the Ehrenfest theorem:

  d/dt ⟨U(t)ψ, A U(t)ψ⟩ = ⟨U(t)ψ, i[H,A] U(t)ψ⟩

| Quantum                              | Statistical                          |
|--------------------------------------|--------------------------------------|
| Observable A                         | Smooth function f : Θ → ℝ            |
| Expectation ⟨ψ(t), Aψ(t)⟩            | Evaluation f(θ(t))                   |
| Commutator i[H,A]                    | Lie bracket / directional deriv X·f  |
| d/dt⟨ψ(t),Aψ(t)⟩ = ⟨ψ(t),i[H,A]ψ(t)⟩ | d/dt f(θ(t)) = (Xf)(θ(t))            |
-/
theorem infoGeometric_ehrenfest
    (F : M.DivergencePreservingFamily)
    (f : ParamSpace n → ℝ) (hf : Differentiable ℝ f)
    (θ : ParamSpace n) (t : ℝ) :
    HasDerivAt (fun s => f (F.φ s θ))
      (fderiv ℝ f (F.φ t θ) (F.generator (F.φ t θ))) t :=
  (hf (F.φ t θ)).hasFDerivAt.comp_hasDerivAt t
    (infoGeometric_schrodinger₂ M F θ t)


end TwiceDifferentiableModel

end InformationGeometry
