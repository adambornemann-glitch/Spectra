/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.DiracEquation.Operators
import Spectra.QuantumMechanics.DiracEquation.FreeHamiltonian
/-!
# The concrete free Dirac operator meets the abstract spectrum theorems

`Operators.lean` proves the headline relativistic facts
(`dirac_unbounded_below/above`, `dirac_not_semibounded`) for an *abstract*
`DiracHamiltonian`, leaving as the only physical input the spectral-reach hypotheses
`h_spectrum_below/above`.  `FreeHamiltonian.lean` builds the *concrete* self-adjoint free Dirac
operator `H_D = -iα·∇ + βmc²` on `L²(ℝ³; ℂ⁴)`, with
`generator (diracUnitaryGroup mc2) = diracHamiltonian mc2`.

This file connects the two layers (TODO task **(b)**):

1. **Instantiate.** `diracHamiltonianAbstract mc2 κ` is a genuine `DiracHamiltonian` whose unitary
   group is the real Stone evolution `diracUnitaryGroup mc2`.  Because
   `generator (diracHamiltonianAbstract mc2 κ).U_grp = diracHamiltonian mc2`, *every*
   `Operators.lean` theorem is now a statement about the honest operator on `L²(ℝ³; ℂ⁴)`.

2. **Reduce the physical hypothesis.** Using the engine bridge
   `spectralProjection_Iic_ne_zero_of_energy_lt` (energy expectation below `N` ⟹ nonzero spectral
   mass below `N`), the still-undischarged `h_spectrum_below/above` are *reduced* to a clean,
   self-contained energy-expectation criterion on `H_D`:

   > for every `N`, some `ψ ∈ H¹(ℝ³; ℂ⁴)` has `Re⟪H_D ψ, ψ⟫ < N·‖ψ‖²`
   > (resp. `> N·‖ψ‖²`).

   The conditional theorems `diracHamiltonian_unbounded_below/above`,
   `diracHamiltonian_not_semibounded` package this.

The **negative-energy** direction is now fully discharged: `NegativeEnergy.lean` constructs, for
every `N`, a high-momentum `H¹` bump on the negative mass shell (where the Fourier symbol
`Ĥ(ξ) = 2π(α·ξ) + mc²β` has eigenvalue `−E(ξ)`, `E(ξ) = √((2π‖ξ‖)² + (mc²)²)`), yielding the
*unconditional* theorems `diracHamiltonian_unbounded_below_unconditional` and
`diracHamiltonian_not_semibounded_unconditional`.  The **only** remaining open piece is the
mirror-image positive-energy wavepacket (Step 3, the `above` direction): the same construction on
the positive mass shell, which would make `diracHamiltonian_unbounded_above` unconditional too.
This file makes those wavepackets the sole missing input.

## References

* [Thaller, *The Dirac Equation*][thaller1992], Section 1.4 (spectrum of the free Dirac operator,
  `σ(H_D) = (-∞, -mc²] ∪ [mc², ∞)`)
* [Bjorken, Drell, *Relativistic Quantum Mechanics*][bjorken1964], Section 3.2 (negative-energy
  solutions and the Dirac sea)
* [Sakurai, Napolitano, *Modern Quantum Mechanics*][sakurai2020], Section 8.3 (relativistic
  quantum mechanics, negative-energy states)

## Tags

Dirac operator, free Dirac Hamiltonian, unbounded below, not semibounded, Dirac sea, antimatter,
spectral reach, energy expectation
-/

open scoped InnerProductSpace
open Spectra.OneParameterUnitaryGroup
open Spectra.QuantumMechanics.SpectralTheory

noncomputable section
namespace Spectra.QuantumMechanics.Dirac

/-! ## Step 1 — Instantiating the abstract `DiracHamiltonian` -/

/-- The concrete free Dirac Hamiltonian, packaged as an abstract `DiracHamiltonian`: its unitary
group is the real Stone evolution `diracUnitaryGroup mc2 = e^{-itH_D}`.  The opaque `matrices`
carrier is `Unit` (the Clifford witness already lives at the matrix layer, `CliffordAlgebra.lean`).
After this definition the `Operators.lean` spectral theorems are statements about `H_D`.

The stored `κ : DiracConstants` is **inert bookkeeping**: it is placed in the `constants` field
but nothing ties `κ.restEnergy = κ.m * κ.c ^ 2` to the `mc2` used to build `diracUnitaryGroup mc2`.
The two are independent arguments and may be passed inconsistently (e.g. `κ.restEnergy ≠ mc2`) with
no contradiction — no theorem in this file constrains or consumes `κ`. -/
def diracHamiltonianAbstract (mc2 : ℝ) (κ : DiracConstants) :
    DiracHamiltonian DiracSpinorL2 DiracConstants Unit where
  U_grp := diracUnitaryGroup mc2
  constants := κ
  matrices := ()

/-- The abstract Hamiltonian's unitary group unfolds to the concrete Stone evolution
`diracUnitaryGroup mc2`; a `simp` lemma so downstream rewriting sees the honest evolution. -/
@[simp] theorem diracHamiltonianAbstract_U_grp (mc2 : ℝ) (κ : DiracConstants) :
    (diracHamiltonianAbstract mc2 κ).U_grp = diracUnitaryGroup mc2 := rfl

/-- **The abstract generator is the concrete operator.**  `generator` of the instantiated
Hamiltonian's evolution is, on the nose, the honest free Dirac operator `H_D = -iα·∇ + βmc²`. -/
theorem generator_diracHamiltonianAbstract (mc2 : ℝ) (κ : DiracConstants) :
    generator (diracHamiltonianAbstract mc2 κ).U_grp = diracHamiltonian mc2 :=
  generator_diracUnitaryGroup mc2

/-- The domain of the abstract generator is the spinor Sobolev space `H¹(ℝ³; ℂ⁴)`. -/
theorem generator_diracUnitaryGroup_domain (mc2 : ℝ) :
    (generator (diracUnitaryGroup mc2)).domain = SobolevDiracH1 := by
  rw [generator_diracUnitaryGroup, diracHamiltonian_domain]

/-! ## Step 2 — Reducing the spectral-reach hypotheses to an energy criterion

The abstract theorems need `h_spectrum_below/above` (nonzero spectral mass arbitrarily far
down/up).  The general engine bridge converts a *single* energy-expectation witness into such
spectral mass, so the physical input collapses to "the energy form is unbounded below/above". -/

/-- **Energy below ⟹ spectral mass below.**  If for every `N` some domain vector has energy
expectation below `N·‖ψ‖²`, the free Dirac operator has nonzero spectral mass in `(-∞, N]` for
every `N` — i.e. `h_spectrum_below` for `diracUnitaryGroup mc2`. -/
theorem dirac_spectrum_below_of_energy (mc2 : ℝ)
    (h_energy : ∀ N : ℝ, ∃ ψ : (generator (diracUnitaryGroup mc2)).domain,
      (⟪generator (diracUnitaryGroup mc2) ψ, (ψ : DiracSpinorL2)⟫_ℂ).re
        < N * ‖(ψ : DiracSpinorL2)‖ ^ 2) :
    ∀ N : ℝ, ∃ φ : DiracSpinorL2,
      spectralProjection (diracUnitaryGroup mc2) (Set.Iic N) measurableSet_Iic φ ≠ 0 := by
  intro N
  obtain ⟨ψ, hψ⟩ := h_energy N
  exact ⟨(ψ : DiracSpinorL2),
    spectralProjection_Iic_ne_zero_of_energy_lt (diracUnitaryGroup mc2) N ψ hψ⟩

/-- **Energy above ⟹ spectral mass above** — `h_spectrum_above` for `diracUnitaryGroup mc2`. -/
theorem dirac_spectrum_above_of_energy (mc2 : ℝ)
    (h_energy : ∀ N : ℝ, ∃ ψ : (generator (diracUnitaryGroup mc2)).domain,
      (⟪generator (diracUnitaryGroup mc2) ψ, (ψ : DiracSpinorL2)⟫_ℂ).re
        > N * ‖(ψ : DiracSpinorL2)‖ ^ 2) :
    ∀ N : ℝ, ∃ φ : DiracSpinorL2,
      spectralProjection (diracUnitaryGroup mc2) (Set.Ici N) measurableSet_Ici φ ≠ 0 := by
  intro N
  obtain ⟨ψ, hψ⟩ := h_energy N
  exact ⟨(ψ : DiracSpinorL2),
    spectralProjection_Ici_ne_zero_of_energy_gt (diracUnitaryGroup mc2) N ψ hψ⟩

/-! ## The concrete relativistic theorems (conditional on the energy criterion) -/

/-- **The free Dirac operator is unbounded below** — the concrete instance of
`dirac_unbounded_below`, conditional only on the energy-expectation criterion (no abstract
spectral hypotheses). -/
theorem diracHamiltonian_unbounded_below (mc2 : ℝ) (κ : DiracConstants)
    (h_energy : ∀ N : ℝ, ∃ ψ : (generator (diracUnitaryGroup mc2)).domain,
      (⟪generator (diracUnitaryGroup mc2) ψ, (ψ : DiracSpinorL2)⟫_ℂ).re
        < N * ‖(ψ : DiracSpinorL2)‖ ^ 2) :
    ∀ bound : ℝ, ∃ ψ : (generator (diracUnitaryGroup mc2)).domain,
      (⟪generator (diracUnitaryGroup mc2) ψ, (ψ : DiracSpinorL2)⟫_ℂ).re
        < bound * ‖(ψ : DiracSpinorL2)‖ ^ 2 :=
  dirac_unbounded_below (diracHamiltonianAbstract mc2 κ)
    (dirac_spectrum_below_of_energy mc2 h_energy)

/-- **The free Dirac operator is unbounded above** — the concrete instance of
`dirac_unbounded_above`. -/
theorem diracHamiltonian_unbounded_above (mc2 : ℝ) (κ : DiracConstants)
    (h_energy : ∀ N : ℝ, ∃ ψ : (generator (diracUnitaryGroup mc2)).domain,
      (⟪generator (diracUnitaryGroup mc2) ψ, (ψ : DiracSpinorL2)⟫_ℂ).re
        > N * ‖(ψ : DiracSpinorL2)‖ ^ 2) :
    ∀ bound : ℝ, ∃ ψ : (generator (diracUnitaryGroup mc2)).domain,
      (⟪generator (diracUnitaryGroup mc2) ψ, (ψ : DiracSpinorL2)⟫_ℂ).re
        > bound * ‖(ψ : DiracSpinorL2)‖ ^ 2 :=
  dirac_unbounded_above (diracHamiltonianAbstract mc2 κ)
    (dirac_spectrum_above_of_energy mc2 h_energy)

/-- **The free Dirac operator is NOT semibounded** — the concrete instance of
`dirac_not_semibounded`: no ground state, the spectrum runs to `−∞`.  This is the Dirac-sea /
antimatter prediction, now stated for the honest operator on `L²(ℝ³; ℂ⁴)`. -/
theorem diracHamiltonian_not_semibounded (mc2 : ℝ) (κ : DiracConstants)
    (h_energy : ∀ N : ℝ, ∃ ψ : (generator (diracUnitaryGroup mc2)).domain,
      (⟪generator (diracUnitaryGroup mc2) ψ, (ψ : DiracSpinorL2)⟫_ℂ).re
        < N * ‖(ψ : DiracSpinorL2)‖ ^ 2) :
    ¬∃ bound : ℝ, ∀ ψ : (generator (diracUnitaryGroup mc2)).domain,
      bound * ‖(ψ : DiracSpinorL2)‖ ^ 2
        ≤ (⟪generator (diracUnitaryGroup mc2) ψ, (ψ : DiracSpinorL2)⟫_ℂ).re :=
  dirac_not_semibounded (diracHamiltonianAbstract mc2 κ)
    (dirac_spectrum_below_of_energy mc2 h_energy)

end Spectra.QuantumMechanics.Dirac
end
