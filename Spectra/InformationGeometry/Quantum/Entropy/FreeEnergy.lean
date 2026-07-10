/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Quantum.Entropy.CrossEntropy

/-!
# The Gibbs variational principle and the maximum-entropy characterization of thermal states

Quantum statistical mechanics rests on one inequality: the **Gibbs variational principle**, which
says that a thermal (Gibbs) state minimizes the free energy, or equivalently maximizes the
entropy at fixed energy.  In the operator-algebraic formulation this principle *is* Klein's
inequality (the positivity of the quantum relative entropy), which Spectra proved in
`CrossEntropy.lean`.  This file records that identification.

## The modular Hamiltonian and modular energy

A **faithful** state `σ` is a thermal state: it is the Gibbs state `σ = e^{-K}` of its own **modular
Hamiltonian** `K = -log σ` (equivalently `e^{-βH}/Z` for a physical Hamiltonian `H` at inverse
temperature `β`, with `K = βH + (log Z)·I`).  The **modular energy** of a state `ρ` is the
expectation `⟨K⟩_ρ = -Tr(ρ log σ)`, which is exactly the cross entropy
`crossEntropy(ρ,σ)` built operator-theoretically in `CrossEntropy.lean` (so that it is correct even
when `K` is unbounded, as it is for any faithful state on an infinite-dimensional space).

## The variational principle

The **relative free energy** `F_σ(ρ) = ⟨K⟩_ρ - S(ρ) = D(ρ‖σ) ≥ 0` is nonnegative — this is Klein's
inequality `vonNeumannEntropy_le_crossEntropy`, restated here as `entropy_le_modularEnergy`:
`S(ρ) ≤ ⟨K⟩_ρ`.  It is **saturated exactly at the thermal state** (`modularEnergy_self`:
`⟨K⟩_σ = S(σ)`, i.e. `D(σ‖σ) = 0`).  Together these give the **maximum-entropy principle**
(`maxEntropy_of_modularEnergy_eq`): among all states of a given modular energy, the thermal
state has the greatest entropy.

Since `F_σ(ρ) = ⟨K⟩_ρ - S(ρ)` is a `ℝ≥0∞` truncated difference (vacuously `≥ 0`), the content is
shipped as the ordering `S(ρ) ≤ ⟨K⟩_ρ`, never as `F_σ ≥ 0` — the same discipline as Klein itself.

## Deferred (the physical layer)

Connecting the modular Hamiltonian to a *physical* Hamiltonian — constructing the Gibbs state
`e^{-βH}/Z` from a given `H` with discrete spectrum (so that `e^{-βH}` is trace-class),
identifying `-log σ = βH + (log Z)·I`, and expressing the free energy as `F = ⟨H⟩ - T·S` with
the physical energy expectation `⟨H⟩ = Tr(ρH)` (subtle for unbounded `H`) — is a substantial
follow-on requiring an operator-exponential/trace-class construction not yet in Spectra.

## Main results

* `modularEnergy` — `⟨K⟩_ρ = -Tr(ρ log σ)`, the modular energy of `ρ` in the thermal state `σ`.
* `entropy_le_modularEnergy` — the **Gibbs variational principle** `S(ρ) ≤ ⟨K⟩_ρ`.
* `modularEnergy_self` — the thermal state **saturates** the bound: `⟨K⟩_σ = S(σ)`.
* `maxEntropy_of_modularEnergy_eq` — the **maximum-entropy principle**: at fixed modular energy the
  thermal state maximizes entropy.
-/

open scoped ENNReal

namespace Spectra.InformationGeometry.Quantum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The **modular energy** `⟨K⟩_ρ = -Tr(ρ log σ)` of a state `ρ` relative to a thermal state `σ`,
where `K = -log σ` is the modular Hamiltonian.  It is the cross entropy `crossEntropy(ρ,σ)`;
with the physical identification `σ = e^{-βH}/Z` it is `β⟨H⟩_ρ + log Z`. -/
noncomputable def modularEnergy (σ ρ : QState H) : ℝ≥0∞ := QState.crossEntropy ρ σ

/-- **The Gibbs variational principle.**  For a faithful thermal state `σ`, every state's von
Neumann entropy is bounded by its modular energy: `S(ρ) ≤ ⟨K⟩_ρ`.  Equivalently the relative free
energy `F_σ(ρ) = ⟨K⟩_ρ - S(ρ) = D(ρ‖σ)` is nonnegative — this is Klein's inequality.  Shipped as the
ordering (the truncated `ℝ≥0∞` difference `≥ 0` would be vacuous). -/
theorem entropy_le_modularEnergy (σ ρ : QState H) (hσ : σ.Faithful) :
    vonNeumannEntropy ρ ≤ modularEnergy σ ρ :=
  ρ.vonNeumannEntropy_le_crossEntropy σ hσ

/-- **The thermal state saturates the variational bound**: `⟨K⟩_σ = S(σ)`, i.e. the relative free
energy `D(σ‖σ)` vanishes.  This is the equality case of the Gibbs variational principle and
expresses that `σ` sits *at* the free-energy minimum. -/
theorem modularEnergy_self (σ : QState H) : modularEnergy σ σ = vonNeumannEntropy σ :=
  σ.crossEntropy_self

/-- **The maximum-entropy principle.**  Among all states with the same modular energy as the thermal
state `σ`, the thermal state has the greatest entropy: if `⟨K⟩_ρ = ⟨K⟩_σ` then `S(ρ) ≤ S(σ)`.  This
is the precise sense in which the Gibbs state is the maximum-entropy state at fixed energy. -/
theorem maxEntropy_of_modularEnergy_eq (σ ρ : QState H) (hσ : σ.Faithful)
    (hE : modularEnergy σ ρ = modularEnergy σ σ) :
    vonNeumannEntropy ρ ≤ vonNeumannEntropy σ := by
  calc vonNeumannEntropy ρ ≤ modularEnergy σ ρ := entropy_le_modularEnergy σ ρ hσ
    _ = modularEnergy σ σ := hE
    _ = vonNeumannEntropy σ := modularEnergy_self σ

end Spectra.InformationGeometry.Quantum
