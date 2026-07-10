/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/

/-
Spectra: Operators.lean
Dirac Operator and Hamiltonian, rebuilt on the constructed spectral calculus.

-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Spectra.SpectralTheory.Measure.GeneratorLink
import Spectra.SpectralTheory.Algebra
/-!
# Dirac Operator and Hamiltonian

This file rebuilds the abstract Dirac Hamiltonian on the constructed spectral machinery.  The
Hamiltonian is packaged as a one-parameter unitary group `U(t) = e^{-itH_D/ℏ}` together with the
physical constants and Dirac matrices of a given particle; the operator `H_D` itself is recovered
as the (constructed) `generator` of that group.  On this footing, symmetry of `H_D` is a theorem
rather than a hypothesis, and the headline spectral facts — the Dirac Hamiltonian is unbounded
below and above, hence not semibounded (no ground state) — reduce to the genuinely physical input
that the spectrum reaches arbitrarily far in each direction.

## Main definitions

* `DiracHamiltonian` — the abstract Dirac Hamiltonian: a one-parameter unitary group `U_grp`
  bundled with physical constants and Dirac matrices; `H_D` itself is `generator U_grp`.
* `DiracConstants` — the physical constants `ℏ, c, m` (with positivity/non-negativity witnesses).

## Main results

* `dirac_unbounded_below` — for any bound, some state has energy below it.
* `dirac_unbounded_above` — for any bound, some state has energy above it.
* `dirac_not_semibounded` — the Dirac Hamiltonian has no lower energy bound (no ground state).

## Implementation notes

The old version of this file took a projection-valued measure as a *hypothesis*
(`IsSpectralMeasure E`, `IsSpectralMeasureFor E gen`) and stored a self-adjoint generator
as a *field*.  Every one of those inputs is now a theorem:

| old (hypothesis/field)                   | new (theorem)                                      |
| ---------------------------------------- | -------------------------------------------------- |
| `E : Set ℝ → H →L[ℂ] H`, `hE.univ/…/mul` | `spectralProjection` + `_univ`, `_empty`, `_inter` |
| `spectral_scalar_measure E φ`            | `borelMeasure U_grp φ` (a genuine `Measure`)       |
| `spectral_scalar_measure_eq_norm_sq`     | `norm_sq_spectralProjection`                       |
| `gen : Generator U_grp` (field)          | `generator U_grp` (constructed `LinearPMap`)       |
| `gen_selfAdjoint` (field)                | `generator_isFormalAdjoint` (symmetry, proved)     |
| `dirac_generates_unitary` (axiom→field)  | trivial by construction                            |
| `id_domain_subset_generator_domain`      | `spectralProjection_mem_generatorDomain`           |
| `generator_inner_eq_integral_diagonal`   | `generator_spectralProjection` + absorption        |
| `functional_calculus_comm`               | `spectralCalculus_comm` (already compiled)         |

For `gen_selfAdjoint`, note that `generator_isFormalAdjoint` supplies only symmetry; full
self-adjointness is the deficiency-index project in `SelfAdjoint.lean`, not a stored assumption.
For the `id_domain_subset_generator_domain` route, `spectralProjection_mem_generatorDomain` is
proved from the bounded calculus and the dominated convergence theorem only.

The headline theorems (`dirac_unbounded_below/above`, `dirac_not_semibounded`) keep their
statements, with the *only* surviving hypotheses being the genuinely physical ones,
`h_spectrum_below/above` — discharging those requires the concrete Dirac operator on
`L²(ℝ³; ℂ⁴)` (Fourier multiplier `α·p + βmc²`), a separate project.

PVM σ-additivity is never needed: the finite-approximation lemmas use
`measure_iUnion_null` on the *scalar* measure, and `borelMeasure` is a genuine `Measure`.

Dropped relative to the old file: `domain_dense'` (density follows from self-adjointness,
which awaits `SelfAdjoint.lean`), and the `∫s²`-integrability domain route (subsumed).

## References

* [Thaller, *The Dirac Equation*][thaller1992], Section 1 (unbounded spectrum and the
  Dirac-sea interpretation of the negative-energy states).

## Tags

Dirac operator, Dirac Hamiltonian, unbounded operator, semibounded, Dirac sea, spectrum
-/

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace

open Spectra.Borel
open SpectralMeasure
open Spectra.OneParameterUnitaryGroup

/-! ## The Dirac Hamiltonian -/
open Spectra.QuantumMechanics.SpectralTheory
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.QuantumMechanics.Dirac
variable {K M : Type*}

/-- The fiber space ℂ⁴ at each spatial point.

Encodes spin (2 components) and particle/antiparticle (2 components) degrees of freedom.
A Dirac spinor field is a section `ψ : ℝ³ → SpinorSpace`. -/
abbrev SpinorSpace := EuclideanSpace ℂ (Fin 4)

/-- Physical constants for the Dirac equation. -/
structure DiracConstants where
  /-- Reduced Planck constant ℏ: the quantum of action. -/
  hbar : ℝ
  /-- Speed of light c: the relativistic velocity scale. -/
  c : ℝ
  /-- Particle rest mass m: determines the spectral gap 2mc². -/
  m : ℝ
  /-- ℏ > 0: required for non-trivial quantum dynamics. -/
  hbar_pos : hbar > 0
  /-- c > 0: required for Lorentz signature. -/
  c_pos : c > 0
  /-- m ≥ 0: negative mass is unphysical; zero mass allowed. -/
  m_nonneg : m ≥ 0

/-- Rest mass energy `E₀ = mc²`. -/
def DiracConstants.restEnergy (κ : DiracConstants) : ℝ := κ.m * κ.c ^ 2

/-- The Dirac Hamiltonian. **Constructed** from `U_grp` (`generator U_grp`), and its
symmetry is the theorem `generator_isFormalAdjoint`.  Full self-adjointness is the
deficiency-index project (`SelfAdjoint.lean`), not a stored assumption.
Physical content: `H_D = -iℏc(α·∇) + βmc²` generates `U(t) = e^{-itH_D/ℏ}`. -/
structure DiracHamiltonian (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (K M : Type*) where
  /-- The one-parameter unitary group `U(t) = e^{-itH_D/ℏ}`. -/
  U_grp : OneParameterUnitaryGroup (H := H)
  /-- Physical constants ℏ, c, m for this particle. -/
  constants : K
  /-- The Dirac matrices for this particle (an opaque carrier: the Clifford relations are not
  enforced by this structure and must be supplied by whatever instantiates it). -/
  matrices : M

/-- The domain of the Hamiltonian (from the constructed generator). -/
abbrev domain (H_D : DiracHamiltonian H K M) : Submodule ℂ H :=
  generatorDomain H_D.U_grp

/-- The operator (from the constructed generator). -/
noncomputable abbrev op (H_D : DiracHamiltonian H K M) :
    (generator H_D.U_grp).domain →ₗ[ℂ] H :=
  (generator H_D.U_grp).toFun

/-- Symmetry: `⟪H_D ψ, φ⟫ = ⟪ψ, H_D φ⟫`.  A theorem now (`generator_isFormalAdjoint`),
not a field. -/
lemma symmetric (H_D : DiracHamiltonian H K M)
    (ψ φ : (generator H_D.U_grp).domain) :
    ⟪generator H_D.U_grp ψ, (φ : H)⟫_ℂ = ⟪(ψ : H), generator H_D.U_grp φ⟫_ℂ :=
  generator_isFormalAdjoint H_D.U_grp ψ φ

/-- The Dirac operator generates a strongly continuous unitary group with a symmetric
generator — trivial by construction.  (The old axiom, then the old field, now nothing.) -/
lemma dirac_generates_unitary (H_D : DiracHamiltonian H K M) :
    ∃ U : OneParameterUnitaryGroup (H := H),
      (generator U).IsFormalAdjoint (generator U) :=
  ⟨H_D.U_grp, generator_isFormalAdjoint H_D.U_grp⟩


/-- **The Dirac operator is unbounded below**: for any bound, some state has energy below it.

Every spectral input is constructed from `H_D.U_grp`; the lone hypothesis is the genuinely
physical one (the spectrum reaches arbitrarily far down), which for the concrete operator
`H_D = -iℏc(α·∇) + βmc²` on `L²(ℝ³; ℂ⁴)` is a Fourier-multiplier computation — a
separate project. -/
lemma dirac_unbounded_below (H_D : DiracHamiltonian H K M)
    (h_spectrum_below : ∀ N : ℝ, ∃ φ : H,
      spectralProjection H_D.U_grp (Set.Iic N) measurableSet_Iic φ ≠ 0) :
    ∀ bound : ℝ, ∃ ψ : (generator H_D.U_grp).domain,
      (⟪generator H_D.U_grp ψ, (ψ : H)⟫_ℂ).re < bound * ‖(ψ : H)‖ ^ 2 := by
  intro bound
  obtain ⟨ψ, _, hψ⟩ :=
    generator_has_arbitrarily_negative_energy H_D.U_grp h_spectrum_below bound
  exact ⟨ψ, hψ⟩

/-- **The Dirac operator is unbounded above**: for any bound, some state has energy above it. -/
lemma dirac_unbounded_above (H_D : DiracHamiltonian H K M)
    (h_spectrum_above : ∀ N : ℝ, ∃ φ : H,
      spectralProjection H_D.U_grp (Set.Ici N) measurableSet_Ici φ ≠ 0) :
    ∀ bound : ℝ, ∃ ψ : (generator H_D.U_grp).domain,
      (⟪generator H_D.U_grp ψ, (ψ : H)⟫_ℂ).re > bound * ‖(ψ : H)‖ ^ 2 := by
  intro bound
  obtain ⟨ψ, _, hψ⟩ :=
    generator_has_arbitrarily_positive_energy H_D.U_grp h_spectrum_above bound
  exact ⟨ψ, hψ⟩

/-- **The Dirac operator is NOT semibounded** (no ground state).

**Physical significance**: unlike the non-relativistic Hamiltonian `H = p²/2m + V`, which
is bounded below (has a ground state), the Dirac Hamiltonian has states of arbitrarily
negative energy — the spectrum extends to `−∞`.  This is why Dirac introduced the "sea"
interpretation: in the physical vacuum all negative-energy states are already occupied,
and the Pauli exclusion principle prevents further electrons from falling into them —
the prediction of antimatter. -/
lemma dirac_not_semibounded (H_D : DiracHamiltonian H K M)
    (h_spectrum_below : ∀ N : ℝ, ∃ φ : H,
      spectralProjection H_D.U_grp (Set.Iic N) measurableSet_Iic φ ≠ 0) :
    ¬∃ bound : ℝ, ∀ ψ : (generator H_D.U_grp).domain,
      bound * ‖(ψ : H)‖ ^ 2 ≤ (⟪generator H_D.U_grp ψ, (ψ : H)⟫_ℂ).re := by
  push Not
  intro bound
  obtain ⟨ψ, _, hψ⟩ :=
    generator_has_arbitrarily_negative_energy H_D.U_grp h_spectrum_below bound
  exact ⟨ψ, hψ⟩

end Spectra.QuantumMechanics.Dirac
