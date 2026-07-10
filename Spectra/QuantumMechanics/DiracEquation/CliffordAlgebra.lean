/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearPMap
/-!
# The Dirac Equation and Relativistic Quantum Mechanics

This file fixes the standard (Dirac–Pauli) representation of the velocity matrices
`α = (α₁, α₂, α₃)`, the mass matrix `β`, and the gamma matrices `γ⁰ = β`, `γⁱ = βαⁱ`,
and proves their Clifford-algebra relations by brute-force entrywise computation
(`dirac_compute`). It is the matrix foundation of the directory; the physics those
relations *imply* is formalized in the other files and is **not** proved here (see "Where
the physics is actually proved" below). The "Physical interpretation" notes that follow are
motivation only.

## Overview

The Dirac equation is the relativistic wave equation for fermions:

  iℏ ∂ψ/∂t = H_D ψ,    where   H_D = -iℏc(α·∇) + βmc²

The matrices α = (α₁, α₂, α₃) and β satisfy the Clifford algebra relations:
- αᵢ² = β² = I (involutions)
- {αᵢ, αⱼ} = 0 for i ≠ j (spatial anticommutation)
- {αᵢ, β} = 0 (momentum-mass anticommutation)

These relations ensure H_D² gives the relativistic dispersion relation
E² = (pc)² + (mc²)², which is the mathematical content of special relativity.

## Physical interpretation

### The Dirac Sea and Antiparticles
The spectrum σ(H_D) = (-∞, -mc²] ∪ [mc², ∞) has negative energy states.
Dirac's interpretation: the "vacuum" has all negative-energy states filled
(the Dirac sea). A hole in the sea appears as a positron — a particle with
positive energy and opposite charge.

### Chirality and the Weak Force
The matrix γ⁵ projects onto left-handed (P_L = (1-γ⁵)/2) and right-handed
(P_R = (1+γ⁵)/2) states. The weak nuclear force couples only to left-handed
particles, which is why γ⁵ is physically important.

### Probability Conservation
Unlike the Klein-Gordon equation, the Dirac equation has a *positive-definite*
probability density ρ = ψ†ψ ≥ 0. This is the key physical requirement that
motivated Dirac's construction. The proof that dP/dt = 0 follows from the
continuity equation ∂ᵤjᵘ = 0.

### The Born Rule
The theorem `born_rule_valid` (in `QuantumMechanics/BornRule/Conservation.lean`, **not** this
file) shows that `ρ/∫ρ` satisfies the axioms of a probability distribution. This connects the
mathematical formalism to quantum mechanical measurement.

## Where the physics is actually proved

This file is pure matrix algebra. The downstream physics lives elsewhere in the directory:
`Dispersion.lean` (`D² = (|p|²+m²)I`), `FreeHamiltonian.lean` (the concrete self-adjoint `H_D` on
`L²(ℝ³;ℂ⁴)`), `Chirality.lean` / `Spin.lean` (projectors, spin algebra), `Current.lean` /
`Conservation.lean` (`j⁰ ≥ 0`, local `∂ᵤjᵘ = 0`). The spectrum
`σ(H_D) = (-∞,-mc²]∪[mc²,∞)` and the mass gap are so far only abstract (`Operators.lean`),
not established for the concrete operator.

## Main definitions

* `diracAlpha1`, `diracAlpha2`, `diracAlpha3` — the velocity matrices `α₁, α₂, α₃` in the
  standard (Dirac–Pauli) representation.
* `diracBeta` — the mass matrix `β = diag(1, 1, -1, -1)`.
* `gamma0`, `gamma1`, `gamma2`, `gamma3` — the gamma matrices `γ⁰ = β`, `γⁱ = βαⁱ`.

## Main results

* `diracAlpha1_sq`, `diracAlpha2_sq`, `diracAlpha3_sq`, `diracBeta_sq` — each of
  `α₁, α₂, α₃, β` is an involution (`M² = I`).
* `diracAlpha12_anticommute`, `diracAlpha13_anticommute`, `diracAlpha23_anticommute` — distinct
  `αᵢ` anticommute; `diracAlpha1_beta_anticommute`, `diracAlpha2_beta_anticommute`,
  `diracAlpha3_beta_anticommute` — each `αᵢ` anticommutes with `β`.
* `diracAlpha1_hermitian`, `diracAlpha2_hermitian`, `diracAlpha3_hermitian`,
  `diracBeta_hermitian` — each `αᵢ` and `β` is Hermitian.
* `clifford_μν` (the sixteen lemmas `clifford_00` … `clifford_33`) — the Minkowski–Clifford
  table `{γᵘ, γᵛ} = 2ηᵘᵛ I`.
* `gamma0_hermitian_proof`, `gamma1_antihermitian`, `gamma2_antihermitian`,
  `gamma3_antihermitian` — `γ⁰` is Hermitian and the spacelike `γⁱ` are anti-Hermitian.

## References

* [Dirac, *The Principles of Quantum Mechanics*][dirac1930], Chapter XI
* [Thaller, *The Dirac Equation*][thaller1992], Chapter 2
* [Peskin, Schroeder, *An Introduction to Quantum Field Theory*][peskin1995], Chapter 3
* [Reed, Simon, *Methods of Modern Mathematical Physics*][reed1975], Vol. II §X.4

## Tags

Dirac equation, Clifford algebra, gamma matrices, spinor, relativistic quantum mechanics,
spectral gap, probability conservation, Born rule, chirality
-/
open Complex
namespace Spectra.QuantumMechanics.Dirac

/-- α₁ in standard representation (4×4) -/
def diracAlpha1 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 1;
     0, 0, 1, 0;
     0, 1, 0, 0;
     1, 0, 0, 0]

/-- α₂ in standard representation (4×4) -/
def diracAlpha2 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, -I;
     0, 0, I, 0;
     0, -I, 0, 0;
     I, 0, 0, 0]

/-- α₃ in standard representation (4×4) -/
def diracAlpha3 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0;
     0, 0, 0, -1;
     1, 0, 0, 0;
     0, -1, 0, 0]

/-- β in standard representation (4×4) -/
def diracBeta : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]

/-- Verify an entrywise matrix identity in the Dirac/Clifford algebra.
    Pass the matrix definitions to unfold as simp lemmas. -/
macro "dirac_compute" defs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic|
    (ext a b
     fin_cases a <;> fin_cases b <;>
       simp [$defs,*, Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply,
             Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply,
             Fin.sum_univ_four, Complex.I_mul_I] <;>
     ring_nf <;> rfl))


/-- α₁ is an involution: α₁² = I.

**Mathematical meaning**: α₁ has eigenvalues ±1 (since x² = 1 ⟹ x = ±1).
Combined with Hermiticity, this gives a complete spectral decomposition.

**Physical meaning**: The Clifford algebra relation {αᵢ, αⱼ} = 2δᵢⱼ
(of which this is the i = j = 1 case) is what makes H_D² yield the
relativistic dispersion relation E² = (pc)² + (mc²)².

**Proof strategy**: Brute-force verification of all 16 matrix entries.
`fin_cases a <;> fin_cases b` splits into the 4×4 = 16 cases (a,b) ∈ Fin 4 × Fin 4,
then `simp` computes each entry of the product. -/
lemma diracAlpha1_sq : diracAlpha1 * diracAlpha1 = 1 := by
  dirac_compute diracAlpha1

/-- α₂ is an involution: α₂² = I.

Unlike α₁ and α₃, the matrix α₂ contains imaginary entries (±I) from the
Pauli-Y matrix. The product α₂² involves terms like (-I)(I) = 1, which
is why `mul_neg, neg_mul` appear in the simplification. -/
lemma diracAlpha2_sq : diracAlpha2 * diracAlpha2 = 1 := by
  dirac_compute diracAlpha2

/-- α₃ is an involution: α₃² = I.

The matrix α₃ is built from the Pauli-Z matrix (diagonal ±1 entries).
The product involves (-1)(-1) = 1 terms, hence `neg_neg` in the simplification. -/
lemma diracAlpha3_sq : diracAlpha3 * diracAlpha3 = 1 := by
  dirac_compute diracAlpha3

/-- β is an involution: β² = I.

The mass matrix β = diag(1, 1, -1, -1) distinguishes upper spinor components
(particle) from lower components (antiparticle). Being diagonal, the proof
is simpler than for the α matrices — just (-1)² = 1 on the lower block. -/
lemma diracBeta_sq : diracBeta * diracBeta = 1 := by
  dirac_compute diracBeta

/-- α₁ and α₂ anticommute: {α₁, α₂} = α₁α₂ + α₂α₁ = 0.

This is the i ≠ j case of the Clifford relation {αᵢ, αⱼ} = 2δᵢⱼ.
Anticommutation of distinct α matrices ensures that H_D² produces
the Laplacian (not some cross-term mess): (α·p)² = p₁² + p₂² + p₃².

The proof mixes real entries (from α₁) with imaginary entries (from α₂),
producing cancellations like 1·I + I·(-1) = 0. -/
lemma diracAlpha12_anticommute : diracAlpha1 * diracAlpha2 + diracAlpha2 * diracAlpha1 = 0 := by
  dirac_compute diracAlpha1, diracAlpha2

/-- α₁ and α₃ anticommute: {α₁, α₃} = 0.

Both matrices have real entries (α₁ from Pauli-X, α₃ from Pauli-Z),
so cancellations involve only ±1 arithmetic, no complex numbers. -/
lemma diracAlpha13_anticommute : diracAlpha1 * diracAlpha3 + diracAlpha3 * diracAlpha1 = 0 := by
  dirac_compute diracAlpha1, diracAlpha3

/-- α₂ and α₃ anticommute: {α₂, α₃} = 0.

This mixes imaginary entries (from α₂) with real entries (from α₃).
Cancellations have the form I·1 + 1·(-I) = 0. -/
lemma diracAlpha23_anticommute : diracAlpha2 * diracAlpha3 + diracAlpha3 * diracAlpha2 = 0 := by
  dirac_compute diracAlpha2, diracAlpha3

/-- α₁ and β anticommute: {α₁, β} = 0.

This is the key structural relation connecting momentum and mass terms in
H_D = -iℏc(α·∇) + βmc². Because {αᵢ, β} = 0, the square H_D² separates cleanly:

  H_D² = (ℏc)²(α·∇)² + (mc²)²β² = -ℏ²c²∇² + m²c⁴

with no cross terms. This yields the relativistic dispersion E² = p²c² + m²c⁴. -/
lemma diracAlpha1_beta_anticommute : diracAlpha1 * diracBeta + diracBeta * diracAlpha1 = 0 := by
  dirac_compute diracAlpha1, diracBeta

/-- α₂ and β anticommute: {α₂, β} = 0.

Same structural role as `diracAlpha1_beta_anticommute`. The imaginary entries
of α₂ don't affect the cancellation pattern since β is diagonal and real. -/
lemma diracAlpha2_beta_anticommute : diracAlpha2 * diracBeta + diracBeta * diracAlpha2 = 0 := by
  dirac_compute diracAlpha2, diracBeta

/-- α₃ and β anticommute: {α₃, β} = 0.

Completes the set of α-β anticommutation relations. Both matrices have
real entries, so the cancellations are purely ±1 arithmetic. -/
lemma diracAlpha3_beta_anticommute : diracAlpha3 * diracBeta + diracBeta * diracAlpha3 = 0 := by
  dirac_compute diracAlpha3, diracBeta

/-- α₁ is Hermitian: α₁† = α₁.

Hermiticity of all α matrices and β ensures the Dirac Hamiltonian is symmetric:
⟨H_D ψ, φ⟩ = ⟨ψ, H_D φ⟩ on its domain. This is the first step toward proving
essential self-adjointness.

α₁ has only real entries (0 and 1), so conjugate transpose = transpose,
and the matrix is symmetric. -/
lemma diracAlpha1_hermitian : diracAlpha1.conjTranspose = diracAlpha1 := by
  dirac_compute diracAlpha1

/-- α₂ is Hermitian: α₂† = α₂.

Despite having imaginary entries (±I), α₂ is still Hermitian. The key is that
I appears in antisymmetric positions: (α₂)ᵢⱼ = -I implies (α₂)ⱼᵢ = +I.
Transposing swaps positions, conjugating flips signs: I* = -I. The two operations cancel:
(α₂)†ᵢⱼ = conj((α₂)ⱼᵢ) = conj(±I) = ∓I = (α₂)ᵢⱼ. -/
lemma diracAlpha2_hermitian : diracAlpha2.conjTranspose = diracAlpha2 := by
  dirac_compute diracAlpha2

/-- α₃ is Hermitian: α₃† = α₃.

Like α₁, the matrix α₃ has only real entries (0 and ±1). Real symmetric
matrices are Hermitian: transpose is the identity, conjugation does nothing. -/
lemma diracAlpha3_hermitian : diracAlpha3.conjTranspose = diracAlpha3 := by
  dirac_compute diracAlpha3

/-- β is Hermitian: β† = β.

The mass matrix β = diag(1, 1, -1, -1) is diagonal with real entries.
Diagonal matrices are symmetric, and real entries are self-conjugate,
so Hermiticity is immediate. -/
lemma diracBeta_hermitian : diracBeta.conjTranspose = diracBeta := by
  dirac_compute diracBeta

/-- γ⁰ = β: the timelike gamma matrix (Hermitian). -/
def gamma0 : Matrix (Fin 4) (Fin 4) ℂ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]

/-- γ¹ = βα₁: spacelike gamma matrix (anti-Hermitian). -/
def gamma1 : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]

/-- γ² = βα₂: spacelike gamma matrix (anti-Hermitian, contains ±I). -/
def gamma2 : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, -I; 0, 0, I, 0; 0, I, 0, 0; -I, 0, 0, 0]

/-- γ³ = βα₃: spacelike gamma matrix (anti-Hermitian). -/
def gamma3 : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0]


/-- Minkowski-Clifford relation for γ⁰: {γ⁰, γ⁰} = 2η⁰⁰ I = 2I.

The timelike component has η⁰⁰ = +1, so γ⁰ squares to +I.
Written as γ⁰γ⁰ + γ⁰γ⁰ = 2I to match the anticommutator form. -/
 lemma clifford_00 : gamma0 * gamma0 + gamma0 * gamma0 =
    2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  dirac_compute gamma0

/-- Minkowski-Clifford relation: {γ⁰, γ¹} = 2η⁰¹ I = 0.

Off-diagonal Minkowski components vanish (η⁰¹ = 0), so distinct
gamma matrices anticommute. This is the covariant form of {αᵢ, β} = 0. -/
lemma clifford_01 : gamma0 * gamma1 + gamma1 * gamma0 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  dirac_compute gamma0, gamma1

/-- Minkowski-Clifford relation: {γ⁰, γ²} = 0.

Off-diagonal relation with the imaginary-entry matrix γ². The ±I entries
don't affect the anticommutation since γ⁰ is diagonal. -/
lemma clifford_02 : gamma0 * gamma2 + gamma2 * gamma0 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  dirac_compute gamma0, gamma2

/-- Minkowski-Clifford relation: {γ⁰, γ³} = 0.

Both matrices have real entries; cancellation is pure ±1 arithmetic. -/
lemma clifford_03 : gamma0 * gamma3 + gamma3 * gamma0 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  dirac_compute gamma0, gamma3

/-- Minkowski-Clifford relation: {γ¹, γ⁰} = 0.

Same as `clifford_01` with reversed order; anticommutators are symmetric. -/
lemma clifford_10 : gamma1 * gamma0 + gamma0 * gamma1 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) :=
  (add_comm _ _).trans clifford_01

/-- Minkowski-Clifford relation for γ¹: {γ¹, γ¹} = 2η¹¹ I = -2I.

Spacelike components have η¹¹ = -1 (Minkowski signature), so γ¹ squares to -I.
This sign difference from γ⁰ is what makes the metric indefinite. -/
lemma clifford_11 : gamma1 * gamma1 + gamma1 * gamma1 =
    (-2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  dirac_compute gamma1

/-- Minkowski-Clifford relation: {γ¹, γ²} = 0.

Distinct spacelike gamma matrices anticommute (η¹² = 0). This mixes
real entries (γ¹) with imaginary entries (γ²). -/
lemma clifford_12 : gamma1 * gamma2 + gamma2 * gamma1 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  dirac_compute gamma1, gamma2

/-- Minkowski-Clifford relation: {γ¹, γ³} = 0.

Both matrices have real entries; purely ±1 arithmetic. -/
lemma clifford_13 : gamma1 * gamma3 + gamma3 * gamma1 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  dirac_compute gamma1, gamma3

/-- Minkowski-Clifford relation: {γ², γ⁰} = 0.

Same as `clifford_02` with reversed order. -/
lemma clifford_20 : gamma2 * gamma0 + gamma0 * gamma2 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) :=
  (add_comm _ _).trans clifford_02

/-- Minkowski-Clifford relation: {γ², γ¹} = 0.

Same as `clifford_12` with reversed order. -/
lemma clifford_21 : gamma2 * gamma1 + gamma1 * gamma2 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) :=
  (add_comm _ _).trans clifford_12

/-- Minkowski-Clifford relation for γ²: {γ², γ²} = 2η²² I = -2I.

Spacelike signature gives -2I. The proof uses `I_mul_I` to simplify
products of imaginary entries: (±I)(±I) = -1. -/
lemma clifford_22 : gamma2 * gamma2 + gamma2 * gamma2 =
    (-2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  dirac_compute gamma2

/-- Minkowski-Clifford relation: {γ², γ³} = 0.

Mixes imaginary entries (γ²) with real entries (γ³). -/
lemma clifford_23 : gamma2 * gamma3 + gamma3 * gamma2 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  dirac_compute gamma2, gamma3

/-- Minkowski-Clifford relation: {γ³, γ⁰} = 0.

Same as `clifford_03` with reversed order. -/
lemma clifford_30 : gamma3 * gamma0 + gamma0 * gamma3 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) :=
  (add_comm _ _).trans clifford_03

/-- Minkowski-Clifford relation: {γ³, γ¹} = 0.

Same as `clifford_13` with reversed order. -/
lemma clifford_31 : gamma3 * gamma1 + gamma1 * gamma3 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) :=
  (add_comm _ _).trans clifford_13

/-- Minkowski-Clifford relation: {γ³, γ²} = 0.

Same as `clifford_23` with reversed order. -/
lemma clifford_32 : gamma3 * gamma2 + gamma2 * gamma3 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) :=
  (add_comm _ _).trans clifford_23

/-- Minkowski-Clifford relation for γ³: {γ³, γ³} = 2η³³ I = -2I.

Completes the diagonal relations. All three spacelike matrices square to -I,
reflecting the signature (1, -1, -1, -1) of Minkowski space. -/
lemma clifford_33 : gamma3 * gamma3 + gamma3 * gamma3 =
    (-2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  dirac_compute gamma3


/-- Helper: -2 as scalar matrix equals -2 • 1 -/
lemma neg_two_eq_smul :
    (-2 : Matrix (Fin 4) (Fin 4) ℂ) = (-2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [← Algebra.algebraMap_eq_smul_one]
  simp only [map_neg, neg_inj]
  rfl

/-- γ⁰ is Hermitian: (γ⁰)† = γ⁰.

The timelike gamma matrix has real diagonal entries, hence is self-adjoint. -/
lemma gamma0_hermitian_proof : gamma0.conjTranspose = gamma0 := by
  dirac_compute gamma0

/-- γ¹ is anti-Hermitian: (γ¹)† = -γ¹.

Spacelike gamma matrices pick up a sign under adjoint. This is connected to
the −1 in the Minkowski metric η¹¹ = −1. -/
lemma gamma1_antihermitian : gamma1.conjTranspose = -gamma1 := by
  dirac_compute gamma1

/-- γ² is anti-Hermitian: (γ²)† = -γ².

Despite having imaginary entries, the anti-Hermiticity comes from the spatial
structure, not the presence of I. -/
lemma gamma2_antihermitian : gamma2.conjTranspose = -gamma2 := by
  dirac_compute gamma2

/-- γ³ is anti-Hermitian: (γ³)† = -γ³. -/
lemma gamma3_antihermitian : gamma3.conjTranspose = -gamma3 := by
  dirac_compute gamma3

end Spectra.QuantumMechanics.Dirac
