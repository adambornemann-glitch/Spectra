/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ported from Isabelle/HOL formalization by Echenim & Mhalla, by Adam Bornemann
-/
import Spectra.QuantumMechanics.BellsTheorem.QuantumCHSH.Q_CHSH_Basic
import Spectra.QuantumMechanics.BellsTheorem.Basic
/-!
# CHSH Correlations for the Bell State

The four singlet-state correlators `E(Aᵢ, Bⱼ) = Tr(Aᵢ Bⱼ ρ)` for Alice's/Bob's CHSH observables
`A₀`, `A₁`, `B₀`, `B₁` (declared below, built from the Pauli matrices in `Q_CHSH_Basic.lean`).
`A₀`, `A₁`, `B₀`, `B₁`, `ρΨMinus` here are *definitionally* equal to
`Spectra.QuantumInfo.aliceA₀ ⊗ 1`, `aliceA₁ ⊗ 1`, `1 ⊗ bobB₀`, `1 ⊗ bobB₁`, and
`bellStatePsiMinus` (`BellsTheorem/Basic.lean`), so each correlator is proved by reusing that
file's `correlation_A*_B*` computation rather than re-deriving the same trace from scratch.

## Main definitions

* `expectation`, `correlation` : the trace functionals `Tr(Oρ)`, `Tr(ABρ)`

## Main results

* `E_A₀_B₀`, `E_A₀_B₁`, `E_A₁_B₀`, `E_A₁_B₁` : the four CHSH correlators for the singlet state

## Implementation notes

`A₀`/`A₁` are plain `def`s (no irrational scalar involved), while `B₀`/`B₁` are
`noncomputable def` because they carry a `Real.sqrt 2` scalar.

## References

* [Echenim, Mhalla, *A formalization of the CHSH inequality and Tsirelson's
  upper-bound in Isabelle/HOL*][echenim2023]
-/
open Matrix Complex
namespace Spectra.QuantumCHSH

/-! ## Alice's and Bob's Observables -/

/-- Alice's first observable: A₀ = σZ ⊗ I -/
def A₀ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  kroneckerMap (· * ·) σZ I₂

/-- Alice's second observable: A₁ = σₓ ⊗ I -/
def A₁ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  kroneckerMap (· * ·) σₓ I₂

/-- Bob's first observable: B₀ = I ⊗ (σZ - σₓ)/√2 -/
noncomputable def B₀ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  kroneckerMap (· * ·) I₂ ((1/Real.sqrt 2 : ℂ) • (σZ - σₓ))

/-- Bob's second observable: B₁ = I ⊗ -(σZ + σₓ)/√2 -/
noncomputable def B₁ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  kroneckerMap (· * ·) I₂ ((-1/Real.sqrt 2 : ℂ) • (σZ + σₓ))

/-! ## Expectation Values -/

/-- Expectation value ⟨O⟩ = Tr(O · ρ) -/
noncomputable def expectation (O ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℂ :=
  (O * ρ).trace

/-- The correlation E(A, B) = ⟨AB⟩ = Tr(AB · ρ) for observables A, B on state ρ -/
noncomputable def correlation (A B ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℂ :=
  expectation (A * B) ρ

/-! ## Computing the Correlations

`correlation A B ρΨMinus` unfolds (definitionally) to exactly the trace
`Spectra.QuantumInfo.correlation_A*_B*` already computes (`BellsTheorem/Basic.lean`), so each
correlator is that lemma composed with `ring` for the `-1/√2` vs. `-(√2)⁻¹` notational mismatch. -/

/-- E(A₀, B₀) = -1/√2 for the Bell state -/
lemma E_A₀_B₀ : correlation A₀ B₀ ρΨMinus = -1 / Real.sqrt 2 :=
  Spectra.QuantumInfo.correlation_A₀_B₀.trans (by ring)

/-- E(A₀, B₁) = 1/√2 for the Bell state -/
lemma E_A₀_B₁ : correlation A₀ B₁ ρΨMinus = 1 / Real.sqrt 2 :=
  Spectra.QuantumInfo.correlation_A₀_B₁.trans (by ring)

/-- E(A₁, B₀) = 1/√2 for the Bell state -/
lemma E_A₁_B₀ : correlation A₁ B₀ ρΨMinus = 1 / Real.sqrt 2 :=
  Spectra.QuantumInfo.correlation_A₁_B₀.trans (by ring)

/-- E(A₁, B₁) = 1/√2 for the Bell state -/
lemma E_A₁_B₁ : correlation A₁ B₁ ρΨMinus = 1 / Real.sqrt 2 :=
  Spectra.QuantumInfo.correlation_A₁_B₁.trans (by ring)

end Spectra.QuantumCHSH
