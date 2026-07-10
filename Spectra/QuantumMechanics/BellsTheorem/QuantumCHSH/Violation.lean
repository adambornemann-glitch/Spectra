/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ported from Isabelle/HOL formalization by Echenim & Mhalla, by Adam Bornemann
-/
import Spectra.QuantumMechanics.BellsTheorem.QuantumCHSH.Correlations
/-!
# Quantum CHSH Violation for the Bell State

Assembles the CHSH observables and correlators from `Q_CHSH_Basic.lean`/`Correlations.lean` into
the CHSH value for the singlet state, and ties its Tsirelson-bound violation to the classical
(LHV) bound — Bell's theorem's headline consequence, in the naming convention of Echenim &
Mhalla's Isabelle/HOL formalization.

## Main definitions

* `chshQuantum`, `chshValue` : the CHSH operator and its expectation value for the singlet state,
  re-exported from `Spectra.QuantumInfo.chshOp`/`chshExpect` (`BellsTheorem/Basic.lean`)

## Main results

* `quantum_chsh_value` : `chshValue = 2√2`, the raw complex CHSH value
* `chshValue_norm` : `‖chshValue‖ = 2√2`, reusing `Spectra.QuantumInfo.CHSH_quantum_violation`
* `quantum_exceeds_lhv` : `‖chshValue‖ > 2`, exceeding the classical ceiling of
  `Spectra.QuantumInfo.CHSH_lhv_bound`

## Implementation notes

`chshQuantum`/`chshValue` are re-exports of `Spectra.QuantumInfo.chshOp`/`chshExpect` applied to
this port chain's own observables (`A₀`, `A₁`, `B₀`, `B₁`, `ρΨMinus` from `Correlations.lean`/
`Q_CHSH_Basic.lean`), rather than independent re-derivations of the same CHSH operator and
expectation value.

## References

* [Echenim, Mhalla, *A formalization of the CHSH inequality and Tsirelson's
  upper-bound in Isabelle/HOL*][echenim2023]

## Tags

chsh, bell state, tsirelson bound, quantum information
-/
open Matrix
namespace Spectra.QuantumCHSH

/-! ## The CHSH Value for the Bell State -/

/-- The CHSH operator for quantum observables, re-exported from `Spectra.QuantumInfo.chshOp`. -/
noncomputable def chshQuantum : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Spectra.QuantumInfo.chshOp A₀ A₁ B₀ B₁

/-- The CHSH expectation value, re-exported from `Spectra.QuantumInfo.chshExpect`. -/
noncomputable def chshValue : ℂ :=
  Spectra.QuantumInfo.chshExpect A₀ A₁ B₀ B₁ ρΨMinus

/-- **Quantum CHSH Violation**: The Bell state achieves S = 2√2.

This is the maximum quantum violation, known as the Tsirelson bound. -/
lemma quantum_chsh_value : chshValue = 2 * Real.sqrt 2 := by
  unfold chshValue Spectra.QuantumInfo.chshExpect Spectra.QuantumInfo.chshOp
  calc ((A₀ * B₁ - A₀ * B₀ + A₁ * B₀ + A₁ * B₁) * ρΨMinus).trace
      = (A₀ * B₁ * ρΨMinus).trace - (A₀ * B₀ * ρΨMinus).trace +
        (A₁ * B₀ * ρΨMinus).trace + (A₁ * B₁ * ρΨMinus).trace := by
          simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.trace_sub, Matrix.trace_add]
      _ = correlation A₀ B₁ ρΨMinus - correlation A₀ B₀ ρΨMinus +
          correlation A₁ B₀ ρΨMinus + correlation A₁ B₁ ρΨMinus := by
          unfold correlation expectation
          simp only [mul_assoc]
      _ = 1/Real.sqrt 2 - (-1/Real.sqrt 2) + 1/Real.sqrt 2 + 1/Real.sqrt 2 := by
          rw [E_A₀_B₁, E_A₀_B₀, E_A₁_B₀, E_A₁_B₁]
      _ = 4/Real.sqrt 2 := by ring
      _ = 2 * Real.sqrt 2 := by
          have sqrt2_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
            simp [Real.sqrt_ne_zero'.mpr (by norm_num : (2:ℝ) > 0)]
          have hsq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
            rw [sq, ← Complex.ofReal_mul]; norm_num
          field_simp
          linear_combination (-2 : ℂ) * hsq

/-- `chshValue`'s norm, reusing `Spectra.QuantumInfo.CHSH_quantum_violation` directly since
`chshQuantum`/`chshValue`/`ρΨMinus` are all re-exports of that theorem's own terms. -/
lemma chshValue_norm : ‖chshValue‖ = 2 * Real.sqrt 2 :=
  Spectra.QuantumInfo.CHSH_quantum_violation

/-- The quantum CHSH value exceeds the classical (LHV) bound of 2 — Bell's theorem's headline
consequence for the singlet state, tied to `Spectra.QuantumInfo.CHSH_lhv_bound`'s ceiling. -/
lemma quantum_exceeds_lhv : ‖chshValue‖ > 2 := by
  rw [chshValue_norm]
  linarith [Real.one_lt_sqrt_two]

end Spectra.QuantumCHSH
