/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ported from Isabelle/HOL formalization by Echenim & Mhalla, by Adam Bornemann
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Spectra.QuantumMechanics.PauliMatrices
/-!
# Bell's Theorem and the CHSH Inequality in Lean 4

This file formalizes Bell's lemma, the CHSH inequality, and its quantum-mechanical violation.
The formalization follows the structure of Echenim & Mhalla's Isabelle/HOL work,
adapted to leverage Lean 4's type system and Mathlib4's existing infrastructure.

## Main definitions

* `DensityMatrix` : a positive semidefinite Hermitian matrix with trace 1
* `LocalHiddenVariableModel` : a classical (local hidden variable) model of a CHSH experiment

The Hermitian/involutive/commuting conditions on a CHSH observable tuple are mathlib's
`IsCHSHTuple` (`Mathlib.Algebra.Star.CHSH`), used directly rather than redeclared here.

## Main results

* `CHSH_lhv_bound` : under any local hidden variable model, `|S| ≤ 2`
* `CHSH_quantum_violation` : the Bell state with optimal measurements achieves `|S| = 2√2`

## References

* [Echenim, Mhalla, *A formalization of the CHSH inequality and Tsirelson's
  upper-bound in Isabelle/HOL*][echenim2023]
* [Clauser, Horne, Shimony, Holt, *Proposed experiment to test local
  hidden-variable theories*][chsh1969]
* [Bell, *On the Einstein Podolsky Rosen paradox*][bell1964]

## Tags

bell's theorem, chsh, local hidden variables, density matrix, quantum information
-/
open MeasureTheory ProbabilityTheory Matrix Complex

/-! ## Quantum State Foundations -/

namespace Spectra.QuantumInfo

variable {n : ℕ} [NeZero n]

/-- A complex matrix is positive semidefinite if `x†Mx` has non-negative real part for all `x`.
    For Hermitian matrices, `x†Mx` is automatically real.

Implementation notes: this is deliberately weaker than mathlib's `Matrix.PosSemidef`, which
additionally bundles `M.IsHermitian`. The CHSH/Tsirelson development below repeatedly builds
positivity witnesses for expressions such as `4 • 1 - ⟦A₀, A₁⟧ * ⟦B₀, B₁⟧` before their
Hermitian-ness has been separately established, so carrying the conjunct through every
intermediate step would add proof burden without changing the final bounds. Callers that need
the mathlib-standard notion can bridge via
`Spectra.QuantumInfo.isPosSemidefComplex_iff_posSemidef` in `CHSH_Bounds/CHSH_Basic.lean`, which
shows the two predicates agree on Hermitian matrices. -/
def IsPosSemidefComplex (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ x : Fin n → ℂ, 0 ≤ (star x ⬝ᵥ M.mulVec x).re

/-- A density matrix is a positive semidefinite Hermitian matrix with trace 1.
    This represents the state of a quantum system. -/
structure DensityMatrix (n : ℕ) [NeZero n] where
  /-- The underlying matrix -/
  toMatrix : Matrix (Fin n) (Fin n) ℂ
  /-- Density matrices are Hermitian -/
  hermitian : toMatrix.IsHermitian
  /-- Density matrices have trace 1 -/
  trace_one : toMatrix.trace = 1
  /-- Density matrices are positive semidefinite -/
  pos_semidef : IsPosSemidefComplex toMatrix

/-- A density matrix coerces to its underlying matrix. -/
instance : Coe (DensityMatrix n) (Matrix (Fin n) (Fin n) ℂ) where
  coe ρ := ρ.toMatrix

/-! ## CHSH Operator and Conditions -/

/-- The CHSH operator `S = A₀B₁ - A₀B₀ + A₁B₀ + A₁B₁`, in the algebraic form where `Aᵢ` and `Bⱼ`
already live in the same operator algebra and commute (e.g. as `Aᵢ ⊗ 1` and `1 ⊗ Bⱼ` on a joint
Hilbert space, once lifted via `kroneckerMap` as at call sites below): what physicists write as
`Aᵢ ⊗ Bⱼ` on the joint space becomes ordinary multiplication `Aᵢ * Bⱼ` here, since `chshOp` itself
is stated generically over any shared algebra `Matrix ι ι ℂ`, not over a tensor-product type. -/
noncomputable def chshOp {ι : Type*} [Fintype ι]
    (A₀ A₁ B₀ B₁ : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  A₀ * B₁ - A₀ * B₀ + A₁ * B₀ + A₁ * B₁

/-- CHSH expectation value for a density matrix -/
noncomputable def chshExpect {ι : Type*} [Fintype ι]
    (A₀ A₁ B₀ B₁ : Matrix ι ι ℂ) (ρ : Matrix ι ι ℂ) : ℂ :=
  (chshOp A₀ A₁ B₀ B₁ * ρ).trace

/- `IsCHSHTuple` (Hermitian/involutive/commuting conditions on a CHSH observable tuple) is not
redeclared here: mathlib's `IsCHSHTuple` (`Mathlib.Algebra.Star.CHSH`, imported above) already
states exactly this for any `[Monoid R] [StarMul R]`, at the standard shape `A₀ ^ 2 = 1`/
`star A₀ = A₀` rather than `A₀ * A₀ = 1`/`A₀.IsHermitian` — defeq-equivalent for
`Matrix (Fin n) (Fin n) ℂ` (whose `Star` instance *is* `conjTranspose`) and strictly more general,
so callers below use it directly instead of a local, non-standard copy. -/

/-! ## Local Hidden Variable Model -/

/-- A local hidden variable (LHV) model for a bipartite quantum experiment.

Given a bipartite state ρ and observables A, B, the LHV hypothesis asserts
the existence of:
- A probability space (Λ, μ)
- Random variables Xₐ for each eigenvalue a of A
- Random variables Yᵦ for each eigenvalue b of B

Such that the quantum correlations arise as classical expectations:
  `Tr(Πᵃ ⊗ Πᵇ · ρ) = 𝔼[Xₐ · Yᵦ]`

The key constraint is *locality*: Xₐ depends only on A (not B),
and Yᵦ depends only on B (not A).
-/
structure LocalHiddenVariableModel (Λ : Type*) [MeasurableSpace Λ] where
  /-- The probability measure on the hidden variable space -/
  μ : ProbabilityMeasure Λ
  /-- Response function for Alice: given setting a and hidden variable ω, output ±1 -/
  alice : Fin 2 → Λ → ℝ  -- settings 0, 1
  /-- Response function for Bob: given setting b and hidden variable ω, output ±1 -/
  bob : Fin 2 → Λ → ℝ    -- settings 0, 1
  /-- Alice's outputs are ±1 a.e. -/
  alice_pm1 : ∀ a, ∀ᵐ ω ∂(μ : Measure Λ), alice a ω = 1 ∨ alice a ω = -1
  /-- Bob's outputs are ±1 a.e. -/
  bob_pm1 : ∀ b, ∀ᵐ ω ∂(μ : Measure Λ), bob b ω = 1 ∨ bob b ω = -1
  /-- Measurability -/
  alice_meas : ∀ a, Measurable (alice a)
  bob_meas : ∀ b, Measurable (bob b)

variable {Λ : Type*} [MeasurableSpace Λ]

/-- The LHV correlation for settings (a, b) -/
noncomputable def lhvCorrelation (M : LocalHiddenVariableModel Λ) (a b : Fin 2) : ℝ :=
  ∫ ω, M.alice a ω * M.bob b ω ∂M.μ

/-- The CHSH value under an LHV model:
    `S = E(0,1) - E(0,0) + E(1,0) + E(1,1)`. -/
noncomputable def lhvCHSHValue (M : LocalHiddenVariableModel Λ) : ℝ :=
  lhvCorrelation M 0 1 - lhvCorrelation M 0 0 +
  lhvCorrelation M 1 0 + lhvCorrelation M 1 1

/-! ## The CHSH Inequality for LHV Models -/

/-- Key algebraic identity: for `a, a', b, b' ∈ {-1, 1}`,
    `|ab' - ab + a'b + a'b'| ≤ 2`. -/
lemma chsh_algebraic_bound (a a' b b' : ℝ)
    (ha : a = 1 ∨ a = -1) (ha' : a' = 1 ∨ a' = -1)
    (hb : b = 1 ∨ b = -1) (hb' : b' = 1 ∨ b' = -1) :
    |a * b' - a * b + a' * b + a' * b'| ≤ 2 := by
  -- The key insight: a*b' - a*b + a'*b + a'*b' = a*(b'-b) + a'*(b+b')
  -- Since b, b' ∈ {-1,1}, either b'=b (so b'-b=0, b+b'=±2)
  -- or b'=-b (so b'-b=±2, b+b'=0)
  -- In either case, one term vanishes and the other is ±2
  rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl <;>
  rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl <;>
  norm_num

/-- **CHSH Inequality**: Under any local hidden variable model, `|S| ≤ 2`.

This is the fundamental constraint that Bell showed is violated by quantum mechanics. -/
theorem CHSH_lhv_bound (M : LocalHiddenVariableModel Λ) :
    |lhvCHSHValue M| ≤ 2 := by
  unfold lhvCHSHValue lhvCorrelation
  have h_int : ∀ a b, Integrable (fun ω => M.alice a ω * M.bob b ω) (M.μ : Measure Λ) := by
    intro a b
    apply Integrable.mono' (g := fun _ => (1 : ℝ)) (integrable_const 1)
    · exact ((M.alice_meas a).mul (M.bob_meas b)).aestronglyMeasurable
    · filter_upwards [M.alice_pm1 a, M.bob_pm1 b] with ω ha hb
      simp only [norm_mul, Real.norm_eq_abs]
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] <;> norm_num
  rw [← integral_sub, ← integral_add, ← integral_add]
  · -- Main bound
    have hμ : IsProbabilityMeasure (M.μ : Measure Λ) :=
      ProbabilityMeasure.instIsProbabilityMeasureToMeasure M.μ
    calc |∫ ω, M.alice 0 ω * M.bob 1 ω - M.alice 0 ω * M.bob 0 ω +
              M.alice 1 ω * M.bob 0 ω + M.alice 1 ω * M.bob 1 ω ∂(M.μ : Measure Λ)|
        ≤ ∫ ω, |M.alice 0 ω * M.bob 1 ω - M.alice 0 ω * M.bob 0 ω +
               M.alice 1 ω * M.bob 0 ω + M.alice 1 ω * M.bob 1 ω| ∂(M.μ : Measure Λ) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _, (2 : ℝ) ∂(M.μ : Measure Λ) := by
          apply integral_mono_ae
          · exact (((h_int 0 1).sub (h_int 0 0)).add (h_int 1 0)).add (h_int 1 1) |>.abs
          · exact integrable_const 2
          · filter_upwards [M.alice_pm1 0, M.alice_pm1 1, M.bob_pm1 0, M.bob_pm1 1]
              with ω ha ha' hb hb'
            exact chsh_algebraic_bound _ _ _ _ ha ha' hb hb'
      _ = 2 := by
          rw [integral_const]
          simp only [MeasureTheory.probReal_univ, smul_eq_mul, one_mul]
  -- Integrability side goals for integral_add/sub
  · exact ((h_int 0 1).sub (h_int 0 0)).add (h_int 1 0)
  · exact h_int 1 1
  · exact (h_int 0 1).sub (h_int 0 0)
  · exact h_int 1 0
  · exact h_int 0 1
  · exact h_int 0 0

/-! ## Quantum Violation -/

/-- The Pauli-Z matrix, re-exported for the Bell/CHSH namespace. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  Spectra.QuantumMechanics.Pauli.pauliZ

/-- The Pauli-X matrix, re-exported for the Bell/CHSH namespace. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  Spectra.QuantumMechanics.Pauli.pauliX

/-- The Bell state `|Ψ⁻⟩ = (1/√2)(|01⟩ - |10⟩)` as a density matrix
    on the product space `Fin 2 × Fin 2`. -/
noncomputable def bellStatePsiMinus : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun i j =>
    match i, j with
    | (0, 1), (0, 1) =>  (1/2 : ℂ)
    | (0, 1), (1, 0) => -(1/2 : ℂ)
    | (1, 0), (0, 1) => -(1/2 : ℂ)
    | (1, 0), (1, 0) =>  (1/2 : ℂ)
    | _, _ => 0

/-- Alice's `A₀` observable for optimal CHSH violation: `A₀ = Z`. -/
def aliceA₀ : Matrix (Fin 2) (Fin 2) ℂ := pauliZ

/-- Alice's `A₁` observable for optimal CHSH violation: `A₁ = X`. -/
def aliceA₁ : Matrix (Fin 2) (Fin 2) ℂ := pauliX

/-- Bob's `B₀` observable for optimal CHSH violation: `B₀ = (Z - X)/√2`.

Implementation notes: `noncomputable`, unlike `aliceA₀`/`aliceA₁`, because it scales by
`Real.sqrt 2`, whose inverse is not computable in Lean (Alice's observables have only rational
entries). -/
noncomputable def bobB₀ : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / Complex.ofReal (Real.sqrt 2)) • (pauliZ - pauliX)

/-- Bob's `B₁` observable for optimal CHSH violation: `B₁ = -(Z + X)/√2`. -/
noncomputable def bobB₁ : Matrix (Fin 2) (Fin 2) ℂ :=
  (-1 / Complex.ofReal (Real.sqrt 2)) • (pauliZ + pauliX)

/-- Shared trace formula behind all four `correlation_A*_B*` lemmas below: for any single-qubit
`a`, `b` lifted to the two-qubit space by `kroneckerMap`, the Bell-state expectation
`⟨Ψ⁻|(a ⊗ 1)(1 ⊗ b)|Ψ⁻⟩` reduces to a fixed linear combination of the four entries of `a` and of
`b`. Each `correlation_A*_B*` lemma is this formula plus the numeric entries of its specific
observables. -/
lemma bellStatePsiMinus_kroneckerMap_trace (a b : Matrix (Fin 2) (Fin 2) ℂ) :
    ((kroneckerMap (· * ·) a (1 : Matrix (Fin 2) (Fin 2) ℂ) *
        kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ) b) * bellStatePsiMinus).trace =
      (1 / 2 : ℂ) * (a 0 0 * b 1 1 - a 1 0 * b 0 1 - a 0 1 * b 1 0 + a 1 1 * b 0 0) := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.isValue]
  simp only [Matrix.mul_apply, bellStatePsiMinus, Matrix.of_apply]
  simp only [Fin.isValue, mul_zero, Finset.sum_const_zero, one_div, zero_add, add_zero]
  simp only [kroneckerMap_apply, Matrix.one_apply]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.isValue]
  simp only [Fin.isValue, one_ne_zero, zero_ne_one, ↓reduceIte, mul_one, mul_zero, one_mul,
    zero_mul, add_zero, zero_add]
  ring

/-- Correlation `E(A₀, B₁)` for the Bell state. -/
lemma correlation_A₀_B₁ :
    let A₀ := kroneckerMap (· * ·) aliceA₀ (1 : Matrix (Fin 2) (Fin 2) ℂ)
    let B₁ := kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ) bobB₁
    ((A₀ * B₁) * bellStatePsiMinus).trace = ((Real.sqrt 2)⁻¹ : ℂ) := by
  intro A₀ B₁
  simp only [A₀, B₁, bellStatePsiMinus_kroneckerMap_trace]
  simp only [aliceA₀, bobB₁, pauliZ, pauliX, Spectra.QuantumMechanics.Pauli.pauliZ,
    Spectra.QuantumMechanics.Pauli.pauliX, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring_nf

/-- Correlation `E(A₀, B₀)` for the Bell state. -/
lemma correlation_A₀_B₀ :
    let A₀ := kroneckerMap (· * ·) aliceA₀ (1 : Matrix (Fin 2) (Fin 2) ℂ)
    let B₀ := kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ) bobB₀
    ((A₀ * B₀) * bellStatePsiMinus).trace = -((Real.sqrt 2)⁻¹ : ℂ) := by
  intro A₀ B₀
  simp only [A₀, B₀, bellStatePsiMinus_kroneckerMap_trace]
  simp only [aliceA₀, bobB₀, pauliZ, pauliX, Spectra.QuantumMechanics.Pauli.pauliZ,
    Spectra.QuantumMechanics.Pauli.pauliX, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring_nf

/-- Correlation `E(A₁, B₀)` for the Bell state. -/
lemma correlation_A₁_B₀ :
    let A₁ := kroneckerMap (· * ·) aliceA₁ (1 : Matrix (Fin 2) (Fin 2) ℂ)
    let B₀ := kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ) bobB₀
    ((A₁ * B₀) * bellStatePsiMinus).trace = ((Real.sqrt 2)⁻¹ : ℂ) := by
  intro A₁ B₀
  simp only [A₁, B₀, bellStatePsiMinus_kroneckerMap_trace]
  simp only [aliceA₁, bobB₀, pauliZ, pauliX, Spectra.QuantumMechanics.Pauli.pauliZ,
    Spectra.QuantumMechanics.Pauli.pauliX, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring_nf

/-- Correlation `E(A₁, B₁)` for the Bell state. -/
lemma correlation_A₁_B₁ :
    let A₁ := kroneckerMap (· * ·) aliceA₁ (1 : Matrix (Fin 2) (Fin 2) ℂ)
    let B₁ := kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ) bobB₁
    ((A₁ * B₁) * bellStatePsiMinus).trace = ((Real.sqrt 2)⁻¹ : ℂ) := by
  intro A₁ B₁
  simp only [A₁, B₁, bellStatePsiMinus_kroneckerMap_trace]
  simp only [aliceA₁, bobB₁, pauliZ, pauliX, Spectra.QuantumMechanics.Pauli.pauliZ,
    Spectra.QuantumMechanics.Pauli.pauliX, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring_nf

/-! ## The CHSH Value for the Bell State -/

/-- **Quantum Violation**: The Bell state with optimal measurements achieves `|S| = 2√2`. -/
theorem CHSH_quantum_violation :
    let A₀ := kroneckerMap (· * ·) aliceA₀ (1 : Matrix (Fin 2) (Fin 2) ℂ)
    let A₁ := kroneckerMap (· * ·) aliceA₁ (1 : Matrix (Fin 2) (Fin 2) ℂ)
    let B₀ := kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ) bobB₀
    let B₁ := kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ) bobB₁
    ‖chshExpect A₀ A₁ B₀ B₁ bellStatePsiMinus‖ = 2 * Real.sqrt 2 := by
  intro A₀ A₁ B₀ B₁
  simp only [chshExpect, chshOp]
  rw [add_mul, add_mul, sub_mul]
  rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_sub]
  rw [correlation_A₀_B₁, correlation_A₀_B₀, correlation_A₁_B₀, correlation_A₁_B₁]
  simp only [sub_neg_eq_add]
  ring_nf
  simp only [Complex.norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, norm_ofNat]
  rw [abs_of_pos (Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0))]
  field_simp
  simp only [Nat.ofNat_nonneg, Real.sq_sqrt]
  ring

end Spectra.QuantumInfo
