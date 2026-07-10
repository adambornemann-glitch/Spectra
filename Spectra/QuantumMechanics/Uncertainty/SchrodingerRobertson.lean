/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.SelfAdjoint
/-!
# The Schrödinger (and Robertson) Uncertainty Relations

This module proves the Schrödinger uncertainty inequality — the strengthened
form of Heisenberg's uncertainty principle, including the covariance term — and
derives Robertson's inequality as a corollary by discarding that term.

This is the *consolidated, Schrödinger-first* development. The strengthened
inequality is the foundational lemma; Robertson's bound (and the
standard-deviation forms) follow from it. It supersedes the earlier separate
`Robertson.lean` / `Schrodinger.lean` pair.

## Main definitions

* `covariance`: Cov(A,B)_ψ = ½⟨{A,B}⟩_ψ - ⟨A⟩_ψ⟨B⟩_ψ

## Main results

* `schrodinger_uncertainty` (**primary**): variance form,
  $$\sigma_A^2 \sigma_B^2 \geq \tfrac14|\langle[A,B]\rangle|^2 + \mathrm{Cov}(A,B)^2$$
* `schrodinger_stddev`: standard-deviation form
* `robertson_uncertainty`: Robertson's variance bound, a corollary (drop covariance)
* `robertson_stddev`: Robertson's standard-deviation bound
* `observable_schrodinger_uncertainty`, `observable_robertson_uncertainty`,
  `observable_schrodinger_stddev`, `observable_robertson_stddev`: the same bounds
  (variance and standard-deviation forms) stated for `SelfAdjointOperator`s


## Generality note

The inequalities hold for *symmetric* operators — they never use the domain
equality `Dom(A) = Dom(A†)` that distinguishes self-adjointness. They are
therefore proved at `SymmetricOperator` generality, and specialized to genuine
self-adjoint observables (`SelfAdjointOperator`) via `toSymmetricOperator` in the
`observable_*` corollaries.

## References

* [Schrödinger, "Zum Heisenbergschen Unschärfeprinzip"][schrodinger1930]
* [Robertson, "The uncertainty principle"][robertson1929]

## Tags

uncertainty principle, Schrödinger inequality, Robertson inequality, covariance
-/
open Spectra.Operator SymmetricOperator
open InnerProductSpace
open scoped ComplexConjugate
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.QuantumMechanics.Schrodinger

/-! ### Real/complex helper lemmas -/

/-- `‖z‖² = z.im²` when `z.re = 0`. -/
lemma normSq_of_re_zero {z : ℂ} (h : z.re = 0) : Complex.normSq z = z.im^2 := by
  rw [Complex.normSq_apply, h]
  ring

/-- `‖z‖² = z.re² + z.im²`. -/
lemma normSq_eq_re_sq_add_im_sq (z : ℂ) : Complex.normSq z = z.re^2 + z.im^2 := by
  rw [Complex.normSq_apply]
  ring

/-- Move the shifted operator `Ã := A - ⟨A⟩` across the inner product, using that `Ã` is
symmetric: `⟪Ãψ, B̃ψ⟫ = ⟪ψ, Ã(B̃ψ)⟫`. The `A`-side of the shifted-symmetry rewrite shared by
the real- and imaginary-part identities below. -/
lemma inner_A'ψ_B'ψ_eq (A B : SymmetricOperator H) (ψ : H) (h : ShiftedDomainConditions A B ψ) :
    ⟪h.A'ψ, h.B'ψ⟫_ℂ = ⟪ψ, A.shiftedApply ψ h.B'ψ h.h_norm h.hψ_A h.B'ψ_in_A_domain⟫_ℂ :=
  A.shifted_symmetric ψ h.h_norm h.hψ_A h.hψ_A h.B'ψ_in_A_domain

/-- Move the shifted operator `B̃ := B - ⟨B⟩` across the inner product, using that `B̃` is
symmetric: `⟪B̃ψ, Ãψ⟫ = ⟪ψ, B̃(Ãψ)⟫`. The `B`-side mirror of `inner_A'ψ_B'ψ_eq`. -/
lemma inner_B'ψ_A'ψ_eq (A B : SymmetricOperator H) (ψ : H) (h : ShiftedDomainConditions A B ψ) :
    ⟪h.B'ψ, h.A'ψ⟫_ℂ = ⟪ψ, B.shiftedApply ψ h.A'ψ h.h_norm h.hψ_B h.A'ψ_in_B_domain⟫_ℂ :=
  B.shifted_symmetric ψ h.h_norm h.hψ_B h.hψ_B h.A'ψ_in_B_domain

/-! ### The imaginary part identity -/

/-- The key identity: `Im⟨Ãψ, B̃ψ⟩ = ½ Im⟨ψ, [A,B]ψ⟩`. -/
lemma im_inner_shifted_eq_half_commutator (A B : SymmetricOperator H) (ψ : H)
    (h : ShiftedDomainConditions A B ψ) :
    (⟪h.A'ψ, h.B'ψ⟫_ℂ).im =
    (1/2) * (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).im := by
  have h_im_formula : (⟪h.A'ψ, h.B'ψ⟫_ℂ).im = (⟪h.A'ψ, h.B'ψ⟫_ℂ - ⟪h.B'ψ, h.A'ψ⟫_ℂ).im / 2 := by
    rw [← inner_conj_symm h.B'ψ h.A'ψ]
    simp only [Complex.sub_im, Complex.conj_im]
    ring
  rw [h_im_formula, inner_A'ψ_B'ψ_eq A B ψ h, inner_B'ψ_A'ψ_eq A B ψ h]
  have h_expand : A.shiftedApply ψ h.B'ψ h.h_norm h.hψ_A h.B'ψ_in_A_domain -
                  B.shiftedApply ψ h.A'ψ h.h_norm h.hψ_B h.A'ψ_in_B_domain =
                  commutatorAt A B ψ h.toDomainConditions := by
    unfold ShiftedDomainConditions.A'ψ ShiftedDomainConditions.B'ψ
    unfold commutatorAt DomainConditions.ABψ DomainConditions.BAψ
    simp only [shiftedApply]
    rw [A.apply_sub h.hBψ_A (A.domain.smul_mem _ h.hψ_A)]
    rw [A.apply_smul _ h.hψ_A]
    rw [B.apply_sub h.hAψ_B (B.domain.smul_mem _ h.hψ_B)]
    rw [B.apply_smul _ h.hψ_B]
    match_scalars <;> ring_nf
  unfold commutatorAt DomainConditions.ABψ DomainConditions.BAψ
  simp only [inner_sub_right]
  ring_nf
  have h_key : ⟪ψ, A.shiftedApply ψ h.B'ψ h.h_norm h.hψ_A h.B'ψ_in_A_domain⟫_ℂ -
               ⟪ψ, B.shiftedApply ψ h.A'ψ h.h_norm h.hψ_B h.A'ψ_in_B_domain⟫_ℂ =
               ⟪ψ, h.ABψ⟫_ℂ - ⟪ψ, h.BAψ⟫_ℂ := by
    rw [← inner_sub_right, ← inner_sub_right, h_expand]
    exact rfl
  rw [h_key]
  exact rfl

/-! ### Covariance and the real part identity -/

/-- The covariance `Cov(A,B)_ψ = ½⟨{A,B}⟩ - ⟨A⟩⟨B⟩`. -/
noncomputable def covariance (A B : SymmetricOperator H) (ψ : H)
    (h : ShiftedDomainConditions A B ψ) : ℝ :=
  (1/2) * (⟪ψ, anticommutatorAt A B ψ h.toDomainConditions⟫_ℂ).re -
  A.expectation ψ h.h_norm h.hψ_A * B.expectation ψ h.h_norm h.hψ_B

/-- The real part of `⟨Ãψ, B̃ψ⟩` equals the covariance. -/
lemma re_inner_shifted_eq_covariance (A B : SymmetricOperator H) (ψ : H)
    (h : ShiftedDomainConditions A B ψ) :
    (⟪h.A'ψ, h.B'ψ⟫_ℂ).re = covariance A B ψ h := by
  set μ_A := A.expectation ψ h.h_norm h.hψ_A
  set μ_B := B.expectation ψ h.h_norm h.hψ_B
  have h_norm_sq : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, h.h_norm]; simp
  have h_re_formula : (⟪h.A'ψ, h.B'ψ⟫_ℂ).re = (⟪h.A'ψ, h.B'ψ⟫_ℂ + ⟪h.B'ψ, h.A'ψ⟫_ℂ).re / 2 := by
    rw [← inner_conj_symm h.B'ψ h.A'ψ]
    simp only [Complex.add_re, Complex.conj_re]
    ring
  rw [h_re_formula, inner_A'ψ_B'ψ_eq A B ψ h, inner_B'ψ_A'ψ_eq A B ψ h]
  have h_expand_sum : A.shiftedApply ψ h.B'ψ h.h_norm h.hψ_A h.B'ψ_in_A_domain +
                      B.shiftedApply ψ h.A'ψ h.h_norm h.hψ_B h.A'ψ_in_B_domain =
                      anticommutatorAt A B ψ h.toDomainConditions -
                      (2 * μ_B : ℂ) • h.Aψ - (2 * μ_A : ℂ) • h.Bψ +
                      (2 * μ_A * μ_B : ℂ) • ψ := by
    unfold ShiftedDomainConditions.A'ψ ShiftedDomainConditions.B'ψ
    unfold anticommutatorAt DomainConditions.ABψ DomainConditions.BAψ
    unfold DomainConditions.Aψ DomainConditions.Bψ
    simp only [shiftedApply]
    rw [A.apply_sub h.hBψ_A (A.domain.smul_mem _ h.hψ_A)]
    rw [A.apply_smul _ h.hψ_A]
    rw [B.apply_sub h.hAψ_B (B.domain.smul_mem _ h.hψ_B)]
    rw [B.apply_smul _ h.hψ_B]
    field_simp
    match_scalars <;> ring_nf
    · -- -(↑(B.expectation ψ ⋯ ⋯) * 2) = -(↑μ_B * 2)
      rfl
    · -- -(↑(A.expectation ψ ⋯ ⋯) * 2) = -(↑μ_A * 2)
      rfl
    · -- ↑(A.expectation ψ ⋯ ⋯) * ↑(B.expectation ψ ⋯ ⋯) * 2 = ↑μ_B * ↑μ_A * 2
      ring
  have h_inner_Aψ : ⟪ψ, h.Aψ⟫_ℂ = μ_A := by
    unfold DomainConditions.Aψ
    rw [A.inner_self_eq_re h.hψ_A]
    exact rfl
  have h_inner_Bψ : ⟪ψ, h.Bψ⟫_ℂ = μ_B := by
    unfold DomainConditions.Bψ
    rw [B.inner_self_eq_re h.hψ_B]
    exact rfl
  have h_inner_sum : ⟪ψ, A.shiftedApply ψ h.B'ψ h.h_norm h.hψ_A h.B'ψ_in_A_domain +
                        B.shiftedApply ψ h.A'ψ h.h_norm h.hψ_B h.A'ψ_in_B_domain⟫_ℂ =
                     ⟪ψ, anticommutatorAt A B ψ h.toDomainConditions⟫_ℂ -
                     (2 * μ_A * μ_B : ℂ) := by
    rw [h_expand_sum]
    simp only [inner_sub_right, inner_add_right, inner_smul_right]
    rw [h_inner_Aψ, h_inner_Bψ, h_norm_sq]
    ring
  have h_add_re : (⟪ψ, A.shiftedApply ψ h.B'ψ h.h_norm h.hψ_A h.B'ψ_in_A_domain⟫_ℂ +
                ⟪ψ, B.shiftedApply ψ h.A'ψ h.h_norm h.hψ_B h.A'ψ_in_B_domain⟫_ℂ).re =
                (⟪ψ, anticommutatorAt A B ψ h.toDomainConditions⟫_ℂ - (2 * μ_A * μ_B : ℂ)).re := by
    congr 1
    rw [← inner_add_right, h_inner_sum]
  rw [h_add_re]
  unfold covariance
  have _h_anti_real : (⟪ψ, anticommutatorAt A B ψ h.toDomainConditions⟫_ℂ).im = 0 :=
    anticommutator_im_eq_zero A B ψ h.toDomainConditions
  simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.mul_im, zero_mul, add_zero, one_div]
  ring

/-! ### Schrödinger inequality -/

/-- **Schrödinger uncertainty inequality** (variance form):
`Var(A) Var(B) ≥ ¼|⟨[A,B]⟩|² + Cov(A,B)²`. This is the strengthened form, from
which Robertson's inequality follows by dropping the (nonnegative) covariance
term. -/
lemma schrodinger_uncertainty (A B : SymmetricOperator H) (ψ : H)
    (h : ShiftedDomainConditions A B ψ) :
    A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B ≥
    (1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2 +
    (covariance A B ψ h)^2 := by
  have h_cs_sq : ‖⟪h.A'ψ, h.B'ψ⟫_ℂ‖^2 ≤ ‖h.A'ψ‖^2 * ‖h.B'ψ‖^2 := by
    have h_cs : ‖⟪h.A'ψ, h.B'ψ⟫_ℂ‖ ≤ ‖h.A'ψ‖ * ‖h.B'ψ‖ := norm_inner_le_norm h.A'ψ h.B'ψ
    have := pow_le_pow_left₀ (norm_nonneg _) h_cs 2
    rwa [mul_pow] at this
  have h_var_eq : ‖h.A'ψ‖^2 * ‖h.B'ψ‖^2 =
                  A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B := by
    unfold variance ShiftedDomainConditions.A'ψ ShiftedDomainConditions.B'ψ; rfl
  have h_re_eq : (⟪h.A'ψ, h.B'ψ⟫_ℂ).re = covariance A B ψ h :=
    re_inner_shifted_eq_covariance A B ψ h
  have h_im_eq : (⟪h.A'ψ, h.B'ψ⟫_ℂ).im =
                 (1/2) * (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).im :=
    im_inner_shifted_eq_half_commutator A B ψ h
  have h_comm_re_zero : (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).re = 0 :=
    commutator_re_eq_zero A B ψ h.toDomainConditions
  have h_norm_sq_decomp : ‖⟪h.A'ψ, h.B'ψ⟫_ℂ‖^2 =
                          (covariance A B ψ h)^2 +
                          (1/4) * (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).im^2 := by
    rw [Complex.sq_norm, normSq_eq_re_sq_add_im_sq, h_re_eq, h_im_eq]
    ring
  have h_comm_norm_eq : (1/4) * (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).im^2 =
                        (1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2 := by
    congr 1
    rw [Complex.sq_norm, normSq_of_re_zero h_comm_re_zero]
  calc A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B
    _ = ‖h.A'ψ‖^2 * ‖h.B'ψ‖^2 := h_var_eq.symm
    _ ≥ ‖⟪h.A'ψ, h.B'ψ⟫_ℂ‖^2 := h_cs_sq
    _ = (covariance A B ψ h)^2 + (1/4) * (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).im^2 :=
        h_norm_sq_decomp
    _ = (covariance A B ψ h)^2 + (1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2 := by
        rw [h_comm_norm_eq]
    _ = (1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2 + (covariance A B ψ h)^2 := by
        ring

/-- **Schrödinger uncertainty inequality** (standard-deviation form). -/
lemma schrodinger_stddev (A B : SymmetricOperator H) (ψ : H)
    (h : ShiftedDomainConditions A B ψ) :
    A.stdDev ψ h.h_norm h.hψ_A * B.stdDev ψ h.h_norm h.hψ_B ≥
    Real.sqrt ((1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2 +
               (covariance A B ψ h)^2) := by
  have h_var := schrodinger_uncertainty A B ψ h
  have h_sqrt := Real.sqrt_le_sqrt h_var
  have h_lhs : Real.sqrt (A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B) =
               A.stdDev ψ h.h_norm h.hψ_A * B.stdDev ψ h.h_norm h.hψ_B := by
    unfold stdDev
    rw [← Real.sqrt_mul (variance_nonneg A ψ h.h_norm h.hψ_A)]
  rw [h_lhs] at h_sqrt
  exact h_sqrt

/-! ### Robertson inequality (corollaries) -/

/-- **Robertson uncertainty inequality** (variance form): a corollary of
Schrödinger's, obtained by discarding the covariance term. -/
lemma robertson_uncertainty (A B : SymmetricOperator H) (ψ : H)
    (h : ShiftedDomainConditions A B ψ) :
    A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B ≥
    (1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2 := by
  have h_schrodinger := schrodinger_uncertainty A B ψ h
  have h_cov_sq_nonneg : 0 ≤ (covariance A B ψ h)^2 := sq_nonneg _
  linarith

/-- **Robertson uncertainty inequality** (standard-deviation form):
`σ_A σ_B ≥ ½ |⟨[A,B]⟩|`. -/
lemma robertson_stddev (A B : SymmetricOperator H) (ψ : H)
    (h : ShiftedDomainConditions A B ψ) :
    A.stdDev ψ h.h_norm h.hψ_A * B.stdDev ψ h.h_norm h.hψ_B ≥
    (1/2) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖ := by
  have h_var := robertson_uncertainty A B ψ h
  have h_sqrt := Real.sqrt_le_sqrt h_var
  have h_lhs : Real.sqrt (A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B) =
               A.stdDev ψ h.h_norm h.hψ_A * B.stdDev ψ h.h_norm h.hψ_B := by
    unfold stdDev
    rw [← Real.sqrt_mul (variance_nonneg A ψ h.h_norm h.hψ_A)]
  have h_rhs : Real.sqrt ((1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2) =
               (1/2) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖ := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 1/4)]
    rw [Real.sqrt_sq (norm_nonneg _)]
    have : Real.sqrt (1/4 : ℝ) = 1/2 := by
      rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/2)]; norm_num
    rw [this]
  rw [h_lhs, h_rhs] at h_sqrt
  exact h_sqrt

/-! ### Specialization to self-adjoint observables

The bounds above hold for symmetric operators; here are the physics-facing
statements for genuine self-adjoint observables, obtained by feeding
`toSymmetricOperator` into the general lemmas. The standard-deviation forms
specialize identically. -/

/-- Schrödinger uncertainty for self-adjoint observables. -/
lemma observable_schrodinger_uncertainty (A B : SelfAdjointOperator H) (ψ : H)
    (h : ShiftedDomainConditions A.toSymmetricOperator B.toSymmetricOperator ψ) :
    A.toSymmetricOperator.variance ψ h.h_norm h.hψ_A *
        B.toSymmetricOperator.variance ψ h.h_norm h.hψ_B ≥
    (1/4) * ‖⟪ψ, commutatorAt A.toSymmetricOperator B.toSymmetricOperator ψ
        h.toDomainConditions⟫_ℂ‖^2 +
    (covariance A.toSymmetricOperator B.toSymmetricOperator ψ h)^2 :=
  schrodinger_uncertainty A.toSymmetricOperator B.toSymmetricOperator ψ h

/-- Robertson uncertainty for self-adjoint observables. -/
lemma observable_robertson_uncertainty (A B : SelfAdjointOperator H) (ψ : H)
    (h : ShiftedDomainConditions A.toSymmetricOperator B.toSymmetricOperator ψ) :
    A.toSymmetricOperator.variance ψ h.h_norm h.hψ_A *
        B.toSymmetricOperator.variance ψ h.h_norm h.hψ_B ≥
    (1/4) * ‖⟪ψ, commutatorAt A.toSymmetricOperator B.toSymmetricOperator ψ
        h.toDomainConditions⟫_ℂ‖^2 :=
  robertson_uncertainty A.toSymmetricOperator B.toSymmetricOperator ψ h

/-- Schrödinger uncertainty (standard-deviation form) for self-adjoint observables. -/
lemma observable_schrodinger_stddev (A B : SelfAdjointOperator H) (ψ : H)
    (h : ShiftedDomainConditions A.toSymmetricOperator B.toSymmetricOperator ψ) :
    A.toSymmetricOperator.stdDev ψ h.h_norm h.hψ_A *
        B.toSymmetricOperator.stdDev ψ h.h_norm h.hψ_B ≥
    Real.sqrt ((1/4) * ‖⟪ψ, commutatorAt A.toSymmetricOperator B.toSymmetricOperator ψ
        h.toDomainConditions⟫_ℂ‖^2 +
      (covariance A.toSymmetricOperator B.toSymmetricOperator ψ h)^2) :=
  schrodinger_stddev A.toSymmetricOperator B.toSymmetricOperator ψ h

/-- Robertson uncertainty (standard-deviation form) for self-adjoint observables. -/
lemma observable_robertson_stddev (A B : SelfAdjointOperator H) (ψ : H)
    (h : ShiftedDomainConditions A.toSymmetricOperator B.toSymmetricOperator ψ) :
    A.toSymmetricOperator.stdDev ψ h.h_norm h.hψ_A *
        B.toSymmetricOperator.stdDev ψ h.h_norm h.hψ_B ≥
    (1/2) * ‖⟪ψ, commutatorAt A.toSymmetricOperator B.toSymmetricOperator ψ
        h.toDomainConditions⟫_ℂ‖ :=
  robertson_stddev A.toSymmetricOperator B.toSymmetricOperator ψ h

end Spectra.QuantumMechanics.Schrodinger
