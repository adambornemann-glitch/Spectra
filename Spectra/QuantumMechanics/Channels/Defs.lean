/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Channels.TraceClass.Complete

/-!
# Quantum channels: definition

A **quantum channel** is a completely positive, trace-non-increasing linear map on the
trace-class operators (the Schrödinger picture): `Φ : TraceClass H →ₗ[ℂ] TraceClass H` such
that for every `n`, `Φ` applied entrywise to an `n × n` array of trace-class operators sends
positive-semidefinite arrays to positive-semidefinite arrays (complete positivity), and `Φ`
does not increase the trace norm of any positive operator (sub-normalization; equality is the
distinguished trace-preserving case).

Complete positivity is necessary but not sufficient for a map to be physical: an ordinary
positive map (`n = 1` case) can fail to send positive operators on a *larger* system to
positive operators once tensored with an ancilla (the transpose map on `M_n(ℂ)` is the classic
example). Positivity of the finite matrix amplification is the correct, standard fix, and is
tested here via the block-quadratic-form criterion already used throughout Spectra for operator
positivity (`re ⟪ξ, T ξ⟫ ≥ 0`), applied to an `n`-tuple of vectors rather than a single one — the
same idea as `IsPositiveMatrix`'s single-operator special case `n = 1`.

## Main definitions

* `Spectra.QuantumMechanics.Channels.IsPositiveMatrix` — an `n × n` array of trace-class
  operators is *positive* if `∑ᵢⱼ ⟪ξᵢ, Mᵢⱼ ξⱼ⟫ ≥ 0` for every finite family of vectors
  `ξ : Fin n → H`.
* `Spectra.QuantumMechanics.Channels.IsCompletelyPositive` — `Φ` is completely positive if it sends
  every positive array to a positive array, entrywise, for every `n`.
* `Spectra.QuantumMechanics.Channels.QuantumChannel` — the bundled structure: a linear map on
  `TraceClass H` that is completely positive and trace-non-increasing on positive operators.

## Main results

* `isPositiveMatrix_zero_iff` / `isPositiveMatrix_one_iff` — the `n = 0` case is vacuous, the
  `n = 1` case recovers ordinary operator positivity `0 ≤ T`.
* `QuantumChannel.id` — the identity map is a quantum channel.

## Context

First brick of the Quantum Channels project (`Projects/Quantum Channels/` in the vault): the
Schrödinger-picture definition, built directly on the completed Trace-Class Hard Core
(`TraceClass/*.lean`, all sorry-free). See the vault Goal note
`Goal - Quantum Channels Core (Kraus Decomposition and Stinespring Dilation)` for the full roadmap
(Kraus decomposition, Naimark/Choi cross-checks, channel algebra, general Stinespring dilation).
-/

open ContinuousLinearMap RCLike
open scoped InnerProductSpace InnerProduct ComplexOrder

namespace Spectra.QuantumMechanics.Channels

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Positivity of a finite array of trace-class operators -/

/-- The block quadratic form `∑ᵢⱼ ⟪Mᵢⱼ ξⱼ, ξᵢ⟫` of an `n × n` array of trace-class operators against
a finite family of vectors. -/
noncomputable def blockForm {n : ℕ} (M : Fin n → Fin n → TraceClass H) (ξ : Fin n → H) : ℂ :=
  ∑ i, ∑ j, ⟪(M i j).toOp (ξ j), ξ i⟫_ℂ

/-- An `n × n` array of trace-class operators `M` is **positive** if the block quadratic form
`blockForm M ξ` is a nonnegative *real* number — `0 ≤ z` in `ℂ`'s order means both `re z ≥ 0` and
`im z = 0` (`RCLike.nonneg_iff`) — for every finite family of vectors `ξ : Fin n → H`. This is the
standard "block operator on `H^n` is positive" criterion, generalizing the single-operator case
`n = 1` (`isPositiveMatrix_one_iff`). -/
def IsPositiveMatrix {n : ℕ} (M : Fin n → Fin n → TraceClass H) : Prop :=
  ∀ ξ : Fin n → H, 0 ≤ blockForm M ξ

/-- The `n = 0` case is vacuous: the empty sum is `0`. -/
@[simp] theorem isPositiveMatrix_zero_iff (M : Fin 0 → Fin 0 → TraceClass H) :
    IsPositiveMatrix M := fun _ξ => by simp [blockForm]

/-- `blockForm` for `n = 1` collapses to the single entry's quadratic form. -/
theorem blockForm_one (M : Fin 1 → Fin 1 → TraceClass H) (ξ : Fin 1 → H) :
    blockForm M ξ = ⟪(M 0 0).toOp (ξ 0), ξ 0⟫_ℂ := by simp [blockForm]

/-- The `n = 1` case recovers ordinary operator positivity: a `1 × 1` array is positive iff its
single entry is a positive operator. -/
theorem isPositiveMatrix_one_iff (M : Fin 1 → Fin 1 → TraceClass H) :
    IsPositiveMatrix M ↔ 0 ≤ (M 0 0).toOp := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
  simp only [IsPositiveMatrix, blockForm_one]
  constructor
  · intro hM x
    obtain ⟨hre, him⟩ := RCLike.nonneg_iff.1 (hM (fun _ => x))
    exact ⟨RCLike.conj_eq_iff_re.1 (RCLike.conj_eq_iff_im.2 him), hre⟩
  · intro hM ξ
    obtain ⟨heq, hre⟩ := hM (ξ 0)
    exact RCLike.nonneg_iff.2 ⟨hre, RCLike.conj_eq_iff_im.1 (RCLike.conj_eq_iff_re.2 heq)⟩

/-! ## Complete positivity -/

/-- A linear map `Φ` on the trace-class operators is **completely positive** if, for every `n`, it
sends positive `n × n` arrays to positive `n × n` arrays when applied entrywise. -/
def IsCompletelyPositive (Φ : TraceClass H →ₗ[ℂ] TraceClass H) : Prop :=
  ∀ (n : ℕ) (M : Fin n → Fin n → TraceClass H),
    IsPositiveMatrix M → IsPositiveMatrix (fun i j => Φ (M i j))

/-- Complete positivity implies ordinary positivity (the `n = 1` instance). -/
theorem IsCompletelyPositive.isPositive {Φ : TraceClass H →ₗ[ℂ] TraceClass H}
    (hΦ : IsCompletelyPositive Φ) {ρ : TraceClass H} (hρ : 0 ≤ ρ.toOp) :
    0 ≤ (Φ ρ).toOp := by
  have h1 : IsPositiveMatrix (fun _ _ : Fin 1 => ρ) := (isPositiveMatrix_one_iff _).2 hρ
  have h2 := hΦ 1 (fun _ _ => ρ) h1
  exact (isPositiveMatrix_one_iff _).1 h2

/-! ## Quantum channels -/

/-- A **quantum channel**: a completely positive, trace-non-increasing linear map on the
trace-class operators (Schrödinger picture). Trace-preservation (`=` rather than `≤`) is the
distinguished unital case, e.g. the identity channel (`QuantumChannel.id`); genuinely sub-unital
channels arise from conditioning on a measurement outcome. -/
structure QuantumChannel (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The underlying linear map on the trace-class operators. -/
  toFun : TraceClass H →ₗ[ℂ] TraceClass H
  /-- The map is completely positive. -/
  cp : IsCompletelyPositive toFun
  /-- The map does not increase the trace norm of a positive operator. -/
  traceNonIncreasing : ∀ ρ : TraceClass H, 0 ≤ ρ.toOp → traceNorm (toFun ρ).toOp ≤ traceNorm ρ.toOp

namespace QuantumChannel

variable (H) in
/-- **The identity channel.** Trivially completely positive (it changes nothing) and
trace-preserving (hence, in particular, trace-non-increasing). -/
def id : QuantumChannel H where
  toFun := LinearMap.id
  cp := fun _n _M hM => hM
  traceNonIncreasing := fun _ρ _hρ => le_refl _

@[simp] theorem id_toFun_apply (ρ : TraceClass H) : (id H).toFun ρ = ρ := rfl

end QuantumChannel

end Spectra.QuantumMechanics.Channels
