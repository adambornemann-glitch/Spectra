/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Quantum.State
import Spectra.QuantumMechanics.Channels.TraceClass.RankOne
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection

/-!
# Von Neumann entropy of a quantum state

For a quantum state `ρ : QState H` — a positive, trace-one trace-class operator on a (possibly
**infinite-dimensional**) complex Hilbert space `H` — the **von Neumann entropy** is
`S(ρ) = tr(-ρ log ρ)`.  We build it purely operator-theoretically, so that it is correct in
infinite dimensions:

* the operator `-ρ log ρ` is `cfc Real.negMulLog ρ.toOp`, the continuous functional calculus of
  `x ↦ -x log x` applied to `ρ` (`entropyOp`);
* its **positive trace** `posTrace` — valued in `ℝ≥0∞`, hence gracefully `+∞` for states whose
  eigenvalues decay too slowly — is the entropy (`vonNeumannEntropy`).

Working in `ℝ≥0∞` is essential in infinite dimensions: the von Neumann entropy of a density
operator can be `+∞`, and a real-valued definition would silently collapse that to `0`.  `posTrace`
is basis-independent (`posTrace_indep`), so although the definition names a fixed basis, its value
does not depend on it (`vonNeumannEntropy_indep`); in particular one may evaluate it in `ρ`'s own
eigenbasis, where it becomes the Shannon entropy `∑ᵢ negMulLog λᵢ` of the eigenvalue distribution.

## Main definitions

* `entropyOp ρ` — the operator `-ρ log ρ = cfc Real.negMulLog ρ.toOp`.
* `vonNeumannEntropy ρ` — `S(ρ) = tr(-ρ log ρ)`, valued in `ℝ≥0∞` (possibly `+∞`).
* `pureState hψ` — the pure state `|ψ⟩⟨ψ|` of a unit vector, as a `QState`.

## Main results

* `entropyOp_nonneg` — `0 ≤ -ρ log ρ` (because `spectrum ℝ ρ ⊆ [0,1]` and `negMulLog ≥ 0` there).
  This is the load-bearing fact: it is what makes `posTrace (entropyOp ρ)` the honest trace of a
  *positive* operator rather than a junk artifact of `posTrace` on a non-positive operator.
* `vonNeumannEntropy_indep` — the entropy does not depend on the chosen Hilbert basis.
* `vonNeumannEntropy_pure` — a pure state has zero entropy.

## Deferred

The **spectral form** `vonNeumannEntropy ρ = ∑ᵢ negMulLog λᵢ` over `ρ`'s eigenvalues — the identity
that literally reads `S(ρ) = -∑ λᵢ log λᵢ` — requires an eigenbasis decomposition of a compact
positive operator, which is not yet available in Spectra.  The definition here is the operator form
`tr(-ρ log ρ)`, which is the standard textbook *definition* of the von Neumann entropy; the
eigenvalue-sum form is a downstream theorem about it.
-/

open Spectra.QuantumMechanics.Channels
open scoped ENNReal NNReal InnerProductSpace

namespace Spectra.InformationGeometry.Quantum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The spectrum of a quantum state lies in `[0,1]` -/

namespace QState

/-- The spectrum of a quantum state is nonnegative: `spectrum ℝ ρ ⊆ [0, ∞)`. -/
lemma spectrum_toOp_nonneg (ρ : QState H) {x : ℝ} (hx : x ∈ spectrum ℝ ρ.toOp) : 0 ≤ x :=
  spectrum_nonneg_of_nonneg ρ.nonneg hx

/-- The spectrum of a quantum state is bounded by `1`: `spectrum ℝ ρ ⊆ (-∞, 1]`.  For a positive
trace-one operator every spectral value is at most the operator norm `‖ρ‖ ≤ ‖ρ‖₁ = 1`. -/
lemma spectrum_toOp_le_one (ρ : QState H) {x : ℝ} (hx : x ∈ spectrum ℝ ρ.toOp) : x ≤ 1 := by
  have hx0 : 0 ≤ x := ρ.spectrum_toOp_nonneg hx
  -- `H` is nontrivial: a trivial space would force `ρ = 0`, contradicting `tr ρ = 1`.
  have hntriv : Nontrivial H := by
    rcases subsingleton_or_nontrivial H with hs | hn
    · exfalso
      have h0 : ρ.toOp = 0 := Subsingleton.elim _ _
      have h1 : trace ρ.toOp = 1 := ρ.trace_toOp
      rw [h0] at h1
      have htz : trace (0 : H →L[ℂ] H) = 0 := by unfold trace; simp
      rw [htz] at h1
      exact one_ne_zero h1.symm
    · exact hn
  have hnorm : ‖x‖ ≤ ‖ρ.toOp‖ := spectrum.norm_le_norm_of_mem hx
  have hle1 : ‖ρ.toOp‖ ≤ 1 := ρ.traceNorm_toOp ▸ norm_le_traceNorm ρ.isTraceClass
  rw [Real.norm_eq_abs, abs_of_nonneg hx0] at hnorm
  linarith

end QState

/-! ## The entropy operator and the von Neumann entropy -/

/-- The **entropy operator** `-ρ log ρ = cfc Real.negMulLog ρ.toOp` of a quantum state. -/
noncomputable def entropyOp (ρ : QState H) : H →L[ℂ] H := cfc Real.negMulLog ρ.toOp

/-- **The entropy operator is nonnegative.** Since `spectrum ℝ ρ ⊆ [0,1]` and `negMulLog ≥ 0` on
`[0,1]`, the functional-calculus operator `-ρ log ρ` is positive.  This is what makes
`vonNeumannEntropy` the honest positive trace of `-ρ log ρ` rather than a `posTrace` junk value. -/
lemma entropyOp_nonneg (ρ : QState H) : 0 ≤ entropyOp ρ :=
  cfc_nonneg fun _ hx =>
    Real.negMulLog_nonneg (ρ.spectrum_toOp_nonneg hx) (ρ.spectrum_toOp_le_one hx)

/-- The entropy operator is self-adjoint. -/
lemma entropyOp_isSelfAdjoint (ρ : QState H) : IsSelfAdjoint (entropyOp ρ) :=
  (entropyOp_nonneg ρ).isSelfAdjoint

/-- The **von Neumann entropy** `S(ρ) = tr(-ρ log ρ)`, valued in `ℝ≥0∞` (possibly `+∞`). -/
noncomputable def vonNeumannEntropy (ρ : QState H) : ℝ≥0∞ :=
  posTrace (stdHilbertBasis H) (entropyOp ρ)

/-- The von Neumann entropy does not depend on the chosen Hilbert basis: it may be evaluated in any
basis, in particular `ρ`'s own eigenbasis. -/
theorem vonNeumannEntropy_indep {ι : Type*} (b : HilbertBasis ι ℂ H) (ρ : QState H) :
    posTrace b (entropyOp ρ) = vonNeumannEntropy ρ :=
  posTrace_indep b (stdHilbertBasis H) (entropyOp ρ)

/-- The von Neumann entropy is nonnegative.  (In `ℝ≥0∞` this is immediate; the mathematical content
— that the real trace of the *positive* operator `-ρ log ρ` is `≥ 0` — is carried by
`entropyOp_nonneg`.) -/
lemma vonNeumannEntropy_nonneg (ρ : QState H) : 0 ≤ vonNeumannEntropy ρ := zero_le

/-! ## Pure states have zero entropy -/

/-- The **pure state** `|ψ⟩⟨ψ|` of a unit vector `ψ`, as a quantum state. -/
noncomputable def pureState {ψ : H} (hψ : ‖ψ‖ = 1) : QState H where
  toTraceClass := rankOneTC ψ
  nonneg := by rw [rankOneTC_toOp]; exact rankOneSelf_nonneg ψ
  trace_one := by
    rw [rankOneTC_toOp, trace_rankOne, inner_self_eq_norm_sq_to_K, hψ]
    norm_num

@[simp] lemma pureState_toOp {ψ : H} (hψ : ‖ψ‖ = 1) :
    (pureState hψ).toOp = InnerProductSpace.rankOne ℂ ψ ψ := rankOneTC_toOp ψ

/-- The entropy operator of a pure state vanishes: `-|ψ⟩⟨ψ| log|ψ⟩⟨ψ| = 0`.  `|ψ⟩⟨ψ|` is an
idempotent, so its spectrum is `⊆ {0,1}`, and `negMulLog` vanishes at both `0` and `1`. -/
lemma entropyOp_pure {ψ : H} (hψ : ‖ψ‖ = 1) : entropyOp (pureState hψ) = 0 := by
  have hsa : IsSelfAdjoint (pureState hψ).toOp := (pureState hψ).nonneg.isSelfAdjoint
  have hidem : IsIdempotentElem (pureState hψ).toOp := by
    rw [pureState_toOp]; exact InnerProductSpace.isIdempotentElem_rankOne_self hψ
  have hspec : spectrum ℝ (pureState hψ).toOp ⊆ {0, 1} :=
    (isIdempotentElem_iff_spectrum_subset ℝ _ hsa).mp hidem
  rw [entropyOp,
    cfc_congr (f := Real.negMulLog) (g := fun _ : ℝ => (0 : ℝ)) (a := (pureState hψ).toOp) ?_,
    cfc_const_zero]
  intro x hx
  have := hspec hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  rcases this with h | h <;> subst h <;> simp

/-- **A pure state has zero von Neumann entropy**, `S(|ψ⟩⟨ψ|) = 0`. -/
lemma vonNeumannEntropy_pure {ψ : H} (hψ : ‖ψ‖ = 1) : vonNeumannEntropy (pureState hψ) = 0 := by
  rw [vonNeumannEntropy, entropyOp_pure hψ, posTrace_zero]

end Spectra.InformationGeometry.Quantum
