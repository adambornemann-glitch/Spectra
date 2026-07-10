/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Quantum.Entropy.Gibbs
import Spectra.QuantumMechanics.Channels.TraceClass.Basic
import Spectra.SpectralTheory.Weak
import Spectra.SpectralTheory.Eigenspace
import Spectra.SpectralTheory.Essential.Discrete
import Spectra.SpectralTheory.Calculus.PMapSquareRoot
import Spectra.Operator.Bounded
import Spectra.Resolvent.NumericalRangeSpectrum

/-!
# The quantum cross entropy and the full Klein inequality

For two quantum states `ρ σ : QState H`, the **quantum relative entropy** (Umegaki) is
`D(ρ‖σ) = Tr(ρ log ρ) − Tr(ρ log σ) = crossEntropy(ρ,σ) − S(ρ)`, and **Klein's inequality** is the
statement `D(ρ‖σ) ≥ 0`, i.e. `S(ρ) ≤ crossEntropy(ρ,σ)`.  This file builds the cross-entropy
`crossEntropy(ρ,σ) = −Tr(ρ log σ)` **operator-theoretically**, so that it is correct in
(possibly) infinite dimensions, and proves the full Klein inequality as the ordering
`S(ρ) ≤ crossEntropy(ρ,σ)`.

## The construction

`−Tr(ρ log σ) = ∑ᵢ λᵢ ⟪eᵢ, (−log σ) eᵢ⟫` in `ρ`'s eigenbasis `{eᵢ}` (with eigenvalues `λᵢ`).  The
operator `log σ` is **unbounded** in infinite dimensions (a faithful compact `σ` has eigenvalues
accumulating at `0`), so we never form it: instead we read `⟪eᵢ, (−log σ) eᵢ⟫ = ∫ (−log t) dμ_{eᵢ}`
off `σ`'s **scalar spectral measure** `μ_{eᵢ}` at `eᵢ`, realized as a lower Lebesgue integral in
`ℝ≥0∞`.  Because `σ` is a state, `‖σ‖ ≤ 1`, so its spectrum lies in `[0,1]` and `−log t ≥ 0` on the
support; the whole cross-entropy is therefore a sum of nonnegative `ℝ≥0∞` quantities — **always
well-defined (possibly `+∞`) with no integrability hypothesis**.

## The proof (chain of two legs)

`S(ρ) = ∑ᵢ negMulLog λᵢ ≤ measuredCrossEntropy(ρ,σ) = ∑ᵢ −λᵢ log sᵢ ≤ crossEntropy(ρ,σ)`, where
`sᵢ = ⟪eᵢ, σ eᵢ⟫` is `σ`'s diagonal.  The first leg is the (already proved) Gibbs inequality; the
second leg is the **tangent-line Jensen** inequality `∫ log t dμ_{eᵢ} ≤ log sᵢ`
(`Real.integral_log_le_log_of_probability`), applied per eigenvector.  Faithfulness of `σ` enters in
exactly one place: it kills the spectral atom at `0`, so `t > 0` `μ_{eᵢ}`-a.e. and the tangent line
is valid `μ_{eᵢ}`-a.e.

## Main results

* `QState.crossEntropy` — `−Tr(ρ log σ)`, valued in `ℝ≥0∞`.
* `QState.measuredCrossEntropy_le_crossEntropy` — the second leg (the Jensen bridge).
* `QState.vonNeumannEntropy_le_crossEntropy` — **the full Klein inequality** `S(ρ) ≤ crossEntropy`.
* `QState.crossEntropy_self` — non-vacuity: `crossEntropy ρ ρ = vonNeumannEntropy ρ`.
-/

open Spectra.QuantumMechanics.Channels RCLike MeasureTheory
open Spectra.QuantumMechanics.SpectralTheory Spectra.YosidaHille Spectra.Operator
open Spectra.OneParameterUnitaryGroup Spectra.Resolvent
open scoped InnerProductSpace ENNReal NNReal

namespace Spectra.InformationGeometry.Quantum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace QState

/-! ## `σ`'s spectral measure -/

/-- `σ` as a (bounded) self-adjoint operator with full domain, via `ofBounded`. -/
noncomputable def sigmaOp (σ : QState H) : SelfAdjointOperator H :=
  SelfAdjointOperator.ofBounded σ.toOp σ.isSelfAdjoint_toOp

/-- The spectral projection-valued measure of `σ`. -/
noncomputable def sigmaPVM (σ : QState H) : Spectra.ProjValMeasure H :=
  PVM.spectralPVM σ.sigmaOp.selfAdjoint

/-- `σ`'s **scalar spectral measure** at a vector `ψ`, `μ_ψ = ⟪ψ, E(·) ψ⟫`. -/
noncomputable def spectralMeasure (σ : QState H) (ψ : H) : Measure ℝ :=
  σ.sigmaPVM.diag ψ

lemma spectralMeasure_eq (σ : QState H) (ψ : H) :
    σ.spectralMeasure ψ = (PVM.spectralPVM σ.sigmaOp.selfAdjoint).diag ψ := rfl

/-- Every vector lies in `σ.sigmaOp`'s (full) domain. -/
lemma mem_sigmaOp_domain (σ : QState H) (ψ : H) : ψ ∈ σ.sigmaOp.toLinearPMap.domain := by
  change ψ ∈ ((σ.toOp : H →ₗ[ℂ] H).toPMap ⊤).domain
  rw [LinearMap.toPMap_domain]; trivial

/-- `σ.sigmaOp` acts as `σ.toOp`. -/
lemma sigmaOp_apply (σ : QState H) (ψ : H) (hψ : ψ ∈ σ.sigmaOp.toLinearPMap.domain) :
    σ.sigmaOp.toLinearPMap ⟨ψ, hψ⟩ = σ.toOp ψ := by
  change ((σ.toOp : H →ₗ[ℂ] H).toPMap ⊤) ⟨ψ, hψ⟩ = σ.toOp ψ
  rw [LinearMap.toPMap_apply]; rfl

/-- **The mean of `σ`'s spectral measure is the diagonal element `⟪ψ, σ ψ⟫`.**  For `ψ = eᵢ` this is
`sᵢ = diagSigma σ i` — tying the σ-mean back to the very diagonal the Gibbs leg uses. -/
lemma spectralMeasure_integral_id (σ : QState H) (ψ : H) :
    ∫ t, t ∂(σ.spectralMeasure ψ) = (⟪ψ, σ.toOp ψ⟫_ℂ).re := by
  have hmem := σ.mem_sigmaOp_domain ψ
  rw [spectralMeasure_eq, spectralPVM_integral_id σ.sigmaOp.selfAdjoint ψ hmem,
    σ.sigmaOp_apply ψ hmem]

/-- `∫ t dμ_{eᵢ} = diagSigma σ i` (the eigenbasis specialization). -/
lemma spectralMeasure_integral_id_eigenbasis (ρ σ : QState H) (i : eigenIndex ρ.toOp) :
    ∫ t, t ∂(σ.spectralMeasure (ρ.eigenbasis i)) = ρ.diagSigma σ i :=
  σ.spectralMeasure_integral_id (ρ.eigenbasis i)

/-- The identity is `μ_ψ`-integrable (a first-moment bound). -/
lemma integrable_id_spectralMeasure (σ : QState H) (ψ : H) :
    Integrable (fun t : ℝ => t) (σ.spectralMeasure ψ) :=
  spectralPVM_integrable_id σ.sigmaOp.selfAdjoint ψ (σ.mem_sigmaOp_domain ψ)

/-- For a unit vector, `σ`'s spectral measure is a **probability measure**. -/
lemma isProbabilityMeasure_spectralMeasure (σ : QState H) {ψ : H} (hψ : ‖ψ‖ = 1) :
    IsProbabilityMeasure (σ.spectralMeasure ψ) := by
  haveI : IsFiniteMeasure (σ.spectralMeasure ψ) := σ.sigmaPVM.diag_finite ψ
  refine ⟨?_⟩
  have h := σ.sigmaPVM.diag_univ_toReal ψ
  rw [hψ, one_pow] at h
  rw [show σ.spectralMeasure ψ = σ.sigmaPVM.diag ψ from rfl,
    ← ENNReal.ofReal_toReal (measure_ne_top (σ.sigmaPVM.diag ψ) Set.univ), h, ENNReal.ofReal_one]

/-! ## Faithfulness kills the atom at `0` and the negative rays -/

/-- **No spectral atom at `0` for faithful `σ`.**  `E({0}) ψ` is a `0`-eigenvector of `σ`, hence in
`ker σ = {0}`, so `μ_ψ({0}) = ‖E({0}) ψ‖² = 0`. -/
lemma spectralMeasure_singleton_zero_of_faithful (σ : QState H) (hσ : σ.Faithful) (ψ : H) :
    (σ.spectralMeasure ψ) {0} = 0 := by
  obtain ⟨hmem, hval⟩ :=
    spectralPVM_proj_singleton_apply_isEigen σ.sigmaOp.selfAdjoint 0 ψ
  have hσv : σ.toOp ((PVM.spectralPVM σ.sigmaOp.selfAdjoint).proj {0}
      (measurableSet_singleton 0) ψ) = 0 := by
    rw [← σ.sigmaOp_apply _ hmem, hval]; simp
  have hv0 : (PVM.spectralPVM σ.sigmaOp.selfAdjoint).proj {0} (measurableSet_singleton 0) ψ = 0 :=
    hσ (by rw [hσv, map_zero])
  rw [spectralMeasure_eq]
  exact (PVM.spectralPVM σ.sigmaOp.selfAdjoint).diag_apply_eq_zero_of_proj_apply_eq_zero
    (measurableSet_singleton 0) hv0

/-- **`σ`'s spectral measure charges no negative reals** (`σ ≥ 0`). -/
lemma spectralMeasure_Iio_zero (σ : QState H) (ψ : H) :
    (σ.spectralMeasure ψ) (Set.Iio 0) = 0 := by
  rw [spectralMeasure_eq, PVM.spectralPVM_diag]
  apply borelMeasure_Iio_zero_eq_zero_of_dense
  · rw [generator_genToGroup σ.sigmaOp.selfAdjoint]
    exact σ.sigmaOp.selfAdjoint.dense_domain
  · intro z
    have hz2 : (z : H) ∈ σ.sigmaOp.toLinearPMap.domain := σ.mem_sigmaOp_domain z
    have hval : generator (genToGroup σ.sigmaOp.selfAdjoint) z = σ.toOp (z : H) := by
      have h1 : generator (genToGroup σ.sigmaOp.selfAdjoint) z
          = σ.sigmaOp.toLinearPMap ⟨(z : H), hz2⟩ :=
        (le_of_eq (generator_genToGroup σ.sigmaOp.selfAdjoint)).2 rfl
      rw [h1, σ.sigmaOp_apply (z : H) hz2]
    rw [hval]
    simpa using
      ((ContinuousLinearMap.nonneg_iff_isPositive σ.toOp).mp σ.toOp_nonneg).re_inner_nonneg_right
        (z : H)

/-- **The spectral measure of a faithful `σ` is supported on the positives**: `t > 0` `μ_ψ`-a.e. -/
lemma spectralMeasure_ae_pos_of_faithful (σ : QState H) (hσ : σ.Faithful) (ψ : H) :
    ∀ᵐ t ∂(σ.spectralMeasure ψ), 0 < t := by
  have hIic : (σ.spectralMeasure ψ) (Set.Iic 0) = 0 := by
    rw [show (Set.Iic (0 : ℝ)) = Set.Iio 0 ∪ {0} from (Set.Iio_union_right).symm]
    exact measure_union_null (σ.spectralMeasure_Iio_zero ψ)
      (σ.spectralMeasure_singleton_zero_of_faithful hσ ψ)
  rw [ae_iff]
  have hset : {t : ℝ | ¬ 0 < t} = Set.Iic 0 := by ext t; simp [not_lt]
  rw [hset]; exact hIic

/-- A quantum state forces the Hilbert space to be nontrivial (`tr ρ = 1 ≠ 0`). -/
lemma nontrivial (σ : QState H) : Nontrivial H := by
  rcases subsingleton_or_nontrivial H with hs | hn
  · refine absurd σ.trace_toOp ?_
    rw [Subsingleton.elim σ.toOp 0, show trace (0 : H →L[ℂ] H) = 0 by unfold trace; simp]
    exact zero_ne_one
  · exact hn

/-- **`σ`'s spectral measure charges no reals `> 1`** (`σ ≤ 1`, via the numerical range).  For a
state `‖σ‖ ≤ 1`, so `W(σ) ⊆ {re ≤ 1}` and any `λ > 1` lies outside `closure (W(σ))`, hence in the
resolvent set; the spectral projection `E((1,∞))` therefore vanishes. -/
lemma spectralMeasure_Ioi_one (σ : QState H) (ψ : H) :
    (σ.spectralMeasure ψ) (Set.Ioi 1) = 0 := by
  haveI := σ.nontrivial
  have hσnorm : ‖σ.toOp‖ ≤ 1 := σ.traceNorm_toOp ▸ norm_le_traceNorm σ.isTraceClass
  have hW : numericalRange σ.sigmaOp.toLinearPMap ⊆ {z : ℂ | z.re ≤ 1} := by
    rintro z ⟨φ, hφ1, rfl⟩
    change (⟪(φ : H), σ.sigmaOp.toLinearPMap φ⟫_ℂ).re ≤ 1
    rw [show σ.sigmaOp.toLinearPMap φ = σ.toOp (φ : H) from σ.sigmaOp_apply (φ : H) φ.2]
    calc (⟪(φ : H), σ.toOp (φ : H)⟫_ℂ).re
        ≤ ‖⟪(φ : H), σ.toOp (φ : H)⟫_ℂ‖ := by
          simpa using re_le_norm (⟪(φ : H), σ.toOp (φ : H)⟫_ℂ)
      _ ≤ ‖(φ : H)‖ * ‖σ.toOp (φ : H)‖ := norm_inner_le_norm _ _
      _ ≤ ‖(φ : H)‖ * (‖σ.toOp‖ * ‖(φ : H)‖) := by gcongr; exact σ.toOp.le_opNorm _
      _ ≤ 1 := by rw [hφ1]; nlinarith [hσnorm]
  have hne : (numericalRange σ.sigmaOp.toLinearPMap).Nonempty := by
    obtain ⟨u, hu⟩ := exists_ne (0 : H)
    exact ⟨_, ⟨⟨(‖u‖⁻¹ : ℂ) • u, Submodule.mem_top⟩, norm_smul_inv_norm hu, rfl⟩⟩
  rw [spectralMeasure_eq]
  have hproj : (PVM.spectralPVM σ.sigmaOp.selfAdjoint).proj (Set.Ioi 1) measurableSet_Ioi = 0 :=
    spectralPVM_proj_eq_zero_of_subset_resolventSet σ.sigmaOp.selfAdjoint measurableSet_Ioi
      (fun lam hlam => numericalRange_mem_resolventSet σ.sigmaOp.selfAdjoint hne (lam : ℂ)
        (fun hmem => by
          have hle : (lam : ℂ).re ≤ 1 :=
            closure_minimal hW (isClosed_le Complex.continuous_re continuous_const) hmem
          rw [Complex.ofReal_re] at hle
          exact absurd hle (not_le.mpr (Set.mem_Ioi.mp hlam))))
  exact (PVM.spectralPVM σ.sigmaOp.selfAdjoint).diag_apply_eq_zero_of_proj_apply_eq_zero
    measurableSet_Ioi (by rw [hproj]; rfl)

/-- The spectral measure of a state is supported below `1`: `t ≤ 1` `μ_ψ`-a.e. -/
lemma spectralMeasure_ae_le_one (σ : QState H) (ψ : H) :
    ∀ᵐ t ∂(σ.spectralMeasure ψ), t ≤ 1 := by
  rw [ae_iff]
  have hset : {t : ℝ | ¬ t ≤ 1} = Set.Ioi 1 := by ext t; simp [not_le]
  rw [hset]; exact σ.spectralMeasure_Ioi_one ψ

/-! ## Faithful `σ` has strictly positive diagonal (feeds the Gibbs leg) -/

/-- **A faithful `σ` has strictly positive diagonal `sᵢ > 0`.**  If `sᵢ = re⟪eᵢ, σ eᵢ⟫ = 0` then
`‖σ^{1/2} eᵢ‖ = 0`, so `σ eᵢ = σ^{1/2}(σ^{1/2} eᵢ) = 0`, contradicting injectivity and `eᵢ ≠ 0`. -/
lemma diagSigma_pos_of_faithful (ρ σ : QState H) (hσ : σ.Faithful) (i : eigenIndex ρ.toOp) :
    0 < ρ.diagSigma σ i := by
  rcases lt_or_eq_of_le (ρ.diagSigma_nonneg σ i) with h | h
  · exact h
  · exfalso
    have hnorm : ‖sqrtOp σ.toOp (ρ.eigenbasis i)‖ ^ 2 = 0 := by
      rw [norm_sqrtOp_sq σ.toOp σ.toOp_nonneg (ρ.eigenbasis i)]
      exact h.symm
    have hsqrt0 : sqrtOp σ.toOp (ρ.eigenbasis i) = 0 := by
      have hn : ‖sqrtOp σ.toOp (ρ.eigenbasis i)‖ = 0 := by
        nlinarith [norm_nonneg (sqrtOp σ.toOp (ρ.eigenbasis i)), hnorm]
      exact norm_eq_zero.mp hn
    have hσ0 : σ.toOp (ρ.eigenbasis i) = 0 := by
      have hmul : (sqrtOp σ.toOp * sqrtOp σ.toOp) (ρ.eigenbasis i) = σ.toOp (ρ.eigenbasis i) := by
        rw [sqrtOp_mul_self σ.toOp σ.toOp_nonneg]
      rw [← hmul, ContinuousLinearMap.mul_apply, hsqrt0, map_zero]
    exact ρ.eigenbasis_ne_zero i (hσ (by rw [hσ0, map_zero]))

/-! ## The cross entropy and the full Klein inequality -/

/-- **The quantum cross entropy** `crossEntropy(ρ,σ) = −Tr(ρ log σ)`, valued in `ℝ≥0∞`.  Read off
in `ρ`'s eigenbasis as `∑ᵢ λᵢ ⟪eᵢ, (−log σ) eᵢ⟫`, with each `⟪eᵢ, (−log σ) eᵢ⟫` realized as the
lower Lebesgue integral `∫⁻ (−log t) dμ_{eᵢ}` against `σ`'s scalar spectral measure — so the
unbounded operator `log σ` is never formed, and the value is always well-defined (possibly `+∞`). -/
noncomputable def crossEntropy (ρ σ : QState H) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (ρ.eigenvalue i)
    * ∫⁻ t, ENNReal.ofReal (-Real.log t) ∂(σ.spectralMeasure (ρ.eigenbasis i))

/-- **The per-eigenvector Jensen bridge** (the analytic crux).  `ofReal(−λᵢ log sᵢ)` is dominated by
the `i`-th cross-entropy term.  In the integrable branch this is the tangent-line Jensen
inequality `∫ log t dμ_{eᵢ} ≤ log sᵢ`; in the non-integrable branch the lower integral is `+∞`
and domination is free. -/
lemma ofReal_measuredTerm_le_lintegral (ρ σ : QState H) (hσ : σ.Faithful) (i : eigenIndex ρ.toOp) :
    ENNReal.ofReal (-ρ.eigenvalue i * Real.log (ρ.diagSigma σ i))
      ≤ ENNReal.ofReal (ρ.eigenvalue i)
        * ∫⁻ t, ENNReal.ofReal (-Real.log t) ∂(σ.spectralMeasure (ρ.eigenbasis i)) := by
  set μ := σ.spectralMeasure (ρ.eigenbasis i) with _hμ
  haveI : IsProbabilityMeasure μ :=
    σ.isProbabilityMeasure_spectralMeasure (ρ.eigenbasis.orthonormal.1 i)
  set lam := ρ.eigenvalue i with _hlam
  set s := ρ.diagSigma σ i with _hs
  have hlam0 : 0 ≤ lam := ρ.eigenvalue_nonneg i
  have hs0 : 0 < s := ρ.diagSigma_pos_of_faithful σ hσ i
  have haepos : ∀ᵐ t ∂μ, 0 < t := σ.spectralMeasure_ae_pos_of_faithful hσ (ρ.eigenbasis i)
  have haele : ∀ᵐ t ∂μ, t ≤ 1 := σ.spectralMeasure_ae_le_one (ρ.eigenbasis i)
  have haenn : 0 ≤ᵐ[μ] fun t => -Real.log t := by
    filter_upwards [haepos, haele] with t ht1 ht2
    change (0 : ℝ) ≤ -Real.log t
    have : Real.log t ≤ 0 := Real.log_nonpos ht1.le ht2
    linarith
  have hmeas : AEStronglyMeasurable (fun t => -Real.log t) μ :=
    Real.measurable_log.neg.aestronglyMeasurable
  by_cases hint : Integrable (fun t => -Real.log t) μ
  · have hbridge : ∫⁻ t, ENNReal.ofReal (-Real.log t) ∂μ = ENNReal.ofReal (∫ t, -Real.log t ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hint haenn).symm
    rw [hbridge, ← ENNReal.ofReal_mul hlam0]
    apply ENNReal.ofReal_le_ofReal
    have hlogint : Integrable (fun t => Real.log t) μ := by simpa using hint.neg
    have hjensen : ∫ t, Real.log t ∂μ ≤ Real.log s :=
      Real.integral_log_le_log_of_probability hs0 haepos
        (σ.integrable_id_spectralMeasure (ρ.eigenbasis i)) hlogint
        (spectralMeasure_integral_id_eigenbasis ρ σ i)
    rw [integral_neg]
    nlinarith [hjensen, hlam0]
  · have htop : ∫⁻ t, ENNReal.ofReal (-Real.log t) ∂μ = ⊤ := by
      by_contra h
      exact hint ((lintegral_ofReal_ne_top_iff_integrable hmeas haenn).mp h)
    rw [htop]
    rcases eq_or_lt_of_le hlam0 with h0 | h0
    · rw [← h0]; simp
    · rw [ENNReal.mul_top (ENNReal.ofReal_pos.mpr h0).ne']
      exact le_top

/-- **The Jensen bridge, summed**: `measuredCrossEntropy ≤ crossEntropy`.  The tighter Gibbs bound
`∑ᵢ −λᵢ log sᵢ` (dephased `σ`) is dominated by the genuine cross entropy `−Tr(ρ log σ)`. -/
lemma measuredCrossEntropy_le_crossEntropy (ρ σ : QState H) (hσ : σ.Faithful) :
    measuredCrossEntropy ρ σ ≤ crossEntropy ρ σ :=
  ENNReal.tsum_le_tsum fun i => ρ.ofReal_measuredTerm_le_lintegral σ hσ i

/-- **Klein's inequality (full Umegaki form).**  For a faithful `σ`, the von Neumann entropy is
bounded by the cross entropy: `S(ρ) ≤ −Tr(ρ log σ)` — equivalently the quantum relative entropy
`D(ρ‖σ) = crossEntropy(ρ,σ) − S(ρ) ≥ 0`.  Shipped as the ordering (a truncated-subtraction
`relativeEntropy ≥ 0` in `ℝ≥0∞` would be vacuous).  Composes the Gibbs (commuting-case) leg with the
tangent-line Jensen bridge. -/
theorem vonNeumannEntropy_le_crossEntropy (ρ σ : QState H) (hσ : σ.Faithful) :
    vonNeumannEntropy ρ ≤ crossEntropy ρ σ :=
  le_trans
    (ρ.vonNeumannEntropy_le_measuredCrossEntropy σ
      fun i => ρ.diagSigma_pos_of_faithful σ hσ i)
    (ρ.measuredCrossEntropy_le_crossEntropy σ hσ)

/-! ## Non-vacuity: `crossEntropy ρ ρ = S(ρ)` -/

/-- **`ρ`'s spectral measure at its own eigenvector is a point mass.**  `eᵢ` is a `λᵢ`-eigenvector,
so `E({λᵢ}) eᵢ = eᵢ`, giving `μ_{eᵢ}({λᵢ}) = ‖eᵢ‖² = 1`; a probability measure with a full atom is
the Dirac measure `δ_{λᵢ}`. -/
lemma spectralMeasure_self_eq_dirac (ρ : QState H) (i : eigenIndex ρ.toOp) :
    ρ.spectralMeasure (ρ.eigenbasis i) = Measure.dirac (ρ.eigenvalue i) := by
  haveI : IsProbabilityMeasure (ρ.spectralMeasure (ρ.eigenbasis i)) :=
    ρ.isProbabilityMeasure_spectralMeasure (ρ.eigenbasis.orthonormal.1 i)
  have hmem := ρ.mem_sigmaOp_domain (ρ.eigenbasis i)
  have heig : ρ.sigmaOp.toLinearPMap ⟨ρ.eigenbasis i, hmem⟩
      = (ρ.eigenvalue i : ℂ) • ρ.eigenbasis i := by
    rw [ρ.sigmaOp_apply (ρ.eigenbasis i) hmem, ρ.apply_eigenbasis i]
  have hself : (PVM.spectralPVM ρ.sigmaOp.selfAdjoint).proj {ρ.eigenvalue i}
      (measurableSet_singleton _) (ρ.eigenbasis i) = ρ.eigenbasis i :=
    spectralPVM_proj_singleton_eq_self_of_eigen ρ.sigmaOp.selfAdjoint (ρ.eigenbasis i) hmem heig
  have hatom1 : (ρ.spectralMeasure (ρ.eigenbasis i)) {ρ.eigenvalue i} = 1 := by
    have h := (PVM.spectralPVM ρ.sigmaOp.selfAdjoint).norm_sq_proj_apply {ρ.eigenvalue i}
      (measurableSet_singleton _) (ρ.eigenbasis i)
    rw [hself, ρ.eigenbasis.orthonormal.1 i, one_pow, ← spectralMeasure_eq] at h
    rw [← ENNReal.ofReal_toReal (measure_ne_top (ρ.spectralMeasure (ρ.eigenbasis i)) _), ← h,
      ENNReal.ofReal_one]
  refine Measure.ext fun s hs => ?_
  rw [Measure.dirac_apply' _ hs]
  by_cases hasin : ρ.eigenvalue i ∈ s
  · rw [Set.indicator_of_mem hasin, Pi.one_apply]
    exact le_antisymm ((measure_mono (Set.subset_univ s)).trans_eq measure_univ)
      (hatom1 ▸ measure_mono (Set.singleton_subset_iff.mpr hasin))
  · rw [Set.indicator_of_notMem hasin]
    have hsub : s ⊆ {ρ.eigenvalue i}ᶜ := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      rintro rfl
      exact hasin hx
    have hcompl : (ρ.spectralMeasure (ρ.eigenbasis i)) {ρ.eigenvalue i}ᶜ = 0 := by
      rw [measure_compl (measurableSet_singleton _) (measure_ne_top _ _), hatom1, measure_univ,
        tsub_self]
    exact le_antisymm ((measure_mono hsub).trans_eq hcompl) (zero_le)

/-- **Non-vacuity of the cross entropy**: `crossEntropy ρ ρ = S(ρ)`.  Against `ρ`'s own spectral
measures (point masses at the eigenvalues), the cross entropy collapses to the spectral form
`∑ᵢ negMulLog λᵢ` of the von Neumann entropy — so `crossEntropy` is a genuine quantity, not the
constant `+∞`.  (Correspondingly `D(ρ‖ρ) = 0`, the equality case of Klein's inequality.) -/
theorem crossEntropy_self (ρ : QState H) : crossEntropy ρ ρ = vonNeumannEntropy ρ := by
  rw [crossEntropy, vonNeumannEntropy_eq_tsum]
  refine tsum_congr fun i => ?_
  rw [ρ.spectralMeasure_self_eq_dirac i, lintegral_dirac,
    ← ENNReal.ofReal_mul (ρ.eigenvalue_nonneg i)]
  congr 1
  rw [Real.negMulLog]; ring

end QState

end Spectra.InformationGeometry.Quantum
