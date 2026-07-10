/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SpectralTheory.Calculus.FlowGenerator
import Spectra.Modular.Cocycle.ModularFlowVacuum
import Spectra.Modular.Cocycle.PolarIsometry
/-!
# The modular Hamiltonian: `generator (Δ^{it}) = log Δ`

The **modular flow** `Δ^{it} = modularFlow hcyc hsep` is Stone's `e^{it K}` for the self-adjoint
**modular Hamiltonian** `K`.  This file identifies that generator explicitly as the unbounded
Borel functional calculus of `Real.log` against the spectral measure of the modular operator
`Δ = modularOp M Ω`:

> `generator (modularFlow hcyc hsep) = logModularOp hcyc hsep = ∫ log s dE_Δ(s) = log Δ`.

This is the theorem the abstract KMS layer explicitly **declines** to prove
(`Spectra/Modular/KMS/UnitaryGroup.lean`: *"We never form `log Δ` nor prove `generator = ±log Δ`;
the labels `Δ^{it}` and `K = -log Δ` name the canonical implementation by convention."*).  Here the
naming convention becomes a theorem for the concrete Tomita–Takesaki flow.

## The proof

Everything is a corollary of the general spectral-flow theorem
`generator_eq_pmapOfPVM_of_flowSymbol` (`FlowGenerator.lean`): the modular flow is, on its own group
`genToGroup Δ`, the spectral exponential of the symbol `logExpSym t s = exp(i t log s)`
(`modularFlow_U_eq_spectralCalculus`), so its generator is `pmapOfPVM (genToGroup Δ) log`.

The one nontrivial obligation is **density of `D(log Δ)`**: `log` is unbounded near `0`, but `Δ > 0`
and injective, so its spectral measure is carried by `(0,∞)` (`borelMeasure_modular_Iio_zero`,
`borelMeasure_modular_singleton_zero`) where `log` is bounded on each away-from-zero band
`[1/(n+1), n+1]` — exactly the hypotheses of `pmapOfPVM_domain_dense_of_support_Ioi`.
-/

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace
open Spectra.QuantumMechanics.SpectralTheory
open Spectra.OneParameterUnitaryGroup Spectra.YosidaHille

namespace Spectra.TomitaTakesaki

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

/-! ## The real symbol `log` -/

/-- The complexified logarithm symbol `s ↦ (log s : ℂ)`. -/
noncomputable def logC : ℝ → ℂ := fun s => (Real.log s : ℂ)

/-- `logC` is measurable. -/
lemma measurable_logC : Measurable logC :=
  Complex.measurable_ofReal.comp Real.measurable_log

/-- `logC` is real: `conj (logC s) = logC s`. -/
lemma conj_logC : ∀ s, (starRingEnd ℂ) (logC s) = logC s :=
  fun s => Complex.conj_ofReal (Real.log s)

/-- `log` is bounded by `log (n+1)` on the away-from-zero band `[1/(n+1), n+1]`. -/
lemma logC_band_bound (n : ℕ) :
    ∀ s ∈ Set.Icc (((n : ℝ) + 1)⁻¹) ((n : ℝ) + 1), ‖logC s‖ ≤ Real.log ((n : ℝ) + 1) := by
  intro s hs
  rw [Set.mem_Icc] at hs
  obtain ⟨hlo, hhi⟩ := hs
  have _hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hinv : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
  have hspos : 0 < s := lt_of_lt_of_le hinv hlo
  have hup : Real.log s ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hspos hhi
  have hlow : Real.log (((n : ℝ) + 1)⁻¹) ≤ Real.log s := Real.log_le_log hinv hlo
  rw [Real.log_inv] at hlow
  rw [logC, Complex.norm_real, Real.norm_eq_abs, abs_le]
  exact ⟨by linarith, hup⟩

/-! ## The modular Hamiltonian `log Δ` -/

/-- **The modular Hamiltonian `log Δ`**, the unbounded functional calculus of `Real.log` against the
spectral measure of the modular operator `Δ = modularOp M Ω`. -/
noncomputable def logModularOp (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) : H →ₗ.[ℂ] H :=
  pmapOfPVM (genToGroup (modularOp_isSelfAdjoint hcyc hsep)) logC measurable_logC

/-- **`D(log Δ)` is dense.**  `Δ`'s spectral measure is carried by `(0,∞)`
(`borelMeasure_modular_Iio_zero`, `borelMeasure_modular_singleton_zero`), and `log` is bounded on
each band `[1/(n+1), n+1]` (`logC_band_bound`), so `pmapOfPVM_domain_dense_of_support_Ioi`
applies. -/
theorem logModularOp_domain_dense (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    Dense ((logModularOp hcyc hsep).domain : Set H) :=
  pmapOfPVM_domain_dense_of_support_Ioi (genToGroup (modularOp_isSelfAdjoint hcyc hsep)) logC
    measurable_logC (borelMeasure_modular_Iio_zero hcyc hsep)
    (borelMeasure_modular_singleton_zero hcyc hsep)
    (fun n => ⟨Real.log ((n : ℝ) + 1), logC_band_bound n⟩)

/-- **`log Δ` is self-adjoint** (real symbol + dense domain). -/
theorem logModularOp_isSelfAdjoint (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    IsSelfAdjoint (logModularOp hcyc hsep) :=
  pmapOfPVM_isSelfAdjoint_of_real (genToGroup (modularOp_isSelfAdjoint hcyc hsep)) logC
    measurable_logC conj_logC (logModularOp_domain_dense hcyc hsep)

/-! ## The modular Hamiltonian identity -/

/-- **`generator (Δ^{it}) = log Δ`.**  The generator of the Tomita–Takesaki modular flow is the
modular Hamiltonian `log Δ`, the honest unbounded functional calculus
`∫ log s dE_Δ(s)`.  A corollary
of the general spectral-flow generator theorem `generator_eq_pmapOfPVM_of_flowSymbol`, applied on
`Δ`'s own group with the symbol `logC`; the flow hypothesis is `modularFlow_U_eq_spectralCalculus`
(the flow is the spectral exponential of `logExpSym t = flowSymbol logC t`).

The `[Nontrivial H]` hypothesis is **not** a degeneracy of the generator identity itself
(the general
engine `generator_eq_pmapOfPVM_of_flowSymbol` is unconditional): it enters *solely* through the
Cayley/vacuum bridge `modularFlow_U_eq_spectralCalculus`, whose `stoneGroup = genToGroup` step needs
`Nontrivial H`. -/
theorem generator_modularFlow_eq_logModularOp [Nontrivial H]
    (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    generator (modularFlow hcyc hsep) = logModularOp hcyc hsep :=
  generator_eq_pmapOfPVM_of_flowSymbol logC (genToGroup (modularOp_isSelfAdjoint hcyc hsep))
    (modularFlow hcyc hsep) measurable_logC conj_logC (logModularOp_domain_dense hcyc hsep)
    (fun t => modularFlow_U_eq_spectralCalculus hcyc hsep t)

end Spectra.TomitaTakesaki
