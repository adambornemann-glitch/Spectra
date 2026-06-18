/-
Copyright (c) 2026 Spectra Project, Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Util.AssertNoSorry
import Spectra

/-!
# Axiom gate — every headline result is `sorry`-free

This module is a **compile-time gate**, not library content. It runs Mathlib's
`assert_no_sorry` on each result the [README](README.md) advertises as proved.
`assert_no_sorry` resolves the name (so a typo fails the build) and throws if the
declaration depends transitively on `sorryAx`.

Because `AxiomCheck` is a `@[default_target]` in [`lakefile.lean`](lakefile.lean), a
plain `lake build` — and therefore CI — fails the moment a `sorry` reaches any guarded
theorem. This converts Spectra's "the build is `sorry`-free" claim from a manual audit
into an enforced invariant.

To guard a new result, add an `assert_no_sorry` line below. The `#print axioms` block at
the end echoes the full axiom set of the crown jewels into the build log; the only axioms
that should ever appear are `propext`, `Classical.choice`, and `Quot.sound`.
-/

/-! ## Spectral theorem · Stone's theorem · Bochner · Herglotz -/

assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.spectralTheorem
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.spectralPVM
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.stonesFormula_spectralPVM
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.weak_first_moment
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.weak_second_moment
assert_no_sorry Spectra.StonesTheorem.stoneEquiv
assert_no_sorry Spectra.StonesTheorem.stoneEquivSpectral
assert_no_sorry Spectra.Bochner.bochner_theorem
assert_no_sorry Spectra.Bochner.GNS.gns_theorem
assert_no_sorry Spectra.Herglotz.helly_selection

/-! ## Essential spectrum · Weyl's theorem -/

assert_no_sorry Spectra.Essential.essSpectrum_subset_spectrum
assert_no_sorry Spectra.Essential.isClosed_essSpectrum
assert_no_sorry Spectra.Essential.essSpectrum_subset_of_isCompactOperator_resolvent_sub
assert_no_sorry Spectra.Essential.essSpectrum_eq_of_isCompactOperator_resolvent_sub
assert_no_sorry Spectra.Essential.isCompactOperator_resolvent_sub_of_isCompactOperator_perturb
assert_no_sorry Spectra.Essential.essSpectrum_eq_of_isCompactOperator_perturb

/-! ### σ_ess(−Δ) = [0, ∞) -/

assert_no_sorry Spectra.QuantumMechanics.Hydrogen.mem_essSpectrum_laplacian
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.essSpectrum_laplacian_subset_Ici
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.essSpectrum_laplacian

/-! ### Free resolvent as a Fourier multiplier -/

assert_no_sorry Spectra.QuantumMechanics.Hydrogen.fourierL2_selfAdjointResolvent
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.integral_exp_neg_mul_sin

/-! ### Radial disintegration (sphere integration infrastructure) -/

assert_no_sorry Spectra.SphereIntegral.integral_eq_integral_prod_toSphere
assert_no_sorry Spectra.SphereIntegral.integral_eq_integral_toSphere

/-! ## Quantum mechanics -/

assert_no_sorry Spectra.QuantumInfo.CHSH_lhv_bound
assert_no_sorry Spectra.QuantumCHSH.tsirelson_bound'
assert_no_sorry Spectra.QuantumMechanics.Heisenberg.heisenberg_uncertainty
assert_no_sorry Spectra.QuantumMechanics.Ehrenfest.ehrenfest_theorem
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.first_law
assert_no_sorry Spectra.QuantumMechanics.Dirac.diracHamiltonian_isSelfAdjoint
assert_no_sorry Spectra.QuantumMechanics.Dirac.diracHamiltonian_mass_gap
assert_no_sorry Spectra.QuantumMechanics.Hamiltonian.kato_rellich
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.hardy_inequality

/-! ## KMS condition & modular theory -/

assert_no_sorry Spectra.KMS.IsKMSState
assert_no_sorry Spectra.KMS.isKMSState_iff_imaginaryTime

/-! ## Information geometry -/

assert_no_sorry Spectra.InformationGeometry.RegularStatisticalModel.cramerRao_scalar
assert_no_sorry Spectra.InformationGeometry.TwiceDifferentiableModel.klDiv_hessian_eq_fisher

/-! ## Sobolev spaces -/

assert_no_sorry Spectra.Sobolev.meyers_serrin_approx
assert_no_sorry Spectra.Sobolev.sobolev_embedding_L6

/-! ## Axiom transparency

These print the full axiom set into the build log. Only `propext`, `Classical.choice`,
and `Quot.sound` should appear — anything else (especially `sorryAx`) is a red flag. -/

#print axioms Spectra.QuantumMechanics.SpectralTheory.spectralTheorem
#print axioms Spectra.StonesTheorem.stoneEquiv
#print axioms Spectra.Bochner.bochner_theorem
#print axioms Spectra.QuantumCHSH.tsirelson_bound'
