/-
Copyright (c) 2026 Spectra Project, Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Util.AssertNoSorry
import Spectra
-- The gated sector-reduction / eigenfunction-equation results below live in
-- `Spectrum.Eigenvalue` (renamed from the former `Spectrum.Basic`), which is already
-- part of the root `Spectra` import, so no extra direct import is needed here.

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
-- Eigenvalues ↔ spectral atoms: `range E({λ}) = ker(A − λ)` for self-adjoint `A`.
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.spectralPVM_sq_dist_integral
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.spectralPVM_proj_singleton_eq_self_of_eigen
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.spectralPVM_proj_singleton_apply_isEigen
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.spectralPVM_proj_singleton_eq_self_iff
assert_no_sorry Spectra.YosidaHille.stoneEquiv
assert_no_sorry Spectra.YosidaHille.stoneEquivSpectral
assert_no_sorry Spectra.Bochner.bochner_theorem
assert_no_sorry Spectra.Bochner.GNS.gns_theorem
assert_no_sorry Spectra.Herglotz.helly_selection

/-! ## Essential spectrum · Weyl's theorem -/

assert_no_sorry Spectra.Essential.essSpectrum_subset_spectrum
-- assert_no_sorry Spectra.Essential.isClosed_essSpectrum
assert_no_sorry Spectra.Essential.essSpectrum_subset_of_isCompactOperator_resolvent_sub
assert_no_sorry Spectra.Essential.essSpectrum_eq_of_isCompactOperator_resolvent_sub
assert_no_sorry Spectra.Essential.isCompactOperator_resolvent_sub_of_isCompactOperator_perturb
assert_no_sorry Spectra.Essential.essSpectrum_eq_of_isCompactOperator_perturb
assert_no_sorry Spectra.Essential.isSelfAdjoint_smul_real
assert_no_sorry Spectra.Essential.essSpectrum_smul_real
assert_no_sorry Spectra.Essential.selfAdjointResolvent_smul_real
assert_no_sorry Spectra.Essential.essSpectrum_smul_pos_Ici
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.halfLaplacian_isSelfAdjoint
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.essSpectrum_halfLaplacian

/-! ### σ_ess(−Δ) = [0, ∞) -/

assert_no_sorry Spectra.QuantumMechanics.Hydrogen.mem_essSpectrum_laplacian
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.essSpectrum_laplacian_subset_Ici
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.essSpectrum_laplacian

/-! ### Free resolvent as a Fourier multiplier -/

-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.fourierL2_selfAdjointResolvent
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.integral_exp_neg_mul_sin

/-! ### Radial disintegration (sphere integration infrastructure) -/

-- assert_no_sorry Spectra.SphereIntegral.integral_eq_integral_prod_toSphere
-- assert_no_sorry Spectra.SphereIntegral.integral_eq_integral_toSphere
-- assert_no_sorry Spectra.SphereIntegral.exists_linearIsometryEquiv_apply_eq

/-! ### Coulomb relative compactness (Track A toward σ_ess(H) = [0,∞)) -/

-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.memLp_inv_laplacianSymbol_sub
-- assert_no_sorry Spectra.CompactOperator.isCompactOperator_smulRight
-- assert_no_sorry Spectra.CompactOperator.isCompactOperator_sum_smulRight
-- assert_no_sorry Spectra.CompactOperator.memLp_section_ae
-- assert_no_sorry Spectra.CompactOperator.norm_integral_mul_sq_le
-- assert_no_sorry Spectra.CompactOperator.integral_norm_integralKernel_sq_le
-- assert_no_sorry Spectra.CompactOperator.memLp_kernelIntegral
-- assert_no_sorry Spectra.CompactOperator.L2_norm_sq_eq
-- assert_no_sorry Spectra.CompactOperator.integrable_kernel_mul
-- assert_no_sorry Spectra.CompactOperator.integralOperator
-- assert_no_sorry Spectra.CompactOperator.norm_integralOperator_le
-- assert_no_sorry Spectra.CompactOperator.integralOperator_add
-- assert_no_sorry Spectra.CompactOperator.integralOperator_smul
-- assert_no_sorry Spectra.CompactOperator.integralOperatorCLM
-- assert_no_sorry Spectra.CompactOperator.memLp_tensor
-- assert_no_sorry Spectra.CompactOperator.isCompactOperator_integralOperator_indicatorRect
-- assert_no_sorry Spectra.CompactOperator.rectSimple_dense
-- assert_no_sorry Spectra.CompactOperator.isCompactOperator_finset_sum
-- assert_no_sorry Spectra.CompactOperator.isCompactOperator_of_isRectSimple
-- assert_no_sorry Spectra.CompactOperator.isCompactOperator_integralOperator
-- assert_no_sorry Spectra.CompactOperator.memLp_kernel_mul_sub
-- assert_no_sorry Spectra.CompactOperator.eLpNorm_kernel_mul_sub
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.memL1_freeGreensFunction
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.memL2_freeGreensFunction
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.freeGreensL2
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.truncCoulomb_memLp
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.truncKernel_memLp
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.eLpNorm_truncKernel
-- assert_no_sorry Spectra.CompactOperator.young_L1_conv_L2
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.freeGreensFunctionL2
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.fourierL2_freeGreensFunctionL2
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.integrable_conv_integrand
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.young_R3
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.memLp_conv_L2_schwartz
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.fourier_conv_L2_schwartz
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.freeGreens_resolvent_kernel_schwartz
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.coulombResolvent
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.coulomb_hVW
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.truncCoulombBall_memLp
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.truncKernelG_memLp
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.hydrogen_essSpectrum_of_compact
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.hydrogen_essSpectrum_eq_Ici_of_compact
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.coulombResolvent_isCompact
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.hydrogen_essSpectrum

/-! ### Hydrogen bound states · the eigenfunction equation H ψ_{nℓm} = E_n ψ_{nℓm} (textbook −½Δ) -/

assert_no_sorry QuantumMechanics.Hydrogen.Spectrum.hydrogen_reduces_half
assert_no_sorry QuantumMechanics.Hydrogen.Spectrum.hydrogen_eigenfunction_eq

/-! ### Hydrogen continuous spectrum · σ_ess(H) = [0,∞) and no embedded eigenvalues (Kato) -/

assert_no_sorry QuantumMechanics.Hydrogen.Spectrum.hydrogen_continuous_spectrum
assert_no_sorry QuantumMechanics.Hydrogen.Spectrum.hydrogen_no_positive_eigenvalues

-- `hydrogen_discrete_spectrum` (in `Spectrum.Discrete`, kept out of the root `Spectra`
-- import) still carries a documented `sorry`: the remaining leaves are the
-- `chartRealization` intertwining and `reduced_radial_L2_quantized` analytic gap. Uncomment
-- the import and the gate below once that proof lands — it will then enforce sorry-freeness.
-- import Spectra.QuantumMechanics.Hydrogen.Spectrum.Discrete
-- assert_no_sorry QuantumMechanics.Hydrogen.Spectrum.hydrogen_discrete_spectrum

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
#print axioms QuantumMechanics.Hydrogen.Spectrum.hydrogen_no_positive_eigenvalues
#print axioms Spectra.YosidaHille.stoneEquiv
#print axioms Spectra.Bochner.bochner_theorem
#print axioms Spectra.QuantumCHSH.tsirelson_bound'
