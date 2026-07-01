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

/-! ### Hydrogen discrete eigenspaces · degeneracy states are eigenvectors, span = eigenspace,
and the spectral projection `E({Eₙ})` onto the `n²`-dimensional bound-state subspace -/

assert_no_sorry QuantumMechanics.Hydrogen.Spectrum.degenFamily_mem_ker
assert_no_sorry QuantumMechanics.Hydrogen.Spectrum.eigenspace_subset_span
assert_no_sorry QuantumMechanics.Hydrogen.Spectrum.hydrogen_eigenspace_eq_span
assert_no_sorry QuantumMechanics.Hydrogen.Spectrum.hydrogen_spectral_projection_discrete
assert_no_sorry QuantumMechanics.Hydrogen.Spectrum.hydrogen_spectral_projection_finrank

/-! ### Spectral theory · discreteness (Weyl hard half) and hydrogen eigenfunction completeness -/

assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.mem_pointSpectrum_of_mem_spectrum_notMem_essSpectrum
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.spectralPVM_proj_eq_zero_of_subset_resolventSet
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.selfAdjointResolvent_residue_proj_singleton
-- Tier C: general resolvent on the open resolvent set, analytic there.
assert_no_sorry Spectra.Resolvent.isOpen_resolventSet
assert_no_sorry Spectra.Resolvent.resolventOf_identity
assert_no_sorry Spectra.Resolvent.resolventOf_eq_resolvent
assert_no_sorry Spectra.Resolvent.resolventOf_analyticOnNhd
-- Tier C2: each negative hydrogen eigenvalue is isolated in the spectrum.
assert_no_sorry QuantumMechanics.Hydrogen.Spectrum.hydrogen_punctured_disk_subset_resolventSet
-- Tier C3/C4: the resolvent is meromorphic — simple pole at each Eₙ, analytic off [0,∞).
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.meromorphicAt_resolventOf_of_isolated
assert_no_sorry QuantumMechanics.Hydrogen.Spectrum.hydrogen_meromorphicAt_eigenvalue
assert_no_sorry QuantumMechanics.Hydrogen.Spectrum.hydrogen_meromorphicOn
-- Tier C5: the residue at each Eₙ is the spectral projection −E({Eₙ}).
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.tendsto_sub_smul_resolventOf
assert_no_sorry QuantumMechanics.Hydrogen.Spectrum.hydrogen_residue_eigenvalue
assert_no_sorry QuantumMechanics.Hydrogen.Spectrum.mem_eigenvalues_of_mem_spectrum_neg
assert_no_sorry QuantumMechanics.Hydrogen.Spectrum.hydrogen_eigenfunction_complete

/-! ## Quantum mechanics -/

assert_no_sorry Spectra.QuantumInfo.CHSH_lhv_bound
assert_no_sorry Spectra.QuantumCHSH.tsirelson_bound'
assert_no_sorry Spectra.QuantumMechanics.Heisenberg.heisenberg_uncertainty
assert_no_sorry Spectra.QuantumMechanics.Ehrenfest.ehrenfest_theorem
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.first_law
assert_no_sorry Spectra.QuantumMechanics.Pauli.pauliX_hermitian
assert_no_sorry Spectra.QuantumMechanics.Pauli.pauliY_hermitian
assert_no_sorry Spectra.QuantumMechanics.Pauli.pauliZ_hermitian
assert_no_sorry Spectra.QuantumMechanics.Pauli.pauliX_isSelfAdjoint
assert_no_sorry Spectra.QuantumMechanics.Pauli.pauliY_isSelfAdjoint
assert_no_sorry Spectra.QuantumMechanics.Pauli.pauliZ_isSelfAdjoint
assert_no_sorry Spectra.QuantumMechanics.Pauli.pauliX_sq
assert_no_sorry Spectra.QuantumMechanics.Pauli.pauliY_sq
assert_no_sorry Spectra.QuantumMechanics.Pauli.pauliZ_sq
assert_no_sorry Spectra.QuantumMechanics.Pauli.pauliXY_anticommute
assert_no_sorry Spectra.QuantumMechanics.Pauli.pauliXZ_anticommute
assert_no_sorry Spectra.QuantumMechanics.Pauli.pauliYZ_anticommute
assert_no_sorry Spectra.QuantumMechanics.Pauli.pauliXY_commutator
assert_no_sorry Spectra.QuantumMechanics.Pauli.pauliYZ_commutator
assert_no_sorry Spectra.QuantumMechanics.Pauli.pauliZX_commutator
assert_no_sorry Spectra.QuantumMechanics.Dirac.diracHamiltonian_isSelfAdjoint
assert_no_sorry Spectra.QuantumMechanics.Dirac.diracHamiltonian_mass_gap
assert_no_sorry Spectra.QuantumMechanics.Hamiltonian.kato_rellich
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.hardy_inequality
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.hardy_constant_sharp

/-! ### Joint spectral measures · strong commutativity (Born rule, relational layer)

Strong commutativity ⟺ commutation of the unitary groups, and the **full** joint-PVM
equivalence `stronglyCommute_iff_jointPVM` (the multivariate spectral theorem — both directions:
strong commutativity ⟺ a joint projective PVM on `ℝ²` with the right cylinder marginals), plus the
**correlation identity** `jointBornMeasure_correlation` (`∫ xy dμ_ξ = ⟪ξ, A(Bξ)⟫.re`, the bridge to
Bell/CHSH).  All `sorry`-free and axiom-clean. -/

assert_no_sorry Spectra.QuantumMechanics.BornRule.stronglyCommute_iff_groups_commute
assert_no_sorry Spectra.QuantumMechanics.BornRule.stronglyCommute_of_jointPVM
assert_no_sorry Spectra.QuantumMechanics.BornRule.jointBornMeasure_fst
assert_no_sorry Spectra.QuantumMechanics.BornRule.jointBornMeasure_snd
assert_no_sorry Spectra.QuantumMechanics.BornRule.isProbabilityMeasure_jointBornMeasure
assert_no_sorry Spectra.QuantumMechanics.BornRule.stronglyCommute_iff_jointPVM
assert_no_sorry Spectra.QuantumMechanics.BornRule.jointBornMeasure_correlation

/-! ## KMS condition & modular theory -/

assert_no_sorry Spectra.KMS.IsKMSState
assert_no_sorry Spectra.KMS.isKMSState_iff_imaginaryTime

-- von Neumann's `T⋆T` theorem: the modular operator `Δ = S⋆S` is self-adjoint and `≥ 0`
-- (Tomita–Takesaki milestone H3 — the GATE of the modular-flow / RN-cocycle construction).
assert_no_sorry Spectra.TomitaTakesaki.modularOp_isSelfAdjoint
assert_no_sorry Spectra.TomitaTakesaki.modularOp_nonneg
-- R1-link: the modular flow `Δ^{it}` constructed from `Δ` (Cayley transform → Borel calculus).
assert_no_sorry Spectra.TomitaTakesaki.modularFlow_unitary
assert_no_sorry Spectra.TomitaTakesaki.modularFlow_group_law
-- R2: the unbounded (Cauchy-limit) functional calculus `∫ f dP` of a spectral PVM — the engine
-- for the modular square root `Δ^{½}`. Operator + its `L²` isometry and pairing characterization.
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.pmapOfPVM
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.pmapTrunc_cauchySeq
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.pmapOfPVM_apply_tendsto
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.norm_sq_pmapOfPVM_apply
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.inner_pmapOfPVM
-- R2 cont.: the quadratic-form pairing `⟪ξ,(∫f dP)ξ⟫=∫f dμ_ξ`, symmetry of `∫f dP` for real `f`,
-- and positivity `0≤Re⟪ξ,(∫f dP)ξ⟫` for `f≥0` — the "real f ⟹ self-adjoint, ≥0" prerequisites.
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.inner_self_pmapOfPVM
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.pmapOfPVM_isFormalAdjoint_self
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.re_inner_self_pmapOfPVM_nonneg
-- R2 square root: spectral-measure restriction, support of a `≥0` generator on `[0,∞)`, and the
-- form identity `‖A^{½}x‖² = Re⟪x,Ax⟫` — the engine for `Δ^{½}` and `‖Δ^{½}x‖=‖Sx‖` (R3 input).
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.borelMeasure_spectralProjection_restrict
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.borelMeasure_Iio_zero_eq_zero
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.norm_sq_pmapOfPVM_sqrt
-- R2 capstone: the modular square root `Δ^{½} = pmapOfPVM (genToGroup Δ) √` and the polar isometry
-- `‖Δ^{½}x‖ = ‖Sx‖` (the input `LinearEquiv.extendOfIsometry` needs for `W` in R3 / `S = JΔ^{½}`).
assert_no_sorry Spectra.TomitaTakesaki.modularSqrt
assert_no_sorry Spectra.TomitaTakesaki.norm_sq_modularSqrt
assert_no_sorry Spectra.TomitaTakesaki.norm_modularSqrt_eq_norm_tomita
-- R3 polar-decomposition substrate (`S = J Δ^{½}`): injectivity of `S` and `Δ` (`inj`), and the
-- density inputs to `W = extendOfIsometry` — `range S` dense, and `S(D(Δ))` dense (`D(Δ)` a core
-- for `S`, from `1+Δ` surjective). (Source density `Δ^{½}(D(Δ))` awaits R2-completion.)
assert_no_sorry Spectra.TomitaTakesaki.tomitaClosure_injective
assert_no_sorry Spectra.TomitaTakesaki.modularOp_injective
assert_no_sorry Spectra.TomitaTakesaki.tomitaClosure_range_dense
assert_no_sorry Spectra.TomitaTakesaki.denseRange_tomitaOnModularDomain
-- R3 completion: the source density `Δ^{½}(D(Δ))` (direct spectral argument, no product law), then
-- the polar isometry `W : H ≃ₗᵢ Conj H`, the modular conjugation `J = ofConj ∘ W : H ≃ₗᵢ⋆ H`, and
-- the polar decomposition `S = J Δ^{½}`.
assert_no_sorry Spectra.TomitaTakesaki.denseRange_modularSqrtOnModularDomain
assert_no_sorry Spectra.TomitaTakesaki.modularW
assert_no_sorry Spectra.TomitaTakesaki.modularConjugation
assert_no_sorry Spectra.TomitaTakesaki.tomita_eq_modularConjugation_modularSqrt
-- R4a vacuum-fixing facts: `Δ Ω = Ω`, `Δ^{½} Ω = Ω`, `J Ω = Ω` (Tomita's `J Ω = Ω`), each from the
-- eigenvector `Δ Ω = Ω` (direct `S Ω = toConj Ω`, `S⋆ toConj Ω = Ω`) through the spectral atom and
-- the polar decomposition `S = J Δ^{½}`.
assert_no_sorry Spectra.TomitaTakesaki.modularOp_vacuum
assert_no_sorry Spectra.TomitaTakesaki.modularSqrt_vacuum
assert_no_sorry Spectra.TomitaTakesaki.modularConjugation_fixes_vacuum

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
