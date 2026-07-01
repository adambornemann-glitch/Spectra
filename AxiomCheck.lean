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
-- `PVM.spectralPVM` is an alias for the line above (`SpectralTheory/Measure/PVM.lean`), guarded
-- under its own name since it is what the Born-rule/hydrogen-spectrum results actually import.
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.PVM.spectralPVM
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
-- A finite Borel measure is determined by its characteristic function; consumed directly inside
-- `bochner_theorem`'s proof.
assert_no_sorry Spectra.Fourier.fourier_uniqueness
assert_no_sorry Spectra.Bochner.GNS.gns_theorem
-- The abstract 3ε extension (strong continuity on a dense set ⟹ strong continuity everywhere),
-- load-bearing for `Modular/KMS/UnitaryGroup.lean`'s `invariantUnitaryGroup`.
assert_no_sorry Spectra.Bochner.GNS.strong_continuity_extends
assert_no_sorry Spectra.Herglotz.helly_selection
-- An absolutely continuous measure equals the Stieltjes measure of its CDF; load-bearing for
-- `Bochner/Borel/Identity/CauchyVague.lean`.
assert_no_sorry Spectra.Herglotz.withDensity_ofReal_eq_stieltjes_measure
-- Stone's theorem, self-adjointness half: the generator of a strongly continuous one-parameter
-- unitary group is self-adjoint, via the surjectivity-of-`A±iI` criterion and domain density.
assert_no_sorry Spectra.Resolvent.generator_isSelfAdjoint
assert_no_sorry Spectra.Resolvent.range_plus_i_eq_top
assert_no_sorry Spectra.Resolvent.range_minus_i_eq_top
assert_no_sorry Spectra.Resolvent.generatorDomain_dense_via_average
-- The resolvent `R(z) = (A - zI)⁻¹`: its operator bound and its defining right-inverse property.
assert_no_sorry Spectra.Resolvent.resolvent_bound
assert_no_sorry Spectra.Resolvent.resolvent_apply_mem_domain
assert_no_sorry Spectra.Resolvent.resolvent_sub_smul_apply
-- Off-axis arithmetic of `z = ± in` for `n : ℕ+`, feeding the Yosida approximants built from
-- `R(± in)` (`YosidaHille/Approximation/Helpers.lean`); load-bearing for `stoneEquiv` above.
assert_no_sorry Spectra.YosidaHille.Approximation.I_mul_pnat_im_ne_zero
assert_no_sorry Spectra.YosidaHille.Approximation.neg_I_mul_pnat_im_ne_zero
assert_no_sorry Spectra.YosidaHille.Approximation.norm_I_mul_pnat

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

/-! ### Radial × angular tensor decomposition L²(ℝ³) ≅ ⊕_ℓ RadialL2 ⊗ V_ℓ -/

-- The two headline unitaries: R ↦ rR (radial substitution) and the spherical-harmonic
-- expansion of L²(ℝ³) into angular-momentum sectors.
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.Decomposition.radialReduction
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.Decomposition.sphericalDecomposition

/-! ### Classical radial equation · quantization, explicit eigenfunctions, uniqueness -/

assert_no_sorry QuantumMechanics.Hydrogen.RadialEq.radial_quantization
assert_no_sorry QuantumMechanics.Hydrogen.RadialEq.radial_continuum
assert_no_sorry QuantumMechanics.Hydrogen.RadialEq.radial_eigenvalue_eq
assert_no_sorry QuantumMechanics.Hydrogen.RadialEq.radial_wavefunction_orthonormal
assert_no_sorry QuantumMechanics.Hydrogen.RadialEq.radial_wavefunction_norm
assert_no_sorry QuantumMechanics.Hydrogen.RadialEq.radial_bound_state_unique
assert_no_sorry QuantumMechanics.Hydrogen.RadialEq.hydrogenEigenvalue_tendsto

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
-- Bell's original (1964) inequality — the historical precursor to CHSH.
assert_no_sorry Spectra.BellTheorem.bell_1964_inequality
-- Wigner's (1970) set-theoretic form — same physical conclusion via finite combinatorics.
assert_no_sorry Spectra.BellTheorem.wigner_inequality
-- The Popescu–Rohrlich box hits the algebraic maximum CHSH value 4, exceeding both the classical
-- and quantum (Tsirelson) bounds while satisfying no-signaling exactly.
assert_no_sorry Spectra.BellTheorem.prBox_chsh_eq_four
assert_no_sorry Spectra.BellTheorem.prBox_chsh_exceeds_tsirelson
-- Clauser–Horne (1974): the historically prior generalization of CHSH to sub-normalized
-- [0,1]-valued detection probabilities.
assert_no_sorry Spectra.BellTheorem.ch_bound
assert_no_sorry Spectra.QuantumMechanics.Heisenberg.heisenberg_uncertainty
assert_no_sorry Spectra.QuantumMechanics.Schrodinger.schrodingerEquation
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
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.hydrogen_isSelfAdjoint
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.coulomb_kato_rellich

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

-- Cayley Transform Bridge, P0: `spectralPVM` (the canonical PVM every consumer uses) IS the
-- projection-valued measure of the Cayley/Borel group `stoneGroup`, and its diagonal measures are
-- the pushforward of the Riesz–Markov measure of the bounded Cayley transform — von Neumann's own
-- derivation of the unbounded spectral theorem from the bounded unitary one, made explicit.
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.groupPVM_eq_toPVM
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.spectralPVM_eq_groupPVM_stoneGroup
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.spectralPVM_eq_stoneGroup_toPVM
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.spectralPVM_proj_eq_spectralProjection_stoneGroup
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.spectralPVM_diag_eq_map_cayleySpectralMeasure

-- P5: the spectral theorem, proved a SECOND, INDEPENDENT way via Cayley/Riesz–Markov — existence
-- witnessed by `groupPVM (stoneGroup hA)`, mentioning `genToGroup` nowhere; uniqueness reused
-- verbatim from `spectralPVM_unique` (already fully generic). This is the historical point of the
-- Cayley transform, not merely an identification with the Yosida-built spectral theorem.
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.selfAdjointResolvent_eq_stoneGroup
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.cayleyPVM_resolvent_formula
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.groupPVM_stoneGroup_eq_spectralPVM_independent
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.spectralTheoremCayley

-- P4 (rescoped): closes the square `pmapOfPVM`/`spectralCalculus` (group-generic, already
-- multiplicative — SpectralTheory/Calculus/Bounded.lean) ↔ `borelCalculus`/`cfcHom` (Cayley-
-- specific, already matches Mathlib's cfc — CayleyTransform/BorelCalculus.lean). Identifies the
-- library's own unbounded functional calculus with Mathlib's continuous functional calculus,
-- pulled back through the Cayley transform.
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.spectralCalculus_stoneGroup_eq_borelCalculus
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.spectralCalculus_stoneGroup_eq_cfcHom
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.pmapOfPVM_apply_eq_borelCalculus_of_bounded
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.pmapOfPVM_apply_eq_cfcHom_of_bounded

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
-- R2 bounded-symbol product law: `pmapOfPVM` collapses to the already-multiplicative bounded
-- calculus `spectralCalculus` on bounded symbols (truncations stabilize past the global bound).
-- Closes the product law `(∫f)(∫g)=∫fg` for BOUNDED f,g only — the general unbounded case (needed
-- for `(Δ^{½})²=Δ` in general) remains open; see `PMapBounded.lean`'s scope-honesty note.
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.integrable_sq_of_bounded
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.mem_pmapDomain_of_bounded
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.pmapOfPVM_apply_eq_spectralCalculus_of_bounded
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.pmapOfPVM_mul_of_bounded
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
-- R4a field 5: `Δ^{it} Ω = Ω` (the modular flow fixes the vacuum), via the Stone/genToGroup bridge
-- `spectralCalculus_stoneGroup_eq_borelCalculus` + the spectral atom `E_Δ({1}) Ω = Ω`.
assert_no_sorry Spectra.TomitaTakesaki.modularFlow_fixes_vacuum
-- R4a field 3 foundation: the Tomita involution `S̃² = 1` on the core `M Ω` (`S̃ (a Ω) = (star a) Ω`,
-- hence `S̃ (S̃ (a Ω)) = a Ω`), plus the polar helper `J (Δ^{½} x) = ofConj (S x)`. The genuine content
-- seeding `J² = 1` (field 3); the range-vs-core bridge closing `J² = 1` is the remaining node.
assert_no_sorry Spectra.TomitaTakesaki.sTilde_core
assert_no_sorry Spectra.TomitaTakesaki.sTilde_involutive_core
assert_no_sorry Spectra.TomitaTakesaki.modularConjugation_apply_modularSqrt
-- Field-3 keystone spike result: the Tomita involution `S̃² = 1` upgraded from the core `M Ω` to the
-- whole domain `D(S)` of the closure (`S̃ y ∈ D(S)` and `S̃ (S̃ y) = y`), via the continuous
-- conjugate-linear graph-symmetry `swapConj`. No `Δ`/`Δ^{½}`/adjoint calculus. (Closing `J² = 1`
-- still needs the polar relation on the full `D(Δ^{½})` — the Route B calculus.)
assert_no_sorry Spectra.TomitaTakesaki.sTilde_closure_mem_domain
assert_no_sorry Spectra.TomitaTakesaki.sTilde_closure_involutive
-- R4a field 3, Route B gate (HC1): the modular square root `Δ^{½}` is SELF-ADJOINT — von Neumann's
-- deficiency criterion `isSelfAdjoint_of_surjective_addSub` fed by symmetry + surjectivity of `Δ^{½} ± i`
-- (bounded resolvent `Φ(1/(√±i))`). The single blocker of the J²=1 endgame; unblocks `(Δ^{½})²=Δ`.
-- Plus the reusable NEW infrastructure: the mixed bounded/unbounded product law for the PVM calculus.
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.pmapOfPVM_spectralCalculus_of_mul_bounded
assert_no_sorry Spectra.TomitaTakesaki.modularSqrt_isSelfAdjoint
-- R4a field 3, HC2: (Δ^{½})² = Δ (the modular square root squares to Δ), via a closed-graph
-- argument on the now-self-adjoint Δ^{½} + the mixed product law. Unblocks the J²=1 endgame
-- reduction. Ships the reusable unbounded output-density `μ_{(∫f dP)ξ} = μ_ξ.withDensity ‖f‖²`.
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.borelMeasure_pmapOfPVM_eq_withDensity
assert_no_sorry Spectra.TomitaTakesaki.modularSqrt_mem_domain_of_mem_modularOp
assert_no_sorry Spectra.TomitaTakesaki.modularSqrt_sq_apply
-- R4a field 3, polar-uniqueness DAG node 1.2 (the KILL-SPIKE — GREEN): the `s ↦ s²` resolvent
-- identity `(A² − z)⁻¹ = Φ(1/(s²−z))` and its diagonal `⟪ξ,(A²−z)⁻¹ξ⟫ = ∫(s²−z)⁻¹ dμ^E_ξ`, via the
-- mixed product law on the `s²` symbol. Validates the `posSqrt_unique` route on Spectra's calculus.
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.resolvent_sq_identity
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.resolvent_sq_mem
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.inner_resolvent_sq

/-! ## Inner-product `ℓ²`-pairing estimates (shared, trace-class-free)

General `RCLike`-valued inner-product summability facts underpinning the trace bounds: inner
summability from square-summability, and the weighted arithmetic–geometric estimate that yields the
sharp Cauchy–Schwarz constant without any `Lᵖ`/Hölder machinery. -/
assert_no_sorry Spectra.QuantumMechanics.Channels.summable_inner_of_summable_sq
assert_no_sorry Spectra.QuantumMechanics.Channels.weighted_norm_tsum_inner_le

/-! ## Operator algebra · bounded polar decomposition `T = U |T|`

First brick of the trace-class / von Neumann predual development (discharge-first route to the
Tomita–Takesaki fundamental theorem). `|T| = CFC.abs T`, the polar isometry identity `‖|T|x‖ = ‖Tx‖`,
and the partial isometry `U` with `U |T| = T` — the last built by hand since Mathlib's
`LinearIsometry.extend` is finite-dimensional only. -/
assert_no_sorry Spectra.QuantumMechanics.Channels.norm_absOp_apply
assert_no_sorry Spectra.QuantumMechanics.Channels.denseRange_absOpCorestrict
assert_no_sorry Spectra.QuantumMechanics.Channels.polarIsometry_absOp
assert_no_sorry Spectra.QuantumMechanics.Channels.polar_decomposition
-- Trace of a positive operator: the per-term identity `‖T^{1/2} x‖² = ⟪x, T x⟫` behind
-- `tr T = ∑ᵢ ‖T^{1/2} eᵢ‖²`.
assert_no_sorry Spectra.QuantumMechanics.Channels.sqrtOp_comp_self
assert_no_sorry Spectra.QuantumMechanics.Channels.norm_sqrtOp_sq
-- Basis-independence of the positive trace `∑ᵢ ‖T^{1/2} eᵢ‖²` (Parseval + Tonelli): the trace does
-- not depend on the Hilbert basis, so the trace norm `‖T‖₁ = tr |T|` is well-defined.
assert_no_sorry Spectra.QuantumMechanics.Channels.hasSum_norm_inner_sq
assert_no_sorry Spectra.QuantumMechanics.Channels.posTrace_indep
-- Trace norm `‖T‖₁ = tr |T|` and the trace-class predicate `IsTraceClass T := tr |T| ≠ ∞`, packaged
-- over a canonical Hilbert basis (`stdHilbertBasis`) but proven basis-independent (`traceNorm_eq`,
-- `isTraceClass_iff`). Absolute homogeneity `‖c • T‖₁ = ‖c‖ · ‖T‖₁` reduces to the `ℝ≥0∞`-level
-- identity `tr |c • T| = ‖c‖ · tr |T|` (`posTrace_absOp_smul`), via the per-term expansion
-- `tr S = ∑ᵢ re ⟪eᵢ, S eᵢ⟫` for `0 ≤ S` (`posTrace_eq_tsum_ofReal`).
assert_no_sorry Spectra.QuantumMechanics.Channels.posTrace_eq_tsum_ofReal
assert_no_sorry Spectra.QuantumMechanics.Channels.posTrace_absOp_smul
assert_no_sorry Spectra.QuantumMechanics.Channels.traceNorm_eq
assert_no_sorry Spectra.QuantumMechanics.Channels.isTraceClass_iff
assert_no_sorry Spectra.QuantumMechanics.Channels.traceNorm_nonneg
assert_no_sorry Spectra.QuantumMechanics.Channels.traceNorm_zero
assert_no_sorry Spectra.QuantumMechanics.Channels.isTraceClass_zero
assert_no_sorry Spectra.QuantumMechanics.Channels.traceNorm_of_nonneg
assert_no_sorry Spectra.QuantumMechanics.Channels.traceNorm_absOp
assert_no_sorry Spectra.QuantumMechanics.Channels.traceNorm_smul
assert_no_sorry Spectra.QuantumMechanics.Channels.isTraceClass_iff_summable
-- Trace-class hard-core Stage A (partial-isometry infrastructure): the Hilbert–Schmidt sum is
-- adjoint-invariant (`∑ᵢ ‖A eᵢ‖² = ∑ᵢ ‖A⋆ eᵢ‖²`), the polar partial isometry `U` is a contraction, and
-- the initial-space identities `U⋆ U = P_K` and `U⋆ T = |T|` (load-bearing for trace-norm duality and
-- the triangle inequality).
assert_no_sorry Spectra.QuantumMechanics.Channels.tsum_enorm_apply_sq_adjoint
assert_no_sorry Spectra.QuantumMechanics.Channels.norm_polarPartial_eq
assert_no_sorry Spectra.QuantumMechanics.Channels.norm_polarIsometry_le_one
assert_no_sorry Spectra.QuantumMechanics.Channels.polarIsometry_adjoint_comp_self
assert_no_sorry Spectra.QuantumMechanics.Channels.polarIsometry_adjoint_comp
-- Trace-class hard-core Stage C (minimal Hilbert–Schmidt ideal): the predicate `IsHilbertSchmidt`
-- (`∑ᵢ ‖A eᵢ‖² < ∞`) with basis-independence, `A⋆` HS ↔ `A` HS, `|A|^{1/2}` HS ↔ `A` trace-class, and
-- the two-sided-ideal closure `B∘A`, `A∘B` HS — the factorization toolkit for cyclicity `tr(AB)=tr(BA)`.
assert_no_sorry Spectra.QuantumMechanics.Channels.hsSum_indep
assert_no_sorry Spectra.QuantumMechanics.Channels.isHilbertSchmidt_iff
assert_no_sorry Spectra.QuantumMechanics.Channels.isHilbertSchmidt_iff_summable
assert_no_sorry Spectra.QuantumMechanics.Channels.isHilbertSchmidt_adjoint
assert_no_sorry Spectra.QuantumMechanics.Channels.isHilbertSchmidt_sqrtOp_absOp
assert_no_sorry Spectra.QuantumMechanics.Channels.IsHilbertSchmidt.comp_left
assert_no_sorry Spectra.QuantumMechanics.Channels.IsHilbertSchmidt.comp_right
-- Trace-class hard-core Stage B (the complex trace functional): `trace T = ∑ᵢ ⟪eᵢ, T eᵢ⟫` with the
-- twisted-inner-product identity (`trace_summand_polar`), diagonal summability for trace-class `T`,
-- linearity, the trace bound `|tr T| ≤ ‖T‖₁` (`norm_trace_le_traceNorm`), the duality-functional
-- bound `|tr (B T)| ≤ ‖B‖ · ‖T‖₁` (`norm_trace_comp_le`, consumed by `B(H) = (TraceClass H)⋆`), and
-- the positive-operator bridge `tr S = ((tr |S|).toReal : ℂ)` (`trace_of_nonneg`).
assert_no_sorry Spectra.QuantumMechanics.Channels.trace_summand_polar
assert_no_sorry Spectra.QuantumMechanics.Channels.trace_summable
assert_no_sorry Spectra.QuantumMechanics.Channels.trace_add
assert_no_sorry Spectra.QuantumMechanics.Channels.trace_smul
assert_no_sorry Spectra.QuantumMechanics.Channels.norm_trace_le_traceNorm
assert_no_sorry Spectra.QuantumMechanics.Channels.norm_trace_comp_le
assert_no_sorry Spectra.QuantumMechanics.Channels.trace_of_nonneg
-- Trace-class hard-core Stage D (cyclicity of the trace): the Hilbert–Schmidt case `tr (X Y) = tr (Y X)`
-- via a Fubini swap of the absolutely convergent double sum, and the general case `tr (A B) = tr (B A)`
-- (`A` trace-class, `B` bounded) via the `A = (U |A|^{1/2}) |A|^{1/2}` Hilbert–Schmidt factorization.
assert_no_sorry Spectra.QuantumMechanics.Channels.trace_comp_comm_hs
assert_no_sorry Spectra.QuantumMechanics.Channels.trace_comp_comm
-- The contraction–trace bound `∑ᵢ ‖⟪W eᵢ, S eᵢ⟫‖ ≤ ‖S‖₁` (`‖W‖ ≤ 1`), the single-fixed-`W` estimate.
assert_no_sorry Spectra.QuantumMechanics.Channels.tsum_norm_inner_comp_le
-- Trace-class hard-core Stage E (the triangle inequality): `tr |S+T| ≤ tr |S| + tr |T|` in `ℝ≥0∞` via
-- the polar decomposition of `S + T` with one fixed partial isometry, closure of trace-class under
-- addition, and the triangle inequality `‖S + T‖₁ ≤ ‖S‖₁ + ‖T‖₁`.
assert_no_sorry Spectra.QuantumMechanics.Channels.posTrace_absOp_add_le
assert_no_sorry Spectra.QuantumMechanics.Channels.isTraceClass_add
assert_no_sorry Spectra.QuantumMechanics.Channels.traceNorm_add_le
-- Trace-class hard-core Stage F (toward the Banach space): the trace class is a `ℂ`-submodule of `B(H)`
-- (`traceClassSubmodule`, via `isTraceClass_smul`), and the operator norm is dominated by the trace
-- norm `‖T‖ ≤ ‖T‖₁` (`norm_le_traceNorm`) — the comparison making `‖·‖₁`-Cauchy sequences `‖·‖`-Cauchy.
assert_no_sorry Spectra.QuantumMechanics.Channels.isTraceClass_smul
assert_no_sorry Spectra.QuantumMechanics.Channels.traceNorm_neg
assert_no_sorry Spectra.QuantumMechanics.Channels.traceClassSubmodule
assert_no_sorry Spectra.QuantumMechanics.Channels.norm_le_traceNorm
-- Trace-class hard-core Stage F (F2, the normed space): the trace-class operators, as the
-- non-reducible type synonym `TraceClass H` of `↥(traceClassSubmodule H)` carrying the trace norm
-- `‖·‖₁`, form a `ℂ`-normed space (`NormedAddCommGroup`/`NormedSpace` via `NormedSpace.Core`); the
-- operator norm is dominated by the trace norm on the synonym (`TraceClass.norm_toOp_le`).
assert_no_sorry Spectra.QuantumMechanics.Channels.TraceClass.toOp
assert_no_sorry Spectra.QuantumMechanics.Channels.TraceClass.isTraceClass
assert_no_sorry Spectra.QuantumMechanics.Channels.TraceClass.core
assert_no_sorry Spectra.QuantumMechanics.Channels.TraceClass.instNormedAddCommGroup
assert_no_sorry Spectra.QuantumMechanics.Channels.TraceClass.instNormedSpace
assert_no_sorry Spectra.QuantumMechanics.Channels.TraceClass.norm_toOp_le
-- Trace-class hard-core Stage F (F3, completeness): the Fatou / lower-semicontinuity estimate — the
-- operator-norm limit of a trace-norm-bounded sequence is trace-class with the limiting bound
-- (`isTraceClass_and_traceNorm_le_of_tendsto`) — yields that `TraceClass H` is complete, hence a
-- `ℂ`-Banach space (`TraceClass.instCompleteSpace`).
assert_no_sorry Spectra.QuantumMechanics.Channels.isTraceClass_sub
assert_no_sorry Spectra.QuantumMechanics.Channels.tendsto_re_inner_absOp_of_tendsto
assert_no_sorry Spectra.QuantumMechanics.Channels.isTraceClass_and_traceNorm_le_of_tendsto
assert_no_sorry Spectra.QuantumMechanics.Channels.TraceClass.instCompleteSpace

-- Quantum channels (Schrödinger picture): complete positivity via the block-quadratic-form
-- criterion on finite arrays of trace-class operators (`IsPositiveMatrix`/`IsCompletelyPositive`),
-- the bundled `QuantumChannel` structure, and the identity channel.
assert_no_sorry Spectra.QuantumMechanics.Channels.isPositiveMatrix_zero_iff
assert_no_sorry Spectra.QuantumMechanics.Channels.blockForm_one
assert_no_sorry Spectra.QuantumMechanics.Channels.isPositiveMatrix_one_iff
assert_no_sorry Spectra.QuantumMechanics.Channels.IsCompletelyPositive.isPositive
assert_no_sorry Spectra.QuantumMechanics.Channels.QuantumChannel.id_toFun_apply

/-! ## Information geometry -/

assert_no_sorry Spectra.InformationGeometry.RegularStatisticalModel.cramerRao_scalar
assert_no_sorry Spectra.InformationGeometry.TwiceDifferentiableModel.klDiv_hessian_eq_fisher

/-! ## Sobolev spaces -/

assert_no_sorry Spectra.Sobolev.meyers_serrin_approx
assert_no_sorry Spectra.Sobolev.sobolev_embedding_L6
-- Meyers–Serrin mollification step: bump convolution simultaneously approximates a compactly
-- supported L² function and its weak derivative(s) by a smooth compactly supported function.
assert_no_sorry Spectra.Sobolev.mollify_compactly_supported
assert_no_sorry Spectra.Sobolev.mollify_compactly_supported_multi
-- Density chain L² ← C_c ← C_c^∞: the capstone and its own load-bearing dependency, consumed by
-- `DuBoisReymond.lean`, `DensityResults.lean`, and `MeyersCommon.lean`.
assert_no_sorry Spectra.Sobolev.dense_test_functions_L2
assert_no_sorry Spectra.Sobolev.dense_continuous_compactSupport_L2

/-! ## Axiom transparency

These print the full axiom set into the build log. Only `propext`, `Classical.choice`,
and `Quot.sound` should appear — anything else (especially `sorryAx`) is a red flag. -/

#print axioms Spectra.QuantumMechanics.SpectralTheory.spectralTheorem
#print axioms QuantumMechanics.Hydrogen.Spectrum.hydrogen_no_positive_eigenvalues
#print axioms Spectra.YosidaHille.stoneEquiv
#print axioms Spectra.Bochner.bochner_theorem
#print axioms Spectra.QuantumCHSH.tsirelson_bound'
#print axioms Spectra.QuantumMechanics.Channels.traceNorm_smul
#print axioms Spectra.QuantumMechanics.Channels.polarIsometry_adjoint_comp
#print axioms Spectra.QuantumMechanics.Channels.IsHilbertSchmidt.comp_right
#print axioms Spectra.QuantumMechanics.Channels.norm_trace_le_traceNorm
#print axioms Spectra.QuantumMechanics.Channels.norm_trace_comp_le
#print axioms Spectra.QuantumMechanics.Channels.trace_comp_comm
#print axioms Spectra.QuantumMechanics.Channels.traceNorm_add_le
#print axioms Spectra.QuantumMechanics.Channels.norm_le_traceNorm
#print axioms Spectra.QuantumMechanics.Channels.TraceClass.instNormedAddCommGroup
#print axioms Spectra.QuantumMechanics.Channels.TraceClass.instNormedSpace
#print axioms Spectra.QuantumMechanics.Channels.TraceClass.norm_toOp_le
#print axioms Spectra.QuantumMechanics.Channels.isTraceClass_and_traceNorm_le_of_tendsto
#print axioms Spectra.QuantumMechanics.Channels.TraceClass.instCompleteSpace
#print axioms Spectra.QuantumMechanics.Channels.isPositiveMatrix_one_iff
#print axioms Spectra.QuantumMechanics.Channels.IsCompletelyPositive.isPositive
#print axioms Spectra.QuantumMechanics.Channels.QuantumChannel.id_toFun_apply
