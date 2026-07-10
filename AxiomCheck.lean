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

/-! ## Resolvent module tree — headline results not yet individually gated above
(house-cleaning pass, 2026-07-03/04: `Spectra/Resolvent/**`). -/

-- `Defs.lean`: the Neumann series `Σ (zA)ⁿ` for the resolvent inverse.
assert_no_sorry Spectra.Resolvent.opNorm_pow_le
assert_no_sorry Spectra.Resolvent.opNorm_pow_tendsto_zero
assert_no_sorry Spectra.Resolvent.isUnit_one_sub
assert_no_sorry Spectra.Resolvent.neumannSeries_summable
assert_no_sorry Spectra.Resolvent.neumannSeries_hasSum
assert_no_sorry Spectra.Resolvent.tsum_eq_neumannSeries
assert_no_sorry Spectra.Resolvent.neumannSeries_mul_left
assert_no_sorry Spectra.Resolvent.neumannSeries_mul_right
assert_no_sorry Spectra.Resolvent.im_ne_zero_of_near
-- `Integral/GroupIntegration.lean`: the resolvent as a Laplace-type integral of the unitary group.
assert_no_sorry Spectra.Resolvent.continuous_unitary_apply
assert_no_sorry Spectra.Resolvent.integrable_exp_neg_unitary
assert_no_sorry Spectra.Resolvent.norm_integral_exp_neg_unitary_le
assert_no_sorry Spectra.Resolvent.resolventIntegralPlus
assert_no_sorry Spectra.Resolvent.resolventIntegralMinus
assert_no_sorry Spectra.Resolvent.norm_resolventIntegralPlus_le
assert_no_sorry Spectra.Resolvent.norm_resolventIntegralMinus_le
-- `Integral/Limits.lean`: elementary Laplace-transform tail limits feeding the
-- group-integral route.
assert_no_sorry Spectra.Resolvent.tendsto_exp_sub_one_div
assert_no_sorry Spectra.Resolvent.integrableOn_Ici_of_Ici_zero
assert_no_sorry Spectra.Resolvent.integral_Ici_split_of
-- `LowerBound.lean` / `NormExpansion.lean`: the symmetric-operator norm estimates
-- `‖(A - (λ ± i)I)φ‖ ≥ ‖φ‖` underlying deficiency-index and resolvent-bound arguments.
assert_no_sorry Spectra.Resolvent.lower_bound_estimate
assert_no_sorry Spectra.Resolvent.inner_self_im_eq_zero_of_symmetric
assert_no_sorry Spectra.Resolvent.cross_term_re_eq_zero_of_symmetric
assert_no_sorry Spectra.Resolvent.norm_sq_sub_smul_of_symmetric
assert_no_sorry Spectra.Resolvent.norm_sq_sub_I_smul
assert_no_sorry Spectra.Resolvent.norm_sq_add_I_smul
assert_no_sorry Spectra.Resolvent.norm_le_norm_sub_I_smul
assert_no_sorry Spectra.Resolvent.norm_le_norm_add_I_smul
-- `SpecialCases.lean`: the resolvent specialized to `z = ±i`
-- (existence/uniqueness/bound/right-inverse).
assert_no_sorry Spectra.Resolvent.resolventAtImaginary_unique
assert_no_sorry Spectra.Resolvent.resolventAtImaginary_bound
assert_no_sorry Spectra.Resolvent.resolventAtImaginary_left_inverse
assert_no_sorry Spectra.Resolvent.resolventAtI
assert_no_sorry Spectra.Resolvent.resolventAtNegI
assert_no_sorry Spectra.Resolvent.resolvent_at_i_unique
assert_no_sorry Spectra.Resolvent.resolvent_at_neg_i_unique
assert_no_sorry Spectra.Resolvent.resolvent_at_i_bound
assert_no_sorry Spectra.Resolvent.resolvent_at_neg_i_bound
assert_no_sorry Spectra.Resolvent.resolvent_at_i_left_inverse
assert_no_sorry Spectra.Resolvent.resolvent_at_neg_i_left_inverse
-- `Range/Orthogonal.lean` / `Range/ClosedRange.lean`: `ran(A ∓ iI)` orthogonality and closedness.
assert_no_sorry Spectra.Resolvent.weak_eigenvalue_of_orthogonal_to_range
assert_no_sorry Spectra.Resolvent.orthogonal_range_eq_zero
assert_no_sorry Spectra.Resolvent.preimage_cauchySeq
assert_no_sorry Spectra.Resolvent.range_sub_smul_closed
-- `Range/Surjectivity.lean`: symmetric with deficiency indices (0,0) ⟹
-- `ran(A - zI) = H` for all `z`.
assert_no_sorry Spectra.Resolvent.self_adjoint_range_all_z
assert_no_sorry Spectra.Resolvent.rangeSubmodule
assert_no_sorry Spectra.Resolvent.range_sub_smul_dense
assert_no_sorry Spectra.Resolvent.resolvent_unique
assert_no_sorry Spectra.Resolvent.solution_unique
-- `Range.lean` / `Identities.lean`: the resolvent as a function, its
-- defining/uniqueness identities, commutation, adjoint symmetry, and analytic
-- continuity in `z`.
assert_no_sorry Spectra.Resolvent.resolventSolution
assert_no_sorry Spectra.Resolvent.resolventSolution_mem
assert_no_sorry Spectra.Resolvent.resolventSolution_eq
assert_no_sorry Spectra.Resolvent.resolventFun
assert_no_sorry Spectra.Resolvent.resolvent_identity
assert_no_sorry Spectra.Resolvent.resolvent_tendsto
assert_no_sorry Spectra.Resolvent.resolvent_commute
assert_no_sorry Spectra.Resolvent.resolvent_adjoint
assert_no_sorry Spectra.Resolvent.resolvent_inner_diag_conj
-- `Spectrum.lean` / `Analytic.lean`: the resolvent set via `im z ≠ 0`, and the `HasSum` form of the
-- Neumann-series resolvent expansion.
assert_no_sorry Spectra.Resolvent.mem_resolventSet_of_im_ne_zero
assert_no_sorry Spectra.Resolvent.mem_resolventSet_of_isFormalAdjoint_of_surjective
assert_no_sorry Spectra.Resolvent.resolventFun_hasSum
-- `Range/NumericalRangeSurjectivity.lean` / `NumericalRangeSpectrum.lean`: the numerical-range
-- analogue of the resolvent-existence/uniqueness/bound package above.
assert_no_sorry Spectra.Resolvent.numericalRange_solution_unique
assert_no_sorry Spectra.Resolvent.numResolvent_bound
assert_no_sorry Spectra.Resolvent.numResolvent_apply_mem_domain
assert_no_sorry Spectra.Resolvent.numResolvent_sub_smul_apply
-- `BoundedBelow.lean`: the existence/uniqueness backbone of the PVM-free Weyl-criterion gluing.
assert_no_sorry Spectra.Resolvent.existsUnique_sub_smul_eq_of_boundedBelow
-- `Diagonal/IntegralZ/{Defs,Tendsto,Shift,Bulk,DiffQuotient,GeneratorLim,Basic}.lean`: the
-- generator-recovery-by-Laplace-integral construction `resolventIntegralZ`, its unitary-shift and
-- bulk/boundary difference-quotient limits, and its identification with the abstract resolvent.
assert_no_sorry Spectra.Resolvent.resolventIntegralZ
assert_no_sorry Spectra.Resolvent.expZ_orbit_continuous
assert_no_sorry Spectra.Resolvent.integrable_expZ_unitary
assert_no_sorry Spectra.Resolvent.unitary_apply_expZ_integral
assert_no_sorry Spectra.Resolvent.tendsto_cexp_mul_sub_one_div
assert_no_sorry Spectra.Resolvent.tendsto_integral_Ici_expZ_unitary
assert_no_sorry Spectra.Resolvent.tendsto_average_integral_expZ_unitary
assert_no_sorry Spectra.Resolvent.tendsto_average_integral_expZ_unitary_neg
assert_no_sorry Spectra.Resolvent.unitary_shift_resolventIntegralZ
assert_no_sorry Spectra.Resolvent.unitary_shift_resolventIntegralZ_neg
assert_no_sorry Spectra.Resolvent.genZ_target_eq
assert_no_sorry Spectra.Resolvent.genZ_scalar
assert_no_sorry Spectra.Resolvent.genZ_bulk_pos
assert_no_sorry Spectra.Resolvent.genZ_bulk_neg
assert_no_sorry Spectra.Resolvent.genZ_diffQuotient_pos
assert_no_sorry Spectra.Resolvent.genZ_diffQuotient_neg
assert_no_sorry Spectra.Resolvent.generator_limit_resolventIntegralZ
assert_no_sorry Spectra.Resolvent.resolventIntegralZ_eq_resolvent
-- `SpectralRepresentation.lean` / `Diagonal/Basic.lean`: the resolvent as the Cauchy transform of
-- the spectral measure, its diagonal matrix element, and the Herglotz/Laplace representation.
assert_no_sorry Spectra.Resolvent.resolvent_eq_spectralCalculus
assert_no_sorry Spectra.Resolvent.inner_resolvent_diag_eq_integral
assert_no_sorry Spectra.Resolvent.im_inner_resolvent_diag
assert_no_sorry Spectra.Resolvent.resolvent_diag_laplace
assert_no_sorry Spectra.Resolvent.im_resolvent_diag
assert_no_sorry Spectra.Resolvent.laplace_exp
assert_no_sorry Spectra.Resolvent.cauchy_kernel_laplace_neg_im
assert_no_sorry Spectra.Resolvent.resolvent_continuous_at_height
assert_no_sorry Spectra.Resolvent.resolvent_diag_lower_laplace
assert_no_sorry Spectra.Resolvent.resolvent_diag_upper_eq_conj
-- `Residue.lean`: the bridge identifying `selfAdjointResolvent` with the totalized `resolventOf`,
-- feeding the already-gated `selfAdjointResolvent_residue_proj_singleton` below.
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.selfAdjointResolvent_eq_resolventOf

/-! ## Numerical range · spectrum ⊆ closure(numerical range) -/

assert_no_sorry Spectra.Operator.numericalRange_range_isClosed
assert_no_sorry Spectra.Operator.numericalRange_conj_notMem_of_notMem
assert_no_sorry Spectra.Operator.numericalRange_range_dense
assert_no_sorry Spectra.Resolvent.numericalRange_range_all_z
assert_no_sorry Spectra.Resolvent.numericalRange_mem_resolventSet
-- The marquee theorem: the spectrum of a self-adjoint operator lies inside the closure of its
-- numerical range, via a genuine resolvent construction (injective + closed range + dense range
-- glued into a bounded two-sided inverse).
assert_no_sorry Spectra.Resolvent.spectrum_subset_closure_numericalRange

/-! ## Essential self-adjointness · Kato-Rellich companion (sums on a common domain) -/

-- Generic closability backbone (Lane A extraction): any operator with a densely-defined formal
-- adjoint is closable; the classical `D(T*)` dense ⟹ `T` closable criterion; and the bridge
-- identifying Mathlib's `LinearPMap.HasCore` with topological density of the restricted graph.
assert_no_sorry Spectra.Operator.isClosable_of_isFormalAdjoint
assert_no_sorry Spectra.Operator.isClosable_of_dense_adjoint_domain
assert_no_sorry Spectra.Operator.hasCore_iff_topologicalClosure_graph
assert_no_sorry Spectra.Operator.mem_closure_graph_of_hasCore
-- The bounded ⟺ closed loop (Lane A): norm-bounded on a closed domain ⟹ closed graph
-- (Reed–Simon VIII.1 at `domain = ⊤`), and conversely everywhere-defined + closed ⟹ bounded,
-- via Mathlib's closed graph theorem (`ContinuousLinearMap.ofIsClosedGraph`).
assert_no_sorry Spectra.Operator.isClosed_of_bound_of_isClosed_domain
assert_no_sorry Spectra.Operator.isClosed_of_bound_of_domain_eq_top
assert_no_sorry Spectra.Operator.exists_bound_of_isClosed_of_domain_eq_top
assert_no_sorry Spectra.Operator.symmetric_isClosable
assert_no_sorry Spectra.Operator.closure_le_adjoint
assert_no_sorry Spectra.Operator.Submodule.adjoint_topologicalClosure_eq
assert_no_sorry Spectra.Operator.closure_adjoint_eq_adjoint
-- The double adjoint (Reed–Simon VIII.1(b)): at the graph level `g.adjoint.adjoint =
-- g.topologicalClosure` (skew-swaps compose to `-1`, double orthocomplement is closure), hence
-- `T** = T̄` for densely-defined `T` with densely-defined adjoint — `T** = T` when `T` is
-- closed, and unconditionally `T** = T̄` for symmetric `T`. Plus adjoint antitonicity.
assert_no_sorry Spectra.Operator.adjoint_le_adjoint_of_le
assert_no_sorry Spectra.Operator.Submodule.adjoint_adjoint
assert_no_sorry Spectra.Operator.Submodule.isClosed_adjoint
assert_no_sorry Spectra.Operator.adjoint_adjoint_eq_closure
assert_no_sorry Spectra.Operator.adjoint_adjoint_eq_self
assert_no_sorry Spectra.Operator.adjoint_adjoint_eq_closure_of_isFormalAdjoint
-- The classical closability criterion as an IFF (RS VIII.1(a)): closable ⟺ D(T*) dense. The
-- necessity half puts `(0, ψ)` for `ψ ⊥ D(T*)` into `Γ(T)ᵃᵃ = Γ(T)‾ = Γ(T̄)`, forcing `ψ = 0`;
-- plus `T** = T̄` restated for closable `T`.
assert_no_sorry Spectra.Operator.dense_adjoint_domain_of_isClosable
assert_no_sorry Spectra.Operator.isClosable_iff_dense_adjoint_domain
assert_no_sorry Spectra.Operator.adjoint_adjoint_eq_closure_of_isClosable
-- The dense-range von Neumann criterion for essential self-adjointness: symmetric + dense domain
-- + dense range of `B ± i` (not necessarily surjective) already gives `B.closure` self-adjoint.
assert_no_sorry Spectra.Operator.isEssentiallySelfAdjoint_of_denseRange_addSub
-- The Kato-Rellich companion: essential self-adjointness of a sum on a common domain, reduced to
-- the deficiency condition for the sum itself (deliberately not automatic — Nelson's
-- counterexample, see `Operator/CommonCoreSum.lean`'s docstring).
assert_no_sorry Spectra.Operator.isEssentiallySelfAdjoint_sumOp_of_denseRange_addSub

/-! ## Deficiency subspaces and indices (von Neumann's self-adjoint extension theory, N1–N4) -/

-- N₊(A) = ker(A* - i) = ran(A + i)ᗮ, N₋(A) = ker(A* + i) = ran(A - i)ᗮ, unconditional for any
-- densely-defined `A` (no symmetry hypothesis needed).
assert_no_sorry Spectra.Operator.deficiencySubspacePlus_eq_orthogonal
assert_no_sorry Spectra.Operator.deficiencySubspaceMinus_eq_orthogonal
-- Deficiency indices `n±(A) := Module.rank ℂ N±(A)` vanish for self-adjoint `A`.
assert_no_sorry Spectra.Operator.deficiencyIndexPlus_eq_zero_of_isSelfAdjoint
assert_no_sorry Spectra.Operator.deficiencyIndexMinus_eq_zero_of_isSelfAdjoint
-- Cross-lane unification: both deficiency subspaces trivial is exactly the dense-range hypothesis
-- of `isEssentiallySelfAdjoint_of_denseRange_addSub` above.
assert_no_sorry Spectra.Operator.deficiencySubspacesBot_iff_denseRange_addSub
-- Von Neumann extension theory (N3): the extension `A_V = A*|_{D(A) ⊔ (1-V)N₊}` along a unitary
-- `V : N₊(A) ≃ₗᵢ N₋(A)`, its symmetry, and its (essential) self-adjointness — self-adjoint for
-- closed `A`, essentially self-adjoint with no closedness hypothesis.
assert_no_sorry Spectra.Operator.vonNeumannExtension
assert_no_sorry Spectra.Operator.le_vonNeumannExtension
assert_no_sorry Spectra.Operator.vonNeumannExtension_apply_add_defect
assert_no_sorry Spectra.Operator.vonNeumannExtension_isFormalAdjoint
assert_no_sorry Spectra.Operator.vonNeumannExtension_isSelfAdjoint
assert_no_sorry Spectra.Operator.vonNeumannExtension_isEssentiallySelfAdjoint
-- Von Neumann's self-adjoint extension theorem (N4, unitary-equivalence phrasing): a symmetric
-- densely-defined `A` admits a self-adjoint extension iff `N₊(A) ≃ₗᵢ N₋(A)`. The "only if" half
-- restricts the Cayley transform of the extension along `Submodule.map_orthogonal_equiv`.
assert_no_sorry Spectra.Operator.nonempty_deficiencyEquiv_of_le_isSelfAdjoint
assert_no_sorry Spectra.Operator.exists_le_isSelfAdjoint_of_nonempty_deficiencyEquiv
assert_no_sorry Spectra.Operator.exists_le_isSelfAdjoint_iff_nonempty_deficiencyEquiv
-- Von Neumann's CLASSIFICATION (N3d): the correspondence `V ↦ A_V` is a bijection —
-- completeness (every self-adjoint extension is the von Neumann extension at the deficiency
-- identification its own Cayley transform induces; closure thereof for non-closed `A`) plus
-- injectivity, packaged as `∃!` and as an explicit `Equiv`.
assert_no_sorry Spectra.Operator.vonNeumannExtension_inducedDeficiencyEquiv_le
assert_no_sorry Spectra.Operator.eq_closure_vonNeumannExtension_inducedDeficiencyEquiv
assert_no_sorry Spectra.Operator.eq_vonNeumannExtension_inducedDeficiencyEquiv
assert_no_sorry Spectra.Operator.vonNeumannExtension_injective
assert_no_sorry Spectra.Operator.existsUnique_vonNeumannExtension_eq
assert_no_sorry Spectra.Operator.selfAdjointExtensionEquiv
-- The classical characterization closing the loop: essential self-adjointness ⟺ EXACTLY ONE
-- self-adjoint extension (forward: closures are minimal + self-adjoint operators are maximal;
-- converse: nontrivial deficiency spaces of `Ā` would give two distinct von Neumann extensions
-- via the `-1` twist + injectivity of `V ↦ A_V`), plus the ≥2-extensions dichotomy.
assert_no_sorry Spectra.Operator.existsUnique_le_isSelfAdjoint_of_isEssentiallySelfAdjoint
assert_no_sorry Spectra.Operator.isEssentiallySelfAdjoint_of_existsUnique_le_isSelfAdjoint
assert_no_sorry Spectra.Operator.isEssentiallySelfAdjoint_iff_existsUnique_le_isSelfAdjoint
assert_no_sorry Spectra.Operator.exists_ne_of_not_isEssentiallySelfAdjoint
-- The FIRST VON NEUMANN FORMULA: for closed symmetric densely-defined `A`,
-- `D(A*) = D(A) ⊔ N₊(A) ⊔ N₋(A)` — with the decomposition unique (`∃!`), graph-orthogonal
-- (`⟪u,v⟫ + ⟪A*u,A*v⟫ = 0` across the three summands), and the adjoint acting as
-- `A*(ψ + η + ξ) = Aψ + iη - iξ`; for general symmetric `A`, `D(A*) = D(Ā) ⊔ N₊(A) ⊔ N₋(A)`
-- via `N±(Ā) = N±(A)`.
assert_no_sorry Spectra.Operator.deficiencySubspacePlus_closure
assert_no_sorry Spectra.Operator.deficiencySubspaceMinus_closure
assert_no_sorry Spectra.Operator.graphInner_domain_deficiencySubspacePlus
assert_no_sorry Spectra.Operator.graphInner_domain_deficiencySubspaceMinus
assert_no_sorry Spectra.Operator.graphInner_deficiencySubspaces
assert_no_sorry Spectra.Operator.adjoint_domain_cases
assert_no_sorry Spectra.Operator.vonNeumannFormula
assert_no_sorry Spectra.Operator.adjoint_apply_add_deficiency
assert_no_sorry Spectra.Operator.eq_zero_of_add_deficiency_eq_zero
assert_no_sorry Spectra.Operator.existsUnique_deficiency_decomposition
assert_no_sorry Spectra.Operator.vonNeumannFormula_closure
assert_no_sorry Spectra.Operator.eq_zero_of_mem_closure_add_deficiency_eq_zero
-- The SECOND VON NEUMANN FORMULA: the boundary form of `A*` collapses to the defect components
-- (`⟪A*u,w⟫ - ⟪u,A*w⟫ = -2i(⟪η,η'⟫ - ⟪ξ,ξ'⟫)`), the partial von Neumann extension
-- `A_V = A*|_{D(A) ⊔ (1-V)F}` along an isometry `V : F →ₗᵢ N₋(A)` on `F ≤ N₊(A)` is a symmetric
-- extension, and — for closed `A` — EVERY symmetric extension `B ≥ A` arises this way
-- (`exists_eq_vonNeumannExtensionOn`), with `F` and `V` recoverable from the operator
-- (injectivity of the correspondence).
assert_no_sorry Spectra.Operator.adjoint_boundaryForm
assert_no_sorry Spectra.Operator.adjoint_boundaryForm_defect
assert_no_sorry Spectra.Operator.vonNeumannExtensionOn
assert_no_sorry Spectra.Operator.le_vonNeumannExtensionOn
assert_no_sorry Spectra.Operator.vonNeumannExtensionOn_apply_add_defect
assert_no_sorry Spectra.Operator.vonNeumannExtensionOn_isFormalAdjoint
-- compatibility: the partial construction at `F = N₊` with a full unitary is definitionally the
-- original `vonNeumannExtension`.
assert_no_sorry Spectra.Operator.vonNeumannExtensionOn_toLinearIsometry
assert_no_sorry Spectra.Operator.le_adjoint_of_le_of_isFormalAdjoint
assert_no_sorry Spectra.Operator.eq_zero_of_mem_domain_of_mem_deficiencySubspaceMinus
assert_no_sorry Spectra.Operator.defect_partner_unique
assert_no_sorry Spectra.Operator.inducedDefectIsometry
assert_no_sorry Spectra.Operator.domain_eq_vonNeumannDomainOn_induced
assert_no_sorry Spectra.Operator.eq_vonNeumannExtensionOn_induced
assert_no_sorry Spectra.Operator.exists_eq_vonNeumannExtensionOn
assert_no_sorry Spectra.Operator.inducedDefectDomain_vonNeumannExtensionOn
assert_no_sorry Spectra.Operator.vonNeumannExtensionOn_inj_apply
-- Which partial von Neumann extensions are self-adjoint (endgame plan Ⓡ2): exactly the full
-- deficiency unitaries — `IsSelfAdjoint A_V ↔ F = N₊(A) ∧ Surjective V` for closed `A`.
-- ⟸ re-runs the surjectivity engine (no cast along `F = N₊` ever happens); ⟹ is a direct
-- range-orthogonality argument needing no closedness and no classification machinery.
assert_no_sorry Spectra.Operator.vonNeumannExtensionOn_isSelfAdjoint
assert_no_sorry Spectra.Operator.deficiencySubspacePlus_le_of_vonNeumannExtensionOn_isSelfAdjoint
assert_no_sorry Spectra.Operator.surjective_of_vonNeumannExtensionOn_isSelfAdjoint
assert_no_sorry Spectra.Operator.vonNeumannExtensionOn_isSelfAdjoint_iff
-- Which partial von Neumann extensions are CLOSED (endgame plan Ⓡ1): exactly those with closed
-- `F` — via graph-Pythagoras (`‖u‖² + ‖A*u‖²` splits over the first-formula decomposition,
-- `norm_sq_add_deficiency_decomposition`, symmetry-free), a triple-Cauchy transfer for ⟸, and
-- the first formula's unique decomposition for ⟹. Closed symmetric extensions ↔ isometries on
-- closed subspaces of N₊(A): the textbook classification is now complete.
assert_no_sorry Spectra.Operator.norm_sq_add_deficiency_decomposition
assert_no_sorry Spectra.Operator.norm_sq_graph_defect
assert_no_sorry Spectra.Operator.vonNeumannExtensionOn_isClosed_of_isClosed
assert_no_sorry Spectra.Operator.isClosed_of_vonNeumannExtensionOn_isClosed
assert_no_sorry Spectra.Operator.vonNeumannExtensionOn_isClosed_iff
-- VON NEUMANN'S CONJUGATION CRITERION (Reed–Simon X.3): a symmetric densely-defined operator
-- commuting with a conjugation (antiunitary involution) admits self-adjoint extensions — the
-- conjugation swaps N₊ ↔ N₋, restricts to an antiunitary equivalence, and the general
-- Hilbert-basis transport `nonempty_linearIsometryEquiv_of_antiunitary` (antiunitarily
-- equivalent Hilbert spaces are unitarily equivalent) feeds von Neumann's extension theorem.
-- Covers Schrödinger operators with real potentials.
-- The PVM-free Weyl criterion (endgame plan Ⓦ): `λ ∈ spectrum A` ⟺ approximate eigensequence,
-- proved via the parametric bounded-below core — closed range from a closed graph + lower bound
-- (no symmetry), dense range at real λ for self-adjoint A, and the generic
-- bounded-below + surjective ⟹ resolvent-point gluing. Drops the former
-- `SpectralTheory.Essential` dependency of `Operator/WeylCriterion.lean` entirely.
assert_no_sorry Spectra.Resolvent.range_isClosed_of_boundedBelow
assert_no_sorry Spectra.Resolvent.range_dense_of_boundedBelow_real
assert_no_sorry Spectra.Resolvent.sub_smul_injective_of_boundedBelow
assert_no_sorry Spectra.Resolvent.mem_resolventSet_of_boundedBelow_surjective
assert_no_sorry Spectra.Resolvent.mem_resolventSet_of_boundedBelow_real
assert_no_sorry Spectra.Operator.mem_spectrum_iff_exists_weylSequence
assert_no_sorry Spectra.Operator.nonempty_linearIsometryEquiv_of_antiunitary
assert_no_sorry Spectra.Operator.deficiencySubspacePlus_isClosed
assert_no_sorry Spectra.Operator.deficiencySubspaceMinus_isClosed
assert_no_sorry Spectra.Operator.conj_mem_deficiencySubspaceMinus
assert_no_sorry Spectra.Operator.conj_mem_deficiencySubspacePlus
assert_no_sorry Spectra.Operator.conjDeficiencyEquiv
assert_no_sorry Spectra.Operator.exists_le_isSelfAdjoint_of_conjugation
-- Off-axis arithmetic of `z = ± in` for `n : ℕ+`, feeding the Yosida approximants built from
-- `R(± in)` (`YosidaHille/Approximation/Helpers.lean`); load-bearing for `stoneEquiv` above.
assert_no_sorry Spectra.YosidaHille.Approximation.I_mul_pnat_im_ne_zero
assert_no_sorry Spectra.YosidaHille.Approximation.neg_I_mul_pnat_im_ne_zero
assert_no_sorry Spectra.YosidaHille.Approximation.norm_I_mul_pnat
-- Strong convergence of the Yosida approximants `Aₙ`, `Aₙ⁻`, `Aₙˢʸᵐ` to the generator `A` on its
-- domain, and `Aₙ`'s commutation with every resolvent (`YosidaHille/Approximation/Convergence/
-- Approximants.lean`).
assert_no_sorry Spectra.YosidaHille.Approximation.yosidaApprox_eq_J_comp_A
assert_no_sorry Spectra.YosidaHille.Approximation.yosidaApprox_tendsto_on_domain
assert_no_sorry Spectra.YosidaHille.Approximation.yosidaApproxNeg_eq_JNeg_A
assert_no_sorry Spectra.YosidaHille.Approximation.yosidaApproxNeg_tendsto_on_domain
assert_no_sorry Spectra.YosidaHille.Approximation.yosidaApproxSym_eq_avg
assert_no_sorry Spectra.YosidaHille.Approximation.yosidaApproxSym_tendsto_on_domain
assert_no_sorry Spectra.YosidaHille.Approximation.yosidaApprox_commutes_resolvent
-- Self-adjointness of the symmetric Yosida approximant and skew-adjointness of `I` times it —
-- together what makes `exp(i·Aₙˢʸᵐ·t)` unitary (`YosidaHille/Approximation/Symmetry.lean`).
assert_no_sorry Spectra.YosidaHille.Approximation.yosidaApproxSym_selfAdjoint
assert_no_sorry Spectra.YosidaHille.Approximation.I_smul_yosidaApproxSym_skewAdjoint
-- The bounded-operator exponential `expBounded` (power series `Σₖ (tB)ᵏ/k!`) and its analytic
-- backbone (`YosidaHille/Approximation/ExpBounded/Helpers.lean`).
assert_no_sorry Spectra.YosidaHille.Approximation.expBounded_summable
assert_no_sorry Spectra.YosidaHille.Approximation.expBounded_norm_summable
assert_no_sorry Spectra.YosidaHille.Approximation.expBounded_norm_bound
assert_no_sorry Spectra.YosidaHille.Approximation.expBounded_at_zero
assert_no_sorry Spectra.YosidaHille.Approximation.expBounded_at_zero'
assert_no_sorry Spectra.YosidaHille.Approximation.expBounded_zero_op
assert_no_sorry Spectra.YosidaHille.Approximation.expBounded_eq_exp
assert_no_sorry Spectra.YosidaHille.Approximation.expBounded_smul_commute
assert_no_sorry Spectra.YosidaHille.Approximation.B_commute_expBounded
assert_no_sorry Spectra.YosidaHille.Approximation.expBounded_add_smul
-- Unitarity of exponentials of skew-adjoint operators, specialized to `exp(i·Aₙˢʸᵐ·t)`
-- (`YosidaHille/Approximation/ExpBounded/Unitary.lean`).
assert_no_sorry Spectra.YosidaHille.Approximation.expBounded_skewAdjoint_unitary
assert_no_sorry Spectra.YosidaHille.Approximation.expBounded_mem_unitary
assert_no_sorry Spectra.YosidaHille.Approximation.smul_I_skewSelfAdjoint
assert_no_sorry Spectra.YosidaHille.Approximation.expBounded_yosidaApproxSym_unitary
assert_no_sorry Spectra.YosidaHille.Approximation.expBounded_yosidaApproxSym_isometry
assert_no_sorry Spectra.YosidaHille.Approximation.expBounded_hasDerivAt_zero
assert_no_sorry Spectra.YosidaHille.Approximation.expBounded_hasDerivAt

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

assert_no_sorry Spectra.QuantumMechanics.Hydrogen.fourierL2_selfAdjointResolvent
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.integral_exp_neg_mul_sin

/-! ### Radial disintegration (sphere integration infrastructure) -/

assert_no_sorry Spectra.SphereIntegral.integral_eq_integral_prod_toSphere
assert_no_sorry Spectra.SphereIntegral.integral_eq_integral_toSphere
assert_no_sorry Spectra.SphereIntegral.exists_linearIsometryEquiv_apply_eq

/-! ### Coulomb relative compactness (Track A toward σ_ess(H) = [0,∞)) -/

assert_no_sorry Spectra.QuantumMechanics.Hydrogen.memLp_inv_laplacianSymbol_sub
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
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.memL1_freeGreensFunction
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.memL2_freeGreensFunction
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.freeGreensL2
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.truncCoulomb_memLp
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.truncKernel_memLp
-- assert_no_sorry Spectra.QuantumMechanics.Hydrogen.eLpNorm_truncKernel
-- assert_no_sorry Spectra.CompactOperator.young_L1_conv_L2
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.freeGreensFunctionL2
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.fourierL2_freeGreensFunctionL2
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.integrable_conv_integrand
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.young_R3
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.memLp_conv_L2_schwartz
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.fourier_conv_L2_schwartz
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.freeGreens_resolvent_kernel_schwartz
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.coulombResolvent
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.coulomb_hVW
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.truncCoulombBall_memLp
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.truncKernelG_memLp
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.hydrogen_essSpectrum_of_compact
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.hydrogen_essSpectrum_eq_Ici_of_compact
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.coulombResolvent_isCompact
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.hydrogen_essSpectrum

/-! ### Radial × angular tensor decomposition L²(ℝ³) ≅ ⊕_ℓ RadialL2 ⊗ V_ℓ -/

-- The two headline unitaries: R ↦ rR (radial substitution) and the spherical-harmonic
-- expansion of L²(ℝ³) into angular-momentum sectors.
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.Decomposition.radialReduction
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.Decomposition.sphericalDecomposition

/-! ### The 3D spherical change-of-variables unitary (Cartesian ↔ spherical `L²(ℝ³)`) -/

-- `chartRealization : Sobolev.l2R3 ≃ₗᵢ[ℂ] Decomposition.l2R3`, precomposition with the spherical
-- chart `(r, θ, φ) ↦ (r sinθ cosφ, r sinθ sinφ, r cosθ)`; the chart is measure-preserving, its
-- eLpNorm change-of-variables identity, and the a.e. pointwise action of the unitary and its
-- inverse (used in later hydrogen intertwining arguments).
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.Decomposition.measurePreserving_sphereChart
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.Decomposition.eLpNorm_chartRealizationFun
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.Decomposition.chartRealization
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.Decomposition.chartRealization_coeFn
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.Decomposition.chartRealization_symm_coeFn

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

-- `hydrogen_discrete_spectrum` (in `Spectrum.Discrete`) — the E<0 characterization
-- `E ∈ σ_p(H) ↔ E = Eₙ`. Now fully proved sorry-free and axiom-clean; gate restored.
assert_no_sorry QuantumMechanics.Hydrogen.Spectrum.hydrogen_discrete_spectrum

/-! ### Hydrogen discrete eigenspaces · degeneracy states are eigenvectors, span = eigenspace,
and the spectral projection `E({Eₙ})` onto the `n²`-dimensional bound-state subspace -/

assert_no_sorry QuantumMechanics.Hydrogen.Spectrum.degenFamily_mem_ker
assert_no_sorry QuantumMechanics.Hydrogen.Spectrum.eigenspace_subset_span
assert_no_sorry QuantumMechanics.Hydrogen.Spectrum.hydrogen_eigenspace_eq_span
assert_no_sorry QuantumMechanics.Hydrogen.Spectrum.hydrogen_spectral_projection_discrete
assert_no_sorry QuantumMechanics.Hydrogen.Spectrum.hydrogen_spectral_projection_finrank

/-! ### Spectral theory · discreteness (Weyl hard half) and hydrogen eigenfunction completeness -/

assert_no_sorry
  Spectra.QuantumMechanics.SpectralTheory.mem_pointSpectrum_of_mem_spectrum_notMem_essSpectrum
assert_no_sorry
  Spectra.QuantumMechanics.SpectralTheory.spectralPVM_proj_eq_zero_of_subset_resolventSet
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
assert_no_sorry Spectra.QuantumMechanics.Dirac.dirac_energy_witness
assert_no_sorry Spectra.QuantumMechanics.Dirac.diracHamiltonian_unbounded_below_unconditional
assert_no_sorry Spectra.QuantumMechanics.Dirac.diracHamiltonian_not_semibounded_unconditional
assert_no_sorry Spectra.Operator.kato_rellich
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.hardy_inequality
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.hardy_constant_sharp
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.hydrogen_isSelfAdjoint
assert_no_sorry Spectra.QuantumMechanics.Hydrogen.coulomb_kato_rellich

/-! ### Born rule for a single observable (probability measure, expectation, variance, support) -/

assert_no_sorry Spectra.QuantumMechanics.BornRule.Observable.born_rule
assert_no_sorry Spectra.QuantumMechanics.BornRule.Observable.isProbabilityMeasure_bornMeasure
assert_no_sorry Spectra.QuantumMechanics.BornRule.Observable.bornExpectation_eq_inner
assert_no_sorry Spectra.QuantumMechanics.BornRule.Observable.bornVariance_eq_central_moment
assert_no_sorry Spectra.QuantumMechanics.BornRule.Observable.bornMeasure_support_subset_spectrum

/-! ### Generalized measurement · POVMs and Naimark dilation (effect-valued Born rule) -/

assert_no_sorry Spectra.POVM.ofEffects
assert_no_sorry Spectra.QuantumMechanics.BornRule.bornMeasurePOVM_apply
assert_no_sorry Spectra.QuantumMechanics.BornRule.toState_effect_eq
assert_no_sorry Spectra.QuantumMechanics.BornRule.binaryPOVM
assert_no_sorry Spectra.QuantumMechanics.BornRule.binaryPOVM_bornPure_true
assert_no_sorry Spectra.QuantumMechanics.BornRule.naimark_dilation

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

/-! ### Reflection positivity (Osterwalder–Schrader OS3, abstract predicate)

The abstract reflection-positivity condition and its bundled `ReflectionData` (self-adjoint
involution + positive-time subspace + OS3 axiom), with the reflected-diagonal realness lemma and the
`trivial` inhabitation witness.  `sorry`-free and axiom-clean. -/

assert_no_sorry Spectra.QuantumFieldTheory.OsterwalderSchrader.IsReflectionPositive
assert_no_sorry
  Spectra.QuantumFieldTheory.OsterwalderSchrader.ReflectionData.reflected_inner_conj_eq
assert_no_sorry Spectra.QuantumFieldTheory.OsterwalderSchrader.ReflectionData.trivial

/-! ### Reflection positivity engine (Osterwalder–Seiler collapse, Lane R2 core)

The integral-form reflected pairing `reflectedForm` and the Osterwalder–Seiler positivity mechanism:
for a Gram-form Boltzmann kernel `ρ = ∑ᵢ conj(gᵢ) ⊗ gᵢ` the reflected pairing collapses to
`∑ᵢ ‖∫ f·gᵢ‖²` (`reflectedForm_gram`), hence is a nonnegative real (reflection positivity,
`reflectedForm_gram_re_nonneg`/`_im`), reducing R2 to G5's character/heat-kernel Gram decomposition
of the Wilson weight (`IsReflectionPositiveKernel`, `reflectedForm_re_nonneg_of_kernel`).  The free
(`β = 0`) case is the first unconditional instance (`reflectedForm_const_one`).  All
`sorry`-free and axiom-clean. -/

assert_no_sorry Spectra.QuantumFieldTheory.OsterwalderSchrader.reflectedForm_gram
assert_no_sorry Spectra.QuantumFieldTheory.OsterwalderSchrader.reflectedForm_gram_re_nonneg
assert_no_sorry Spectra.QuantumFieldTheory.OsterwalderSchrader.reflectedForm_gram_im
assert_no_sorry Spectra.QuantumFieldTheory.OsterwalderSchrader.isReflectionPositiveKernel_const_one
assert_no_sorry Spectra.QuantumFieldTheory.OsterwalderSchrader.reflectedForm_re_nonneg_of_kernel
assert_no_sorry Spectra.QuantumFieldTheory.OsterwalderSchrader.reflectedForm_const_one
assert_no_sorry Spectra.QuantumFieldTheory.OsterwalderSchrader.reflectedForm_const_one_re_nonneg

/-! ### Wightman spectral condition & mass gap (relativistic joint-spectral statement)

The precise **joint-spectral** statement of the Wightman spectral condition (W2), vacuum uniqueness
(W3), and the **mass gap** for a relativistic Hilbert space, bundled `ModularData`-style in
`RelativisticSpectralData` (uninhabited until an OS-type reconstruction supplies a representation).
Gated here: the concrete spacetime-momentum regions' measurability, the `n`-ary marginal ⟹ pairwise
strong-commutativity sanity lemma, and the structure's sanity lemmas.  All `sorry`-free and
axiom-clean. -/

assert_no_sorry Spectra.QuantumFieldTheory.Wightman.measurableSet_cylinder
assert_no_sorry Spectra.QuantumFieldTheory.Wightman.measurableSet_closedForwardLightCone
assert_no_sorry Spectra.QuantumFieldTheory.Wightman.measurableSet_massGapAnnulus
assert_no_sorry Spectra.QuantumFieldTheory.Wightman.measurableSet_singleton_zero
assert_no_sorry Spectra.QuantumFieldTheory.Wightman.isStarProjection_rankOneProjection
assert_no_sorry Spectra.QuantumFieldTheory.Wightman.stronglyCommute_of_isJointOfFamily
assert_no_sorry
  Spectra.QuantumFieldTheory.Wightman.RelativisticSpectralData.stronglyCommute_of_marginal
assert_no_sorry
  Spectra.QuantumFieldTheory.Wightman.RelativisticSpectralData.isStarProjection_proj_zero

/-! ### Gauge theory: the compact gauge group and the lattice substrate

Lane G: `U(n)`/`SU(n)` are compact topological groups — the topological-group half is derivable from
Mathlib's generic `unitary R` machinery (recorded as `isClosed_unitaryGroup`); compactness is proved
here via a Tychonoff entry-box argument (`norm_entry_le_one` → `isCompact_unitaryGroup`).  Lane L1:
the finite periodic-lattice combinatorial substrate (sites/links/plaquettes/holonomy).  All
`sorry`-free and axiom-clean. -/

assert_no_sorry Spectra.GaugeTheory.isClosed_unitaryGroup
assert_no_sorry Spectra.GaugeTheory.norm_entry_le_one
assert_no_sorry Spectra.GaugeTheory.isCompact_unitaryGroup
assert_no_sorry Spectra.GaugeTheory.isCompact_specialUnitaryGroup
-- G3: Haar probability measure on the compact gauge groups + uniqueness.
assert_no_sorry Spectra.GaugeTheory.haarUnitary
assert_no_sorry Spectra.GaugeTheory.haarUnitary_unique
assert_no_sorry Spectra.GaugeTheory.haarSpecialUnitary
assert_no_sorry Spectra.GaugeTheory.haarSpecialUnitary_unique
assert_no_sorry Spectra.GaugeTheory.Lattice.card_site
assert_no_sorry Spectra.GaugeTheory.Lattice.plaquetteHolonomy_one
-- L2 Wilson action: nonnegativity (via the G-lane entry bound) and the vacuum minimizer.
assert_no_sorry Spectra.GaugeTheory.Lattice.re_trace_le_card
assert_no_sorry Spectra.GaugeTheory.Lattice.plaquetteAction_nonneg
assert_no_sorry Spectra.GaugeTheory.Lattice.wilsonAction_nonneg
assert_no_sorry Spectra.GaugeTheory.Lattice.wilsonAction_one
assert_no_sorry Spectra.GaugeTheory.Lattice.wilsonAction_le
-- L3 finite-volume Gibbs measure: partition-function bounds, measurable density,
-- probability measure.
assert_no_sorry Spectra.GaugeTheory.Lattice.continuous_wilsonAction
assert_no_sorry Spectra.GaugeTheory.Lattice.measurable_gibbsDensity
assert_no_sorry Spectra.GaugeTheory.Lattice.partitionFunction_pos
assert_no_sorry Spectra.GaugeTheory.Lattice.partitionFunction_ne_top
assert_no_sorry Spectra.GaugeTheory.Lattice.gibbsMeasure
assert_no_sorry Spectra.GaugeTheory.Lattice.isProbabilityMeasure_gibbsMeasure
-- R2 free case: reflection positivity of the a-priori (β=0) lattice measure via the R2-core engine.
-- The a-priori measure factors as `posMeasure ⊗ negMeasure`; the explicit configuration reflection
-- `Θ` (an involution) reflects a positive-time observable, and the reflected pairing over
-- `aprioriMeasure` collapses to `‖𝔼[f]‖² ≥ 0`.
assert_no_sorry Spectra.GaugeTheory.Lattice.measurePreserving_split
assert_no_sorry Spectra.GaugeTheory.Lattice.measurePreserving_congr
assert_no_sorry Spectra.GaugeTheory.Lattice.reflectionPositive_free
assert_no_sorry Spectra.GaugeTheory.Lattice.configReflection_involutive
assert_no_sorry Spectra.GaugeTheory.Lattice.posPart_configReflection
assert_no_sorry Spectra.GaugeTheory.Lattice.reflectionPositive_configReflection
assert_no_sorry Spectra.GaugeTheory.Lattice.reflectionPositive_configReflection_re_nonneg
-- R2 interacting (β>0) case, modulo G5: if the Wilson weight is a reflected Gram sum (the
-- character-expansion structure Lane G5 supplies), the reflected pairing over the genuine
-- `gibbsMeasure` is ≥ 0 — reduced per Gram-mode to the free case.  The `_tsum` (countable) versions
-- are the genuine β>0 statement (the character expansion is countably infinite for β>0); the finite
-- `reflectionPositive_weighted` is the truncated/finite-mode case (exact for exp(−S) only at β=0).
assert_no_sorry Spectra.GaugeTheory.Lattice.reflectionPositive_weighted
assert_no_sorry Spectra.GaugeTheory.Lattice.reflectionPositive_weighted_re_nonneg
assert_no_sorry Spectra.GaugeTheory.Lattice.reflectionPositive_weighted_tsum
assert_no_sorry Spectra.GaugeTheory.Lattice.reflectionPositive_gibbsMeasure

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
assert_no_sorry
  Spectra.QuantumMechanics.SpectralTheory.spectralPVM_proj_eq_spectralProjection_stoneGroup
assert_no_sorry
  Spectra.QuantumMechanics.SpectralTheory.spectralPVM_diag_eq_map_cayleySpectralMeasure

-- P5: the spectral theorem, proved a SECOND, INDEPENDENT way via Cayley/Riesz–Markov — existence
-- witnessed by `groupPVM (stoneGroup hA)`, mentioning `genToGroup` nowhere; uniqueness reused
-- verbatim from `spectralPVM_unique` (already fully generic). This is the historical point of the
-- Cayley transform, not merely an identification with the Yosida-built spectral theorem.
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.selfAdjointResolvent_eq_stoneGroup
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.cayleyPVM_resolvent_formula
assert_no_sorry
  Spectra.QuantumMechanics.SpectralTheory.groupPVM_stoneGroup_eq_spectralPVM_independent
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
assert_no_sorry
  Spectra.QuantumMechanics.SpectralTheory.pmapOfPVM_apply_eq_spectralCalculus_of_bounded
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
-- R4a field 3 foundation: the Tomita involution `S̃² = 1` on the core `M Ω`
-- (`S̃ (a Ω) = (star a) Ω`, hence `S̃ (S̃ (a Ω)) = a Ω`), plus the polar helper
-- `J (Δ^{½} x) = ofConj (S x)`. The genuine content seeding `J² = 1` (field 3); the range-vs-core
-- bridge closing `J² = 1` is the remaining node.
assert_no_sorry Spectra.TomitaTakesaki.sTilde_core
assert_no_sorry Spectra.TomitaTakesaki.sTilde_involutive_core
assert_no_sorry Spectra.TomitaTakesaki.modularConjugation_apply_modularSqrt
-- Field-3 keystone spike result: the Tomita involution `S̃² = 1` upgraded from the core `M Ω` to
-- the whole domain `D(S)` of the closure (`S̃ y ∈ D(S)` and `S̃ (S̃ y) = y`), via the continuous
-- conjugate-linear graph-symmetry `swapConj`. No `Δ`/`Δ^{½}`/adjoint calculus. (Closing `J² = 1`
-- still needs the polar relation on the full `D(Δ^{½})` — the Route B calculus.)
assert_no_sorry Spectra.TomitaTakesaki.sTilde_closure_mem_domain
assert_no_sorry Spectra.TomitaTakesaki.sTilde_closure_involutive
-- R4a field 3, Route B gate (HC1): the modular square root `Δ^{½}` is SELF-ADJOINT — von Neumann's
-- deficiency criterion `isSelfAdjoint_of_surjective_addSub` fed by symmetry + surjectivity of
-- `Δ^{½} ± i` (bounded resolvent `Φ(1/(√±i))`). The single blocker of the J²=1 endgame; unblocks
-- `(Δ^{½})²=Δ`. Plus the reusable NEW infrastructure: the mixed bounded/unbounded product law for
-- the PVM calculus.
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
-- The projection-valued pushforward `P.map φ` (`(P.map φ).proj B = P.proj (φ⁻¹ B)`,
-- `(P.map φ).diag ξ = (P.diag ξ).map φ`) — the previously-missing PVM constructor, carrier of the
-- spectral-mapping `E^{f(A)} = (spectralPVM A).map f` for the polar-uniqueness build.
assert_no_sorry Spectra.ProjValMeasure.map
-- The `s ↦ s²` spectral-mapping theorem `spectralPVM (A²) = (spectralPVM A).map (·²)` (DAG node
-- `spectralPVM_sq_eq_pushforward`), with `A²` self-adjoint (`sq_isSelfAdjoint`) and the resolvent
-- bridge `(A²−z)⁻¹ = Φ(1/(s²−z))` — the crux of positive-square-root uniqueness for Field-3 polar
-- uniqueness.
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.sq_isSelfAdjoint
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.selfAdjointResolvent_sq_eq
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.spectralPVM_sq_eq_pushforward
-- Injectivity of the `s↦s²` pushforward on `[0,∞)`-supported PVMs, that a self-adjoint operator is
-- determined by its spectral measure, and the ★ KEYSTONE positive-square-root uniqueness
-- `posSqrt_unique` (P,Q≥0 self-adjoint, P²=Q² ⟹ P=Q) — the crux of Field-3 polar uniqueness.
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.sq_pushforward_injective
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.spectralPVM_determines
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.posSqrt_unique

/-! ## The spectral-flow generator engine and the modular Hamiltonian `generator(Δ^{it}) = log Δ`

The general Stone-type theorem for the spectral exponential flow of a real symbol: the group
`V.U t = Φ_U(exp(i t φ))` has generator `pmapOfPVM U φ` (`generator_eq_pmapOfPVM_of_flowSymbol`),
via the real-symbol resolvent bridge `(A_φ − z)⁻¹ = Φ_U(1/(φ − z))`
(`selfAdjointResolvent_pmapOfPVM_real_eq`) and the `φ`-pushforward of the flow's spectral measure
(`borelMeasure_flowSymbol_eq_map`).  Its Tomita–Takesaki corollary
`generator_modularFlow_eq_logModularOp` identifies the modular Hamiltonian `generator(Δ^{it})` with
the honest unbounded calculus `log Δ = ∫ log s dE_Δ(s)` (`logModularOp`, self-adjoint) — the theorem
the abstract KMS layer states only by naming convention. -/
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.resolvent_real_identity
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.selfAdjointResolvent_pmapOfPVM_real_eq
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.borelMeasure_flowSymbol_eq_map
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.generator_eq_pmapOfPVM_of_flowSymbol
assert_no_sorry Spectra.TomitaTakesaki.logModularOp
assert_no_sorry Spectra.TomitaTakesaki.logModularOp_isSelfAdjoint
assert_no_sorry Spectra.TomitaTakesaki.generator_modularFlow_eq_logModularOp

/-! ## Field-3 Stage 0 — the reciprocal modular calculus `Δ⁻¹`, `Δ^{-½}` (COMPLETE)

The generic J-free real-symbol self-adjointness engine (surjectivity of `A_f ± i` is
unconditional for a real symbol `f`, since `1/(f ± i)` is bounded), the away-from-zero band
density engine
(`D(∫f dP)` dense whenever every `μ_y` is carried by `(0,∞)` and `f` is bounded on each band
`[1/(n+1), n+1]`), and their instantiation at the reciprocal symbols `1/s`, `1/√s`:
`Δ⁻¹ = modularOpInv` and `Δ^{-½} = modularSqrtInv` are **unconditionally self-adjoint**, with
`(Δ^{-½})² = Δ⁻¹` on `D(Δ⁻¹)` — the operators needed to *state* the final Tomita relation
`J Δ J⁻¹ = Δ⁻¹`. -/
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.pmapOfPVM_add_I_surjective
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.pmapOfPVM_sub_I_surjective
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.pmapOfPVM_isSelfAdjoint_of_real
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.spectralProjection_band_mem_pmapDomain
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.pmapOfPVM_domain_dense_of_support_Ioi
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.norm_sq_spectralProjection
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.generator_has_arbitrarily_negative_energy
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.generator_has_arbitrarily_positive_energy
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.spectralProjection_Ioo_eq_zero_of_norm_ge
assert_no_sorry Spectra.TomitaTakesaki.modularOpInv
assert_no_sorry Spectra.TomitaTakesaki.modularSqrtInv
assert_no_sorry Spectra.TomitaTakesaki.modularOpInv_isSelfAdjoint_of_dense
assert_no_sorry Spectra.TomitaTakesaki.modularSqrtInv_isSelfAdjoint_of_dense
assert_no_sorry Spectra.TomitaTakesaki.modularOpInv_domain_dense
assert_no_sorry Spectra.TomitaTakesaki.modularSqrtInv_domain_dense
assert_no_sorry Spectra.TomitaTakesaki.modularOpInv_isSelfAdjoint
assert_no_sorry Spectra.TomitaTakesaki.modularSqrtInv_isSelfAdjoint
assert_no_sorry Spectra.TomitaTakesaki.modularOpInv_domain_le_modularSqrtInv_domain
assert_no_sorry Spectra.TomitaTakesaki.modularSqrtInv_mem_domain_of_mem_modularOpInv
assert_no_sorry Spectra.TomitaTakesaki.modularSqrtInv_sq_apply

/-! ## Field-3 kill-spikes KS1–KS3 — ALL GREEN

The three binary go/no-go probes of the Route-B staged DAG, each landed as a full sorry-free
theorem rather than a mere feasibility verdict.  **KS1** (Stage-3 pin): `D(Δ)` is a core for
`Δ^{½}` (Mathlib `LinearPMap.HasCore`, via spectral cut-offs `E([0,n])y`).  **KS2** (Stage-4/5
stateability): the conjugation `J Δ^{½} J⁻¹` by the antiunitary modular conjugation exists as a
`LinearPMap` (`conjPMap`), is self-adjoint, and its spectral measures charge no negative reals —
the exact `posSqrt_unique` input shapes.  **KS3** (Stage-1 substrate): the bounded-factor
adjoint law `(b∘A)⋆ = A⋆∘b⁻¹` for a unitary factor `b`, absent from Mathlib. -/
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.borelMeasure_Iio_zero_eq_zero_of_dense
assert_no_sorry Spectra.TomitaTakesaki.modularSqrt_hasCore_modularOp_domain
assert_no_sorry Spectra.TomitaTakesaki.modularSqrt_mem_closure_graph_domRestrict

/-! ## Field-3 Route B Stage 3 — the extended polar decomposition `S = W ∘ Δ^{½}` (COMPLETE)

The polar relation `W(Δ^{½}x) = Sx` extended from `D(Δ)` to the full square-root domain, with the
polar domains coinciding: `D(S) = D(Δ^{½})`, `S y = W(Δ^{½}y)`, the extended isometry
`‖Δ^{½}y‖ = ‖Sy‖`, and the `J`-form `toConj (J (Δ^{½}y)) = S y`.  Both directions are image-closure
pushes of the two core facts (KS1's `HasCore` and the graph-L² closure) through
`(u,v) ↦ (u, W^{±1}v)` into the closed graphs.  This pins `W` on `cl(ran Δ^{½})` — the Stage-4
ingredient. -/
assert_no_sorry Spectra.TomitaTakesaki.modularSqrt_domain_le_tomitaClosure_domain
assert_no_sorry Spectra.TomitaTakesaki.tomitaClosure_domain_le_modularSqrt_domain
assert_no_sorry Spectra.TomitaTakesaki.tomitaClosure_domain_eq_modularSqrt_domain
assert_no_sorry Spectra.TomitaTakesaki.tomitaClosure_eq_modularW_modularSqrt
assert_no_sorry Spectra.TomitaTakesaki.norm_modularSqrt_eq_norm_tomitaClosure
assert_no_sorry Spectra.TomitaTakesaki.tomita_eq_modularConjugation_modularSqrt_full
assert_no_sorry Spectra.TomitaTakesaki.conjPMap
assert_no_sorry Spectra.TomitaTakesaki.conjPMap_isSelfAdjoint
assert_no_sorry Spectra.TomitaTakesaki.inner_modularConjugation
assert_no_sorry Spectra.TomitaTakesaki.conjModularSqrt
assert_no_sorry Spectra.TomitaTakesaki.conjModularSqrt_isSelfAdjoint
assert_no_sorry Spectra.TomitaTakesaki.conjModularSqrt_borelMeasure_Iio_zero
assert_no_sorry Spectra.Operator.mem_compPMap_adjoint_domain_iff
assert_no_sorry Spectra.Operator.compPMap_adjoint_apply

/-! ## M4 — the `2 × 2` matrix amplification `M₂(M)` (block operators + `*`-subalgebra)

Block operators on the `L²` direct sum `H2 H = WithLp 2 (H × H)`, the carrier of the balanced-state
amplification for the Connes cocycle.  The block algebra is a ring under matrix multiplication
(`blockOp_comp`), entrywise-linear (`blockOp_add`/`_smul`), and `*`-closed via the conjugate
transpose (`blockOp_star`), from which the matrix-unit relations `eᵢⱼ eₖₗ = δⱼₖ eᵢₗ`,
`e₁₁ + e₂₂ = 1`, and the `*`-subalgebra `M2subalg M` of block operators with all entries in `M` all
follow. -/
assert_no_sorry Spectra.TomitaTakesaki.blockOp_comp
assert_no_sorry Spectra.TomitaTakesaki.blockOp_add
assert_no_sorry Spectra.TomitaTakesaki.blockOp_smul
assert_no_sorry Spectra.TomitaTakesaki.blockOp_zero
assert_no_sorry Spectra.TomitaTakesaki.blockOp_one
assert_no_sorry Spectra.TomitaTakesaki.blockOp_star
assert_no_sorry Spectra.TomitaTakesaki.e₁₂_mul_e₂₁
assert_no_sorry Spectra.TomitaTakesaki.e₂₁_mul_e₁₂
assert_no_sorry Spectra.TomitaTakesaki.e₁₁_add_e₂₂
assert_no_sorry Spectra.TomitaTakesaki.star_e₁₂
assert_no_sorry Spectra.TomitaTakesaki.M2subalg
assert_no_sorry Spectra.TomitaTakesaki.e₁₁_mem_M2subalg
assert_no_sorry Spectra.TomitaTakesaki.e₂₁_mem_M2subalg
assert_no_sorry Spectra.TomitaTakesaki.eq_blockOp
assert_no_sorry Spectra.TomitaTakesaki.centralizer_M2set
assert_no_sorry Spectra.TomitaTakesaki.centralizer_scalarBlockSet
assert_no_sorry Spectra.TomitaTakesaki.M2

/-! ## M4/E2 — the spatial modular automorphism `σ_t = Ad(U t)`

The carrier-agnostic `*`-automorphism builder: for any one-parameter unitary group `U` (e.g. the
modular flow `Δ^{it}`), `modularAut U t : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H)` is spatial conjugation
`x ↦ U t · x · U(-t)`, built on Mathlib's `Unitary.conjStarAlgAut`.  A one-parameter group of
automorphisms (`modularAut_zero`/`_add`); Tomita invariance enters only as a hypothesis
(`modularAut_mapsTo_of_invariance`), keeping this off the research gates. -/
assert_no_sorry Spectra.TomitaTakesaki.modularAut
assert_no_sorry Spectra.TomitaTakesaki.modularAut_apply
assert_no_sorry Spectra.TomitaTakesaki.modularAut_zero
assert_no_sorry Spectra.TomitaTakesaki.modularAut_add
assert_no_sorry Spectra.TomitaTakesaki.modularAut_mapsTo_of_invariance

/-! ## E3 — vector-state invariance of the modular flow

`ω(σ_t x) = ω(x)` for the vector state `ω = ⟪Ω, ·Ω⟫`: generic for any unitary flow fixing `Ω`,
unconditional for the constructed modular flow (via the proved `Δ^{it}Ω = Ω`), and in bundled
`ModularData` form. -/
assert_no_sorry Spectra.TomitaTakesaki.inner_modularAut_vacuum
assert_no_sorry Spectra.TomitaTakesaki.inner_modularAut_modularFlow_vacuum
assert_no_sorry Spectra.TomitaTakesaki.ModularData.inner_modularAut_vacuum

/-! ## The inverse-calculus twins `Δ^{-½}Δ^{½} = 1`, `Δ^{½}Δ^{-½} = 1` and
`ran Δ^{½} = D(Δ^{-½})` -/
assert_no_sorry Spectra.TomitaTakesaki.modularSqrt_mem_modularSqrtInv_domain
assert_no_sorry Spectra.TomitaTakesaki.modularSqrtInv_modularSqrt_apply
assert_no_sorry Spectra.TomitaTakesaki.modularSqrtInv_mem_modularSqrt_domain
assert_no_sorry Spectra.TomitaTakesaki.modularSqrt_modularSqrtInv_apply
assert_no_sorry Spectra.TomitaTakesaki.mem_modularSqrtInv_domain_iff

/-! ## The spectral-square bridge (generic): pointwise composition ⟹ `pmapOfPVM (·²)` -/
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.mem_pmapDomain_id_of_mem_generator
assert_no_sorry
  Spectra.QuantumMechanics.SpectralTheory.spectralCalculus_apply_pmapOfPVM_of_mul_bounded
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.mem_sq_domain_of_generator_comp
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.pmapOfPVM_sq_apply_generator_comp
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.pmapOfPVM_sq_genToGroup_eq

/-! ## ★★ Field 3 CLOSED — `J² = 1` and the Tomita conjugation relations

The second-polar-decomposition argument: the involution `S̃² = 1` + the full-domain polar identity
give `S = W″ ∘ (JΔ^{-½}J⁻¹)`; the KS3 bounded-factor adjoint law computes `Δ = S⋆S = (JΔ^{-½}J⁻¹)²`;
`posSqrt_unique` forces `JΔ^{-½}J⁻¹ = Δ^{½}`; factor-matching on the dense `ran Δ^{½}` closes
`J² = 1`, and the conjugation relations `JΔ^{½}J⁻¹ = Δ^{-½}`, `JΔJ⁻¹ = Δ⁻¹` follow.  This
discharges the `ModularData.J_involutive` field — the former research node. -/
assert_no_sorry Spectra.TomitaTakesaki.modularConjugation_symm_apply_eq
assert_no_sorry Spectra.TomitaTakesaki.tomitaClosure_eq_modularWInv_comp
assert_no_sorry Spectra.TomitaTakesaki.exists_conjModularSqrtInv_sq
assert_no_sorry Spectra.TomitaTakesaki.sq_conjModularSqrtInv_eq_modularOp
assert_no_sorry Spectra.TomitaTakesaki.sq_modularSqrt_eq_modularOp
assert_no_sorry Spectra.TomitaTakesaki.sq_modularSqrtInv_eq_modularOpInv
assert_no_sorry Spectra.TomitaTakesaki.conjModularSqrtInv_eq_modularSqrt
assert_no_sorry Spectra.TomitaTakesaki.modularConjugation_involutive
assert_no_sorry Spectra.TomitaTakesaki.modularConjugation_symm_eq
assert_no_sorry Spectra.TomitaTakesaki.conjModularSqrt_eq_modularSqrtInv
assert_no_sorry Spectra.TomitaTakesaki.conjModularOp_eq_modularOpInv

/-! ## D3-1 — the balanced vector: cyclic for `M₂(M)`, NOT separating (the `H⊕H` dead-end sealed)

The cyclic half of the balanced-state construction is real (`isCyclic_M2_of_isCyclic`), and the
in-code witness (`M = B(H)`, `[[1,-1],[0,0]]`) proves the naive `Ω_θ = (Ω,Ω)` on `H⊕H` is NOT
separating — the correct GNS carrier for the balanced state is `H⁴` (Route A). -/
assert_no_sorry Spectra.TomitaTakesaki.isCyclic_M2_of_isCyclic
assert_no_sorry Spectra.TomitaTakesaki.wholeAlgebra
assert_no_sorry Spectra.TomitaTakesaki.isCyclic_wholeAlgebra
assert_no_sorry Spectra.TomitaTakesaki.not_isSeparating_M2_wholeAlgebra
assert_no_sorry Spectra.TomitaTakesaki.exists_isCyclic_not_isSeparating_M2

/-! ## Base-`M` Tomita (fields 6/7/8) — the off-gate engines (vault: PLAN-tomita-fields678)

First bricks of the merged RvD-§4 / van-Daele route to Tomita's theorem: the bounded picture
`R = Φ(2/(1+s))`, `T = Φ(2√s/(1+s))` with the resolvent gluing `Δ(Rξ) = 2ξ − Rξ`, `Δ^{½}∘R = T`;
the adjoint-closure lemma `S̄⋆ = S₀⋆`; the L¹-Fourier injectivity closer; and ★ the flow-commutation
ladder `J Δ^{it} = Δ^{it} J` (via `J e^{isΔ} J⁻¹ = e^{isΔ⁻¹}` + the spectral-measure pushforward
`μ_{Jξ} = (s⁻¹)_*μ_ξ` — classically available only inside the polar machinery). -/
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.spectralCalculus_congr_ae_forall
assert_no_sorry Spectra.TomitaTakesaki.rvdR
assert_no_sorry Spectra.TomitaTakesaki.rvdT
assert_no_sorry Spectra.TomitaTakesaki.rvdT_sq
assert_no_sorry Spectra.TomitaTakesaki.modularOp_rvdR_apply
assert_no_sorry Spectra.TomitaTakesaki.modularSqrt_rvdR_apply
assert_no_sorry Spectra.TomitaTakesaki.rvdT_comm_modularFlow
assert_no_sorry Spectra.TomitaTakesaki.rvdT_injective
assert_no_sorry Spectra.TomitaTakesaki.denseRange_rvdT
assert_no_sorry Spectra.TomitaTakesaki.tomitaClosure_adjoint_eq
assert_no_sorry Spectra.TomitaTakesaki.tomitaClosure_adjoint_apply_commutant
assert_no_sorry Spectra.Fourier.eq_zero_of_fourierIntegral_eq_zero
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.flowGroup
assert_no_sorry Spectra.QuantumMechanics.SpectralTheory.generator_flowGroup
assert_no_sorry Spectra.TomitaTakesaki.modularConjGroup
assert_no_sorry Spectra.TomitaTakesaki.generator_modularConjGroup
assert_no_sorry Spectra.TomitaTakesaki.modularConjGroup_genToGroup_modularOp
assert_no_sorry Spectra.TomitaTakesaki.borelMeasure_modularConjugation_eq_map
assert_no_sorry Spectra.TomitaTakesaki.jConj_modularFlow
assert_no_sorry Spectra.TomitaTakesaki.modularConjugation_comm_modularFlow

/-! ## R4 — `ModularData` existence, up to Tomita's theorem

Fields 1–5 (J, Δ^{it}, `J²=1`, `JΩ=Ω`, `Δ^{it}Ω=Ω`) are constructed and proved; the two Tomita
fields and the commutation theorem enter as typed hypotheses — the isolated research frontier. -/
assert_no_sorry Spectra.TomitaTakesaki.tomitaTakesaki_exists_of_invariance

/-! ## M1 — the GNS bridge: state ⟶ `(π(A)'', Ω)` with `Ω` cyclic

The generic double-commutant constructor, the GNS von Neumann algebra `π(A)''`, unconditional
cyclicity of the GNS vacuum, and the separation consequences of faithfulness at the level of `A`
(the bicommutant-level `IsSeparating` needs normality + Kaplansky density — the documented gap). -/
assert_no_sorry Spectra.KMS.doubleCommutant
assert_no_sorry Spectra.KMS.subset_doubleCommutant
assert_no_sorry Spectra.KMS.State.gnsVonNeumann
assert_no_sorry Spectra.KMS.State.gnsStarAlgHom_mem_gnsVonNeumann
assert_no_sorry Spectra.KMS.State.isCyclic_gnsVonNeumann
assert_no_sorry Spectra.KMS.State.norm_sq_gnsStarAlgHom_cyclicVector
assert_no_sorry Spectra.KMS.State.gnsStarAlgHom_cyclicVector_eq_zero_iff
assert_no_sorry Spectra.KMS.State.gnsStarAlgHom_injective
assert_no_sorry Spectra.KMS.FaithfulNormalState.isCyclic_gnsVonNeumann
assert_no_sorry Spectra.KMS.FaithfulNormalState.gnsStarAlgHom_injective

/-! ## Inner-product `ℓ²`-pairing estimates (shared, trace-class-free)

General `RCLike`-valued inner-product summability facts underpinning the trace bounds: inner
summability from square-summability, and the weighted arithmetic–geometric estimate that yields the
sharp Cauchy–Schwarz constant without any `Lᵖ`/Hölder machinery. -/
assert_no_sorry Spectra.QuantumMechanics.Channels.summable_inner_of_summable_sq
assert_no_sorry Spectra.QuantumMechanics.Channels.weighted_norm_tsum_inner_le

/-! ## Operator algebra · bounded polar decomposition `T = U |T|`

First brick of the trace-class / von Neumann predual development (discharge-first route to the
Tomita–Takesaki fundamental theorem). `|T| = CFC.abs T`, the polar isometry identity
`‖|T|x‖ = ‖Tx‖`, and the partial isometry `U` with `U |T| = T` — the last built by hand since
Mathlib's `LinearIsometry.extend` is finite-dimensional only. -/
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
-- adjoint-invariant (`∑ᵢ ‖A eᵢ‖² = ∑ᵢ ‖A⋆ eᵢ‖²`), the polar partial isometry `U` is a contraction,
-- and the initial-space identities `U⋆ U = P_K` and `U⋆ T = |T|` (load-bearing for trace-norm
-- duality and the triangle inequality).
assert_no_sorry Spectra.QuantumMechanics.Channels.tsum_enorm_apply_sq_adjoint
assert_no_sorry Spectra.QuantumMechanics.Channels.norm_polarPartial_eq
assert_no_sorry Spectra.QuantumMechanics.Channels.norm_polarIsometry_le_one
assert_no_sorry Spectra.QuantumMechanics.Channels.polarIsometry_adjoint_comp_self
assert_no_sorry Spectra.QuantumMechanics.Channels.polarIsometry_adjoint_comp
-- Trace-class hard-core Stage C (minimal Hilbert–Schmidt ideal): the predicate `IsHilbertSchmidt`
-- (`∑ᵢ ‖A eᵢ‖² < ∞`) with basis-independence, `A⋆` HS ↔ `A` HS, `|A|^{1/2}` HS ↔ `A` trace-class,
-- and the two-sided-ideal closure `B∘A`, `A∘B` HS — the factorization toolkit for cyclicity
-- `tr(AB)=tr(BA)`.
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
-- Trace-class hard-core Stage D (cyclicity of the trace): the Hilbert–Schmidt case
-- `tr (X Y) = tr (Y X)` via a Fubini swap of the absolutely convergent double sum, and the general
-- case `tr (A B) = tr (B A)` (`A` trace-class, `B` bounded) via the `A = (U |A|^{1/2}) |A|^{1/2}`
-- Hilbert–Schmidt factorization.
assert_no_sorry Spectra.QuantumMechanics.Channels.trace_comp_comm_hs
assert_no_sorry Spectra.QuantumMechanics.Channels.trace_comp_comm
-- The contraction–trace bound `∑ᵢ ‖⟪W eᵢ, S eᵢ⟫‖ ≤ ‖S‖₁` (`‖W‖ ≤ 1`), the single-fixed-`W`
-- estimate.
assert_no_sorry Spectra.QuantumMechanics.Channels.tsum_norm_inner_comp_le
-- Trace-class hard-core Stage E (the triangle inequality): `tr |S+T| ≤ tr |S| + tr |T|` in `ℝ≥0∞`
-- via the polar decomposition of `S + T` with one fixed partial isometry, closure of trace-class
-- under addition, and the triangle inequality `‖S + T‖₁ ≤ ‖S‖₁ + ‖T‖₁`.
assert_no_sorry Spectra.QuantumMechanics.Channels.posTrace_absOp_add_le
assert_no_sorry Spectra.QuantumMechanics.Channels.isTraceClass_add
assert_no_sorry Spectra.QuantumMechanics.Channels.traceNorm_add_le
-- Trace-class hard-core Stage F (toward the Banach space): the trace class is a `ℂ`-submodule of
-- `B(H)` (`traceClassSubmodule`, via `isTraceClass_smul`), and the operator norm is dominated by
-- the trace norm `‖T‖ ≤ ‖T‖₁` (`norm_le_traceNorm`) — the comparison making `‖·‖₁`-Cauchy sequences
-- `‖·‖`-Cauchy.
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
-- Trace-class hard-core Stage G (Hilbert–Schmidt × Hilbert–Schmidt is trace class): the qualitative
-- Schatten–Hölder membership `X, Y` HS ⟹ `X∘Y` trace-class, proved by the diagonal estimate
-- `⟪eᵢ,|XY|eᵢ⟫ = ⟪X⋆ U eᵢ, Y eᵢ⟫ ≤ ‖X⋆ U eᵢ‖² + ‖Y eᵢ‖²` (the polar factor `U⋆(XY)=|XY|`, avoiding
-- the sup-over-bases characterization), and the resulting trace-class two-sided ideal `B∘T`, `T∘B`.
assert_no_sorry Spectra.QuantumMechanics.Channels.IsHilbertSchmidt.isTraceClass_comp
assert_no_sorry Spectra.QuantumMechanics.Channels.IsTraceClass.comp_left
assert_no_sorry Spectra.QuantumMechanics.Channels.IsTraceClass.comp_right
assert_no_sorry Spectra.QuantumMechanics.Channels.isTraceClass_sqrtOp_absOp_comp
-- Trace-class hard-core Stage H (the Hilbert–Schmidt norm + sharp Schatten–Hölder): the norm
-- `‖A‖₂ = (∑ᵢ ‖A eᵢ‖²)^{1/2}` with adjoint-invariance and the operator-ideal bound, and the sharp
-- `‖X∘Y‖₁ ≤ ‖X‖₂ ‖Y‖₂` via the diagonal ℓ²-Cauchy–Schwarz
-- `∑ᵢ re⟪X⋆Ueᵢ,Yeᵢ⟫ ≤ ‖X⋆U‖₂‖Y‖₂ ≤ ‖X‖₂‖Y‖₂`.
assert_no_sorry Spectra.QuantumMechanics.Channels.hsNorm
assert_no_sorry Spectra.QuantumMechanics.Channels.hsNorm_adjoint
assert_no_sorry Spectra.QuantumMechanics.Channels.hsNorm_comp_le
assert_no_sorry Spectra.QuantumMechanics.Channels.hsNorm_comp_le'
assert_no_sorry Spectra.QuantumMechanics.Channels.traceNorm_comp_le
-- Trace-class hard-core Stage I (the Uhlmann fidelity `F(ρ,σ)=‖√ρ√σ‖₁`): `‖√ρ‖₂=√(tr ρ)`,
-- `F(ρ,ρ)=tr ρ`, and the Schatten–Hölder / Cauchy–Schwarz bound `F(ρ,σ) ≤ √(tr ρ · tr σ)` ⟹ `≤ 1`
-- for normalized states — the elementary information-geometric fidelity (I1).
assert_no_sorry Spectra.QuantumMechanics.Channels.hsNorm_sqrtOp_of_nonneg
assert_no_sorry Spectra.QuantumMechanics.Channels.fidelity_self
assert_no_sorry Spectra.QuantumMechanics.Channels.fidelity_le_sqrt_mul
assert_no_sorry Spectra.QuantumMechanics.Channels.fidelity_le_one
-- The trace norm is adjoint-invariant `‖A⋆‖₁ = ‖A‖₁` (`traceNorm_adjoint`, via the polar identity
-- `|A⋆| = U|A|U⋆` + cyclicity, with `A⋆` trace-class iff `A` is by the ideal) — gives fidelity
-- symmetry.
assert_no_sorry Spectra.QuantumMechanics.Channels.isTraceClass_adjoint
assert_no_sorry Spectra.QuantumMechanics.Channels.traceNorm_adjoint
assert_no_sorry Spectra.QuantumMechanics.Channels.fidelity_comm
-- Trace-class hard-core Stage J (the predual embedding `B(H) ↪ (T(H))*`): the trace pairing
-- `traceFunctional B = (T ↦ tr(BT))` is bounded (`≤‖B‖`), injective (rank-one separation), and —
-- via the unit rank-one witnesses `‖|u⟩⟨v|‖₁=1` — an isometry `‖traceFunctional B‖=‖B‖`, packaged
-- as the linear isometric embedding `traceDualₗᵢ`.  (Surjectivity is the deferred research-grade
-- half.)
assert_no_sorry Spectra.QuantumMechanics.Channels.traceFunctional
assert_no_sorry Spectra.QuantumMechanics.Channels.norm_traceFunctional_le
assert_no_sorry Spectra.QuantumMechanics.Channels.traceFunctional_injective
assert_no_sorry Spectra.QuantumMechanics.Channels.traceNorm_rankOne_of_unit
assert_no_sorry Spectra.QuantumMechanics.Channels.norm_traceFunctional
assert_no_sorry Spectra.QuantumMechanics.Channels.traceDualₗᵢ

-- Quantum channels (Schrödinger picture): complete positivity via the block-quadratic-form
-- criterion on finite arrays of trace-class operators (`IsPositiveMatrix`/`IsCompletelyPositive`),
-- the bundled `QuantumChannel` structure, and the identity channel.
assert_no_sorry Spectra.QuantumMechanics.Channels.isPositiveMatrix_zero_iff
assert_no_sorry Spectra.QuantumMechanics.Channels.blockForm_one
assert_no_sorry Spectra.QuantumMechanics.Channels.isPositiveMatrix_one_iff
assert_no_sorry Spectra.QuantumMechanics.Channels.IsCompletelyPositive.isPositive
assert_no_sorry Spectra.QuantumMechanics.Channels.QuantumChannel.id_toFun_apply

/-! ## Quantum entropy -/

-- Von Neumann entropy `S(ρ) = tr(-ρ log ρ)` of a quantum state, built operator-theoretically for a
-- (possibly infinite-dimensional) `H`.  The spectrum of a state lies in `[0,1]`, so the entropy
-- operator `-ρ log ρ = cfc negMulLog ρ` is positive (`entropyOp_nonneg`, the load-bearing fact that
-- makes `posTrace` the honest trace and not a junk value); its `ℝ≥0∞`-valued positive trace is
-- `vonNeumannEntropy`, which is basis-independent, and a pure state `|ψ⟩⟨ψ|` has zero entropy.
assert_no_sorry Spectra.InformationGeometry.Quantum.QState.spectrum_toOp_nonneg
assert_no_sorry Spectra.InformationGeometry.Quantum.QState.spectrum_toOp_le_one
assert_no_sorry Spectra.InformationGeometry.Quantum.entropyOp_nonneg
assert_no_sorry Spectra.InformationGeometry.Quantum.entropyOp_isSelfAdjoint
assert_no_sorry Spectra.InformationGeometry.Quantum.vonNeumannEntropy
assert_no_sorry Spectra.InformationGeometry.Quantum.vonNeumannEntropy_indep
assert_no_sorry Spectra.InformationGeometry.Quantum.pureState
assert_no_sorry Spectra.InformationGeometry.Quantum.entropyOp_pure
assert_no_sorry Spectra.InformationGeometry.Quantum.vonNeumannEntropy_pure

-- The eigenbasis KEYSTONE: a positive trace-class operator is compact
-- (`IsTraceClass.isCompactOperator`, general; via `opNorm_le_hsNorm` + finite-rank truncation), so
-- Mathlib's compact self-adjoint spectral theorem assembles a genuine `HilbertBasis` of
-- eigenvectors (`eigenbasis`/`apply_eigenbasis`), and the CFC acts diagonally on eigenvectors
-- (`cfc_apply_eigenvector`).  Applied to a `QState`, the eigenvalues form a probability
-- distribution (`eigenvalue_nonneg`/`eigenvalue_le_one`/`hasSum_eigenvalue`), yielding the SPECTRAL
-- FORM of the von Neumann entropy `S(ρ) = ∑ᵢ negMulLog λᵢ` (`vonNeumannEntropy_eq_tsum`) and the
-- scalar Klein inequality (`Real.klein_scalar`) for the quantum relative entropy.
assert_no_sorry Spectra.QuantumMechanics.Channels.opNorm_le_hsNorm
assert_no_sorry Spectra.QuantumMechanics.Channels.IsHilbertSchmidt.isCompactOperator
assert_no_sorry Spectra.QuantumMechanics.Channels.IsTraceClass.isCompactOperator
assert_no_sorry Spectra.InformationGeometry.Quantum.eigenbasis
assert_no_sorry Spectra.InformationGeometry.Quantum.apply_eigenbasis
assert_no_sorry Spectra.InformationGeometry.Quantum.inner_eigenbasis_self
assert_no_sorry Spectra.InformationGeometry.Quantum.cfc_apply_eigenvector
assert_no_sorry Spectra.InformationGeometry.Quantum.inner_cfc_eigenvector
assert_no_sorry Spectra.InformationGeometry.Quantum.QState.isCompactOperator_toOp
assert_no_sorry Spectra.InformationGeometry.Quantum.QState.eigenvalue_nonneg
assert_no_sorry Spectra.InformationGeometry.Quantum.QState.eigenvalue_mem_spectrum
assert_no_sorry Spectra.InformationGeometry.Quantum.QState.eigenvalue_le_one
assert_no_sorry Spectra.InformationGeometry.Quantum.QState.hasSum_eigenvalue
assert_no_sorry Spectra.InformationGeometry.Quantum.QState.vonNeumannEntropy_eq_tsum
assert_no_sorry Real.klein_scalar
assert_no_sorry Real.mul_log_sub_mul_log_ge

-- M4 (quantum relative entropy), first leg: the bounded diagonal `sᵢ = ⟪eᵢ, σ eᵢ⟫` of a second
-- state `σ` in `ρ`'s eigenbasis is a probability distribution (`hasSum_diagSigma`), and the GIBBS /
-- commuting-case Klein inequality `S(ρ) ≤ ∑ᵢ -λᵢ log sᵢ` holds for faithful `σ`
-- (`vonNeumannEntropy_le_measuredCrossEntropy`) — the classical KL divergence of `ρ`'s eigenvalues
-- against `σ`'s dephased diagonal is nonnegative.
assert_no_sorry Spectra.InformationGeometry.Quantum.QState.diagSigma_nonneg
assert_no_sorry Spectra.InformationGeometry.Quantum.QState.diagSigma_le_one
assert_no_sorry Spectra.InformationGeometry.Quantum.QState.hasSum_diagSigma
assert_no_sorry Spectra.InformationGeometry.Quantum.QState.measuredCrossEntropy
assert_no_sorry Spectra.InformationGeometry.Quantum.QState.vonNeumannEntropy_le_measuredCrossEntropy

-- M4 (quantum relative entropy), full Umegaki leg: the quantum cross entropy `crossEntropy(ρ,σ) =
-- -Tr(ρ log σ)` is built in `ℝ≥0∞` from `σ`'s scalar spectral measure (never forming the unbounded
-- `log σ`), and the FULL Klein inequality `S(ρ) ≤ crossEntropy(ρ,σ)` holds for faithful `σ` — the
-- ordering form of the quantum relative entropy `D(ρ‖σ) ≥ 0`, proved via the tangent-line Jensen
-- inequality `∫ log t dμ_{eᵢ} ≤ log sᵢ`.  `crossEntropy_self` (`crossEntropy ρ ρ = S(ρ)`) is the
-- non-vacuity witness (`D(ρ‖ρ) = 0`).
assert_no_sorry Real.integral_log_le_log_of_probability
assert_no_sorry Spectra.InformationGeometry.Quantum.QState.crossEntropy
assert_no_sorry Spectra.InformationGeometry.Quantum.QState.measuredCrossEntropy_le_crossEntropy
assert_no_sorry Spectra.InformationGeometry.Quantum.QState.vonNeumannEntropy_le_crossEntropy
assert_no_sorry Spectra.InformationGeometry.Quantum.QState.crossEntropy_self

-- M5 foundation: classical Shannon entropy `H(p) = ∑ᵢ negMulLog pᵢ` of a discrete distribution,
-- and the identity `S(ρ) = H(λ(ρ))` — the von Neumann entropy is the Shannon entropy of the
-- eigenvalue distribution (the entry point for the Holevo bound).
assert_no_sorry Spectra.InformationGeometry.Quantum.shannonEntropy
assert_no_sorry Spectra.InformationGeometry.Quantum.vonNeumannEntropy_eq_shannonEntropy

-- M1 (classical Shannon entropy) — the analytic core: nonnegativity, the point-mass
-- characterization `H(p) = 0 ↔ ∀ i, pᵢ ∈ {0,1}`, concavity (mixing never decreases entropy), and
-- additivity under independent products `H(p⊗q) = H(p) + H(q)` (the chain rule for independent
-- variables).
assert_no_sorry Spectra.InformationGeometry.Quantum.shannonEntropy_nonneg
assert_no_sorry Spectra.InformationGeometry.Quantum.shannonEntropy_eq_zero_iff
assert_no_sorry Spectra.InformationGeometry.Quantum.shannonEntropy_concave
assert_no_sorry Spectra.InformationGeometry.Quantum.shannonEntropy_prod

-- M6 (quantum thermodynamics): the Gibbs variational principle `S(ρ) ≤ ⟨K⟩_ρ` (modular energy
-- `⟨K⟩_ρ = -Tr(ρ log σ)`, `K = -log σ` the modular Hamiltonian of the thermal state `σ`) — the
-- operator-algebraic form of "a thermal state maximizes entropy at fixed energy", which is Klein's
-- inequality; saturated at `σ` (`modularEnergy_self`), giving the maximum-entropy principle.
assert_no_sorry Spectra.InformationGeometry.Quantum.modularEnergy
assert_no_sorry Spectra.InformationGeometry.Quantum.entropy_le_modularEnergy
assert_no_sorry Spectra.InformationGeometry.Quantum.modularEnergy_self
assert_no_sorry Spectra.InformationGeometry.Quantum.maxEntropy_of_modularEnergy_eq
-- The Bogoliubov–Kubo–Mori (BKM) metric object and its well-definedness (G4a): the integrand kernel
-- `K_τ(A,B) = tr(A τ⁻¹ B τ⁻¹)` is trace-class (via the trace-class ideal), bilinear, symmetric (one
-- cyclicity step), and positive-semidefinite (`tr((τ^{-1/2}Aτ^{-1/2})⋆(·))`); the metric
-- `bkmMetric ρ A B = ∫_{s>0} re K_{ρ+s}(A,B)` inherits symmetry and positive-semidefiniteness.
assert_no_sorry Spectra.InformationGeometry.Quantum.bkmKernel
assert_no_sorry Spectra.InformationGeometry.Quantum.bkmKernel_isTraceClass
assert_no_sorry Spectra.InformationGeometry.Quantum.bkmKernel_comm
assert_no_sorry Spectra.InformationGeometry.Quantum.bkmKernel_self_re_nonneg
assert_no_sorry Spectra.InformationGeometry.Quantum.bkmMetric
assert_no_sorry Spectra.InformationGeometry.Quantum.bkmMetric_comm
assert_no_sorry Spectra.InformationGeometry.Quantum.bkmMetric_self_nonneg

/-! ## Information geometry -/

assert_no_sorry Spectra.InformationGeometry.RegularStatisticalModel.cramerRao_scalar
assert_no_sorry Spectra.InformationGeometry.TwiceDifferentiableModel.klDiv_hessian_eq_fisher
-- The information-geometric Stone theorem: refutation of global flow-completeness for bounded
-- domains (why `FlowComplete` is domain-relative), invariant-set flow uniqueness, and the
-- packaged existence-plus-uniqueness statement.
assert_no_sorry
  Spectra.InformationGeometry.TwiceDifferentiableModel.not_forall_hasGlobalFlow_of_isBounded
assert_no_sorry Spectra.InformationGeometry.TwiceDifferentiableModel.flow_eqOn_of_generator_eqOn
assert_no_sorry Spectra.InformationGeometry.TwiceDifferentiableModel.infoGeometric_stone_unique
assert_no_sorry Spectra.InformationGeometry.TwiceDifferentiableModel.infoGeometric_stone
-- The classical–quantum dichotomy: classical-bit rigidity, the qubit generator classification
-- (every generator is `c·∂_β` on the domain), and their conjunction.
assert_no_sorry Spectra.InformationGeometry.GeometricData.classicalBit_rigid
assert_no_sorry Spectra.InformationGeometry.GeometricData.qubit_generator_azimuthal
assert_no_sorry Spectra.InformationGeometry.GeometricData.classical_quantum_dichotomy
-- The m-connection transformation law: cubic-tensor preservation (the key intermediate step)
-- and the main law, each a `#print axioms`-worthy capstone of the four-file
-- MixtureSymmetry → ThirdDerivative → PullbackIdentities → MixtureConnection cluster — gating
-- the final theorem transitively certifies every lemma it depends on throughout that chain.
open Spectra.InformationGeometry.ThriceDifferentiableModel.DivergencePreservingFamily in
assert_no_sorry preserves_cubic_basis
open Spectra.InformationGeometry.ThriceDifferentiableModel.DivergencePreservingFamily in
assert_no_sorry mConnection_correction

/-! ## Hilbert tensor product `E ⊗̂[𝕜] F` (Fock Spaces M0) -/

-- The completed tensor product of inner product spaces: inner product and cross norm on
-- pure tensors, density of pure-tensor span, and isometric functoriality through the
-- completion (map/congr/comm/lid/assoc). Closes Mathlib's "Complete space of tensor
-- products" TODO on the Spectra side.
assert_no_sorry Spectra.HilbertTensor.inner_tmul_tmul
assert_no_sorry Spectra.HilbertTensor.norm_tmul
assert_no_sorry Spectra.HilbertTensor.dense_span_tmul
assert_no_sorry Spectra.HilbertTensor.span_tmul_topologicalClosure
assert_no_sorry Spectra.HilbertTensor.tmulL
assert_no_sorry Spectra.HilbertTensor.map_tmul
assert_no_sorry Spectra.HilbertTensor.congr_tmul
assert_no_sorry Spectra.HilbertTensor.comm_tmul
assert_no_sorry Spectra.HilbertTensor.lid_tmul
assert_no_sorry Spectra.HilbertTensor.assoc_tmul
-- General completion functoriality for linear isometries (upstream candidates).
assert_no_sorry LinearIsometry.completionMap_coe
assert_no_sorry LinearIsometryEquiv.completionMap_coe
-- Bounded functoriality `A ⊗̂ B` (`Spaces/Tensor/Map.lean`): the orthonormal fiber
-- representation, tensor Pythagoras, the rTensor/lTensor/map operator bounds, and the
-- cross-norm identity `‖A ⊗̂ B‖ = ‖A‖·‖B‖` on both the algebraic and completed products.
assert_no_sorry Spectra.HilbertTensor.exists_sum_tmul_orthonormal
assert_no_sorry Spectra.HilbertTensor.norm_sq_sum_tmul_orthonormal
assert_no_sorry Spectra.HilbertTensor.norm_rTensor_apply_le
assert_no_sorry Spectra.HilbertTensor.norm_lTensor_apply_le
assert_no_sorry Spectra.HilbertTensor.norm_map_apply_le
assert_no_sorry Spectra.HilbertTensor.mapCLM
assert_no_sorry Spectra.HilbertTensor.norm_mapCLM
assert_no_sorry Spectra.HilbertTensor.mapL
assert_no_sorry Spectra.HilbertTensor.mapL_tmul
assert_no_sorry Spectra.HilbertTensor.norm_mapL
-- `‖f.completion‖ = ‖f‖`, companion to `ContinuousLinearMap.completion` (upstream candidate).
assert_no_sorry ContinuousLinearMap.norm_completion
-- The tensor Hilbert basis (`Spaces/Tensor/Basis.lean`): Hilbert bases of the factors
-- tensor to a Hilbert basis of `E ⊗̂[𝕜] F`, indexed by `ι × κ`.
assert_no_sorry Spectra.HilbertTensor.orthonormal_tmul
assert_no_sorry Spectra.HilbertTensor.dense_span_tensor
assert_no_sorry Spectra.HilbertTensor.tensorHilbertBasis
assert_no_sorry Spectra.HilbertTensor.tensorHilbertBasis_apply

/-! ## Tensor powers `⨂[𝕜]^n H` and the full Fock space (Fock Spaces M1) -/

-- The inner product space structure on the algebraic n-fold tensor power
-- (`Spaces/Tensor/PowerInner.lean`) — the PiTensorProduct generalization of Mathlib's
-- binary construction: ⟪⨂ₜ x, ⨂ₜ y⟫ = ∏ ⟪x i, y i⟫, positive-definiteness by induction
-- through the splitting (⨂ⁿH) ⊗ H ≃ ⨂ⁿ⁺¹H and the orthonormal fiber representation.
assert_no_sorry Spectra.TensorPower.instInner
assert_no_sorry Spectra.TensorPower.instNormedAddCommGroup
assert_no_sorry Spectra.TensorPower.instInnerProductSpace
assert_no_sorry Spectra.TensorPower.inner_tprod_tprod
assert_no_sorry Spectra.TensorPower.norm_tprod
-- The Hilbert tensor power (`Spaces/Tensor/Power.lean`): the completed n-particle sector,
-- with pure tensors, dense span, and the permutation unitaries feeding symmetrization.
assert_no_sorry Spectra.HilbertTensorPower.inner_tprod_tprod
assert_no_sorry Spectra.HilbertTensorPower.norm_tprod
assert_no_sorry Spectra.HilbertTensorPower.dense_span_tprod
assert_no_sorry Spectra.HilbertTensorPower.permUnitary
assert_no_sorry Spectra.HilbertTensorPower.permUnitary_tprod
-- The full Fock space (`Spaces/Fock/Basic.lean`): the Hilbert sum of the sectors.
assert_no_sorry Spectra.fullFock

/-! ## Symmetrizers, Bose/Fermi Fock spaces, and the Krein–Fock lift (Fock Spaces M2) -/

-- M2 symmetrizers (`Spaces/Fock/Symmetrizer.lean`): the permutation-unitary group law on the
-- n-particle sector and the symmetrizer/antisymmetrizer as self-adjoint contractive idempotents.
assert_no_sorry Spectra.HilbertTensorPower.permUnitary_comp
assert_no_sorry Spectra.HilbertTensorPower.symProj
assert_no_sorry Spectra.HilbertTensorPower.altProj
assert_no_sorry Spectra.HilbertTensorPower.symProj_idem
assert_no_sorry Spectra.HilbertTensorPower.altProj_idem
assert_no_sorry Spectra.HilbertTensorPower.isSelfAdjoint_symProj
assert_no_sorry Spectra.HilbertTensorPower.isSelfAdjoint_altProj
assert_no_sorry Spectra.HilbertTensorPower.norm_symProj_le
-- M2 sectors (`Spaces/Fock/BoseFermi.lean`): the bosonic/fermionic sectors as closed subspaces
-- (permutation-(anti)invariant vectors), Pauli exclusion, sector disjointness for n ≥ 2, and
-- the bosonic/fermionic Fock spaces as Hilbert sums of the sectors.
assert_no_sorry Spectra.HilbertTensorPower.symPower
assert_no_sorry Spectra.HilbertTensorPower.altPower
assert_no_sorry Spectra.HilbertTensorPower.mem_symPower_iff_forall
assert_no_sorry Spectra.HilbertTensorPower.mem_altPower_iff_forall
assert_no_sorry Spectra.HilbertTensorPower.altProj_tprod_eq_zero
assert_no_sorry Spectra.HilbertTensorPower.symPower_inf_altPower
assert_no_sorry Spectra.boseFock
assert_no_sorry Spectra.fermiFock
-- Sector functoriality Γₙ (`Spaces/Tensor/PowerCongr.lean`): a unitary `H ≃ H'` lifts
-- isometrically to the completed tensor powers, functorially in the unitary.
assert_no_sorry Spectra.HilbertTensorPower.congr
assert_no_sorry Spectra.HilbertTensorPower.congr_tprod
assert_no_sorry Spectra.HilbertTensorPower.congr_trans
assert_no_sorry Spectra.HilbertTensorPower.congr_refl
assert_no_sorry Spectra.HilbertTensorPower.congr_symm
assert_no_sorry Spectra.HilbertTensorPower.inner_congr_left
-- lp congruence (`Spaces/HilbertSum/Congr.lean`): componentwise unitaries assemble into a
-- unitary of Hilbert sums (upstream candidates; norm/membership transfer holds for all `p`).
assert_no_sorry memℓp_congrRight_iff
assert_no_sorry lp.norm_congr
assert_no_sorry LinearIsometryEquiv.lpCongrRight
assert_no_sorry LinearIsometryEquiv.lpCongrRight_apply
assert_no_sorry LinearIsometryEquiv.lpCongrRight_symm
assert_no_sorry LinearIsometryEquiv.lpCongrRight_trans
-- Krein spaces (`Spaces/Krein/Basic.lean`): fundamental symmetries, the indefinite inner
-- product, the fundamental decomposition H = H₊ ⊕ H₋, and the Krein adjoint.
assert_no_sorry Spectra.FundamentalSymmetry.isometryEquiv_trans_self
assert_no_sorry Spectra.FundamentalSymmetry.posPart_sup_negPart
assert_no_sorry Spectra.FundamentalSymmetry.negPart_eq_orthogonal
assert_no_sorry Spectra.FundamentalSymmetry.kreinInner_self_of_mem_posPart
assert_no_sorry Spectra.FundamentalSymmetry.kreinInner_self_of_mem_negPart
assert_no_sorry Spectra.FundamentalSymmetry.kreinInner_map_left
assert_no_sorry Spectra.FundamentalSymmetry.kreinAdjoint_kreinAdjoint
assert_no_sorry Spectra.FundamentalSymmetry.isKreinSelfAdjoint_iff_isSelfAdjoint_comp
-- Krein–Fock lift (`Spaces/Krein/Fock.lean`): Γ(J) — a fundamental symmetry on the
-- one-particle space lifts to the Gupta–Bleuler indefinite metric on the full Fock space.
assert_no_sorry Spectra.FundamentalSymmetry.powerLift
assert_no_sorry Spectra.FundamentalSymmetry.powerLift_tprod
assert_no_sorry Spectra.FundamentalSymmetry.fockLiftEquiv
assert_no_sorry Spectra.FundamentalSymmetry.inner_fockLiftEquiv_left
assert_no_sorry Spectra.FundamentalSymmetry.fockSymmetry
assert_no_sorry Spectra.FundamentalSymmetry.kreinInner_fockSymmetry
assert_no_sorry Spectra.FundamentalSymmetry.fockSymmetry_id_apply
-- M2 non-degeneracy (`Spaces/Fock/BoseFermi.lean`): constant tensors are bosonic, and the
-- Slater normalization ‖altProj (⨂ₜ x)‖² = (n!)⁻¹ for orthonormal x makes the fermionic
-- sector visibly nonzero — the sectors are not vacuous subspaces.
assert_no_sorry Spectra.HilbertTensorPower.tprod_const_mem_symPower
assert_no_sorry Spectra.HilbertTensorPower.symPower_ne_bot
assert_no_sorry Spectra.HilbertTensorPower.norm_sq_altProj_tprod
assert_no_sorry Spectra.HilbertTensorPower.altProj_tprod_ne_zero_of_orthonormal
assert_no_sorry Spectra.HilbertTensorPower.altPower_ne_bot
-- Γₙ intertwines permutations (`Spaces/Tensor/PowerCongr.lean`), hence Γₙ(J) preserves the
-- bosonic/fermionic sectors (`Spaces/Krein/Fock.lean`): the Gupta–Bleuler metric restricts.
assert_no_sorry Spectra.HilbertTensorPower.congr_permUnitary
assert_no_sorry Spectra.FundamentalSymmetry.powerLift_mem_symPower
assert_no_sorry Spectra.FundamentalSymmetry.powerLift_mem_altPower
-- Krein spectral projections project onto the parts, and the diag(1, −1) witness on 𝕜²
-- exhibits a Krein form taking both signs (`Spaces/Krein/Basic.lean`).
assert_no_sorry Spectra.FundamentalSymmetry.range_posProj
assert_no_sorry Spectra.FundamentalSymmetry.range_negProj
assert_no_sorry Spectra.FundamentalSymmetry.diagSymmetry
assert_no_sorry Spectra.FundamentalSymmetry.kreinInner_diagSymmetry_single_zero
assert_no_sorry Spectra.FundamentalSymmetry.kreinInner_diagSymmetry_single_one

/-! ## Vacuum, sectors, number operator, exponential vectors (Fock Spaces M3) -/

-- Sector embeddings and the vacuum (`Spaces/Fock/Sector.lean`): `lp.single` bundled as a
-- linear isometry, orthogonal sector embeddings into the full/bose/fermi Fock spaces, the
-- normalized vacuum vectors, and the dense finite-particle cores.
assert_no_sorry lp.dense_iSup_range_lsingle
assert_no_sorry Spectra.fockSector
assert_no_sorry Spectra.inner_fockSector_of_ne
assert_no_sorry Spectra.fockVacuum
assert_no_sorry Spectra.norm_fockVacuum
assert_no_sorry Spectra.boseVacuum
assert_no_sorry Spectra.dense_finParticle
assert_no_sorry Spectra.dense_boseFinParticle
assert_no_sorry Spectra.dense_fermiFinParticle
-- Exponential (coherent) vectors (`Spaces/Fock/Exponential.lean`), Parthasarathy convention
-- `ε(f)ₙ = (√n!)⁻¹ f^⊗n`: the inner-product formula `⟪ε(f), ε(g)⟫ = exp ⟪f, g⟫` and
-- `‖ε(f)‖² = exp ‖f‖²`.
assert_no_sorry Spectra.expVec
assert_no_sorry Spectra.expVec_apply
assert_no_sorry Spectra.inner_expVec_expVec
assert_no_sorry Spectra.norm_expVec_sq
assert_no_sorry Spectra.expVec_ne_zero
-- Polarization (`Spaces/Fock/Polarization.lean`): the inclusion–exclusion identity
-- `n! • symProj (⨂ₜ x) = ∑_{S ⊆ [n]} (−1)^{n−|S|} (∑_{i∈S} xᵢ)^{⊗n}`, hence tensor powers
-- span a dense subspace of the bosonic sector.
assert_no_sorry Spectra.HilbertTensorPower.polarization_symProj_tprod
assert_no_sorry Spectra.HilbertTensorPower.symProj_tprod_mem_span_powers
assert_no_sorry Spectra.HilbertTensorPower.topologicalClosure_span_tprod_const
-- The number operator (`Spaces/Fock/NumberOp.lean`): the diagonal multiplier `(Nξ)ₙ = n ξₙ`
-- on its natural dense domain is SELF-ADJOINT (adjoint domain forced by sector testing),
-- with `N (sector n x) = n • sector n x`, `N Ω = 0`, and `⟪ξ, Nξ⟫ ≥ 0`.
assert_no_sorry Spectra.numberOp
assert_no_sorry Spectra.dense_numberDomain
assert_no_sorry Spectra.numberOp_isFormalAdjoint_self
assert_no_sorry Spectra.numberOp_isSelfAdjoint
assert_no_sorry Spectra.numberOp_fockSector
assert_no_sorry Spectra.re_inner_self_numberOp_nonneg
assert_no_sorry Spectra.numberOperator
-- ★ The M3 keystone (`Spaces/Fock/Total.lean`): exponential vectors are TOTAL in the bosonic
-- Fock space — the closed span of `{ε(f) : f ∈ H}` is everything. Load-bearing for the Weyl
-- operators (M5), second quantization (M6), and Fock irreducibility (M7).
assert_no_sorry Spectra.expVecSector_smul
assert_no_sorry Spectra.boseSector_expVecSector_mem
assert_no_sorry Spectra.boseSector_mem_of_forall_tprod_const
assert_no_sorry Spectra.expVec_total
assert_no_sorry Spectra.dense_span_expVec

/-! ## Sobolev spaces -/

-- `WeakDerivative.lean`: the foundational file for the whole directory (configuration space
-- `R3`, Hilbert space `l2R3`, the `HasWeakDerivative` distributional pairing, and the closure
-- lemmas for smooth compactly supported test functions that everything downstream reuses).
assert_no_sorry Spectra.Sobolev.memLp_of_smooth_compactSupport
assert_no_sorry Spectra.Sobolev.hasCompactSupport_partialDeriv
assert_no_sorry Spectra.Sobolev.contDiff_partialDeriv
assert_no_sorry Spectra.Sobolev.memLp_partialDeriv
assert_no_sorry Spectra.Sobolev.meyers_serrin_approx
assert_no_sorry Spectra.Sobolev.meyers_serrin_approx_multi
assert_no_sorry Spectra.Sobolev.sobolev_embedding_L6
-- Meyers–Serrin mollification step: bump convolution simultaneously approximates a compactly
-- supported L² function and its weak derivative(s) by a smooth compactly supported function.
assert_no_sorry Spectra.Sobolev.mollify_compactly_supported
assert_no_sorry Spectra.Sobolev.mollify_compactly_supported_multi
-- Density chain L² ← C_c ← C_c^∞: the capstone and its own load-bearing dependency, consumed by
-- `DuBoisReymond.lean`, `DensityResults.lean`, and `MeyersCommon.lean`.
assert_no_sorry Spectra.Sobolev.dense_test_functions_L2
assert_no_sorry Spectra.Sobolev.dense_continuous_compactSupport_L2
-- `DuBoisReymond.lean`: the fundamental lemma of the calculus of variations for L²(ℝ³,ℂ) and its
-- corollary, uniqueness of the weak derivative.
assert_no_sorry Spectra.Sobolev.inner_L2_test_eq_zero
assert_no_sorry Spectra.Sobolev.eq_zero_of_integral_against_test_eq_zero
assert_no_sorry Spectra.Sobolev.hasWeakDerivative_unique
-- `Operations.lean`: the calculus of weak derivatives (closure under `0`/`+`/`•`, Schwarz
-- symmetry, and uniqueness of second weak derivatives) — consumed by `Submodules.lean`'s
-- `Submodule` instance and by the Hydrogen-atom formalization (`RadialEigenfunction/`,
-- `SectorProjection.lean`, `Eigenpair.lean`).
assert_no_sorry Spectra.Sobolev.hasWeakDerivative_zero
assert_no_sorry Spectra.Sobolev.hasWeakDerivative_add
assert_no_sorry Spectra.Sobolev.hasWeakDerivative_smul
assert_no_sorry Spectra.Sobolev.hasWeakSecondDerivative_comm
assert_no_sorry Spectra.Sobolev.hasWeakSecondDerivative_unique
-- `Submodules.lean`: `SobolevH1`/`SobolevH2` as `Submodule ℂ l2R3`, the weak gradient/Dirichlet
-- norm, and the weak Laplacian `-Δ` bundled as a linear map — consumed by `IntegrationByParts.lean`
-- and, downstream, the Hydrogen/Dirac Laplacian developments.
assert_no_sorry Spectra.Sobolev.sobolevH2_le_sobolevH1
assert_no_sorry Spectra.Sobolev.laplacianLinearMap
-- `IntegrationByParts.lean`: the no-boundary integration-by-parts identity for the weak Laplacian
-- on `ℝ³` and its corollaries (symmetry, the Dirichlet energy identity, non-negativity, and
-- first-order skew-symmetry of the weak gradient) — consumed by `DensityResults.lean`,
-- `Embeddings.lean`, and the Hydrogen/Dirac Laplacian developments.
assert_no_sorry Spectra.Sobolev.integration_by_parts
assert_no_sorry Spectra.Sobolev.laplacian_symmetric
assert_no_sorry Spectra.Sobolev.gradient_norm_sq_eq_laplacian_inner
assert_no_sorry Spectra.Sobolev.laplacian_nonneg
assert_no_sorry Spectra.Sobolev.weakGradient_inner_skew
-- `DensityResults.lean`: the two headline density results the operator theory needs to build
-- `-Δ` with a core — `H²(ℝ³)` dense in `L²(ℝ³)`, and `C_c^∞(ℝ³)` dense in `H¹(ℝ³)` — plus the
-- two supporting lemmas that identify smooth compactly supported functions with their weak
-- derivatives / full `H²` membership.
assert_no_sorry Spectra.Sobolev.hasWeakDerivative_of_smooth_compactSupport
assert_no_sorry Spectra.Sobolev.smooth_compactSupport_memSobolevH2
assert_no_sorry Spectra.Sobolev.sobolevH2_dense
assert_no_sorry Spectra.Sobolev.smooth_compactly_supported_dense_H1

/-! ## Density Functional Theory — variational substrate, N-electron space, Fenchel library

The S0-independent, gate-light lanes of the DFT project: the abstract Rayleigh–Ritz variational
principle (S2/S3), the named `N`-electron antisymmetric space with its Slater reference state (S1),
and the standalone Legendre–Fenchel library shared with Information Geometry (FD1/FD3). Every open
research input (⛔S0, ⛔SB, ⛔SUCP, ⛔GSE, ⛔VR) is carried as an explicit hypothesis, never an axiom. -/

-- `DFT/Variational/Semibounded.lean` (S3): bottom of the spectrum of a semibounded operator.
assert_no_sorry Spectra.DFT.spectrum_subset_Ici
assert_no_sorry Spectra.DFT.spectrum_subset_Ici_groundStateEnergy
assert_no_sorry Spectra.DFT.groundStateEnergy_mem_spectrum
-- `DFT/Variational/RayleighRitz.lean` (S2 + HK1S): the variational principle, its equality case,
-- and the strict / nondegeneracy forms that drive Hohenberg–Kohn I.
assert_no_sorry Spectra.DFT.groundStateEnergy_le_rayleigh
assert_no_sorry Spectra.DFT.eigenvector_of_rayleigh_eq_groundStateEnergy
assert_no_sorry Spectra.DFT.sInf_rayleigh_eq_groundStateEnergy
assert_no_sorry Spectra.DFT.groundStateEnergy_lt_rayleigh_of_not_eigenvector
assert_no_sorry Spectra.DFT.groundStateEnergy_lt_rayleigh_of_not_scalar_multiple
assert_no_sorry Spectra.DFT.ground_state_unique_up_to_phase
-- `DFT/State/AntisymmetricSpace.lean` (S1): the normalized Slater reference state and Pauli
-- exclusion.
assert_no_sorry Spectra.DFT.norm_slaterDet
assert_no_sorry Spectra.DFT.slaterDet_eq_zero
assert_no_sorry Spectra.DFT.NElectronSpace_ne_bot
-- `Analysis/Convex/Fenchel/Conjugate.lean` (FD1 + FD3): Fenchel–Young inequality and the
-- subdifferential's Fenchel–Young equality characterization.
assert_no_sorry Spectra.le_fenchelConj_add
assert_no_sorry Spectra.le_concaveConj_add
assert_no_sorry Spectra.mem_subgradient_iff_fenchelConj_add_eq
-- `Analysis/Convex/Fenchel/Conjugate.lean` (FD2): the biconjugate `f**`, the unconditional
-- Fenchel–Moreau core (`f** ≤ f`, `f*** = f*`, `f**** = f**`), and the conditional Fenchel–Moreau
-- equality `f** = f` for `f` a supremum of pairing-affine functions (the honest
-- Hahn–Banach-free form).
assert_no_sorry Spectra.biconjugate_le
assert_no_sorry Spectra.fenchelConj_biconjugate
assert_no_sorry Spectra.biconjugate_biconjugate
assert_no_sorry Spectra.biconjugate_eq_of_eq_iSup_affine
-- `DFT/State/CoordinatePermutation.lean` (S0-iii substrate): the measure-preserving `Lp`-unitary
-- builder (a mathlib gap-fill), the coordinate-permutation action, and the closed antisymmetric
-- `L²` subspace (the deferred coordinate realization's target object).
assert_no_sorry Spectra.lpEquivₗᵢOfMeasurePreserving
assert_no_sorry Spectra.DFT.coordPerm
assert_no_sorry Spectra.DFT.isClosed_antisymL2
-- `Operator/Unitary/Conjugation.lean` (Stage SB transport tool): unitary conjugation `U A U⁻¹`
-- preserves self-adjointness and energy nonnegativity — the linchpin for carrying the kinetic
-- operator `−½Δ` onto the `N`-electron coordinate space `nBodyL2 N`.
assert_no_sorry Spectra.Operator.unitaryConj_isSelfAdjoint
assert_no_sorry Spectra.Operator.unitaryConj_re_inner_nonneg

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
#print axioms Spectra.QuantumMechanics.Channels.IsHilbertSchmidt.isTraceClass_comp
#print axioms Spectra.QuantumMechanics.Channels.IsTraceClass.comp_left
#print axioms Spectra.QuantumMechanics.Channels.IsTraceClass.comp_right
#print axioms Spectra.QuantumMechanics.Channels.isTraceClass_sqrtOp_absOp_comp
#print axioms Spectra.QuantumMechanics.Channels.traceNorm_comp_le
#print axioms Spectra.QuantumMechanics.Channels.fidelity_le_sqrt_mul
#print axioms Spectra.QuantumMechanics.Channels.traceNorm_adjoint
#print axioms Spectra.QuantumMechanics.Channels.fidelity_comm
#print axioms Spectra.QuantumMechanics.Channels.norm_traceFunctional
#print axioms Spectra.QuantumMechanics.Channels.traceDualₗᵢ
#print axioms Spectra.InformationGeometry.Quantum.entropyOp_nonneg
#print axioms Spectra.InformationGeometry.Quantum.vonNeumannEntropy_pure
#print axioms Spectra.QuantumMechanics.Channels.IsTraceClass.isCompactOperator
#print axioms Spectra.InformationGeometry.Quantum.eigenbasis
#print axioms Spectra.InformationGeometry.Quantum.QState.vonNeumannEntropy_eq_tsum
#print axioms Spectra.InformationGeometry.Quantum.QState.vonNeumannEntropy_le_measuredCrossEntropy
#print axioms Spectra.InformationGeometry.Quantum.QState.vonNeumannEntropy_le_crossEntropy
#print axioms Spectra.InformationGeometry.Quantum.QState.crossEntropy_self
#print axioms Spectra.InformationGeometry.Quantum.bkmKernel_self_re_nonneg
#print axioms Spectra.InformationGeometry.Quantum.bkmMetric_self_nonneg
#print axioms Spectra.QuantumMechanics.Channels.isPositiveMatrix_one_iff
#print axioms Spectra.QuantumMechanics.Channels.IsCompletelyPositive.isPositive
#print axioms Spectra.QuantumMechanics.Channels.QuantumChannel.id_toFun_apply
#print axioms Spectra.Resolvent.spectrum_subset_closure_numericalRange
#print axioms Spectra.Operator.isEssentiallySelfAdjoint_of_denseRange_addSub
#print axioms Spectra.Operator.isEssentiallySelfAdjoint_sumOp_of_denseRange_addSub
#print axioms Spectra.Operator.deficiencySubspacesBot_iff_denseRange_addSub
#print axioms Spectra.Operator.vonNeumannExtension_isSelfAdjoint
#print axioms Spectra.Operator.exists_le_isSelfAdjoint_iff_nonempty_deficiencyEquiv
#print axioms Spectra.Operator.eq_vonNeumannExtension_inducedDeficiencyEquiv
#print axioms Spectra.Operator.selfAdjointExtensionEquiv
#print axioms Spectra.Operator.isEssentiallySelfAdjoint_iff_existsUnique_le_isSelfAdjoint
#print axioms Spectra.Operator.adjoint_adjoint_eq_closure
#print axioms Spectra.Operator.vonNeumannFormula
#print axioms Spectra.Operator.existsUnique_deficiency_decomposition
#print axioms Spectra.Operator.vonNeumannFormula_closure
#print axioms Spectra.Operator.vonNeumannExtensionOn_isFormalAdjoint
#print axioms Spectra.Operator.exists_eq_vonNeumannExtensionOn
#print axioms Spectra.Operator.inducedDefectDomain_vonNeumannExtensionOn
#print axioms Spectra.Operator.nonempty_linearIsometryEquiv_of_antiunitary
#print axioms Spectra.Operator.exists_le_isSelfAdjoint_of_conjugation
#print axioms Spectra.Operator.isClosable_iff_dense_adjoint_domain
#print axioms Spectra.Operator.mem_spectrum_iff_exists_weylSequence
#print axioms Spectra.Resolvent.mem_resolventSet_of_boundedBelow_real
#print axioms Spectra.Operator.vonNeumannExtensionOn_isSelfAdjoint_iff
#print axioms Spectra.Operator.vonNeumannExtensionOn_isClosed_iff
#print axioms Spectra.QuantumMechanics.SpectralTheory.pmapOfPVM_isSelfAdjoint_of_real
#print axioms Spectra.QuantumMechanics.SpectralTheory.pmapOfPVM_domain_dense_of_support_Ioi
#print axioms Spectra.TomitaTakesaki.modularOpInv
#print axioms Spectra.TomitaTakesaki.modularSqrtInv
#print axioms Spectra.TomitaTakesaki.modularOpInv_isSelfAdjoint_of_dense
#print axioms Spectra.TomitaTakesaki.modularSqrtInv_isSelfAdjoint_of_dense
#print axioms Spectra.TomitaTakesaki.modularOpInv_isSelfAdjoint
#print axioms Spectra.TomitaTakesaki.modularSqrtInv_isSelfAdjoint
#print axioms Spectra.TomitaTakesaki.modularSqrtInv_sq_apply
#print axioms Spectra.TomitaTakesaki.modularSqrt_hasCore_modularOp_domain
#print axioms Spectra.TomitaTakesaki.tomitaClosure_domain_eq_modularSqrt_domain
#print axioms Spectra.TomitaTakesaki.tomitaClosure_eq_modularW_modularSqrt
#print axioms Spectra.TomitaTakesaki.tomita_eq_modularConjugation_modularSqrt_full
#print axioms Spectra.TomitaTakesaki.conjModularSqrt_isSelfAdjoint
#print axioms Spectra.TomitaTakesaki.conjModularSqrt_borelMeasure_Iio_zero
#print axioms Spectra.QuantumMechanics.SpectralTheory.generator_eq_pmapOfPVM_of_flowSymbol
#print axioms Spectra.TomitaTakesaki.generator_modularFlow_eq_logModularOp
#print axioms Spectra.Operator.compPMap_adjoint_apply
#print axioms Spectra.TomitaTakesaki.blockOp_comp
#print axioms Spectra.TomitaTakesaki.blockOp_star
#print axioms Spectra.TomitaTakesaki.M2subalg
#print axioms Spectra.TomitaTakesaki.eq_blockOp
#print axioms Spectra.TomitaTakesaki.M2
#print axioms Spectra.TomitaTakesaki.modularAut
#print axioms Spectra.TomitaTakesaki.modularAut_add
#print axioms Spectra.TomitaTakesaki.inner_modularAut_modularFlow_vacuum
#print axioms Spectra.TomitaTakesaki.modularSqrtInv_modularSqrt_apply
#print axioms Spectra.TomitaTakesaki.modularSqrt_modularSqrtInv_apply
#print axioms Spectra.QuantumMechanics.SpectralTheory.pmapOfPVM_sq_genToGroup_eq
#print axioms Spectra.TomitaTakesaki.conjModularSqrtInv_eq_modularSqrt
#print axioms Spectra.TomitaTakesaki.modularConjugation_involutive
#print axioms Spectra.TomitaTakesaki.conjModularSqrt_eq_modularSqrtInv
#print axioms Spectra.TomitaTakesaki.conjModularOp_eq_modularOpInv
#print axioms Spectra.TomitaTakesaki.tomitaTakesaki_exists_of_invariance
#print axioms Spectra.KMS.State.isCyclic_gnsVonNeumann
#print axioms Spectra.KMS.State.gnsStarAlgHom_injective
#print axioms Spectra.TomitaTakesaki.isCyclic_M2_of_isCyclic
#print axioms Spectra.TomitaTakesaki.not_isSeparating_M2_wholeAlgebra
#print axioms Spectra.TomitaTakesaki.modularOp_rvdR_apply
#print axioms Spectra.TomitaTakesaki.tomitaClosure_adjoint_eq
#print axioms Spectra.TomitaTakesaki.modularConjugation_comm_modularFlow
#print axioms Spectra.HilbertTensor.dense_span_tmul
#print axioms Spectra.HilbertTensor.inner_tmul_tmul
#print axioms Spectra.HilbertTensor.norm_mapL
#print axioms Spectra.HilbertTensor.tensorHilbertBasis
#print axioms
  Spectra.InformationGeometry.TwiceDifferentiableModel.not_forall_hasGlobalFlow_of_isBounded
#print axioms Spectra.InformationGeometry.TwiceDifferentiableModel.infoGeometric_stone
#print axioms Spectra.InformationGeometry.GeometricData.qubit_generator_azimuthal
#print axioms Spectra.InformationGeometry.GeometricData.classical_quantum_dichotomy
open Spectra.InformationGeometry.ThriceDifferentiableModel.DivergencePreservingFamily in
#print axioms preserves_cubic_basis
open Spectra.InformationGeometry.ThriceDifferentiableModel.DivergencePreservingFamily in
#print axioms mConnection_correction
#print axioms Spectra.TensorPower.instInnerProductSpace
#print axioms Spectra.fullFock
#print axioms Spectra.boseFock
#print axioms Spectra.fermiFock
#print axioms Spectra.FundamentalSymmetry.fockSymmetry
#print axioms Spectra.expVec_total
#print axioms Spectra.numberOp_isSelfAdjoint
#print axioms Spectra.DFT.eigenvector_of_rayleigh_eq_groundStateEnergy
#print axioms Spectra.DFT.sInf_rayleigh_eq_groundStateEnergy
#print axioms Spectra.DFT.ground_state_unique_up_to_phase
#print axioms Spectra.DFT.norm_slaterDet
#print axioms Spectra.mem_subgradient_iff_fenchelConj_add_eq
#print axioms Spectra.biconjugate_le
#print axioms Spectra.fenchelConj_biconjugate
#print axioms Spectra.biconjugate_eq_of_eq_iSup_affine
#print axioms Spectra.lpEquivₗᵢOfMeasurePreserving
#print axioms Spectra.DFT.isClosed_antisymL2
#print axioms Spectra.Operator.unitaryConj_isSelfAdjoint
#print axioms Spectra.Operator.unitaryConj_re_inner_nonneg
