/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.DiracEquation.Operators
/-!
# Relativistic Thermodynamics of Quantum Evolution

This file establishes the equivalence between **unitarity** and **thermodynamic
invariance** in quantum mechanics, rebuilt on the constructed spectral calculus.
The old version of this file threaded a hypothesis quadruple
(`gen : Generator U_grp`, `hsa : gen.IsSelfAdjoint`, `E : Set ℝ → H →L[ℂ] H`,
`hE : IsSpectralMeasureFor E gen`) through every statement.  All four are now
constructed objects, so every theorem here is parametrized by `U_grp` alone and
**carries no hypotheses at all**.

## Main results

* `borelMeasure_unitary_invariant` — **THE FIRST LAW**: `μ_{U(t)ψ} = μ_ψ` as an
  equality of genuine `Measure`s.  Not just `⟨H⟩`, the entire probability
  distribution over energies is frozen.
* `quantum_liouville`, `spectral_moment_conserved`, `energyVariance_conserved` —
  setwise, moment, and uncertainty forms; each is one `rw` of the First Law.
* `unitary_of_borelMeasure_invariant` — **the converse (rigidity)**: any
  surjective `V : H →L[ℂ] H` preserving every diagonal spectral measure is
  unitary.  Derived from invariance alone (`B = univ` + polarization), without
  touching `U_grp.unitary`.
* `unitary_iff_borelMeasure_invariant` — the fundamental equivalence.
* `generator_group_comm` — `A (U(t)x) = U(t) (Ax)` on the domain; with the group's
  inner-product preservation this yields `energy_expectation_conserved` with no
  integral in sight.
* `FirstLawEquivalence` + `first_law` — the four-pillar structure (unitarity,
  symmetry, spectral invariance, energy conservation), now a theorem with **zero
  hypotheses**.
* Dirac applications: `electronProjection` / `positronProjection` (defined here
  directly from the constructed calculus), `electron_number_conserved`,
  `positron_number_conserved`, `charge_conserved`, `sector_orthogonal`,
  `dirac_first_law`.

**Note on the energy moment identity.**  The old route to energy conservation
went through `⟪Aψ, ψ⟫ = ∫ s dμ_ψ` on the full domain, which needed
self-adjointness.  Energy conservation itself needs neither: the generator
commutes with its own flow (`generator_group_comm`, the value-level companion of
`generator_domain_invariant`), and `U_grp.unitary` finishes it.  The diagonal
integral identity on *general* domain vectors is the truncation/resolvent
project flagged in `GeneratorLink.lean`; on spectrally supported vectors it is
already available there via `generator_spectralProjection`.

## Proof of the First Law

The proof never touches projections.  By `borelMeasure_fourier` and the abelian
group law,

  `∫ e^{iωs} dμ_{U(t)ψ} = ⟪U(t)ψ, U(s)U(t)ψ⟫ = ⟪U(t)ψ, U(t)U(s)ψ⟫ = ⟪ψ, U(s)ψ⟫
                       = ∫ e^{iωs} dμ_ψ`,

and Fourier uniqueness (`measure_ext_of_fourier`) concludes.  The classical
analogue is Liouville's theorem: Hamiltonian flow preserves phase-space volume;
unitary flow preserves spectral measure.

| Classical                          | Quantum                      |
|------------------------------------|------------------------------|
| Phase space volume                 | Spectral measure             |
| `∂ρ/∂t + {H,ρ} = 0`                | `μ_{U(t)ψ} = μ_ψ`            |
| Hamiltonian flow                   | Unitary group                |

## Axioms used

None.  Every spectral input is constructed from `U_grp`; the third pillar of
`FirstLawEquivalence` is symmetry (`generator_isFormalAdjoint`, a theorem), with
full self-adjointness deferred to the deficiency-index project
(`SelfAdjoint.lean`), per `Operators.lean`.

## References

- Stone, M.H. (1932). "On one-parameter unitary groups in Hilbert space"
- von Neumann, J. (1932). "Mathematical Foundations of Quantum Mechanics"
- Reed, M. & Simon, B. (1980). "Methods of Modern Mathematical Physics, Vol. I"
- Connes, A. & Rovelli, C. (1994). "Von Neumann algebra automorphisms and
  time-thermodynamics relation in general covariant quantum theories"
-/
open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace
open Spectra.Borel
open SpectralMeasure
open Spectra.Fourier

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open Spectra.OneParameterUnitaryGroup

namespace Spectra.QuantumMechanics.SpectralTheory

variable (U_grp : OneParameterUnitaryGroup (H := H))

/-! ## Group algebra -/

/-- The flow is abelian: `U(s) (U(t) ψ) = U(t) (U(s) ψ)`.  (`group_law` + `add_comm`;
the pattern inside `generator_domain_invariant`, exported.) -/
lemma group_apply_comm (s t : ℝ) (ψ : H) :
    U_grp.U s (U_grp.U t ψ) = U_grp.U t (U_grp.U s ψ) := by
  rw [← ContinuousLinearMap.comp_apply, ← U_grp.group_law, add_comm s t, U_grp.group_law,
    ContinuousLinearMap.comp_apply]

/-- Each `U(t)` is surjective: `U(−t)` is a right inverse by the group law. -/
lemma unitary_group_surjective (t : ℝ) : Function.Surjective (U_grp.U t) := fun ψ =>
  ⟨U_grp.U (-t) ψ, by
    rw [← ContinuousLinearMap.comp_apply, ← U_grp.group_law, add_neg_cancel,
      U_grp.identity, ContinuousLinearMap.id_apply]⟩

/-- `U(t)` is unitary in the operator-algebraic sense: `U(t)* U(t) = 1 = U(t) U(t)*`.
Both halves are the group law at `±t`, since `U(t)* = U(−t)` (`inverse_eq_adjoint`). -/
theorem mem_unitary (t : ℝ) : U_grp.U t ∈ _root_.unitary (H →L[ℂ] H) := by
  have hL : star (U_grp.U t) * U_grp.U t = 1 := by
    ext ψ
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.star_eq_adjoint]
    rw [← inverse_eq_adjoint U_grp t, ← ContinuousLinearMap.comp_apply, ← U_grp.group_law,
      neg_add_cancel, U_grp.identity, ContinuousLinearMap.id_apply]
  have hR : U_grp.U t * star (U_grp.U t) = 1 := by
    ext ψ
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.star_eq_adjoint]
    rw [← inverse_eq_adjoint U_grp t, ← ContinuousLinearMap.comp_apply, ← U_grp.group_law,
      add_neg_cancel, U_grp.identity, ContinuousLinearMap.id_apply]
  exact Unitary.mem_iff.mpr ⟨hL, hR⟩

/-! ## The First Law -/

/-- **THE FIRST LAW of quantum thermodynamics**: the diagonal spectral measure is
invariant under the flow, `μ_{U(t)ψ} = μ_ψ` — an equality of `Measure`s, so every
integral statement downstream is a rewrite.

**Physical meaning**: the probability of measuring energy in any Borel set is the
same before and after time evolution.  In thermodynamics the first law says energy
is conserved; here the ENTIRE probability distribution over energies is conserved.

**Proof**: Fourier uniqueness.  Both measures have the same characteristic
function, because the flow is abelian and inner-product preserving:
`⟪U(t)ψ, U(s)(U(t)ψ)⟫ = ⟪U(t)ψ, U(t)(U(s)ψ)⟫ = ⟪ψ, U(s)ψ⟫`. -/
theorem borelMeasure_unitary_invariant (t : ℝ) (ψ : H) :
    borelMeasure U_grp (U_grp.U t ψ) = borelMeasure U_grp ψ := by
  haveI : IsFiniteMeasure (borelMeasure U_grp (U_grp.U t ψ)) :=
    borelMeasure_isFiniteMeasure U_grp (U_grp.U t ψ)
  haveI : IsFiniteMeasure (borelMeasure U_grp ψ) := borelMeasure_isFiniteMeasure U_grp ψ
  refine measure_ext_of_fourier fun s => ?_
  rw [← borelMeasure_fourier U_grp (U_grp.U t ψ) s, ← borelMeasure_fourier U_grp ψ s,
    group_apply_comm U_grp s t ψ]
  exact U_grp.unitary t ψ (U_grp.U s ψ)

/-- **Quantum Liouville theorem** (setwise form of the First Law):
`μ_{U(t)ψ}(B) = μ_ψ(B)` for every `B` — no measurability hypothesis needed, since
the measures themselves are equal.  Classical Liouville: Hamiltonian flow preserves
phase-space volume.  Quantum: unitary flow preserves spectral measure. -/
theorem quantum_liouville (t : ℝ) (ψ : H) (B : Set ℝ) :
    borelMeasure U_grp (U_grp.U t ψ) B = borelMeasure U_grp ψ B := by
  rw [borelMeasure_unitary_invariant]

/-- **Spectral moment conservation**: every moment `∫ sⁿ dμ_ψ` is frozen.
`n = 0`: normalization; `n = 1`: `⟨H⟩` (the classical first law); `n = 2`: drives
variance conservation; higher `n`: all fluctuation statistics. -/
theorem spectral_moment_conserved (n : ℕ) (t : ℝ) (ψ : H) :
    ∫ s, s ^ n ∂(borelMeasure U_grp (U_grp.U t ψ))
      = ∫ s, s ^ n ∂(borelMeasure U_grp ψ) := by
  rw [borelMeasure_unitary_invariant]

/-- The energy variance `(ΔH)² = ∫ s² dμ_ψ − (∫ s dμ_ψ)²` of a state. -/
noncomputable def energyVariance (ψ : H) : ℝ :=
  (∫ s, s ^ 2 ∂(borelMeasure U_grp ψ)) - (∫ s, s ∂(borelMeasure U_grp ψ)) ^ 2

/-- **Energy uncertainty conservation**: `ΔH` is a constant of motion.  A state with
sharply defined energy stays sharp; via `ΔE·Δt ≥ ℏ/2`, the minimum time for state
change is likewise a constant of motion. -/
theorem energyVariance_conserved (t : ℝ) (ψ : H) :
    energyVariance U_grp (U_grp.U t ψ) = energyVariance U_grp ψ := by
  unfold energyVariance
  rw [borelMeasure_unitary_invariant]

/-! ## Spectral projections commute with the flow -/

/-- `E(B)` commutes with the flow: `E(B)(U(t)ψ) = U(t)(E(B)ψ)` — the old
`unitary_commutes_with_spectral`, now one specialization of
`spectralCalculus_group_comm` at the indicator symbol. -/
theorem spectralProjection_group_comm (B : Set ℝ) (hB : MeasurableSet B) (t : ℝ) (ψ : H) :
    spectralProjection U_grp B hB (U_grp.U t ψ)
      = U_grp.U t (spectralProjection U_grp B hB ψ) := by
  simp only [spectralProjection]
  exact spectralCalculus_group_comm U_grp _ (measurable_const.indicator hB)
    (indicator_one_bdd B) t ψ

/-- **Sector probability conservation**: `‖E(B) U(t) ψ‖ = ‖E(B) ψ‖`.  The probability
of finding the evolved state in the energy window `B` never changes: commute `E(B)`
across the flow, then `norm_preserving`. -/
theorem spectralProjection_norm_conserved (B : Set ℝ) (hB : MeasurableSet B)
    (t : ℝ) (ψ : H) :
    ‖spectralProjection U_grp B hB (U_grp.U t ψ)‖
      = ‖spectralProjection U_grp B hB ψ‖ := by
  rw [spectralProjection_group_comm U_grp B hB t ψ, norm_preserving]

/-! ## The converse: spectral invariance forces unitarity -/

/-- **Rigidity**: any surjective continuous linear map that preserves every diagonal
spectral measure is unitary.  This direction does NOT use `U_grp.unitary` about `V`:

1. `B = univ` and `borelMeasure_mass` give `‖Vψ‖ = ‖ψ‖`;
2. polarization (`LinearMap.norm_map_iff_inner_map_map`) upgrades to inner products;
3. `V†V = 1` follows; surjectivity then yields `VV† = 1`.

Unitarity is the UNIQUE dynamics compatible with energy-probability conservation. -/
theorem unitary_of_borelMeasure_invariant (V : H →L[ℂ] H)
    (hsurj : Function.Surjective V)
    (hinv : ∀ ψ : H, borelMeasure U_grp (V ψ) = borelMeasure U_grp ψ) :
    V ∈ _root_.unitary (H →L[ℂ] H) := by
  -- Step 1: `V` is an isometry — invariance at `B = univ` is mass conservation.
  have hnorm : ∀ ψ : H, ‖V ψ‖ = ‖ψ‖ := by
    intro ψ
    have h2 : ‖V ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [← borelMeasure_mass U_grp (V ψ), hinv ψ, borelMeasure_mass U_grp ψ]
    calc ‖V ψ‖ = Real.sqrt (‖V ψ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (‖ψ‖ ^ 2) := by rw [h2]
      _ = ‖ψ‖ := Real.sqrt_sq (norm_nonneg _)
  -- Step 2: polarization.
  have hinner : ∀ ψ φ : H, ⟪V ψ, V φ⟫_ℂ = ⟪ψ, φ⟫_ℂ :=
    (LinearMap.norm_map_iff_inner_map_map V).mp hnorm
  -- Step 3: isometry condition `V†V = 1`.
  have hVV : ContinuousLinearMap.adjoint V * V = 1 := by
    ext ψ
    refine ext_inner_left ℂ fun φ => ?_
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact hinner φ ψ
  -- Step 4: co-isometry `VV† = 1` from surjectivity.
  have hVVadj : V * ContinuousLinearMap.adjoint V = 1 := by
    ext ψ
    obtain ⟨χ, hχ⟩ := hsurj ψ
    have hχ' : ContinuousLinearMap.adjoint V (V χ) = χ := by
      have h := congrFun (congrArg DFunLike.coe hVV) χ
      simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using h
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
    rw [← hχ, hχ']
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint]
  exact ⟨hVV, hVVadj⟩

/-- **The fundamental equivalence**: `U(t)` is unitary if and only if it preserves
every diagonal spectral measure.

In the constructed setting both sides are theorems (`mem_unitary`,
`borelMeasure_unitary_invariant`); the residual content lives in the backward
direction, which re-derives unitarity from measure invariance alone via the
rigidity theorem — the spectral-theoretic statement that "no other dynamics
conserves energy probabilities". -/
theorem unitary_iff_borelMeasure_invariant (t : ℝ) :
    U_grp.U t ∈ _root_.unitary (H →L[ℂ] H)
      ↔ ∀ ψ : H, borelMeasure U_grp (U_grp.U t ψ) = borelMeasure U_grp ψ :=
  ⟨fun _ ψ => borelMeasure_unitary_invariant U_grp t ψ,
   unitary_of_borelMeasure_invariant U_grp (U_grp.U t) (unitary_group_surjective U_grp t)⟩

/-! ## The generator commutes with the flow: energy conservation -/

/-- **The generator commutes with its own flow**: `A (U(t)x) = U(t) (Ax)` on the
domain.  This is the value-level companion of `generator_domain_invariant` (which
only exports membership): the same pointwise identity
`genDiffQuot (U(t)x) = U(t) ∘ genDiffQuot x`, closed by `tendsto_nhds_unique`. -/
theorem generator_group_comm (t : ℝ) (x : (generator U_grp).domain) :
    generator U_grp ⟨U_grp.U t (x : H), generator_domain_invariant U_grp t x⟩
      = U_grp.U t (generator U_grp x) := by
  have hpt : genDiffQuot U_grp (U_grp.U t (x : H))
      = fun s => U_grp.U t (genDiffQuot U_grp (x : H) s) := by
    funext s
    simp only [genDiffQuot_apply, map_smul]
    congr 1
    rw [map_sub, group_apply_comm U_grp s t (x : H)]
  refine tendsto_nhds_unique
    (generator_tendsto U_grp ⟨U_grp.U t (x : H), generator_domain_invariant U_grp t x⟩) ?_
  change Tendsto (genDiffQuot U_grp (U_grp.U t (x : H))) (𝓝[≠] 0)
    (𝓝 (U_grp.U t (generator U_grp x)))
  rw [hpt]
  exact ((U_grp.U t).continuous.tendsto _).comp (generator_tendsto U_grp x)

/-- **Energy conservation**: `⟪A(U(t)x), U(t)x⟫ = ⟪Ax, x⟫` for `x` in the domain.
No integral, no self-adjointness: commute the generator across the flow, then
inner-product preservation.  (The old route through `energy_eq_spectral_moment`
needed Fatou and a two-stream DCT argument.) -/
theorem energy_expectation_conserved (t : ℝ) (x : (generator U_grp).domain) :
    ⟪generator U_grp ⟨U_grp.U t (x : H), generator_domain_invariant U_grp t x⟩,
        U_grp.U t (x : H)⟫_ℂ
      = ⟪generator U_grp x, (x : H)⟫_ℂ := by
  rw [generator_group_comm U_grp t x]
  exact U_grp.unitary t (generator U_grp x) (x : H)

/-! ## The First Law equivalence -/

/-- **THE FIRST LAW EQUIVALENCE**: the four pillars of quantum dynamics.

1. **Unitarity**: probability is conserved (`U(t)* U(t) = 1 = U(t) U(t)*`);
2. **Symmetry**: `⟪Aψ, φ⟫ = ⟪ψ, Aφ⟫` — energy expectations are real.  (Full
   self-adjointness, hence density and closedness, is the deficiency-index
   project in `SelfAdjoint.lean`; symmetry is the proved structural half.)
3. **Spectral invariance** (the First Law itself): `μ_{U(t)ψ} = μ_ψ`;
4. **Energy conservation**: `⟪A(U(t)x), U(t)x⟫ = ⟪Ax, x⟫`.

In the old file this structure took `gen`, `hsa`, `E`, `hE` as inputs and was
inhabited only under self-adjointness.  Now it is parametrized by `U_grp` alone
and inhabited unconditionally (`first_law`): a strongly continuous unitary group
carries its own thermodynamics. -/
structure FirstLawEquivalence : Prop where
  /-- Time evolution is unitary: probability is conserved. -/
  unitary : ∀ t : ℝ, U_grp.U t ∈ _root_.unitary (H →L[ℂ] H)
  /-- The generator is symmetric: energy is a real-valued observable. -/
  symmetric : (generator U_grp).IsFormalAdjoint (generator U_grp)
  /-- **THE FIRST LAW**: the entire energy distribution is invariant. -/
  spectral_invariant : ∀ (t : ℝ) (ψ : H),
    borelMeasure U_grp (U_grp.U t ψ) = borelMeasure U_grp ψ
  /-- Energy expectation is conserved on the generator's domain. -/
  energy_conserved : ∀ (t : ℝ) (x : (generator U_grp).domain),
    ⟪generator U_grp ⟨U_grp.U t (x : H), generator_domain_invariant U_grp t x⟩,
        U_grp.U t (x : H)⟫_ℂ
      = ⟪generator U_grp x, (x : H)⟫_ℂ

/-- **MAIN THEOREM**: the First Law equivalence holds for every strongly continuous
one-parameter unitary group — with no hypotheses.  Every field is one of the
theorems above; the old `first_law_equivalence_of_self_adjoint hsa` has shed its
last assumption. -/
theorem first_law : FirstLawEquivalence U_grp where
  unitary := mem_unitary U_grp
  symmetric := generator_isFormalAdjoint U_grp
  spectral_invariant := borelMeasure_unitary_invariant U_grp
  energy_conserved := energy_expectation_conserved U_grp

end SpectralTheory

/-! ## Dirac equation applications -/

namespace Dirac
open SpectralTheory

variable {M : Type*}

/-- **The electron sector projection** `E₊ = E([mc², ∞))`: positive-energy
(particle) states, directly from the constructed calculus.  (The old
`DiracSpectralData` carrier is gone — its every field is now a theorem.) -/
noncomputable def electronProjection (H_D : DiracHamiltonian H DiracConstants M) :
    H →L[ℂ] H :=
  spectralProjection H_D.U_grp (Set.Ici H_D.constants.restEnergy) measurableSet_Ici

/-- **The positron sector projection** `E₋ = E((−∞, −mc²])`: negative-energy
(antiparticle) states. -/
noncomputable def positronProjection (H_D : DiracHamiltonian H DiracConstants M) :
    H →L[ℂ] H :=
  spectralProjection H_D.U_grp (Set.Iic (-H_D.constants.restEnergy)) measurableSet_Iic

/-- **Electron number conservation**: `‖E₊ U(t) ψ‖ = ‖E₊ ψ‖`.  For the FREE Dirac
equation the electron-sector probability is frozen; with interactions (QED), pair
creation can change it. -/
theorem electron_number_conserved (H_D : DiracHamiltonian H DiracConstants M)
    (t : ℝ) (ψ : H) :
    ‖electronProjection H_D (H_D.U_grp.U t ψ)‖ = ‖electronProjection H_D ψ‖ := by
  simp only [electronProjection]
  exact spectralProjection_norm_conserved H_D.U_grp _ measurableSet_Ici t ψ

/-- **Positron number conservation**: `‖E₋ U(t) ψ‖ = ‖E₋ ψ‖`. -/
theorem positron_number_conserved (H_D : DiracHamiltonian H DiracConstants M)
    (t : ℝ) (ψ : H) :
    ‖positronProjection H_D (H_D.U_grp.U t ψ)‖ = ‖positronProjection H_D ψ‖ := by
  simp only [positronProjection]
  exact spectralProjection_norm_conserved H_D.U_grp _ measurableSet_Iic t ψ

/-- **Charge conservation**: `Q = ‖E₊ψ‖² − ‖E₋ψ‖²` is time-invariant.  In natural
units with `e = 1` this IS the electric charge of the free Dirac particle; both
sector probabilities are individually conserved, hence their difference. -/
theorem charge_conserved (H_D : DiracHamiltonian H DiracConstants M) (t : ℝ) (ψ : H) :
    ‖electronProjection H_D (H_D.U_grp.U t ψ)‖ ^ 2
        - ‖positronProjection H_D (H_D.U_grp.U t ψ)‖ ^ 2
      = ‖electronProjection H_D ψ‖ ^ 2 - ‖positronProjection H_D ψ‖ ^ 2 := by
  rw [electron_number_conserved H_D t ψ, positron_number_conserved H_D t ψ]

/-- **The spectral gap separates matter from antimatter**: for `m > 0` the sectors
are orthogonal, `E₊ E₋ = 0`, since `[mc², ∞) ∩ (−∞, −mc²] = ∅`.  Free evolution
cannot mix electron and positron content (`spectralProjection_group_comm`). -/
theorem sector_orthogonal (H_D : DiracHamiltonian H DiracConstants M)
    (hm : 0 < H_D.constants.m) :
    electronProjection H_D * positronProjection H_D = 0 := by
  have hE0 : 0 < H_D.constants.restEnergy := by
    unfold DiracConstants.restEnergy
    exact mul_pos hm (pow_pos H_D.constants.c_pos 2)
  have hdisj : Set.Ici H_D.constants.restEnergy ∩ Set.Iic (-H_D.constants.restEnergy)
      = (∅ : Set ℝ) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Iic, Set.mem_empty_iff_false,
      iff_false, not_and, not_le]
    intro h1
    linarith
  simp only [electronProjection, positronProjection]
  rw [spectralProjection_inter H_D.U_grp _ _ measurableSet_Ici measurableSet_Iic,
    spectralProjection_congr H_D.U_grp hdisj (measurableSet_Ici.inter measurableSet_Iic)
      MeasurableSet.empty,
    spectralProjection_empty]

/-- **The First Law for the Dirac equation**, hypothesis-free: relativistic quantum
mechanics conserves probability, energy, and the full energy distribution.
Combined with the positive-definite probability density (`Current.lean`,
`Conservation.lean`), this is a complete, consistent relativistic quantum
mechanics. -/
theorem dirac_first_law {K M' : Type*} (H_D : DiracHamiltonian H K M') :
    FirstLawEquivalence H_D.U_grp :=
  first_law H_D.U_grp

end Dirac
end Spectra.QuantumMechanics
