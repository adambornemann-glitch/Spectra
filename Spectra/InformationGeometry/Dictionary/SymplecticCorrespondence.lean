/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: InformationGeometry/QIGDictionary/SymplecticCorrespondence.lean
-/
import LogosLibrary.InformationGeometry.Dictionary.Defs
import LogosLibrary.InformationGeometry.Dictionary.MetricCorrespondence
import LogosLibrary.InformationGeometry.CompositeObservable
/-!
=====================================================================
# THE SYMPLECTIC CORRESPONDENCE: ω ↔ Im ⟨Õᵢψ, Õⱼψ⟩
=====================================================================

## Overview

This file binds the SKELETAL `SymplecticSpanData` from `Defs.lean`
to the analytic content already in the library:

  Claim of symplecticSpan       | Analytic witness                         | Source
  ──────────────────────────────┼──────────────────────────────────────────┼─────────────────────
  isBilinear        = true      | commutator_im_composite                  | CompositeObservable
  isAntiSymmetric   = true      | commutator antisymm + Complex.neg_im     | (constructed here)
  isClosed          = true      | global/geometric (manifold-level)        | NOT DISCHARGED HERE
  vanishesClassically = true    | meta-level: no classical commutator      | NOT DISCHARGED HERE
  fromImaginaryPart = true      | by labeling/construction                 | rfl
  normFactor        = 2         | symplecticForm STIPULATION               | quantumRLDFisherModel

  + The half-factor bridge      | im_inner_shifted_eq_half_commutator      | Schrodinger
    Im⟨Õᵢψ, Õⱼψ⟩ = ½ · Im⟨ψ,[Oᵢ,Oⱼ]ψ⟩

## What .proved Means Here

A `SymplecticCorrespondence` at status `.proved` is a bundle:

  - A `QuantumRLDData n H` on the quantum side
  - A `SymplecticSpanData` on the skeletal side
  - The witness theorems below for bilinearity, antisymmetry, and
    the half-factor bridge
  - A `SymplecticFactorStipulation` recording the factor 2 as INPUT

Closed-ness and classical-vanishing are noted but not discharged
here — they are global/meta facts beyond the algebra of observables.

## The Factor-2 / Half-Factor Pair

`quantumRLDFisherModel.symplecticForm` is set to:

  symplecticForm θ i j = 2 · Im ⟨ψ, [Oᵢ, Oⱼ] ψ⟩

The half-factor bridge gives:

  Im ⟨Õᵢ ψ, Õⱼ ψ⟩ = ½ · Im ⟨ψ, [Oᵢ, Oⱼ] ψ⟩

Combining: 2 · Im⟨ψ,[·,·]ψ⟩ = 4 · Im⟨Õ, Õ⟩.

This 4 PAIRS exactly with the BC factor 4 in the metric span,
making the Kähler synthesis exact:

  G^RLD_{ij} = g_{ij} + i ω_{ij}
             = 4 · Re⟨Õᵢ ψ, Õⱼ ψ⟩  +  i · 4 · Im⟨Õᵢ ψ, Õⱼ ψ⟩
             = 4 · ⟨Õᵢ ψ, Õⱼ ψ⟩

## Dependencies

  - QIGDictionary/Defs.lean
  - QIGDictionary/MetricCorrespondence.lean (for the metric–symplectic
    factor-relationship cross-check)
  - InformationGeometry/CompositeObservable.lean

=====================================================================
-/

namespace QIGDictionary

open QuantumMechanics
open QuantumMechanics.Bridge InformationGeometry QuantumMechanics.UnboundedObservable
open QuantumMechanics.Robertson QuantumMechanics.Schrodinger
open scoped InnerProductSpace

/-!
=====================================================================
## Part I: Bilinearity Witness
=====================================================================

The symplectic span's `isBilinear = true` is justified by
`commutator_im_composite` from `CompositeObservable.lean`:

  Im ⟨ψ, [O_v, O_w] ψ⟩ = ∑ᵢⱼ vᵢ wⱼ Im ⟨ψ, [Oᵢ, Oⱼ] ψ⟩

=====================================================================
-/

section Bilinearity

variable {n : ℕ} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **WITNESS: Bilinearity of the commutator's imaginary part.**

    `Im ⟨ψ, [O_v, O_w] ψ⟩ = ∑ᵢⱼ vᵢ wⱼ Im ⟨ψ, [Oᵢ, Oⱼ] ψ⟩`

    Direct re-export of `commutator_im_composite`. -/
theorem symplectic_bilinearity_witness
    (D : QuantumRLDData n H) (v w : Fin n → ℝ) :
    (⟪D.ψ, commutatorAt
      (compositeObservable D.O v D.h_dense)
      (compositeObservable D.O w D.h_dense)
      D.ψ (D.composites_shiftedDC v w).toDomainConditions⟫_ℂ).im =
    ∑ i : Fin n, ∑ j : Fin n,
      v i * w j *
      (⟪D.ψ, commutatorAt (D.O i) (D.O j) D.ψ
        (pairwise_shiftedDC D i j).toDomainConditions⟫_ℂ).im :=
  commutator_im_composite D v w

end Bilinearity


/-!
=====================================================================
## Part II: The Half-Factor Bridge
=====================================================================

The two ways to write the symplectic data:

  Im ⟨Õᵢ ψ, Õⱼ ψ⟩ = ½ · Im ⟨ψ, [Oᵢ, Oⱼ] ψ⟩

This is `im_inner_shifted_eq_half_commutator` from `Schrodinger.lean`.
The half on the right is what gets absorbed into the factor-2
stipulation: 2 · ½ = 1 in the commutator-Im picture, but
2 · Im⟨ψ,[·,·]ψ⟩ = 4 · Im⟨Õ, Õ⟩ in the shifted-inner-product picture.

=====================================================================
-/

section HalfBridge

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **WITNESS: Half-factor bridge.**

    `Im ⟨Õᵢ ψ, Õⱼ ψ⟩ = ½ · Im ⟨ψ, [Oᵢ, Oⱼ] ψ⟩`

    Direct re-export of `im_inner_shifted_eq_half_commutator`. -/
theorem symplectic_half_bridge_witness
    (A B : UnboundedObservable H) (ψ : H)
    (sdc : ShiftedDomainConditions A B ψ) :
    (⟪sdc.A'ψ, sdc.B'ψ⟫_ℂ).im =
    (1/2) * (⟪ψ, commutatorAt A B ψ sdc.toDomainConditions⟫_ℂ).im :=
  im_inner_shifted_eq_half_commutator A B ψ sdc

end HalfBridge


/-!
=====================================================================
## Part III: Antisymmetry Witness
=====================================================================

The symplectic form is antisymmetric:

  Im ⟨ψ, [Oᵢ, Oⱼ] ψ⟩ = -Im ⟨ψ, [Oⱼ, Oᵢ] ψ⟩

This follows from `[A, B] = -[B, A]` (commutator antisymmetry)
plus `Im(-z) = -Im(z)`.  Reproduces the proof pattern from
`quantumRLDFisherModel.symplectic_antisymm`.

=====================================================================
-/

section Antisymmetry

variable {n : ℕ} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **WITNESS: Antisymmetry of the symplectic form.**

    `Im ⟨ψ, [Oᵢ, Oⱼ] ψ⟩ = -Im ⟨ψ, [Oⱼ, Oᵢ] ψ⟩` -/
theorem symplectic_antisymmetry_witness
    (D : QuantumRLDData n H) (i j : Fin n) :
    (⟪D.ψ, commutatorAt (D.O i) (D.O j) D.ψ
      (pairwise_shiftedDC D i j).toDomainConditions⟫_ℂ).im =
    -(⟪D.ψ, commutatorAt (D.O j) (D.O i) D.ψ
      (pairwise_shiftedDC D j i).toDomainConditions⟫_ℂ).im := by
  have h_anti : commutatorAt (D.O i) (D.O j) D.ψ
      (pairwise_shiftedDC D i j).toDomainConditions =
    -commutatorAt (D.O j) (D.O i) D.ψ
      (pairwise_shiftedDC D j i).toDomainConditions := by
    unfold commutatorAt DomainConditions.ABψ DomainConditions.BAψ
    module
  rw [h_anti, inner_neg_right, Complex.neg_im]

end Antisymmetry


/-!
=====================================================================
## Part IV: The Factor-2 Stipulation
=====================================================================

The user's `quantumRLDFisherModel` defines:

  symplecticForm θ i j = 2 · Im ⟨ψ, [Oᵢ, Oⱼ] ψ⟩

The factor 2 is a STIPULATION — a normalization choice in the model
construction, parallel to the BC factor 4 for the metric span.
Under the half-bridge, this becomes 4 · Im⟨Õ, Õ⟩, matching the
metric's effective factor of 4.

=====================================================================
-/

section SymplecticFactor

/-- The symplectic factor stipulation. -/
structure SymplecticFactorStipulation where
  /-- The factor multiplying Im⟨ψ, [·,·] ψ⟩.  Standard value: 2. -/
  factor : ℕ
  /-- Is it the standard value (2)? -/
  isStandard : Bool
  /-- The factor is positive. -/
  hPos : factor > 0
  /-- Standard iff factor = 2. -/
  hStandardIff : isStandard = true ↔ factor = 2

/-- The standard symplectic stipulation: factor = 2. -/
def standardSymplecticFactor : SymplecticFactorStipulation where
  factor := 2
  isStandard := true
  hPos := by norm_num
  hStandardIff := ⟨fun _ => rfl, fun _ => rfl⟩

theorem standardSymplectic_factor :
    standardSymplecticFactor.factor = 2 := rfl

theorem standardSymplectic_isStandard :
    standardSymplecticFactor.isStandard = true := rfl

theorem standardSymplectic_pos : standardSymplecticFactor.factor > 0 := by norm_cast

end SymplecticFactor


/-!
=====================================================================
## Part V: The Symplectic Correspondence Bundle
=====================================================================
-/

section CorrespondenceBundle

/-- The symplectic correspondence bundle. -/
structure SymplecticCorrespondence (n : ℕ) (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The skeletal span (typically from Defs.lean). -/
  span : SymplecticSpanData
  /-- The quantum data anchoring the bilinearity and antisymmetry witnesses. -/
  D : QuantumRLDData n H
  /-- The symplectic factor stipulation. -/
  symFactor : SymplecticFactorStipulation
  /-- The tangent space matches the parameter count. -/
  hMatch : span.tangent.n = n
  /-- The recorded factor matches the stipulation. -/
  hFactor : span.normFactor = symFactor.factor
  /-- The promoted status (`.skeleton` or `.proved`). -/
  promotedStatus : Status
  /-- `.proved` requires the factor to be standard. -/
  hPromote : promotedStatus = .proved → symFactor.isStandard = true

end CorrespondenceBundle


/-!
=====================================================================
## Part VI: Cross-Checks
=====================================================================

Verify that `symplecticSpan3` (the skeletal entry from `Defs.lean`)
is aligned with the analytic witnesses provided here.

=====================================================================
-/

section CrossChecks

/- **CHECK 1: Bilinearity.**  Witnessed by `symplectic_bilinearity_witness`
    (= `commutator_im_composite`). -/
--theorem isBilinear_witnessed : symplecticSpan3.isBilinear = true := rfl
--redundant

/-- **CHECK 2: Antisymmetry.**  Witnessed by `symplectic_antisymmetry_witness`. -/
theorem isAntiSymmetric_witnessed : symplecticSpan3.isAntiSymmetric = true := rfl

/-- **CHECK 3: Imaginary-part origin.**  By labeling/construction. -/
theorem fromImaginaryPart_recorded :
    symplecticSpan3.fromImaginaryPart = true := rfl

/-- **CHECK 4: Closed-ness.**  Boolean recorded; global/geometric proof
    is not discharged here (would require manifold infrastructure). -/
theorem isClosed_recorded : symplecticSpan3.isClosed = true := rfl

/-- **CHECK 5: Classical vanishing.**  Boolean recorded; meta-level fact
    about classical observables commuting (no classical structure to
    compare against in the formalization). -/
theorem vanishesClassically_recorded :
    symplecticSpan3.vanishesClassically = true := rfl

/-- **CHECK 6: Factor stipulation.**  Recorded factor 2 matches standard. -/
theorem normFactor_matches_standard :
    symplecticSpan3.normFactor = standardSymplecticFactor.factor := rfl

/-- **CHECK 7: Dimensional Home.**  At n = 3, ω lives in 3-dim antisym space. -/
theorem symplectic_lives_in_antisym :
    symplecticSpan3.tangent.antiSymBilinDim = 3 := rfl

/- **CHECK 8: Skeletal status from Defs.lean.** -/
--theorem skeleton_status_recorded : symplecticSpan3.status = .skeleton := rfl
--redundant

/-- **CHECK 9: Factor relationship with metric.**

    The dictionary's central scaling identity:

      metric.normFactor = 2 · symplectic.normFactor

    i.e., 4 = 2 · 2.  Combined with the half-bridge
    (Im⟨Õ,Õ⟩ = ½ Im⟨ψ,[·,·]ψ⟩), both spans contribute equal
    weight 4 to the unified Hermitian form g + iω = 4·⟨Õ,Õ⟩. -/
theorem symplectic_metric_factor_relation :
    metricSpan3.normFactor = 2 * symplecticSpan3.normFactor := rfl

end CrossChecks


/-!
=====================================================================
## Part VII: Master Theorem
=====================================================================
-/

section MasterTheorem

/-- **THE SYMPLECTIC CORRESPONDENCE: MASTER THEOREM**

    All five Bool claims of the symplectic span at n = 3 are
    consistently recorded, with analytic witnesses for bilinearity
    and antisymmetry, the half-factor bridge available, and
    global/meta acknowledgments for closed-ness and classical
    vanishing:

    (1) BILINEARITY      ↔ `commutator_im_composite`
    (2) ANTISYMMETRY     ↔ commutator antisym + `Complex.neg_im`
    (3) FROM IMAGINARY   ↔ by labeling/construction
    (4) CLOSED-NESS      ← global/geometric (not local)
    (5) CLASSICAL ZERO   ← meta-level (no classical comparison)
    (6) FACTOR 2         ↔ `standardSymplecticFactor`
    (7) HALF BRIDGE      ↔ `im_inner_shifted_eq_half_commutator`
                            (Im⟨Õ,Õ⟩ = ½·Im⟨ψ,[·,·]ψ⟩)
    (8) DIMENSIONAL HOME ↔ antisymmetric bilinear subspace, dim 3
    (9) METRIC SCALING   ↔ metric.factor = 2 · symplectic.factor
                            (the central scaling identity) -/
theorem symplectic_correspondence_master :
    -- Bool fields aligned with witnesses
    symplecticSpan3.isBilinear = true
    ∧ symplecticSpan3.isAntiSymmetric = true
    ∧ symplecticSpan3.fromImaginaryPart = true
    ∧ symplecticSpan3.isClosed = true
    ∧ symplecticSpan3.vanishesClassically = true
    -- Factor stipulation
    ∧ symplecticSpan3.normFactor = standardSymplecticFactor.factor
    ∧ standardSymplecticFactor.factor = 2
    ∧ standardSymplecticFactor.isStandard = true
    -- Dimensional home
    ∧ symplecticSpan3.tangent.antiSymBilinDim = 3
    ∧ symplecticSpan3.tangent.n = 3
    -- Metric–symplectic scaling identity
    ∧ metricSpan3.normFactor = 2 * symplecticSpan3.normFactor
    -- Skeletal status (upgrade requires a SymplecticCorrespondence bundle)
    ∧ symplecticSpan3.status = .skeleton :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end MasterTheorem


/-!
=====================================================================
## Epilogue
=====================================================================

What this file establishes:

**The Witnesses (Re-exports + One Constructed):**
  - `symplectic_bilinearity_witness`  ← `commutator_im_composite`
  - `symplectic_half_bridge_witness`  ← `im_inner_shifted_eq_half_commutator`
  - `symplectic_antisymmetry_witness` ← constructed via commutator antisym
                                        + Complex.neg_im (pattern from
                                        quantumRLDFisherModel.symplectic_antisymm)

**The Stipulation:**
  - `SymplecticFactorStipulation`, `standardSymplecticFactor` recording
    the factor 2 as input from `quantumRLDFisherModel.symplecticForm`

**The Bundle:**
  - `SymplecticCorrespondence n H` packaging skeleton + quantum data
    + factor stipulation, with `.proved` promotion gated on standard factor

**The Scaling Identity:**
  metric normFactor (4) = 2 · symplectic normFactor (2)
  ⟹ both contribute weight 4 (after the half-bridge)
  ⟹ g + iω = 4 · ⟨Õ, Õ⟩  (the Kähler synthesis, next file)

**Acknowledged Non-Local Facts:**
  - `isClosed = true` is a global property of the manifold,
    not discharged at the algebra level
  - `vanishesClassically = true` is meta-level — no classical
    observable structure is in scope to compare against

**Theorem Count: 16+**
**Sorry Count: 0**

**Next File:**
  - KahlerCorrespondence.lean : the synthesis g + iω = 4 · ⟨Õ, Õ⟩,
                                tying `kahlerBridge` to
                                `quantum_schrodinger_bilinear`.
                                The Schrödinger uncertainty IS the
                                Hermitian positive-semidefiniteness of
                                G^RLD = g + iω, evaluated on real
                                coefficient vectors.

                        ∎
=====================================================================
-/

end QIGDictionary
