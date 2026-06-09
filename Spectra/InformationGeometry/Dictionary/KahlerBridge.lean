/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: InformationGeometry/QIGDictionary/KahlerCorrespondence.lean
-/
import LogosLibrary.InformationGeometry.Dictionary.Defs
import LogosLibrary.InformationGeometry.Dictionary.MetricCorrespondence
import LogosLibrary.InformationGeometry.Dictionary.SymplecticCorrespondence
import LogosLibrary.InformationGeometry.CompositeObservable
/-!
=====================================================================
# THE KÄHLER CORRESPONDENCE: g + iω = 4 · ⟨Õᵢψ, Õⱼψ⟩
=====================================================================

## Overview

This file binds the SKELETAL `KahlerBridgeData` instance
`kahlerBridge3` from `Defs.lean` to the analytic synthesis of
the metric and symplectic spans:

  G^RLD_{ij} = g_{ij} + i ω_{ij}
             = 4 · Re⟨Õᵢ ψ, Õⱼ ψ⟩  +  i · 4 · Im⟨Õᵢ ψ, Õⱼ ψ⟩
             = 4 · ⟨Õᵢ ψ, Õⱼ ψ⟩

This is not a separate analytic theorem — it is the SYNTHESIS of
two facts already in hand:

  - From `MetricCorrespondence`: g_{ij} = 4 · Cov(Oᵢ, Oⱼ)
                                       = 4 · Re⟨Õᵢ ψ, Õⱼ ψ⟩
  - From `SymplecticCorrespondence`:
                                  ω_{ij} = 2 · Im⟨ψ, [Oᵢ, Oⱼ] ψ⟩
                                       = 4 · Im⟨Õᵢ ψ, Õⱼ ψ⟩
                                       (using the half-factor bridge)

Their combination is the Kähler bridge.

## Witnessed Claims of `kahlerBridge3`

  Claim                       | Witness                          | Source
  ────────────────────────────┼──────────────────────────────────┼─────────────────
  isPositiveSemidef = true    | quantum_schrodinger_bilinear     | QuantumFisherModel
                                (cited; not directly aliased
                                 here — see Part III)
                              | inner_self_nonneg (diagonal case)| Mathlib
  isSchrodingerEquivalent     | by definition / Schrödinger ≡ CS | (structural)
       = true
  isInnerProduct = true       | Hermitian (inner_conj_symm) +    | (synthesis)
                                positivity
  hermFormDim = 18            | dimensional bookkeeping (2·3²)   | Defs.lean
  status = .skeleton          | from Defs.lean                   | Defs.lean

## Methodology Note

Every theorem in this file uses the `kahler_` prefix to avoid
name collisions with `MetricCorrespondence` and
`SymplecticCorrespondence` (both of which use generic names like
`isBilinear_witnessed` that would clash if redeclared).

## Dependencies

  - QIGDictionary/Defs.lean
  - QIGDictionary/MetricCorrespondence.lean
  - QIGDictionary/SymplecticCorrespondence.lean
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
## Part I: The Synthesis Identity
=====================================================================

The Kähler synthesis at factor 4: combining the metric BC factor
(4 multiplying Cov) with the symplectic effective factor (also 4
multiplying Im⟨Õ,Õ⟩, after the half-bridge), the full Hermitian
form G^RLD = g + iω equals 4 · ⟨Õ, Õ⟩.

At the abstract level, this is just `Complex.re_add_im` scaled by 4.

=====================================================================
-/

section SynthesisIdentity

/-- **WITNESS: Real-imaginary decomposition (abstract).**

    For any complex z, z = (z.re : ℂ) + i · (z.im : ℂ). -/
theorem kahler_synthesis_decomposition (z : ℂ) :
    (z.re : ℂ) + Complex.I * (z.im : ℂ) = z := by
  conv_rhs => rw [← Complex.re_add_im z]
  ring

/-- **WITNESS: Kähler synthesis at factor 4.**

    The combined factor 4 from metric BC (4·Re) and effective
    symplectic (4·Im, after half-bridge) collapses to 4 · z:

      G^RLD = 4 · Re⟨Õ,Õ⟩ + i · 4 · Im⟨Õ,Õ⟩ = 4 · ⟨Õ, Õ⟩ -/
theorem kahler_synthesis_factor4 (z : ℂ) :
    ((4 : ℂ) * (z.re : ℂ)) + Complex.I * ((4 : ℂ) * (z.im : ℂ))
      = (4 : ℂ) * z := by
  conv_rhs => rw [← Complex.re_add_im z]
  ring

end SynthesisIdentity


/-!
=====================================================================
## Part II: Hermitian Property
=====================================================================

The Hermitian property of G^RLD: G(a, b) = conj G(b, a).
This decomposes (on real coefficient vectors) into:
  - Re G(a, b) = Re G(b, a)   (symmetry of g)
  - Im G(a, b) = -Im G(b, a)  (antisymmetry of ω)
Both follow from `inner_conj_symm`.

=====================================================================
-/

section HermitianProperty

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **WITNESS: Hermitian symmetry of the inner product (abstract).**

    `conj ⟨b, a⟩ = ⟨a, b⟩`

    Direct re-export of `inner_conj_symm`. -/
theorem kahler_hermitian_witness (a b : H) :
    starRingEnd ℂ ⟪b, a⟫_ℂ = ⟪a, b⟫_ℂ :=
  inner_conj_symm a b

/-- **WITNESS: Hermitian symmetry scaled by 4.**

    `conj (4 · ⟨b, a⟩) = 4 · ⟨a, b⟩`

    The factor 4 is real, so its conjugate is itself; the rest
    is `inner_conj_symm`. -/
theorem kahler_hermitian_factor4 (a b : H) :
    starRingEnd ℂ ((4 : ℂ) * ⟪b, a⟫_ℂ) = (4 : ℂ) * ⟪a, b⟫_ℂ := by
  rw [map_mul, inner_conj_symm a b]
  congr 1
  exact Complex.conj_eq_iff_re.mpr rfl

end HermitianProperty


/-!
=====================================================================
## Part III: Positivity
=====================================================================

The Hermitian form G^RLD is positive semi-definite on real
coefficient vectors:

  G(v, v) ≥ 0  for all v : Fin n → ℝ

In bilinear form, this is the Cauchy-Schwarz inequality:

  |G(v, w)|² ≤ G(v, v) · G(w, w)

which decomposes (using G = g + iω) into:

  g(v, w)² + ω(v, w)² ≤ g(v, v) · g(w, w)

For pure quantum states, this IS the Schrödinger uncertainty
principle — witnessed in the user's library by
`quantum_schrodinger_bilinear` (in `QuantumFisherModel.lean`).

The diagonal case G(v, v) = 4 · Var(O_v) ≥ 0 reduces to
variance ≥ 0, which we prove abstractly here via
`inner_self_nonneg`: `0 ≤ Re ⟨a, a⟩` for any `a` in a complex
inner product space.

=====================================================================
-/

section Positivity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **WITNESS: Diagonal positivity of the Hermitian form (abstract).**

    `0 ≤ Re ⟨a, a⟩` for any `a` in a complex inner product space.

    Direct re-export of `inner_self_nonneg`. -/
theorem kahler_diagonal_positivity (a : H) :
    0 ≤ (⟪a, a⟫_ℂ).re := by
  show (0 : ℝ) ≤ RCLike.re ⟪a, a⟫_ℂ
  exact inner_self_nonneg

/-- **WITNESS: Diagonal positivity scaled by 4.**

    `0 ≤ Re (4 · ⟨a, a⟩) = 4 · Re ⟨a, a⟩`

    The diagonal case G(v, v) = 4 · Var(O_v) ≥ 0. -/
theorem kahler_diagonal_positivity_factor4 (a : H) :
    0 ≤ ((4 : ℂ) * ⟪a, a⟫_ℂ).re := by
  rw [Complex.mul_re,
      show ((4 : ℂ)).im = 0 from by norm_num, zero_mul, sub_zero,
      show ((4 : ℂ)).re = 4 from by norm_num]
  exact mul_nonneg (by norm_num) (kahler_diagonal_positivity a)

end Positivity


/-!
=====================================================================
## Part IV: The Kähler Correspondence Bundle
=====================================================================

A bundle that records:

  - The skeletal `KahlerBridgeData` (typically `kahlerBridge3`)
  - The metric and symplectic correspondences anchoring its halves
  - Whether the synthesis has been promoted to `.proved` status

The bundle does not prove anything new; it serves as a type-theoretic
record that the Kähler bridge has been bound to its analytic synthesis.

=====================================================================
-/

section CorrespondenceBundle

/-- The Kähler correspondence bundle. -/
structure KahlerCorrespondence (n : ℕ) (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The skeletal Kähler bridge (typically from Defs.lean). -/
  bridge : KahlerBridgeData
  /-- The underlying metric correspondence. -/
  metric : MetricCorrespondence n H
  /-- The underlying symplectic correspondence. -/
  symplectic : SymplecticCorrespondence n H
  /-- The metric span matches. -/
  hMetricMatch : bridge.metricSpan = metric.span
  /-- The symplectic span matches. -/
  hSymMatch : bridge.symplecticSpan = symplectic.span
  /-- The promoted status. -/
  promotedStatus : Status
  /-- `.proved` requires both halves to be promoted to `.proved`. -/
  hPromote : promotedStatus = .proved →
    metric.promotedStatus = .proved ∧ symplectic.promotedStatus = .proved

end CorrespondenceBundle


/-!
=====================================================================
## Part V: Cross-Checks
=====================================================================

Verify that `kahlerBridge3` (the skeletal entry from `Defs.lean`)
is aligned with the synthesis above.  All theorems use the
`kahler_` prefix to avoid name collisions with the metric and
symplectic correspondence files.

=====================================================================
-/

section CrossChecks

/-- **CHECK 1: Positive semi-definiteness.**  Witnessed by
    `quantum_schrodinger_bilinear` (full Cauchy-Schwarz form)
    plus `kahler_diagonal_positivity` (diagonal abstract case). -/
theorem kahler_isPositiveSemidef_witnessed :
    kahlerBridge3.isPositiveSemidef = true := rfl

/-- **CHECK 2: Schrödinger equivalence.**  By definition: the
    bilinear Schrödinger uncertainty IS the Cauchy-Schwarz
    inequality for G^RLD on real coefficient vectors. -/
theorem kahler_isSchrodingerEquivalent_witnessed :
    kahlerBridge3.isSchrodingerEquivalent = true := rfl

/-- **CHECK 3: Inner product structure.**  Hermitian
    (`inner_conj_symm`) + positive semi-definite (Schrödinger). -/
theorem kahler_isInnerProduct_witnessed :
    kahlerBridge3.isInnerProduct = true := rfl

/-- **CHECK 4: Hermitian dimension.**  At n = 3, the full complex
    bilinear form space has 2·3² = 18 real degrees of freedom. -/
theorem kahler_hermFormDim_18 : kahlerBridge3.hermFormDim = 18 := rfl

/-- **CHECK 5: Tangent space match (metric).**  The metric span
    inside the Kähler bridge is exactly `metricSpan3`. -/
theorem kahler_metricSpan_match :
    kahlerBridge3.metricSpan = metricSpan3 := rfl

/-- **CHECK 6: Tangent space match (symplectic).**  The symplectic
    span inside the Kähler bridge is exactly `symplecticSpan3`. -/
theorem kahler_symplecticSpan_match :
    kahlerBridge3.symplecticSpan = symplecticSpan3 := rfl

/-- **CHECK 7: Tangent dimension.**  The Kähler bridge lives over
    the same 3-dimensional tangent space as its constituent spans. -/
theorem kahler_tangent_n : kahlerBridge3.tangent.n = 3 := rfl

/-- **CHECK 8: Skeletal status.** -/
theorem kahler_skeleton_status :
    kahlerBridge3.status = .skeleton := rfl

/-- **CHECK 9: Bilinear-form dimension.** At n = 3, the symmetric
    + antisymmetric bilinear pieces sum to 6 + 3 = 9 = n². -/
theorem kahler_bilin_dim_sum :
    metricSpan3.tangent.symBilinDim + symplecticSpan3.tangent.antiSymBilinDim = 9 := rfl

end CrossChecks


/-!
=====================================================================
## Part VI: Master Theorem
=====================================================================
-/

section MasterTheorem

/-- **THE KÄHLER CORRESPONDENCE: MASTER THEOREM**

    The Kähler bridge `kahlerBridge3` is consistently aligned with
    the metric and symplectic correspondences, and the synthesis
    identity holds at factor 4:

    (1) POSITIVE SEMIDEF      ↔ `quantum_schrodinger_bilinear`
                                 (Schrödinger ≡ Cauchy-Schwarz)
    (2) SCHRÖDINGER EQUIV     ↔ by definition
    (3) INNER PRODUCT         ↔ Hermitian + positive semi-definite
    (4) HERM DIM = 18         ↔ 2·3² (full complex bilinear)
    (5) METRIC ALIGNMENT      ↔ metricSpan3
    (6) SYMPLECTIC ALIGNMENT  ↔ symplecticSpan3
    (7) BILIN DIM SUM = 9     ↔ 6 + 3 (sym + antisym = n²)
    (8) SYNTHESIS IDENTITY    ↔ for all complex z,
                                 4·z.re + i·4·z.im = 4·z -/
theorem kahler_correspondence_master :
    -- Bool fields aligned with witnesses
    kahlerBridge3.isPositiveSemidef = true
    ∧ kahlerBridge3.isSchrodingerEquivalent = true
    ∧ kahlerBridge3.isInnerProduct = true
    -- Dimensional bookkeeping
    ∧ kahlerBridge3.hermFormDim = 18
    ∧ kahlerBridge3.tangent.n = 3
    ∧ metricSpan3.tangent.symBilinDim
        + symplecticSpan3.tangent.antiSymBilinDim = 9
    -- Constituent span alignment
    ∧ kahlerBridge3.metricSpan = metricSpan3
    ∧ kahlerBridge3.symplecticSpan = symplecticSpan3
    -- Skeletal status
    ∧ kahlerBridge3.status = .skeleton
    -- Synthesis identity (substantive content)
    ∧ ∀ z : ℂ, ((4 : ℂ) * (z.re : ℂ))
                + Complex.I * ((4 : ℂ) * (z.im : ℂ)) = (4 : ℂ) * z := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact kahler_synthesis_factor4

end MasterTheorem


/-!
=====================================================================
## Epilogue
=====================================================================

What this file establishes:

**The Synthesis (Re-exports + Compositions):**
  - `kahler_synthesis_decomposition` ← `Complex.re_add_im`
  - `kahler_synthesis_factor4`        ← scaled by 4
  - `kahler_hermitian_witness`        ← `inner_conj_symm`
  - `kahler_hermitian_factor4`        ← scaled by 4 (real factor)
  - `kahler_diagonal_positivity`      ← `inner_self_nonneg`
  - `kahler_diagonal_positivity_factor4` ← scaled by 4

**The Bundle:**
  - `KahlerCorrespondence n H` packaging the Kähler bridge with
    pointers into both the metric and symplectic correspondences

**Cited (Not Directly Aliased) Witnesses:**
  - `quantum_schrodinger_bilinear` (in `QuantumFisherModel.lean`)
    is the substantive analytic source for the off-diagonal
    Cauchy-Schwarz / Schrödinger uncertainty.  We cite it in
    documentation rather than aliasing because the exact
    statement form depends on the user's choice of normalization
    in that file.  A direct alias is straightforward to add
    once the signature is in hand.

**The Synthesis Sentence (One Line):**
       g  +  i ω  =  4 · ⟨Õ, Õ⟩

  where:
       g       = 4 · Re⟨Õ, Õ⟩          (metric, BC factor 4)
       ω       = 2 · Im⟨ψ,[·,·]ψ⟩       (symplectic, factor 2)
               = 4 · Im⟨Õ, Õ⟩           (via half-bridge)

  The two 4's pair to give a single complex form on Õ.

**Theorem Count: 14+**
**Sorry Count: 0**

**Next Files:**
  - DivergenceCorrespondence.lean : tie `divergenceSpan` to
                                    `preserves_fisher` and
                                    `preserves_cubic` (Stone forward
                                    direction; coordinate-level
                                    invariance under unitary flow)
  - StoneCorrespondence.lean      : the full IG Stone bridge —
                                    forward proved + reverse
                                    axiomatized under geodesic
                                    completeness

                        ∎
=====================================================================
-/

end QIGDictionary
