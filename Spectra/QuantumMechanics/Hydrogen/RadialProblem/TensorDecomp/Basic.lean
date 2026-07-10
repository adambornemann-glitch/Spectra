/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SphericalHarmonics.Completeness
/-!
# Tensor Decomposition: Radial × Angular

The unitary decomposition L²(ℝ³) ≅ ⊕_ℓ L²(ℝ⁺, r²dr) ⊗ V_ℓ
that reduces the hydrogen Hamiltonian to a family of radial ODEs.

## Physical significance

This is the separation of variables that transforms the 3D partial
differential equation into infinitely many 1D ordinary differential
equations — one for each angular momentum sector ℓ. Within each sector,
the effective potential is V_eff(r) = ℓ(ℓ+1)/r² − Z/r, combining the
centrifugal barrier with the Coulomb attraction.

## Main definitions

* `radialMeasure` — r² dr on (0, ∞), as `(volume.restrict (Ioi 0)).withDensity r²`.
* `RadialL2` — L²(ℝ⁺, r²dr), the radial Hilbert space.
* `ReducedRadialL2` — L²(ℝ⁺, dr), the reduced radial Hilbert space.
* `radialReduction` — the unitary R ↦ rR, `RadialL2 ≃ₗᵢ[ℂ] ReducedRadialL2`.
* `HarmonicIdx` — the index Σ ℓ, {m // |m| ≤ ℓ} of quantum number pairs.
* `l2R3` — L²(ℝ³) in spherical coordinates, `Lp ℂ 2 (radialMeasure.prod sphereMeasure)`.
* `sectorEmbedding` — the isometric embedding R ↦ R ⊗ Y_ℓ^m, `RadialL2 →ₗᵢ[ℂ] l2R3`.
* `sphericalDecomposition` — the unitary L²(ℝ³) ≃ₗᵢ[ℂ] lp (fun _ => RadialL2) 2,
  i.e. ⊕_ℓ RadialL2 ⊗ V_ℓ with each V_ℓ expanded in its Y_ℓ^m basis.

## Main statements

* `eLpNorm_radialReductionFun` — ∫|rR|² dr = ∫|R|² r²dr  (proved).
* `radialReduction_coeFn`, `radialReduction_symm_coeFn` — the unitary and
  its inverse act pointwise a.e. as multiplication by r and r⁻¹  (proved).
* `eLpNorm_tensorFun` — ‖R ⊗ Y_ℓ^m‖_{L²(ℝ³)} = ‖R‖_{L²(r²dr)}  (proved).
* `orthogonalFamily_sectorEmbedding` — distinct sectors are orthogonal  (proved).
* `sectorEmbedding_dense` — the sectors jointly span a dense subspace  (proved).
* `sphericalDecomposition_isometry` — the decomposition is unitary  (proved).
* `sphericalDecomposition_symm_apply`, `sphericalDecomposition_symm_single` —
  the inverse reassembles Σ_i R_i ⊗ Y_i in L²  (proved).

## Implementation notes

`radialMeasure` is `(volume.restrict (Ioi 0)).withDensity (fun r => r ^ 2)` rather than a genuine
measure on the subtype `Set.Ioi (0 : ℝ)`: subtype measures via `Measure.comap` have thin Mathlib
support, and since functions only matter a.e. and a.e. every point lies in `(0, ∞)`, this is
measure-theoretically equivalent for all L² purposes. Downstream statements quantify over `r : ℝ`
and use `ae_radial_mem_Ioi` to localize to `r > 0`; this mirrors the convention already used by
`thetaMeasure`/`phiMeasure` in `SphericalHarmonics/Basic.lean`.

`RadialL2` and `ReducedRadialL2` are `abbrev`s (mirroring `abbrev L2_S2`), so the
`NormedAddCommGroup`/`InnerProductSpace ℂ`/`CompleteSpace` instances on `Lp ℂ 2 _` flow through
without re-derivation.

`radialReduction` realizes R ↦ rR as a `LinearIsometryEquiv` with inverse χ ↦ r⁻¹χ; its analytic
content is the single lemma `eLpNorm_radialReductionFun`
(`‖rR‖_{L²(dr)} = ‖R‖_{L²(r²dr)}` at the `eLpNorm` level), with everything else a.e. bookkeeping
transported along the mutual absolute continuity of `radialMeasure` and `volume.restrict (Ioi 0)`.
Mathlib has no L² analogue of `withDensitySMulLI` (L¹-only, and merely ℝ-linear), so this
construction is original infrastructure (checked against v4.31.0-rc1).

`l2R3` is L²(ℝ³) *in spherical coordinates*: `Lp ℂ 2` of the product measure
`radialMeasure.prod sphereMeasure`, mirroring how `L2_S2` lives on the angular coordinate
rectangle in `Basic.lean`. The change of variables to Cartesian
`Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))` is independent infrastructure — Mathlib
stops at the 2D `polarCoord` — and can be precomposed later as one more unitary without touching
this file.

`sphericalDecomposition` targets `lp (fun _ : HarmonicIdx => RadialL2) 2` with
`HarmonicIdx = Σ ℓ, {m // |m| ≤ ℓ}`: Mathlib has no Hilbert-space tensor product (checked against
v4.31.0-rc1), so `⊕_ℓ (RadialL2 ⊗ V_ℓ)` is realized by expanding each `(2ℓ + 1)`-dimensional `V_ℓ`
in its orthonormal basis `{Y_ℓ^m}` — the standard, mathematically equivalent reformulation. The
unitary comes from `IsHilbertSum.mk` applied to the isometric sector embeddings `R ↦ R ⊗ Y_ℓ^m`
(orthogonal family + dense joint range); the completeness half consumes
`sphericalHarmonic_complete` from `Basic.lean` and mirrors its proof one level up.

This file constructs the two unitaries only. The radial Hamiltonian, the reduced radial operator,
the Laplacian separation, and the Coulomb-sector reduction this decomposition feeds into live
downstream: `radialHamiltonianGen`, `reducedRadialOp`, `coulomb_preserves_sectors`, and
`hydrogen_reduces` in `Spectrum/Eigenvalue.lean`, and `laplacian_separates` in
`Laplacian/Spherical.lean`.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics IV*][reed1978], §XIII.3.
* [Bethe, Salpeter, *Quantum Mechanics of One- and Two-Electron Atoms*][bethesalpeter1957].
-/

open MeasureTheory Complex Filter
open scoped Topology NNReal ENNReal
open Spectra.SphericalHarmonics
namespace Spectra.QuantumMechanics.Hydrogen.Decomposition

/-! ## The radial Hilbert space -/

/-- The radial measure r² dr on (0, ∞).

    This is the natural measure arising from spherical coordinates:
    dx = r² dr dΩ, so after integrating out the angular part,
    the radial functions live in L²((0,∞), r² dr).

    Realized as Lebesgue measure restricted to `(0, ∞)` with density
    `r ↦ ENNReal.ofReal (r²)`, in the same style as `thetaMeasure`. -/
noncomputable def radialMeasure : Measure ℝ :=
  ((volume : Measure ℝ).restrict (Set.Ioi 0)).withDensity fun r =>
    ENNReal.ofReal (r ^ 2)

/-- The density r ↦ r² (valued in `ℝ≥0∞`) is measurable. -/
lemma measurable_radialDensity :
    Measurable fun r : ℝ => ENNReal.ofReal (r ^ 2) :=
  (measurable_id.pow_const 2).ennreal_ofReal

/-- `radialMeasure` is σ-finite (a restricted Lebesgue measure with a density). -/
instance : SigmaFinite radialMeasure := by
  unfold radialMeasure
  infer_instance

/-- `radialMeasure` is absolutely continuous w.r.t. Lebesgue measure on
    `(0, ∞)` (it has a density). -/
lemma radialMeasure_absolutelyContinuous :
    radialMeasure ≪ (volume : Measure ℝ).restrict (Set.Ioi 0) :=
  withDensity_absolutelyContinuous _ _

/-- Conversely, Lebesgue measure on `(0, ∞)` is absolutely continuous w.r.t.
    `radialMeasure`: the density r² is a.e. nonzero there. Together with
    `radialMeasure_absolutelyContinuous` this says the two measures share
    null sets, which is what lets a.e. statements move freely between
    `RadialL2` and `ReducedRadialL2`. -/
lemma absolutelyContinuous_radialMeasure :
    (volume : Measure ℝ).restrict (Set.Ioi 0) ≪ radialMeasure := by
  unfold radialMeasure
  refine withDensity_absolutelyContinuous' measurable_radialDensity.aemeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact ENNReal.ofReal_ne_zero_iff.mpr (pow_pos (Set.mem_Ioi.mp hr) 2)

/-- Almost every point of `radialMeasure` lies in `(0, ∞)`. -/
lemma ae_radial_mem_Ioi : ∀ᵐ r ∂radialMeasure, r ∈ Set.Ioi (0 : ℝ) :=
  (ae_restrict_mem measurableSet_Ioi).filter_mono
    radialMeasure_absolutelyContinuous.ae_le

/-- The radial Hilbert space L²(ℝ⁺, r² dr).

    Functions R(r) with ∫₀^∞ |R(r)|² r² dr < ∞. -/
abbrev RadialL2 : Type := Lp ℂ 2 radialMeasure

/-- The reduced radial Hilbert space L²(ℝ⁺, dr).

    After the substitution χ(r) = r R(r), the measure simplifies:
    ∫|R(r)|² r² dr = ∫|χ(r)|² dr.

    The map R ↦ rR is a unitary isomorphism RadialL2 → ReducedRadialL2. -/
abbrev ReducedRadialL2 : Type := Lp ℂ 2 ((volume : Measure ℝ).restrict (Set.Ioi 0))

-- Smoke tests: the Hilbert space structure flows through the `abbrev`s.
example : CompleteSpace RadialL2 := inferInstance
noncomputable example : InnerProductSpace ℂ ReducedRadialL2 := inferInstance

/-- **The isometry identity** ‖rg‖²_{L²(dr)} = ‖g‖²_{L²(r²dr)}, stated at the
    `eLpNorm` level (and hence with no integrability hypotheses at all: both
    sides are `ℝ≥0∞`-valued). This single computation drives the entire
    construction of `radialReduction`. -/
lemma eLpNorm_radialReductionFun (g : ℝ → ℂ) :
    eLpNorm (fun (r : ℝ) => (r : ℂ) * g r) 2 ((volume : Measure ℝ).restrict (Set.Ioi 0)) =
      eLpNorm g 2 radialMeasure := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  unfold radialMeasure
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ measurable_radialDensity
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : (0 : ℝ) < r := Set.mem_Ioi.mp hr
  simp only [Pi.mul_apply]
  rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  rw [show ‖((r : ℝ) : ℂ)‖ₑ = ‖r‖ₑ by simp [enorm_eq_nnnorm],
    Real.enorm_eq_ofReal_abs, abs_of_pos hr0,
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    ENNReal.rpow_natCast, ← ENNReal.ofReal_pow hr0.le]

/-- Multiplication by r maps L²(r²dr) into L²(dr). -/
lemma memLp_radialReductionFun {g : ℝ → ℂ} (hg : MemLp g 2 radialMeasure) :
    MemLp (fun (r : ℝ) => (r : ℂ) * g r) 2 ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
  refine ⟨Complex.measurable_ofReal.aestronglyMeasurable.mul
    (hg.aestronglyMeasurable.mono_ac absolutelyContinuous_radialMeasure), ?_⟩
  rw [eLpNorm_radialReductionFun]
  exact hg.2

/-- Multiplication by r⁻¹ maps L²(dr) into L²(r²dr). -/
lemma memLp_radialReductionInvFun {χ : ℝ → ℂ}
    (hχ : MemLp χ 2 ((volume : Measure ℝ).restrict (Set.Ioi 0))) :
    MemLp (fun r => ((r : ℝ) : ℂ)⁻¹ * χ r) 2 radialMeasure := by
  refine ⟨Complex.measurable_ofReal.inv.aestronglyMeasurable.mul
    (hχ.aestronglyMeasurable.mono_ac radialMeasure_absolutelyContinuous), ?_⟩
  have hcollapse : (fun r : ℝ => (r : ℂ) * (((r : ℝ) : ℂ)⁻¹ * χ r))
      =ᵐ[(volume : Measure ℝ).restrict (Set.Ioi 0)] χ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hne : ((r : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Set.mem_Ioi.mp hr))
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  calc eLpNorm (fun r => ((r : ℝ) : ℂ)⁻¹ * χ r) 2 radialMeasure
      = eLpNorm (fun (r : ℝ) => (r : ℂ) * (((r : ℝ) : ℂ)⁻¹ * χ r)) 2
          ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
        (eLpNorm_radialReductionFun fun r => ((r : ℝ) : ℂ)⁻¹ * χ r).symm
    _ = eLpNorm χ 2 ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
        eLpNorm_congr_ae hcollapse
    _ < ∞ := hχ.2

/-- The unitary map R(r) ↦ rR(r) from RadialL2 to ReducedRadialL2,
    with inverse χ(r) ↦ r⁻¹χ(r).

    **Discharged** by the direct isometry computation
    ‖rR‖²_{L²(dr)} = ∫|rR(r)|² dr = ∫|R(r)|² r² dr = ‖R‖²_{L²(r²dr)}
    (`eLpNorm_radialReductionFun`); the inverse identities hold a.e. because
    r ≠ 0 almost everywhere for both measures. -/
noncomputable def radialReduction : RadialL2 ≃ₗᵢ[ℂ] ReducedRadialL2 :=
  { toFun := fun R => (memLp_radialReductionFun (Lp.memLp R)).toLp
      (fun r => (r : ℂ) * R r)
    invFun := fun χ => (memLp_radialReductionInvFun (Lp.memLp χ)).toLp
      (fun r => ((r : ℝ) : ℂ)⁻¹ * χ r)
    map_add' := by
      intro R₁ R₂
      refine Lp.ext ?_
      filter_upwards [(memLp_radialReductionFun (Lp.memLp (R₁ + R₂))).coeFn_toLp,
        (memLp_radialReductionFun (Lp.memLp R₁)).coeFn_toLp,
        (memLp_radialReductionFun (Lp.memLp R₂)).coeFn_toLp,
        Lp.coeFn_add ((memLp_radialReductionFun (Lp.memLp R₁)).toLp _)
          ((memLp_radialReductionFun (Lp.memLp R₂)).toLp _),
        (Lp.coeFn_add R₁ R₂).filter_mono absolutelyContinuous_radialMeasure.ae_le]
        with r h12 h1 h2 hadd hR
      rw [h12, hadd, Pi.add_apply, h1, h2, hR, Pi.add_apply, mul_add]
    map_smul' := by
      intro c R
      refine Lp.ext ?_
      filter_upwards [(memLp_radialReductionFun (Lp.memLp (c • R))).coeFn_toLp,
        (memLp_radialReductionFun (Lp.memLp R)).coeFn_toLp,
        Lp.coeFn_smul c ((memLp_radialReductionFun (Lp.memLp R)).toLp _),
        (Lp.coeFn_smul c R).filter_mono absolutelyContinuous_radialMeasure.ae_le]
        with r hc h1 hsmul hR
      rw [RingHom.id_apply] at *
      rw [hc, hsmul, Pi.smul_apply, h1, hR, Pi.smul_apply, smul_eq_mul,
        smul_eq_mul, mul_left_comm]
    left_inv := by
      intro R
      refine Lp.ext ?_
      filter_upwards [(memLp_radialReductionInvFun
          (Lp.memLp ((memLp_radialReductionFun (Lp.memLp R)).toLp _))).coeFn_toLp,
        ((memLp_radialReductionFun (Lp.memLp R)).coeFn_toLp).filter_mono
          radialMeasure_absolutelyContinuous.ae_le,
        ae_radial_mem_Ioi] with r hout hin hr
      have hne : ((r : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt (Set.mem_Ioi.mp hr))
      rw [hout, hin, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    right_inv := by
      intro χ
      refine Lp.ext ?_
      filter_upwards [(memLp_radialReductionFun
          (Lp.memLp ((memLp_radialReductionInvFun (Lp.memLp χ)).toLp _))).coeFn_toLp,
        ((memLp_radialReductionInvFun (Lp.memLp χ)).coeFn_toLp).filter_mono
          absolutelyContinuous_radialMeasure.ae_le,
        ae_restrict_mem measurableSet_Ioi] with r hout hin hr
      have hne : ((r : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt (Set.mem_Ioi.mp hr))
      rw [hout, hin, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    norm_map' := by
      intro R
      change ‖(memLp_radialReductionFun (Lp.memLp R)).toLp (fun (r : ℝ) => (r : ℂ) * R r)‖ = ‖R‖
      rw [Lp.norm_toLp, eLpNorm_radialReductionFun]
      exact (Lp.norm_def R).symm }

/-- The unitary acts a.e. as multiplication by r. -/
lemma radialReduction_coeFn (R : RadialL2) :
    ⇑(radialReduction R) =ᵐ[(volume : Measure ℝ).restrict (Set.Ioi 0)]
      fun r => (r : ℂ) * R r :=
  (memLp_radialReductionFun (Lp.memLp R)).coeFn_toLp

/-- The inverse unitary acts a.e. as multiplication by r⁻¹. -/
lemma radialReduction_symm_coeFn (χ : ReducedRadialL2) :
    ⇑(radialReduction.symm χ) =ᵐ[radialMeasure]
      fun r => ((r : ℝ) : ℂ)⁻¹ * χ r :=
  (memLp_radialReductionInvFun (Lp.memLp χ)).coeFn_toLp


/-! ## Spherical coordinate decomposition

**Design note.** `l2R3` below is L²(ℝ³) *in spherical coordinates*: the
Lebesgue space of the product measure `radialMeasure.prod sphereMeasure` on
`ℝ × (ℝ × ℝ)` (radius × angular chart). This matches the convention of
`SphericalHarmonics/Basic.lean`, where `L2_S2` already lives on the angular
coordinate rectangle rather than on the embedded sphere. The unitary change
of variables to `Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))` is
independent infrastructure (3D spherical change of variables; not in Mathlib,
which stops at 2D `polarCoord`) and can be precomposed later without touching
anything in this section.

The target ⊕_ℓ (RadialL2 ⊗ V_ℓ) is realized as the Hilbert sum
`lp (fun _ : HarmonicIdx => RadialL2) 2` over the index set
`HarmonicIdx = Σ ℓ, {m // |m| ≤ ℓ}`: each (2ℓ+1)-dimensional sector V_ℓ is
expanded in its orthonormal basis {Y_ℓ^m}, so RadialL2 ⊗ V_ℓ ≅ (RadialL2)^{2ℓ+1}.
(Mathlib has no Hilbert-space tensor product, verified against v4.31.0-rc1;
this reformulation is the standard one and is mathematically equivalent.)
The unitary itself is produced by `IsHilbertSum.mk`: an orthogonal family of
isometric embeddings with dense joint range induces an isometric isomorphism
onto the lp-sum. -/

/-- The index set of joint angular-momentum quantum numbers: pairs (ℓ, m)
    with |m| ≤ ℓ. Summing over `HarmonicIdx` is summing over ℓ with each
    sector V_ℓ expanded in its orthonormal basis. -/
def HarmonicIdx : Type := Σ ℓ : ℕ, {m : ℤ // |m| ≤ (ℓ : ℤ)}

/-- The index set `HarmonicIdx` is countable. -/
instance : Countable HarmonicIdx := by
  unfold HarmonicIdx
  infer_instance

/-- Equality of indices in `HarmonicIdx` is decidable. -/
instance : DecidableEq HarmonicIdx := by
  unfold HarmonicIdx
  exact inferInstance

/-- Extensionality: equal quantum numbers, equal index. -/
lemma HarmonicIdx.ext {i j : HarmonicIdx} (h1 : i.1 = j.1) (h2 : i.2.1 = j.2.1) :
    i = j :=
  Sigma.subtype_ext h1 h2

/-- The spherical harmonic attached to an index. -/
noncomputable def harmonic (i : HarmonicIdx) : ℝ × ℝ → ℂ :=
  SphericalHarmonic i.1 i.2.1 i.2.2

/-- The spherical harmonic attached to an index is continuous. -/
lemma harmonic_continuous (i : HarmonicIdx) : Continuous (harmonic i) :=
  sphericalHarmonic_continuous i.1 i.2.1 i.2.2

/-- The spherical harmonic attached to an index lies in L²(S²). -/
lemma memLp_harmonic (i : HarmonicIdx) : MemLp (harmonic i) 2 sphereMeasure :=
  memLp_sphericalHarmonic i.1 i.2.1 i.2.2

/-- The spherical harmonic as an element of L²(S²). -/
noncomputable def harmonicLp (i : HarmonicIdx) : L2_S2 :=
  (memLp_harmonic i).toLp (harmonic i)

/-- The L²(S²) element `harmonicLp i` agrees a.e. with the function `harmonic i`. -/
lemma harmonicLp_coeFn (i : HarmonicIdx) :
    ⇑(harmonicLp i) =ᵐ[sphereMeasure] harmonic i :=
  (memLp_harmonic i).coeFn_toLp

/-- Orthonormality of the indexed family, packaged with a single `if`. -/
lemma inner_harmonicLp (i j : HarmonicIdx) :
    inner ℂ (harmonicLp i) (harmonicLp j) = if i = j then (1 : ℂ) else 0 := by
  have h : inner ℂ (harmonicLp i) (harmonicLp j) =
      if i.1 = j.1 ∧ i.2.1 = j.2.1 then (1 : ℂ) else 0 := by
    rw [show inner ℂ (harmonicLp i) (harmonicLp j) =
        inner ℂ
          ((memLp_sphericalHarmonic i.1 i.2.1 i.2.2).toLp
            (SphericalHarmonic i.1 i.2.1 i.2.2))
          ((memLp_sphericalHarmonic j.1 j.2.1 j.2.2).toLp
            (SphericalHarmonic j.1 j.2.1 j.2.2)) from rfl,
      inner_toLp_sphericalHarmonic, sphericalHarmonic_orthonormal]
  rw [h]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [if_neg hij, if_neg fun hcon => hij (HarmonicIdx.ext hcon.1 hcon.2)]

/-- Each Y_ℓ^m is a unit vector of L²(S²). -/
lemma norm_harmonicLp (i : HarmonicIdx) : ‖harmonicLp i‖ = 1 := by
  have h := inner_harmonicLp i i
  rw [if_pos rfl] at h
  have h3 : ‖harmonicLp i‖ ^ 2 = 1 := by
    have h4 := inner_self_eq_norm_sq (𝕜 := ℂ) (harmonicLp i)
    rw [h] at h4
    simpa using h4.symm
  nlinarith [norm_nonneg (harmonicLp i)]

/-- The normalization at the `lintegral` level: ∫ |Y_ℓ^m|² dΩ = 1. -/
lemma lintegral_enorm_sq_harmonic (i : HarmonicIdx) :
    ∫⁻ ω, ‖harmonic i ω‖ₑ ^ (2 : ℝ) ∂sphereMeasure = 1 := by
  have h1 : eLpNorm (harmonic i) 2 sphereMeasure = 1 := by
    have hne : eLpNorm (harmonic i) 2 sphereMeasure ≠ ∞ := (memLp_harmonic i).2.ne
    have ht : (eLpNorm (harmonic i) 2 sphereMeasure).toReal = 1 := by
      rw [← Lp.norm_toLp _ (memLp_harmonic i)]
      exact norm_harmonicLp i
    rw [← ENNReal.ofReal_toReal hne, ht, ENNReal.ofReal_one]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top] at h1
  simp only [ENNReal.toReal_ofNat] at h1
  calc ∫⁻ ω, ‖harmonic i ω‖ₑ ^ (2 : ℝ) ∂sphereMeasure
      = ((∫⁻ ω, ‖harmonic i ω‖ₑ ^ (2 : ℝ) ∂sphereMeasure) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num,
          ENNReal.rpow_one]
    _ = (1 : ℝ≥0∞) ^ (2 : ℝ) := by rw [h1]
    _ = 1 := ENNReal.one_rpow _

/-- L²(ℝ³) in spherical coordinates: the Lebesgue space of the product of
    the radial measure r²dr on (0,∞) and the sphere measure sinθ dθ dφ.
    (See the design note at the top of this section.) -/
abbrev l2R3 : Type := Lp ℂ 2 (radialMeasure.prod sphereMeasure)

-- Smoke tests: the Hilbert space structure flows through the `abbrev`.
example : CompleteSpace l2R3 := inferInstance
noncomputable example : InnerProductSpace ℂ l2R3 := inferInstance

/-- The pure tensor g ⊗ Y_i as a function on (0,∞) × S². -/
noncomputable def tensorFun (g : ℝ → ℂ) (i : HarmonicIdx) : ℝ × (ℝ × ℝ) → ℂ :=
  fun p => g p.1 * harmonic i p.2

/-- **The isometry identity for pure tensors**: since Y_i is normalized,
    ‖g ⊗ Y_i‖_{L²(prod)} = ‖g‖_{L²(r²dr)}. Stated at the `eLpNorm` level,
    so it needs only measurability of `g`, no integrability. -/
lemma eLpNorm_tensorFun {g : ℝ → ℂ} (hg : AEStronglyMeasurable g radialMeasure)
    (i : HarmonicIdx) :
    eLpNorm (tensorFun g i) 2 (radialMeasure.prod sphereMeasure) =
      eLpNorm g 2 radialMeasure := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  calc ∫⁻ p, ‖tensorFun g i p‖ₑ ^ (2 : ℝ) ∂(radialMeasure.prod sphereMeasure)
      = ∫⁻ p, (fun r => ‖g r‖ₑ ^ (2 : ℝ)) p.1 *
          (fun ω => ‖harmonic i ω‖ₑ ^ (2 : ℝ)) p.2
          ∂(radialMeasure.prod sphereMeasure) := by
        refine lintegral_congr fun p => ?_
        simp only [tensorFun]
        rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    _ = (∫⁻ r, ‖g r‖ₑ ^ (2 : ℝ) ∂radialMeasure) *
          ∫⁻ ω, ‖harmonic i ω‖ₑ ^ (2 : ℝ) ∂sphereMeasure :=
        lintegral_prod_mul (hg.enorm.pow_const (2 : ℝ))
          ((harmonic_continuous i).aestronglyMeasurable.enorm.pow_const (2 : ℝ))
    _ = ∫⁻ r, ‖g r‖ₑ ^ (2 : ℝ) ∂radialMeasure := by
        rw [lintegral_enorm_sq_harmonic, mul_one]

/-- Pure tensors over L²(r²dr) land in L²(prod). -/
lemma memLp_tensorFun {g : ℝ → ℂ} (hg : MemLp g 2 radialMeasure) (i : HarmonicIdx) :
    MemLp (tensorFun g i) 2 (radialMeasure.prod sphereMeasure) := by
  refine ⟨?_, ?_⟩
  · exact (hg.aestronglyMeasurable.comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst).mul
      ((harmonic_continuous i).comp continuous_snd).aestronglyMeasurable
  · rw [eLpNorm_tensorFun hg.aestronglyMeasurable]
    exact hg.2

/-- Modifying the radial factor on a radial null set modifies the tensor only
    on a product null set. -/
lemma tensorFun_congr_ae {g g' : ℝ → ℂ} (h : g =ᵐ[radialMeasure] g')
    (i : HarmonicIdx) :
    tensorFun g i =ᵐ[radialMeasure.prod sphereMeasure] tensorFun g' i := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae_eq h] with p hp
  change g p.1 * harmonic i p.2 = g' p.1 * harmonic i p.2
  rw [show g p.1 = g' p.1 from hp]

/-- **The sector embedding**: the isometric embedding R ↦ R ⊗ Y_i of the
    radial Hilbert space into L²(ℝ³) along the spherical harmonic Y_i.
    Its range is the (ℓ, m)-sector of the decomposition. -/
noncomputable def sectorEmbedding (i : HarmonicIdx) : RadialL2 →ₗᵢ[ℂ] l2R3 :=
  { toFun := fun R => (memLp_tensorFun (Lp.memLp R) i).toLp (tensorFun (⇑R) i)
    map_add' := by
      intro R₁ R₂
      refine Lp.ext ?_
      filter_upwards [(memLp_tensorFun (Lp.memLp (R₁ + R₂)) i).coeFn_toLp,
        (memLp_tensorFun (Lp.memLp R₁) i).coeFn_toLp,
        (memLp_tensorFun (Lp.memLp R₂) i).coeFn_toLp,
        Lp.coeFn_add ((memLp_tensorFun (Lp.memLp R₁) i).toLp _)
          ((memLp_tensorFun (Lp.memLp R₂) i).toLp _),
        tensorFun_congr_ae (Lp.coeFn_add R₁ R₂) i] with p h12 h1 h2 hadd hT
      rw [h12, hT, hadd, Pi.add_apply, h1, h2]
      simp only [tensorFun, Pi.add_apply]
      ring
    map_smul' := by
      intro c R
      refine Lp.ext ?_
      filter_upwards [(memLp_tensorFun (Lp.memLp (c • R)) i).coeFn_toLp,
        (memLp_tensorFun (Lp.memLp R) i).coeFn_toLp,
        Lp.coeFn_smul c ((memLp_tensorFun (Lp.memLp R) i).toLp _),
        tensorFun_congr_ae (Lp.coeFn_smul c R) i] with p hc h1 hsmul hT
      rw [RingHom.id_apply] at *
      rw [hc, hT, hsmul, Pi.smul_apply, h1]
      simp only [tensorFun, Pi.smul_apply, smul_eq_mul]
      ring
    norm_map' := by
      intro R
      change ‖(memLp_tensorFun (Lp.memLp R) i).toLp (tensorFun (⇑R) i)‖ = ‖R‖
      rw [Lp.norm_toLp, eLpNorm_tensorFun (Lp.aestronglyMeasurable R)]
      exact (Lp.norm_def R).symm }

/-- The sector embedding acts a.e. as the pure tensor. -/
lemma sectorEmbedding_coeFn (i : HarmonicIdx) (R : RadialL2) :
    ⇑(sectorEmbedding i R) =ᵐ[radialMeasure.prod sphereMeasure] tensorFun (⇑R) i :=
  (memLp_tensorFun (Lp.memLp R) i).coeFn_toLp

/-- The angular inner product in integral form. -/
lemma inner_harmonicLp_eq (i j : HarmonicIdx) :
    inner ℂ (harmonicLp i) (harmonicLp j) =
      ∫ ω, (starRingEnd ℂ) (harmonic i ω) * harmonic j ω ∂sphereMeasure := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [harmonicLp_coeFn i, harmonicLp_coeFn j] with ω h1 h2
  rw [h1, h2, RCLike.inner_apply']

/-- **Inner products factor over pure tensors**: ⟨R ⊗ Y_i, R' ⊗ Y_j⟩ equals
    the radial pairing times the angular pairing. The product integral
    factorizes unconditionally (`integral_prod_mul` for `RCLike` scalars). -/
lemma inner_sectorEmbedding (i j : HarmonicIdx) (R R' : RadialL2) :
    inner ℂ (sectorEmbedding i R) (sectorEmbedding j R') =
      (∫ r, (starRingEnd ℂ) (R r) * R' r ∂radialMeasure) *
        inner ℂ (harmonicLp i) (harmonicLp j) := by
  rw [inner_harmonicLp_eq]
  calc inner ℂ (sectorEmbedding i R) (sectorEmbedding j R')
      = ∫ p, inner ℂ ((sectorEmbedding i R) p) ((sectorEmbedding j R') p)
          ∂(radialMeasure.prod sphereMeasure) := L2.inner_def _ _
    _ = ∫ p, (fun r => (starRingEnd ℂ) (R r) * R' r) p.1 *
          (fun ω => (starRingEnd ℂ) (harmonic i ω) * harmonic j ω) p.2
          ∂(radialMeasure.prod sphereMeasure) := by
        refine integral_congr_ae ?_
        filter_upwards [sectorEmbedding_coeFn i R, sectorEmbedding_coeFn j R']
          with p h1 h2
        rw [RCLike.inner_apply', h1, h2]
        simp only [tensorFun]
        rw [map_mul]
        ring
    _ = (∫ r, (starRingEnd ℂ) (R r) * R' r ∂radialMeasure) *
          ∫ ω, (starRingEnd ℂ) (harmonic i ω) * harmonic j ω ∂sphereMeasure := by
        exact integral_prod_mul (μ := radialMeasure) (ν := sphereMeasure)
          (fun r => (starRingEnd ℂ) (R r) * R' r)
          (fun ω => (starRingEnd ℂ) (harmonic i ω) * harmonic j ω)

/-- **Orthogonality of the sectors**: distinct quantum numbers give
    orthogonal ranges, because the spherical harmonics are orthogonal. -/
theorem orthogonalFamily_sectorEmbedding :
    OrthogonalFamily ℂ (fun _ : HarmonicIdx => RadialL2) sectorEmbedding := by
  intro i j hij R R'
  rw [inner_sectorEmbedding, inner_harmonicLp, if_neg hij, mul_zero]

/-! ### Completeness of the sectors

The joint range of the sector embeddings is dense. The proof mirrors the
completeness argument for the spherical harmonics themselves
(`sphericalHarmonic_complete`), one level up: if F ⊥ every R ⊗ Y_i, then
each angular coefficient function c_i(r) = ∫ conj(Y_i) F(r,·) dΩ is an L²
radial function (Cauchy–Schwarz fiberwise plus Tonelli) orthogonal to all of
RadialL2, hence zero; so for a.e. r the slice F(r,·) is orthogonal to every
spherical harmonic, hence zero by the angular completeness theorem; gluing
the slices, F = 0. -/

/-- The angular coefficient function of F at index i:
    c_i(r) = ∫ conj(Y_i(ω)) F(r, ω) dΩ. -/
noncomputable def coeffFun (i : HarmonicIdx) (F : l2R3) : ℝ → ℂ :=
  fun r => ∫ ω, (starRingEnd ℂ) (harmonic i ω) * F (r, ω) ∂sphereMeasure

/-- The angular coefficient function `coeffFun i F` is a.e. strongly measurable
    (as a radial function), by integrating the joint measurability of `F` over
    the sphere. -/
lemma coeffFun_aestronglyMeasurable (i : HarmonicIdx) (F : l2R3) :
    AEStronglyMeasurable (coeffFun i F) radialMeasure := by
  have hsm : StronglyMeasurable fun p : ℝ × (ℝ × ℝ) =>
      (starRingEnd ℂ) (harmonic i p.2) * F p :=
    (((Complex.continuous_conj.comp (harmonic_continuous i)).comp
      continuous_snd).stronglyMeasurable).mul (Lp.stronglyMeasurable F)
  exact (StronglyMeasurable.integral_prod_right' hsm).aestronglyMeasurable

/-- Fiberwise Cauchy–Schwarz: |c_i(r)| ≤ ‖Y_i‖_{L²(S²)} ‖F(r,·)‖_{L²(S²)},
    with ‖Y_i‖ = 1. Stated in `ℝ≥0∞` (Hölder for `lintegral`), so it holds
    for every r with no integrability hypotheses. -/
lemma enorm_coeffFun_le (i : HarmonicIdx) (F : l2R3) (r : ℝ) :
    ‖coeffFun i F r‖ₑ ≤
      (∫⁻ ω, ‖F (r, ω)‖ₑ ^ (2 : ℝ) ∂sphereMeasure) ^ (1 / 2 : ℝ) := by
  have hslice : AEMeasurable (fun ω => ‖F (r, ω)‖ₑ) sphereMeasure :=
    (((Lp.stronglyMeasurable F).comp_measurable
      measurable_prodMk_left).aestronglyMeasurable).enorm
  have hY : AEMeasurable (fun ω => ‖harmonic i ω‖ₑ) sphereMeasure :=
    (harmonic_continuous i).aestronglyMeasurable.enorm
  calc ‖coeffFun i F r‖ₑ
      ≤ ∫⁻ ω, ‖(starRingEnd ℂ) (harmonic i ω) * F (r, ω)‖ₑ ∂sphereMeasure :=
        enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ ω, ((fun ω => ‖harmonic i ω‖ₑ) * fun ω => ‖F (r, ω)‖ₑ) ω
          ∂sphereMeasure := by
        refine lintegral_congr fun ω => ?_
        simp [enorm_mul]
    _ ≤ (∫⁻ ω, ‖harmonic i ω‖ₑ ^ (2 : ℝ) ∂sphereMeasure) ^ (1 / 2 : ℝ) *
        (∫⁻ ω, ‖F (r, ω)‖ₑ ^ (2 : ℝ) ∂sphereMeasure) ^ (1 / 2 : ℝ) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq sphereMeasure
          Real.HolderConjugate.two_two hY hslice
    _ = (∫⁻ ω, ‖F (r, ω)‖ₑ ^ (2 : ℝ) ∂sphereMeasure) ^ (1 / 2 : ℝ) := by
        rw [lintegral_enorm_sq_harmonic, ENNReal.one_rpow, one_mul]

/-- The coefficient functions are radial L² functions:
    ∫ |c_i(r)|² r²dr ≤ ‖F‖² < ∞ by Cauchy–Schwarz and Tonelli. -/
lemma memLp_coeffFun (i : HarmonicIdx) (F : l2R3) :
    MemLp (coeffFun i F) 2 radialMeasure := by
  refine ⟨coeffFun_aestronglyMeasurable i F, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat]
  rw [ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hFfin : ∫⁻ p, ‖F p‖ₑ ^ (2 : ℝ) ∂(radialMeasure.prod sphereMeasure) < ∞ := by
    have h2 := (Lp.memLp F).2
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top] at h2
    simp only [ENNReal.toReal_ofNat] at h2
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mp h2
  calc ∫⁻ r, ‖coeffFun i F r‖ₑ ^ (2 : ℝ) ∂radialMeasure
      ≤ ∫⁻ r, ((∫⁻ ω, ‖F (r, ω)‖ₑ ^ (2 : ℝ) ∂sphereMeasure) ^ (1 / 2 : ℝ)) ^ (2 : ℝ)
          ∂radialMeasure :=
        lintegral_mono fun r =>
          ENNReal.rpow_le_rpow (enorm_coeffFun_le i F r) (by norm_num)
    _ = ∫⁻ r, ∫⁻ ω, ‖F (r, ω)‖ₑ ^ (2 : ℝ) ∂sphereMeasure ∂radialMeasure := by
        refine lintegral_congr fun r => ?_
        rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num,
          ENNReal.rpow_one]
    _ = ∫⁻ p, ‖F p‖ₑ ^ (2 : ℝ) ∂(radialMeasure.prod sphereMeasure) :=
        (lintegral_prod _ ((Lp.aestronglyMeasurable F).enorm.pow_const (2 : ℝ))).symm
    _ < ∞ := hFfin

/-- **The Fubini step**: pairing F against a sector element R ⊗ Y_i reduces
    to the radial pairing of R against the coefficient function c_i. -/
lemma inner_sectorEmbedding_eq_integral_coeffFun (i : HarmonicIdx) (R : RadialL2)
    (F : l2R3) :
    inner ℂ (sectorEmbedding i R) F =
      ∫ r, (starRingEnd ℂ) (R r) * coeffFun i F r ∂radialMeasure := by
  have hI : Integrable
      (fun p : ℝ × (ℝ × ℝ) => (starRingEnd ℂ) (tensorFun (⇑R) i p) * F p)
      (radialMeasure.prod sphereMeasure) := by
    refine (L2.integrable_inner (𝕜 := ℂ) (sectorEmbedding i R) F).congr ?_
    filter_upwards [sectorEmbedding_coeFn i R] with p hp
    rw [RCLike.inner_apply', hp]
  calc inner ℂ (sectorEmbedding i R) F
      = ∫ p, inner ℂ ((sectorEmbedding i R) p) (F p)
          ∂(radialMeasure.prod sphereMeasure) := L2.inner_def _ _
    _ = ∫ p, (starRingEnd ℂ) (tensorFun (⇑R) i p) * F p
          ∂(radialMeasure.prod sphereMeasure) := by
        refine integral_congr_ae ?_
        filter_upwards [sectorEmbedding_coeFn i R] with p hp
        rw [RCLike.inner_apply', hp]
    _ = ∫ r, ∫ ω, (starRingEnd ℂ) (tensorFun (⇑R) i (r, ω)) * F (r, ω)
          ∂sphereMeasure ∂radialMeasure := integral_prod _ hI
    _ = ∫ r, (starRingEnd ℂ) (R r) * coeffFun i F r ∂radialMeasure := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
        calc ∫ ω, (starRingEnd ℂ) (tensorFun (⇑R) i (r, ω)) * F (r, ω) ∂sphereMeasure
            = ∫ ω, (starRingEnd ℂ) (R r) *
                ((starRingEnd ℂ) (harmonic i ω) * F (r, ω)) ∂sphereMeasure := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
              simp only [tensorFun]
              rw [map_mul]
              ring
          _ = (starRingEnd ℂ) (R r) * coeffFun i F r :=
              integral_const_mul _ _

/-- **Density of the sectors**: the closure of the joint range of the sector
    embeddings is everything. This is the completeness half of the spherical
    decomposition, consuming `sphericalHarmonic_complete` from `Basic.lean`. -/
theorem sectorEmbedding_dense :
    ⊤ ≤ (⨆ i : HarmonicIdx,
        LinearMap.range (sectorEmbedding i).toLinearMap).topologicalClosure := by
  rw [top_le_iff, Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro F hF
  -- Step 1: F is orthogonal to every sector element.
  have hinner : ∀ (i : HarmonicIdx) (R : RadialL2),
      inner ℂ (sectorEmbedding i R) F = 0 := fun i R =>
    (Submodule.mem_orthogonal
        (K := ⨆ i : HarmonicIdx, LinearMap.range (sectorEmbedding i).toLinearMap)
        F).mp hF
      (sectorEmbedding i R)
      (Submodule.mem_iSup_of_mem i (LinearMap.mem_range.mpr ⟨R, rfl⟩))
  -- Step 2: hence every radial pairing against c_i vanishes.
  have key : ∀ (i : HarmonicIdx) (R : RadialL2),
      ∫ r, (starRingEnd ℂ) (R r) * coeffFun i F r ∂radialMeasure = 0 := by
    intro i R
    rw [← inner_sectorEmbedding_eq_integral_coeffFun]
    exact hinner i R
  -- Step 3: testing against c_i itself, each c_i vanishes a.e.
  have hc0 : ∀ i : HarmonicIdx, coeffFun i F =ᵐ[radialMeasure] 0 := by
    intro i
    have h := key i ((memLp_coeffFun i F).toLp (coeffFun i F))
    have h2 : inner ℂ ((memLp_coeffFun i F).toLp (coeffFun i F))
        ((memLp_coeffFun i F).toLp (coeffFun i F)) = 0 := by
      rw [L2.inner_def, ← h]
      refine integral_congr_ae ?_
      filter_upwards [(memLp_coeffFun i F).coeFn_toLp] with r hr
      rw [RCLike.inner_apply', hr]
    have h3 := inner_self_eq_zero.mp h2
    refine ((memLp_coeffFun i F).coeFn_toLp).symm.trans ?_
    rw [h3]
    exact Lp.coeFn_zero ℂ 2 radialMeasure
  -- Step 4: a.e. slices of F lie in L²(S²).
  have hslice_mem : ∀ᵐ r ∂radialMeasure,
      MemLp (fun ω => F (r, ω)) 2 sphereMeasure := by
    have hF2 : MemLp (⇑F) 2 (radialMeasure.prod sphereMeasure) := Lp.memLp F
    have hsq := (memLp_two_iff_integrable_sq_norm hF2.aestronglyMeasurable).mp hF2
    filter_upwards [hsq.prod_right_ae] with r hr
    exact (memLp_two_iff_integrable_sq_norm
      (((Lp.stronglyMeasurable F).comp_measurable
        measurable_prodMk_left).aestronglyMeasurable)).mpr hr
  -- Step 5: for a.e. r, the slice is orthogonal to every spherical harmonic,
  -- hence zero by the angular completeness theorem.
  have hslices : ∀ᵐ r ∂radialMeasure, ∀ᵐ ω ∂sphereMeasure, F (r, ω) = 0 := by
    have hall : ∀ᵐ r ∂radialMeasure, ∀ i : HarmonicIdx, coeffFun i F r = 0 :=
      ae_all_iff.mpr fun i => by
        filter_upwards [hc0 i] with r hr
        simpa using hr
    filter_upwards [hall, hslice_mem] with r hri hmem
    have hg : hmem.toLp (fun ω => F (r, ω)) ∈ (Submodule.span ℂ harmonicSet)ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro u hu
      induction hu using Submodule.span_induction with
      | mem v hv =>
          obtain ⟨ℓ, m, hm, rfl⟩ := hv
          have hval : inner ℂ
              ((memLp_sphericalHarmonic ℓ m hm).toLp (SphericalHarmonic ℓ m hm))
              (hmem.toLp fun ω => F (r, ω)) = coeffFun ⟨ℓ, ⟨m, hm⟩⟩ F r := by
            rw [L2.inner_def]
            simp only [coeffFun]
            refine integral_congr_ae ?_
            filter_upwards [(memLp_sphericalHarmonic ℓ m hm).coeFn_toLp,
              hmem.coeFn_toLp] with ω h1 h2
            rw [h1, h2, RCLike.inner_apply']
            simp only [harmonic]
          rw [hval]
          exact hri ⟨ℓ, ⟨m, hm⟩⟩
      | zero => simp
      | add u v hu hv hu' hv' => rw [inner_add_left, hu', hv', add_zero]
      | smul c u hu hu' => rw [inner_smul_left, hu', mul_zero]
    have hbot : (Submodule.span ℂ harmonicSet)ᗮ = ⊥ := by
      have hcomp : (Submodule.span ℂ harmonicSet).topologicalClosure = ⊤ :=
        sphericalHarmonic_complete
      rwa [Submodule.topologicalClosure_eq_top_iff] at hcomp
    have hzero : hmem.toLp (fun ω => F (r, ω)) = 0 := by
      have hmem0 := hbot ▸ hg
      simpa using hmem0
    have hae : (fun ω => F (r, ω)) =ᵐ[sphereMeasure] 0 := by
      refine (hmem.coeFn_toLp).symm.trans ?_
      rw [hzero]
      exact Lp.coeFn_zero ℂ 2 sphereMeasure
    filter_upwards [hae] with ω hω
    simpa using hω
  -- Step 6: glue the slices.
  have hms : MeasurableSet {p : ℝ × (ℝ × ℝ) | F p ≠ 0} :=
    ((Lp.stronglyMeasurable F).measurable (measurableSet_singleton (0 : ℂ))).compl
  have hnull : (radialMeasure.prod sphereMeasure) {p : ℝ × (ℝ × ℝ) | F p ≠ 0} = 0 := by
    refine Measure.measure_prod_null_of_ae_null hms ?_
    filter_upwards [hslices] with r hr
    have hr0 := ae_iff.mp hr
    simpa using hr0
  have hae0 : ⇑F =ᵐ[radialMeasure.prod sphereMeasure] 0 := by
    rw [Filter.EventuallyEq, ae_iff]
    simpa using hnull
  exact Lp.eq_zero_iff_ae_eq_zero.mpr hae0

/-- L²(ℝ³) is the Hilbert sum of the radial spaces along the sector
    embeddings: the family is orthogonal with dense joint range. -/
theorem isHilbertSum_sectors :
    IsHilbertSum ℂ (fun _ : HarmonicIdx => RadialL2) sectorEmbedding :=
  IsHilbertSum.mk orthogonalFamily_sectorEmbedding sectorEmbedding_dense

/-- **The spherical decomposition.**

    The unitary isomorphism L²(ℝ³) ≅ ⊕_ℓ (RadialL2 ⊗ V_ℓ) induced by
    spherical coordinates, with the right-hand side realized as the Hilbert
    sum `lp (fun _ : HarmonicIdx => RadialL2) 2` (each (2ℓ+1)-dimensional
    sector V_ℓ expanded in its orthonormal basis {Y_ℓ^m}).

    Every f ∈ L²(ℝ³) decomposes as
      f(r, θ, φ) = Σ_{ℓ=0}^∞ Σ_{m=-ℓ}^{ℓ} R_{ℓm}(r) Y_ℓ^m(θ, φ)
    with R_{ℓm} ∈ RadialL2 and convergence in L²(ℝ³); see
    `sphericalDecomposition_symm_apply` and
    `sphericalDecomposition_symm_single` for the inverse direction making
    this exact. -/
noncomputable def sphericalDecomposition :
    l2R3 ≃ₗᵢ[ℂ] lp (fun _ : HarmonicIdx => RadialL2) 2 :=
  isHilbertSum_sectors.linearIsometryEquiv

/-- The decomposition preserves norms (unitarity). -/
theorem sphericalDecomposition_isometry (f : l2R3) :
    ‖sphericalDecomposition f‖ = ‖f‖ :=
  sphericalDecomposition.norm_map f

/-- The inverse decomposition: a square-summable family of radial functions
    is reassembled as the L²-convergent sum Σ_i R_i ⊗ Y_i. -/
theorem sphericalDecomposition_symm_apply
    (w : lp (fun _ : HarmonicIdx => RadialL2) 2) :
    sphericalDecomposition.symm w = ∑' i, sectorEmbedding i (w i) :=
  isHilbertSum_sectors.linearIsometryEquiv_symm_apply w

/-- A single radial function in the (ℓ, m)-component is reassembled as the
    pure tensor R ⊗ Y_ℓ^m. -/
theorem sphericalDecomposition_symm_single (i : HarmonicIdx) (R : RadialL2) :
    sphericalDecomposition.symm (lp.single 2 i R) = sectorEmbedding i R :=
  isHilbertSum_sectors.linearIsometryEquiv_symm_apply_single R


/-! ## Interface summary

Exports consumed downstream (see `Spectrum/Eigenvalue.lean`, where the reduced
radial operator `reducedRadialOp` and its eigenvalues are built):

- `RadialL2`, `ReducedRadialL2` — the radial Hilbert spaces
- `radialReduction` — the R ↦ rR unitary
- `sphericalDecomposition` — the L²(ℝ³) ≃ ⊕_ℓ RadialL2 ⊗ V_ℓ unitary

-/


end Spectra.QuantumMechanics.Hydrogen.Decomposition
