/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Laplacian.FreeGreens.Fourier
import Spectra.SpectralTheory.YoungConvolution
import Mathlib.Analysis.Fourier.Convolution

/-!
# The `L²` convolution theorem and the resolvent-kernel identity for `G̃_z`

Mathlib has no `L²`-level convolution–Fourier theorem (only Schwartz–Schwartz and
integrable+continuous). This file builds the case needed — `L² ⋆ Schwartz` — by **density on the
`L²` factor**, leaning on the already-proved Young inequality
`Spectra.CompactOperator.young_L1_conv_L2`, and uses it to identify the Fourier-defined free
Green's function `G̃_z` (`freeGreensFunctionL2`) as the integral kernel of the free resolvent — with
**no sphere integral**.

## Main statements

* **S1** `fourier_conv_schwartz_L2` — `𝓕(φ ⋆ χ) =ᵐ 𝓕φ · 𝓕χ` for `φ, χ` Schwartz, bridged to the
  `L²`-Fourier transform `fourierL2` via `SchwartzMap.toLp_fourier_eq`.
* **S2** `fourier_conv_L2_schwartz` — the `L²`-level convolution–Fourier identity: for `g ∈ L²`
  and `χ` Schwartz, `fourierL2 (g ⋆ χ) =ᵐ (fourierL2 g) · 𝓕χ`, proved by density on the `L²`
  factor.
* **S3** `freeGreens_resolvent_kernel_schwartz` — the resolvent-kernel identity: on Schwartz data
  the free resolvent `R_z` acts as convolution by the Fourier-defined Green's function `G̃_z`
  (`freeGreensFunctionL2`), with **no sphere integral**.

Supporting layers:
* `young_R3` — Young's `L¹ ⋆ L² → L²` inequality over `R3`'s default `volume`, obtained from the
  banked `young_L1_conv_L2` by bridging the two `MeasurableSpace` instances on `R3` (`hms`,
  `memLp_borel_invariant`, `ms_default_eq_withLp`, and companions).
* `memLp_conv_L2_schwartz` — `g ∈ L²`, `χ` Schwartz `⟹ g ⋆ χ ∈ L²`; `conv_comm_mul` — convolution
  against the multiplication form commutes.
* density helpers — `memLp_bdd_mul` (multiplication by an `L^∞` symbol is bounded on `L²`),
  `conv_sub_left` (convolution is subtractive in the left slot), `exists_schwartz_seq_tendsto`
  (`L²`-density of Schwartz functions), and the two convergences `conv_seqA_tendsto` /
  `fourier_conv_seqB_tendsto` powering the density argument for S2.
* Fourier-of-Schwartz helpers — `fourier_schwartz_coe`, `fourier_chi_bound`, `fourier_chi_meas`
  (`𝓕χ` is the coercion of a Schwartz function, hence uniformly bounded and measurable).
-/

open MeasureTheory Spectra.Sobolev Spectra.CompactOperator
open scoped Convolution NNReal ENNReal Topology
open FourierTransform SchwartzMap Filter
open Spectra.Resolvent Spectra.Essential Spectra.QuantumMechanics.SpectralTheory

namespace Spectra.QuantumMechanics.Hydrogen

/-! ## S1: Schwartz × Schwartz convolution–Fourier identity -/

/-- Pointwise Schwartz × Schwartz convolution–Fourier identity: `𝓕(φ ⋆ χ) x = 𝓕φ x · 𝓕χ x`
for `φ, χ` Schwartz, in terms of the classical Fourier transform `𝓕`. -/
theorem fourier_conv_schwartz_pointwise (φ χ : 𝓢(R3, ℂ)) (x : R3) :
    𝓕 ((φ : R3 → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (χ : R3 → ℂ)) x
      = 𝓕 (φ : R3 → ℂ) x * 𝓕 (χ : R3 → ℂ) x := by
  have h1 := SchwartzMap.fourier_convolution_apply (ContinuousLinearMap.mul ℂ ℂ) φ χ x
  rw [SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply] at h1
  rw [← h1, ContinuousLinearMap.mul_apply', SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]

/-- The convolution `φ ⋆ χ` of two Schwartz functions is in `L²`. -/
theorem memLp_schwartz_conv (φ χ : 𝓢(R3, ℂ)) :
    MemLp ((φ : R3 → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (χ : R3 → ℂ)) 2 volume := by
  have heq : ((φ : R3 → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (χ : R3 → ℂ))
      = (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) φ χ : R3 → ℂ) := by
    funext x
    exact (SchwartzMap.convolution_apply (ContinuousLinearMap.mul ℂ ℂ) φ χ x).symm
  rw [heq]
  exact (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) φ χ).memLp 2 volume

/-- **S1.** The Schwartz × Schwartz convolution–Fourier identity, bridged to the `L²`-Fourier
transform `fourierL2`. -/
theorem fourier_conv_schwartz_L2 (φ χ : 𝓢(R3, ℂ)) :
    (fourierL2 ((memLp_schwartz_conv φ χ).toLp _) : R3 → ℂ)
      =ᵐ[volume] fun x => 𝓕 (φ : R3 → ℂ) x * 𝓕 (χ : R3 → ℂ) x := by
  set conv : 𝓢(R3, ℂ) := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) φ χ with _hconv
  have hcoe : (conv : R3 → ℂ)
      = ((φ : R3 → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (χ : R3 → ℂ)) := by
    funext x; exact SchwartzMap.convolution_apply (ContinuousLinearMap.mul ℂ ℂ) φ χ x
  have htoLp : (memLp_schwartz_conv φ χ).toLp _ = conv.toLp 2 := by
    apply MemLp.toLp_congr; rw [hcoe]
  rw [htoLp]
  have hbridge : fourierL2 (conv.toLp 2) = (𝓕 conv).toLp 2 :=
    SchwartzMap.toLp_fourier_eq conv
  rw [hbridge]
  filter_upwards [(𝓕 conv).coeFn_toLp 2 volume] with x hx
  rw [hx, SchwartzMap.fourier_coe, hcoe, fourier_conv_schwartz_pointwise]

/-! ## Helpers: bounded-multiplier `L²` continuity; convolution linearity; Schwartz density -/

/-- Multiplication by an `L∞` (uniformly bounded) function is bounded on `L²`. -/
theorem memLp_bdd_mul {m f : R3 → ℂ} {C : ℝ≥0}
    (hm : ∀ᵐ x ∂volume, ‖m x‖₊ ≤ C) (hmmeas : AEStronglyMeasurable m volume)
    (hf : MemLp f 2 volume) :
    MemLp (fun x => m x * f x) 2 volume ∧
      eLpNorm (fun x => m x * f x) 2 volume ≤ C • eLpNorm f 2 volume := by
  have hbound : ∀ᵐ x ∂volume, ‖m x * f x‖₊ ≤ C * ‖f x‖₊ := by
    filter_upwards [hm] with x hx
    rw [nnnorm_mul]; gcongr
  exact ⟨MemLp.of_nnnorm_le_mul hf (hmmeas.mul hf.aestronglyMeasurable) hbound,
    eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul hbound 2⟩

/-- Integrability of `t ↦ h(t) * χ(x − t)`. -/
theorem integrable_mul_schwartz_shift (h : R3 → ℂ) (hh : MemLp h 2 volume) (χ : 𝓢(R3, ℂ)) (x : R3) :
    Integrable (fun t => h t * (χ : R3 → ℂ) (x - t)) volume := by
  have hχ : MemLp (χ : R3 → ℂ) 2 volume := χ.memLp 2 volume
  have hχx : MemLp (fun t => (χ : R3 → ℂ) (x - t)) 2 volume :=
    hχ.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)
  exact hh.integrable_mul hχx

/-- Convolution is linear (subtractive) in the left slot, pointwise. -/
theorem conv_sub_left {h₁ h₂ : R3 → ℂ} (hh₁ : MemLp h₁ 2 volume) (hh₂ : MemLp h₂ 2 volume)
    (χ : 𝓢(R3, ℂ)) (x : R3) :
    ((h₁ - h₂) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (χ : R3 → ℂ)) x
      = (h₁ ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (χ : R3 → ℂ)) x
        - (h₂ ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (χ : R3 → ℂ)) x := by
  simp only [convolution_mul]
  rw [← integral_sub (integrable_mul_schwartz_shift h₁ hh₁ χ x)
        (integrable_mul_schwartz_shift h₂ hh₂ χ x)]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Pi.sub_apply]; ring

/-- Schwartz functions are `L²`-dense: every `g ∈ L²` is the limit of a Schwartz sequence. -/
theorem exists_schwartz_seq_tendsto (g : l2R3) :
    ∃ φ : ℕ → 𝓢(R3, ℂ), Tendsto (fun n => (φ n).toLp (2 : ℝ≥0∞)) atTop (𝓝 g) := by
  have hdense : DenseRange (SchwartzMap.toLpCLM ℂ ℂ (2 : ℝ≥0∞) (volume : Measure R3)) :=
    SchwartzMap.denseRange_toLpCLM (by norm_num)
  have hmem : g ∈ closure (Set.range (SchwartzMap.toLpCLM ℂ ℂ (2 : ℝ≥0∞) (volume : Measure R3))) :=
    hdense g
  rw [mem_closure_iff_seq_limit] at hmem
  obtain ⟨u, hu_range, hu_tendsto⟩ := hmem
  choose φ hφ using hu_range
  refine ⟨φ, ?_⟩
  have : (fun n => (φ n).toLp (2 : ℝ≥0∞)) = u := by funext n; rw [← hφ n]; rfl
  rw [this]; exact hu_tendsto

/-! ## Instance bridging: `R3`'s `borel` measurable space vs `EuclideanSpace`'s `WithLp` one.

`Spectra.Spaces.Sobolev.WeakDerivative` registers a *custom* `MeasurableSpace R3 := borel R3`
instance, propositionally (but not definitionally) equal to the canonical `WithLp.measurableSpace`
that the banked `young_L1_conv_L2` (stated over `EuclideanSpace ℝ (Fin 3)`) carries. The lemmas
below shuttle `MemLp`/`MeasureSpace` facts across the two. -/

/-- The two `MeasurableSpace` instances on `R3` agree: both are the Borel σ-algebra. -/
theorem hms : ((Spectra.Sobolev.instMeasurableSpaceRn 3) : MeasurableSpace R3)
    = (WithLp.measurableSpace 2 ((i : Fin 3) → ℝ)
        : MeasurableSpace (EuclideanSpace ℝ (Fin 3))) := by
  have h2 : (WithLp.measurableSpace 2 ((i : Fin 3) → ℝ)
        : MeasurableSpace (EuclideanSpace ℝ (Fin 3))) = borel (EuclideanSpace ℝ (Fin 3)) :=
    @BorelSpace.measurable_eq (EuclideanSpace ℝ (Fin 3)) _ (WithLp.measurableSpace 2 _) _
  rw [show ((Spectra.Sobolev.instMeasurableSpaceRn 3) : MeasurableSpace R3) = borel R3 from rfl, h2]

/-- `R3` is a `BorelSpace` for the `WithLp` measurable space too. -/
instance instBorelWithLp : @BorelSpace R3 _ (WithLp.measurableSpace 2 ((i : Fin 3) → ℝ)) := by
  rw [← hms]; infer_instance

/-- The default (`borel`) and the `WithLp` `MeasureSpace` structures on `R3` coincide. -/
theorem ms_default_eq_withLp :
    (measureSpaceOfInnerProductSpace : MeasureSpace R3) =
    (@measureSpaceOfInnerProductSpace (EuclideanSpace ℝ (Fin 3)) _ _ _
      (WithLp.measurableSpace 2 ((i : Fin 3) → ℝ)) instBorelWithLp) := by
  congr 1
  · exact hms
  · exact proof_irrel_heq _ _

/-- Measurable-space-level version of `ms_default_eq_withLp`. -/
theorem ms_tomeas_default_eq_withLp :
    (measureSpaceOfInnerProductSpace : MeasureSpace R3).toMeasurableSpace =
    (@measureSpaceOfInnerProductSpace (EuclideanSpace ℝ (Fin 3)) _ _ _
      (WithLp.measurableSpace 2 ((i : Fin 3) → ℝ)) instBorelWithLp).toMeasurableSpace := by
  rw [ms_default_eq_withLp]

/-- Heterogeneous equality of the two `volume`s on `R3`. -/
theorem volume_default_heq_withLp :
    (@MeasureTheory.volume _ (measureSpaceOfInnerProductSpace : MeasureSpace R3)) ≍
    (@MeasureTheory.volume _ (@measureSpaceOfInnerProductSpace (EuclideanSpace ℝ (Fin 3)) _ _ _
      (WithLp.measurableSpace 2 ((i : Fin 3) → ℝ)) instBorelWithLp)) := by
  rw [ms_default_eq_withLp]

/-- `MemLp` of a fixed function is invariant under the choice of `BorelSpace` measurable-space
instance on `R3` (with the corresponding `volume`); all such instances give the Borel/Lebesgue
measure. The workhorse for moving `MemLp` in and out of `young_L1_conv_L2`. -/
theorem memLp_borel_invariant (f : R3 → ℂ) (p : ℝ≥0∞)
    (m₁ : MeasurableSpace R3) (bs₁ : @BorelSpace R3 _ m₁)
    (m₂ : MeasurableSpace R3) (bs₂ : @BorelSpace R3 _ m₂)
    (h : @MemLp R3 ℂ m₁ _ _ f p
      (@MeasureTheory.volume _ (@measureSpaceOfInnerProductSpace R3 _ _ _ m₁ bs₁))) :
    @MemLp R3 ℂ m₂ _ _ f p
      (@MeasureTheory.volume _ (@measureSpaceOfInnerProductSpace R3 _ _ _ m₂ bs₂)) := by
  have e1 : m₁ = borel R3 := @BorelSpace.measurable_eq R3 _ m₁ bs₁
  have e2 : m₂ = borel R3 := @BorelSpace.measurable_eq R3 _ m₂ bs₂
  subst e1; subst e2; exact h

/-- **Young `L¹ ⋆ L² → L²` over `R3`'s default `volume`** (both the `MemLp` and the norm estimate),
obtained from the banked `young_L1_conv_L2` by bridging the measurable-space instances. -/
theorem young_R3 {a b : R3 → ℂ} (ha : MemLp a 1 volume) (hb : MemLp b 2 volume) :
    MemLp (a ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] b) 2 volume ∧
    eLpNorm (a ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] b) 2 volume
      ≤ eLpNorm a 1 volume * eLpNorm b 2 volume := by
  have fa := memLp_borel_invariant a 1 _ (Spectra.Sobolev.instBorelSpaceRn 3) _ instBorelWithLp ha
  have fb := memLp_borel_invariant b 2 _ (Spectra.Sobolev.instBorelSpaceRn 3) _ instBorelWithLp hb
  have y := young_L1_conv_L2 (f := a) (g := b) fa fb
  refine ⟨?_, ?_⟩
  · have := memLp_borel_invariant _ 2 _ instBorelWithLp _ (Spectra.Sobolev.instBorelSpaceRn 3) y.1
    convert this using 3 <;> exact ms_default_eq_withLp
  · have hb2 := y.2
    convert hb2 using 3 <;>
      first
      | exact ms_default_eq_withLp
      | exact ms_tomeas_default_eq_withLp
      | exact volume_default_heq_withLp

/-! ## Convolution commutativity for the multiplication form -/

/-- Convolution against the multiplication bilinear form commutes, pointwise. -/
theorem conv_comm_mul (a b : R3 → ℂ) (x : R3) :
    (a ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] b) x
      = (b ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] a) x := by
  rw [convolution_mul, convolution_mul_swap]
  apply integral_congr_ae
  filter_upwards with t
  rw [mul_comm]

/-! ## Companion: `g ⋆ χ ∈ L²` for `g ∈ L²`, `χ` Schwartz -/

/-- **Companion.** `g ∈ L²` and `χ` Schwartz imply `g ⋆ χ ∈ L²`. Proof: `χ ∈ L¹ ∩ L²`, Young's
`L¹ ⋆ L² → L²` gives `χ ⋆ g ∈ L²`, and convolution commutativity rewrites it to `g ⋆ χ`. -/
theorem memLp_conv_L2_schwartz (g : l2R3) (χ : 𝓢(R3, ℂ)) :
    MemLp ((g : R3 → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (χ : R3 → ℂ)) 2 volume := by
  have y := (young_R3 (a := (χ : R3 → ℂ)) (b := (g : R3 → ℂ)) (χ.memLp 1 volume) (Lp.memLp g)).1
  have hcomm : ((χ : R3 → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (g : R3 → ℂ))
      = ((g : R3 → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (χ : R3 → ℂ)) := by
    funext x; exact conv_comm_mul _ _ x
  rwa [hcomm] at y

/-! ## Fourier-of-Schwartz helpers: `𝓕χ` is bounded and measurable -/

/-- `𝓕 (χ : R3 → ℂ)` is the coercion of a Schwartz function. -/
theorem fourier_schwartz_coe (χ : 𝓢(R3, ℂ)) :
    𝓕 (χ : R3 → ℂ) = ((SchwartzMap.fourierTransformCLM ℂ χ : 𝓢(R3, ℂ)) : R3 → ℂ) := by
  rw [← SchwartzMap.fourier_coe, SchwartzMap.fourierTransformCLM_apply]

/-- `𝓕χ` is uniformly bounded by the `0,0`-seminorm of its (Schwartz) Fourier transform. -/
theorem fourier_chi_bound (χ : 𝓢(R3, ℂ)) :
    ∀ᵐ x ∂volume, ‖𝓕 (χ : R3 → ℂ) x‖₊
      ≤ (SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.fourierTransformCLM ℂ χ)).toNNReal := by
  filter_upwards with x
  rw [fourier_schwartz_coe, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
  have := (SchwartzMap.fourierTransformCLM ℂ χ).le_seminorm ℝ 0 0 x
  simpa using this

/-- `𝓕χ` is a.e.-strongly measurable. -/
theorem fourier_chi_meas (χ : 𝓢(R3, ℂ)) : AEStronglyMeasurable (𝓕 (χ : R3 → ℂ)) volume := by
  rw [fourier_schwartz_coe]
  exact (SchwartzMap.fourierTransformCLM ℂ χ).continuous.aestronglyMeasurable

/-- The target of S2 is in `L²`: `fourierL2 g · 𝓕χ ∈ L²` (`fourierL2 g ∈ L²`, `𝓕χ ∈ L^∞`). -/
theorem memLp_fourierL2_mul_chi (g : l2R3) (χ : 𝓢(R3, ℂ)) :
    MemLp (fun ξ => (fourierL2 g : R3 → ℂ) ξ * 𝓕 (χ : R3 → ℂ) ξ) 2 volume := by
  have hfg : MemLp (fourierL2 g : R3 → ℂ) 2 volume := Lp.memLp _
  have hmul := (memLp_bdd_mul (m := 𝓕 (χ:R3→ℂ)) (f := (fourierL2 g : R3 → ℂ))
    (C := (SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.fourierTransformCLM ℂ χ)).toNNReal)
    (fourier_chi_bound χ) (fourier_chi_meas χ) hfg).1
  refine hmul.ae_eq ?_; filter_upwards with x; rw [mul_comm]

/-- `fourierL2 (φ.toLp 2) =ᵐ 𝓕 (φ : R3 → ℂ)` for a Schwartz `φ`. -/
theorem fourierL2_toLp_ae (φ : 𝓢(R3, ℂ)) :
    (fourierL2 (φ.toLp 2) : R3 → ℂ) =ᵐ[volume] 𝓕 (φ : R3 → ℂ) := by
  have hb : fourierL2 (φ.toLp 2) = (𝓕 φ).toLp 2 := SchwartzMap.toLp_fourier_eq φ
  rw [hb]
  filter_upwards [(𝓕 φ).coeFn_toLp 2 volume] with x hx
  rw [hx, SchwartzMap.fourier_coe]

/-! ## The two convergences powering the density argument -/
/-- Per-index estimate for `Fₙ → B`: the `L²` distance between `fourierL2 (φ ⋆ χ).toLp` and the
`L²` symbol `(fourierL2 g · 𝓕χ).toLp` is bounded by
`‖𝓕χ‖_∞ · ‖fourierL2 (φ.toLp) − fourierL2 g‖`. -/
theorem fourier_conv_seqB_bound (g : l2R3) (χ : 𝓢(R3, ℂ)) (φ : 𝓢(R3, ℂ))
    (memB : MemLp (fun ξ => (fourierL2 g : R3 → ℂ) ξ * 𝓕 (χ : R3 → ℂ) ξ) 2 volume) :
    eLpNorm (⇑(fourierL2 ((memLp_schwartz_conv φ χ).toLp _)) - ⇑(memB.toLp _)) 2 volume
      ≤ ((SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.fourierTransformCLM ℂ χ)).toNNReal : ℝ≥0∞)
        * eLpNorm (⇑(fourierL2 (φ.toLp 2)) - ⇑(fourierL2 g)) 2 volume := by
  set C := (SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.fourierTransformCLM ℂ χ)).toNNReal with _hC
  set fdiff : R3 → ℂ := ⇑(fourierL2 (φ.toLp 2)) - ⇑(fourierL2 g) with hfdiff
  have hFn := fourier_conv_schwartz_L2 φ χ
  have hB := memB.coeFn_toLp
  have hmemdiff : MemLp fdiff 2 volume := (Lp.memLp _).sub (Lp.memLp _)
  have hb := (memLp_bdd_mul (m := 𝓕 (χ:R3→ℂ))
    (f := fdiff) (C := C)
    (fourier_chi_bound χ) (fourier_chi_meas χ) hmemdiff).2
  rw [ENNReal.smul_def, smul_eq_mul] at hb
  have hdiff : (⇑(fourierL2 ((memLp_schwartz_conv φ χ).toLp _)) - ⇑(memB.toLp _))
      =ᵐ[volume] fun ξ => 𝓕 (χ:R3→ℂ) ξ * fdiff ξ := by
    filter_upwards [hFn, hB, fourierL2_toLp_ae φ, Lp.coeFn_sub (fourierL2 (φ.toLp 2)) (fourierL2 g)]
      with ξ h1 h2 h3 h4
    rw [Pi.sub_apply] at h4
    simp only [Pi.sub_apply, h1, h2, h3, hfdiff]
    ring
  rw [eLpNorm_congr_ae hdiff]
  exact hb

/-- **`Fₙ → B`.** `fourierL2 (φₙ ⋆ χ).toLp → (fourierL2 g · 𝓕χ).toLp` in `L²`, from the per-index
estimate and `L²`-continuity of `fourierL2`. -/
theorem fourier_conv_seqB_tendsto (g : l2R3) (χ : 𝓢(R3, ℂ)) (φ : ℕ → 𝓢(R3, ℂ))
    (memB : MemLp (fun ξ => (fourierL2 g : R3 → ℂ) ξ * 𝓕 (χ : R3 → ℂ) ξ) 2 volume)
    (hφ : Tendsto (fun n => (φ n).toLp (2 : ℝ≥0∞)) atTop (𝓝 g)) :
    Tendsto (fun n => fourierL2 ((memLp_schwartz_conv (φ n) χ).toLp _)) atTop
      (𝓝 (memB.toLp _)) := by
  have hcont : Tendsto (fun n => fourierL2 ((φ n).toLp 2)) atTop (𝓝 (fourierL2 g)) :=
    (fourierL2.continuous.tendsto g).comp hφ
  have hL2 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun n => fourierL2 ((φ n).toLp 2))
    (fourierL2 g)).mp hcont
  have hC : ((SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.fourierTransformCLM ℂ χ)).toNNReal : ℝ≥0∞)
      ≠ ∞ := ENNReal.coe_ne_top
  have hRHS := ENNReal.Tendsto.const_mul hL2 (Or.inr hC)
  rw [mul_zero] at hRHS
  have heLp : Tendsto (fun n => eLpNorm (⇑(fourierL2 ((memLp_schwartz_conv (φ n) χ).toLp _))
      - ⇑(memB.toLp _)) 2 volume) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hRHS (fun n => bot_le)
      (fun n => fourier_conv_seqB_bound g χ (φ n) memB)
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr heLp

/-- **`seqₙ → A`.** `(φₙ ⋆ χ).toLp → (g ⋆ χ).toLp` in `L²`, by Young's estimate
`‖(φₙ − g) ⋆ χ‖₂ = ‖χ ⋆ (φₙ − g)‖₂ ≤ ‖χ‖₁ · ‖φₙ − g‖₂` and `L²`-density of `φₙ`. -/
theorem conv_seqA_tendsto (g : l2R3) (χ : 𝓢(R3, ℂ)) (φ : ℕ → 𝓢(R3, ℂ))
    (hφ : Tendsto (fun n => (φ n).toLp (2 : ℝ≥0∞)) atTop (𝓝 g)) :
    Tendsto (fun n => (memLp_schwartz_conv (φ n) χ).toLp _) atTop
      (𝓝 ((memLp_conv_L2_schwartz g χ).toLp _)) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => ((φ n : R3 → ℂ)
        ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (χ : R3 → ℂ)))
        (fun n => memLp_schwartz_conv (φ n) χ) _ (memLp_conv_L2_schwartz g χ)]
  have hbound : ∀ n, eLpNorm (((φ n : R3 → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (χ:R3→ℂ))
        - ((g:R3→ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (χ:R3→ℂ))) 2 volume
      ≤ eLpNorm (χ:R3→ℂ) 1 volume * eLpNorm ((φ n : R3 → ℂ) - (g:R3→ℂ)) 2 volume := by
    intro n
    have hφn : MemLp ((φ n : R3 → ℂ)) 2 volume := (φ n).memLp 2 volume
    have hg : MemLp ((g:R3→ℂ)) 2 volume := Lp.memLp g
    have heq : (((φ n : R3 → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (χ:R3→ℂ))
        - ((g:R3→ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (χ:R3→ℂ)))
        = (((φ n : R3 → ℂ) - (g:R3→ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (χ:R3→ℂ)) := by
      funext x; rw [Pi.sub_apply, conv_sub_left hφn hg χ x]
    rw [heq]
    have hcomm : (((φ n : R3 → ℂ) - (g:R3→ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (χ:R3→ℂ))
        = ((χ:R3→ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] ((φ n : R3 → ℂ) - (g:R3→ℂ))) := by
      funext x; exact conv_comm_mul _ _ x
    rw [hcomm]
    exact (young_R3 (a := (χ:R3→ℂ)) (b := (φ n : R3 → ℂ) - (g:R3→ℂ))
      (χ.memLp 1 volume) (hφn.sub hg)).2
  have hL2 : Tendsto (fun n => eLpNorm ((φ n : R3 → ℂ) - (g:R3→ℂ)) 2 volume) atTop (𝓝 0) := by
    have h1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun n => (φ n).toLp (2:ℝ≥0∞)) g).mp hφ
    refine h1.congr (fun n => ?_)
    apply eLpNorm_congr_ae
    filter_upwards [(φ n).coeFn_toLp 2 volume] with x hx
    rw [Pi.sub_apply, Pi.sub_apply, hx]
  have hχ1 : eLpNorm (χ:R3→ℂ) 1 volume ≠ ∞ := (χ.memLp 1 volume).eLpNorm_ne_top
  have hRHS := ENNReal.Tendsto.const_mul hL2 (Or.inr hχ1)
  rw [mul_zero] at hRHS
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hRHS (fun n => bot_le) hbound

/-! ## S2: the `L²` convolution–Fourier identity -/

/-- **S2.** For `g ∈ L²` and `χ` Schwartz, the `L²`-Fourier transform of `g ⋆ χ` is the pointwise
product `(fourierL2 g) · 𝓕χ`. Proved by density on `g`: a Schwartz sequence `φₙ → g` makes
`Fₙ := fourierL2 (φₙ ⋆ χ).toLp` converge to both `fourierL2 ((g ⋆ χ).toLp)` and
`(fourierL2 g · 𝓕χ).toLp`; uniqueness of limits identifies the two. -/
theorem fourier_conv_L2_schwartz (g : l2R3) (χ : 𝓢(R3, ℂ)) :
    (fourierL2 ((memLp_conv_L2_schwartz g χ).toLp _) : R3 → ℂ)
      =ᵐ[volume] fun ξ => (fourierL2 g : R3 → ℂ) ξ * 𝓕 (χ : R3 → ℂ) ξ := by
  obtain ⟨φ, hφ⟩ := exists_schwartz_seq_tendsto g
  have hFA : Tendsto (fun n => fourierL2 ((memLp_schwartz_conv (φ n) χ).toLp _)) atTop
      (𝓝 (fourierL2 ((memLp_conv_L2_schwartz g χ).toLp _))) :=
    (fourierL2.continuous.tendsto _).comp (conv_seqA_tendsto g χ φ hφ)
  have hFB := fourier_conv_seqB_tendsto g χ φ (memLp_fourierL2_mul_chi g χ) hφ
  have hAB : fourierL2 ((memLp_conv_L2_schwartz g χ).toLp _)
      = (memLp_fourierL2_mul_chi g χ).toLp _ := tendsto_nhds_unique hFA hFB
  rw [hAB]
  exact (memLp_fourierL2_mul_chi g χ).coeFn_toLp

/-! ## S3: the resolvent-kernel identity for Schwartz data -/

/-- **S3.** The resolvent-kernel identity for a Schwartz `ψ`: the free resolvent `R_z (ψ.toLp)`
acts as convolution by the Fourier-defined Green's function `G̃_z`. Assembled from S2
(`fourier_conv_L2_schwartz`), B0 (`fourierL2_freeGreensFunctionL2`), the operator half
(`fourierL2_selfAdjointResolvent`), and injectivity of `fourierL2`; the pointwise convolution form
is `convolution_mul_swap`. -/
theorem freeGreens_resolvent_kernel_schwartz (z : ℂ) (hz : z.im ≠ 0) (ψ : 𝓢(R3, ℂ)) :
    ∀ᵐ x : R3,
      (selfAdjointResolvent laplacian_isSelfAdjoint z hz (ψ.toLp 2) : R3 → ℂ) x
        = ∫ y, (freeGreensFunctionL2 z hz : R3 → ℂ) (x - y) * (ψ : R3 → ℂ) y := by
  set gconv : l2R3 := (memLp_conv_L2_schwartz (freeGreensFunctionL2 z hz) ψ).toLp _ with hgconv
  have hconv_m : (fourierL2 gconv : R3 → ℂ)
        =ᵐ[volume] fun ξ => ((laplacianSymbol ξ : ℂ) - z)⁻¹ * 𝓕 (ψ : R3 → ℂ) ξ := by
    filter_upwards [fourier_conv_L2_schwartz (freeGreensFunctionL2 z hz) ψ,
      fourierL2_freeGreensFunctionL2 z hz] with ξ h1 h2
    rw [h1, h2]
  have hres_m : (fourierL2 (selfAdjointResolvent laplacian_isSelfAdjoint z hz (ψ.toLp 2)) : R3 → ℂ)
      =ᵐ[volume] fun ξ => ((laplacianSymbol ξ : ℂ) - z)⁻¹ * 𝓕 (ψ : R3 → ℂ) ξ := by
    filter_upwards [fourierL2_selfAdjointResolvent z hz (ψ.toLp 2), fourierL2_toLp_ae ψ]
      with ξ h1 h2
    rw [h1, h2]
  have hR_conv : selfAdjointResolvent laplacian_isSelfAdjoint z hz (ψ.toLp 2) = gconv :=
    fourierL2.injective (Lp.ext (hres_m.trans hconv_m.symm))
  rw [hR_conv]
  filter_upwards [hgconv ▸ (memLp_conv_L2_schwartz (freeGreensFunctionL2 z hz) ψ).coeFn_toLp]
    with x hx
  rw [hx, convolution_mul_swap]

end Spectra.QuantumMechanics.Hydrogen
