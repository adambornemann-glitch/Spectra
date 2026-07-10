/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Spectrum.RadialEigenfunction.Defs

/-!
# The Cartesian `s`-state eigenfunction — Green's identity, `L²` membership, and the bound state

This file completes the **reverse direction** (`E = E_n ⟹ eigenpair exists`) of
`hydrogen_discrete_spectrum` at general charge `Z` (and its `Z = 1` specialization) for the
`ℓ = 0` (spherically symmetric) bound states, building on the cutoff integration-by-parts
machinery of `RadialEigenfunction.Defs` (`chi`, `master_ibp`).

## Main statements

* `memLp_two_of_le_exp`/`memLp_two_of_le_exp_add_div` — `L²`-membership criteria for radial
  profiles bounded by an exponentially decaying envelope, upgrading the classical derivative
  bounds (`memLp_first_deriv`, `memLp_second_deriv`) to genuine `MemLp` facts.
* `hasWeakDerivative_radial_first`/`_second` — the weak first/second derivatives of a radial
  `L²` element, identified a.e. with the classical ones via `master_ibp`.
* `bound_state_of_radial_profile` — the abstract bound state: given a `C²` radial profile with
  exponentially decaying derivatives satisfying the eigen-identity, its Cartesian realization
  is a nonzero `MemSobolevH2` eigenvector.
* `hydrogen_bound_state`/`hydrogen_bound_state_Z1` — instantiating the abstraction at the
  Coulomb profile, completing the reverse direction consumed by `Discrete.lean`.
-/

noncomputable section

namespace QuantumMechanics.Hydrogen.Spectrum

open MeasureTheory Real InnerProductSpace Laplacian Complex Filter
open Spectra.Sobolev Spectra.SphericalHarmonics
open RadialEq Spectra.QuantumMechanics.Hydrogen Spectra.QuantumMechanics.Hydrogen.Decomposition
open scoped ContDiff Topology SchwartzMap

/-! ## The per-direction Green's identity

Applying `master_ibp` twice (to `f = g∘‖·‖` then to `∂ⱼf`) gives the per-direction identity
`∫ f·∂ⱼ∂ⱼφ = ∫ ∂ⱼ∂ⱼf·φ`, the building block of the full Laplacian Green's identity. -/

/-- `g∘‖·‖` is `C¹` (in fact `C²`) away from the origin. -/
private lemma radial_contDiffOn (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) :
    ContDiffOn ℝ 1 (fun y : R3 => g ‖y‖) {(0 : R3)}ᶜ :=
  fun x hx => ((contDiffAt_radial g hg hx).of_le (by norm_num)).contDiffWithinAt

/-- The classical partial `∂ⱼ(g∘‖·‖)` is `C¹` away from the origin. -/
lemma first_deriv_contDiffOn (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) (j : Fin 3) :
    ContDiffOn ℝ 1 (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single j 1))
      {(0 : R3)}ᶜ := by
  intro x hx
  have hdf1 : ContDiffAt ℝ 1 (fun y : R3 => fderiv ℝ (fun z => g ‖z‖) y
      (EuclideanSpace.single j 1)) x :=
    ((contDiffAt_radial g hg hx).fderiv_right (m := 1) (by norm_num)).clm_apply
      (contDiffAt_const (c := (EuclideanSpace.single j (1 : ℝ))))
  exact hdf1.contDiffWithinAt

/-- **Integrability of the first-derivative term against `∂ⱼφ`.**
    `(∂ⱼ(g∘‖·‖))·(∂ⱼφ)` is integrable: `∂ⱼ(g∘‖·‖)` is bounded near the origin and `∂ⱼφ` has
    compact support. -/
private lemma integrable_first_deriv_mul (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) (j : Fin 3)
    {φ : R3 → ℂ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x => fderiv ℝ (fun z => g ‖z‖) x (EuclideanSpace.single j 1)
      * fderiv ℝ φ x (EuclideanSpace.single j 1)) := by
  have hdφ_smooth : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y (EuclideanSpace.single j 1)) :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdφ_cs : HasCompactSupport (fun y => fderiv ℝ φ y (EuclideanSpace.single j 1)) :=
    hφc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
  obtain ⟨R, hR_pos, hR⟩ := hdφ_cs.isCompact.isBounded.exists_pos_norm_lt
  have hdg_cont : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  obtain ⟨a', -, hMg'max⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := R)).exists_isMaxOn
    (Set.nonempty_Icc.mpr hR_pos.le) hdg_cont.norm.continuousOn
  obtain ⟨Mφ, hMφ⟩ := hdφ_cs.exists_bound_of_continuous hdφ_smooth.continuous
  set Mg' : ℝ := ‖deriv g a'‖ with _hMg'def
  have hMg' : ∀ r ∈ Set.Icc (0 : ℝ) R, ‖deriv g r‖ ≤ Mg' := isMaxOn_iff.mp hMg'max
  have hMφ0 : 0 ≤ Mφ := (norm_nonneg _).trans (hMφ 0)
  set C : ℝ := Mg' * Mφ with _hC
  have hae : ∀ᵐ x : R3, x ∈ ({(0 : R3)}ᶜ : Set R3) := ae_ne_zero_R3
  have hbound : ∀ᵐ x : R3, ‖fderiv ℝ (fun z => g ‖z‖) x (EuclideanSpace.single j 1)
      * fderiv ℝ φ x (EuclideanSpace.single j 1)‖ ≤ C * ‖x‖ ^ (-(0 : ℝ)) := by
    filter_upwards [hae] with x hx
    have hx' : x ≠ 0 := hx
    rw [neg_zero, Real.rpow_zero, mul_one, norm_mul]
    rcases le_total ‖x‖ R with hxR | hxR
    · have hb1 : ‖fderiv ℝ (fun z => g ‖z‖) x (EuclideanSpace.single j 1)‖ ≤ Mg' :=
        (norm_fderiv_radial_le g hx'
          ((hg.differentiable (by norm_num)).differentiableAt.hasDerivAt) j).trans
          (hMg' ‖x‖ ⟨norm_nonneg x, hxR⟩)
      exact mul_le_mul hb1 (hMφ x) (norm_nonneg _) ((norm_nonneg _).trans hb1)
    · have hφ0 : fderiv ℝ φ x (EuclideanSpace.single j 1) = 0 :=
        image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ φ y (EuclideanSpace.single j 1))
          (mt (hR x) (not_lt.mpr hxR))
      rw [hφ0, norm_zero, mul_zero]
      positivity
  have hmeas : AEStronglyMeasurable (fun x =>
      fderiv ℝ (fun z => g ‖z‖) x (EuclideanSpace.single j 1)
      * fderiv ℝ φ x (EuclideanSpace.single j 1)) volume := by
    have hcont : ContinuousOn (fun x => fderiv ℝ (fun z => g ‖z‖) x (EuclideanSpace.single j 1)
        * fderiv ℝ φ x (EuclideanSpace.single j 1)) {(0 : R3)}ᶜ :=
      (first_deriv_contDiffOn g hg j).continuousOn.mul (hdφ_smooth.continuous.continuousOn)
    have := hcont.aestronglyMeasurable (μ := volume) (measurableSet_singleton (0 : R3)).compl
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at this
  have hLI : LocallyIntegrable (fun x => fderiv ℝ (fun z => g ‖z‖) x (EuclideanSpace.single j 1)
      * fderiv ℝ φ x (EuclideanSpace.single j 1)) volume :=
    locallyIntegrable_of_norm_le_rpow (E := R3) (by rw [finrank_euclideanSpace_fin]; norm_num)
      (by rw [finrank_euclideanSpace_fin]; norm_num) hbound hmeas
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport _)).mp
    (hLI.integrableOn_isCompact (hdφ_cs.mul_left (f := fun x =>
      fderiv ℝ (fun z => g ‖z‖) x (EuclideanSpace.single j 1))))

/-- The mixed classical second derivative `∂ⱼ∂ᵢ(g∘‖·‖)` is continuous away from the origin. -/
private lemma second_deriv_continuousOn' (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) (i j : Fin 3) :
    ContinuousOn (fun x => fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1)) {(0 : R3)}ᶜ := by
  intro x hx
  have hx' : x ≠ 0 := hx
  have hf2 : ContDiffAt ℝ 2 (fun z : R3 => g ‖z‖) x := contDiffAt_radial g hg hx'
  have hdf1 : ContDiffAt ℝ 1 (fun y : R3 => fderiv ℝ (fun z => g ‖z‖) y
      (EuclideanSpace.single i 1)) x :=
    (hf2.fderiv_right (m := 1) (by norm_num)).clm_apply
      (contDiffAt_const (c := (EuclideanSpace.single i (1 : ℝ))))
  have hcaf : ContinuousAt (fderiv ℝ (fun y : R3 => fderiv ℝ (fun z => g ‖z‖) y
      (EuclideanSpace.single i 1))) x := hdf1.continuousAt_fderiv one_ne_zero
  have hcomp : ContinuousAt (fun x => fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1)) x :=
    ((ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single j (1 : ℝ))).continuous.continuousAt).comp
      hcaf
  exact hcomp.continuousWithinAt

/-- **Mixed** second-derivative integrability: `(∂ⱼ∂ᵢ(g∘‖·‖))·φ` is integrable for compactly
    supported `φ` (the `1/‖x‖` singularity at the origin is `L¹_loc` in `ℝ³`). -/
private lemma integrable_second_deriv_mul' (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) (i j : Fin 3)
    {φ : R3 → ℂ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x => fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) * φ x) := by
  obtain ⟨R, hR_pos, hR⟩ := hφc.isCompact.isBounded.exists_pos_norm_lt
  have hdg_cont : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have hddg_cont : Continuous (deriv (deriv g)) :=
    (hg.deriv' (n := 1)).continuous_deriv (by norm_num)
  obtain ⟨a', -, hMg'max⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := R)).exists_isMaxOn
    (Set.nonempty_Icc.mpr hR_pos.le) hdg_cont.norm.continuousOn
  obtain ⟨a'', -, hMg''max⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := R)).exists_isMaxOn
    (Set.nonempty_Icc.mpr hR_pos.le) hddg_cont.norm.continuousOn
  obtain ⟨Mφ, hMφ⟩ := hφc.exists_bound_of_continuous hφ.continuous
  set Mg' : ℝ := ‖deriv g a'‖ with _hMg'def
  set Mg'' : ℝ := ‖deriv (deriv g) a''‖ with _hMg''def
  have hMg' : ∀ r ∈ Set.Icc (0 : ℝ) R, ‖deriv g r‖ ≤ Mg' := isMaxOn_iff.mp hMg'max
  have hMg'' : ∀ r ∈ Set.Icc (0 : ℝ) R, ‖deriv (deriv g) r‖ ≤ Mg'' := isMaxOn_iff.mp hMg''max
  have _hMg'0 : 0 ≤ Mg' := norm_nonneg _
  have _hMg''0 : 0 ≤ Mg'' := norm_nonneg _
  have hMφ0 : 0 ≤ Mφ := (norm_nonneg _).trans (hMφ 0)
  set C : ℝ := (Mg'' * R + 2 * Mg') * Mφ with _hC
  have hae : ∀ᵐ x : R3, x ∈ ({(0 : R3)}ᶜ : Set R3) := ae_ne_zero_R3
  have hbound : ∀ᵐ x : R3, ‖fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) * φ x‖
      ≤ C * ‖x‖ ^ (-(1 : ℝ)) := by
    filter_upwards [hae] with x hx
    have hx' : x ≠ 0 := hx
    rw [Real.rpow_neg_one]
    rcases le_total ‖x‖ R with hxR | hxR
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx'
      have hbd : ‖fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1)‖ ≤ Mg'' + 2 * Mg' / ‖x‖ := by
        have h0 : ‖fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single j 1)‖
            ≤ ‖fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single i 1)) x‖ := by
          calc ‖fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single i 1)) x
                (EuclideanSpace.single j 1)‖
              ≤ ‖fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single i 1)) x‖
                * ‖(EuclideanSpace.single j (1 : ℝ) : R3)‖ := ContinuousLinearMap.le_opNorm _ _
            _ = ‖fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single i 1)) x‖ :=
                by rw [PiLp.norm_single, norm_one, mul_one]
        have h1 := norm_fderiv_fderiv_radial_le g hg hx' i
        have h2 : ‖deriv (deriv g) ‖x‖‖ ≤ Mg'' := hMg'' ‖x‖ ⟨norm_nonneg x, hxR⟩
        have h3 : ‖deriv g ‖x‖‖ ≤ Mg' := hMg' ‖x‖ ⟨norm_nonneg x, hxR⟩
        calc _ ≤ ‖fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single i 1)) x‖ :=
              h0
          _ ≤ ‖deriv (deriv g) ‖x‖‖ + 2 * ‖deriv g ‖x‖‖ / ‖x‖ := h1
          _ ≤ Mg'' + 2 * Mg' / ‖x‖ := by gcongr
      rw [norm_mul, ← div_eq_mul_inv, le_div_iff₀ hxpos]
      have hphi : ‖φ x‖ ≤ Mφ := hMφ x
      have h1 : ‖fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1)‖ * ‖x‖ ≤ Mg'' * ‖x‖ + 2 * Mg' := by
        calc _ ≤ (Mg'' + 2 * Mg' / ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right hbd (norm_nonneg x)
          _ = Mg'' * ‖x‖ + 2 * Mg' := by field_simp
      calc ‖fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single j 1)‖ * ‖φ x‖ * ‖x‖
          = (‖fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single i 1)) x
              (EuclideanSpace.single j 1)‖ * ‖x‖) * ‖φ x‖ := by ring
        _ ≤ (Mg'' * ‖x‖ + 2 * Mg') * Mφ := mul_le_mul h1 hphi (norm_nonneg _) (by positivity)
        _ ≤ (Mg'' * R + 2 * Mg') * Mφ := by gcongr
    · have hφ0 : φ x = 0 :=
        image_eq_zero_of_notMem_tsupport (mt (hR x) (not_lt.mpr hxR))
      rw [hφ0, mul_zero, norm_zero]
      positivity
  have hmeas : AEStronglyMeasurable (fun x => fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) * φ x) volume := by
    have hcont : ContinuousOn (fun x => fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) * φ x) {(0 : R3)}ᶜ :=
      (second_deriv_continuousOn' g hg i j).mul hφ.continuous.continuousOn
    have := hcont.aestronglyMeasurable (μ := volume) (measurableSet_singleton (0 : R3)).compl
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at this
  have hLI : LocallyIntegrable (fun x => fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) * φ x) volume :=
    locallyIntegrable_of_norm_le_rpow (E := R3) (by rw [finrank_euclideanSpace_fin]; norm_num)
      (by rw [finrank_euclideanSpace_fin]; norm_num) hbound hmeas
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport _)).mp
    (hLI.integrableOn_isCompact hφc.mul_left)

/-- **Per-direction Green's identity for a radial `C²` function.**
    `∫ (g∘‖·‖)·∂ⱼ∂ⱼφ = ∫ (∂ⱼ∂ⱼ(g∘‖·‖))·φ`, via two cutoff integrations by parts. -/
private lemma radial_green_identity_dir (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) (j : Fin 3)
    {φ : R3 → ℂ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ x, g ‖x‖ * fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single j 1)
      = ∫ x, fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single j 1) * φ x := by
  -- the test functions `∂ⱼφ` and `∂ⱼ∂ⱼφ`
  have hdφ_smooth : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y (EuclideanSpace.single j 1)) :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdφ_cs : HasCompactSupport (fun y => fderiv ℝ φ y (EuclideanSpace.single j 1)) :=
    hφc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
  have hdjjφ_cont : Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ φ y
      (EuclideanSpace.single j 1)) x (EuclideanSpace.single j 1)) :=
    (hdφ_smooth.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hdjjφ_cs : HasCompactSupport (fun x => fderiv ℝ (fun y => fderiv ℝ φ y
      (EuclideanSpace.single j 1)) x (EuclideanSpace.single j 1)) :=
    hdφ_cs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
  -- first IBP: `∫ f·∂ⱼ∂ⱼφ = −∫ ∂ⱼf·∂ⱼφ`
  obtain ⟨b, -, hbmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn
    (Set.nonempty_Icc.mpr zero_le_one) (hg.continuous.norm.continuousOn)
  have firstIBP : (∫ x, g ‖x‖ * fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single j 1))
      = - ∫ x, fderiv ℝ (fun z => g ‖z‖) x (EuclideanSpace.single j 1)
          * fderiv ℝ φ x (EuclideanSpace.single j 1) :=
    master_ibp j (hg.continuous.comp continuous_norm).continuousOn (radial_contDiffOn g hg)
      (fun x _ => rfl) one_pos
      (fun x hx => isMaxOn_iff.mp hbmax ‖x‖ ⟨norm_nonneg x, hx⟩) (norm_nonneg _)
      hdφ_smooth hdφ_cs
      ((hg.continuous.comp continuous_norm).mul hdjjφ_cont |>.integrable_of_hasCompactSupport
        hdjjφ_cs.mul_left)
      (integrable_first_deriv_mul g hg j hφ hφc)
  -- second IBP: `∫ ∂ⱼf·∂ⱼφ = −∫ ∂ⱼ∂ⱼf·φ`
  obtain ⟨b', -, hb'max⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn
    (Set.nonempty_Icc.mpr zero_le_one) (hg.continuous_deriv (by norm_num)).norm.continuousOn
  have hMv_df : ∀ x : R3, ‖x‖ ≤ 1 →
      ‖fderiv ℝ (fun z => g ‖z‖) x (EuclideanSpace.single j 1)‖
        ≤ max ‖deriv g b'‖ ‖fderiv ℝ (fun z => g ‖z‖) (0 : R3) (EuclideanSpace.single j 1)‖ := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact le_max_right _ _
    · calc ‖fderiv ℝ (fun z => g ‖z‖) x (EuclideanSpace.single j 1)‖
          ≤ ‖deriv g ‖x‖‖ := norm_fderiv_radial_le g hx0
            ((hg.differentiable (by norm_num)).differentiableAt.hasDerivAt) j
        _ ≤ ‖deriv g b'‖ := isMaxOn_iff.mp hb'max ‖x‖ ⟨norm_nonneg x, hx⟩
        _ ≤ _ := le_max_left _ _
  have secondIBP : (∫ x, fderiv ℝ (fun z => g ‖z‖) x (EuclideanSpace.single j 1)
        * fderiv ℝ φ x (EuclideanSpace.single j 1))
      = - ∫ x, fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single j 1) * φ x :=
    master_ibp j (first_deriv_contDiffOn g hg j).continuousOn (first_deriv_contDiffOn g hg j)
      (fun x _ => rfl) one_pos hMv_df (le_trans (norm_nonneg _) (le_max_right _ _)) hφ hφc
      (integrable_first_deriv_mul g hg j hφ hφc) (integrable_second_deriv_mul' g hg j j hφ hφc)
  rw [firstIBP, secondIBP, neg_neg]

/-! ## The full radial Laplacian and the summed Green's identity

Summing the per-direction identity over the three axes, and identifying `∑ⱼ ∂ⱼ∂ⱼ(g∘‖·‖)` with the
classical radial Laplacian `g″ + (2/r)g′` (Mathlib `Δ` via `laplacian_comp_norm`). -/

/-- Chain-rule bridge: `∂ᵥ(∂ᵥf) = (D²f)(v,v)` when `fderiv f` is differentiable at `x`. -/
private lemma fderiv_fderiv_apply_eq (f : R3 → ℂ) (v : R3) {x : R3}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x v = fderiv ℝ (fderiv ℝ f) x v v := by
  have h : HasFDerivAt (fun y => fderiv ℝ f y v)
      ((ContinuousLinearMap.apply ℝ ℂ v).comp (fderiv ℝ (fderiv ℝ f) x)) x := by
    have h0 := (ContinuousLinearMap.apply ℝ ℂ v).hasFDerivAt.comp x hf.hasFDerivAt
    simpa [ContinuousLinearMap.apply_apply, Function.comp_def] using h0
  rw [h.fderiv]
  simp [ContinuousLinearMap.apply_apply]

/-- **Classical radial Laplacian as a sum of second partials.**  For a `C²` profile `g`, off the
    origin `∑ⱼ ∂ⱼ∂ⱼ(g∘‖·‖) = g″(‖x‖) + (2/‖x‖)·g′(‖x‖)` (the radial Laplacian). -/
private lemma radial_laplacian_sum (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) {x : R3} (hx : x ≠ 0) :
    ∑ j : Fin 3, fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single j 1)
      = iteratedDeriv 2 g ‖x‖ + (2 / (‖x‖ : ℂ)) * deriv g ‖x‖ := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ (fun z : R3 => g ‖z‖)) x :=
    ((contDiffAt_radial g hg hx).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hΔ : Δ (fun y : R3 => g ‖y‖) x
      = ∑ j : Fin 3, iteratedFDeriv ℝ 2 (fun y => g ‖y‖) x
          ![EuclideanSpace.single j 1, EuclideanSpace.single j 1] := by
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (fun y => g ‖y‖)
      (EuclideanSpace.basisFun (Fin 3) ℝ)]
    simp [EuclideanSpace.basisFun_apply]
  rw [← laplacian_comp_norm g hg hx, hΔ]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact fderiv_fderiv_apply_eq (fun z => g ‖z‖) (EuclideanSpace.single j 1) hfd

/-- **Summed Green's identity.**  `∑ⱼ ∫ f·∂ⱼ∂ⱼφ = ∫ (∑ⱼ ∂ⱼ∂ⱼf)·φ` — sums the per-direction
    identity, ready to be paired with the distributional Laplacian. -/
private lemma radial_green_identity_sum (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g)
    {φ : R3 → ℂ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∑ j : Fin 3, ∫ x, g ‖x‖ * fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single j 1))
      = ∫ x, (∑ j : Fin 3, fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y
          (EuclideanSpace.single j 1)) x (EuclideanSpace.single j 1)) * φ x := by
  rw [Finset.sum_congr rfl
    (fun j (_ : j ∈ Finset.univ) => radial_green_identity_dir g hg j hφ hφc),
    ← integral_finsetSum Finset.univ (fun j _ => integrable_second_deriv_mul' g hg j j hφ hφc)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp only [Finset.sum_mul]

/-! ## The distributional Laplacian, tested against Schwartz functions

`Δ(toTD Ψ) φ = ∫ (∑ⱼ ∂ⱼ∂ⱼφ)·Ψ` (Mathlib `laplacian_apply_apply` + the `Δ = ∑ⱼ ∂ⱼ∂ⱼ` decomposition).
This pairs the distributional side with the classical summed Green's identity. -/

/-- The (Mathlib) Laplacian as a sum of second directional derivatives, for any function whose
    `fderiv` is differentiable at `x`. -/
lemma laplacian_eq_sum_fderiv (h : R3 → ℂ) {x : R3} (hh : DifferentiableAt ℝ (fderiv ℝ h) x) :
    Δ h x = ∑ j : Fin 3, fderiv ℝ (fun y => fderiv ℝ h y (EuclideanSpace.single j 1)) x
      (EuclideanSpace.single j 1) := by
  have hΔ : Δ h x = ∑ j : Fin 3, iteratedFDeriv ℝ 2 h x
      ![EuclideanSpace.single j 1, EuclideanSpace.single j 1] := by
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis h (EuclideanSpace.basisFun (Fin 3) ℝ)]
    simp [EuclideanSpace.basisFun_apply]
  rw [hΔ]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact (fderiv_fderiv_apply_eq h (EuclideanSpace.single j 1) hh).symm

/-- **The distributional Laplacian of `toTD Ψ`, tested against `φ`.**
    `Δ(toTD Ψ) φ = ∫ (∑ⱼ ∂ⱼ∂ⱼφ)·Ψ`.  Pairs with the classical summed Green's identity. -/
private lemma laplacian_toTD_apply (Ψ : Spectra.Sobolev.l2R3) (φ : 𝓢(R3, ℂ)) :
    Laplacian.laplacian (Lp.toTemperedDistribution Ψ) φ
      = ∫ x, (∑ j : Fin 3, fderiv ℝ (fun y => fderiv ℝ (φ : R3 → ℂ) y (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single j 1)) * Ψ x := by
  rw [TemperedDistribution.laplacian_apply_apply, Lp.toTemperedDistribution_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp only [smul_eq_mul]
  congr 1
  rw [SchwartzMap.laplacian_apply]
  exact laplacian_eq_sum_fderiv (φ : R3 → ℂ)
    (((φ.smooth 2).contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)

/-! ## `L²`-membership of the singular radial terms

The Coulomb term `(g∘‖·‖)/r` and hence the classical Laplacian `Δf = −2(E+1/r)f` are `L²`. -/

/-- **A radial `L²` profile divided by `r` is `L²`.**  If `g` is continuous and `g∘‖·‖ ∈ L²(ℝ³)`,
    then `(g∘‖·‖)/‖·‖ ∈ L²`: the `1/r` singularity at the origin is `L²` in `ℝ³` (`2 < 3`), and
    away from the origin `‖(g∘‖·‖)/r‖ ≤ ‖g∘‖·‖‖`. -/
private lemma memLp_radial_div_norm (g : ℝ → ℂ) (hg : Continuous g)
    (hL2 : MemLp (fun x : R3 => g ‖x‖) 2 volume) :
    MemLp (fun x : R3 => g ‖x‖ / (‖x‖ : ℂ)) 2 volume := by
  have hh_cont : Continuous (fun x : R3 => g ‖x‖) := hg.comp continuous_norm
  have hq_meas' : Measurable (fun x : R3 => g ‖x‖ / (‖x‖ : ℂ)) :=
    hh_cont.measurable.div ((Complex.continuous_ofReal.comp continuous_norm).measurable)
  have hae : ∀ᵐ x : R3, x ≠ 0 := ae_ne_zero_R3
  rw [memLp_two_iff_integrable_sq_norm hq_meas'.aestronglyMeasurable]
  have hsq_h : Integrable (fun x : R3 => ‖g ‖x‖‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).mp hL2
  have hnorm : ∀ x : R3, ‖g ‖x‖ / (‖x‖ : ℂ)‖ ^ 2 = ‖g ‖x‖‖ ^ 2 / ‖x‖ ^ 2 := by
    intro x
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x), div_pow]
  rw [← integrableOn_univ, ← Set.union_compl_self (Metric.ball (0 : R3) 1)]
  apply IntegrableOn.union
  · -- near the origin: `≤ ‖g ‖b‖‖²·‖x‖^(-2)`, integrable since `2 < 3`
    obtain ⟨b, -, hbmax⟩ := (isCompact_closedBall (0 : R3) 1).exists_isMaxOn
      ⟨0, Metric.mem_closedBall_self zero_le_one⟩ hh_cont.norm.continuousOn
    apply integrableOn_ball_of_norm_le_rpow (E := R3) (C := ‖g ‖b‖‖ ^ 2) (α := 2)
      (by rw [finrank_euclideanSpace_fin]; norm_num)
      (by rw [finrank_euclideanSpace_fin]; norm_num) ?_
      (hq_meas'.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_ball] with x hx0 hxmem
    have _hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hrp : ‖x‖ ^ (-(2 : ℝ)) = (‖x‖ ^ 2)⁻¹ := by
      rw [Real.rpow_neg (norm_nonneg x), ← Real.rpow_natCast ‖x‖ 2]; norm_num
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hnorm, hrp, div_eq_mul_inv]
    gcongr
    exact hbmax (Metric.ball_subset_closedBall hxmem)
  · -- away from the origin: dominated by `‖g∘‖·‖‖²`
    refine (hsq_h.integrableOn (s := (Metric.ball (0 : R3) 1)ᶜ)).mono'
      ((hq_meas'.norm.pow_const 2).aestronglyMeasurable.restrict)
      ((ae_restrict_iff' measurableSet_ball.compl).mpr
        (Filter.Eventually.of_forall (fun x hx => ?_)))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hnorm]
    rw [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] at hx
    have _hxpos : (0 : ℝ) < ‖x‖ := lt_of_lt_of_le one_pos hx
    rw [div_le_iff₀ (by positivity)]
    have hx2 : (1 : ℝ) ≤ ‖x‖ ^ 2 := by nlinarith [hx]
    nlinarith [sq_nonneg ‖g ‖x‖‖, hx2]

/-! ## The classical Laplacian of the witness as an `L²` element

From the radial eigen-equation, `∑ⱼ ∂ⱼ∂ⱼf = −2(E+1/r)·f` off the origin, an `L²` function (`f ∈ L²`
and `f/r ∈ L²`).  This is the candidate for the distributional Laplacian `Lf`. -/

/-- **The summed second derivative equals `−2(E + 1/r)·f` off the origin** (the eigen-equation
    form of the classical Laplacian of the `s`-state witness `f = c·R_{n0}(‖·‖)`). -/
lemma sum_second_deriv_eigen (n : ℕ) (hn : 0 + 1 ≤ n) {x : R3} (hx : x ≠ 0) :
    ∑ j : Fin 3, fderiv ℝ (fun y => fderiv ℝ
        (fun z => (sphericalNorm 0 0 : ℂ) * Rc n 0 hn ‖z‖) y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single j 1)
      = (-2 : ℂ) * ((hydrogenEigenvalue n (by omega) : ℂ) + (‖x‖ : ℂ)⁻¹)
          * ((sphericalNorm 0 0 : ℂ) * Rc n 0 hn ‖x‖) := by
  set c : ℂ := (sphericalNorm 0 0 : ℂ) with _hc
  have hRc2 : ContDiff ℝ 2 (fun r => c * Rc n 0 hn r) := contDiff_const.mul (contDiff_Rc n 0 hn)
  have hfd : DifferentiableAt ℝ (fderiv ℝ (fun z : R3 => c * Rc n 0 hn ‖z‖)) x :=
    ((contDiffAt_radial _ hRc2 hx).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [← laplacian_eq_sum_fderiv (fun z : R3 => c * Rc n 0 hn ‖z‖) hfd]
  have hsmul : Δ (fun z : R3 => c * Rc n 0 hn ‖z‖) x
      = c * Δ (fun y : R3 => Rc n 0 hn ‖y‖) x := by
    rw [show (fun z : R3 => c * Rc n 0 hn ‖z‖) = c • (fun y : R3 => Rc n 0 hn ‖y‖) from rfl,
      laplacian_smul (𝕜 := ℂ) c (contDiffAt_radial _ (contDiff_Rc n 0 hn) hx), smul_eq_mul]
  rw [hsmul]
  have heig := classical_radial_eigen n hn hx
  have hrne : (‖x‖ : ℂ) ≠ 0 := by
    simpa using (Complex.ofReal_ne_zero.mpr (ne_of_gt (norm_pos_iff.mpr hx)))
  field_simp at heig ⊢
  linear_combination (-c) * heig

/-- **The classical Laplacian `Δf = −2(E+1/r)f` of the `s`-state witness is `L²`.** -/
private lemma memLp_classical_laplacian (n : ℕ) (hn : 0 + 1 ≤ n) (hm : |(0 : ℤ)| ≤ 0) :
    MemLp (fun x : R3 => (-2 : ℂ) * ((hydrogenEigenvalue n (by omega) : ℂ) + (‖x‖ : ℂ)⁻¹)
        * ((sphericalNorm 0 0 : ℂ) * Rc n 0 hn ‖x‖)) 2 volume := by
  set c : ℂ := (sphericalNorm 0 0 : ℂ) with _hc
  set E : ℂ := (hydrogenEigenvalue n (by omega) : ℂ) with _hE
  have hf_L2 : MemLp (fun x : R3 => c * Rc n 0 hn ‖x‖) 2 volume :=
    (Lp.memLp (chartRealization.symm (hydrogenEigenfunction n 0 0 hn hm))).ae_eq
      (chartRealization_symm_eigenfunction_coeFn n hn hm)
  have hfr_L2 : MemLp (fun x : R3 => (c * Rc n 0 hn ‖x‖) / (‖x‖ : ℂ)) 2 volume :=
    memLp_radial_div_norm (fun r => c * Rc n 0 hn r)
      (continuous_const.mul (contDiff_Rc n 0 hn).continuous) hf_L2
  have hrw : (fun x : R3 => (-2 : ℂ) * (E + (‖x‖ : ℂ)⁻¹) * (c * Rc n 0 hn ‖x‖))
      = fun x : R3 => (-2 * E) * (c * Rc n 0 hn ‖x‖)
          + (-2) * ((c * Rc n 0 hn ‖x‖) / (‖x‖ : ℂ)) := by
    funext x; rw [div_eq_mul_inv]; ring
  rw [hrw]
  exact (hf_L2.const_mul _).add (hfr_L2.const_mul _)

/-- A continuous function whose product with `exp(a·r)` tends to `0` at `+∞` is bounded by
    `C·exp(−a·r)` on `[0,∞)`. -/
lemma exp_bound_of_tendsto {h : ℝ → ℝ} (hcont : Continuous h) {a : ℝ}
    (htend : Tendsto (fun r => h r * Real.exp (a * r)) atTop (𝓝 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → |h r| ≤ C * Real.exp (-a * r) := by
  -- `g r = h r · exp(a r)` is continuous and `→ 0`, hence bounded
  have hev : ∀ᶠ r in atTop, |h r * Real.exp (a * r)| ≤ 1 := by
    have := htend.eventually (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)
    simpa [Real.dist_eq, Real.norm_eq_abs] using this
  obtain ⟨T, hT⟩ := eventually_atTop.mp hev
  obtain ⟨b, -, hbmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := max T 0)).exists_isMaxOn
    (Set.nonempty_Icc.mpr (le_max_right _ _))
    (hcont.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).norm.continuousOn
  set C : ℝ := max (|h b * Real.exp (a * b)|) 1 with _hC
  refine ⟨C, le_trans zero_le_one (le_max_right _ _), fun r hr => ?_⟩
  have hgb : |h r * Real.exp (a * r)| ≤ C := by
    rcases le_total r (max T 0) with hrT | hrT
    · exact le_trans (isMaxOn_iff.mp hbmax r ⟨hr, hrT⟩) (le_max_left _ _)
    · exact le_trans (hT r (le_trans (le_max_left _ _) hrT)) (le_max_right _ _)
  rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)] at hgb
  -- |h r| · exp(a r) ≤ C  ⟹  |h r| ≤ C · exp(-a r)
  rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
  exact hgb

/-! ## Exp-decay bounds give `L²` membership

The reusable tool for the regularity packaging: a function bounded by `C·exp(−a‖·‖)` is `L²`.
(`exp(−a‖·‖) ∈ L²` via the radial reduction `integrable_fun_norm_addHaar` +
`integrableOn_rpow_mul_exp_neg_mul_rpow`.) -/

/-- `exp(−a‖·‖) ∈ L²(ℝ³)` for `a > 0`. -/
private lemma memLp_exp_neg_norm {a : ℝ} (ha : 0 < a) :
    MemLp (fun x : R3 => Real.exp (-a * ‖x‖)) 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm (by fun_prop)]
  have hsq : (fun x : R3 => ‖Real.exp (-a * ‖x‖)‖ ^ 2)
      = fun x : R3 => Real.exp (-(2 * a) * ‖x‖) := by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), pow_two, ← Real.exp_add]
    congr 1; ring
  rw [hsq, integrable_fun_norm_addHaar volume (f := fun y => Real.exp (-(2 * a) * y))]
  have hib := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 2) (b := 2 * a)
    (by norm_num) (le_refl 1) (by linarith)
  refine hib.congr_fun (fun y hy => ?_) measurableSet_Ioi
  have _hy0 : (0 : ℝ) < y := hy
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]
  rw [Real.rpow_one, ← Real.rpow_natCast y 2]
  norm_num

/-- **An exp-decay-bounded function is `L²`.**  If `h` is a.e.-strongly-measurable and
    `‖h x‖ ≤ C·exp(−a‖x‖)` with `a > 0`, then `h ∈ L²(ℝ³)`. -/
lemma memLp_two_of_le_exp {h : R3 → ℂ} (hmeas : AEStronglyMeasurable h volume)
    {C a : ℝ} (ha : 0 < a) (hbd : ∀ x : R3, ‖h x‖ ≤ C * Real.exp (-a * ‖x‖)) :
    MemLp h 2 volume := by
  refine MemLp.of_le_mul (c := 1) ((memLp_exp_neg_norm ha).const_mul C) hmeas
    (Filter.Eventually.of_forall (fun x => ?_))
  rw [one_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  calc ‖h x‖ ≤ C * Real.exp (-a * ‖x‖) := hbd x
    _ ≤ |C| * Real.exp (-a * ‖x‖) := by gcongr; exact le_abs_self C

/-! ## `L²` membership of the classical first and second derivatives

The first and second classical partial derivatives of the radial witness `f = c·R_{n0}(‖·‖)`
are `L²`.  This is the engine of the weak-derivative construction (the `master_ibp` integration
by parts produces the *identity* `∫ f·∂φ = −∫ ∂f·φ`; these lemmas put the `∂f` into `L²` so it
becomes a genuine Sobolev weak derivative).  The bounds come from the exponential decay of
`R_{n0}` and its derivatives (`tendsto_*_hydrogenRadial_mul_exp`); the `1/r` singularity of the
second derivative at the origin is `L²` in `ℝ³`. -/

/-- An exp-decay-with-`1/r` bound gives `L²`.  Generalises `memLp_two_of_le_exp` to allow the
    `C'·e^{−a‖x‖}/‖x‖` term arising from the `1/r` singularity of `∂ⱼ∂ᵢf` at the origin. -/
lemma memLp_two_of_le_exp_add_div {h : R3 → ℂ} (hmeas : AEStronglyMeasurable h volume)
    {C C' a : ℝ} (ha : 0 < a)
    (hbd : ∀ x : R3, ‖h x‖ ≤ C * Real.exp (-a * ‖x‖) + C' * (Real.exp (-a * ‖x‖) / ‖x‖)) :
    MemLp h 2 volume := by
  have hexpc : MemLp (fun x : R3 => (Real.exp (-a * ‖x‖) : ℂ)) 2 volume :=
    memLp_two_of_le_exp (Continuous.aestronglyMeasurable (by fun_prop)) ha (C := 1) (fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), one_mul])
  have hdivR : MemLp (fun x : R3 => Real.exp (-a * ‖x‖) / ‖x‖) 2 volume := by
    have hℂ := memLp_radial_div_norm (fun r => (Real.exp (-a * r) : ℂ)) (by fun_prop) hexpc
    refine (hℂ.norm).ae_eq (Filter.Eventually.of_forall (fun x => ?_))
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _),
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
  have hB : MemLp (fun x : R3 => C * Real.exp (-a * ‖x‖) + C' * (Real.exp (-a * ‖x‖) / ‖x‖))
      2 volume := ((memLp_exp_neg_norm ha).const_mul C).add (hdivR.const_mul C')
  exact hB.mono' hmeas (Filter.Eventually.of_forall hbd)

/-- `∂ᵢ(g∘‖·‖)` is a.e.-strongly-measurable (continuous off the null set `{0}`). -/
private lemma aestronglyMeasurable_first_deriv (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) (i : Fin 3) :
    AEStronglyMeasurable
      (fun x : R3 => fderiv ℝ (fun y => g ‖y‖) x (EuclideanSpace.single i 1)) volume := by
  have hae : ∀ᵐ x : R3, x ∈ ({(0 : R3)}ᶜ : Set R3) := ae_ne_zero_R3
  have := (first_deriv_contDiffOn g hg i).continuousOn.aestronglyMeasurable (μ := volume)
    (measurableSet_singleton (0 : R3)).compl
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at this

/-- `∂ⱼ∂ᵢ(g∘‖·‖)` is a.e.-strongly-measurable. -/
private lemma aestronglyMeasurable_second_deriv (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) (i j : Fin 3) :
    AEStronglyMeasurable (fun x : R3 => fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1)) volume := by
  have hae : ∀ᵐ x : R3, x ∈ ({(0 : R3)}ᶜ : Set R3) := ae_ne_zero_R3
  have := (second_deriv_continuousOn' g hg i j).aestronglyMeasurable (μ := volume)
    (measurableSet_singleton (0 : R3)).compl
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at this

/-- **`∂ᵢ(g∘‖·‖) ∈ L²`** for a radial `C²` profile `g` whose derivative decays exponentially. -/
lemma memLp_first_deriv (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) {C a : ℝ} (ha : 0 < a)
    (hbd : ∀ r : ℝ, 0 ≤ r → ‖deriv g r‖ ≤ C * Real.exp (-a * r)) (i : Fin 3) :
    MemLp (fun x : R3 => fderiv ℝ (fun y => g ‖y‖) x (EuclideanSpace.single i 1)) 2 volume := by
  set D : R3 → ℂ := fun x => fderiv ℝ (fun y => g ‖y‖) x (EuclideanSpace.single i 1) with _hD
  refine memLp_two_of_le_exp (aestronglyMeasurable_first_deriv g hg i) ha
    (C := max ‖D 0‖ C) (fun x => ?_)
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [norm_zero, mul_zero, Real.exp_zero, mul_one]
    exact le_max_left _ _
  · calc ‖D x‖ ≤ ‖deriv g ‖x‖‖ :=
          norm_fderiv_radial_le g hx
            ((hg.differentiable (by norm_num)).differentiableAt.hasDerivAt) i
      _ ≤ C * Real.exp (-a * ‖x‖) := hbd ‖x‖ (norm_nonneg x)
      _ ≤ max ‖D 0‖ C * Real.exp (-a * ‖x‖) := by
          gcongr; exact le_max_right _ _

/-- **`∂ⱼ∂ᵢ(g∘‖·‖) ∈ L²`** for a radial `C²` profile `g` whose first and second derivatives
    decay exponentially.  (The `1/r` singularity at the origin is `L²` in `ℝ³`.) -/
lemma memLp_second_deriv (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) {C₁ C₂ a : ℝ} (ha : 0 < a)
    (hbd1 : ∀ r : ℝ, 0 ≤ r → ‖deriv g r‖ ≤ C₁ * Real.exp (-a * r))
    (hbd2 : ∀ r : ℝ, 0 ≤ r → ‖deriv (deriv g) r‖ ≤ C₂ * Real.exp (-a * r)) (i j : Fin 3) :
    MemLp (fun x : R3 => fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1)) 2 volume := by
  set D : R3 → ℂ := fun x => fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) with _hD
  refine memLp_two_of_le_exp_add_div (aestronglyMeasurable_second_deriv g hg i j) ha
    (C := max ‖D 0‖ C₂) (C' := 2 * C₁) (fun x => ?_)
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [norm_zero, mul_zero, Real.exp_zero, mul_one, div_zero, add_zero]
    exact le_max_left _ _
  · have _hxr : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
    have hopn : ‖D x‖ ≤ ‖deriv (deriv g) ‖x‖‖ + 2 * ‖deriv g ‖x‖‖ / ‖x‖ := by
      calc ‖D x‖
          ≤ ‖fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single i 1)) x‖
              * ‖(EuclideanSpace.single j (1 : ℝ) : R3)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single i 1)) x‖ := by
            rw [PiLp.norm_single, norm_one, mul_one]
        _ ≤ ‖deriv (deriv g) ‖x‖‖ + 2 * ‖deriv g ‖x‖‖ / ‖x‖ :=
            norm_fderiv_fderiv_radial_le g hg hx i
    have h1 : ‖deriv (deriv g) ‖x‖‖ ≤ max ‖D 0‖ C₂ * Real.exp (-a * ‖x‖) :=
      (hbd2 ‖x‖ (norm_nonneg x)).trans (by gcongr; exact le_max_right _ _)
    have h2 : 2 * ‖deriv g ‖x‖‖ / ‖x‖ ≤ 2 * C₁ * (Real.exp (-a * ‖x‖) / ‖x‖) := by
      rw [show 2 * C₁ * (Real.exp (-a * ‖x‖) / ‖x‖) = 2 * (C₁ * Real.exp (-a * ‖x‖)) / ‖x‖ from by
        ring]
      gcongr
      exact hbd1 ‖x‖ (norm_nonneg x)
    linarith [hopn, h1, h2]

/-! ## Weak derivatives of the witness (Step 3) -/

/-- `(∂ᵢ(g∘‖·‖))·ψ` is integrable for any continuous compactly-supported test `ψ`
    (`∂ᵢ(g∘‖·‖)` is bounded near the origin). -/
private lemma integrable_first_deriv_mul_test (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) (i : Fin 3)
    {ψ : R3 → ℂ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun x => fderiv ℝ (fun y => g ‖y‖) x (EuclideanSpace.single i 1) * ψ x) := by
  obtain ⟨R, hR_pos, hR⟩ := hψc.isCompact.isBounded.exists_pos_norm_lt
  have hdg_cont : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  obtain ⟨a', -, hMg'max⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := R)).exists_isMaxOn
    (Set.nonempty_Icc.mpr hR_pos.le) hdg_cont.norm.continuousOn
  obtain ⟨Mψ, hMψ⟩ := hψc.exists_bound_of_continuous hψ
  set Mg' : ℝ := ‖deriv g a'‖ with _hMg'def
  have hMg' : ∀ r ∈ Set.Icc (0 : ℝ) R, ‖deriv g r‖ ≤ Mg' := isMaxOn_iff.mp hMg'max
  have hMψ0 : 0 ≤ Mψ := (norm_nonneg _).trans (hMψ 0)
  set C : ℝ := Mg' * Mψ with _hC
  have hae : ∀ᵐ x : R3, x ∈ ({(0 : R3)}ᶜ : Set R3) := ae_ne_zero_R3
  have hbound : ∀ᵐ x : R3, ‖fderiv ℝ (fun y => g ‖y‖) x (EuclideanSpace.single i 1) * ψ x‖
      ≤ C * ‖x‖ ^ (-(0 : ℝ)) := by
    filter_upwards [hae] with x hx
    have hx' : x ≠ 0 := hx
    rw [neg_zero, Real.rpow_zero, mul_one, norm_mul]
    rcases le_total ‖x‖ R with hxR | hxR
    · have hb1 : ‖fderiv ℝ (fun y => g ‖y‖) x (EuclideanSpace.single i 1)‖ ≤ Mg' :=
        (norm_fderiv_radial_le g hx'
          ((hg.differentiable (by norm_num)).differentiableAt.hasDerivAt) i).trans
          (hMg' ‖x‖ ⟨norm_nonneg x, hxR⟩)
      exact mul_le_mul hb1 (hMψ x) (norm_nonneg _) ((norm_nonneg _).trans hb1)
    · have hψ0 : ψ x = 0 := image_eq_zero_of_notMem_tsupport (mt (hR x) (not_lt.mpr hxR))
      rw [hψ0, norm_zero, mul_zero]; positivity
  have hmeas : AEStronglyMeasurable
      (fun x => fderiv ℝ (fun y => g ‖y‖) x (EuclideanSpace.single i 1) * ψ x) volume := by
    have hcont : ContinuousOn
        (fun x => fderiv ℝ (fun y => g ‖y‖) x (EuclideanSpace.single i 1) * ψ x) {(0 : R3)}ᶜ :=
      (first_deriv_contDiffOn g hg i).continuousOn.mul hψ.continuousOn
    have := hcont.aestronglyMeasurable (μ := volume) (measurableSet_singleton (0 : R3)).compl
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at this
  have hLI : LocallyIntegrable
      (fun x => fderiv ℝ (fun y => g ‖y‖) x (EuclideanSpace.single i 1) * ψ x) volume :=
    locallyIntegrable_of_norm_le_rpow (E := R3) (by rw [finrank_euclideanSpace_fin]; norm_num)
      (by rw [finrank_euclideanSpace_fin]; norm_num) hbound hmeas
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport _)).mp
    (hLI.integrableOn_isCompact (hψc.mul_left))

/-! ## Abstract radial bound state (profile-parameterized; powers general `Z`) -/

/-- Generic first weak derivative of a radial `L²` element `Ψ =ᵐ g∘‖·‖`. -/
lemma hasWeakDerivative_radial_first (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) {C a : ℝ} (ha : 0 < a)
    (hbd : ∀ r : ℝ, 0 ≤ r → ‖deriv g r‖ ≤ C * Real.exp (-a * r))
    (Ψ : Spectra.Sobolev.l2R3) (hΨ : ⇑Ψ =ᵐ[volume] fun x : R3 => g ‖x‖) (i : Fin 3) :
    HasWeakDerivative Ψ i ((memLp_first_deriv g hg ha hbd i).toLp _) := by
  intro φ hφ hφc
  have hd1 : ⇑((memLp_first_deriv g hg ha hbd i).toLp _) =ᵐ[volume]
      fun x : R3 => fderiv ℝ (fun y => g ‖y‖) x (EuclideanSpace.single i 1) :=
    (memLp_first_deriv g hg ha hbd i).coeFn_toLp
  have hdiφ_cont : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (hφ.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hdiφ_cs : HasCompactSupport (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    hφc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  obtain ⟨b, -, hbmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn
    (Set.nonempty_Icc.mpr zero_le_one) (hg.continuous.norm.continuousOn)
  have hIBP := master_ibp i (hg.continuous.comp continuous_norm).continuousOn
    (radial_contDiffOn g hg) (fun x _ => rfl) one_pos
    (fun x hx => isMaxOn_iff.mp hbmax ‖x‖ ⟨norm_nonneg x, hx⟩) (norm_nonneg _) hφ hφc
    (((hg.continuous.comp continuous_norm).mul hdiφ_cont).integrable_of_hasCompactSupport
      hdiφ_cs.mul_left)
    (integrable_first_deriv_mul_test g hg i hφ.continuous hφc)
  calc ∫ x, Ψ x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x, g ‖x‖ * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
        refine integral_congr_ae ?_; filter_upwards [hΨ] with x hx; rw [hx]
    _ = - ∫ x, fderiv ℝ (fun y => g ‖y‖) x (EuclideanSpace.single i 1) * φ x := hIBP
    _ = - ∫ x, ((memLp_first_deriv g hg ha hbd i).toLp _) x * φ x := by
        congr 1; refine integral_congr_ae ?_; filter_upwards [hd1] with x hx; rw [hx]

/-- Generic second weak derivative of a radial `C²` profile. -/
lemma hasWeakDerivative_radial_second (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) {C₁ C₂ a : ℝ} (ha : 0 < a)
    (hbd1 : ∀ r : ℝ, 0 ≤ r → ‖deriv g r‖ ≤ C₁ * Real.exp (-a * r))
    (hbd2 : ∀ r : ℝ, 0 ≤ r → ‖deriv (deriv g) r‖ ≤ C₂ * Real.exp (-a * r)) (i j : Fin 3) :
    HasWeakDerivative ((memLp_first_deriv g hg ha hbd1 i).toLp _) j
      ((memLp_second_deriv g hg ha hbd1 hbd2 i j).toLp _) := by
  intro φ hφ hφc
  have hd1 : ⇑((memLp_first_deriv g hg ha hbd1 i).toLp _) =ᵐ[volume]
      fun x : R3 => fderiv ℝ (fun y => g ‖y‖) x (EuclideanSpace.single i 1) :=
    (memLp_first_deriv g hg ha hbd1 i).coeFn_toLp
  have hd2 : ⇑((memLp_second_deriv g hg ha hbd1 hbd2 i j).toLp _) =ᵐ[volume]
      fun x : R3 => fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1) :=
    (memLp_second_deriv g hg ha hbd1 hbd2 i j).coeFn_toLp
  have hdjφ_cont : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single j 1)) :=
    (hφ.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hdjφ_cs : HasCompactSupport (fun x => fderiv ℝ φ x (EuclideanSpace.single j 1)) :=
    hφc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
  obtain ⟨b', -, hb'max⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn
    (Set.nonempty_Icc.mpr zero_le_one) (hg.continuous_deriv (by norm_num)).norm.continuousOn
  have hMv : ∀ x : R3, ‖x‖ ≤ 1 →
      ‖fderiv ℝ (fun y => g ‖y‖) x (EuclideanSpace.single i 1)‖
        ≤ max ‖deriv g b'‖ ‖fderiv ℝ (fun y => g ‖y‖) (0 : R3) (EuclideanSpace.single i 1)‖ := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact le_max_right _ _
    · calc ‖fderiv ℝ (fun y => g ‖y‖) x (EuclideanSpace.single i 1)‖
          ≤ ‖deriv g ‖x‖‖ := norm_fderiv_radial_le g hx0
            ((hg.differentiable (by norm_num)).differentiableAt.hasDerivAt) i
        _ ≤ ‖deriv g b'‖ := isMaxOn_iff.mp hb'max ‖x‖ ⟨norm_nonneg x, hx⟩
        _ ≤ _ := le_max_left _ _
  have hIBP := master_ibp j (first_deriv_contDiffOn g hg i).continuousOn
    (first_deriv_contDiffOn g hg i) (fun x _ => rfl) one_pos hMv
    (le_trans (norm_nonneg _) (le_max_right _ _)) hφ hφc
    (integrable_first_deriv_mul_test g hg i hdjφ_cont hdjφ_cs)
    (integrable_second_deriv_mul' g hg i j hφ hφc)
  calc ∫ x, ((memLp_first_deriv g hg ha hbd1 i).toLp _) x * fderiv ℝ φ x (EuclideanSpace.single j 1)
      = ∫ x, fderiv ℝ (fun y => g ‖y‖) x (EuclideanSpace.single i 1)
          * fderiv ℝ φ x (EuclideanSpace.single j 1) := by
        refine integral_congr_ae ?_; filter_upwards [hd1] with x hx; rw [hx]
    _ = - ∫ x, fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1) * φ x := hIBP
    _ = - ∫ x, ((memLp_second_deriv g hg ha hbd1 hbd2 i j).toLp _) x * φ x := by
        congr 1; refine integral_congr_ae ?_; filter_upwards [hd2] with x hx; rw [hx]

/-- **Abstract radial bound state.**  Given a `C²` radial profile `g` with exponentially decaying
    first and second derivatives, an `L²` element `Ψ =ᵐ g∘‖·‖` that is nonzero, and the classical
    summed-second-derivative eigen-identity at charge `p.Z`, the Hamiltonian `H_p = −½Δ − Z/r` has
    `Ψ` as a genuine eigenvector with eigenvalue `E`. -/
theorem bound_state_of_radial_profile (p : CoulombParams) (E : ℝ)
    (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) {C₁ C₂ a : ℝ} (ha : 0 < a)
    (hbd1 : ∀ r : ℝ, 0 ≤ r → ‖deriv g r‖ ≤ C₁ * Real.exp (-a * r))
    (hbd2 : ∀ r : ℝ, 0 ≤ r → ‖deriv (deriv g) r‖ ≤ C₂ * Real.exp (-a * r))
    (Ψ : Spectra.Sobolev.l2R3) (hΨ : ⇑Ψ =ᵐ[volume] fun x : R3 => g ‖x‖) (hΨ0 : Ψ ≠ 0)
    (heigen : ∀ x : R3, x ≠ 0 →
      ∑ j : Fin 3, fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single j 1)
        = (-2 : ℂ) * ((E : ℂ) + (p.Z : ℂ) * (‖x‖ : ℂ)⁻¹) * g ‖x‖) :
    ∃ ψ : (hydrogenHamiltonian p).domain,
      (ψ : Spectra.Sobolev.l2R3) ≠ 0 ∧
        hydrogenHamiltonian p ψ = ((E : ℝ) : ℂ) • (ψ : Spectra.Sobolev.l2R3) := by
  set d2 : Fin 3 → Fin 3 → Spectra.Sobolev.l2R3 :=
    fun i j => (memLp_second_deriv g hg ha hbd1 hbd2 i j).toLp _ with _hd2_def
  have hH2 : MemSobolevH2 Ψ := by
    refine ⟨fun i => ⟨(memLp_first_deriv g hg ha hbd1 i).toLp _,
      hasWeakDerivative_radial_first g hg ha hbd1 Ψ hΨ i⟩, fun i j => ?_⟩
    exact ⟨d2 i j, (memLp_first_deriv g hg ha hbd1 i).toLp _,
      hasWeakDerivative_radial_first g hg ha hbd1 Ψ hΨ i,
      hasWeakDerivative_radial_second g hg ha hbd1 hbd2 i j⟩
  refine ⟨⟨Ψ, hH2⟩, hΨ0, ?_⟩
  have hchoose : ∀ i : Fin 3, (hH2.2 i i).choose = d2 i i := by
    intro i
    exact hasWeakSecondDerivative_unique Ψ i i _ _ (hH2.2 i i).choose_spec
      ⟨(memLp_first_deriv g hg ha hbd1 i).toLp _,
        hasWeakDerivative_radial_first g hg ha hbd1 Ψ hΨ i,
        hasWeakDerivative_radial_second g hg ha hbd1 hbd2 i i⟩
  have hwL : weakLaplacian Ψ hH2 = -∑ i : Fin 3, d2 i i := by
    simp only [weakLaplacian]; rw [neg_inj]; exact Finset.sum_congr rfl (fun i _ => hchoose i)
  have hwL_coeFn : ⇑(weakLaplacian Ψ hH2) =ᵐ[volume]
      fun x => -∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) := by
    have hc : ∀ i : Fin 3, ⇑(d2 i i) =ᵐ[volume]
        fun x => fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1) :=
      fun i => (memLp_second_deriv g hg ha hbd1 hbd2 i i).coeFn_toLp
    rw [hwL, Fin.sum_univ_three]
    filter_upwards [Lp.coeFn_neg (d2 0 0 + d2 1 1 + d2 2 2),
      Lp.coeFn_add (d2 0 0 + d2 1 1) (d2 2 2), Lp.coeFn_add (d2 0 0) (d2 1 1),
      hc 0, hc 1, hc 2] with x hneg hadd2 hadd1 h0 h1 h2
    simp only [Fin.sum_univ_three, hneg, Pi.neg_apply, hadd2, hadd1, Pi.add_apply, h0, h1, h2]
  refine Lp.ext ?_
  have hae0 : ∀ᵐ x : R3, x ≠ 0 := ae_ne_zero_R3
  have ehalf : ⇑(halfLaplacianPMap ⟨Ψ, hH2⟩) =ᵐ[volume]
      ((1 / 2 : ℝ) : ℂ) • ⇑(weakLaplacian Ψ hH2) := by
    rw [show halfLaplacianPMap ⟨Ψ, hH2⟩ = ((1 / 2 : ℝ) : ℂ) • weakLaplacian Ψ hH2 from by
      rw [halfLaplacianPMap_apply]; rfl]
    exact Lp.coeFn_smul _ _
  have ecoul : ⇑(coulombPotential p ⟨Ψ, hH2⟩) =ᵐ[volume]
      fun x => (coulombMultiplier p x : ℂ) * ⇑Ψ x :=
    (coulomb_mul_memLp_H2 p Ψ hH2).coeFn_toLp
  have eH : ⇑(hydrogenHamiltonian p ⟨Ψ, hH2⟩) =ᵐ[volume]
      fun x => ⇑(halfLaplacianPMap ⟨Ψ, hH2⟩) x + ⇑(coulombPotential p ⟨Ψ, hH2⟩) x := by
    rw [hydrogenHamiltonian_apply]; exact Lp.coeFn_add _ _
  filter_upwards [eH, ehalf, ecoul, hwL_coeFn, Lp.coeFn_smul ((E : ℝ) : ℂ) Ψ, hΨ, hae0]
    with x heH hehalf hecoul hwLx hsmulE hΨfx hx0
  rw [heH, hehalf, hecoul, hsmulE, Pi.smul_apply, Pi.smul_apply, hwLx, hΨfx, smul_eq_mul,
    smul_eq_mul, heigen x hx0]
  have hcoulx : (coulombMultiplier p x : ℂ) = -(p.Z : ℂ) * (‖x‖ : ℂ)⁻¹ := by
    rw [coulombMultiplier, if_neg (by simpa using (norm_pos_iff.mpr hx0).ne')]
    push_cast; ring
  have hrne : (‖x‖ : ℂ) ≠ 0 := by
    simpa using (Complex.ofReal_ne_zero.mpr (ne_of_gt (norm_pos_iff.mpr hx0)))
  rw [hcoulx]
  field_simp
  push_cast
  ring

/-! ## The hydrogen bound state at `Z = 1` (reverse direction of the discrete spectrum) -/

/-- **Reverse direction of the hydrogen discrete spectrum at general charge `Z`** (`ℓ = 0`):
    every `E_n = −Z²/(2n²)` is an eigenvalue of `H = −½Δ − Z/r`, via the dilated `s`-state. -/
theorem hydrogen_bound_state (p : CoulombParams) (n : ℕ) (hn : 1 ≤ n) :
    ∃ ψ : (hydrogenHamiltonian p).domain,
      (ψ : Spectra.Sobolev.l2R3) ≠ 0 ∧
      hydrogenHamiltonian p ψ = ((eigenvalue p n hn : ℝ) : ℂ) • (ψ : Spectra.Sobolev.l2R3) := by
  have hn' : 0 + 1 ≤ n := by omega
  have hZ : (0 : ℝ) < p.Z := p.hZ
  set Z : ℝ := p.Z with hZ_def
  set g : ℝ → ℂ := fun r => (sphericalNorm 0 0 : ℂ) * Rc n 0 hn' (Z * r) with hg_def
  have hg : ContDiff ℝ 2 g := by
    rw [hg_def]
    exact contDiff_const.mul ((contDiff_Rc n 0 hn').comp (contDiff_const.mul contDiff_id))
  have hRcd : ∀ w, HasDerivAt (Rc n 0 hn') (deriv (Rc n 0 hn') w) w :=
    fun w => ((contDiff_Rc n 0 hn').differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hRcd2 : ∀ w, HasDerivAt (deriv (Rc n 0 hn')) (deriv (deriv (Rc n 0 hn')) w) w :=
    fun w => ((contDiff_Rc n 0 hn').differentiable_deriv_two).differentiableAt.hasDerivAt
  have hlin : ∀ s : ℝ, HasDerivAt (fun t : ℝ => Z * t) Z s :=
    fun s => by simpa using (hasDerivAt_id s).const_mul Z
  have hgd : ∀ s, deriv g s = (sphericalNorm 0 0 : ℂ) * ((Z : ℂ) * deriv (Rc n 0 hn') (Z * s)) := by
    intro s
    have hsc : HasDerivAt (fun t => Rc n 0 hn' (Z * t)) (Z • deriv (Rc n 0 hn') (Z * s)) s :=
      (hRcd (Z * s)).scomp s (hlin s)
    have : deriv g s = (sphericalNorm 0 0 : ℂ) * (Z • deriv (Rc n 0 hn') (Z * s)) := by
      rw [hg_def]; exact (hsc.const_mul _).deriv
    rwa [Complex.real_smul] at this
  have hgd2 : ∀ s, deriv (deriv g) s
      = (sphericalNorm 0 0 : ℂ) * ((Z : ℂ) * ((Z : ℂ) * deriv (deriv (Rc n 0 hn')) (Z * s))) := by
    intro s
    have hderiv_g : deriv g
        = fun t => ((sphericalNorm 0 0 : ℂ) * (Z : ℂ)) * deriv (Rc n 0 hn') (Z * t) := by
      funext t; rw [hgd t]; ring
    rw [hderiv_g]
    have hsc : HasDerivAt (fun t => deriv (Rc n 0 hn') (Z * t))
        (Z • deriv (deriv (Rc n 0 hn')) (Z * s)) s :=
      (hRcd2 (Z * s)).scomp s (hlin s)
    rw [(hsc.const_mul _).deriv, Complex.real_smul]; ring
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set ε : ℝ := 1 / (2 * (n : ℝ)) with hε_def
  have hε0 : 0 < ε := by rw [hε_def]; positivity
  have hε : ε < 1 / (n : ℝ) := by rw [hε_def, div_lt_div_iff₀ (by positivity) hnR]; nlinarith
  have htop : Tendsto (fun s : ℝ => Z * s) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hZ tendsto_id
  have hdecay : ∀ (h : ℝ → ℝ), Continuous h →
      Tendsto (fun s => h s * Real.exp (ε * s)) atTop (nhds 0) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s, 0 ≤ s → |h (Z * s)| ≤ C * Real.exp (-(ε * Z) * s) := by
    intro h hcont htend
    have hcomp : Tendsto (fun s => h (Z * s) * Real.exp ((ε * Z) * s)) atTop (nhds 0) := by
      refine (htend.comp htop).congr (fun s => ?_)
      simp only [Function.comp]; rw [show ε * (Z * s) = (ε * Z) * s from by ring]
    exact exp_bound_of_tendsto (hcont.comp (continuous_const.mul continuous_id)) hcomp
  obtain ⟨Cd, _, hCd⟩ := hdecay (deriv (hydrogenRadialWavefunction n 0 hn'))
    ((contDiff_hydrogenRadial n 0 hn').continuous_deriv (by norm_num))
    (tendsto_deriv_hydrogenRadial_mul_exp n 0 hn' hε)
  obtain ⟨Cdd, _, hCdd⟩ := hdecay (deriv (deriv (hydrogenRadialWavefunction n 0 hn')))
    (((contDiff_hydrogenRadial n 0 hn').deriv' (n := 1)).continuous_deriv (by norm_num))
    (tendsto_deriv2_hydrogenRadial_mul_exp n 0 hn' hε)
  obtain ⟨CR, _, hCR⟩ := hdecay (hydrogenRadialWavefunction n 0 hn')
    (contDiff_hydrogenRadial n 0 hn').continuous (tendsto_hydrogenRadial_mul_exp n 0 hn' hε)
  have haZ : 0 < ε * Z := mul_pos hε0 hZ
  have hbd1 : ∀ s : ℝ, 0 ≤ s →
      ‖deriv g s‖ ≤ (|sphericalNorm 0 0| * (Z * Cd)) * Real.exp (-(ε * Z) * s) := by
    intro s hs
    have hns : ‖deriv g s‖
        = |sphericalNorm 0 0| * (Z * |deriv (hydrogenRadialWavefunction n 0 hn') (Z * s)|) := by
      rw [hgd s, deriv_Rc]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ]
    rw [hns]
    calc |sphericalNorm 0 0| * (Z * |deriv (hydrogenRadialWavefunction n 0 hn') (Z * s)|)
        ≤ |sphericalNorm 0 0| * (Z * (Cd * Real.exp (-(ε * Z) * s))) := by gcongr; exact hCd s hs
      _ = |sphericalNorm 0 0| * (Z * Cd) * Real.exp (-(ε * Z) * s) := by ring
  have hbd2 : ∀ s : ℝ, 0 ≤ s →
      ‖deriv (deriv g) s‖ ≤ (|sphericalNorm 0 0| * (Z * (Z * Cdd))) * Real.exp (-(ε * Z) * s) := by
    intro s hs
    have hns : ‖deriv (deriv g) s‖
        = |sphericalNorm 0 0|
          * (Z * (Z * |deriv (deriv (hydrogenRadialWavefunction n 0 hn')) (Z * s)|)) := by
      rw [hgd2 s, deriv2_Rc]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ]
    rw [hns]
    calc |sphericalNorm 0 0|
          * (Z * (Z * |deriv (deriv (hydrogenRadialWavefunction n 0 hn')) (Z * s)|))
        ≤ |sphericalNorm 0 0| * (Z * (Z * (Cdd * Real.exp (-(ε * Z) * s)))) := by
          gcongr; exact hCdd s hs
      _ = |sphericalNorm 0 0| * (Z * (Z * Cdd)) * Real.exp (-(ε * Z) * s) := by ring
  have hgnorm : ∀ x : R3, ‖g ‖x‖‖ ≤ (|sphericalNorm 0 0| * CR) * Real.exp (-(ε * Z) * ‖x‖) := by
    intro x
    have hns : ‖g ‖x‖‖ = |sphericalNorm 0 0| * |hydrogenRadialWavefunction n 0 hn' (Z * ‖x‖)| := by
      simp only [hg_def, Rc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hns]
    calc |sphericalNorm 0 0| * |hydrogenRadialWavefunction n 0 hn' (Z * ‖x‖)|
        ≤ |sphericalNorm 0 0| * (CR * Real.exp (-(ε * Z) * ‖x‖)) := by
          gcongr; exact hCR ‖x‖ (norm_nonneg x)
      _ = |sphericalNorm 0 0| * CR * Real.exp (-(ε * Z) * ‖x‖) := by ring
  have hmemΨ : MemLp (fun x : R3 => g ‖x‖) 2 volume :=
    memLp_two_of_le_exp (hg.continuous.comp continuous_norm).aestronglyMeasurable haZ hgnorm
  set Ψ : Spectra.Sobolev.l2R3 := hmemΨ.toLp _ with _hΨ_def
  have hΨ : ⇑Ψ =ᵐ[volume] fun x : R3 => g ‖x‖ := hmemΨ.coeFn_toLp
  -- nonzero
  have hΨ0 : Ψ ≠ 0 := by
    intro h0
    have hae : (fun x : R3 => g ‖x‖) =ᵐ[volume] 0 := by
      refine hΨ.symm.trans ?_; rw [h0]; exact Lp.coeFn_zero _ _ _
    have hcont : Continuous (fun x : R3 => g ‖x‖) := hg.continuous.comp continuous_norm
    have hzero : (fun x : R3 => g ‖x‖) = 0 := (hcont.ae_eq_iff_eq volume continuous_const).mp hae
    have hRz : ∀ s : ℝ, 0 < s → hydrogenRadialWavefunction n 0 hn' s = 0 := by
      intro s hs
      have hx : ‖(EuclideanSpace.single (0 : Fin 3) (s / Z) : R3)‖ = s / Z := by
        rw [PiLp.norm_single, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have h1 := congrFun hzero (EuclideanSpace.single (0 : Fin 3) (s / Z))
      rw [hg_def] at h1
      simp only [hx, Pi.zero_apply] at h1
      rw [show Z * (s / Z) = s from by field_simp, Rc] at h1
      have h2 := mul_eq_zero.mp h1
      rcases h2 with h2 | h2
      · exact absurd h2 (by simpa using (sphericalNorm_pos 0 0).ne')
      · exact_mod_cast h2
    have hint : (∫ r in Set.Ioi 0, hydrogenRadialWavefunction n 0 hn' r ^ 2 * r ^ 2) = 0 := by
      rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℝ)) (fun r hr => by
        rw [hRz r hr]; ring)]
      simp
    rw [radial_wavefunction_norm] at hint
    exact one_ne_zero hint
  -- eigenvalue identity
  have hEval : (eigenvalue p n hn : ℝ) = Z ^ 2 * hydrogenEigenvalue n (by omega) := by
    rw [hZ_def]; simp only [eigenvalue, hydrogenEigenvalue]; ring
  have heigen : ∀ x : R3, x ≠ 0 →
      ∑ j : Fin 3, fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single j 1)
        = (-2 : ℂ) * (((eigenvalue p n hn : ℝ) : ℂ) + (p.Z : ℂ) * (‖x‖ : ℂ)⁻¹) * g ‖x‖ := by
    intro x hx
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hZx : 0 < Z * ‖x‖ := mul_pos hZ hr
    have _hZxne : (Z * ‖x‖ : ℝ) ≠ 0 := ne_of_gt hZx
    have hrne : (‖x‖ : ℝ) ≠ 0 := ne_of_gt hr
    have hfd : DifferentiableAt ℝ (fderiv ℝ (fun z : R3 => g ‖z‖)) x :=
      ((contDiffAt_radial g hg hx).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    rw [← laplacian_eq_sum_fderiv (fun z => g ‖z‖) hfd, laplacian_comp_norm g hg hx,
      show iteratedDeriv 2 g ‖x‖ = deriv (deriv g) ‖x‖ from by
        rw [iteratedDeriv_succ, iteratedDeriv_one],
      hgd2 ‖x‖, hgd ‖x‖, hg_def, deriv2_Rc]
    simp only [deriv_Rc, Rc]
    have hR'' : deriv (deriv (hydrogenRadialWavefunction n 0 hn')) (Z * ‖x‖)
        = -(2 * hydrogenEigenvalue n (by omega)) * hydrogenRadialWavefunction n 0 hn' (Z * ‖x‖)
          - 2 / (Z * ‖x‖) * deriv (hydrogenRadialWavefunction n 0 hn') (Z * ‖x‖)
          - 2 / (Z * ‖x‖) * hydrogenRadialWavefunction n 0 hn' (Z * ‖x‖) := by
      have heqn := radial_eigenvalue_eq n 0 hn' (Z * ‖x‖) hZx
      unfold RadialEq.radialHamiltonian at heqn
      rw [show deriv^[2] (hydrogenRadialWavefunction n 0 hn') (Z * ‖x‖)
          = deriv (deriv (hydrogenRadialWavefunction n 0 hn')) (Z * ‖x‖) from by
        simp [Function.iterate_succ]] at heqn
      simp only [Nat.cast_zero, zero_add, zero_mul, zero_div] at heqn
      linear_combination (-2 : ℝ) * heqn
    have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hZ
    have hxc : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast hrne
    have hR''ℂ : ((deriv (deriv (hydrogenRadialWavefunction n 0 hn')) (Z * ‖x‖) : ℝ) : ℂ)
        = -(2 * ((hydrogenEigenvalue n (by omega) : ℝ) : ℂ))
            * ((hydrogenRadialWavefunction n 0 hn' (Z * ‖x‖) : ℝ) : ℂ)
          - 2 / ((Z : ℂ) * (‖x‖ : ℂ))
            * ((deriv (hydrogenRadialWavefunction n 0 hn') (Z * ‖x‖) : ℝ) : ℂ)
          - 2 / ((Z : ℂ) * (‖x‖ : ℂ))
            * ((hydrogenRadialWavefunction n 0 hn' (Z * ‖x‖) : ℝ) : ℂ) := by
      rw [hR'']; push_cast; ring
    rw [hEval, ← hZ_def, hR''ℂ]
    push_cast
    field_simp
    ring
  exact bound_state_of_radial_profile p (eigenvalue p n hn) g hg haZ hbd1 hbd2 Ψ hΨ hΨ0 heigen

/-- **Reverse direction at `Z = 1`** (the special case `p = ⟨1, _⟩` of `hydrogen_bound_state`):
    every `E_n = −1/(2n²)` is an eigenvalue of `H = −½Δ − 1/r` with a nonzero `H²` bound state. -/
theorem hydrogen_bound_state_Z1 (n : ℕ) (hn : 1 ≤ n) :
    ∃ ψ : (hydrogenHamiltonian ⟨1, one_pos⟩).domain,
      (ψ : Spectra.Sobolev.l2R3) ≠ 0 ∧
      hydrogenHamiltonian ⟨1, one_pos⟩ ψ
        = ((eigenvalue ⟨1, one_pos⟩ n hn : ℝ) : ℂ) • (ψ : Spectra.Sobolev.l2R3) :=
  hydrogen_bound_state ⟨1, one_pos⟩ n hn

end QuantumMechanics.Hydrogen.Spectrum
