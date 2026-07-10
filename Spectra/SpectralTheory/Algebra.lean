/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/

/-
Spectra: SpectralTheory/Algebra.lean
Dirac Operator and Hamiltonian, rebuilt on the constructed spectral calculus.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Spectra.SpectralTheory.Measure.GeneratorLink

/-!
# Spectral-projection algebra and energy bounds

This file rebuilds the spectral-projection algebra and the generator energy-bound machinery
purely from the already-constructed spectral calculus in `Spectra.SpectralTheory.Measure`
(`spectralCalculus`, `generator`, `borelMeasure`) — no `IsSpectralMeasure` hypothesis is taken,
and no self-adjoint generator is stored as a field.  Everything below is a theorem:

* the projection algebra: `spectralProjection_univ`/`_empty`/`_inter`/`_comm`/`_compl`/`_union`
  (the classical PVM axioms, all proved from the calculus at indicator functions);
* the scalar-measure bridge `norm_sq_spectralProjection` (`‖E(B)φ‖² = μ_φ(B)`) and its
  zero-measure corollaries;
* finite-mass approximation (`spectralProjection_finite_approx_below/above`) and truncation
  limits (`tendsto_spectralProjection_Icc_Ici/Iic`), using only `measure_iUnion_null` /
  dominated convergence on the *scalar* measure — PVM σ-additivity is never needed;
* energy bounds on spectrally supported vectors
  (`spectralProjection_energy_upper_bound`/`_lower_bound`,
  `generator_sub_smul_norm_le_Icc`) and their truncation-limit lift to genuine domain
  vectors (`energy_lower_bound_of_spectralProjection_Iic_eq_zero`,
  `energy_upper_bound_of_spectralProjection_Ici_eq_zero`);
* the two-way energy/spectral-mass bridge
  (`spectralProjection_Iic_ne_zero_of_energy_lt`, `spectralProjection_Ici_ne_zero_of_energy_gt`)
  and the resulting **spectrum-unbounded ⟹ numerical-range-unbounded** headline theorems
  `generator_has_arbitrarily_negative_energy`/`generator_has_arbitrarily_positive_energy`;
* a **spectral gap from a uniform norm lower bound**
  (`spectralProjection_Ioo_eq_zero_of_norm_ge`): if `c·‖ψ‖ ≤ ‖Aψ‖` on the whole domain, then
  `E((−c,c)) = 0`.

This module is generic in `H` and `U_grp : OneParameterUnitaryGroup`; it is consumed by
`Spectra.QuantumMechanics.DiracEquation.Operators`, whose own headline theorems
(`dirac_unbounded_below/above`, `dirac_not_semibounded`) specialize
`generator_has_arbitrarily_negative_energy`/`_positive_energy` to the Dirac Hamiltonian, with
the only surviving hypotheses being the genuinely physical `h_spectrum_below/above` — full
self-adjointness of the generator is the separate deficiency-index project in
`Spectra.Operator.SelfAdjoint` and friends.
-/

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace

open Spectra.Borel
open SpectralMeasure
open Spectra.OneParameterUnitaryGroup
open Spectra.Fourier  -- `integrable_of_bounded`

/-! ## Spectral projection algebra (generic; extends `SpectralTheory`) -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.QuantumMechanics
variable (U_grp : OneParameterUnitaryGroup (H := H))
namespace SpectralTheory

/-- `E` respects equality of sets, with arbitrary measurability proofs on each side. -/
theorem spectralProjection_congr {B₁ B₂ : Set ℝ} (h : B₁ = B₂)
    (h₁ : MeasurableSet B₁) (h₂ : MeasurableSet B₂) :
    spectralProjection U_grp B₁ h₁ = spectralProjection U_grp B₂ h₂ := by
  subst h
  rfl

/-- `E(univ) = 1` (the old `hE.univ`). -/
theorem spectralProjection_univ :
    spectralProjection U_grp Set.univ MeasurableSet.univ = ContinuousLinearMap.id ℂ H := by
  have hfun : Set.indicator (Set.univ : Set ℝ) (fun _ => (1 : ℂ)) = fun _ : ℝ => (1 : ℂ) := by
    funext l; simp
  simp only [spectralProjection]
  rw [spectralCalculus_congr U_grp hfun (measurable_const.indicator MeasurableSet.univ)
      (indicator_one_bdd _) measurable_const ⟨1, fun _ => norm_one.le⟩,
    spectralCalculus_one]

/-- `E(∅) = 0` (the old `hE.empty`). -/
theorem spectralProjection_empty :
    spectralProjection U_grp ∅ MeasurableSet.empty = 0 := by
  have hfun : Set.indicator (∅ : Set ℝ) (fun _ => (1 : ℂ)) = fun l : ℝ => (0 : ℂ) * 1 := by
    funext l; simp
  simp only [spectralProjection]
  rw [spectralCalculus_congr U_grp hfun (measurable_const.indicator MeasurableSet.empty)
      (indicator_one_bdd _) (measurable_const.mul measurable_const) ⟨1, fun _ => by simp⟩,
    spectralCalculus_smul U_grp 0 (fun _ => (1 : ℂ)) measurable_const
      ⟨1, fun _ => norm_one.le⟩ (measurable_const.mul measurable_const)
      ⟨1, fun _ => by simp⟩,
    zero_smul]

/-- `E(B₁)E(B₂) = E(B₁ ∩ B₂)` (the old `hE.mul`): indicator products are indicators of
intersections, under multiplicativity of the calculus. -/
theorem spectralProjection_inter (B₁ B₂ : Set ℝ)
    (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂) :
    spectralProjection U_grp B₁ hB₁ * spectralProjection U_grp B₂ hB₂
      = spectralProjection U_grp (B₁ ∩ B₂) (hB₁.inter hB₂) := by
  have hfun : (fun l => Set.indicator B₁ (fun _ => (1 : ℂ)) l
        * Set.indicator B₂ (fun _ => (1 : ℂ)) l)
      = Set.indicator (B₁ ∩ B₂) (fun _ => (1 : ℂ)) := by
    classical
    funext l
    simp only [Set.indicator_apply, Set.mem_inter_iff]
    by_cases h₁ : l ∈ B₁ <;> by_cases h₂ : l ∈ B₂ <;> simp [h₁, h₂]
  simp only [spectralProjection]
  rw [spectralCalculus_mul U_grp (Set.indicator B₂ fun _ => (1 : ℂ))
      (Set.indicator B₁ fun _ => (1 : ℂ))
      (measurable_const.indicator hB₂) (indicator_one_bdd B₂)
      (measurable_const.indicator hB₁) (indicator_one_bdd B₁)
      ((measurable_const.indicator hB₁).mul (measurable_const.indicator hB₂))
      (bounded_mul (indicator_one_bdd B₁) (indicator_one_bdd B₂)),
    spectralCalculus_congr U_grp hfun
      ((measurable_const.indicator hB₁).mul (measurable_const.indicator hB₂))
      (bounded_mul (indicator_one_bdd B₁) (indicator_one_bdd B₂))
      (measurable_const.indicator (hB₁.inter hB₂)) (indicator_one_bdd (B₁ ∩ B₂))]

/-- Spectral projections commute (the old `functional_calculus_comm`, at indicators). -/
theorem spectralProjection_comm (B₁ B₂ : Set ℝ)
    (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂) :
    spectralProjection U_grp B₁ hB₁ * spectralProjection U_grp B₂ hB₂
      = spectralProjection U_grp B₂ hB₂ * spectralProjection U_grp B₁ hB₁ := by
  simp only [spectralProjection]
  exact spectralCalculus_comm U_grp _ _ (measurable_const.indicator hB₂) (indicator_one_bdd B₂)
    (measurable_const.indicator hB₁) (indicator_one_bdd B₁)

/-- **Complementation**: `E(Bᶜ) = 1 − E(B)` — from `1_{Bᶜ} = 1 − 1_B` under the calculus.
This is the new-stack replacement for the old `spectral_projection_compl_add`. -/
theorem spectralProjection_compl (B : Set ℝ) (hB : MeasurableSet B) :
    spectralProjection U_grp Bᶜ hB.compl
      = ContinuousLinearMap.id ℂ H - spectralProjection U_grp B hB := by
  classical
  have hfun : Set.indicator Bᶜ (fun _ => (1 : ℂ))
      = fun l => (fun _ : ℝ => (1 : ℂ)) l - Set.indicator B (fun _ => (1 : ℂ)) l := by
    funext l
    by_cases h : l ∈ B <;> simp only [Set.mem_compl_iff, h, not_true_eq_false, not_false_eq_true,
      Set.indicator_of_notMem, Set.indicator_of_mem, sub_self, sub_zero]
  simp only [spectralProjection]
  rw [spectralCalculus_congr U_grp hfun (measurable_const.indicator hB.compl)
      (indicator_one_bdd _) (measurable_const.sub (measurable_const.indicator hB))
      (bounded_sub ⟨1, fun _ => norm_one.le⟩ (indicator_one_bdd B)),
    spectralCalculus_sub U_grp _ _ measurable_const ⟨1, fun _ => norm_one.le⟩
      (measurable_const.indicator hB) (indicator_one_bdd B)
      (measurable_const.sub (measurable_const.indicator hB))
      (bounded_sub ⟨1, fun _ => norm_one.le⟩ (indicator_one_bdd B)),
    spectralCalculus_one]

/-- **Finite additivity**: `E(B₁ ∪ B₂) = E(B₁) + E(B₂)` for disjoint measurable sets —
from `1_{B₁ ∪ B₂} = 1_{B₁} + 1_{B₂}` under the calculus.  Replaces the old `proj_add`
field; countable additivity is never needed (see `inner_spectralProjection_self`). -/
theorem spectralProjection_union (B₁ B₂ : Set ℝ)
    (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂) (hdisj : Disjoint B₁ B₂) :
    spectralProjection U_grp (B₁ ∪ B₂) (hB₁.union hB₂)
      = spectralProjection U_grp B₁ hB₁ + spectralProjection U_grp B₂ hB₂ := by
  classical
  have hfun : Set.indicator (B₁ ∪ B₂) (fun _ => (1 : ℂ))
      = fun l => Set.indicator B₁ (fun _ => (1 : ℂ)) l
          + Set.indicator B₂ (fun _ => (1 : ℂ)) l := by
    funext l
    by_cases h₁ : l ∈ B₁
    · have h₂ : l ∉ B₂ := fun h₂ => Set.disjoint_left.mp hdisj h₁ h₂
      simp [h₁, h₂]
    · by_cases h₂ : l ∈ B₂ <;> simp [h₁, h₂]
  simp only [spectralProjection]
  rw [spectralCalculus_congr U_grp hfun (measurable_const.indicator (hB₁.union hB₂))
      (indicator_one_bdd _)
      ((measurable_const.indicator hB₁).add (measurable_const.indicator hB₂))
      (bounded_add (indicator_one_bdd B₁) (indicator_one_bdd B₂)),
    spectralCalculus_add U_grp _ _ (measurable_const.indicator hB₁) (indicator_one_bdd B₁)
      (measurable_const.indicator hB₂) (indicator_one_bdd B₂)
      ((measurable_const.indicator hB₁).add (measurable_const.indicator hB₂))
      (bounded_add (indicator_one_bdd B₁) (indicator_one_bdd B₂))]

/-- **The scalar measure through the projections** (the old
`spectral_scalar_measure_eq_norm_sq`): `‖E(B)φ‖² = μ_φ(B)`.  From the `L²` identity, since
`‖1_B‖² = 1_B`. -/
theorem norm_sq_spectralProjection (B : Set ℝ) (hB : MeasurableSet B) (φ : H) :
    ‖spectralProjection U_grp B hB φ‖ ^ 2 = ((borelMeasure U_grp φ) B).toReal := by
  classical
  have h := norm_sq_spectralCalculus_apply U_grp (Set.indicator B fun _ => (1 : ℂ))
    (measurable_const.indicator hB) (indicator_one_bdd B) φ
  have hcongr : (∫ l, ‖Set.indicator B (fun _ => (1 : ℂ)) l‖ ^ 2 ∂(borelMeasure U_grp φ))
      = ∫ l, Set.indicator B (fun _ => (1 : ℝ)) l ∂(borelMeasure U_grp φ) := by
    refine integral_congr_ae (.of_forall fun l => ?_)
    simp only [Set.indicator_apply]
    split_ifs <;> simp
  simp only [spectralProjection]
  rw [h, hcongr, integral_indicator_const (1 : ℝ) hB, smul_eq_mul, mul_one]; rfl

/-- Projection-measure zero equivalence: `E(B)φ = 0 ↔ μ_φ(B) = 0` (ported verbatim from
the old file, with the constructed measure). -/
theorem spectralProjection_eq_zero_iff_measure_zero (B : Set ℝ) (hB : MeasurableSet B)
    (φ : H) :
    spectralProjection U_grp B hB φ = 0 ↔ borelMeasure U_grp φ B = 0 := by
  haveI : IsFiniteMeasure (borelMeasure U_grp φ) := borelMeasure_isFiniteMeasure U_grp φ
  constructor
  · intro h
    have h_toReal : ((borelMeasure U_grp φ) B).toReal = 0 := by
      rw [← norm_sq_spectralProjection U_grp B hB φ, h, norm_zero]
      norm_num
    have h_ne_top := measure_ne_top (borelMeasure U_grp φ) B
    rw [← ENNReal.ofReal_toReal h_ne_top, h_toReal, ENNReal.ofReal_zero]
  · intro h
    have h_toReal : ((borelMeasure U_grp φ) B).toReal = 0 := by simp [h]
    rw [← norm_sq_spectralProjection U_grp B hB φ] at h_toReal
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp h_toReal)

/-- The spectral measure of a projected vector is supported on the projection set
(the old `spectral_measure_proj_supported`): `μ_{E(B)φ}(Bᶜ) = 0`, since
`E(Bᶜ)E(B) = E(∅) = 0`. -/
theorem borelMeasure_spectralProjection_supported (B : Set ℝ) (hB : MeasurableSet B)
    (φ : H) :
    borelMeasure U_grp (spectralProjection U_grp B hB φ) Bᶜ = 0 := by
  haveI : IsFiniteMeasure (borelMeasure U_grp (spectralProjection U_grp B hB φ)) :=
    borelMeasure_isFiniteMeasure U_grp _
  have h0 : spectralProjection U_grp Bᶜ hB.compl (spectralProjection U_grp B hB φ) = 0 := by
    rw [← ContinuousLinearMap.mul_apply, spectralProjection_inter U_grp Bᶜ B hB.compl hB,
      spectralProjection_congr U_grp (Set.compl_inter_self B) (hB.compl.inter hB)
        MeasurableSet.empty,
      spectralProjection_empty, ContinuousLinearMap.zero_apply]
  have h := norm_sq_spectralProjection U_grp Bᶜ hB.compl (spectralProjection U_grp B hB φ)
  rw [h0, norm_zero] at h
  have h' : ((borelMeasure U_grp (spectralProjection U_grp B hB φ)) Bᶜ).toReal = 0 := by
    rw [← h]; norm_num
  exact ((ENNReal.toReal_eq_zero_iff _).mp h').resolve_right (measure_ne_top _ _)

/-! ## Finite approximation (σ-additivity of the *scalar* measure suffices) -/

/-- `Iic N = ⋃ n, Icc (-↑n) N`: every `s ≤ N` is eventually in `[-n, N]`. -/
lemma Iic_eq_iUnion_Icc (N : ℝ) :
    Set.Iic N = ⋃ n : ℕ, Set.Icc (-(↑n : ℝ)) N := by
  ext s; simp only [Set.mem_Iic, Set.mem_iUnion, Set.mem_Icc]
  exact ⟨fun hs => by obtain ⟨n, hn⟩ := exists_nat_gt (-s); exact ⟨n, by linarith, hs⟩,
         fun ⟨_, _, h⟩ => h⟩

/-- `Ici N = ⋃ n, Icc N ↑n`. -/
lemma Ici_eq_iUnion_Icc (N : ℝ) :
    Set.Ici N = ⋃ n : ℕ, Set.Icc N (↑n : ℝ) := by
  ext s; simp only [Set.mem_Ici, Set.mem_iUnion, Set.mem_Icc]
  exact ⟨fun hs => by obtain ⟨n, hn⟩ := exists_nat_gt s; exact ⟨n, hs, by linarith⟩,
         fun ⟨_, h, _⟩ => h⟩

/-- Finite approximation of spectral projections from below: if `E((-∞, N])φ ≠ 0`, then
`E([-M, N])φ ≠ 0` for some finite `M`.  By contradiction via `measure_iUnion_null` on the
scalar measure — no PVM σ-additivity. -/
theorem spectralProjection_finite_approx_below (N : ℝ) (φ : H)
    (hφ : spectralProjection U_grp (Set.Iic N) measurableSet_Iic φ ≠ 0) :
    ∃ M : ℕ, spectralProjection U_grp (Set.Icc (-(↑M : ℝ)) N) measurableSet_Icc φ ≠ 0 := by
  by_contra hall
  push Not at hall
  apply hφ
  have h_zero : ∀ n : ℕ, borelMeasure U_grp φ (Set.Icc (-(↑n : ℝ)) N) = 0 := fun n =>
    (spectralProjection_eq_zero_iff_measure_zero U_grp _ measurableSet_Icc φ).mp (hall n)
  have h_null : borelMeasure U_grp φ (Set.Iic N) = 0 := by
    rw [Iic_eq_iUnion_Icc N]
    exact measure_iUnion_null h_zero
  exact (spectralProjection_eq_zero_iff_measure_zero U_grp _ measurableSet_Iic φ).mpr h_null

/-- Finite approximation from above: `E([N,∞))φ ≠ 0 ⟹ ∃ M, E([N, M])φ ≠ 0`. -/
theorem spectralProjection_finite_approx_above (N : ℝ) (φ : H)
    (hφ : spectralProjection U_grp (Set.Ici N) measurableSet_Ici φ ≠ 0) :
    ∃ M : ℕ, spectralProjection U_grp (Set.Icc N (↑M : ℝ)) measurableSet_Icc φ ≠ 0 := by
  by_contra hall
  push Not at hall
  apply hφ
  have h_zero : ∀ n : ℕ, borelMeasure U_grp φ (Set.Icc N (↑n : ℝ)) = 0 := fun n =>
    (spectralProjection_eq_zero_iff_measure_zero U_grp _ measurableSet_Icc φ).mp (hall n)
  have h_null : borelMeasure U_grp φ (Set.Ici N) = 0 := by
    rw [Ici_eq_iUnion_Icc N]
    exact measure_iUnion_null h_zero
  exact (spectralProjection_eq_zero_iff_measure_zero U_grp _ measurableSet_Ici φ).mpr h_null

/-! ## Energy bounds on spectrally supported vectors -/

/-- `|s| ≤ max |a| |b|` for `s ∈ [a, b]`. -/
lemma abs_le_max_of_mem_Icc {a b s : ℝ} (hs : s ∈ Set.Icc a b) : |s| ≤ max |a| |b| := by
  rw [abs_le]
  constructor
  · calc -(max |a| |b|) ≤ -|a| := neg_le_neg (le_max_left _ _)
      _ ≤ a := neg_abs_le a
      _ ≤ s := hs.1
  · calc s ≤ b := hs.2
      _ ≤ |b| := le_abs_self b
      _ ≤ max |a| |b| := le_max_right _ _

/-- Shared computation underlying both energy bounds.  For `ψ = E([a,b])φ` in the
generator's domain, returns the diagonal identity `Re⟪Aψ, ψ⟫ = ∫ s dμ_ψ`, integrability
of `id` against `μ_ψ`, and a.e. support of `μ_ψ` inside `[a, b]`.

Route: `A ψ = Φ(λ·1_B)φ = Φ(λ·1_B)ψ` (`generator_spectralProjection` + absorption via
`1_B² = 1_B`), so `⟪ψ, Aψ⟫ = spectralForm ψ ψ (λ·1_B) = ∫ λ·1_B dμ_ψ`; real parts pass
through the integral, and a.e. support converts `λ·1_B` to `λ`. -/
private lemma spectralProjection_re_inner_eq_integral (a b : ℝ) (φ : H)
    (hmem : spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ
      ∈ (generator U_grp).domain) :
    (⟪generator U_grp ⟨spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ, hmem⟩,
        spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ⟫_ℂ).re
      = (∫ s, s ∂(borelMeasure U_grp
          (spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ)))
    ∧ Integrable (fun s : ℝ => s)
        (borelMeasure U_grp (spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ))
    ∧ ∀ᵐ s ∂(borelMeasure U_grp
        (spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ)), s ∈ Set.Icc a b := by
  haveI : IsFiniteMeasure (borelMeasure U_grp
      (spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ)) :=
    borelMeasure_isFiniteMeasure U_grp _
  have habs : ∀ x ∈ Set.Icc a b, |x| ≤ max |a| |b| := fun x hx => abs_le_max_of_mem_Icc hx
  -- a.e. support inside [a, b]
  have h_supp := borelMeasure_spectralProjection_supported U_grp (Set.Icc a b)
    measurableSet_Icc φ
  have h_ae_mem : ∀ᵐ s ∂(borelMeasure U_grp
      (spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ)), s ∈ Set.Icc a b :=
    ae_iff.mpr (by convert h_supp using 1)
  -- absorption: Φ(λ·1_B) (E(B)φ) = Φ(λ·1_B) φ
  have habsorb : spectralCalculus U_grp
        (fun l => (l : ℂ) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) l)
        (id_indicator_measurable measurableSet_Icc) (id_indicator_bdd habs)
        (spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ)
      = spectralCalculus U_grp
          (fun l => (l : ℂ) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) l)
          (id_indicator_measurable measurableSet_Icc) (id_indicator_bdd habs) φ := by
    have hfun : (fun l => ((l : ℝ) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) l)
          * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) l)
        = fun l => (l : ℝ) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) l := by
      classical
      funext l
      simp only [Set.indicator_apply]
      split_ifs <;> ring
    simp only [spectralProjection]
    rw [← ContinuousLinearMap.mul_apply,
      spectralCalculus_mul U_grp (Set.indicator (Set.Icc a b) fun _ => (1 : ℂ))
        (fun l => (l : ℂ) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) l)
        (measurable_const.indicator measurableSet_Icc) (indicator_one_bdd _)
        (id_indicator_measurable measurableSet_Icc) (id_indicator_bdd habs)
        ((id_indicator_measurable measurableSet_Icc).mul
          (measurable_const.indicator measurableSet_Icc))
        (bounded_mul (id_indicator_bdd habs) (indicator_one_bdd _)),
      spectralCalculus_congr U_grp hfun
        ((id_indicator_measurable measurableSet_Icc).mul
          (measurable_const.indicator measurableSet_Icc))
        (bounded_mul (id_indicator_bdd habs) (indicator_one_bdd _))
        (id_indicator_measurable measurableSet_Icc) (id_indicator_bdd habs)]
  -- generator value, absorbed onto ψ
  have h1 : generator U_grp
        ⟨spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ, hmem⟩
      = spectralCalculus U_grp
          (fun l => (l : ℂ) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) l)
          (id_indicator_measurable measurableSet_Icc) (id_indicator_bdd habs) φ :=
    generator_spectralProjection U_grp measurableSet_Icc habs φ
  have hval : generator U_grp
        ⟨spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ, hmem⟩
      = spectralCalculus U_grp
          (fun l => (l : ℂ) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) l)
          (id_indicator_measurable measurableSet_Icc) (id_indicator_bdd habs)
          (spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ) := by
    rw [h1, ← habsorb]
  -- the ℂ-valued diagonal identity
  have hdiag : ⟪spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ,
      generator U_grp ⟨spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ, hmem⟩⟫_ℂ
      = ∫ s, (s : ℂ) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) s
          ∂(borelMeasure U_grp
            (spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ)) := by
    rw [hval, inner_spectralCalculus, spectralForm_self U_grp _
      (id_indicator_measurable measurableSet_Icc) (id_indicator_bdd habs)]
  -- integrabilities
  have h_int_C : Integrable
      (fun s : ℝ => (s : ℂ) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) s)
      (borelMeasure U_grp (spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ)) :=
    integrable_of_bounded (id_indicator_measurable measurableSet_Icc)
      (id_indicator_bdd habs).choose_spec
  have h_int_R : Integrable (fun s : ℝ => s)
      (borelMeasure U_grp (spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ)) :=
    Integrable.mono' (integrable_const (max |a| |b|)) measurable_id.aestronglyMeasurable
      (by filter_upwards [h_ae_mem] with s hs
          rw [Real.norm_eq_abs]
          exact abs_le_max_of_mem_Icc hs)
  refine ⟨?_, h_int_R, h_ae_mem⟩
  -- pass to real parts and strip the indicator a.e.
  calc (⟪generator U_grp
        ⟨spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ, hmem⟩,
        spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ⟫_ℂ).re
      = (⟪spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ,
          generator U_grp
            ⟨spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ, hmem⟩⟫_ℂ).re := by
        rw [← inner_conj_symm, Complex.conj_re]
    _ = (∫ s, (s : ℂ) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) s
          ∂(borelMeasure U_grp
            (spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ))).re :=
        congrArg Complex.re hdiag
    _ = ∫ s, ((s : ℂ) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) s).re
          ∂(borelMeasure U_grp
            (spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ)) :=
        (integral_re h_int_C).symm
    _ = ∫ s, s ∂(borelMeasure U_grp
          (spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ)) := by
        refine integral_congr_ae ?_
        filter_upwards [h_ae_mem] with s hs
        rw [Set.indicator_of_mem hs, mul_one, Complex.ofReal_re]

/-- **Energy upper bound** for spectrally supported vectors:
`Re⟪Aψ, ψ⟫ ≤ b·‖ψ‖²` for `ψ = E([a,b])φ`. -/
theorem spectralProjection_energy_upper_bound (a b : ℝ) (φ : H)
    (hmem : spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ
      ∈ (generator U_grp).domain) :
    (⟪generator U_grp ⟨spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ, hmem⟩,
        spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ⟫_ℂ).re
      ≤ b * ‖spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ‖ ^ 2 := by
  haveI : IsFiniteMeasure (borelMeasure U_grp
      (spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ)) :=
    borelMeasure_isFiniteMeasure U_grp _
  obtain ⟨h_re_eq, h_int_R, h_ae_mem⟩ :=
    spectralProjection_re_inner_eq_integral U_grp a b φ hmem
  rw [h_re_eq]
  have h_ae_le : ∀ᵐ s ∂(borelMeasure U_grp
      (spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ)), s ≤ b := by
    filter_upwards [h_ae_mem] with s hs
    exact hs.2
  calc (∫ s, s ∂(borelMeasure U_grp
        (spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ)))
      ≤ ∫ _, b ∂(borelMeasure U_grp
          (spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ)) :=
        integral_mono_ae h_int_R (integrable_const _) h_ae_le
    _ = b * ‖spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ‖ ^ 2 := by
        rw [integral_const, smul_eq_mul, Measure.real_def, borelMeasure_mass, mul_comm]

/-- **Energy lower bound**: `a·‖ψ‖² ≤ Re⟪Aψ, ψ⟫` for `ψ = E([a,b])φ`. -/
theorem spectralProjection_energy_lower_bound (a b : ℝ) (φ : H)
    (hmem : spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ
      ∈ (generator U_grp).domain) :
    a * ‖spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ‖ ^ 2
      ≤ (⟪generator U_grp
          ⟨spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ, hmem⟩,
          spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ⟫_ℂ).re := by
  haveI : IsFiniteMeasure (borelMeasure U_grp
      (spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ)) :=
    borelMeasure_isFiniteMeasure U_grp _
  obtain ⟨h_re_eq, h_int_R, h_ae_mem⟩ :=
    spectralProjection_re_inner_eq_integral U_grp a b φ hmem
  rw [h_re_eq]
  have h_ae_ge : ∀ᵐ s ∂(borelMeasure U_grp
      (spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ)), a ≤ s := by
    filter_upwards [h_ae_mem] with s hs
    exact hs.1
  calc a * ‖spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ‖ ^ 2
      = ∫ _, a ∂(borelMeasure U_grp
          (spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ)) := by
        rw [integral_const, smul_eq_mul, Measure.real_def, borelMeasure_mass, mul_comm]
    _ ≤ ∫ s, s ∂(borelMeasure U_grp
          (spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ)) :=
        integral_mono_ae (integrable_const _) h_int_R h_ae_ge

/-- **Spectral norm bound** (the old `gen_sub_scalar_norm_le_on_Icc`, collapsed):
`‖Aψ − sψ‖ ≤ max (s−a) (b−s) · ‖ψ‖` for `ψ = E([a,b])φ` and `a ≤ s ≤ b`.

Route — no second moments, no completing the square: `Aψ = Φ(λ·1_B)φ` and
`sψ = Φ(s·1_B)φ`, so `Aψ − sψ = Φ((λ−s)·1_B)φ`; the `L²` identity bounds its norm
squared by `δ² · μ_φ(B) = δ² · ‖ψ‖²` (`norm_sq_spectralProjection`), since the symbol is
supported on `B` where `|λ−s| ≤ δ`. -/
theorem generator_sub_smul_norm_le_Icc (a b s : ℝ) (has : a ≤ s) (_hsb : s ≤ b) (φ : H)
    (hmem : spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ
      ∈ (generator U_grp).domain) :
    ‖generator U_grp ⟨spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ, hmem⟩
        - s • spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ‖
      ≤ max (s - a) (b - s)
          * ‖spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ‖ := by
  classical
  haveI : IsFiniteMeasure (borelMeasure U_grp φ) := borelMeasure_isFiniteMeasure U_grp φ
  have habs : ∀ x ∈ Set.Icc a b, |x| ≤ max |a| |b| := fun x hx => abs_le_max_of_mem_Icc hx
  have hδ0 : (0 : ℝ) ≤ max (s - a) (b - s) :=
    le_trans (by linarith : (0 : ℝ) ≤ s - a) (le_max_left _ _)
  -- ── Symbol bookkeeping ──
  have hSm : Measurable fun l : ℝ =>
      (s : ℂ) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) l :=
    measurable_const.mul (measurable_const.indicator measurableSet_Icc)
  have hSb : ∃ C, ∀ ω, ‖(s : ℂ) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) ω‖ ≤ C :=
    bounded_mul (g₁ := fun _ => (s : ℂ)) ⟨‖(s : ℂ)‖, fun _ => le_rfl⟩
      (indicator_one_bdd _)
  have hDm : Measurable fun l : ℝ =>
      (l : ℂ) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) l
        - (s : ℂ) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) l :=
    (id_indicator_measurable measurableSet_Icc).sub hSm
  have hDb := bounded_sub (id_indicator_bdd habs) hSb
  have hsym_meas : Measurable fun l : ℝ =>
      ((l : ℂ) - (s : ℂ)) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) l :=
    (Complex.measurable_ofReal.sub measurable_const).mul
      (measurable_const.indicator measurableSet_Icc)
  have hpoint : ∀ ω : ℝ,
      ‖((ω : ℂ) - (s : ℂ)) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) ω‖
        ≤ max (s - a) (b - s) := by
    intro ω
    by_cases hω : ω ∈ Set.Icc a b
    · rw [Set.indicator_of_mem hω, mul_one,
        show ((ω : ℂ) - (s : ℂ)) = ((ω - s : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hω.1, le_max_left (s - a) (b - s)],
        by linarith [hω.2, le_max_right (s - a) (b - s)]⟩
    · rw [Set.indicator_of_notMem hω, mul_zero, norm_zero]
      exact hδ0
  have hsym_bdd : ∃ C, ∀ ω,
      ‖((ω : ℝ) - (s : ℂ)) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) ω‖ ≤ C :=
    ⟨max (s - a) (b - s), hpoint⟩
  have hdiff : (fun l : ℝ => (l : ℂ) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) l
        - (s : ℂ) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) l)
      = fun l : ℝ => ((l : ℂ) - (s : ℂ)) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) l :=
    funext fun l => by ring
  -- ── `Aψ − sψ = Φ((λ−s)·1_B)φ` ──
  have hA : generator U_grp
        ⟨spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ, hmem⟩
      = spectralCalculus U_grp
          (fun l => (l : ℂ) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) l)
          (id_indicator_measurable measurableSet_Icc) (id_indicator_bdd habs) φ :=
    generator_spectralProjection U_grp measurableSet_Icc habs φ
  have hS : s • spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ
      = spectralCalculus U_grp
          (fun l => (s : ℂ) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) l)
          hSm hSb φ := by
    rw [← Complex.coe_smul]
    simp only [spectralProjection]
    rw [← ContinuousLinearMap.smul_apply,
      ← spectralCalculus_smul U_grp (s : ℂ) (Set.indicator (Set.Icc a b) fun _ => (1 : ℂ))
        (measurable_const.indicator measurableSet_Icc) (indicator_one_bdd _) hSm hSb]
  have hkey : generator U_grp
        ⟨spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ, hmem⟩
        - s • spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ
      = spectralCalculus U_grp
          (fun l => ((l : ℂ) - (s : ℂ)) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) l)
          hsym_meas hsym_bdd φ := by
    rw [hA, hS, ← ContinuousLinearMap.sub_apply,
      ← spectralCalculus_sub U_grp _ _ (id_indicator_measurable measurableSet_Icc)
        (id_indicator_bdd habs) hSm hSb hDm hDb,
      spectralCalculus_congr U_grp hdiff hDm hDb hsym_meas hsym_bdd]
  rw [hkey]
  -- ── Squared bound against `μ_φ`, localized to `[a,b]` ──
  have hpt_sq : ∀ ω : ℝ,
      ‖((ω : ℂ) - (s : ℂ)) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) ω‖ ^ 2
        ≤ Set.indicator (Set.Icc a b) (fun _ => max (s - a) (b - s) ^ 2) ω := by
    intro ω
    by_cases hω : ω ∈ Set.Icc a b
    · simp only [Set.indicator_of_mem hω, mul_one,
        show ((ω : ℂ) - (s : ℂ)) = ((ω - s : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
      nlinarith [hω.1, hω.2, le_max_left (s - a) (b - s), le_max_right (s - a) (b - s),
        sq_abs (ω - s)]
    · simp only [Set.indicator_of_notMem hω, mul_zero, norm_zero]
      norm_num
  have h_sq : ‖spectralCalculus U_grp
        (fun l => ((l : ℂ) - (s : ℂ)) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) l)
        hsym_meas hsym_bdd φ‖ ^ 2
      ≤ max (s - a) (b - s) ^ 2
          * ‖spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ‖ ^ 2 := by
    rw [norm_sq_spectralCalculus_apply]
    calc (∫ l, ‖((l : ℂ) - (s : ℂ)) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) l‖ ^ 2
            ∂(borelMeasure U_grp φ))
        ≤ ∫ l, Set.indicator (Set.Icc a b) (fun _ => max (s - a) (b - s) ^ 2) l
            ∂(borelMeasure U_grp φ) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun l => sq_nonneg _)
            ((integrable_const _).indicator measurableSet_Icc)
            (Filter.Eventually.of_forall hpt_sq)
      _ = ((borelMeasure U_grp φ) (Set.Icc a b)).toReal • (max (s - a) (b - s) ^ 2) :=
          integral_indicator_const _ measurableSet_Icc
      _ = max (s - a) (b - s) ^ 2
            * ‖spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ‖ ^ 2 := by
          rw [smul_eq_mul, ← norm_sq_spectralProjection U_grp (Set.Icc a b)
            measurableSet_Icc φ, mul_comm]
  -- ── Take square roots ──
  calc ‖spectralCalculus U_grp
        (fun l => ((l : ℂ) - (s : ℂ)) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) l)
        hsym_meas hsym_bdd φ‖
      = Real.sqrt (‖spectralCalculus U_grp
          (fun l => ((l : ℂ) - (s : ℂ)) * Set.indicator (Set.Icc a b) (fun _ => (1 : ℂ)) l)
          hsym_meas hsym_bdd φ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (max (s - a) (b - s) ^ 2
          * ‖spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ‖ ^ 2) :=
        Real.sqrt_le_sqrt h_sq
    _ = Real.sqrt ((max (s - a) (b - s)
          * ‖spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ‖) ^ 2) := by
        ring_nf
    _ = max (s - a) (b - s)
          * ‖spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ‖ :=
        Real.sqrt_sq (mul_nonneg hδ0 (norm_nonneg _))

/-! ## The headline theorems -/

/-- **Spectrum unbounded below ⟹ numerical range unbounded below.**  All spectral inputs
are now constructed; the only hypothesis is the physical one. -/
theorem generator_has_arbitrarily_negative_energy
    (h_spectrum_below : ∀ N : ℝ, ∃ φ : H,
      spectralProjection U_grp (Set.Iic N) measurableSet_Iic φ ≠ 0)
    (bound : ℝ) :
    ∃ ψ : (generator U_grp).domain, (ψ : H) ≠ 0 ∧
      (⟪generator U_grp ψ, (ψ : H)⟫_ℂ).re < bound * ‖(ψ : H)‖ ^ 2 := by
  obtain ⟨φ, hφ⟩ := h_spectrum_below (bound - 1)
  obtain ⟨M, hM⟩ := spectralProjection_finite_approx_below U_grp (bound - 1) φ hφ
  have hmem : spectralProjection U_grp (Set.Icc (-(↑M : ℝ)) (bound - 1)) measurableSet_Icc φ
      ∈ (generator U_grp).domain :=
    spectralProjection_mem_generatorDomain U_grp measurableSet_Icc
      (fun s hs => abs_le_max_of_mem_Icc hs) φ
  have hψ_energy := spectralProjection_energy_upper_bound U_grp (-(↑M : ℝ)) (bound - 1) φ hmem
  have h_pos : (0 : ℝ) <
      ‖spectralProjection U_grp (Set.Icc (-(↑M : ℝ)) (bound - 1)) measurableSet_Icc φ‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hM) 2
  refine ⟨⟨spectralProjection U_grp (Set.Icc (-(↑M : ℝ)) (bound - 1)) measurableSet_Icc φ,
    hmem⟩, hM, ?_⟩
  change (⟪generator U_grp
      ⟨spectralProjection U_grp (Set.Icc (-(↑M : ℝ)) (bound - 1)) measurableSet_Icc φ, hmem⟩,
      spectralProjection U_grp (Set.Icc (-(↑M : ℝ)) (bound - 1)) measurableSet_Icc φ⟫_ℂ).re
    < bound * ‖spectralProjection U_grp (Set.Icc (-(↑M : ℝ)) (bound - 1))
        measurableSet_Icc φ‖ ^ 2
  nlinarith [hψ_energy, h_pos]

/-- **Spectrum unbounded above ⟹ numerical range unbounded above.** -/
theorem generator_has_arbitrarily_positive_energy
    (h_spectrum_above : ∀ N : ℝ, ∃ φ : H,
      spectralProjection U_grp (Set.Ici N) measurableSet_Ici φ ≠ 0)
    (bound : ℝ) :
    ∃ ψ : (generator U_grp).domain, (ψ : H) ≠ 0 ∧
      (⟪generator U_grp ψ, (ψ : H)⟫_ℂ).re > bound * ‖(ψ : H)‖ ^ 2 := by
  obtain ⟨φ, hφ⟩ := h_spectrum_above (bound + 1)
  obtain ⟨M, hM⟩ := spectralProjection_finite_approx_above U_grp (bound + 1) φ hφ
  have hmem : spectralProjection U_grp (Set.Icc (bound + 1) (↑M : ℝ)) measurableSet_Icc φ
      ∈ (generator U_grp).domain :=
    spectralProjection_mem_generatorDomain U_grp measurableSet_Icc
      (fun s hs => abs_le_max_of_mem_Icc hs) φ
  have hψ_energy := spectralProjection_energy_lower_bound U_grp (bound + 1) (↑M : ℝ) φ hmem
  have h_pos : (0 : ℝ) <
      ‖spectralProjection U_grp (Set.Icc (bound + 1) (↑M : ℝ)) measurableSet_Icc φ‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hM) 2
  refine ⟨⟨spectralProjection U_grp (Set.Icc (bound + 1) (↑M : ℝ)) measurableSet_Icc φ,
    hmem⟩, hM, ?_⟩
  change (⟪generator U_grp
      ⟨spectralProjection U_grp (Set.Icc (bound + 1) (↑M : ℝ)) measurableSet_Icc φ, hmem⟩,
      spectralProjection U_grp (Set.Icc (bound + 1) (↑M : ℝ)) measurableSet_Icc φ⟫_ℂ).re
    > bound * ‖spectralProjection U_grp (Set.Icc (bound + 1) (↑M : ℝ))
        measurableSet_Icc φ‖ ^ 2
  nlinarith [hψ_energy, h_pos]

/-! ## Energy expectation ⟹ spectral mass (the bridge to concrete operators)

The headline theorems above run *spectral mass ⟹ energy*: a vector with spectral support
reaching below `N` realizes energy below any bound.  The concrete Dirac construction needs the
*converse* one-directional fact — exactly what discharges `h_spectrum_below/above`:

> a single domain vector whose energy **expectation** lies below `N·‖φ‖²` already forces nonzero
> spectral mass in `(-∞, N]`.

No full PVM↔Fourier identification is needed, only the variational inequality.  The proof is a
domain-truncation limit: `E([N, M])φ → E([N, ∞))φ = φ` (`tendsto_spectralProjection_Icc_Ici`),
against `spectralProjection_energy_lower_bound` on each finite truncation. -/

/-- Truncations from above converge: `E([a, M])ξ → E([a, ∞))ξ` as `M → ∞`.  One application of
`tendsto_spectralCalculus_apply` (DCT) to the indicators `1_{[a,M]} → 1_{[a,∞)}`. -/
theorem tendsto_spectralProjection_Icc_Ici (a : ℝ) (ξ : H) :
    Tendsto (fun M : ℕ => spectralProjection U_grp (Set.Icc a (M : ℝ)) measurableSet_Icc ξ)
      atTop (𝓝 (spectralProjection U_grp (Set.Ici a) measurableSet_Ici ξ)) := by
  refine tendsto_spectralCalculus_apply U_grp (l := Filter.atTop)
    (G := fun M : ℕ => Set.indicator (Set.Icc a (M : ℝ)) fun _ => (1 : ℂ))
    (g := Set.indicator (Set.Ici a) fun _ => (1 : ℂ))
    (fun _ => measurable_const.indicator measurableSet_Icc) (fun _ => indicator_one_bdd _)
    (measurable_const.indicator measurableSet_Ici) (indicator_one_bdd _)
    (C := 1) (fun _ ω => ?_) (fun ω => ?_) ξ
  · rw [Set.indicator_apply]; split_ifs <;> simp
  · by_cases hω : a ≤ ω
    · obtain ⟨n₀, hn₀⟩ := exists_nat_ge ω
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop n₀] with M hM
      have hωM : ω ≤ (M : ℝ) := hn₀.trans (Nat.cast_le.mpr hM)
      rw [Set.indicator_of_mem (Set.mem_Ici.mpr hω),
        Set.indicator_of_mem (Set.mem_Icc.mpr ⟨hω, hωM⟩)]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards with M
      rw [Set.indicator_of_notMem (fun h => hω (Set.mem_Ici.mp h)),
        Set.indicator_of_notMem (fun h => hω (Set.mem_Icc.mp h).1)]

/-- Truncations from below converge: `E([-M, b])ξ → E((-∞, b])ξ` as `M → ∞`. -/
theorem tendsto_spectralProjection_Icc_Iic (b : ℝ) (ξ : H) :
    Tendsto (fun M : ℕ => spectralProjection U_grp (Set.Icc (-(M : ℝ)) b) measurableSet_Icc ξ)
      atTop (𝓝 (spectralProjection U_grp (Set.Iic b) measurableSet_Iic ξ)) := by
  refine tendsto_spectralCalculus_apply U_grp (l := Filter.atTop)
    (G := fun M : ℕ => Set.indicator (Set.Icc (-(M : ℝ)) b) fun _ => (1 : ℂ))
    (g := Set.indicator (Set.Iic b) fun _ => (1 : ℂ))
    (fun _ => measurable_const.indicator measurableSet_Icc) (fun _ => indicator_one_bdd _)
    (measurable_const.indicator measurableSet_Iic) (indicator_one_bdd _)
    (C := 1) (fun _ ω => ?_) (fun ω => ?_) ξ
  · rw [Set.indicator_apply]; split_ifs <;> simp
  · by_cases hω : ω ≤ b
    · obtain ⟨n₀, hn₀⟩ := exists_nat_ge (-ω)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop n₀] with M hM
      have hωM : -(M : ℝ) ≤ ω := by
        have : (n₀ : ℝ) ≤ (M : ℝ) := Nat.cast_le.mpr hM; linarith [hn₀]
      rw [Set.indicator_of_mem (Set.mem_Iic.mpr hω),
        Set.indicator_of_mem (Set.mem_Icc.mpr ⟨hωM, hω⟩)]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards with M
      rw [Set.indicator_of_notMem (fun h => hω (Set.mem_Iic.mp h)),
        Set.indicator_of_notMem (fun h => hω (Set.mem_Icc.mp h).2)]

/-- If `E((-∞, N])ξ = 0` then all spectral mass is in `[N, ∞)`: `E([N, ∞))ξ = ξ`. -/
theorem spectralProjection_Ici_eq_self_of_Iic (N : ℝ) (ξ : H)
    (h : spectralProjection U_grp (Set.Iic N) measurableSet_Iic ξ = 0) :
    spectralProjection U_grp (Set.Ici N) measurableSet_Ici ξ = ξ := by
  have hIio : spectralProjection U_grp (Set.Iio N) measurableSet_Iio ξ = 0 := by
    rw [spectralProjection_eq_zero_iff_measure_zero]
    exact measure_mono_null
      (show Set.Iio N ⊆ Set.Iic N from fun _ hx => Set.mem_Iic.mpr (le_of_lt (Set.mem_Iio.mp hx)))
      ((spectralProjection_eq_zero_iff_measure_zero U_grp (Set.Iic N) measurableSet_Iic ξ).mp h)
  have hset : (Set.Iio N)ᶜ = Set.Ici N := Set.compl_Iio
  have h1 : spectralProjection U_grp (Set.Ici N) measurableSet_Ici
      = spectralProjection U_grp (Set.Iio N)ᶜ measurableSet_Iio.compl :=
    spectralProjection_congr U_grp hset.symm measurableSet_Ici measurableSet_Iio.compl
  rw [h1, spectralProjection_compl U_grp (Set.Iio N) measurableSet_Iio,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, hIio, sub_zero]

/-- If `E([N, ∞))ξ = 0` then all spectral mass is in `(-∞, N]`: `E((-∞, N])ξ = ξ`. -/
theorem spectralProjection_Iic_eq_self_of_Ici (N : ℝ) (ξ : H)
    (h : spectralProjection U_grp (Set.Ici N) measurableSet_Ici ξ = 0) :
    spectralProjection U_grp (Set.Iic N) measurableSet_Iic ξ = ξ := by
  have hIoi : spectralProjection U_grp (Set.Ioi N) measurableSet_Ioi ξ = 0 := by
    rw [spectralProjection_eq_zero_iff_measure_zero]
    exact measure_mono_null
      (show Set.Ioi N ⊆ Set.Ici N from fun _ hx => Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hx)))
      ((spectralProjection_eq_zero_iff_measure_zero U_grp (Set.Ici N) measurableSet_Ici ξ).mp h)
  have hset : (Set.Ioi N)ᶜ = Set.Iic N := Set.compl_Ioi
  have h1 : spectralProjection U_grp (Set.Iic N) measurableSet_Iic
      = spectralProjection U_grp (Set.Ioi N)ᶜ measurableSet_Ioi.compl :=
    spectralProjection_congr U_grp hset.symm measurableSet_Iic measurableSet_Ioi.compl
  rw [h1, spectralProjection_compl U_grp (Set.Ioi N) measurableSet_Ioi,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, hIoi, sub_zero]

/-- The generator inherits the spectral support: `E((-∞, N])φ = 0 ⟹ E((-∞, N])(Aφ) = 0`, since
`E` commutes with the generator on its domain. -/
theorem spectralProjection_Iic_generator_eq_zero (N : ℝ) (φ : (generator U_grp).domain)
    (h : spectralProjection U_grp (Set.Iic N) measurableSet_Iic (φ : H) = 0) :
    spectralProjection U_grp (Set.Iic N) measurableSet_Iic (generator U_grp φ) = 0 := by
  rw [← generator_spectralProjection_comm U_grp (B := Set.Iic N) measurableSet_Iic φ]
  have hz : (⟨spectralProjection U_grp (Set.Iic N) measurableSet_Iic (φ : H),
      spectralProjection_mem_generatorDomain_of_mem U_grp measurableSet_Iic φ⟩
      : (generator U_grp).domain) = 0 := by
    apply Subtype.ext; simpa using h
  rw [hz]; exact LinearPMap.map_zero _

/-- The generator inherits the spectral support (above): `E([N, ∞))φ = 0 ⟹ E([N, ∞))(Aφ) = 0`. -/
theorem spectralProjection_Ici_generator_eq_zero (N : ℝ) (φ : (generator U_grp).domain)
    (h : spectralProjection U_grp (Set.Ici N) measurableSet_Ici (φ : H) = 0) :
    spectralProjection U_grp (Set.Ici N) measurableSet_Ici (generator U_grp φ) = 0 := by
  rw [← generator_spectralProjection_comm U_grp (B := Set.Ici N) measurableSet_Ici φ]
  have hz : (⟨spectralProjection U_grp (Set.Ici N) measurableSet_Ici (φ : H),
      spectralProjection_mem_generatorDomain_of_mem U_grp measurableSet_Ici φ⟩
      : (generator U_grp).domain) = 0 := by
    apply Subtype.ext; simpa using h
  rw [hz]; exact LinearPMap.map_zero _

/-- **Energy lower bound from zero low-mass**: if `φ ∈ D(A)` has no spectral mass in `(-∞, N]`,
its energy expectation is at least `N·‖φ‖²`.  The truncation limit of
`spectralProjection_energy_lower_bound`. -/
theorem energy_lower_bound_of_spectralProjection_Iic_eq_zero
    (N : ℝ) (φ : (generator U_grp).domain)
    (hE0 : spectralProjection U_grp (Set.Iic N) measurableSet_Iic (φ : H) = 0) :
    N * ‖(φ : H)‖ ^ 2 ≤ (⟪generator U_grp φ, (φ : H)⟫_ℂ).re := by
  have hφself : spectralProjection U_grp (Set.Ici N) measurableSet_Ici (φ : H) = (φ : H) :=
    spectralProjection_Ici_eq_self_of_Iic U_grp N (φ : H) hE0
  have hAφself :
      spectralProjection U_grp (Set.Ici N) measurableSet_Ici (generator U_grp φ)
        = generator U_grp φ :=
    spectralProjection_Ici_eq_self_of_Iic U_grp N (generator U_grp φ)
      (spectralProjection_Iic_generator_eq_zero U_grp N φ hE0)
  have hmem : ∀ M : ℕ,
      spectralProjection U_grp (Set.Icc N (M : ℝ)) measurableSet_Icc (φ : H)
        ∈ (generator U_grp).domain := fun _ =>
    spectralProjection_mem_generatorDomain U_grp measurableSet_Icc
      (fun _ hx => abs_le_max_of_mem_Icc hx) (φ : H)
  have hbound : ∀ M : ℕ,
      N * ‖spectralProjection U_grp (Set.Icc N (M : ℝ)) measurableSet_Icc (φ : H)‖ ^ 2
        ≤ (⟪spectralProjection U_grp (Set.Icc N (M : ℝ)) measurableSet_Icc (generator U_grp φ),
            spectralProjection U_grp (Set.Icc N (M : ℝ)) measurableSet_Icc (φ : H)⟫_ℂ).re := by
    intro M
    have h := spectralProjection_energy_lower_bound U_grp N (M : ℝ) (φ : H) (hmem M)
    rwa [generator_spectralProjection_comm U_grp measurableSet_Icc φ] at h
  have hψφ :
      Tendsto (fun M : ℕ =>
          spectralProjection U_grp (Set.Icc N (M : ℝ)) measurableSet_Icc (φ : H))
        atTop (𝓝 (φ : H)) := by
    have h := tendsto_spectralProjection_Icc_Ici U_grp N (φ : H); rwa [hφself] at h
  have hψAφ :
      Tendsto (fun M : ℕ =>
          spectralProjection U_grp (Set.Icc N (M : ℝ)) measurableSet_Icc (generator U_grp φ))
        atTop (𝓝 (generator U_grp φ)) := by
    have h := tendsto_spectralProjection_Icc_Ici U_grp N (generator U_grp φ); rwa [hAφself] at h
  exact le_of_tendsto_of_tendsto'
    ((hψφ.norm.pow 2).const_mul N)
    ((Complex.continuous_re.tendsto _).comp (hψAφ.inner hψφ)) hbound

/-- **Energy upper bound from zero high-mass**: if `φ ∈ D(A)` has no spectral mass in `[N, ∞)`,
its energy expectation is at most `N·‖φ‖²`. -/
theorem energy_upper_bound_of_spectralProjection_Ici_eq_zero
    (N : ℝ) (φ : (generator U_grp).domain)
    (hE0 : spectralProjection U_grp (Set.Ici N) measurableSet_Ici (φ : H) = 0) :
    (⟪generator U_grp φ, (φ : H)⟫_ℂ).re ≤ N * ‖(φ : H)‖ ^ 2 := by
  have hφself : spectralProjection U_grp (Set.Iic N) measurableSet_Iic (φ : H) = (φ : H) :=
    spectralProjection_Iic_eq_self_of_Ici U_grp N (φ : H) hE0
  have hAφself :
      spectralProjection U_grp (Set.Iic N) measurableSet_Iic (generator U_grp φ)
        = generator U_grp φ :=
    spectralProjection_Iic_eq_self_of_Ici U_grp N (generator U_grp φ)
      (spectralProjection_Ici_generator_eq_zero U_grp N φ hE0)
  have hmem : ∀ M : ℕ,
      spectralProjection U_grp (Set.Icc (-(M : ℝ)) N) measurableSet_Icc (φ : H)
        ∈ (generator U_grp).domain := fun _ =>
    spectralProjection_mem_generatorDomain U_grp measurableSet_Icc
      (fun _ hx => abs_le_max_of_mem_Icc hx) (φ : H)
  have hbound : ∀ M : ℕ,
      (⟪spectralProjection U_grp (Set.Icc (-(M : ℝ)) N) measurableSet_Icc (generator U_grp φ),
          spectralProjection U_grp (Set.Icc (-(M : ℝ)) N) measurableSet_Icc (φ : H)⟫_ℂ).re
        ≤ N * ‖spectralProjection U_grp (Set.Icc (-(M : ℝ)) N) measurableSet_Icc (φ : H)‖ ^ 2 := by
    intro M
    have h := spectralProjection_energy_upper_bound U_grp (-(M : ℝ)) N (φ : H) (hmem M)
    rwa [generator_spectralProjection_comm U_grp measurableSet_Icc φ] at h
  have hψφ :
      Tendsto (fun M : ℕ =>
          spectralProjection U_grp (Set.Icc (-(M : ℝ)) N) measurableSet_Icc (φ : H))
        atTop (𝓝 (φ : H)) := by
    have h := tendsto_spectralProjection_Icc_Iic U_grp N (φ : H); rwa [hφself] at h
  have hψAφ :
      Tendsto (fun M : ℕ =>
          spectralProjection U_grp (Set.Icc (-(M : ℝ)) N) measurableSet_Icc (generator U_grp φ))
        atTop (𝓝 (generator U_grp φ)) := by
    have h := tendsto_spectralProjection_Icc_Iic U_grp N (generator U_grp φ); rwa [hAφself] at h
  exact le_of_tendsto_of_tendsto'
    ((Complex.continuous_re.tendsto _).comp (hψAφ.inner hψφ))
    ((hψφ.norm.pow 2).const_mul N) hbound

/-- **The bridge, below**: a domain vector whose energy expectation lies below `N·‖φ‖²` has
nonzero spectral mass in `(-∞, N]`.  Discharges the `h_spectrum_below` hypothesis from a single
negative-energy witness — no PVM↔Fourier identification required. -/
theorem spectralProjection_Iic_ne_zero_of_energy_lt
    (N : ℝ) (φ : (generator U_grp).domain)
    (hlt : (⟪generator U_grp φ, (φ : H)⟫_ℂ).re < N * ‖(φ : H)‖ ^ 2) :
    spectralProjection U_grp (Set.Iic N) measurableSet_Iic (φ : H) ≠ 0 := fun hE0 =>
  absurd hlt
    (not_lt.mpr (energy_lower_bound_of_spectralProjection_Iic_eq_zero U_grp N φ hE0))

/-- **The bridge, above**: a domain vector whose energy expectation lies above `N·‖φ‖²` has
nonzero spectral mass in `[N, ∞)`. -/
theorem spectralProjection_Ici_ne_zero_of_energy_gt
    (N : ℝ) (φ : (generator U_grp).domain)
    (hgt : (⟪generator U_grp φ, (φ : H)⟫_ℂ).re > N * ‖(φ : H)‖ ^ 2) :
    spectralProjection U_grp (Set.Ici N) measurableSet_Ici (φ : H) ≠ 0 := fun hE0 =>
  absurd hgt
    (not_lt.mpr (energy_upper_bound_of_spectralProjection_Ici_eq_zero U_grp N φ hE0))

/-! ## Spectral gap from a norm lower bound (the mass-gap engine)

If the generator is bounded below in norm by `c ≥ 0` on its whole domain (`c·‖ψ‖ ≤ ‖Aψ‖`), then it
has no spectral mass in the open interval `(−c, c)`: every bounded spectral chunk `E([a,b])φ` with
`[a,b] ⊆ (−c,c)` would satisfy both `c‖·‖ ≤ ‖A·‖` and `‖A·‖ ≤ max(−a,b)‖·‖ < c‖·‖`, forcing it to
vanish; the open interval is the increasing union of such chunks. -/

/-- `(−c, c) = ⋃ₙ [−c+1/(n+1), c−1/(n+1)]`. -/
lemma Ioo_eq_iUnion_Icc_symm (c : ℝ) :
    Set.Ioo (-c) c = ⋃ n : ℕ, Set.Icc (-c + 1 / ((n : ℝ) + 1)) (c - 1 / ((n : ℝ) + 1)) := by
  ext x
  simp only [Set.mem_Ioo, Set.mem_iUnion, Set.mem_Icc]
  constructor
  · rintro ⟨hx1, hx2⟩
    have hmin : 0 < min (c + x) (c - x) := lt_min (by linarith) (by linarith)
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / min (c + x) (c - x))
    rw [div_lt_iff₀ hmin] at hn
    have hsmall : (1 : ℝ) / ((n : ℝ) + 1) ≤ min (c + x) (c - x) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      nlinarith [hn, hmin]
    exact ⟨n, by linarith [hsmall, min_le_left (c + x) (c - x)],
      by linarith [hsmall, min_le_right (c + x) (c - x)]⟩
  · rintro ⟨n, hn1, hn2⟩
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    exact ⟨by linarith, by linarith⟩

/-- **Spectral gap from a uniform norm lower bound**: if `c·‖ψ‖ ≤ ‖Aψ‖` for all domain vectors,
then `E((−c, c)) = 0`. -/
theorem spectralProjection_Ioo_eq_zero_of_norm_ge (c : ℝ)
    (hbound : ∀ ψ : (generator U_grp).domain, c * ‖(ψ : H)‖ ≤ ‖generator U_grp ψ‖) :
    spectralProjection U_grp (Set.Ioo (-c) c) measurableSet_Ioo = 0 := by
  haveI : ∀ φ : H, IsFiniteMeasure (borelMeasure U_grp φ) := borelMeasure_isFiniteMeasure U_grp
  ext φ
  simp only [ContinuousLinearMap.zero_apply]
  rw [spectralProjection_eq_zero_iff_measure_zero U_grp (Set.Ioo (-c) c) measurableSet_Ioo,
    Ioo_eq_iUnion_Icc_symm]
  refine measure_iUnion_null fun n => ?_
  set a := -c + 1 / ((n : ℝ) + 1) with ha
  set b := c - 1 / ((n : ℝ) + 1) with hb
  rw [← spectralProjection_eq_zero_iff_measure_zero U_grp (Set.Icc a b) measurableSet_Icc]
  by_cases hab : a ≤ b
  · have hmem : spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ
        ∈ (generator U_grp).domain :=
      spectralProjection_mem_generatorDomain U_grp measurableSet_Icc
        (fun x hx => abs_le_max_of_mem_Icc hx) φ
    by_contra hne
    have hnpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have ha0 : a ≤ 0 := by rw [ha]; nlinarith [hab]
    have hb0 : (0 : ℝ) ≤ b := by rw [hb]; nlinarith [hab]
    have hsub := generator_sub_smul_norm_le_Icc U_grp a b 0 ha0 hb0 φ hmem
    rw [zero_smul, sub_zero] at hsub
    have hmax : max (0 - a) (b - 0) = c - 1 / ((n : ℝ) + 1) := by
      have e1 : (0 : ℝ) - a = c - 1 / ((n : ℝ) + 1) := by rw [ha]; ring
      have e2 : b - (0 : ℝ) = c - 1 / ((n : ℝ) + 1) := by rw [hb]; ring
      rw [e1, e2, max_self]
    rw [hmax] at hsub
    have hlow := hbound ⟨spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ, hmem⟩
    have hnorm_pos : 0 < ‖spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ‖ :=
      norm_pos_iff.mpr hne
    nlinarith [hlow, hsub, hnorm_pos, hnpos]
  · rw [spectralProjection_congr U_grp (Set.Icc_eq_empty hab) measurableSet_Icc
      MeasurableSet.empty, spectralProjection_empty, ContinuousLinearMap.zero_apply]

end Spectra.QuantumMechanics.SpectralTheory
