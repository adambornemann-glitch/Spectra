/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SpectralTheory.Algebra
import Spectra.SpectralTheory.Measure.PVM
import Spectra.Resolvent.Spectrum
/-!
# Spectrum ↔ spectral-measure support

The resolvent-set definition of the spectrum (`Spectra.Resolvent.spectrum`) agrees with the
projection-valued-measure characterization: `λ ∈ spectrum A` iff every open neighborhood of `λ`
carries a nonzero spectral projection.

This file proves the support-critical direction at the level of a one-parameter unitary group:
if `λ` lies in the resolvent set of `generator U_grp`, then `E((λ-ε, λ+ε)) = 0` for small `ε`.
The proof is the **bounded-inverse lower bound** — no Stone's formula needed: on the band
`[λ-ε, λ+ε]` the spectral localization bound `generator_sub_smul_norm_le_Icc` gives
`‖(A-λ)E(B)φ‖ ≤ ε‖E(B)φ‖`, while the bounded inverse `R` gives `‖E(B)φ‖ ≤ ‖R‖‖(A-λ)E(B)φ‖`;
for `ε < 1/‖R‖` these force `E(B) = 0`.
-/

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace
open Spectra.Borel
open SpectralMeasure
open Spectra.OneParameterUnitaryGroup
open Spectra.YosidaHille
open Spectra.Resolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.QuantumMechanics

variable (U_grp : OneParameterUnitaryGroup (H := H))

namespace SpectralTheory

/-- **Resolvent set ⟹ spectral gap.**  If `λ` is in the resolvent set of `generator U_grp`,
then a whole open interval around `λ` carries no spectral mass: `E((λ-ε, λ+ε)) = 0` for some
`ε > 0`.  Bounded-inverse lower bound argument. -/
theorem spectralProjection_Ioo_eq_zero_of_mem_resolventSet {lam : ℝ}
    (h : (lam : ℂ) ∈ resolventSet (generator U_grp)) :
    ∃ ε > 0, spectralProjection U_grp (Set.Ioo (lam - ε) (lam + ε)) measurableSet_Ioo = 0 := by
  obtain ⟨R, hleft, _hright⟩ := h
  set M := ‖R‖ with _hMdef
  have hM0 : 0 ≤ M := norm_nonneg R
  set ε : ℝ := 1 / (M + 1) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hMε : M * ε < 1 := by
    rw [hεdef, mul_one_div, div_lt_one (by positivity)]; linarith
  refine ⟨ε, hεpos, ?_⟩
  -- first kill the closed band `[λ-ε, λ+ε]`
  have hIcc : spectralProjection U_grp (Set.Icc (lam - ε) (lam + ε)) measurableSet_Icc = 0 := by
    refine ContinuousLinearMap.ext fun φ' => ?_
    rw [ContinuousLinearMap.zero_apply]
    set ξ := spectralProjection U_grp (Set.Icc (lam - ε) (lam + ε)) measurableSet_Icc φ' with _hξdef
    have hmem : ξ ∈ (generator U_grp).domain :=
      spectralProjection_mem_generatorDomain U_grp measurableSet_Icc
        (fun x hx => abs_le_max_of_mem_Icc hx) φ'
    have hbound := generator_sub_smul_norm_le_Icc U_grp (lam - ε) (lam + ε) lam
      (by linarith) (by linarith) φ' hmem
    rw [show max (lam - (lam - ε)) (lam + ε - lam) = ε by
      rw [show lam - (lam - ε) = ε by ring, show lam + ε - lam = ε by ring, max_self]] at hbound
    have hsmul : (lam : ℂ) • ξ = lam • ξ := (RCLike.real_smul_eq_coe_smul lam ξ).symm
    have hleft_appC : R (generator U_grp ⟨ξ, hmem⟩ - (lam : ℂ) • ξ) = ξ := hleft ⟨ξ, hmem⟩
    have hleft_app : R (generator U_grp ⟨ξ, hmem⟩ - lam • ξ) = ξ := by
      rw [← hsmul]; exact hleft_appC
    have hnormle : ‖ξ‖ ≤ M * (ε * ‖ξ‖) :=
      calc ‖ξ‖ = ‖R (generator U_grp ⟨ξ, hmem⟩ - lam • ξ)‖ := by rw [hleft_app]
        _ ≤ M * ‖generator U_grp ⟨ξ, hmem⟩ - lam • ξ‖ := R.le_opNorm _
        _ ≤ M * (ε * ‖ξ‖) := mul_le_mul_of_nonneg_left hbound hM0
    have hξ0 : ‖ξ‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖ξ‖ := lt_of_le_of_ne (norm_nonneg ξ) (Ne.symm hne)
      exact lt_irrefl ‖ξ‖
        (calc ‖ξ‖ ≤ M * (ε * ‖ξ‖) := hnormle
          _ = M * ε * ‖ξ‖ := by ring
          _ < 1 * ‖ξ‖ := mul_lt_mul_of_pos_right hMε hpos
          _ = ‖ξ‖ := one_mul _)
    exact norm_eq_zero.mp hξ0
  -- the open band is a sub-projection, hence also zero
  have hinter : spectralProjection U_grp (Set.Ioo (lam - ε) (lam + ε)) measurableSet_Ioo
        * spectralProjection U_grp (Set.Icc (lam - ε) (lam + ε)) measurableSet_Icc
      = spectralProjection U_grp (Set.Ioo (lam - ε) (lam + ε)) measurableSet_Ioo := by
    rw [spectralProjection_inter]
    exact spectralProjection_congr U_grp (Set.inter_eq_left.mpr Set.Ioo_subset_Icc_self)
      (measurableSet_Ioo.inter measurableSet_Icc) measurableSet_Ioo
  calc spectralProjection U_grp (Set.Ioo (lam - ε) (lam + ε)) measurableSet_Ioo
      = spectralProjection U_grp (Set.Ioo (lam - ε) (lam + ε)) measurableSet_Ioo
          * spectralProjection U_grp (Set.Icc (lam - ε) (lam + ε)) measurableSet_Icc := hinter.symm
    _ = spectralProjection U_grp (Set.Ioo (lam - ε) (lam + ε)) measurableSet_Ioo * 0 := by
        rw [hIcc]
    _ = 0 := mul_zero _

/-- **Transfer to the spectral PVM.**  For a self-adjoint `A`, if `λ` is in the resolvent set
then a neighborhood of `λ` carries no `spectralPVM` mass.  (`(spectralPVM hA).proj` is
definitionally `spectralProjection (genToGroup hA)`, and `generator (genToGroup hA) = A`.) -/
theorem spectralPVM_proj_Ioo_eq_zero_of_mem_resolventSet {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) {lam : ℝ} (h : (lam : ℂ) ∈ resolventSet A) :
    ∃ ε > 0, (PVM.spectralPVM hA).proj (Set.Ioo (lam - ε) (lam + ε)) measurableSet_Ioo = 0 := by
  have h' : (lam : ℂ) ∈ resolventSet (generator (genToGroup hA)) := by
    rw [generator_genToGroup hA]; exact h
  exact spectralProjection_Ioo_eq_zero_of_mem_resolventSet (genToGroup hA) h'

/-! ### The converse: a spectral gap puts `λ` in the resolvent set -/

/-- **Spectral gap ⟹ resolvent set.**  If `E((λ-ε, λ+ε)) = 0`, then `A - λ` has a two-sided
bounded inverse `R = Φ(g')`, where `g'(s) = (s-λ)⁻¹` truncated to `{|s-λ| ≥ ε}` (bounded by
`1/ε`).  Right inverse: `(A-λ)Φ(g')φ = Φ((s-λ)·g')φ = Φ(1_{gapᶜ})φ = E(gapᶜ)φ = φ`.  Left
inverse: `Φ(g')` commutes with `A` on the domain, reducing to the right inverse. -/
theorem mem_resolventSet_of_spectralProjection_Ioo_eq_zero {lam ε : ℝ} (hε : 0 < ε)
    (hgap : spectralProjection U_grp (Set.Ioo (lam - ε) (lam + ε)) measurableSet_Ioo = 0) :
    (lam : ℂ) ∈ resolventSet (generator U_grp) := by
  classical
  have hCmeas : MeasurableSet (Set.Ioo (lam - ε) (lam + ε))ᶜ := measurableSet_Ioo.compl
  -- on the complement, `|s - λ| ≥ ε`
  have hball : ∀ l ∈ (Set.Ioo (lam - ε) (lam + ε))ᶜ, ε ≤ |l - lam| := by
    intro l hl
    rw [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt, not_lt] at hl
    rcases hl with h | h
    · rw [abs_of_nonpos (by linarith : l - lam ≤ 0)]; linarith
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ l - lam)]; linarith
  -- the bounded truncated symbol
  set g' : ℝ → ℂ :=
    (Set.Ioo (lam - ε) (lam + ε))ᶜ.indicator (fun l => ((l : ℂ) - (lam : ℂ))⁻¹) with hg'def
  have hg'meas : Measurable g' := by
    rw [hg'def]
    exact ((Complex.measurable_ofReal.sub measurable_const).inv).indicator hCmeas
  have hg'bdd : ∃ C, ∀ l, ‖g' l‖ ≤ C := by
    refine ⟨ε⁻¹, fun l => ?_⟩
    by_cases hl : l ∈ (Set.Ioo (lam - ε) (lam + ε))ᶜ
    · rw [hg'def, Set.indicator_of_mem hl, norm_inv, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
      simpa only [one_div] using one_div_le_one_div_of_le hε (hball l hl)
    · rw [hg'def, Set.indicator_of_notMem hl, norm_zero]; positivity
  -- the product `(s-λ)·g'(s) = 1_{gapᶜ}(s)`
  have hprod : ∀ l : ℝ, ((l : ℂ) - (lam : ℂ)) * g' l
      = (Set.Ioo (lam - ε) (lam + ε))ᶜ.indicator (fun _ => (1 : ℂ)) l := by
    intro l
    by_cases hl : l ∈ (Set.Ioo (lam - ε) (lam + ε))ᶜ
    · have hne : (l : ℂ) - (lam : ℂ) ≠ 0 := by
        rw [sub_ne_zero, Ne, Complex.ofReal_inj]
        intro heq
        have hb := hball l hl; rw [heq, sub_self, abs_zero] at hb; linarith
      rw [hg'def, Set.indicator_of_mem hl, Set.indicator_of_mem hl, mul_inv_cancel₀ hne]
    · rw [hg'def, Set.indicator_of_notMem hl, Set.indicator_of_notMem hl, mul_zero]
  -- boundedness of `s·g'`
  have hlg'meas : Measurable fun l : ℝ => (l : ℂ) * g' l :=
    Complex.measurable_ofReal.mul hg'meas
  have hlg'bdd : ∃ C, ∀ ω : ℝ, ‖(ω : ℂ) * g' ω‖ ≤ C := by
    refine ⟨1 + |lam| * ε⁻¹, fun ω => ?_⟩
    by_cases hω : ω ∈ (Set.Ioo (lam - ε) (lam + ε))ᶜ
    · rw [hg'def, Set.indicator_of_mem hω, norm_mul, norm_inv,
        show ‖(ω : ℂ)‖ = |ω| from by rw [Complex.norm_real, Real.norm_eq_abs],
        show ‖(ω : ℂ) - (lam : ℂ)‖ = |ω - lam| from by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]]
      have hb : ε ≤ |ω - lam| := hball ω hω
      have hb0 : (0:ℝ) < |ω - lam| := lt_of_lt_of_le hε hb
      have htri : |ω| ≤ |ω - lam| + |lam| := by
        rw [← Real.norm_eq_abs, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
        calc ‖ω‖ = ‖(ω - lam) + lam‖ := by congr 1; ring
          _ ≤ ‖ω - lam‖ + ‖lam‖ := norm_add_le _ _
      calc |ω| * |ω - lam|⁻¹
          ≤ (|ω - lam| + |lam|) * |ω - lam|⁻¹ :=
            mul_le_mul_of_nonneg_right htri (inv_nonneg.mpr hb0.le)
        _ = 1 + |lam| * |ω - lam|⁻¹ := by rw [add_mul, mul_inv_cancel₀ hb0.ne']
        _ ≤ 1 + |lam| * ε⁻¹ := by
            have hinv : |ω - lam|⁻¹ ≤ ε⁻¹ := by
              simpa only [one_div] using one_div_le_one_div_of_le hε hb
            have := mul_le_mul_of_nonneg_left hinv (abs_nonneg lam)
            linarith
    · rw [hg'def, Set.indicator_of_notMem hω, mul_zero, norm_zero]; positivity
  -- `(s-λ)·g'` as a single symbol equals `1_{gapᶜ}`
  have hsymeq : (fun l : ℝ => (l : ℂ) * g' l - (lam : ℂ) * g' l)
      = (Set.Ioo (lam - ε) (lam + ε))ᶜ.indicator (fun _ => (1 : ℂ)) := by
    funext l; rw [← hprod l]; ring
  have hlamg'meas : Measurable fun l : ℝ => (lam : ℂ) * g' l := measurable_const.mul hg'meas
  have hlamg'bdd : ∃ C, ∀ ω : ℝ, ‖(lam : ℂ) * g' ω‖ ≤ C := by
    obtain ⟨C, hC⟩ := hg'bdd
    exact ⟨‖(lam : ℂ)‖ * C, fun ω => by rw [norm_mul]; gcongr; exact hC ω⟩
  have hsubm : Measurable fun l : ℝ => (l : ℂ) * g' l - (lam : ℂ) * g' l := hlg'meas.sub hlamg'meas
  have hsubb : ∃ C, ∀ ω : ℝ, ‖(ω : ℂ) * g' ω - (lam : ℂ) * g' ω‖ ≤ C := by
    refine ⟨1, fun ω => ?_⟩
    rw [show (ω : ℂ) * g' ω - (lam : ℂ) * g' ω = ((ω : ℂ) - (lam : ℂ)) * g' ω from by ring,
      hprod ω]
    by_cases hω : ω ∈ (Set.Ioo (lam - ε) (lam + ε))ᶜ
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  -- `E(gapᶜ) = id`
  have hcompl_id : spectralProjection U_grp (Set.Ioo (lam - ε) (lam + ε))ᶜ measurableSet_Ioo.compl
      = ContinuousLinearMap.id ℂ H := by
    rw [spectralProjection_compl U_grp (Set.Ioo (lam - ε) (lam + ε)) measurableSet_Ioo, hgap,
      sub_zero]
  -- the operator identity `Φ(s·g') - Φ(λ·g') = E(gapᶜ) = id`
  have hop : spectralCalculus U_grp (fun l : ℝ => (l : ℂ) * g' l) hlg'meas hlg'bdd
        - spectralCalculus U_grp (fun l : ℝ => (lam : ℂ) * g' l) hlamg'meas hlamg'bdd
      = ContinuousLinearMap.id ℂ H := by
    rw [← spectralCalculus_sub U_grp _ _ hlg'meas hlg'bdd hlamg'meas hlamg'bdd hsubm hsubb,
      spectralCalculus_congr U_grp hsymeq hsubm hsubb (measurable_const.indicator hCmeas)
        (indicator_one_bdd _)]
    exact hcompl_id
  -- the key value identity, used for both inverses
  have hmem : ∀ φ : H, spectralCalculus U_grp g' hg'meas hg'bdd φ ∈ (generator U_grp).domain :=
    fun φ => spectralCalculus_mem_generatorDomain U_grp g' hg'meas hg'bdd hlg'meas hlg'bdd φ
  have hval : ∀ φ : H,
      generator U_grp ⟨spectralCalculus U_grp g' hg'meas hg'bdd φ, hmem φ⟩
        - (lam : ℂ) • spectralCalculus U_grp g' hg'meas hg'bdd φ = φ := by
    intro φ
    rw [generator_spectralCalculus U_grp g' hg'meas hg'bdd hlg'meas hlg'bdd φ,
      show (lam : ℂ) • spectralCalculus U_grp g' hg'meas hg'bdd φ
          = spectralCalculus U_grp (fun l : ℝ => (lam : ℂ) * g' l) hlamg'meas hlamg'bdd φ from by
        rw [spectralCalculus_smul U_grp (lam : ℂ) g' hg'meas hg'bdd hlamg'meas hlamg'bdd,
          ContinuousLinearMap.smul_apply],
      ← ContinuousLinearMap.sub_apply, hop, ContinuousLinearMap.id_apply]
  refine ⟨spectralCalculus U_grp g' hg'meas hg'bdd, ?_, fun φ => ⟨hmem φ, hval φ⟩⟩
  intro ψ
  rw [map_sub, ContinuousLinearMap.map_smul,
    ← generator_spectralCalculus_comm U_grp g' hg'meas hg'bdd ψ]
  exact hval (ψ : H)

/-- **Spectrum = spectral-measure support** (group level).  `λ` is in the spectrum of
`generator U_grp` iff every open interval around `λ` carries nonzero spectral mass. -/
theorem mem_spectrum_iff_forall_spectralProjection_Ioo_ne_zero {lam : ℝ} :
    lam ∈ spectrum (generator U_grp) ↔
      ∀ ε > 0, spectralProjection U_grp (Set.Ioo (lam - ε) (lam + ε)) measurableSet_Ioo ≠ 0 := by
  constructor
  · intro hlam ε hε hcon
    exact hlam (mem_resolventSet_of_spectralProjection_Ioo_eq_zero U_grp hε hcon)
  · intro hforall hres
    obtain ⟨ε, hε, hzero⟩ := spectralProjection_Ioo_eq_zero_of_mem_resolventSet U_grp hres
    exact hforall ε hε hzero

/-- **Spectrum = spectral-measure support** for a self-adjoint operator `A`, in terms of its
projection-valued measure `spectralPVM hA`.  This is the resolvent-set definition
(`Resolvent.spectrum`) proven equal to the PVM-support characterization — the honest
equivalence the design called for. -/
theorem mem_spectrum_iff_forall_spectralPVM_proj_Ioo_ne_zero {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) {lam : ℝ} :
    lam ∈ spectrum A ↔
      ∀ ε > 0, (PVM.spectralPVM hA).proj (Set.Ioo (lam - ε) (lam + ε)) measurableSet_Ioo ≠ 0 := by
  constructor
  · intro hlam ε hε hcon
    refine hlam ?_
    rw [← generator_genToGroup hA]
    exact mem_resolventSet_of_spectralProjection_Ioo_eq_zero (genToGroup hA) hε hcon
  · intro hforall hres
    obtain ⟨ε, hε, hzero⟩ := spectralPVM_proj_Ioo_eq_zero_of_mem_resolventSet hA hres
    exact hforall ε hε hzero

end SpectralTheory
end Spectra.QuantumMechanics
