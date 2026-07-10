/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SpectralTheory.Spectrum
import Spectra.Resolvent.Meromorphic
import Mathlib.Analysis.Complex.RemovableSingularity
/-!
# Simple pole of the resolvent at an isolated eigenvalue (Tier C: C3)

For a self-adjoint operator `A = generator U_grp` with an **isolated** real spectral point `lam`
(a punctured disk around `lam` lies in the resolvent set), the resolvent `resolventOf A` is
*meromorphic at `lam`*, with a simple pole and residue `−E({lam})`.

The construction mirrors spectral-gap resolvent `mem_resolventSet_of_spectralProjection_Ioo_eq_zero`
(`SpectralTheory/Spectrum.lean`): build the bounded operator `Φ(g)` where `g` is the resolvent
symbol `(·−z)⁻¹` **truncated to remove the punctured gap** `J = (lam−δ', lam+δ') ∖ {lam}` — the
truncation removes exactly the spectrally-null interval where the symbol would be unbounded (the
pole at `s=z`), keeping the lone eigenvalue point `{lam}` which carries the residue. Then
`(A−z)·Φ(g) = Φ(1_{Jᶜ}) = E(Jᶜ) = 1` (since `E(J)=0` by isolation), so `Φ(g) = resolventOf A z` by
the right-inverse uniqueness `resolventOf_eq_of_rightInverse` — valid at **real** `z` (no `Im z≠0`).

## Main definitions
* `puncturedGap lam δ'` — `(lam−δ', lam+δ') ∖ {lam}`.
* `simplePoleSymbol lam δ' z` — the truncated symbol `1_{Jᶜ}(s)·(s−z)⁻¹`.

This file (C3-sym): measurability and the two global bounds (`g` and `s·g`, the latter required by
`generator_spectralCalculus`).
-/
open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace
open Spectra.OneParameterUnitaryGroup
open Spectra.Resolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.QuantumMechanics.SpectralTheory

variable (U_grp : OneParameterUnitaryGroup (H := H))

/-! ## The truncated resolvent symbol -/

/-- The **punctured spectral gap** `(lam−δ', lam+δ') ∖ {lam}` around an isolated eigenvalue. -/
def puncturedGap (lam δ' : ℝ) : Set ℝ := Set.Ioo (lam - δ') (lam + δ') \ {lam}

lemma measurableSet_puncturedGap (lam δ' : ℝ) : MeasurableSet (puncturedGap lam δ') :=
  measurableSet_Ioo.diff (measurableSet_singleton lam)

/-- A point of `(puncturedGap)ᶜ` is either outside the open interval or equals `lam`. -/
lemma mem_compl_puncturedGap_iff {lam δ' : ℝ} {s : ℝ} :
    s ∈ (puncturedGap lam δ')ᶜ ↔ s ∉ Set.Ioo (lam - δ') (lam + δ') ∨ s = lam := by
  simp only [puncturedGap, Set.mem_compl_iff, Set.mem_diff, Set.mem_singleton_iff,
    not_and_or, not_not]

/-- The **truncated resolvent symbol** `1_{Jᶜ}(s)·(s−z)⁻¹`, `J` the punctured gap.  Globally bounded
(for fixed `z` near `lam`) since the truncation deletes the interval carrying the pole. -/
noncomputable def simplePoleSymbol (lam δ' : ℝ) (z : ℂ) : ℝ → ℂ :=
  (puncturedGap lam δ')ᶜ.indicator (fun s => ((s : ℂ) - z)⁻¹)

lemma simplePoleSymbol_measurable (lam δ' : ℝ) (z : ℂ) :
    Measurable (simplePoleSymbol lam δ' z) :=
  ((Complex.measurable_ofReal.sub measurable_const).inv).indicator
    (measurableSet_puncturedGap lam δ').compl

/-- **Separation from the spectrum.**  For `z` within `δ'/2` of `lam` and `s` outside the open
interval, `‖(s:ℂ)−z‖ ≥ δ'/2` — bounded via the real part, so no case split on `z` real. -/
lemma simplePole_sep {lam δ' : ℝ} {z : ℂ} (hz : dist z (lam : ℂ) < δ' / 2)
    {s : ℝ} (hs : s ∉ Set.Ioo (lam - δ') (lam + δ')) : δ' / 2 ≤ ‖(s : ℂ) - z‖ := by
  have hδ' : 0 < δ' := by have := dist_nonneg (x := z) (y := (lam : ℂ)); linarith
  have hre : |s - z.re| ≤ ‖(s : ℂ) - z‖ := by
    have h := Complex.abs_re_le_norm ((s : ℂ) - z)
    rwa [Complex.sub_re, Complex.ofReal_re] at h
  have hslam : δ' ≤ |s - lam| := by
    rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hs
    rcases hs with h | h
    · rw [abs_of_nonpos (by linarith : s - lam ≤ 0)]; linarith
    · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - lam)]; linarith
  have hzre : |z.re - lam| < δ' / 2 := by
    have h1 : |z.re - lam| = |(z - (lam : ℂ)).re| := by rw [Complex.sub_re, Complex.ofReal_re]
    have h2 : |(z - (lam : ℂ)).re| ≤ ‖z - (lam : ℂ)‖ := Complex.abs_re_le_norm _
    rw [dist_eq_norm] at hz
    rw [h1]; linarith
  have htri : |s - lam| ≤ |s - z.re| + |z.re - lam| := abs_sub_le s z.re lam
  linarith

open scoped Classical in
/-- **Global bound** `‖g(s)‖ ≤ 2/δ' + (dist z lam)⁻¹` (the `(dist z lam)⁻¹` is the residue/pole
contribution at the lone point `{lam}`). -/
lemma norm_simplePoleSymbol_le {lam δ' : ℝ} (hδ' : 0 < δ') {z : ℂ}
    (hz : dist z (lam : ℂ) < δ' / 2) (s : ℝ) :
    ‖simplePoleSymbol lam δ' z s‖ ≤ 2 / δ' + (dist z (lam : ℂ))⁻¹ := by
  rw [simplePoleSymbol, Set.indicator_apply]
  split_ifs with hs
  · rw [norm_inv]
    rcases mem_compl_puncturedGap_iff.mp hs with hsIoo | hslam
    · have hsep := simplePole_sep hz hsIoo
      have hpos : (0 : ℝ) < δ' / 2 := by positivity
      calc ‖(s : ℂ) - z‖⁻¹ = 1 / ‖(s : ℂ) - z‖ := by rw [one_div]
        _ ≤ 1 / (δ' / 2) := one_div_le_one_div_of_le hpos hsep
        _ = 2 / δ' := by rw [one_div, inv_div]
        _ ≤ 2 / δ' + (dist z (lam : ℂ))⁻¹ := le_add_of_nonneg_right (by positivity)
    · rw [hslam, show ‖(lam : ℂ) - z‖ = dist z (lam : ℂ) from by rw [dist_eq_norm, norm_sub_rev]]
      linarith [show (0 : ℝ) ≤ 2 / δ' from by positivity]
  · rw [norm_zero]; positivity

open scoped Classical in
/-- **Fix-A** — the *spectral* boundedness `‖s·g(s)‖ ≤ C` that `generator_spectralCalculus`
requires (`s·g = 1_{Jᶜ}(1 + z(s−z)⁻¹)`). -/
lemma id_mul_simplePoleSymbol_bdd {lam δ' : ℝ} (hδ' : 0 < δ') {z : ℂ}
    (hz : dist z (lam : ℂ) < δ' / 2) :
    ∃ C, ∀ s : ℝ, ‖(s : ℂ) * simplePoleSymbol lam δ' z s‖
      ≤ C := by
  refine ⟨1 + ‖z‖ * (2 / δ') + |lam| * (dist z (lam : ℂ))⁻¹, fun s => ?_⟩
  rw [simplePoleSymbol, Set.indicator_apply]
  have hC0 : (0 : ℝ) ≤ 1 + ‖z‖ * (2 / δ') + |lam| * (dist z (lam : ℂ))⁻¹ := by positivity
  split_ifs with hs
  · rcases mem_compl_puncturedGap_iff.mp hs with hsIoo | hslam
    · have hsep := simplePole_sep hz hsIoo
      have hpos : (0 : ℝ) < δ' / 2 := by positivity
      have hne : (s : ℂ) - z ≠ 0 := by
        rw [← norm_pos_iff]; linarith
      have hdecomp : (s : ℂ) * ((s : ℂ) - z)⁻¹ = 1 + z * ((s : ℂ) - z)⁻¹ := by
        field_simp; ring
      rw [hdecomp]
      have hinv : ‖((s : ℂ) - z)⁻¹‖ ≤ 2 / δ' := by
        rw [norm_inv]
        calc ‖(s : ℂ) - z‖⁻¹ = 1 / ‖(s : ℂ) - z‖ := by rw [one_div]
          _ ≤ 1 / (δ' / 2) := one_div_le_one_div_of_le hpos hsep
          _ = 2 / δ' := by rw [one_div, inv_div]
      have hb : ‖(1 : ℂ) + z * ((s : ℂ) - z)⁻¹‖ ≤ 1 + ‖z‖ * (2 / δ') := by
        have htri := norm_add_le (1 : ℂ) (z * ((s : ℂ) - z)⁻¹)
        rw [norm_mul, NormOneClass.norm_one] at htri
        calc ‖(1 : ℂ) + z * ((s : ℂ) - z)⁻¹‖
            ≤ 1 + ‖z‖ * ‖((s : ℂ) - z)⁻¹‖ := htri
          _ ≤ 1 + ‖z‖ * (2 / δ') := by gcongr
      linarith [hb, show (0 : ℝ) ≤ |lam| * (dist z (lam : ℂ))⁻¹ from by positivity]
    · rw [hslam, norm_mul,
        show ‖(lam : ℂ)‖ = |lam| from by rw [Complex.norm_real, Real.norm_eq_abs],
        norm_inv, show ‖(lam : ℂ) - z‖ = dist z (lam : ℂ) from by rw [dist_eq_norm, norm_sub_rev]]
      linarith [show (0 : ℝ) ≤ 1 + ‖z‖ * (2 / δ') from by positivity]
  · rw [mul_zero, norm_zero]; exact hC0

/-! ## The resolvent equals the truncated calculus near the isolated point (C3-rinv + C3-eq) -/

/-- **The resolvent at `z` near the isolated point equals the truncated calculus** `Φ(g)`.
Mirrors `mem_resolventSet_of_spectralProjection_Ioo_eq_zero` but with the punctured-gap symbol; the
key input is `E(puncturedGap)=0` (isolation).  Valid at **real** `z` — no `Im z≠0`. -/
lemma resolventOf_eq_simplePoleSymbol {lam δ' : ℝ} (hδ' : 0 < δ') {z : ℂ}
    (hz : dist z (lam : ℂ) < δ' / 2) (hzlam : z ≠ (lam : ℂ))
    (hgapJ : spectralProjection U_grp (puncturedGap lam δ')
        (measurableSet_puncturedGap lam δ') = 0)
    (hgm : Measurable (simplePoleSymbol lam δ' z))
    (hgb : ∃ C, ∀ s, ‖simplePoleSymbol lam δ' z s‖ ≤ C) :
    resolventOf (generator U_grp) z
      = spectralCalculus U_grp (simplePoleSymbol lam δ' z) hgm hgb := by
  classical
  set g := simplePoleSymbol lam δ' z with hg
  have hCmeas : MeasurableSet (puncturedGap lam δ')ᶜ := (measurableSet_puncturedGap lam δ').compl
  -- the product `(s−z)·g(s) = 1_{Jᶜ}(s)`
  have hprod : ∀ s : ℝ, ((s : ℂ) - z) * g s
      = (puncturedGap lam δ')ᶜ.indicator (fun _ => (1 : ℂ)) s := by
    intro s
    rw [hg, simplePoleSymbol, Set.indicator_apply, Set.indicator_apply]
    split_ifs with hs
    · have hne : (s : ℂ) - z ≠ 0 := by
        rcases mem_compl_puncturedGap_iff.mp hs with hsIoo | hslam
        · rw [← norm_pos_iff]; have := simplePole_sep hz hsIoo; linarith
        · rw [hslam, sub_ne_zero]; exact hzlam.symm
      rw [mul_inv_cancel₀ hne]
    · rw [mul_zero]
  -- symbol data for `s·g`, `z·g`, `s·g − z·g`
  have hidm : Measurable fun s : ℝ => (s : ℂ) * g s := Complex.measurable_ofReal.mul hgm
  have hidb : ∃ C, ∀ s : ℝ, ‖(s : ℂ) * g s‖ ≤ C := id_mul_simplePoleSymbol_bdd hδ' hz
  have hzgm : Measurable fun s : ℝ => z * g s := measurable_const.mul hgm
  have hzgb : ∃ C, ∀ s : ℝ, ‖z * g s‖ ≤ C := by
    obtain ⟨C, hC⟩ := hgb
    exact ⟨‖z‖ * C, fun s => by rw [norm_mul]; gcongr; exact hC s⟩
  have hsubm : Measurable fun s : ℝ => (s : ℂ) * g s - z * g s := hidm.sub hzgm
  have hsymeq : (fun s : ℝ => (s : ℂ) * g s - z * g s)
      = (puncturedGap lam δ')ᶜ.indicator (fun _ => (1 : ℂ)) := by
    funext s; rw [← hprod s]; ring
  have hsubb : ∃ C, ∀ s : ℝ, ‖(s : ℂ) * g s - z * g s‖ ≤ C := by
    refine ⟨1, fun s => ?_⟩
    rw [show (s : ℂ) * g s - z * g s = ((s : ℂ) - z) * g s from by ring, hprod s,
      Set.indicator_apply]
    split_ifs <;> simp
  -- `E(Jᶜ) = id`
  have hcompl_id : spectralProjection U_grp (puncturedGap lam δ')ᶜ hCmeas
      = ContinuousLinearMap.id ℂ H := by
    rw [spectralProjection_compl U_grp (puncturedGap lam δ') (measurableSet_puncturedGap lam δ'),
      hgapJ, sub_zero]
  -- `Φ(s·g) − Φ(z·g) = id`
  have hop : spectralCalculus U_grp (fun s : ℝ => (s : ℂ) * g s) hidm hidb
        - spectralCalculus U_grp (fun s : ℝ => z * g s) hzgm hzgb
      = ContinuousLinearMap.id ℂ H := by
    rw [← spectralCalculus_sub U_grp _ _ hidm hidb hzgm hzgb hsubm hsubb,
      spectralCalculus_congr U_grp hsymeq hsubm hsubb (measurable_const.indicator hCmeas)
        (indicator_one_bdd _)]
    exact hcompl_id
  -- the right inverse `(A − z)(Φ(g)φ) = φ`
  have hmem : ∀ φ : H, spectralCalculus U_grp g hgm hgb φ ∈ (generator U_grp).domain :=
    fun φ => spectralCalculus_mem_generatorDomain U_grp g hgm hgb hidm hidb φ
  have hval : ∀ φ : H,
      generator U_grp ⟨spectralCalculus U_grp g hgm hgb φ, hmem φ⟩
        - z • spectralCalculus U_grp g hgm hgb φ = φ := by
    intro φ
    rw [generator_spectralCalculus U_grp g hgm hgb hidm hidb φ,
      show z • spectralCalculus U_grp g hgm hgb φ
          = spectralCalculus U_grp (fun s : ℝ => z * g s) hzgm hzgb φ from by
        rw [spectralCalculus_smul U_grp z g hgm hgb hzgm hzgb, ContinuousLinearMap.smul_apply],
      ← ContinuousLinearMap.sub_apply, hop, ContinuousLinearMap.id_apply]
  -- the left inverse, needed only to certify `z ∈ resolventSet`
  have hleft : ∀ ψ : (generator U_grp).domain,
      spectralCalculus U_grp g hgm hgb (generator U_grp ψ - z • (ψ : H)) = (ψ : H) := by
    intro ψ
    rw [map_sub, ContinuousLinearMap.map_smul, ← generator_spectralCalculus_comm U_grp g hgm hgb ψ]
    exact hval (ψ : H)
  have hmem_set : z ∈ resolventSet (generator U_grp) :=
    ⟨spectralCalculus U_grp g hgm hgb, hleft, fun φ => ⟨hmem φ, hval φ⟩⟩
  exact resolventOf_eq_of_rightInverse hmem_set (fun φ => ⟨hmem φ, hval φ⟩)

/-! ## The simple-pole bound and meromorphy (C3-bound + C3-mero) -/

/-- **C3-bound** — near the isolated point the resolvent has at most a simple pole:
`‖R(z)‖ ≤ 2/δ' + (dist z lam)⁻¹`. -/
lemma norm_resolventOf_le_of_isolated {lam δ' : ℝ} (hδ' : 0 < δ') {z : ℂ}
    (hz : dist z (lam : ℂ) < δ' / 2) (hzlam : z ≠ (lam : ℂ))
    (hgapJ : spectralProjection U_grp (puncturedGap lam δ')
        (measurableSet_puncturedGap lam δ') = 0) :
    ‖resolventOf (generator U_grp) z‖ ≤ 2 / δ' + (dist z (lam : ℂ))⁻¹ := by
  have hgm := simplePoleSymbol_measurable lam δ' z
  have hgb : ∃ C, ∀ s, ‖simplePoleSymbol lam δ' z s‖ ≤ C :=
    ⟨_, fun s => norm_simplePoleSymbol_le hδ' hz s⟩
  rw [resolventOf_eq_simplePoleSymbol U_grp hδ' hz hzlam hgapJ hgm hgb]
  exact norm_spectralCalculus_le U_grp _ hgm hgb (norm_simplePoleSymbol_le hδ' hz)

/-- **C3-mero** — the resolvent is meromorphic at the isolated point `lam` (a simple pole).
`hiso` is the punctured-disk isolation (`C2`), `hgapJ` the spectral-gap projection (`G3 + C2`). -/
theorem meromorphicAt_resolventOf_of_isolated {lam δ' : ℝ} (hδ' : 0 < δ')
    (hgapJ : spectralProjection U_grp (puncturedGap lam δ')
        (measurableSet_puncturedGap lam δ') = 0)
    (hiso : ∀ z : ℂ, z ≠ (lam : ℂ) → dist z (lam : ℂ) < δ' →
      z ∈ resolventSet (generator U_grp)) :
    MeromorphicAt (resolventOf (generator U_grp)) (lam : ℂ) := by
  refine ⟨2, ?_⟩
  set f : ℂ → (H →L[ℂ] H) := fun z => (z - (lam : ℂ)) ^ 2 • resolventOf (generator U_grp) z with hf
  -- (a) differentiable on a punctured neighbourhood
  have hd : ∀ᶠ z in 𝓝[≠] (lam : ℂ), DifferentiableAt ℂ f z := by
    have hball : Metric.ball (lam : ℂ) δ' ∈ 𝓝 (lam : ℂ) := Metric.ball_mem_nhds _ hδ'
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hball] with z hz hzball
    have hzne : z ≠ (lam : ℂ) := hz
    have hzres : z ∈ resolventSet (generator U_grp) :=
      hiso z hzne (by rwa [Metric.mem_ball] at hzball)
    have hR : DifferentiableAt ℂ (resolventOf (generator U_grp)) z :=
      (resolventOf_analyticAt hzres).differentiableAt
    exact (((differentiableAt_id.sub (differentiableAt_const _)).pow 2).smul hR)
  -- (b) continuous at `lam` with value `0`
  have hc : ContinuousAt f (lam : ℂ) := by
    have hf_lam : f (lam : ℂ) = 0 := by rw [hf]; simp
    rw [ContinuousAt, hf_lam]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbound : ∀ᶠ z in 𝓝 (lam : ℂ), ‖f z‖
        ≤ ‖z - (lam : ℂ)‖ ^ 2 * (2 / δ') + ‖z - (lam : ℂ)‖ := by
      filter_upwards [Metric.ball_mem_nhds (lam : ℂ) (by positivity : (0 : ℝ) < δ' / 2)]
        with z hzball
      rcases eq_or_ne z (lam : ℂ) with rfl | hzne
      · simp [hf]
      · have hzd : dist z (lam : ℂ) < δ' / 2 := by rwa [Metric.mem_ball] at hzball
        have hdpos : (0 : ℝ) < dist z (lam : ℂ) := dist_pos.mpr hzne
        have hnb := norm_resolventOf_le_of_isolated U_grp hδ' hzd hzne hgapJ
        rw [hf]
        calc ‖(z - (lam : ℂ)) ^ 2 • resolventOf (generator U_grp) z‖
            = ‖z - (lam : ℂ)‖ ^ 2 * ‖resolventOf (generator U_grp) z‖ := by
              rw [norm_smul, norm_pow]
          _ ≤ ‖z - (lam : ℂ)‖ ^ 2 * (2 / δ' + (dist z (lam : ℂ))⁻¹) := by
              gcongr
          _ = ‖z - (lam : ℂ)‖ ^ 2 * (2 / δ') + ‖z - (lam : ℂ)‖ := by
              rw [dist_eq_norm] at hdpos ⊢
              field_simp
    have hB : Filter.Tendsto
        (fun z => ‖z - (lam : ℂ)‖ ^ 2 * (2 / δ') + ‖z - (lam : ℂ)‖)
        (𝓝 (lam : ℂ)) (𝓝 0) := by
      have h0 : Filter.Tendsto (fun z : ℂ => ‖z - (lam : ℂ)‖) (𝓝 (lam : ℂ)) (𝓝 0) := by
        have h1 : Filter.Tendsto (fun z : ℂ => z - (lam : ℂ)) (𝓝 (lam : ℂ))
            (𝓝 ((lam : ℂ) - (lam : ℂ))) := Filter.Tendsto.sub tendsto_id tendsto_const_nhds
        rw [sub_self] at h1
        simpa using h1.norm
      have : Filter.Tendsto
          (fun z => ‖z - (lam : ℂ)‖ ^ 2 * (2 / δ') + ‖z - (lam : ℂ)‖)
          (𝓝 (lam : ℂ)) (𝓝 (0 ^ 2 * (2 / δ') + 0)) :=
        ((h0.pow 2).mul_const _).add h0
      simpa using this
    exact squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbound hB
  exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd hc

/-! ## The residue is `−E({lam})` (C5) -/

open scoped Classical in
/-- Bound on the **residue symbol** `(z−lam)·g_z(s) + 1_{{lam}}(s)`: it is `≤ ‖z−lam‖·(2/δ')`
(it vanishes at `s=lam` because `(z−lam)(lam−z)⁻¹ = −1`). -/
lemma norm_residueSymbol_le {lam δ' : ℝ} (hδ' : 0 < δ') {z : ℂ}
    (hz : dist z (lam : ℂ) < δ' / 2) (hzlam : z ≠ (lam : ℂ)) (s : ℝ) :
    ‖(z - (lam : ℂ)) * simplePoleSymbol lam δ' z s
        + ({lam} : Set ℝ).indicator (fun _ => (1 : ℂ)) s‖
      ≤ ‖z - (lam : ℂ)‖ * (2 / δ') := by
  have hRHS : (0 : ℝ) ≤ ‖z - (lam : ℂ)‖ * (2 / δ') := by positivity
  have hkey : (z - (lam : ℂ)) * ((lam : ℂ) - z)⁻¹ = -1 := by
    rw [show (z - (lam : ℂ)) = -((lam : ℂ) - z) from by ring, neg_mul,
      mul_inv_cancel₀ (sub_ne_zero.mpr (Ne.symm hzlam))]
  rw [simplePoleSymbol, Set.indicator_apply, Set.indicator_apply]
  split_ifs with hJc hsl hsl
  · -- s = lam : value is `−1 + 1 = 0`
    rw [Set.mem_singleton_iff] at hsl
    rw [hsl, hkey, neg_add_cancel, norm_zero]; exact hRHS
  · -- s ∈ Iᶜ : `(z−lam)(s−z)⁻¹`
    have hsIoo : s ∉ Set.Ioo (lam - δ') (lam + δ') := by
      rcases mem_compl_puncturedGap_iff.mp hJc with h | h
      · exact h
      · exact absurd (by rw [Set.mem_singleton_iff]; exact h) hsl
    have hsep := simplePole_sep hz hsIoo
    rw [add_zero, norm_mul, norm_inv]
    gcongr
    calc ‖(s : ℂ) - z‖⁻¹ = 1 / ‖(s : ℂ) - z‖ := by rw [one_div]
      _ ≤ 1 / (δ' / 2) := one_div_le_one_div_of_le (by positivity) hsep
      _ = 2 / δ' := by rw [one_div, inv_div]
  · -- `s ∉ Jᶜ ∧ s = lam` is impossible (`lam ∈ Jᶜ`)
    rw [Set.mem_singleton_iff] at hsl
    exact absurd (mem_compl_puncturedGap_iff.mpr (Or.inr hsl)) hJc
  · rw [mul_zero, add_zero, norm_zero]; exact hRHS

/-- **C5 — the residue of the resolvent at the isolated point is `−E({lam})`**:
`(z − lam)·R(z) → −E({lam})` in operator norm as `z → lam` (through the punctured neighbourhood). -/
theorem tendsto_sub_smul_resolventOf {lam δ' : ℝ} (hδ' : 0 < δ')
    (hgapJ : spectralProjection U_grp (puncturedGap lam δ')
        (measurableSet_puncturedGap lam δ') = 0) :
    Filter.Tendsto (fun z => (z - (lam : ℂ)) • resolventOf (generator U_grp) z)
      (𝓝[≠] (lam : ℂ))
      (𝓝 (-(spectralProjection U_grp {lam} (measurableSet_singleton lam)))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ᶠ z in 𝓝[≠] (lam : ℂ),
      ‖(z - (lam : ℂ)) • resolventOf (generator U_grp) z
          - (-(spectralProjection U_grp {lam} (measurableSet_singleton lam)))‖
        ≤ ‖z - (lam : ℂ)‖ * (2 / δ') := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (lam : ℂ)
        (by positivity : (0 : ℝ) < δ' / 2))] with z hzne hzball
    have hzlam : z ≠ (lam : ℂ) := hzne
    have hzd : dist z (lam : ℂ) < δ' / 2 := by rwa [Metric.mem_ball] at hzball
    set g := simplePoleSymbol lam δ' z with _hgdef
    have hgm : Measurable g := simplePoleSymbol_measurable lam δ' z
    have hgb : ∃ C, ∀ s, ‖g s‖ ≤ C := ⟨_, fun s => norm_simplePoleSymbol_le hδ' hzd s⟩
    have hReq := resolventOf_eq_simplePoleSymbol U_grp hδ' hzd hzlam hgapJ hgm hgb
    have hcm : Measurable fun s : ℝ => (z - (lam : ℂ)) * g s := measurable_const.mul hgm
    have hcb : ∃ C, ∀ s : ℝ, ‖(z - (lam : ℂ)) * g s‖ ≤ C := by
      obtain ⟨C, hC⟩ := hgb
      exact ⟨‖z - (lam : ℂ)‖ * C, fun s => by rw [norm_mul]; gcongr; exact hC s⟩
    have hm1 : Measurable (({lam} : Set ℝ).indicator (fun _ => (1 : ℂ))) :=
      measurable_const.indicator (measurableSet_singleton lam)
    have hb1 := indicator_one_bdd ({lam} : Set ℝ)
    have hrm : Measurable fun s : ℝ => (z - (lam : ℂ)) * g s
        + ({lam} : Set ℝ).indicator (fun _ => (1 : ℂ)) s := hcm.add hm1
    have hrb : ∃ C, ∀ s : ℝ, ‖(z - (lam : ℂ)) * g s
        + ({lam} : Set ℝ).indicator (fun _ => (1 : ℂ)) s‖ ≤ C :=
      ⟨_, fun s => norm_residueSymbol_le hδ' hzd hzlam s⟩
    have hid : (z - (lam : ℂ)) • spectralCalculus U_grp g hgm hgb
          + spectralProjection U_grp {lam} (measurableSet_singleton lam)
        = spectralCalculus U_grp (fun s : ℝ => (z - (lam : ℂ)) * g s
          + ({lam} : Set ℝ).indicator (fun _ => (1 : ℂ)) s) hrm hrb := by
      rw [spectralCalculus_add U_grp _ _ hcm hcb hm1 hb1 hrm hrb,
        spectralCalculus_smul U_grp (z - (lam : ℂ)) g hgm hgb hcm hcb]
      rfl
    rw [hReq, sub_neg_eq_add, hid]
    exact norm_spectralCalculus_le U_grp _ hrm hrb (fun s => norm_residueSymbol_le hδ' hzd hzlam s)
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbound ?_
  have h0 : Filter.Tendsto (fun z : ℂ => ‖z - (lam : ℂ)‖) (𝓝[≠] (lam : ℂ)) (𝓝 0) := by
    have h1 : Filter.Tendsto (fun z : ℂ => z - (lam : ℂ)) (𝓝 (lam : ℂ)) (𝓝 0) := by
      have h2 : Filter.Tendsto (fun z : ℂ => z - (lam : ℂ)) (𝓝 (lam : ℂ))
          (𝓝 ((lam : ℂ) - (lam : ℂ))) := by
        apply Filter.Tendsto.sub
        · exact tendsto_id
        · exact tendsto_const_nhds
      rwa [sub_self] at h2
    simpa using (h1.norm).mono_left nhdsWithin_le_nhds
  simpa using h0.mul_const (2 / δ')

end Spectra.QuantumMechanics.SpectralTheory
