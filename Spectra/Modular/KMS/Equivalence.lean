/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.KMS.AnalyticElements
import Spectra.Modular.KMS.ImaginaryTime
import Spectra.Modular.KMS.PeriodicStrip.Basic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.UniformSpace.UniformConvergence
/-!
# Equivalence of the KMS conditions (Tier-3 capstone)

The **strip** KMS condition (`IsKMSState`: for every pair `a, b` an analytic strip function with the
twisted boundary values) and the **imaginary-time** KMS condition (`IsImaginaryTimeKMS`:
`ω(a·σ_{iβ} b) = ω(b·a)` for every analytic element `b`) are **equivalent**.

* `⟹` is A2 (`IsKMSState.imaginaryTime`), packaged over all analytic `b`.
* `⟸` for analytic `b`: `F_b(z) = ω(a·σ_z b)` is itself a KMS function — its upper boundary is the
  imaginary-time identity applied to the analytic element `σ_t b` (closure under the flow, A1).
* `⟸` for general `b`: approximate `b` by analytic `bₙ → b` (A1 density). Because `α_t` is
  **isometric** (A1), the Hadamard three-lines bound makes `Fₙ = F_{bₙ}` **uniformly Cauchy** on the
  closed strip, so the limit is holomorphic by uniform convergence — Montel/Vitali is *not* needed.

## Main statements

* `Spectra.KMS.IsImaginaryTimeKMS` — the imaginary-time condition.
* `Spectra.KMS.kmsFunctionOfAnalytic` — the KMS function for an analytic element.
* `Spectra.KMS.isKMSState_iff_imaginaryTime` — the equivalence.
-/

open Complex Set Filter Topology
open Spectra.PeriodicHolomorphic

namespace Spectra.KMS

variable {A : Type*} [CStarAlgebra A]

/-- **The imaginary-time KMS condition.** For every `a` and every analytic element `b`,
`ω (a · σ_{iβ}(b)) = ω (b · a)`. (`b` ranges over a `Prop`, so by proof irrelevance the value is
independent of the analyticity witness.) -/
def IsImaginaryTimeKMS (ω : State A) (α : Dynamics A) (β : ℝ) : Prop :=
  ∀ (a b : A) (hb : α.IsAnalyticElement b), ω (a * α.sigma hb ((β : ℂ) * I)) = ω (b * a)

/-- **A3a: the KMS function of an analytic element.** Under the imaginary-time condition, for an
analytic element `b` the correlation continuation `z ↦ ω (a · σ_z b)` is a genuine KMS function for
`(a, b)`. Holomorphy/continuity/boundedness are the KMS-free facts `sigmaCorr_*`; the upper boundary
is the imaginary-time identity at the analytic element `σ_t b` (via the group law `sigma_sigma`). -/
noncomputable def kmsFunctionOfAnalytic {ω : State A} {α : Dynamics A} {β : ℝ}
    (hkmsIT : IsImaginaryTimeKMS ω α β) {b : A} (hb : α.IsAnalyticElement b) (a : A) :
    KMSFunction ω α β a b where
  toFun := fun z => ω (a * α.sigma hb z)
  holomorphic := (sigmaCorr_differentiable hb a).differentiableOn
  continuousOn := (sigmaCorr_differentiable hb a).continuous.continuousOn
  bounded := sigmaCorr_bddAbove_closedStrip hb a
  lower_boundary := fun t => by
    show ω (a * α.sigma hb (realToLower t)) = ω (a * α.evolve t b)
    rw [show α.sigma hb (realToLower t) = α.evolve t b from α.sigma_ofReal hb t]
  upper_boundary := fun t => by
    show ω (a * α.sigma hb (realToUpper β t)) = ω (α.evolve t b * a)
    have hgl : α.sigma hb (realToUpper β t)
        = α.sigma (α.isAnalyticElement_sigma hb (t : ℂ)) ((β : ℂ) * I) := by
      rw [α.sigma_sigma hb ((β : ℂ) * I) (t : ℂ),
        show realToUpper β t = (β : ℂ) * I + (t : ℂ) from by simp only [realToUpper]; ring]
    rw [hgl, hkmsIT a (α.sigma hb (t : ℂ)) (α.isAnalyticElement_sigma hb (t : ℂ)),
      α.sigma_ofReal hb t]

variable {ω : State A} {α : Dynamics A} {β : ℝ}

/-- The state `ω` packaged as a continuous linear functional `A →L[ℂ] ℂ`. -/
private noncomputable def omegaL (ω : State A) : A →L[ℂ] ℂ := ⟨ω.toFun, ω.continuous⟩

/-- `omegaL ω` agrees pointwise with `ω`. -/
private lemma omegaL_apply (ω : State A) (a : A) : omegaL ω a = ω a := rfl

/-- The difference of two `kmsFunctionOfAnalytic`s, bounded on the closed strip by
`C * ‖bₙ - bₘ‖` where `C = ‖ωL‖ * ‖a‖`. -/
private lemma diff_bound (hβ : 0 < β) (hkmsIT : IsImaginaryTimeKMS ω α β) (a : A)
    {bn bm : A} (hbn : α.IsAnalyticElement bn) (hbm : α.IsAnalyticElement bm)
    {z : ℂ} (hz : z ∈ ClosedStrip β) :
    ‖(kmsFunctionOfAnalytic hkmsIT hbn a).toFun z
        - (kmsFunctionOfAnalytic hkmsIT hbm a).toFun z‖
      ≤ (‖omegaL ω‖ * ‖a‖) * ‖bn - bm‖ := by
  set Fn := kmsFunctionOfAnalytic hkmsIT hbn a with _hFn
  set Fm := kmsFunctionOfAnalytic hkmsIT hbm a with _hFm
  set D : ℂ → ℂ := fun w => Fn.toFun w - Fm.toFun w with _hD
  set C : ℝ := ‖omegaL ω‖ * ‖a‖ with hC
  set X : ℝ := C * ‖bn - bm‖ with hX
  have _hCnn : 0 ≤ C := by positivity
  have hXnn : 0 ≤ X := by positivity
  -- D is holomorphic on the open strip, continuous + bounded on the closed strip.
  have hDholo : DifferentiableOn ℂ D (Strip β) := Fn.holomorphic.sub Fm.holomorphic
  have hDcont : ContinuousOn D (ClosedStrip β) := Fn.continuousOn.sub Fm.continuousOn
  have hDbdd : BddAbove (norm '' (D '' ClosedStrip β)) := by
    obtain ⟨Mn, hMn⟩ := Fn.bounded
    obtain ⟨Mm, hMm⟩ := Fm.bounded
    refine ⟨Mn + Mm, ?_⟩
    rintro y ⟨v, ⟨w, hw, rfl⟩, rfl⟩
    calc ‖Fn.toFun w - Fm.toFun w‖ ≤ ‖Fn.toFun w‖ + ‖Fm.toFun w‖ := norm_sub_le _ _
      _ ≤ Mn + Mm :=
          add_le_add (hMn ⟨Fn.toFun w, ⟨w, hw, rfl⟩, rfl⟩) (hMm ⟨Fm.toFun w, ⟨w, hw, rfl⟩, rfl⟩)
  -- Lower-edge bound.
  have hlow : ∀ t : ℝ, ‖D (realToLower t)‖ ≤ X := by
    intro t
    have heq : D (realToLower t) = ω (a * α.evolve t (bn - bm)) := by
      change Fn.toFun (realToLower t) - Fm.toFun (realToLower t) = _
      rw [Fn.lower_boundary, Fm.lower_boundary, map_sub (α.evolve t), mul_sub, map_sub]
    rw [heq]
    calc ‖ω (a * α.evolve t (bn - bm))‖
        = ‖omegaL ω (a * α.evolve t (bn - bm))‖ := by rw [omegaL_apply]
      _ ≤ ‖omegaL ω‖ * ‖a * α.evolve t (bn - bm)‖ := (omegaL ω).le_opNorm _
      _ ≤ ‖omegaL ω‖ * (‖a‖ * ‖α.evolve t (bn - bm)‖) :=
          mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
      _ = ‖omegaL ω‖ * (‖a‖ * ‖bn - bm‖) := by rw [α.norm_evolve]
      _ = X := by rw [hX, hC]; ring
  -- Upper-edge bound.
  have hup : ∀ t : ℝ, ‖D (realToUpper β t)‖ ≤ X := by
    intro t
    have heq : D (realToUpper β t) = ω (α.evolve t (bn - bm) * a) := by
      change Fn.toFun (realToUpper β t) - Fm.toFun (realToUpper β t) = _
      rw [Fn.upper_boundary, Fm.upper_boundary, map_sub (α.evolve t), sub_mul, map_sub]
    rw [heq]
    calc ‖ω (α.evolve t (bn - bm) * a)‖
        = ‖omegaL ω (α.evolve t (bn - bm) * a)‖ := by rw [omegaL_apply]
      _ ≤ ‖omegaL ω‖ * ‖α.evolve t (bn - bm) * a‖ := (omegaL ω).le_opNorm _
      _ ≤ ‖omegaL ω‖ * (‖α.evolve t (bn - bm)‖ * ‖a‖) :=
          mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
      _ = ‖omegaL ω‖ * (‖bn - bm‖ * ‖a‖) := by rw [α.norm_evolve]
      _ = X := by rw [hX, hC]; ring
  -- Case-split on X.
  rcases eq_or_lt_of_le hXnn with hX0 | hXpos
  · -- X = 0: D vanishes on both boundary lines, hence everywhere on the closed strip.
    have hX0' : X = 0 := hX0.symm
    have hlow0 : ∀ t : ℝ, D (realToLower t) = 0 := by
      intro t; have := hlow t; rw [hX0'] at this
      exact norm_eq_zero.mp (le_antisymm this (norm_nonneg _))
    have hup0 : ∀ t : ℝ, D (realToUpper β t) = 0 := by
      intro t; have := hup t; rw [hX0'] at this
      exact norm_eq_zero.mp (le_antisymm this (norm_nonneg _))
    have hDz : D z = 0 :=
      eqZero_of_strip_boundary_zero D hβ hDholo hDcont hDbdd hlow0 hup0 z hz
    change ‖D z‖ ≤ X
    rw [hDz, hX0']; simp
  · -- X > 0: Hadamard three-lines.
    set S0 : ℝ := sSup ((norm ∘ D) '' (Complex.im ⁻¹' {(0 : ℝ)})) with hS0
    set Sb : ℝ := sSup ((norm ∘ D) '' (Complex.im ⁻¹' {β})) with hSb
    -- Boundedness of the boundary-line images (subsets of D '' ClosedStrip β).
    have hbdd0 : BddAbove ((norm ∘ D) '' (Complex.im ⁻¹' {(0 : ℝ)})) := by
      obtain ⟨M, hM⟩ := hDbdd
      refine ⟨M, ?_⟩
      rintro y ⟨w, hw, rfl⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw
      exact hM ⟨D w, ⟨w, ⟨le_of_eq hw.symm, by rw [hw]; exact hβ.le⟩, rfl⟩, rfl⟩
    have hbddb : BddAbove ((norm ∘ D) '' (Complex.im ⁻¹' {β})) := by
      obtain ⟨M, hM⟩ := hDbdd
      refine ⟨M, ?_⟩
      rintro y ⟨w, hw, rfl⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw
      exact hM ⟨D w, ⟨w, ⟨by rw [hw]; exact hβ.le, le_of_eq hw⟩, rfl⟩, rfl⟩
    -- Nonempty witnesses for the boundary-line images.
    have hmem0 : ‖D 0‖ ∈ (norm ∘ D) '' (Complex.im ⁻¹' {(0 : ℝ)}) :=
      ⟨0, by simp [Set.mem_preimage], rfl⟩
    have hmemb : ‖D (realToUpper β 0)‖ ∈ (norm ∘ D) '' (Complex.im ⁻¹' {β}) :=
      ⟨realToUpper β 0, by simp [Set.mem_preimage, realToUpper], rfl⟩
    -- Sups are nonneg (each element is a norm ≥ 0).
    have hS0nn : 0 ≤ S0 := le_trans (norm_nonneg _) (le_csSup hbdd0 hmem0)
    have hSbnn : 0 ≤ Sb := le_trans (norm_nonneg _) (le_csSup hbddb hmemb)
    -- Sups bounded above by X.
    have hS0le : S0 ≤ X := by
      apply csSup_le ⟨_, hmem0⟩
      rintro y ⟨w, hw, rfl⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw
      have hwre : w = realToLower w.re := by apply Complex.ext <;> simp [realToLower, hw]
      change ‖D w‖ ≤ X
      rw [hwre]; exact hlow w.re
    have hSble : Sb ≤ X := by
      apply csSup_le ⟨_, hmemb⟩
      rintro y ⟨w, hw, rfl⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw
      have hwre : w = realToUpper β w.re := by apply Complex.ext <;> simp [realToUpper, hw]
      change ‖D w‖ ≤ X
      rw [hwre]; exact hup w.re
    -- Hadamard interpolation bound.
    have hbound := Spectra.ThreeLines.hadamard_three_lines_horizontal D hβ hDholo hDcont hDbdd z hz
    rw [← hS0, ← hSb] at hbound
    -- exponents
    set th : ℝ := z.im / β with hth
    have hth_nn : 0 ≤ th := by rw [hth]; exact div_nonneg hz.1 hβ.le
    have hth_le : th ≤ 1 := by
      rw [hth, div_le_one hβ]; exact hz.2
    have hexp1 : (β - z.im) / β = 1 - th := by rw [hth]; field_simp
    rw [hexp1] at hbound
    -- S0^(1-th) ≤ X^(1-th), Sb^th ≤ X^th.
    have hpow1 : S0 ^ (1 - th) ≤ X ^ (1 - th) :=
      Real.rpow_le_rpow hS0nn hS0le (by linarith)
    have hpow2 : Sb ^ th ≤ X ^ th :=
      Real.rpow_le_rpow hSbnn hSble hth_nn
    calc ‖D z‖ ≤ S0 ^ (1 - th) * Sb ^ th := hbound
      _ ≤ X ^ (1 - th) * X ^ th :=
          mul_le_mul hpow1 hpow2 (Real.rpow_nonneg hSbnn _) (Real.rpow_nonneg hXnn _)
      _ = X ^ ((1 - th) + th) := (Real.rpow_add hXpos _ _).symm
      _ = X := by rw [show (1 - th) + th = 1 by ring, Real.rpow_one]

/-- **A3b: the limit KMS function for a general element `b`.** Approximate `b` by analytic elements
`bₙ → b`; the `kmsFunctionOfAnalytic`s `Fₙ` are uniformly Cauchy on the closed strip (by
`diff_bound` + Hadamard), so their limit is a KMS function for `(a, b)`. -/
noncomputable def limitKMSFunction (hβ : 0 < β) (hkmsIT : IsImaginaryTimeKMS ω α β) (a b : A) :
    KMSFunction ω α β a b := by
  -- 1. Analytic approximating sequence bₙ → b.
  have hdense := α.analyticElements_dense
  have hchoose : ∀ n : ℕ, ∃ c, c ∈ α.analyticElements ∧ ‖b - c‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨c, hc, hlt⟩ := hdense.exists_dist_lt b (by positivity : (0:ℝ) < 1 / ((n:ℝ)+1))
    exact ⟨c, hc, by rwa [dist_eq_norm] at hlt⟩
  choose bn hbn_mem hbn_lt using hchoose
  have hbn_an : ∀ n, α.IsAnalyticElement (bn n) := fun n => (α.mem_analyticElements).mp (hbn_mem n)
  -- bₙ → b.
  have hbn_tend : Tendsto bn atTop (nhds b) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [dist_comm, dist_eq_norm]; exact (hbn_lt n).le
  -- 2. The sequence of KMS functions and the constant C.
  set F : ℕ → ℂ → ℂ := fun n => (kmsFunctionOfAnalytic hkmsIT (hbn_an n) a).toFun with _hF
  set C : ℝ := ‖omegaL ω‖ * ‖a‖ with _hC
  have hCnn : 0 ≤ C := by positivity
  -- 3. Uniformly Cauchy on the closed strip.
  have hUC : UniformCauchySeqOn F atTop (ClosedStrip β) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    -- bₙ is Cauchy, so ‖bₙ - bₘ‖ → small.
    have hbnCauchy : CauchySeq bn := hbn_tend.cauchySeq
    -- Pick N so ‖bₙ - bₘ‖ < ε / (C+1).
    have hpos : 0 < ε / (C + 1) := by positivity
    rw [Metric.cauchySeq_iff] at hbnCauchy
    obtain ⟨N, hN⟩ := hbnCauchy (ε / (C + 1)) hpos
    refine ⟨N, fun m hm n hn x hx => ?_⟩
    rw [Complex.dist_eq]
    have hbnd := diff_bound hβ hkmsIT a (hbn_an m) (hbn_an n) hx
    have hdist : ‖bn m - bn n‖ < ε / (C + 1) := by
      have := hN m hm n hn; rwa [dist_eq_norm] at this
    calc ‖F m x - F n x‖ ≤ C * ‖bn m - bn n‖ := hbnd
      _ ≤ C * (ε / (C + 1)) :=
          mul_le_mul_of_nonneg_left hdist.le hCnn
      _ < ε := by
          rw [mul_div_assoc']
          rw [div_lt_iff₀ (by positivity : (0:ℝ) < C + 1)]
          nlinarith [hε.le, hCnn]
  -- 4. Pointwise limit f.
  have hlim : ∀ z ∈ ClosedStrip β, ∃ w, Tendsto (fun n => F n z) atTop (nhds w) := by
    intro z hz
    exact cauchySeq_tendsto_of_complete (hUC.cauchySeq hz)
  classical
  set f : ℂ → ℂ := fun z => if hz : z ∈ ClosedStrip β then (hlim z hz).choose else 0 with _hf_def
  have hf' : ∀ z (_hz : z ∈ ClosedStrip β), Tendsto (fun n => F n z) atTop (nhds (f z)) := by
    intro z hz
    have : f z = (hlim z hz).choose := dif_pos hz
    rw [this]
    exact (hlim z hz).choose_spec
  -- 5. Uniform convergence.
  have hTU : TendstoUniformlyOn F f atTop (ClosedStrip β) :=
    hUC.tendstoUniformlyOn_of_tendsto hf'
  -- 6. Assemble.
  refine
    { toFun := f
      holomorphic := ?_
      continuousOn := ?_
      bounded := ?_
      lower_boundary := ?_
      upper_boundary := ?_ }
  · -- holomorphic on the open strip
    have hU : IsOpen (Strip β) :=
      (isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const)
    have hTUstrip : TendstoUniformlyOn F f atTop (Strip β) :=
      hTU.mono (Strip_subset_ClosedStrip hβ)
    refine hTUstrip.tendstoLocallyUniformlyOn.differentiableOn ?_ hU
    exact Eventually.of_forall fun n => (kmsFunctionOfAnalytic hkmsIT (hbn_an n) a).holomorphic
  · -- continuous on the closed strip
    refine hTU.continuousOn ?_
    exact (Eventually.of_forall fun n =>
      (kmsFunctionOfAnalytic hkmsIT (hbn_an n) a).continuousOn).frequently
  · -- bounded on the closed strip
    have hTU1 : ∀ᶠ n in atTop, ∀ x ∈ ClosedStrip β, dist (f x) (F n x) < 1 := by
      have hmem : {p : ℂ × ℂ | dist p.1 p.2 < 1} ∈ uniformity ℂ :=
        Metric.dist_mem_uniformity one_pos
      simpa using hTU _ hmem
    obtain ⟨N, hN⟩ := hTU1.exists
    obtain ⟨M, hM⟩ := (kmsFunctionOfAnalytic hkmsIT (hbn_an N) a).bounded
    refine ⟨M + 1, ?_⟩
    rintro y ⟨w, ⟨z, hz, rfl⟩, rfl⟩
    have hdist : dist (f z) (F N z) < 1 := hN z hz
    have hFNle : ‖F N z‖ ≤ M := hM ⟨F N z, ⟨z, hz, rfl⟩, rfl⟩
    calc ‖f z‖ ≤ ‖F N z‖ + ‖f z - F N z‖ := by
          have := norm_add_le (F N z) (f z - F N z); simpa using this
      _ ≤ M + 1 := by
          rw [Complex.dist_eq] at hdist
          exact add_le_add hFNle hdist.le
  · -- lower boundary
    intro t
    have hmem : realToLower t ∈ ClosedStrip β := by
      refine ⟨?_, ?_⟩ <;> simp only [realToLower, ofReal_im, le_refl]
      · exact hβ.le
    have h1 : Tendsto (fun n => F n (realToLower t)) atTop (nhds (f (realToLower t))) :=
      hf' (realToLower t) hmem
    -- F n (realToLower t) = ω (a * α.evolve t (bn n))
    have hFeq : ∀ n, F n (realToLower t) = ω (a * α.evolve t (bn n)) := fun n =>
      (kmsFunctionOfAnalytic hkmsIT (hbn_an n) a).lower_boundary t
    have h2 : Tendsto (fun n => ω (a * α.evolve t (bn n))) atTop (nhds (ω (a * α.evolve t b))) := by
      have hev : Tendsto (fun n => α.evolve t (bn n)) atTop (nhds (α.evolve t b)) := by
        have := (α.evolveL t).continuous.tendsto b
        exact (this.comp hbn_tend).congr (fun n => by simp [Dynamics.evolveL_apply])
      have hmul : Tendsto (fun n => a * α.evolve t (bn n)) atTop (nhds (a * α.evolve t b)) :=
        (continuous_const_mul a).continuousAt.tendsto.comp hev
      exact ω.continuous.tendsto _ |>.comp hmul
    have h1' : Tendsto (fun n => ω (a * α.evolve t (bn n))) atTop (nhds (f (realToLower t))) := by
      refine h1.congr (fun n => ?_); rw [hFeq n]
    exact tendsto_nhds_unique h1' h2
  · -- upper boundary
    intro t
    have hmem : realToUpper β t ∈ ClosedStrip β := by
      refine ⟨?_, ?_⟩ <;> simp only [realToUpper, add_im, ofReal_im, mul_im, ofReal_re,
        I_im, mul_one, I_re, mul_zero, add_zero, zero_add]
      · exact le_of_lt hβ
      · rfl
    have h1 : Tendsto (fun n => F n (realToUpper β t)) atTop (nhds (f (realToUpper β t))) :=
      hf' (realToUpper β t) hmem
    have hFeq : ∀ n, F n (realToUpper β t) = ω (α.evolve t (bn n) * a) := fun n =>
      (kmsFunctionOfAnalytic hkmsIT (hbn_an n) a).upper_boundary t
    have h2 : Tendsto (fun n => ω (α.evolve t (bn n) * a)) atTop (nhds (ω (α.evolve t b * a))) := by
      have hev : Tendsto (fun n => α.evolve t (bn n)) atTop (nhds (α.evolve t b)) := by
        have := (α.evolveL t).continuous.tendsto b
        exact (this.comp hbn_tend).congr (fun n => by simp [Dynamics.evolveL_apply])
      have hmul : Tendsto (fun n => α.evolve t (bn n) * a) atTop (nhds (α.evolve t b * a)) :=
        (continuous_mul_const a).continuousAt.tendsto.comp hev
      exact ω.continuous.tendsto _ |>.comp hmul
    have h1' : Tendsto (fun n => ω (α.evolve t (bn n) * a)) atTop (nhds (f (realToUpper β t))) := by
      refine h1.congr (fun n => ?_); rw [hFeq n]
    exact tendsto_nhds_unique h1' h2

/-- **The equivalence of the strip and imaginary-time KMS conditions.** -/
theorem isKMSState_iff_imaginaryTime (hβ : 0 < β) :
    IsKMSState ω α β ↔ IsImaginaryTimeKMS ω α β := by
  constructor
  · intro hkms a b hb
    exact hkms.imaginaryTime hβ hb a
  · intro hkmsIT a b
    exact ⟨limitKMSFunction hβ hkmsIT a b⟩

end Spectra.KMS
