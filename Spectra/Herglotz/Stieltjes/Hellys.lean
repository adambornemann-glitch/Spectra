/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Data.Rat.Denumerable
import Mathlib.Topology.Sequences

/-!
# Helly's selection theorem

Helly's selection theorem: a sequence of uniformly bounded, monotone real functions
admits a subsequence converging pointwise on a countable dense set, and the limit of
that subsequence extends to a monotone function `G` on all of `ℝ` to which the
subsequence converges at every continuity point of `G`. The extracted limit is then
repackaged as a `StieltjesFunction` (and its associated Borel measure) via Mathlib's
`Monotone.stieltjesFunction`.

## Main definitions

* `hellyLimitMeasure`: the Borel measure induced by a monotone Helly limit `G`, via
  `Monotone.stieltjesFunction`.

## Main results

* `helly_selection`: the unanchored selection theorem — no value of the limit is fixed.
* `helly_selection'`: the anchored variant, additionally assuming (and concluding)
  `Fₙ 0 = 0` for all `n` (resp. `G 0 = 0`).
* `hellyLimitMeasure_Ioc`: the measure of `Set.Ioc a b` under `hellyLimitMeasure` is
  `G⁺(b) - G⁺(a)`, where `G⁺` is the right-continuous regularization of `G`.

## Implementation notes

The proof extracts a convergent subsequence on the rationals by viewing
`(Fₙ)_{q ∈ ℚ}` as a sequence in the compact product space `∏_{q ∈ ℚ} [0, M]`
(`isCompact_univ_pi`/`IsCompact.isSeqCompact`), then extends the rational limit `g`
to all of `ℝ` by right-continuous regularization, `G x := sInf (g '' {q : ℚ | x ≤ q})`.
Monotonicity of `G` and agreement with `g` on `ℚ` are immediate from this definition;
convergence of the subsequence at continuity points of `G` follows by squeezing `F (φ k) x`
between rational approximations from below and above.

## References

* P. Billingsley, *Probability and Measure*, 3rd ed., Theorem 25.9.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., §11.29 (Helly's selection principle).
-/

open Filter Topology
namespace Spectra.Herglotz

section HellySelection

/-- **Helly selection, unanchored.** Uniformly bounded, monotone `Fₙ` admit a
subsequence converging at every rational and at every continuity point of the
limit. No value is fixed at the origin.

`_hM` is logically redundant (it follows from `h_bnd 0 0`) and unused in the proof;
it is carried explicitly only for API symmetry with `helly_selection'`, whose `hM`
is genuinely load-bearing. -/
lemma helly_selection
    (F : ℕ → ℝ → ℝ) (M : ℝ) (_hM : 0 ≤ M)
    (h_mono : ∀ N, Monotone (F N))
    (h_bnd : ∀ N x, F N x ∈ Set.Icc (0 : ℝ) M) :
    ∃ (G : ℝ → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ Monotone G ∧
      (∀ x, G x ∈ Set.Icc (0 : ℝ) M) ∧
      (∀ q : ℚ, Tendsto (fun k => F (φ k) (q : ℝ)) atTop (𝓝 (G (q : ℝ)))) ∧
      (∀ x : ℝ, ContinuousAt G x →
        Tendsto (fun k => F (φ k) x) atTop (𝓝 (G x))) := by
  have hC : IsCompact (Set.univ.pi fun _ : ℚ => Set.Icc (0 : ℝ) M) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ n, (fun q : ℚ => F n (q : ℝ)) ∈ Set.univ.pi fun _ => Set.Icc (0:ℝ) M :=
    fun n q _ => h_bnd n (q : ℝ)
  obtain ⟨g, -, φ, hφ_mono, hφ_lim⟩ := hC.isSeqCompact hmem
  have h_rat_conv : ∀ q : ℚ, Tendsto (fun k => F (φ k) (q : ℝ)) atTop (𝓝 (g q)) :=
    fun q => (tendsto_pi_nhds.mp hφ_lim) q
  have hg_bnd : ∀ q : ℚ, g q ∈ Set.Icc (0 : ℝ) M := fun q =>
    ⟨ge_of_tendsto' (h_rat_conv q) fun k => (h_bnd (φ k) _).1,
     le_of_tendsto'  (h_rat_conv q) fun k => (h_bnd (φ k) _).2⟩
  have hg_mono : ∀ {q r : ℚ}, q ≤ r → g q ≤ g r := fun {q r} hqr =>
    le_of_tendsto_of_tendsto (h_rat_conv q) (h_rat_conv r)
      (Eventually.of_forall fun k => h_mono (φ k) (by exact_mod_cast hqr))
  set S : ℝ → Set ℝ := fun x => g '' {q : ℚ | x ≤ (q : ℝ)} with _hS
  have hS_ne  : ∀ x, (S x).Nonempty := fun x => by
    obtain ⟨q, hq⟩ := exists_rat_gt x; exact ⟨g q, q, hq.le, rfl⟩
  have hS_bdd : ∀ x, BddBelow (S x) := fun x =>
    ⟨0, by rintro _ ⟨q, _, rfl⟩; exact (hg_bnd q).1⟩
  set G : ℝ → ℝ := fun x => sInf (S x) with _hG
  have hG_rat : ∀ q : ℚ, G (q : ℝ) = g q := fun q =>
  le_antisymm (csInf_le (hS_bdd _) ⟨q, Set.mem_setOf.mpr le_rfl, rfl⟩)
    (le_csInf (hS_ne _) (by rintro _ ⟨r, hr, rfl⟩; exact hg_mono (by exact_mod_cast hr)))
  have hG_mono : Monotone G := fun x y hxy =>
    le_csInf (hS_ne _) (by
      rintro _ ⟨r, hr, rfl⟩; exact csInf_le (hS_bdd _) ⟨r, le_trans hxy hr, rfl⟩)
  have hG_bnd : ∀ x, G x ∈ Set.Icc (0 : ℝ) M := fun x =>
    ⟨le_csInf (hS_ne _) (by rintro _ ⟨r, _, rfl⟩; exact (hg_bnd r).1),
     by obtain ⟨q, hq⟩ := exists_rat_gt x
        exact le_trans (csInf_le (hS_bdd _) ⟨q, hq.le, rfl⟩) (hg_bnd q).2⟩
  refine ⟨G, φ, hφ_mono, hG_mono, hG_bnd, fun q => by rw [hG_rat q]; exact h_rat_conv q, ?_⟩
  intro x hx
  refine tendsto_order.mpr ⟨fun c hc => ?_, fun c hc => ?_⟩
  · -- hc : c < G x.  Seat a rational a < x with c < g a, then sandwich from below.
    have hnhds : ∀ᶠ y in 𝓝 x, c < G y :=
      Filter.Tendsto.eventually hx (eventually_gt_nhds hc)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp hnhds
    obtain ⟨a, ha₁, ha₂⟩ := exists_rat_btwn (show x - δ < x by linarith)
    have hca : c < g a := by
      have h := hδ' (show dist (a : ℝ) x < δ by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
      rwa [hG_rat a] at h
    filter_upwards [Filter.Tendsto.eventually (h_rat_conv a) (eventually_gt_nhds hca)]
      with k hk
    exact lt_of_lt_of_le hk (h_mono (φ k) ha₂.le)
  · -- hc : G x < c.  Seat a rational b > x with g b < c, then sandwich from above.
    have hnhds : ∀ᶠ y in 𝓝 x, G y < c :=
      Filter.Tendsto.eventually hx (eventually_lt_nhds hc)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp hnhds
    obtain ⟨b, hb₁, hb₂⟩ := exists_rat_btwn (show x < x + δ by linarith)
    have hcb : g b < c := by
      have h := hδ' (show dist (b : ℝ) x < δ by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
      rwa [hG_rat b] at h
    filter_upwards [Filter.Tendsto.eventually (h_rat_conv b) (eventually_lt_nhds hcb)]
      with k hk
    exact lt_of_le_of_lt (h_mono (φ k) hb₁.le) hk

/-- **Helly's selection lemma** for distribution functions on `[0, 2π]`.
  Given a sequence of monotone functions `F_N : ℝ → ℝ` with
  `0 ≤ F_N(x) ≤ M` for all `N, x`, there exists a subsequence converging
  pointwise at all points of a countable dense set. -/
theorem helly_selection'
    (F : ℕ → ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (h_mono : ∀ N, Monotone (F N))
    (h_bnd : ∀ N x, F N x ∈ Set.Icc (0 : ℝ) M)
    (h_zero : ∀ N, F N 0 = 0) :
    ∃ (G : ℝ → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ Monotone G ∧ G 0 = 0 ∧
      (∀ x, G x ∈ Set.Icc (0 : ℝ) M) ∧
      (∀ q : ℚ, Tendsto (fun k => F (φ k) (q : ℝ)) atTop (𝓝 (G (q : ℝ)))) ∧
      (∀ x : ℝ, ContinuousAt G x →
        Tendsto (fun k => F (φ k) x) atTop (𝓝 (G x))) := by
  obtain ⟨G, φ, hφ, hGmono, hGbnd, hGrat, hGcont⟩ := helly_selection F M hM h_mono h_bnd
  refine ⟨G, φ, hφ, hGmono, ?_, hGbnd, hGrat, hGcont⟩
  have h0 := hGrat 0
  simp only [Rat.cast_zero, h_zero] at h0
  exact tendsto_nhds_unique h0 tendsto_const_nhds

open MeasureTheory in
/-- Given the Helly limit `G` (monotone, bounded), produce a
`StieltjesFunction` and its associated measure.

The key: `Monotone.stieltjesFunction` right-regularizes `G` and
packages it as a `StieltjesFunction`. Then `.measure` gives the
Borel measure. -/
noncomputable def hellyLimitMeasure (G : ℝ → ℝ) (h_mono : Monotone G) :
    Measure ℝ :=
  (h_mono.stieltjesFunction).measure

/-- The Stieltjes measure satisfies `μ(Ioc a b) = ofReal (G⁺(b) - G⁺(a))`, where
`G⁺ = h_mono.stieltjesFunction` is the right-continuous regularization of `G`.

At a continuity point `x` of `G`, `G⁺ x = G x`, so this recovers the familiar
`μ(Ioc a b) = G(b) - G(a)` whenever `a` and `b` are both continuity points of `G`. -/
lemma hellyLimitMeasure_Ioc (G : ℝ → ℝ) (h_mono : Monotone G)
    (a b : ℝ) :
    (hellyLimitMeasure G h_mono) (Set.Ioc a b) =
    ENNReal.ofReal (h_mono.stieltjesFunction b - h_mono.stieltjesFunction a) :=
  StieltjesFunction.measure_Ioc _ a b

end HellySelection

end Spectra.Herglotz
