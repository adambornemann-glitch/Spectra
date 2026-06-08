/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: SpectralTheory/HerglotzTheorem/Stieltjes/Hellys.lean
-/
import Spectra.Herglotz.Stieltjes.CumulativeDistFun
import Spectra.PositiveDefinite.Defs
import Mathlib.Data.Rat.Denumerable

open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Herglotz

/-! ### Helly's selection lemma (via diagonal extraction) -/

section HellySelection

/-- **Helly's selection lemma** for distribution functions on `[0, 2π]`.
  Given a sequence of monotone functions `F_N : ℝ → ℝ` with
  `0 ≤ F_N(x) ≤ M` for all `N, x`, there exists a subsequence converging
  pointwise at all points of a countable dense set. -/
lemma helly_selection
    (F : ℕ → ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (h_mono : ∀ N, Monotone (F N))
    (h_bnd : ∀ N x, F N x ∈ Set.Icc 0 M)
    (h_zero : ∀ N, F N 0 = 0) :        -- ADDED: needed for `G 0 = 0` (see note)
    ∃ (G : ℝ → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      Monotone G ∧
      G 0 = 0 ∧
      (∀ x, G x ∈ Set.Icc 0 M) ∧
      (∀ q : ℚ, Tendsto (fun k => F (φ k) ↑q) atTop (𝓝 (G ↑q))) ∧
      (∀ x : ℝ, ContinuousAt G x →
        Tendsto (fun k => F (φ k) x) atTop (𝓝 (G x))) := by
  classical
  -- enumerate ℚ
  set e : ℚ ≃ ℕ := Denumerable.eqv ℚ with he
  set xarr : ℕ → ℕ → ℝ := fun n k => F k ((e.symm n : ℝ)) with hxarr
  have hbnd' : ∀ n k, xarr n k ∈ Set.Icc (-M) M := by
    intro n k
    simp only [hxarr]
    rw [Set.mem_Icc]
    have h := h_bnd k ((e.symm n : ℝ))
    rw [Set.mem_Icc] at h
    exact ⟨by linarith [h.1, hM], h.2⟩
  obtain ⟨L, φ, hφ_mono, hL⟩ :=
    coordinatewise_convergent_subseq xarr (fun _ => M) (fun _ => hM) hbnd'
  -- limit at rationals
  set Lq : ℚ → ℝ := fun q => L (e q) with hLq_def
  have hconv_rat : ∀ q : ℚ, Tendsto (fun k => F (φ k) (q : ℝ)) atTop (𝓝 (Lq q)) := by
    intro q
    have h := hL (e q)
    have hrw : (fun k => xarr (e q) (φ k)) = (fun k => F (φ k) (q : ℝ)) := by
      funext k; simp only [hxarr, Equiv.symm_apply_apply]
    rw [hrw] at h
    exact h
  have hLq_mem : ∀ q : ℚ, Lq q ∈ Set.Icc 0 M := fun q =>
    isClosed_Icc.mem_of_tendsto (hconv_rat q)
      (Eventually.of_forall (fun k => h_bnd (φ k) (q : ℝ)))
  have hLq_mono : ∀ {q₁ q₂ : ℚ}, q₁ ≤ q₂ → Lq q₁ ≤ Lq q₂ := by
    intro q₁ q₂ hq
    exact le_of_tendsto_of_tendsto (hconv_rat q₁) (hconv_rat q₂)
      (Eventually.of_forall (fun k => h_mono (φ k) (by exact_mod_cast hq)))
  have hLq_zero : Lq 0 = 0 := by
    have hc : Tendsto (fun k => F (φ k) ((0 : ℚ) : ℝ)) atTop (𝓝 (0 : ℝ)) := by
      have hfun : (fun k => F (φ k) ((0 : ℚ) : ℝ)) = (fun _ => (0 : ℝ)) := by
        funext k; rw [Rat.cast_zero, h_zero (φ k)]
      rw [hfun]; exact tendsto_const_nhds
    exact tendsto_nhds_unique (hconv_rat 0) hc
  -- left-regularization
  set S : ℝ → Set ℝ := fun x => Lq '' {q : ℚ | (q : ℝ) ≤ x} with hS
  set G : ℝ → ℝ := fun x => sSup (S x) with hG
  have hS_nonempty : ∀ x, (S x).Nonempty := by
    intro x
    obtain ⟨q, hq⟩ := exists_rat_lt x
    exact ⟨Lq q, q, le_of_lt hq, rfl⟩
  have hS_bddAbove : ∀ x, BddAbove (S x) := by
    intro x
    refine ⟨M, ?_⟩
    rintro r ⟨q, _, rfl⟩
    exact (hLq_mem q).2
  have hS_nonneg : ∀ x, ∀ r ∈ S x, 0 ≤ r := by
    rintro x r ⟨q, _, rfl⟩
    exact (hLq_mem q).1
  have hG_mem : ∀ x, G x ∈ Set.Icc 0 M := by
    intro x
    rw [Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · obtain ⟨r, hr⟩ := hS_nonempty x
      exact le_trans (hS_nonneg x r hr) (le_csSup (hS_bddAbove x) hr)
    · exact csSup_le (hS_nonempty x) (by rintro r ⟨q, _, rfl⟩; exact (hLq_mem q).2)
  have hG_mono : Monotone G := by
    intro x y hxy
    exact csSup_le_csSup (hS_bddAbove y) (hS_nonempty x)
      (by rintro r ⟨q, hq, rfl⟩; exact ⟨q, le_trans hq hxy, rfl⟩)
  have hG_rat : ∀ q₀ : ℚ, G (q₀ : ℝ) = Lq q₀ := by
    intro q₀
    apply le_antisymm
    · exact csSup_le (hS_nonempty _)
        (by rintro r ⟨q, hq, rfl⟩; exact hLq_mono (by exact_mod_cast hq))
    · refine le_csSup (hS_bddAbove _) ⟨q₀, ?_, rfl⟩
      simp only [Rat.cast_le, Set.mem_setOf_eq, le_refl]
  have hG_zero : G 0 = 0 := by
    have h := hG_rat 0
    rw [Rat.cast_zero] at h
    rw [h, hLq_zero]
  have hrat : ∀ q : ℚ, Tendsto (fun k => F (φ k) (↑q)) atTop (𝓝 (G ↑q)) := by
    intro q; rw [hG_rat q]; exact hconv_rat q
  -- convergence at continuity points
  have hG_cont_conv : ∀ x : ℝ, ContinuousAt G x →
      Tendsto (fun k => F (φ k) x) atTop (𝓝 (G x)) := by
    intro x hx_cont
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hδ_prop⟩ := (Metric.continuousAt_iff.mp hx_cont) (ε / 2) (by linarith)
    obtain ⟨q₂, hq₂_lo, hq₂_hi⟩ := exists_rat_btwn (show x < x + δ by linarith)
    obtain ⟨q₁, hq₁_lo, hq₁_hi⟩ := exists_rat_btwn (show x - δ < x by linarith)
    have hdist₂ : dist ((q₂ : ℝ)) x < δ := by
      rw [Real.dist_eq, abs_lt]; exact ⟨by linarith, by linarith⟩
    have hdist₁ : dist ((q₁ : ℝ)) x < δ := by
      rw [Real.dist_eq, abs_lt]; exact ⟨by linarith, by linarith⟩
    have hd₂ := hδ_prop hdist₂
    have hd₁ := hδ_prop hdist₁
    have hc₁ : Tendsto (fun k => F (φ k) ((q₁ : ℝ))) atTop (𝓝 (G ↑q₁)) := by
      rw [hG_rat q₁]; exact hconv_rat q₁
    have hc₂ : Tendsto (fun k => F (φ k) ((q₂ : ℝ))) atTop (𝓝 (G ↑q₂)) := by
      rw [hG_rat q₂]; exact hconv_rat q₂
    rw [Metric.tendsto_atTop] at hc₁ hc₂
    obtain ⟨N₁, hN₁⟩ := hc₁ (ε / 2) (by linarith)
    obtain ⟨N₂, hN₂⟩ := hc₂ (ε / 2) (by linarith)
    refine ⟨max N₁ N₂, fun k hk => ?_⟩
    have e₁ := hN₁ k (le_of_max_le_left hk)
    have e₂ := hN₂ k (le_of_max_le_right hk)
    have hsand₁ : F (φ k) ((q₁ : ℝ)) ≤ F (φ k) x := h_mono (φ k) (le_of_lt hq₁_hi)
    have hsand₂ : F (φ k) x ≤ F (φ k) ((q₂ : ℝ)) := h_mono (φ k) (le_of_lt hq₂_lo)
    rw [Real.dist_eq, abs_lt] at e₁ e₂ hd₁ hd₂
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [e₁.1, hd₁.1, hsand₁], by linarith [e₂.2, hd₂.2, hsand₂]⟩
  exact ⟨G, φ, hφ_mono, hG_mono, hG_zero, hG_mem, hrat, hG_cont_conv⟩

end HellySelection

end Spectra.Herglotz
