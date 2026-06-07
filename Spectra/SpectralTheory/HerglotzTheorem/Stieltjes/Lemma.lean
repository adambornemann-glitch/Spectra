/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: SpectralTheory/HerglotzTheorem/Stieltjes/Lemma.lean
-/
import Spectra.SpectralTheory.HerglotzTheorem.Stieltjes.IntegralConv
import Mathlib.MeasureTheory.Measure.Stieltjes

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace

namespace QuantumMechanics.SpectralTheory.HerglotzStieltjes

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


/-! ### Herglotz's lemma (Stieltjes version) -/

section HerglotzStieltjes

variable (U : H →L[ℂ] H) --(hU : Cayley.Unitary U)

-- stieltjes_rightLim_const:
private lemma stieltjes_rightLim_const {F : ℝ → ℝ} (hF : Monotone F) {a M : ℝ}
    (hconst : ∀ x, a < x → F x = M) :          -- was a ≤ x
    Function.rightLim F a = M := by
  have htend : Tendsto F (𝓝[>] a) (𝓝 M) := by
    have heq : F =ᶠ[𝓝[>] a] (fun _ => M) := by
      filter_upwards [self_mem_nhdsWithin] with y hy using hconst y hy   -- was (le_of_lt hy)
    rw [Filter.tendsto_congr' heq]; exact tendsto_const_nhds
  exact tendsto_nhds_unique (hF.tendsto_rightLim a) htend

/-- **Herglotz's lemma** -/
lemma herglotz_lemma_stieltjes
    (c : ℤ → ℂ)  -- the correlation sequence c(n) = ⟨ψ, U^n ψ⟩
    (M : ℝ) (hM : 0 ≤ M)  -- M = ‖ψ‖²
    (_c_zero : c 0 = ↑M)
    -- Fejér CDFs and their properties:
    (F : ℕ → ℝ → ℝ)
    (h_mono : ∀ N, Monotone (F N))
    (h_bnd : ∀ N x, F N x ∈ Set.Icc 0 M)
    (h_zero : ∀ N, F N 0 = 0)
    (h_top : ∀ N, F N (2 * Real.pi) = M)
    -- Fourier property of Fejér CDFs:
    (h_fourier : ∀ N (n : ℤ),
      ∫ θ in Set.Icc 0 (2 * Real.pi),
        exp (I * n * θ) ∂((h_mono N).stieltjesFunction.measure) =
      (c n * (fejerWeight N n : ℂ))) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧
      μ (Set.Icc 0 (2 * Real.pi))ᶜ = 0 ∧
      (∀ n : ℤ, ∫ θ in Set.Icc 0 (2 * Real.pi), exp (I * n * θ) ∂μ = c n) := by
  -- Step 1: Helly selection
  obtain ⟨G, φ, hφ, h_mono_G, h_G_zero, h_G_bnd, _h_rat_conv, h_cont_conv⟩ :=
    helly_selection F M hM h_mono h_bnd h_zero
  have hFconst : ∀ N (y : ℝ), 2 * Real.pi ≤ y → F N y = M := fun N y hy =>
    le_antisymm (h_bnd N y).2 ((h_top N) ▸ h_mono N hy)
  have hG_left : ∀ x ≤ (0 : ℝ), G x = 0 := fun x hx =>
    le_antisymm (h_G_zero ▸ h_mono_G hx) (h_G_bnd x).1
  have hG_right : ∀ x, 2 * Real.pi < x → G x = M := by
    intro x hx
    refine le_antisymm (h_G_bnd x).2 ?_
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hx
    have hGq : G (q : ℝ) = M := by
      have hconst : ∀ k, F (φ k) (q : ℝ) = M := fun k => hFconst (φ k) q (le_of_lt hq1)
      refine tendsto_nhds_unique (_h_rat_conv q) ?_
      simp_rw [hconst]; exact tendsto_const_nhds
    calc M = G (q : ℝ) := hGq.symm
      _ ≤ G x := h_mono_G (le_of_lt hq2)
  -- Step 2: Build the Stieltjes measure
  set μ := hellyLimitMeasure G h_mono_G with hμ_def
  -- the Helly limit measure is the Stieltjes measure of G
  have hμ_eq : μ = h_mono_G.stieltjesFunction.measure := hμ_def
  -- Stieltjes function vanishes on the left, equals M on the right
  have hsf_left : ∀ y < (0 : ℝ), h_mono_G.stieltjesFunction y = 0 := by
    intro y hy
    rw [h_mono_G.stieltjesFunction_eq]
    refine le_antisymm ?_ ?_
    · have hr : Function.rightLim G y ≤ G (y / 2) := h_mono_G.rightLim_le (by linarith)
      rwa [hG_left (y / 2) (by linarith)] at hr
    · rw [← hG_left y (le_of_lt hy)]; exact h_mono_G.le_rightLim (le_refl y)
  have hsf_right : ∀ y, 2 * Real.pi < y → h_mono_G.stieltjesFunction y = M := by
    intro y hy
    rw [h_mono_G.stieltjesFunction_eq]
    refine le_antisymm ?_ ?_
    · rw [← hG_right (y + 1) (by linarith)]; exact h_mono_G.rightLim_le (by linarith)
    · rw [← hG_right y hy]; exact h_mono_G.le_rightLim (le_refl y)
  have hsf2pi : h_mono_G.stieltjesFunction (2 * Real.pi) = M := by
    rw [h_mono_G.stieltjesFunction_eq]; exact stieltjes_rightLim_const h_mono_G hG_right
  have hsf_atBot : Tendsto (h_mono_G.stieltjesFunction) atBot (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_lt_atBot (0 : ℝ)] with y hy using (hsf_left y hy).symm
  have hsf_atTop : Tendsto (h_mono_G.stieltjesFunction) atTop (𝓝 M) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (2 * Real.pi)] with y hy using (hsf_right y hy).symm
  -- Step 3: finiteness  (total mass = ofReal (M - 0) < ∞)
  have hμ_finite : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [hμ_eq, h_mono_G.stieltjesFunction.measure_univ hsf_atBot hsf_atTop]
    exact ENNReal.ofReal_lt_top
  -- Step 4: support
  have hμ_supp : μ (Set.Icc 0 (2 * Real.pi))ᶜ = 0 := by
    have hsplit : (Set.Icc 0 (2 * Real.pi))ᶜ = Set.Iio 0 ∪ Set.Ioi (2 * Real.pi) := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi,
        not_and_or, not_le]
    rw [hμ_eq, hsplit]
    refine measure_union_null ?_ ?_
    · rw [h_mono_G.stieltjesFunction.measure_Iio hsf_atBot 0,
        stieltjes_leftLim_zero h_mono_G hG_left, sub_zero, ENNReal.ofReal_zero]
    · rw [h_mono_G.stieltjesFunction.measure_Ioi hsf_atTop (2 * Real.pi), hsf2pi, sub_self,
        ENNReal.ofReal_zero]
  -- Step 5: Verify Fourier coefficients
  have hμ_fourier : ∀ n : ℤ,
      ∫ θ in Set.Icc 0 (2 * Real.pi), exp (I * n * θ) ∂μ = c n := by
    intro n
    -- The Fourier integral of σ_{φ(k)} converges to that of μ:
    have h_lhs := fourier_integral_tendsto_of_cdf_tendsto F G φ
      h_mono h_mono_G M hM h_bnd h_G_bnd h_cont_conv
      (fun N => ⟨h_zero N, fun x hx => hFconst N x (le_of_lt hx)⟩)
      ⟨h_G_zero, hG_right⟩
      n
    -- The Fourier integral of σ_{φ(k)} equals w_{φ(k)}(n) · c(n):
    have h_rhs : Tendsto
        (fun k => (fejerWeight (φ k) n : ℂ) * c n)
        atTop (𝓝 (c n)) := by
      conv_rhs => rw [← one_mul (c n)]
      exact (fejerWeight_tendsto_complex n |>.comp hφ.tendsto_atTop).mul
        tendsto_const_nhds
    -- The two limits agree:
    have h_eq_seq : ∀ k,
        ∫ θ in Set.Icc 0 (2 * Real.pi),
          exp (I * n * θ) ∂((h_mono (φ k)).stieltjesFunction.measure)
          = (fejerWeight (φ k) n : ℂ) * c n := by
      intro k;
      rw [h_fourier (φ k) n, mul_comm]
    exact tendsto_nhds_unique (h_lhs.congr h_eq_seq) h_rhs
  exact ⟨μ, hμ_finite, hμ_supp, hμ_fourier⟩

end HerglotzStieltjes

end QuantumMechanics.SpectralTheory.HerglotzStieltjes
