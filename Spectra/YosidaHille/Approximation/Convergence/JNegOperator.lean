/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.YosidaHille.Approximation.Convergence.JOperator

/-!
# Convergence of the JNeg operator

The contraction `Jₙ⁻ = in·R(-in)` converges strongly to the identity: first on the domain `D(A)`
(where `Jₙ⁻φ = φ - R(-in)(Aφ)`), then on all of `H` by density and the uniform bound `‖Jₙ⁻‖ ≤ 1`.
This is the mirror of `JOperator` under `in ↔ -in`.

## Main statements

* `yosidaJNeg_eq_sub_resolvent_A` — `Jₙ⁻φ = φ - R(-in)(Aφ)` for `φ ∈ D(A)`.
* `yosidaJNeg_tendsto_on_domain` — `Jₙ⁻φ → φ` for `φ ∈ D(A)`.
* `yosidaJNeg_tendsto_id` — `Jₙ⁻ψ → ψ` for all `ψ ∈ H`.
-/
open Complex Filter Topology Spectra.Resolvent
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.YosidaHille.Approximation

/-- On the domain, `Jₙ⁻` splits off the resolvent of `Aφ`: `Jₙ⁻φ = φ - R(-in)(Aφ)` for
`φ ∈ D(A)`. -/
lemma yosidaJNeg_eq_sub_resolvent_A {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) (φ : H) (hφ : φ ∈ A.domain) :
    (I * (n : ℂ)) •
      Resolvent.resolvent (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus φ =
      φ - Resolvent.resolvent (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus
        (A ⟨φ, hφ⟩) := by
  set z := -I * (n : ℂ) with hz_def
  set R := Resolvent.resolvent z (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus with _hR_def
  have h_R_AzI : R (A ⟨φ, hφ⟩ - z • φ) = φ := by
    let ψ_sub : A.domain := Classical.choose (self_adjoint_range_all_z hsym hplus hminus z
                               (neg_I_mul_pnat_im_ne_zero n) (A ⟨φ, hφ⟩ - z • φ)).exists
    have h_ψ_eq := Classical.choose_spec (self_adjoint_range_all_z hsym hplus hminus z
                    (neg_I_mul_pnat_im_ne_zero n) (A ⟨φ, hφ⟩ - z • φ)).exists
    have h_subtype : (⟨φ, hφ⟩ : A.domain) = ψ_sub :=
      (self_adjoint_range_all_z hsym hplus hminus z (neg_I_mul_pnat_im_ne_zero n)
        (A ⟨φ, hφ⟩ - z • φ)).unique rfl h_ψ_eq
    calc R (A ⟨φ, hφ⟩ - z • φ)
        = ψ_sub.val := rfl
      _ = (⟨φ, hφ⟩ : A.domain).val := by rw [← h_subtype]
      _ = φ := rfl
  have h_R_linear : R (A ⟨φ, hφ⟩ - z • φ) = R (A ⟨φ, hφ⟩) - z • R φ := by
    calc R (A ⟨φ, hφ⟩ - z • φ)
        = R (A ⟨φ, hφ⟩) - R (z • φ) := by rw [R.map_sub]
      _ = R (A ⟨φ, hφ⟩) - z • R φ := by rw [R.map_smul]
  have h_RAφ_explicit : R (A ⟨φ, hφ⟩) = φ + z • R φ := by
    calc R (A ⟨φ, hφ⟩)
        = R (A ⟨φ, hφ⟩) - z • R φ + z • R φ := by abel
      _ = R (A ⟨φ, hφ⟩ - z • φ) + z • R φ := by rw [h_R_linear]
      _ = φ + z • R φ := by rw [h_R_AzI]
  calc (I * (n : ℂ)) • R φ
      = -((-I * (n : ℂ)) • R φ) := by simp only [neg_mul, neg_smul, neg_neg]
    _ = -(z • R φ) := by rw [hz_def]
    _ = φ - (φ + z • R φ) := by abel
    _ = φ - R (A ⟨φ, hφ⟩) := by rw [← h_RAφ_explicit]

/-- On the domain, `Jₙ⁻` converges strongly to the identity: `Jₙ⁻φ → φ` for `φ ∈ D(A)`. -/
lemma yosidaJNeg_tendsto_on_domain {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (φ : H) (hφ : φ ∈ A.domain) :
    Tendsto (fun n : ℕ+ => yosidaJNeg hsym hplus hminus n φ) atTop (𝓝 φ) := by
  unfold yosidaJNeg resolventAtNegIn
  have h_identity : ∀ n : ℕ+,
      (I * (n : ℂ)) •
        Resolvent.resolvent (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus φ =
      φ - Resolvent.resolvent (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus
        (A ⟨φ, hφ⟩) :=
    fun n => yosidaJNeg_eq_sub_resolvent_A hsym hplus hminus n φ hφ
  have h_tendsto :
      Tendsto (fun n : ℕ+ => φ - Resolvent.resolvent (-I * (n : ℂ))
        (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus (A ⟨φ, hφ⟩)) atTop (𝓝 φ) := by
    have h_to_zero :
        Tendsto (fun n : ℕ+ => Resolvent.resolvent (-I * (n : ℂ))
          (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus (A ⟨φ, hφ⟩)) atTop (𝓝 0) := by
      apply Metric.tendsto_atTop.mpr
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_gt (‖A ⟨φ, hφ⟩‖ / ε)
      use ⟨N + 1, Nat.succ_pos N⟩
      intro n hn
      rw [dist_eq_norm, sub_zero]
      have h_res_bound :
          ‖Resolvent.resolvent (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus‖ ≤
            1 / (n : ℝ) := by
        calc ‖Resolvent.resolvent (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus‖
            ≤ 1 / |(-I * (n : ℂ)).im| := resolvent_bound _ _ hsym hplus hminus
          _ = 1 / (n : ℝ) := by
              simp only [neg_mul, neg_im, mul_im, I_re, I_im, zero_mul, one_mul, zero_add]
              rw [div_eq_div_iff_comm, natCast_re, abs_neg, Nat.abs_cast]
      have hn_gt : (n : ℝ) > N := by
        have h : (N + 1 : ℕ) ≤ (n : ℕ) := hn
        exact_mod_cast Nat.lt_of_succ_le h
      calc
          ‖Resolvent.resolvent (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus
            (A ⟨φ, hφ⟩)‖
          ≤ ‖Resolvent.resolvent (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus‖ *
              ‖A ⟨φ, hφ⟩‖ :=
              ContinuousLinearMap.le_opNorm _ _
        _ ≤ (1 / (n : ℝ)) * ‖A ⟨φ, hφ⟩‖ :=
            mul_le_mul_of_nonneg_right h_res_bound (norm_nonneg _)
        _ = ‖A ⟨φ, hφ⟩‖ / (n : ℝ) := by ring
        _ < ε := by
              by_cases hAφ : ‖A ⟨φ, hφ⟩‖ = 0
              · rw [hAφ]; simp [hε]
              · have hAφ_pos : 0 < ‖A ⟨φ, hφ⟩‖ := (norm_nonneg _).lt_of_ne' hAφ
                have hN_pos : (0 : ℝ) < N := by
                  have : 0 < ‖A ⟨φ, hφ⟩‖ / ε := div_pos hAφ_pos hε
                  linarith
                calc ‖A ⟨φ, hφ⟩‖ / (n : ℝ)
                  < ‖A ⟨φ, hφ⟩‖ / N := div_lt_div_of_pos_left hAφ_pos hN_pos hn_gt
                _ ≤ ε := by
                      rw [div_le_iff₀ hN_pos]
                      calc ‖A ⟨φ, hφ⟩‖ = (‖A ⟨φ, hφ⟩‖ / ε) * ε := by field_simp
                        _ ≤ N * ε := mul_le_mul_of_nonneg_right (le_of_lt hN) (le_of_lt hε)
                      linarith
    have h_sub :
        Tendsto (fun n : ℕ+ => φ - Resolvent.resolvent (-I * (n : ℂ))
          (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus (A ⟨φ, hφ⟩)) atTop (𝓝 (φ - 0)) := by
      exact Filter.Tendsto.sub tendsto_const_nhds h_to_zero
    simp only [sub_zero] at h_sub
    exact h_sub
  exact h_tendsto.congr (fun n => (h_identity n).symm)

/-- By density and the bound `‖Jₙ⁻‖ ≤ 1`, `Jₙ⁻` converges strongly to the identity on all of `H`. -/
lemma yosidaJNeg_tendsto_id {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (h_dense : Dense (A.domain : Set H))
    (ψ : H) :
    Tendsto (fun n : ℕ+ => yosidaJNeg hsym hplus hminus n ψ) atTop (𝓝 ψ) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hε3 : ε / 3 > 0 := by linarith
  obtain ⟨φ, hφ_mem, hφ_close⟩ := Metric.mem_closure_iff.mp
    (h_dense.closure_eq ▸ Set.mem_univ ψ) (ε / 3) hε3
  rw [dist_eq_norm] at hφ_close
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp
    (yosidaJNeg_tendsto_on_domain hsym hplus hminus φ hφ_mem)) (ε / 3) hε3
  use N
  intro n hn
  rw [dist_eq_norm]
  calc ‖yosidaJNeg hsym hplus hminus n ψ - ψ‖
      = ‖(yosidaJNeg hsym hplus hminus n ψ - yosidaJNeg hsym hplus hminus n φ) +
         (yosidaJNeg hsym hplus hminus n φ - φ) + (φ - ψ)‖ := by abel_nf
    _ ≤ ‖yosidaJNeg hsym hplus hminus n ψ - yosidaJNeg hsym hplus hminus n φ‖ +
        ‖yosidaJNeg hsym hplus hminus n φ - φ‖ + ‖φ - ψ‖ := by
          calc _ ≤ ‖yosidaJNeg hsym hplus hminus n ψ - yosidaJNeg hsym hplus hminus n φ +
                    (yosidaJNeg hsym hplus hminus n φ - φ)‖ + ‖φ - ψ‖ := norm_add_le _ _
            _ ≤ _ := by gcongr; exact norm_add_le _ _
    _ = ‖yosidaJNeg hsym hplus hminus n (ψ - φ)‖ +
        ‖yosidaJNeg hsym hplus hminus n φ - φ‖ + ‖φ - ψ‖ := by
          congr 2; simp only [map_sub]
    _ ≤ ‖yosidaJNeg hsym hplus hminus n‖ * ‖ψ - φ‖ +
        ‖yosidaJNeg hsym hplus hminus n φ - φ‖ + ‖φ - ψ‖ := by
          gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖ψ - φ‖ + ‖yosidaJNeg hsym hplus hminus n φ - φ‖ + ‖φ - ψ‖ := by
          gcongr; exact yosidaJNeg_norm_bound hsym hplus hminus n
    _ = ‖ψ - φ‖ + ‖yosidaJNeg hsym hplus hminus n φ - φ‖ + ‖φ - ψ‖ := by ring
    _ < ε / 3 + ε / 3 + ε / 3 := by
          gcongr
          · exact mem_ball_iff_norm.mp (hN n hn)
          · rw [← dist_eq_norm, ← @Metric.mem_ball']
            exact mem_ball_iff_norm.mpr hφ_close
    _ = ε := by ring

end Spectra.YosidaHille.Approximation
