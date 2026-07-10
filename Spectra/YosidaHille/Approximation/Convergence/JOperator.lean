/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.YosidaHille.Approximation.Symmetry

/-!
# Convergence of the J operator

The contraction `Jₙ = -in·R(in)` converges strongly to the identity: first on the domain `D(A)`
(where `Jₙφ = φ - R(in)(Aφ)`), then on all of `H` by density together with the uniform bound
`‖Jₙ‖ ≤ 1`.

## Main statements

* `yosidaJ_eq_sub_resolvent_A` — `Jₙφ = φ - R(in)(Aφ)` for `φ ∈ D(A)`.
* `yosidaJ_tendsto_on_domain` — `Jₙφ → φ` for `φ ∈ D(A)`.
* `yosida_J_tendsto_id` — `Jₙψ → ψ` for all `ψ ∈ H`.
-/
open Complex Filter Topology Spectra.Resolvent
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.YosidaHille.Approximation

/-- On the domain, `Jₙ` splits off the resolvent of `Aφ`: `Jₙφ = φ - R(in)(Aφ)` for `φ ∈ D(A)`. -/
lemma yosidaJ_eq_sub_resolvent_A {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) (φ : H) (hφ : φ ∈ A.domain) :
    (-I * (n : ℂ)) • Resolvent.resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n)
        hsym hplus hminus φ =
      φ - Resolvent.resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus
        (A ⟨φ, hφ⟩) := by
  set z := I * (n : ℂ) with _hz_def
  set R := Resolvent.resolvent z (I_mul_pnat_im_ne_zero n) hsym hplus hminus with _hR_def
  have h_R_AzI : R (A ⟨φ, hφ⟩ - z • φ) = φ := by
    let ψ_sub : A.domain := Classical.choose (self_adjoint_range_all_z hsym hplus hminus z
                               (I_mul_pnat_im_ne_zero n) (A ⟨φ, hφ⟩ - z • φ)).exists
    have h_ψ_eq := Classical.choose_spec (self_adjoint_range_all_z hsym hplus hminus z
                    (I_mul_pnat_im_ne_zero n) (A ⟨φ, hφ⟩ - z • φ)).exists
    have h_subtype : (⟨φ, hφ⟩ : A.domain) = ψ_sub :=
      (self_adjoint_range_all_z hsym hplus hminus z (I_mul_pnat_im_ne_zero n)
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
  calc (-I * (n : ℂ)) • R φ
      = (-z) • R φ := by rw [neg_mul]
    _ = -(z • R φ) := by rw [neg_smul]
    _ = φ - (φ + z • R φ) := by abel
    _ = φ - R (A ⟨φ, hφ⟩) := by rw [← h_RAφ_explicit]

/-- On the domain, `Jₙ` converges strongly to the identity: `Jₙφ → φ` for `φ ∈ D(A)`. -/
lemma yosidaJ_tendsto_on_domain {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (φ : H) (hφ : φ ∈ A.domain) :
    Tendsto (fun n : ℕ+ => (-I * (n : ℂ)) •
              Resolvent.resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus φ)
            atTop (𝓝 φ) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_cases h_Aφ_zero : ‖A ⟨φ, hφ⟩‖ = 0
  · use 1
    intro n _
    rw [yosidaJ_eq_sub_resolvent_A hsym hplus hminus n φ hφ, norm_eq_zero.mp h_Aφ_zero]
    simp [dist_self, hε]
  · have _h_Aφ_pos : 0 < ‖A ⟨φ, hφ⟩‖ := (norm_nonneg _).lt_of_ne' h_Aφ_zero
    use ⟨Nat.ceil (‖A ⟨φ, hφ⟩‖ / ε) + 1, Nat.add_one_pos _⟩
    intro n hn
    have h_eq : dist ((-I * (n : ℂ)) • Resolvent.resolvent (I * (n : ℂ))
        (I_mul_pnat_im_ne_zero n) hsym hplus hminus φ) φ =
        ‖Resolvent.resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus
        (A ⟨φ, hφ⟩)‖ := by
      rw [dist_eq_norm, yosidaJ_eq_sub_resolvent_A hsym hplus hminus n φ hφ]
      simp [norm_neg]
    rw [h_eq]
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr n.pos
    calc ‖Resolvent.resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus
            (A ⟨φ, hφ⟩)‖
        ≤ ‖Resolvent.resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus‖ *
            ‖A ⟨φ, hφ⟩‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (1 / (n : ℝ)) * ‖A ⟨φ, hφ⟩‖ := by
          gcongr
          exact resolventAtIn_bound hsym hplus hminus n
      _ < ε := by
          rw [one_div, inv_mul_lt_iff₀ hn_pos]
          have h1 : (⌈‖A ⟨φ, hφ⟩‖ / ε⌉₊ + 1 : ℕ) ≤ n := hn
          calc ‖A ⟨φ, hφ⟩‖
              = (‖A ⟨φ, hφ⟩‖ / ε) * ε := by field_simp
            _ ≤ ↑⌈‖A ⟨φ, hφ⟩‖ / ε⌉₊ * ε := by gcongr; exact Nat.le_ceil _
            _ < (↑⌈‖A ⟨φ, hφ⟩‖ / ε⌉₊ + 1) * ε := by nlinarith
            _ ≤ (n : ℝ) * ε := by gcongr; exact_mod_cast h1

/-- By density and the bound `‖Jₙ‖ ≤ 1`, `Jₙ` converges strongly to the identity on all of `H`. -/
lemma yosida_J_tendsto_id {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (hdense : Dense (A.domain : Set H))
    (ψ : H) :
    Tendsto (fun n : ℕ+ => (-I * (n : ℂ)) •
              resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus ψ)
            atTop (𝓝 ψ) := by
  let J : ℕ+ → H →L[ℂ] H := fun n =>
    (-I * (n : ℂ)) • resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨φ, hφ_mem, hφ_close⟩ := Metric.mem_closure_iff.mp
    (hdense.closure_eq ▸ Set.mem_univ ψ) (ε / 3) (by linarith)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp
    (yosidaJ_tendsto_on_domain hsym hplus hminus φ hφ_mem)) (ε / 3) (by linarith)
  use N
  intro n hn
  calc dist (J n ψ) ψ
      ≤ dist (J n ψ) (J n φ) + dist (J n φ) φ + dist φ ψ :=
        dist_triangle4 _ _ _ _
    _ = ‖J n (ψ - φ)‖ + dist (J n φ) φ + dist φ ψ := by
        rw [dist_eq_norm, ContinuousLinearMap.map_sub]
    _ ≤ ‖J n‖ * ‖ψ - φ‖ + dist (J n φ) φ + dist φ ψ := by
        gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖ψ - φ‖ + dist (J n φ) φ + dist φ ψ := by
        gcongr; exact yosidaJ_norm_bound hsym hplus hminus n
    _ = dist ψ φ + dist (J n φ) φ + dist φ ψ := by
        rw [one_mul, ← dist_eq_norm]
    _ < ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact Metric.mem_ball.mp (hN n hn)
        · exact Metric.mem_ball'.mp hφ_close
    _ = ε := by ring

end Spectra.YosidaHille.Approximation
