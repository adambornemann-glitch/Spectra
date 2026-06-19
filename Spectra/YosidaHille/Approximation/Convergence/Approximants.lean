/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.YosidaHille.Approximation.Convergence.JNegOperator

/-!
# Convergence of the Yosida approximants

The Yosida approximants `Aₙ`, `Aₙ⁻`, and the symmetric `Aₙˢʸᵐ` converge strongly to the generator
`A` on its domain. Each factors through the corresponding contraction (`Aₙφ = Jₙ(Aφ)`), so the
convergence `Jₙ → 1` lifts to `Aₙ → A`. The symmetric approximant is their average.

## Main statements

* `yosidaApprox_eq_J_comp_A` — `Aₙφ = Jₙ(Aφ)` for `φ ∈ D(A)`.
* `yosidaApprox_tendsto_on_domain` — `Aₙφ → Aφ` for `φ ∈ D(A)`.
* `yosidaApproxNeg_eq_JNeg_A` — `Aₙ⁻φ = Jₙ⁻(Aφ)` for `φ ∈ D(A)`.
* `yosidaApproxNeg_tendsto_on_domain` — `Aₙ⁻φ → Aφ` for `φ ∈ D(A)`.
* `yosidaApproxSym_eq_avg` — `Aₙˢʸᵐ = ½(Aₙ + Aₙ⁻)`.
* `yosidaApproxSym_tendsto_on_domain` — `Aₙˢʸᵐφ → Aφ` for `φ ∈ D(A)`.
* `yosidaApprox_commutes_resolvent` — `Aₙ` commutes with every resolvent.
-/
open Complex Filter Topology Spectra.Resolvent
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.YosidaHille.Approximation

/-- On the domain, `Aₙ` factors through `Jₙ`: `Aₙφ = Jₙ(Aφ)` for `φ ∈ D(A)`. -/
lemma yosidaApprox_eq_J_comp_A {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) (φ : H) (hφ : φ ∈ A.domain) :
    yosidaApprox hsym hplus hminus n φ = yosidaJ hsym hplus hminus n (A ⟨φ, hφ⟩) := by
  have hJ_eq := yosidaJ_eq_sub_resolvent_A hsym hplus hminus n φ hφ
  have hR_Aφ : Resolvent.resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus (A ⟨φ, hφ⟩)
             = φ + (I * (n : ℂ)) • Resolvent.resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus φ := by
    have h_rearrange : Resolvent.resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus (A ⟨φ, hφ⟩) =
             φ - (-I * (n : ℂ)) • Resolvent.resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus φ := by
      calc Resolvent.resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus (A ⟨φ, hφ⟩)
          = φ - (φ - Resolvent.resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus (A ⟨φ, hφ⟩)) := by
              rw [sub_sub_cancel]
        _ = φ - (-I * (n : ℂ)) • Resolvent.resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus φ := by
              rw [← hJ_eq]
    calc Resolvent.resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus (A ⟨φ, hφ⟩)
        = φ - (-I * (n : ℂ)) • Resolvent.resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus φ := h_rearrange
      _ = φ + -(-I * (n : ℂ)) • Resolvent.resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus φ := by
          rw [sub_eq_add_neg, neg_smul]
      _ = φ + (I * (n : ℂ)) • Resolvent.resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus φ := by
          congr 2
          ring
  have h_scalar : (-I * (n : ℂ)) * (I * (n : ℂ)) = (n : ℂ)^2 := by
    calc (-I * (n : ℂ)) * (I * (n : ℂ))
        = -I * I * (n : ℂ) * (n : ℂ) := by ring
      _ = -(I * I) * (n : ℂ)^2 := by ring
      _ = -(I^2) * (n : ℂ)^2 := by rw [sq I]
      _ = -(-1) * (n : ℂ)^2 := by rw [I_sq]
      _ = (n : ℂ)^2 := by ring
  symm
  unfold yosidaApprox yosidaJ
  simp only [resolventAtIn]
  calc (-I * (n : ℂ)) • Resolvent.resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus (A ⟨φ, hφ⟩)
      = (-I * (n : ℂ)) • (φ + (I * (n : ℂ)) • Resolvent.resolvent (I * (n : ℂ)) _ hsym hplus hminus φ) := by
          rw [hR_Aφ]
    _ = (-I * (n : ℂ)) • φ + (-I * (n : ℂ)) • ((I * (n : ℂ)) • Resolvent.resolvent (I * (n : ℂ)) _ hsym hplus hminus φ) := by
          rw [smul_add]
    _ = (-I * (n : ℂ)) • φ + ((-I * (n : ℂ)) * (I * (n : ℂ))) • Resolvent.resolvent (I * (n : ℂ)) _ hsym hplus hminus φ := by
          rw [smul_smul]
    _ = (-I * (n : ℂ)) • φ + ((n : ℂ)^2) • Resolvent.resolvent (I * (n : ℂ)) _ hsym hplus hminus φ := by
          rw [h_scalar]
    _ = ((n : ℂ)^2) • Resolvent.resolvent (I * (n : ℂ)) _ hsym hplus hminus φ + (-I * (n : ℂ)) • φ := by
          rw [add_comm]
    _ = ((n : ℂ)^2) • Resolvent.resolvent (I * (n : ℂ)) _ hsym hplus hminus φ - (I * (n : ℂ)) • φ := by
          rw [neg_mul, neg_smul, ← sub_eq_add_neg]

/-- `Aₙ` converges strongly to the generator on its domain: `Aₙφ → Aφ` for `φ ∈ D(A)`. -/
lemma yosidaApprox_tendsto_on_domain {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (h_dense : Dense (A.domain : Set H))
    (ψ : H) (hψ : ψ ∈ A.domain) :
    Tendsto (fun n : ℕ+ => yosidaApprox hsym hplus hminus n ψ) atTop (𝓝 (A ⟨ψ, hψ⟩)) := by
  simp only [fun n => yosidaApprox_eq_J_comp_A hsym hplus hminus n ψ hψ]
  exact yosida_J_tendsto_id hsym hplus hminus h_dense (A ⟨ψ, hψ⟩)

/-- On the domain, `Aₙ⁻` factors through `Jₙ⁻`: `Aₙ⁻φ = Jₙ⁻(Aφ)` for `φ ∈ D(A)`. -/
lemma yosidaApproxNeg_eq_JNeg_A {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) (φ : H) (hφ : φ ∈ A.domain) :
    yosidaApproxNeg hsym hplus hminus n φ = yosidaJNeg hsym hplus hminus n (A ⟨φ, hφ⟩) := by
  unfold yosidaApproxNeg yosidaJNeg resolventAtNegIn
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
             ContinuousLinearMap.id_apply]
  set R := Resolvent.resolvent (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus
  have h := yosidaJNeg_eq_sub_resolvent_A hsym hplus hminus n φ hφ
  have h_RAφ : R (A ⟨φ, hφ⟩) = φ - (I * (n : ℂ)) • R φ := by
    abel_nf
    simp_all only [neg_mul, Int.reduceNeg, neg_smul, one_smul, neg_sub, add_sub_cancel, R]
  have h_in_sq : (I * (n : ℂ)) * (I * (n : ℂ)) = -((n : ℂ)^2) := by
    calc (I * (n : ℂ)) * (I * (n : ℂ))
        = I * I * (n : ℂ) * (n : ℂ) := by ring
      _ = (-1) * (n : ℂ) * (n : ℂ) := by rw [I_mul_I]
      _ = -((n : ℂ)^2) := by ring
  symm
  calc (I * (n : ℂ)) • R (A ⟨φ, hφ⟩)
      = (I * (n : ℂ)) • (φ - (I * (n : ℂ)) • R φ) := by rw [h_RAφ]
    _ = (I * (n : ℂ)) • φ - (I * (n : ℂ)) • ((I * (n : ℂ)) • R φ) := smul_sub _ _ _
    _ = (I * (n : ℂ)) • φ - ((I * (n : ℂ)) * (I * (n : ℂ))) • R φ := by rw [smul_smul]
    _ = (I * (n : ℂ)) • φ - (-((n : ℂ)^2)) • R φ := by rw [h_in_sq]
    _ = (I * (n : ℂ)) • φ + (n : ℂ)^2 • R φ := by rw [neg_smul, sub_neg_eq_add]
    _ = (n : ℂ)^2 • R φ + (I * (n : ℂ)) • φ := by abel

/-- `Aₙ⁻` converges strongly to the generator on its domain: `Aₙ⁻φ → Aφ` for `φ ∈ D(A)`. -/
lemma yosidaApproxNeg_tendsto_on_domain {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (h_dense : Dense (A.domain : Set H))
    (φ : H) (hφ : φ ∈ A.domain) :
    Tendsto (fun n : ℕ+ => yosidaApproxNeg hsym hplus hminus n φ) atTop (𝓝 (A ⟨φ, hφ⟩)) := by
  have h_eq : ∀ n : ℕ+, yosidaApproxNeg hsym hplus hminus n φ = yosidaJNeg hsym hplus hminus n (A ⟨φ, hφ⟩) :=
    fun n => yosidaApproxNeg_eq_JNeg_A hsym hplus hminus n φ hφ
  simp_rw [h_eq]
  exact yosidaJNeg_tendsto_id hsym hplus hminus h_dense (A ⟨φ, hφ⟩)

/-- The symmetric approximant is the average of the two one-sided ones: `Aₙˢʸᵐ = ½(Aₙ + Aₙ⁻)`. -/
lemma yosidaApproxSym_eq_avg {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) :
    yosidaApproxSym hsym hplus hminus n = (1/2 : ℂ) • (yosidaApprox hsym hplus hminus n + yosidaApproxNeg hsym hplus hminus n) := by
  unfold yosidaApproxSym yosidaApprox yosidaApproxNeg resolventAtIn resolventAtNegIn
  ext ψ
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
             ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  set R_pos := resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus
  set R_neg := resolvent (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus
  have h : (1 / 2 : ℂ) * (n : ℂ)^2 = (n : ℂ)^2 / 2 := by ring
  calc ((n : ℂ)^2 / 2) • (R_pos ψ + R_neg ψ)
      = ((n : ℂ)^2 / 2) • R_pos ψ + ((n : ℂ)^2 / 2) • R_neg ψ := smul_add _ _ _
    _ = (1 / 2 : ℂ) • ((n : ℂ)^2 • R_pos ψ) + (1 / 2 : ℂ) • ((n : ℂ)^2 • R_neg ψ) := by
        simp only [smul_smul]; ring_nf
    _ = (1 / 2 : ℂ) • ((n : ℂ)^2 • R_pos ψ + (n : ℂ)^2 • R_neg ψ) := by rw [← smul_add]
    _ = (1 / 2 : ℂ) • ((n : ℂ)^2 • R_pos ψ - (I * (n : ℂ)) • ψ + ((n : ℂ)^2 • R_neg ψ + (I * (n : ℂ)) • ψ)) := by
        congr 1; abel

/-- `Aₙˢʸᵐ` converges strongly to the generator on its domain: `Aₙˢʸᵐφ → Aφ` for `φ ∈ D(A)`. -/
lemma yosidaApproxSym_tendsto_on_domain {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (h_dense : Dense (A.domain : Set H))
    (φ : H) (hφ : φ ∈ A.domain) :
    Tendsto (fun n : ℕ+ => yosidaApproxSym hsym hplus hminus n φ) atTop (𝓝 (A ⟨φ, hφ⟩)) := by
  have h_eq : ∀ n : ℕ+, yosidaApproxSym hsym hplus hminus n φ =
      (1/2 : ℂ) • (yosidaApprox hsym hplus hminus n φ + yosidaApproxNeg hsym hplus hminus n φ) := by
    intro n
    calc yosidaApproxSym hsym hplus hminus n φ
        = ((1/2 : ℂ) • (yosidaApprox hsym hplus hminus n + yosidaApproxNeg hsym hplus hminus n)) φ := by
            rw [yosidaApproxSym_eq_avg]
      _ = (1/2 : ℂ) • (yosidaApprox hsym hplus hminus n φ + yosidaApproxNeg hsym hplus hminus n φ) := by
            simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply]
  simp_rw [h_eq]
  have h_pos := yosidaApprox_tendsto_on_domain hsym hplus hminus h_dense φ hφ
  have h_neg := yosidaApproxNeg_tendsto_on_domain hsym hplus hminus h_dense φ hφ
  have h_sum : Tendsto (fun n : ℕ+ => yosidaApprox hsym hplus hminus n φ + yosidaApproxNeg hsym hplus hminus n φ)
      atTop (𝓝 (A ⟨φ, hφ⟩ + A ⟨φ, hφ⟩)) := h_pos.add h_neg
  have h_half : Tendsto (fun n : ℕ+ => (1/2 : ℂ) • (yosidaApprox hsym hplus hminus n φ + yosidaApproxNeg hsym hplus hminus n φ))
      atTop (𝓝 ((1/2 : ℂ) • (A ⟨φ, hφ⟩ + A ⟨φ, hφ⟩))) := h_sum.const_smul (1/2 : ℂ)
  have h_simp : (1/2 : ℂ) • (A ⟨φ, hφ⟩ + A ⟨φ, hφ⟩) = A ⟨φ, hφ⟩ := by
    rw [← two_smul ℂ (A ⟨φ, hφ⟩), smul_smul]
    norm_num
  rw [h_simp] at h_half
  exact h_half

/-- `Aₙ` commutes with every resolvent `R(z)` (`z` off the real axis). -/
lemma yosidaApprox_commutes_resolvent {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) (z : ℂ) (hz : z.im ≠ 0) :
    (yosidaApprox hsym hplus hminus n).comp (resolvent z hz hsym hplus hminus)
      = (resolvent z hz hsym hplus hminus).comp (yosidaApprox hsym hplus hminus n) := by
  have h_resolvent_comm : (resolventAtIn hsym hplus hminus n).comp (resolvent z hz hsym hplus hminus) =
                          (resolvent z hz hsym hplus hminus).comp (resolventAtIn hsym hplus hminus n) := by
    unfold resolventAtIn
    by_cases h_eq : I * (n : ℂ) = z
    · have hz' : (I * (n : ℂ)).im ≠ 0 := I_mul_pnat_im_ne_zero n
      have h_res_eq : resolvent (I * (n : ℂ)) hz' hsym hplus hminus = resolvent z hz hsym hplus hminus := by
        subst h_eq
        congr
      rw [h_res_eq]
    · have h_diff_ne : I * (n : ℂ) - z ≠ 0 := sub_ne_zero.mpr h_eq
      have h_diff_ne' : z - I * (n : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm h_eq)
      have h_id1 := resolvent_identity hsym hplus hminus (I * (n : ℂ)) z (I_mul_pnat_im_ne_zero n) hz
      have h_id2 := resolvent_identity hsym hplus hminus z (I * (n : ℂ)) hz (I_mul_pnat_im_ne_zero n)
      have h1 : (resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus).comp (resolvent z hz hsym hplus hminus) =
                (I * (n : ℂ) - z)⁻¹ • (resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus - resolvent z hz hsym hplus hminus) := by
        symm
        calc (I * (n : ℂ) - z)⁻¹ • (resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus - resolvent z hz hsym hplus hminus)
            = (I * (n : ℂ) - z)⁻¹ • ((I * (n : ℂ) - z) • (resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus).comp (resolvent z hz hsym hplus hminus)) := by
                rw [h_id1]
          _ = (resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus).comp (resolvent z hz hsym hplus hminus) := by
                rw [smul_smul, inv_mul_cancel₀ h_diff_ne, one_smul]
      have h2 : (resolvent z hz hsym hplus hminus).comp (resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus) =
                (z - I * (n : ℂ))⁻¹ • (resolvent z hz hsym hplus hminus - resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus) := by
        symm
        calc (z - I * (n : ℂ))⁻¹ • (resolvent z hz hsym hplus hminus - resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus)
            = (z - I * (n : ℂ))⁻¹ • ((z - I * (n : ℂ)) • (resolvent z hz hsym hplus hminus).comp (resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus)) := by
                rw [h_id2]
          _ = (resolvent z hz hsym hplus hminus).comp (resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus) := by
                rw [smul_smul, inv_mul_cancel₀ h_diff_ne', one_smul]
      rw [h1, h2]
      have h_inv_neg : (z - I * (n : ℂ))⁻¹ = -(I * (n : ℂ) - z)⁻¹ := by
        rw [← neg_sub, neg_inv]
      have h_sub_neg : resolvent z hz hsym hplus hminus - resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus =
                      -(resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus - resolvent z hz hsym hplus hminus) := by
        rw [neg_sub]
      rw [h_inv_neg, h_sub_neg, smul_neg, neg_smul, neg_neg]
  unfold yosidaApprox
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  rw [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
  congr 1
  unfold resolventAtIn
  simp only [resolventAtIn] at h_resolvent_comm
  rw [h_resolvent_comm]

end Spectra.YosidaHille.Approximation
