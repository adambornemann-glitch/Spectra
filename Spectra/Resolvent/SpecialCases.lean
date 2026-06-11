/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Spectral/Resolvent/SpecialCases.lean
-/
import Spectra.Resolvent.NormExpansion
/-!
# Resolvent at ±i

This file constructs the resolvent operators at `z = ±i` directly from the
self-adjointness criterion. These special cases are used to bootstrap the
general resolvent construction.

## Main definitions

* `resolvent_at_i`: The resolvent `R(i) = (A - iI)⁻¹`
* `resolvent_at_neg_i`: The resolvent `R(-i) = (A + iI)⁻¹`

## Main statements

* `resolvent_at_i_unique`: Solutions to `(A - iI)ψ = φ` are unique
* `resolvent_at_neg_i_unique`: Solutions to `(A + iI)ψ = φ` are unique
* `resolvent_at_i_bound`: `‖R(i)‖ ≤ 1`

## Implementation notes

The self-adjointness criterion states that `ran(A ± iI) = H`. We use
`Classical.choose` to extract solutions and prove they are unique using
the lower bound estimate from `NormExpansion`.
-/
open InnerProductSpace MeasureTheory Complex Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Spectra.Resolvent
/-! ## Resolvent at i -/

lemma resolvent_at_i_spec {A : H →ₗ.[ℂ] H}
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (φ : H) :
    ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ := hminus φ

lemma resolvent_at_i_unique {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (φ ψ₁ ψ₂ : H)
    (hψ₁ : ψ₁ ∈ A.domain) (hψ₂ : ψ₂ ∈ A.domain)
    (h₁ : A ⟨ψ₁, hψ₁⟩ - I • ψ₁ = φ)
    (h₂ : A ⟨ψ₂, hψ₂⟩ - I • ψ₂ = φ) :
    ψ₁ = ψ₂ := by
  have h_sub_mem : ψ₁ - ψ₂ ∈ A.domain := A.domain.sub_mem hψ₁ hψ₂
  have h_factor : A ⟨ψ₁ - ψ₂, h_sub_mem⟩ - I • (ψ₁ - ψ₂) = 0 := by
    have op_sub := A.map_sub ⟨ψ₁, hψ₁⟩ ⟨ψ₂, hψ₂⟩
    calc A ⟨ψ₁ - ψ₂, h_sub_mem⟩ - I • (ψ₁ - ψ₂)
        = (A ⟨ψ₁, hψ₁⟩ - A ⟨ψ₂, hψ₂⟩) - I • (ψ₁ - ψ₂) :=
          congrFun (congrArg HSub.hSub op_sub) (I • (ψ₁ - ψ₂))
      _ = (A ⟨ψ₁, hψ₁⟩ - A ⟨ψ₂, hψ₂⟩) - (I • ψ₁ - I • ψ₂) := by rw [smul_sub]
      _ = (A ⟨ψ₁, hψ₁⟩ - I • ψ₁) - (A ⟨ψ₂, hψ₂⟩ - I • ψ₂) := by abel
      _ = φ - φ := by rw [h₁, h₂]
      _ = 0 := sub_self φ
  have h_le := norm_le_norm_sub_I_smul hsym ⟨ψ₁ - ψ₂, h_sub_mem⟩
  simp only at h_le
  have : ‖ψ₁ - ψ₂‖ ≤ 0 := by
    calc ‖ψ₁ - ψ₂‖
        ≤ ‖A ⟨ψ₁ - ψ₂, h_sub_mem⟩ - I • (ψ₁ - ψ₂)‖ := h_le
      _ = ‖(0 : H)‖ := by rw [h_factor]
      _ = 0 := norm_zero
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm this (norm_nonneg _)))

/-- The minus-resolvent solution `(A - iI)⁻¹ φ`, as a bare vector in `H`. -/
noncomputable def Rminus {A : H →ₗ.[ℂ] H}
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (φ : H) : H :=
  ↑(Classical.choose (hminus φ))

lemma Rminus_mem {A : H →ₗ.[ℂ] H}
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (φ : H) :
    Rminus hminus φ ∈ A.domain :=
  (Classical.choose (hminus φ)).property

lemma Rminus_eq {A : H →ₗ.[ℂ] H}
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (φ : H) :
    A ⟨Rminus hminus φ, Rminus_mem hminus φ⟩ - I • Rminus hminus φ = φ :=
  Classical.choose_spec (hminus φ)

/-- The resolvent at `z = i`, `R(i) = (A - iI)⁻¹`, built from the
self-adjointness criterion. -/
noncomputable def resolvent_at_i {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) : H →L[ℂ] H where
  toFun φ := Rminus hminus φ
  map_add' φ₁ φ₂ := by
    set a := Rminus hminus φ₁
    set b := Rminus hminus φ₂
    have m₁ : a ∈ A.domain := Rminus_mem hminus φ₁
    have m₂ : b ∈ A.domain := Rminus_mem hminus φ₂
    have e₁ : A ⟨a, m₁⟩ - I • a = φ₁ := Rminus_eq hminus φ₁
    have e₂ : A ⟨b, m₂⟩ - I • b = φ₂ := Rminus_eq hminus φ₂
    have m_add : a + b ∈ A.domain := A.domain.add_mem m₁ m₂
    have e_add : A ⟨a + b, m_add⟩ - I • (a + b) = φ₁ + φ₂ := by
      have op_add := A.map_add ⟨a, m₁⟩ ⟨b, m₂⟩
      calc A ⟨a + b, m_add⟩ - I • (a + b)
          = (A ⟨a, m₁⟩ + A ⟨b, m₂⟩) - I • (a + b) :=
            congrFun (congrArg HSub.hSub op_add) (I • (a + b))
        _ = (A ⟨a, m₁⟩ + A ⟨b, m₂⟩) - (I • a + I • b) := by rw [smul_add]
        _ = (A ⟨a, m₁⟩ - I • a) + (A ⟨b, m₂⟩ - I • b) := by abel
        _ = φ₁ + φ₂ := by rw [e₁, e₂]
    exact (resolvent_at_i_unique hsym (φ₁ + φ₂) (a + b) (Rminus hminus (φ₁ + φ₂))
      m_add (Rminus_mem hminus (φ₁ + φ₂)) e_add (Rminus_eq hminus (φ₁ + φ₂))).symm
  map_smul' c φ := by
    set a := Rminus hminus φ
    have m : a ∈ A.domain := Rminus_mem hminus φ
    have e : A ⟨a, m⟩ - I • a = φ := Rminus_eq hminus φ
    have m_smul : c • a ∈ A.domain := A.domain.smul_mem c m
    have e_smul : A ⟨c • a, m_smul⟩ - I • (c • a) = c • φ := by
      have op_smul := A.map_smul c ⟨a, m⟩
      calc A ⟨c • a, m_smul⟩ - I • (c • a)
          = c • A ⟨a, m⟩ - I • (c • a) :=
            congrFun (congrArg HSub.hSub op_smul) (I • (c • a))
        _ = c • A ⟨a, m⟩ - c • (I • a) := by rw [smul_comm]
        _ = c • (A ⟨a, m⟩ - I • a) := by rw [smul_sub]
        _ = c • φ := by rw [e]
    exact (resolvent_at_i_unique hsym (c • φ) (c • a) (Rminus hminus (c • φ))
      m_smul (Rminus_mem hminus (c • φ)) e_smul (Rminus_eq hminus (c • φ))).symm
  cont := by
    have lipschitz : LipschitzWith 1 (fun φ => Rminus hminus φ) := by
      refine LipschitzWith.of_edist_le fun φ₁ φ₂ => ?_
      set a := Rminus hminus φ₁
      set b := Rminus hminus φ₂
      have m₁ : a ∈ A.domain := Rminus_mem hminus φ₁
      have m₂ : b ∈ A.domain := Rminus_mem hminus φ₂
      have e₁ : A ⟨a, m₁⟩ - I • a = φ₁ := Rminus_eq hminus φ₁
      have e₂ : A ⟨b, m₂⟩ - I • b = φ₂ := Rminus_eq hminus φ₂
      have m_sub : a - b ∈ A.domain := A.domain.sub_mem m₁ m₂
      have e_sub : A ⟨a - b, m_sub⟩ - I • (a - b) = φ₁ - φ₂ := by
        have op_sub := A.map_sub ⟨a, m₁⟩ ⟨b, m₂⟩
        calc A ⟨a - b, m_sub⟩ - I • (a - b)
            = (A ⟨a, m₁⟩ - A ⟨b, m₂⟩) - I • (a - b) :=
              congrFun (congrArg HSub.hSub op_sub) (I • (a - b))
          _ = (A ⟨a, m₁⟩ - A ⟨b, m₂⟩) - (I • a - I • b) := by rw [smul_sub]
          _ = (A ⟨a, m₁⟩ - I • a) - (A ⟨b, m₂⟩ - I • b) := by abel
          _ = φ₁ - φ₂ := by rw [e₁, e₂]
      have h_le := norm_le_norm_sub_I_smul hsym ⟨a - b, m_sub⟩
      have bound : ‖a - b‖ ≤ ‖φ₁ - φ₂‖ := by
        calc ‖a - b‖
            ≤ ‖A ⟨a - b, m_sub⟩ - I • (a - b)‖ := h_le
          _ = ‖φ₁ - φ₂‖ := by rw [e_sub]
      rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
      exact ENNReal.ofReal_le_ofReal bound
    exact lipschitz.continuous

/-! ## Resolvent at -i -/

lemma resolvent_at_neg_i_unique {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (φ ψ₁ ψ₂ : H)
    (hψ₁ : ψ₁ ∈ A.domain) (hψ₂ : ψ₂ ∈ A.domain)
    (h₁ : A ⟨ψ₁, hψ₁⟩ + I • ψ₁ = φ)
    (h₂ : A ⟨ψ₂, hψ₂⟩ + I • ψ₂ = φ) :
    ψ₁ = ψ₂ := by
  have h_sub_mem : ψ₁ - ψ₂ ∈ A.domain := A.domain.sub_mem hψ₁ hψ₂
  have h_factor : A ⟨ψ₁ - ψ₂, h_sub_mem⟩ + I • (ψ₁ - ψ₂) = 0 := by
    have op_sub := A.map_sub ⟨ψ₁, hψ₁⟩ ⟨ψ₂, hψ₂⟩
    calc A ⟨ψ₁ - ψ₂, h_sub_mem⟩ + I • (ψ₁ - ψ₂)
        = (A ⟨ψ₁, hψ₁⟩ - A ⟨ψ₂, hψ₂⟩) + I • (ψ₁ - ψ₂) :=
          congrFun (congrArg HAdd.hAdd op_sub) (I • (ψ₁ - ψ₂))
      _ = (A ⟨ψ₁, hψ₁⟩ - A ⟨ψ₂, hψ₂⟩) + (I • ψ₁ - I • ψ₂) := by rw [smul_sub]
      _ = (A ⟨ψ₁, hψ₁⟩ + I • ψ₁) - (A ⟨ψ₂, hψ₂⟩ + I • ψ₂) := by abel
      _ = φ - φ := by rw [h₁, h₂]
      _ = 0 := sub_self φ
  have h_le := norm_le_norm_add_I_smul hsym ⟨ψ₁ - ψ₂, h_sub_mem⟩
  simp only at h_le
  have : ‖ψ₁ - ψ₂‖ ≤ 0 := by
    calc ‖ψ₁ - ψ₂‖
        ≤ ‖A ⟨ψ₁ - ψ₂, h_sub_mem⟩ + I • (ψ₁ - ψ₂)‖ := h_le
      _ = ‖(0 : H)‖ := by rw [h_factor]
      _ = 0 := norm_zero
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm this (norm_nonneg _)))

/-- The plus-resolvent solution `(A + iI)⁻¹ φ`, as a bare vector in `H`. -/
noncomputable def Rplus {A : H →ₗ.[ℂ] H}
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (φ : H) : H :=
  ↑(Classical.choose (hplus φ))

lemma Rplus_mem {A : H →ₗ.[ℂ] H}
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (φ : H) :
    Rplus hplus φ ∈ A.domain :=
  (Classical.choose (hplus φ)).property

lemma Rplus_eq {A : H →ₗ.[ℂ] H}
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (φ : H) :
    A ⟨Rplus hplus φ, Rplus_mem hplus φ⟩ + I • Rplus hplus φ = φ :=
  Classical.choose_spec (hplus φ)

/-- The resolvent at `z = -i`, `R(-i) = (A + iI)⁻¹`, built from the
self-adjointness criterion. -/
noncomputable def resolvent_at_neg_i {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) : H →L[ℂ] H where
  toFun φ := Rplus hplus φ
  map_add' φ₁ φ₂ := by
    set a := Rplus hplus φ₁
    set b := Rplus hplus φ₂
    have m₁ : a ∈ A.domain := Rplus_mem hplus φ₁
    have m₂ : b ∈ A.domain := Rplus_mem hplus φ₂
    have e₁ : A ⟨a, m₁⟩ + I • a = φ₁ := Rplus_eq hplus φ₁
    have e₂ : A ⟨b, m₂⟩ + I • b = φ₂ := Rplus_eq hplus φ₂
    have m_add : a + b ∈ A.domain := A.domain.add_mem m₁ m₂
    have e_add : A ⟨a + b, m_add⟩ + I • (a + b) = φ₁ + φ₂ := by
      have op_add := A.map_add ⟨a, m₁⟩ ⟨b, m₂⟩
      calc A ⟨a + b, m_add⟩ + I • (a + b)
          = (A ⟨a, m₁⟩ + A ⟨b, m₂⟩) + I • (a + b) :=
            congrFun (congrArg HAdd.hAdd op_add) (I • (a + b))
        _ = (A ⟨a, m₁⟩ + A ⟨b, m₂⟩) + (I • a + I • b) := by rw [smul_add]
        _ = (A ⟨a, m₁⟩ + I • a) + (A ⟨b, m₂⟩ + I • b) := by abel
        _ = φ₁ + φ₂ := by rw [e₁, e₂]
    exact (resolvent_at_neg_i_unique hsym (φ₁ + φ₂) (a + b) (Rplus hplus (φ₁ + φ₂))
      m_add (Rplus_mem hplus (φ₁ + φ₂)) e_add (Rplus_eq hplus (φ₁ + φ₂))).symm
  map_smul' c φ := by
    set a := Rplus hplus φ
    have m : a ∈ A.domain := Rplus_mem hplus φ
    have e : A ⟨a, m⟩ + I • a = φ := Rplus_eq hplus φ
    have m_smul : c • a ∈ A.domain := A.domain.smul_mem c m
    have e_smul : A ⟨c • a, m_smul⟩ + I • (c • a) = c • φ := by
      have op_smul := A.map_smul c ⟨a, m⟩
      calc A ⟨c • a, m_smul⟩ + I • (c • a)
          = c • A ⟨a, m⟩ + I • (c • a) :=
            congrFun (congrArg HAdd.hAdd op_smul) (I • (c • a))
        _ = c • A ⟨a, m⟩ + c • (I • a) := by rw [smul_comm]
        _ = c • (A ⟨a, m⟩ + I • a) := by rw [smul_add]
        _ = c • φ := by rw [e]
    exact (resolvent_at_neg_i_unique hsym (c • φ) (c • a) (Rplus hplus (c • φ))
      m_smul (Rplus_mem hplus (c • φ)) e_smul (Rplus_eq hplus (c • φ))).symm
  cont := by
    have lipschitz : LipschitzWith 1 (fun φ => Rplus hplus φ) := by
      refine LipschitzWith.of_edist_le fun φ₁ φ₂ => ?_
      set a := Rplus hplus φ₁
      set b := Rplus hplus φ₂
      have m₁ : a ∈ A.domain := Rplus_mem hplus φ₁
      have m₂ : b ∈ A.domain := Rplus_mem hplus φ₂
      have e₁ : A ⟨a, m₁⟩ + I • a = φ₁ := Rplus_eq hplus φ₁
      have e₂ : A ⟨b, m₂⟩ + I • b = φ₂ := Rplus_eq hplus φ₂
      have m_sub : a - b ∈ A.domain := A.domain.sub_mem m₁ m₂
      have e_sub : A ⟨a - b, m_sub⟩ + I • (a - b) = φ₁ - φ₂ := by
        have op_sub := A.map_sub ⟨a, m₁⟩ ⟨b, m₂⟩
        calc A ⟨a - b, m_sub⟩ + I • (a - b)
            = (A ⟨a, m₁⟩ - A ⟨b, m₂⟩) + I • (a - b) :=
              congrFun (congrArg HAdd.hAdd op_sub) (I • (a - b))
          _ = (A ⟨a, m₁⟩ - A ⟨b, m₂⟩) + (I • a - I • b) := by rw [smul_sub]
          _ = (A ⟨a, m₁⟩ + I • a) - (A ⟨b, m₂⟩ + I • b) := by abel
          _ = φ₁ - φ₂ := by rw [e₁, e₂]
      have h_le := norm_le_norm_add_I_smul hsym ⟨a - b, m_sub⟩
      have bound : ‖a - b‖ ≤ ‖φ₁ - φ₂‖ := by
        calc ‖a - b‖
            ≤ ‖A ⟨a - b, m_sub⟩ + I • (a - b)‖ := h_le
          _ = ‖φ₁ - φ₂‖ := by rw [e_sub]
      rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
      exact ENNReal.ofReal_le_ofReal bound
    exact lipschitz.continuous

/-! ## Bounds -/

lemma resolvent_at_i_bound {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) :
    ‖resolvent_at_i hsym hminus‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro φ
  let ψ := resolvent_at_i hsym hminus φ
  have h_mem : ψ ∈ A.domain := Rminus_mem hminus φ
  have h_eq : A ⟨ψ, h_mem⟩ - I • ψ = φ := Rminus_eq hminus φ
  have h_le := norm_le_norm_sub_I_smul hsym ⟨ψ, h_mem⟩
  simp only at h_le
  calc ‖resolvent_at_i hsym hminus φ‖ = ‖ψ‖ := rfl
    _ ≤ ‖A ⟨ψ, h_mem⟩ - I • ψ‖ := h_le
    _ = ‖φ‖ := by rw [h_eq]
    _ = 1 * ‖φ‖ := by ring

lemma resolvent_at_neg_i_bound {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) :
    ‖resolvent_at_neg_i hsym hplus‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro φ
  let ψ := resolvent_at_neg_i hsym hplus φ
  have h_mem : ψ ∈ A.domain := Rplus_mem hplus φ
  have h_eq : A ⟨ψ, h_mem⟩ + I • ψ = φ := Rplus_eq hplus φ
  have h_le := norm_le_norm_add_I_smul hsym ⟨ψ, h_mem⟩
  simp only at h_le
  calc ‖resolvent_at_neg_i hsym hplus φ‖ = ‖ψ‖ := rfl
    _ ≤ ‖A ⟨ψ, h_mem⟩ + I • ψ‖ := h_le
    _ = ‖φ‖ := by rw [h_eq]
    _ = 1 * ‖φ‖ := by ring


/-! ## Left inverse property -/

lemma resolvent_at_neg_i_left_inverse {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (ψ : H) (hψ : ψ ∈ A.domain) :
    resolvent_at_neg_i hsym hplus (A ⟨ψ, hψ⟩ + I • ψ) = ψ := by
  set φ := A ⟨ψ, hψ⟩ + I • ψ
  set χ := resolvent_at_neg_i hsym hplus φ
  have hχ_mem : χ ∈ A.domain := Rplus_mem hplus φ
  have hχ_eq : A ⟨χ, hχ_mem⟩ + I • χ = φ := Rplus_eq hplus φ
  exact resolvent_at_neg_i_unique hsym φ χ ψ hχ_mem hψ hχ_eq rfl

lemma resolvent_at_i_left_inverse {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (ψ : H) (hψ : ψ ∈ A.domain) :
    resolvent_at_i hsym hminus (A ⟨ψ, hψ⟩ - I • ψ) = ψ := by
  set φ := A ⟨ψ, hψ⟩ - I • ψ
  set χ := resolvent_at_i hsym hminus φ
  have hχ_mem : χ ∈ A.domain := Rminus_mem hminus φ
  have hχ_eq : A ⟨χ, hχ_mem⟩ - I • χ = φ := Rminus_eq hminus φ
  exact resolvent_at_i_unique hsym φ χ ψ hχ_mem hψ hχ_eq rfl

end Spectra.Resolvent
