/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Resolvent/Identities.lean
-/
import Spectra.Resolvent.Range
/-!
# Resolvent Identities

This file proves the fundamental algebraic identities satisfied by the resolvent:
* The resolvent identity: `R(z) - R(w) = (z - w) R(z) R(w)`
* The adjoint relation: `R(z)* = R(z̄)`

## Main definitions

* `resolventFun`: The resolvent as a function on `OffRealAxis`

## Main statements

* `resolvent_identity`: `R(z) - R(w) = (z - w) R(z) R(w)`
* `resolvent_adjoint`: `R(z)* = R(z̄)`
* `resolventFun_bound`: `‖R(z)‖ ≤ 1/|Im(z)|` (wrapper)
* `resolventFun_identity`: Resolvent identity for `resolventFun`
* `resolventFun_adjoint`: Adjoint relation for `resolventFun`

-/
open InnerProductSpace MeasureTheory Complex Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Resolvent

/-- The resolvent identity: `R(z) - R(w) = (z - w) R(z) R(w)`. -/
lemma resolvent_identity {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    resolvent z hz hsym hplus hminus - resolvent w hw hsym hplus hminus =
    (z - w) • ((resolvent z hz hsym hplus hminus).comp (resolvent w hw hsym hplus hminus)) := by
  ext φ
  let ψ_w_sub : A.domain := Classical.choose (self_adjoint_range_all_z hsym hplus hminus w hw φ).exists
  let ψ_w := (ψ_w_sub : H)
  have h_w_domain : ψ_w ∈ A.domain := ψ_w_sub.property
  have h_w_eq : A ψ_w_sub - w • ψ_w = φ :=
    Classical.choose_spec (self_adjoint_range_all_z hsym hplus hminus w hw φ).exists
  let ψ_z_sub : A.domain := Classical.choose (self_adjoint_range_all_z hsym hplus hminus z hz φ).exists
  let ψ_z := (ψ_z_sub : H)
  have h_z_domain : ψ_z ∈ A.domain := ψ_z_sub.property
  have h_z_eq : A ψ_z_sub - z • ψ_z = φ :=
    Classical.choose_spec (self_adjoint_range_all_z hsym hplus hminus z hz φ).exists
  let η_sub : A.domain := Classical.choose (self_adjoint_range_all_z hsym hplus hminus z hz ψ_w).exists
  let η := (η_sub : H)
  have h_η_domain : η ∈ A.domain := η_sub.property
  have h_η_eq : A η_sub - z • η = ψ_w :=
    Classical.choose_spec (self_adjoint_range_all_z hsym hplus hminus z hz ψ_w).exists
  have h_Rz : resolvent z hz hsym hplus hminus φ = ψ_z := rfl
  have h_Rw : resolvent w hw hsym hplus hminus φ = ψ_w := rfl
  have h_Rz_ψw : resolvent z hz hsym hplus hminus ψ_w = η := rfl
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
             ContinuousLinearMap.comp_apply]
  rw [h_Rz, h_Rw, h_Rz_ψw]
  have h_Az_ψw : A ⟨ψ_w, h_w_domain⟩ - z • ψ_w = φ + (w - z) • ψ_w := by
    have h_Aw : A ⟨ψ_w, h_w_domain⟩ = φ + w • ψ_w := by
      have h_eq : A ⟨ψ_w, h_w_domain⟩ = A ψ_w_sub := rfl
      calc A ⟨ψ_w, h_w_domain⟩
          = (A ψ_w_sub - w • ψ_w) + w • ψ_w := by abel
        _ = φ + w • ψ_w := by rw [h_w_eq]
    calc A ⟨ψ_w, h_w_domain⟩ - z • ψ_w
        = (φ + w • ψ_w) - z • ψ_w := by rw [h_Aw]
      _ = φ + (w - z) • ψ_w := by rw [sub_smul]; abel
  have h_sum_domain : ψ_z + (w - z) • η ∈ A.domain := by
    apply A.domain.add_mem h_z_domain
    exact A.domain.smul_mem (w - z) h_η_domain
  have h_sum_eq : A ⟨ψ_z + (w - z) • η, h_sum_domain⟩ -
      z • (ψ_z + (w - z) • η) = φ + (w - z) • ψ_w := by
    have op_add := A.map_add ψ_z_sub ((w - z) • η_sub)
    have h_smul_mem : (w - z) • η ∈ A.domain := A.domain.smul_mem (w - z) h_η_domain
    have op_eq : A ⟨ψ_z + (w - z) • η, h_sum_domain⟩ =
                 A ψ_z_sub + A ⟨(w - z) • η, h_smul_mem⟩ := by
      convert op_add using 1
    have op_smul := A.map_smul (w - z) η_sub
    have op_smul_eq : A ⟨(w - z) • η, h_smul_mem⟩ = (w - z) • A η_sub := by
      convert op_smul using 1
    calc A ⟨ψ_z + (w - z) • η, h_sum_domain⟩ - z • (ψ_z + (w - z) • η)
        = (A ψ_z_sub + A ⟨(w - z) • η, h_smul_mem⟩) - z • (ψ_z + (w - z) • η) :=
            by rw [op_eq]
      _ = (A ψ_z_sub + (w - z) • A η_sub) - z • (ψ_z + (w - z) • η) :=
            by rw [op_smul_eq]
      _ = (A ψ_z_sub + (w - z) • A η_sub) - (z • ψ_z + z • ((w - z) • η)) :=
            by rw [smul_add]
      _ = (A ψ_z_sub - z • ψ_z) + ((w - z) • A η_sub - z • ((w - z) • η)) := by abel
      _ = (A ψ_z_sub - z • ψ_z) + ((w - z) • A η_sub - (w - z) • (z • η)) :=
            by rw [smul_comm z (w - z) η]
      _ = (A ψ_z_sub - z • ψ_z) + (w - z) • (A η_sub - z • η) := by rw [← smul_sub]
      _ = φ + (w - z) • ψ_w := by rw [h_z_eq, h_η_eq]
  let target := φ + (w - z) • ψ_w
  have h_ψw_solves : A ⟨ψ_w, h_w_domain⟩ - z • ψ_w = target := h_Az_ψw
  have h_sum_solves : A ⟨ψ_z + (w - z) • η, h_sum_domain⟩ -
      z • (ψ_z + (w - z) • η) = target := h_sum_eq
  have h_eq_vals : ψ_w = ψ_z + (w - z) • η := by
    have h1 : (⟨ψ_w, h_w_domain⟩ : A.domain) =
        (⟨ψ_z + (w - z) • η, h_sum_domain⟩ : A.domain) :=
      (self_adjoint_range_all_z hsym hplus hminus z hz target).unique h_ψw_solves h_sum_solves
    exact congrArg Subtype.val h1
  calc ψ_z - ψ_w
      = ψ_z - (ψ_z + (w - z) • η) := by rw [h_eq_vals]
    _ = -((w - z) • η) := by abel
    _ = (-(w - z)) • η := by rw [neg_smul]
    _ = (z - w) • η := by abel_nf


/-- Strong-operator continuity of the resolvent in `z` off the real axis.

If `zn → z` in `ℂ` with all `(zn n).im ≠ 0` and `z.im ≠ 0`, then
`resolvent (zn n) ξ → resolvent z ξ` for every `ξ : H`. -/
lemma resolvent_tendsto {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    {z : ℂ} (hz : z.im ≠ 0)
    {zn : ℕ → ℂ} (h_im_ne : ∀ n, (zn n).im ≠ 0)
    (h_lim : Tendsto zn atTop (𝓝 z)) (ξ : H) :
    Tendsto (fun n => resolvent (zn n) (h_im_ne n) hsym hplus hminus ξ) atTop
            (𝓝 (resolvent z hz hsym hplus hminus ξ)) := by
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  -- Pointwise bound: ‖R(zn)ξ - R(z)ξ‖ ≤ ‖zn - z‖ · (1/|(zn).im|) · ‖R(z)ξ‖.
  have hbound : ∀ n,
      ‖resolvent (zn n) (h_im_ne n) hsym hplus hminus ξ
          - resolvent z hz hsym hplus hminus ξ‖
        ≤ ‖zn n - z‖ * (1 / |(zn n).im|)
            * ‖resolvent z hz hsym hplus hminus ξ‖ := by
    intro n
    have hid := resolvent_identity hsym hplus hminus (zn n) z (h_im_ne n) hz
    -- Apply both sides of the resolvent identity to ξ.
    have happ :
        resolvent (zn n) (h_im_ne n) hsym hplus hminus ξ
            - resolvent z hz hsym hplus hminus ξ
          = (zn n - z) • resolvent (zn n) (h_im_ne n) hsym hplus hminus
                            (resolvent z hz hsym hplus hminus ξ) := by
      have hh := congrArg (fun T : H →L[ℂ] H => T ξ) hid
      simpa [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
             ContinuousLinearMap.comp_apply] using hh
    have hop := resolvent_bound hsym hplus hminus (zn n) (h_im_ne n)
    rw [happ, norm_smul]
    calc ‖zn n - z‖ * ‖resolvent (zn n) (h_im_ne n) hsym hplus hminus
                          (resolvent z hz hsym hplus hminus ξ)‖
        ≤ ‖zn n - z‖ * (‖resolvent (zn n) (h_im_ne n) hsym hplus hminus‖
              * ‖resolvent z hz hsym hplus hminus ξ‖) := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖zn n - z‖ * ((1 / |(zn n).im|)
              * ‖resolvent z hz hsym hplus hminus ξ‖) := by gcongr
      _ = ‖zn n - z‖ * (1 / |(zn n).im|)
            * ‖resolvent z hz hsym hplus hminus ξ‖ := by ring
  -- The bound tends to 0: factor by factor.
  refine squeeze_zero (fun _ => norm_nonneg _) hbound ?_
  -- ‖zn - z‖ → 0
  have h_norm_sub : Tendsto (fun n => ‖zn n - z‖) atTop (𝓝 0) := by
    have h_diff : Tendsto (fun n => zn n - z) atTop (𝓝 (z - z)) :=
      h_lim.sub tendsto_const_nhds
    rw [sub_self] at h_diff
    simpa using h_diff.norm
  -- 1/|(zn).im| → 1/|z.im|
  have h_one_div :
      Tendsto (fun n => 1 / |(zn n).im|) atTop (𝓝 (1 / |z.im|)) := by
    have h_im : Tendsto (fun n => (zn n).im) atTop (𝓝 z.im) :=
      (Complex.continuous_im.tendsto z).comp h_lim
    have h_inv : Tendsto (fun n => (|(zn n).im|)⁻¹) atTop (𝓝 (|z.im|)⁻¹) :=
      h_im.abs.inv₀ (abs_pos.mpr hz).ne'
    simpa [one_div] using h_inv
  -- Product → 0 · (1/|z.im|) · ‖R(z)ξ‖ = 0.
  have h_prod := (h_norm_sub.mul h_one_div).mul_const
                    ‖resolvent z hz hsym hplus hminus ξ‖
  simpa using h_prod

/-
Editor:
One thing worth doing while you're in that file: resolvent_identity is stated in
.comp/∘SL form, and resolvent_commute produces a Commute (i.e. *). They're defeq,
but if you ever want a .comp-flavored corollary for some downstream rewrite,
that's the file to add it to as well, right alongside — keeps the whole
"resolvents at different points relate thus" story in one place.
-/

lemma resolvent_commute
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus  : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    Commute (resolvent z hz hsym hplus hminus) (resolvent w hw hsym hplus hminus) := by
  rcases eq_or_ne z w with rfl | hzw
  · exact Commute.refl _
  set Rz := resolvent z hz hsym hplus hminus
  set Rw := resolvent w hw hsym hplus hminus
  have e₁ : Rz - Rw = (z - w) • Rz.comp Rw := resolvent_identity hsym hplus hminus z w hz hw
  have e₂ : Rw - Rz = (w - z) • Rw.comp Rz := resolvent_identity hsym hplus hminus w z hw hz
  -- recast e₂ into the same shape as e₁, but with the factors swapped
  have e₂' : Rz - Rw = (z - w) • Rw.comp Rz := by
    rw [← neg_sub Rw Rz, e₂, ← neg_smul, neg_sub]
  -- the two scalar multiples are equal; cancel (z - w) ≠ 0
  have hcomp : Rz.comp Rw = Rw.comp Rz := by
    have h0 : (z - w) • (Rz.comp Rw - Rw.comp Rz) = 0 := by
      rw [smul_sub, ← e₁, e₂', sub_self]
    have hzw' : z - w ≠ 0 := sub_ne_zero.mpr hzw
    exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_left hzw')
  exact hcomp

/-- The resolvent adjoint relation: `R(z)* = R(z̄)`. -/
lemma resolvent_adjoint {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (z : ℂ) (hz : z.im ≠ 0) :
    (resolvent z hz hsym hplus hminus).adjoint =
    resolvent (starRingEnd ℂ z) (by simp only [Complex.conj_im, neg_ne_zero]; exact hz)
      hsym hplus hminus := by
  ext φ
  apply ext_inner_right ℂ
  intro ψ
  rw [ContinuousLinearMap.adjoint_inner_left]
  set z_bar := (starRingEnd ℂ) z with hz_bar_def
  have hz_bar : z_bar.im ≠ 0 := by
    rw [hz_bar_def]; simp only [Complex.conj_im, neg_ne_zero]; exact hz
  let ξ_sub : A.domain := Classical.choose (self_adjoint_range_all_z hsym hplus hminus z hz ψ).exists
  let ξ := (ξ_sub : H)
  have hξ_domain : ξ ∈ A.domain := ξ_sub.property
  have hξ_eq : A ξ_sub - z • ξ = ψ :=
    Classical.choose_spec (self_adjoint_range_all_z hsym hplus hminus z hz ψ).exists
  have hξ_def : resolvent z hz hsym hplus hminus ψ = ξ := rfl
  let η_sub : A.domain :=
    Classical.choose (self_adjoint_range_all_z hsym hplus hminus z_bar hz_bar φ).exists
  let η := (η_sub : H)
  have hη_domain : η ∈ A.domain := η_sub.property
  have hη_eq : A η_sub - z_bar • η = φ :=
    Classical.choose_spec (self_adjoint_range_all_z hsym hplus hminus z_bar hz_bar φ).exists
  have hη_def : resolvent z_bar hz_bar hsym hplus hminus φ = η := rfl
  rw [hξ_def, hη_def]
  have hAξ : A ξ_sub = ψ + z • ξ := by
    calc A ξ_sub = (A ξ_sub - z • ξ) + z • ξ := by abel
      _ = ψ + z • ξ := by rw [hξ_eq]
  have hAη : A η_sub = φ + z_bar • η := by
    calc A η_sub = (A η_sub - z_bar • η) + z_bar • η := by abel
      _ = φ + z_bar • η := by rw [hη_eq]
  have h_sym : ⟪A η_sub, ξ⟫_ℂ = ⟪η, A ξ_sub⟫_ℂ := hsym η_sub ξ_sub
  have h_LHS : ⟪A η_sub, ξ⟫_ℂ = ⟪φ, ξ⟫_ℂ + z • ⟪η, ξ⟫_ℂ := by
    calc ⟪A η_sub, ξ⟫_ℂ
        = ⟪φ + z_bar • η, ξ⟫_ℂ := by rw [hAη]
      _ = ⟪φ, ξ⟫_ℂ + ⟪z_bar • η, ξ⟫_ℂ := by rw [inner_add_left]
      _ = ⟪φ, ξ⟫_ℂ + (starRingEnd ℂ) z_bar • ⟪η, ξ⟫_ℂ := by rw [inner_smul_left]; rfl
      _ = ⟪φ, ξ⟫_ℂ + z • ⟪η, ξ⟫_ℂ := by simp [hz_bar_def]
  have h_RHS : ⟪η, A ξ_sub⟫_ℂ = ⟪η, ψ⟫_ℂ + z • ⟪η, ξ⟫_ℂ := by
    calc ⟪η, A ξ_sub⟫_ℂ
        = ⟪η, ψ + z • ξ⟫_ℂ := by rw [hAξ]
      _ = ⟪η, ψ⟫_ℂ + ⟪η, z • ξ⟫_ℂ := by rw [inner_add_right]
      _ = ⟪η, ψ⟫_ℂ + z • ⟪η, ξ⟫_ℂ := by rw [inner_smul_right]; rfl
  have h_cancel : ⟪φ, ξ⟫_ℂ + z • ⟪η, ξ⟫_ℂ = ⟪η, ψ⟫_ℂ + z • ⟪η, ξ⟫_ℂ := by
    rw [← h_LHS, ← h_RHS, h_sym]
  exact add_right_cancel h_cancel

/-- Resolvent matrix-element reflection: `conj ⟨ξ, R(conj z) ξ⟩ = ⟨ξ, R(z) ξ⟩`.
Three-step assembly: conjugate-symmetry of the inner product, adjoint-pairing,
and `resolvent_adjoint` (which is `R(z)* = R(conj z)`). -/
lemma resolvent_inner_diag_conj {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    {z : ℂ} (hz : z.im ≠ 0) (hcz : (starRingEnd ℂ z).im ≠ 0) (ξ : H) :
    (starRingEnd ℂ) ⟪ξ, resolvent (starRingEnd ℂ z) hcz hsym hplus hminus ξ⟫_ℂ
      = ⟪ξ, resolvent z hz hsym hplus hminus ξ⟫_ℂ := by
  rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right,
      resolvent_adjoint hsym hplus hminus (starRingEnd ℂ z) hcz]
  congr 2
  simp only [RingHomCompTriple.comp_apply, RingHom.id_apply]

/-! ## Wrapper definitions and lemmas for `resolventFun` -/

/-- The resolvent as a function on `OffRealAxis`. -/
noncomputable def resolventFun {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) :
    OffRealAxis → (H →L[ℂ] H) :=
  fun z => resolvent z.val z.property hsym hplus hminus

end Spectra.Resolvent
