/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Range
/-!
# Resolvent Identities

This file proves the fundamental algebraic identities satisfied by the resolvent `R(z) =
(A - zI)⁻¹` built in `Range.lean`, for a symmetric `A` with vanishing deficiency indices
(`hplus`/`hminus`):
* The resolvent identity: `R(z) - R(w) = (z - w) R(z) R(w)`
* The adjoint relation: `R(z)* = R(z̄)`
* Strong-operator continuity of `z ↦ R(z)` off the real axis
* Commutativity of resolvents at different points
* Conjugate reflection of the diagonal matrix element `⟪ξ, R(z) ξ⟫`

`resolvent_identity` and `resolvent_adjoint` are proved by reusing the public
`resolventSolution`/`resolventSolution_mem`/`resolventSolution_eq` trio from `Range.lean` rather
than re-deriving `self_adjoint_range_all_z`'s `Classical.choose`/`choose_spec` pair by hand at each
use site.

## Main definitions

* `resolventFun`: The resolvent as a function on `OffRealAxis` (`Spectra.Resolvent.OffRealAxis`,
  the subtype `{z : ℂ // z.im ≠ 0}`), bundling `z` and its off-axis proof into one argument.

## Main statements

* `resolvent_identity`: `R(z) - R(w) = (z - w) R(z) R(w)`.
* `resolvent_tendsto`: `z ↦ R(z)` is strong-operator continuous off the real axis.
* `resolvent_commute`: `R(z)` and `R(w)` commute for any `z, w` off the real axis.
* `resolvent_adjoint`: `R(z)* = R(z̄)`.
* `resolvent_inner_diag_conj`: `conj ⟪ξ, R(z̄) ξ⟫ = ⟪ξ, R(z) ξ⟫`.

## Implementation notes

`hplus`/`hminus` witness that `A` has deficiency indices `(0, 0)`: `A + iI` and `A - iI` are each
surjective onto `H`. Together with symmetry (`hsym`) this is exactly the hypothesis of
`self_adjoint_range_all_z`, which every lemma here ultimately rests on for existence and uniqueness
of resolvent-equation solutions.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII.3
* [Kato, *Perturbation Theory for Linear Operators*][kato1995], Section V.3
-/
open InnerProductSpace Complex Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Resolvent

/-- The **resolvent identity**: `R(z) - R(w) = (z - w) R(z) R(w)`, i.e. `R(z)` and `R(w)` at two
points off the real axis differ by `(z - w)` times their composite. Proved by exhibiting both
sides' action on an arbitrary `φ` as the (unique, by `self_adjoint_range_all_z`) solution of the
same resolvent equation at `z`: writing `ψ_w = R(w) φ` and `η = R(z) ψ_w`, one checks directly that
`ψ_z + (w - z) • η` solves `(A - z)· = φ + (w - z) • ψ_w` just as `ψ_w` does, so uniqueness forces
`ψ_w = ψ_z + (w - z) • η`, which rearranges to `ψ_z - ψ_w = (z - w) • η`. -/
lemma resolvent_identity {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    resolvent z hz hsym hplus hminus - resolvent w hw hsym hplus hminus =
    (z - w) • ((resolvent z hz hsym hplus hminus).comp (resolvent w hw hsym hplus hminus)) := by
  ext φ
  set ψ_w := resolventSolution w hw hsym hplus hminus φ with _hψ_w_def
  have h_w_domain : ψ_w ∈ A.domain := resolventSolution_mem w hw hsym hplus hminus φ
  have h_w_eq : A ⟨ψ_w, h_w_domain⟩ - w • ψ_w = φ :=
    resolventSolution_eq w hw hsym hplus hminus φ
  set ψ_z := resolventSolution z hz hsym hplus hminus φ with _hψ_z_def
  have h_z_domain : ψ_z ∈ A.domain := resolventSolution_mem z hz hsym hplus hminus φ
  have h_z_eq : A ⟨ψ_z, h_z_domain⟩ - z • ψ_z = φ :=
    resolventSolution_eq z hz hsym hplus hminus φ
  set η := resolventSolution z hz hsym hplus hminus ψ_w with _hη_def
  have h_η_domain : η ∈ A.domain := resolventSolution_mem z hz hsym hplus hminus ψ_w
  have h_η_eq : A ⟨η, h_η_domain⟩ - z • η = ψ_w :=
    resolventSolution_eq z hz hsym hplus hminus ψ_w
  have h_Rz : resolvent z hz hsym hplus hminus φ = ψ_z := rfl
  have h_Rw : resolvent w hw hsym hplus hminus φ = ψ_w := rfl
  have h_Rz_ψw : resolvent z hz hsym hplus hminus ψ_w = η := rfl
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
             ContinuousLinearMap.comp_apply]
  rw [h_Rz, h_Rw, h_Rz_ψw]
  have h_Az_ψw : A ⟨ψ_w, h_w_domain⟩ - z • ψ_w = φ + (w - z) • ψ_w := by
    have h_Aw : A ⟨ψ_w, h_w_domain⟩ = φ + w • ψ_w := by
      calc A ⟨ψ_w, h_w_domain⟩
          = (A ⟨ψ_w, h_w_domain⟩ - w • ψ_w) + w • ψ_w := by abel
        _ = φ + w • ψ_w := by rw [h_w_eq]
    calc A ⟨ψ_w, h_w_domain⟩ - z • ψ_w
        = (φ + w • ψ_w) - z • ψ_w := by rw [h_Aw]
      _ = φ + (w - z) • ψ_w := by rw [sub_smul]; abel
  have h_sum_domain : ψ_z + (w - z) • η ∈ A.domain := by
    apply A.domain.add_mem h_z_domain
    exact A.domain.smul_mem (w - z) h_η_domain
  have h_sum_eq : A ⟨ψ_z + (w - z) • η, h_sum_domain⟩ -
      z • (ψ_z + (w - z) • η) = φ + (w - z) • ψ_w := by
    have h_smul_mem : (w - z) • η ∈ A.domain := A.domain.smul_mem (w - z) h_η_domain
    have op_eq : A ⟨ψ_z + (w - z) • η, h_sum_domain⟩ =
                 A ⟨ψ_z, h_z_domain⟩ + A ⟨(w - z) • η, h_smul_mem⟩ := by
      convert A.map_add ⟨ψ_z, h_z_domain⟩ ⟨(w - z) • η, h_smul_mem⟩ using 1
    have op_smul_eq : A ⟨(w - z) • η, h_smul_mem⟩ = (w - z) • A ⟨η, h_η_domain⟩ := by
      convert A.map_smul (w - z) ⟨η, h_η_domain⟩ using 1
    calc A ⟨ψ_z + (w - z) • η, h_sum_domain⟩ - z • (ψ_z + (w - z) • η)
        = (A ⟨ψ_z, h_z_domain⟩ + A ⟨(w - z) • η, h_smul_mem⟩) - z • (ψ_z + (w - z) • η) :=
            by rw [op_eq]
      _ = (A ⟨ψ_z, h_z_domain⟩ + (w - z) • A ⟨η, h_η_domain⟩) - z • (ψ_z + (w - z) • η) :=
            by rw [op_smul_eq]
      _ = (A ⟨ψ_z, h_z_domain⟩ + (w - z) • A ⟨η, h_η_domain⟩)
            - (z • ψ_z + z • ((w - z) • η)) := by rw [smul_add]
      _ = (A ⟨ψ_z, h_z_domain⟩ - z • ψ_z)
            + ((w - z) • A ⟨η, h_η_domain⟩ - z • ((w - z) • η)) := by abel
      _ = (A ⟨ψ_z, h_z_domain⟩ - z • ψ_z)
            + ((w - z) • A ⟨η, h_η_domain⟩ - (w - z) • (z • η)) :=
            by rw [smul_comm z (w - z) η]
      _ = (A ⟨ψ_z, h_z_domain⟩ - z • ψ_z) + (w - z) • (A ⟨η, h_η_domain⟩ - z • η) :=
            by rw [← smul_sub]
      _ = φ + (w - z) • ψ_w := by rw [h_z_eq, h_η_eq]
  set target := φ + (w - z) • ψ_w with _htarget_def
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
    have hop := resolvent_bound (zn n) (h_im_ne n) hsym hplus hminus
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

/-- **Resolvents at different points commute**: `R(z) ∘ R(w) = R(w) ∘ R(z)` for any `z, w` off the
real axis, stated as `Commute` in the monoid `H →L[ℂ] H` (whose multiplication is `.comp`). Proved
from the resolvent identity at `(z, w)` and at `(w, z)`: subtracting the two `(z - w) • R(z) R(w) =
(w - z) • R(w) R(z)`-shaped equations and cancelling the nonzero scalar `z - w` forces `R(z) R(w) =
R(w) R(z)` directly. No separate `.comp`-flavored corollary is needed for downstream rewrites:
`Commute` unfolds to `R(z) * R(w) = R(w) * R(z)`, and `*` on `H →L[ℂ] H` is
`ContinuousLinearMap.comp` by definition, so `resolvent_commute` already discharges a `.comp`-form
goal like `R(z).comp (R(w)) = R(w).comp (R(z))` by `rfl`-unfolding — no additional lemma
statement required. -/
lemma resolvent_commute
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
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

/-- The **resolvent adjoint relation**: `R(z)* = R(z̄)`, i.e. the Hilbert-space adjoint of the
resolvent at `z` is the resolvent at the conjugate point `z̄`. This is the operator-level shadow of
symmetry: pairing `⟪Aη, ξ⟫ = ⟪η, Aξ⟫` (`hsym`) against `ξ = R(z)ψ` and `η = R(z̄)φ` and expanding
both sides via the resolvent equation collapses to `⟪φ, ξ⟫ + z⟪η, ξ⟫ = ⟪η, ψ⟫ + z⟪η, ξ⟫`, which
cancels to `⟪φ, R(z)ψ⟫ = ⟪R(z̄)φ, ψ⟫`, exactly `⟪R(z)*φ, ψ⟫ = ⟪R(z̄)φ, ψ⟫` for all `ψ`. -/
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
  set ξ := resolventSolution z hz hsym hplus hminus ψ with _hξ_def'
  have hξ_domain : ξ ∈ A.domain := resolventSolution_mem z hz hsym hplus hminus ψ
  have hξ_eq : A ⟨ξ, hξ_domain⟩ - z • ξ = ψ := resolventSolution_eq z hz hsym hplus hminus ψ
  have hξ_def : resolvent z hz hsym hplus hminus ψ = ξ := rfl
  set η := resolventSolution z_bar hz_bar hsym hplus hminus φ with _hη_def'
  have hη_domain : η ∈ A.domain := resolventSolution_mem z_bar hz_bar hsym hplus hminus φ
  have hη_eq : A ⟨η, hη_domain⟩ - z_bar • η = φ :=
    resolventSolution_eq z_bar hz_bar hsym hplus hminus φ
  have hη_def : resolvent z_bar hz_bar hsym hplus hminus φ = η := rfl
  rw [hξ_def, hη_def]
  have hAξ : A ⟨ξ, hξ_domain⟩ = ψ + z • ξ := by
    calc A ⟨ξ, hξ_domain⟩ = (A ⟨ξ, hξ_domain⟩ - z • ξ) + z • ξ := by abel
      _ = ψ + z • ξ := by rw [hξ_eq]
  have hAη : A ⟨η, hη_domain⟩ = φ + z_bar • η := by
    calc A ⟨η, hη_domain⟩ = (A ⟨η, hη_domain⟩ - z_bar • η) + z_bar • η := by abel
      _ = φ + z_bar • η := by rw [hη_eq]
  have h_sym : ⟪A ⟨η, hη_domain⟩, ξ⟫_ℂ = ⟪η, A ⟨ξ, hξ_domain⟩⟫_ℂ :=
    hsym ⟨η, hη_domain⟩ ⟨ξ, hξ_domain⟩
  have h_LHS : ⟪A ⟨η, hη_domain⟩, ξ⟫_ℂ = ⟪φ, ξ⟫_ℂ + z • ⟪η, ξ⟫_ℂ := by
    calc ⟪A ⟨η, hη_domain⟩, ξ⟫_ℂ
        = ⟪φ + z_bar • η, ξ⟫_ℂ := by rw [hAη]
      _ = ⟪φ, ξ⟫_ℂ + ⟪z_bar • η, ξ⟫_ℂ := by rw [inner_add_left]
      _ = ⟪φ, ξ⟫_ℂ + (starRingEnd ℂ) z_bar • ⟪η, ξ⟫_ℂ := by rw [inner_smul_left]; rfl
      _ = ⟪φ, ξ⟫_ℂ + z • ⟪η, ξ⟫_ℂ := by simp [hz_bar_def]
  have h_RHS : ⟪η, A ⟨ξ, hξ_domain⟩⟫_ℂ = ⟪η, ψ⟫_ℂ + z • ⟪η, ξ⟫_ℂ := by
    calc ⟪η, A ⟨ξ, hξ_domain⟩⟫_ℂ
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

/-- The **resolvent as a function on `OffRealAxis`**: bundles a point `z` off the real axis
together with its off-axis proof into a single subtype argument `z : OffRealAxis`, so that
`resolvent`'s two-argument `(z, hz)` calling convention can be packaged as a plain function
`OffRealAxis → (H →L[ℂ] H)` for contexts (e.g. continuity or analyticity in `z`) that expect one. -/
noncomputable def resolventFun {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) :
    OffRealAxis → (H →L[ℂ] H) :=
  fun z => resolvent z.val z.property hsym hplus hminus

end Spectra.Resolvent
