/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Resolvent/Range/CloasedRange.lean
-/
import Spectra.Resolvent.SpecialCases
import Spectra.Resolvent.LowerBound
/-!
# Closedness of the Range of (A - zI)

This file proves that for a self-adjoint generator `A` and any `z` with
`Im(z) ≠ 0`, the range of `(A - zI)` is closed.

The key insight is the lower bound `|Im(z)| · ‖ψ‖ ≤ ‖(A - zI)ψ‖`, which
implies that preimages of Cauchy sequences are Cauchy. The limit is shown
to lie in the domain by routing through `R(i)`.

## Main results

* `preimage_cauchySeq`: Preimages of Cauchy sequences under `(A - zI)` are Cauchy
* `range_limit_mem`: Sequential limits of range elements are in the range
* `range_sub_smul_closed`: The range of `(A - zI)` is closed

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII.3
-/
open InnerProductSpace MeasureTheory Complex Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Spectra.Resolvent

/-- Preimages of Cauchy sequences under (A - zI) are Cauchy when Im(z) ≠ 0. -/
lemma preimage_cauchySeq {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (z : ℂ) (hz : z.im ≠ 0)
    (ψ_seq : ℕ → A.domain)
    (hu_cauchy : CauchySeq (fun n => A (ψ_seq n) - z • (ψ_seq n : H))) :
    CauchySeq (fun n => (ψ_seq n : H)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hε_scaled : 0 < |z.im| * ε := mul_pos (abs_pos.mpr hz) hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu_cauchy (|z.im| * ε) hε_scaled
  use N
  intro m hm n hn
  have h_sub_mem : (ψ_seq m : H) - (ψ_seq n : H) ∈ A.domain :=
    A.domain.sub_mem (ψ_seq m).property (ψ_seq n).property
  have h_bound := lower_bound_estimate hsym z hz ((ψ_seq m : H) - (ψ_seq n : H)) h_sub_mem
  have h_diff : A ⟨(ψ_seq m : H) - (ψ_seq n : H), h_sub_mem⟩ -
                z • ((ψ_seq m : H) - (ψ_seq n : H)) =
                (A (ψ_seq m) - z • (ψ_seq m : H)) - (A (ψ_seq n) - z • (ψ_seq n : H)) := by
    have op_sub := A.map_sub (ψ_seq m) (ψ_seq n)
    have op_eq : A ⟨(ψ_seq m : H) - (ψ_seq n : H), h_sub_mem⟩ =
                 A (ψ_seq m) - A (ψ_seq n) := by
      convert op_sub using 1
    calc A ⟨(ψ_seq m : H) - (ψ_seq n : H), h_sub_mem⟩ -
        z • ((ψ_seq m : H) - (ψ_seq n : H))
        = (A (ψ_seq m) - A (ψ_seq n)) - z • ((ψ_seq m : H) - (ψ_seq n : H)) :=
            by rw [op_eq]
      _ = (A (ψ_seq m) - A (ψ_seq n)) - (z • (ψ_seq m : H) - z • (ψ_seq n : H)) := by
          rw [smul_sub]
      _ = (A (ψ_seq m) - z • (ψ_seq m : H)) - (A (ψ_seq n) - z • (ψ_seq n : H)) :=
          by abel
  rw [h_diff] at h_bound
  have h_ubound : dist ((A (ψ_seq m) - z • (ψ_seq m : H)))
                       ((A (ψ_seq n) - z • (ψ_seq n : H))) < |z.im| * ε := hN m hm n hn
  rw [dist_eq_norm] at h_ubound
  have h_chain : |z.im| * ‖(ψ_seq m : H) - (ψ_seq n : H)‖ < |z.im| * ε := by
    calc |z.im| * ‖(ψ_seq m : H) - (ψ_seq n : H)‖
        ≤ ‖(A (ψ_seq m) - z • (ψ_seq m : H)) -
           (A (ψ_seq n) - z • (ψ_seq n : H))‖ := h_bound
      _ < |z.im| * ε := h_ubound
  have h_pos : 0 < |z.im| := abs_pos.mpr hz
  rw [dist_eq_norm]
  exact (mul_lt_mul_iff_of_pos_left h_pos).mp h_chain

/-- The limit of a convergent sequence in ran(A - zI) is in ran(A - zI). -/
lemma range_limit_mem {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (z : ℂ) (_ /-hz-/ : z.im ≠ 0)
    (ψ_seq : ℕ → A.domain) (φ_lim : H)
    (hψ_seq : ∀ n, A (ψ_seq n) - z • (ψ_seq n : H) = φ_lim)
    (hψ_lim : ∃ ψ_lim, Tendsto (fun n => (ψ_seq n : H)) atTop (𝓝 ψ_lim)) :
    ∃ (ψ : A.domain), A ψ - z • (ψ : H) = φ_lim := by
  obtain ⟨ψ_lim, hψ_tendsto⟩ := hψ_lim
  let R := resolvent_at_i hsym hminus
  have h_AiI_lim : Tendsto (fun n => A (ψ_seq n) - I • (ψ_seq n : H))
                          atTop (𝓝 (φ_lim + (z - I) • ψ_lim)) := by
    have h1 : Tendsto (fun n => A (ψ_seq n) - z • (ψ_seq n : H)) atTop (𝓝 φ_lim) := by
      simp only [hψ_seq]
      exact tendsto_const_nhds
    have h2 : Tendsto (fun n => (z - I) • (ψ_seq n : H)) atTop (𝓝 ((z - I) • ψ_lim)) :=
      Tendsto.const_smul hψ_tendsto (z - I)
    have h3 := Tendsto.add h1 h2
    have h_eq : ∀ n, A (ψ_seq n) - I • (ψ_seq n : H) =
                (A (ψ_seq n) - z • (ψ_seq n : H)) + (z - I) • (ψ_seq n : H) := fun n => by
      simp only [sub_smul]; abel
    exact h3.congr (fun n => (h_eq n).symm)
  have h_R_inverse : ∀ (ψ : H) (hψ : ψ ∈ A.domain),
                      R (A ⟨ψ, hψ⟩ - I • ψ) = ψ := fun ψ hψ =>
    resolvent_at_i_unique hsym _ (R _) ψ (Rminus_mem hminus _) hψ
      (Rminus_eq hminus _) rfl
  have h_R_lim : Tendsto (fun n => R (A (ψ_seq n) - I • (ψ_seq n : H)))
                        atTop (𝓝 (R (φ_lim + (z - I) • ψ_lim))) :=
    R.continuous.tendsto _ |>.comp h_AiI_lim
  have h_R_eq : ∀ n, R (A (ψ_seq n) - I • (ψ_seq n : H)) = (ψ_seq n : H) := fun n =>
    h_R_inverse (ψ_seq n : H) (ψ_seq n).property
  have h_ψ_lim_alt : Tendsto (fun n => (ψ_seq n : H)) atTop
      (𝓝 (R (φ_lim + (z - I) • ψ_lim))) := h_R_lim.congr (fun n => (h_R_eq n))
  have h_ψ_lim_eq : ψ_lim = R (φ_lim + (z - I) • ψ_lim) :=
    tendsto_nhds_unique hψ_tendsto h_ψ_lim_alt
  have h_ψ_lim_domain : ψ_lim ∈ A.domain := by
    rw [h_ψ_lim_eq]
    exact Rminus_mem hminus (φ_lim + (z - I) • ψ_lim)
  refine ⟨⟨ψ_lim, h_ψ_lim_domain⟩, ?_⟩
  have h_AiI_ψ_lim := Rminus_eq hminus (φ_lim + (z - I) • ψ_lim)
  have h_op_eq : A ⟨ψ_lim, h_ψ_lim_domain⟩ =
                 A ⟨R (φ_lim + (z - I) • ψ_lim),
                        Rminus_mem hminus (φ_lim + (z - I) • ψ_lim)⟩ := by
    congr 1
    exact Subtype.ext h_ψ_lim_eq
  calc A ⟨ψ_lim, h_ψ_lim_domain⟩ - z • ψ_lim
      = A ⟨R (φ_lim + (z - I) • ψ_lim),
              Rminus_mem hminus (φ_lim + (z - I) • ψ_lim)⟩ -
      z • R (φ_lim + (z - I) • ψ_lim) := by
        rw [h_op_eq]
        exact
          congrArg
            (HSub.hSub
              (A
                ⟨R (φ_lim + (z - I) • ψ_lim),
                  Rminus_mem hminus (φ_lim + (z - I) • ψ_lim)⟩))
            (congrArg (HSMul.hSMul z) h_ψ_lim_eq)
    _ = (A ⟨R (φ_lim + (z - I) • ψ_lim),
                Rminus_mem hminus (φ_lim + (z - I) • ψ_lim)⟩ -
        I • R (φ_lim + (z - I) • ψ_lim)) - (z - I) • R (φ_lim + (z - I) • ψ_lim) := by
        simp only [sub_smul]; abel
    _ = (φ_lim + (z - I) • ψ_lim) - (z - I) • R (φ_lim + (z - I) • ψ_lim) := by
      exact congrFun (congrArg HSub.hSub h_AiI_ψ_lim) ((z - I) • R (φ_lim + (z - I) • ψ_lim))
    _ = (φ_lim + (z - I) • ψ_lim) - (z - I) • ψ_lim := by rw [← h_ψ_lim_eq]
    _ = φ_lim := by abel


/-- The range of (A - zI) is closed. -/
lemma range_sub_smul_closed [CompleteSpace H] {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (z : ℂ) (hz : z.im ≠ 0) :
    IsClosed (Set.range (fun (ψ : A.domain) => A ψ - z • (ψ : H))) := by
  rw [← isSeqClosed_iff_isClosed]
  intro u φ_lim hu_range hφ_lim
  have hu_cauchy : CauchySeq u := hφ_lim.cauchySeq
  choose ψ_seq hψ_seq using fun n => Set.mem_range.mp (hu_range n)
  have hψ_cauchy : CauchySeq (fun n => (ψ_seq n : H)) := by
    have hu_cauchy' : CauchySeq (fun n => A (ψ_seq n) - z • (ψ_seq n : H)) := by
      convert hu_cauchy using 1
      ext n
      exact hψ_seq n
    exact preimage_cauchySeq hsym z hz ψ_seq hu_cauchy'
  obtain ⟨ψ_lim, hψ_lim⟩ := cauchySeq_tendsto_of_complete hψ_cauchy
  let R := resolvent_at_i hsym hminus
  have h_AiI : ∀ n, A (ψ_seq n) - I • (ψ_seq n : H) = u n + (z - I) • (ψ_seq n : H) := by
    intro n
    have h := hψ_seq n
    calc A (ψ_seq n) - I • (ψ_seq n : H)
        = (A (ψ_seq n) - z • (ψ_seq n : H)) + (z - I) • (ψ_seq n : H) := by
            rw [sub_smul]; abel
      _ = u n + (z - I) • (ψ_seq n : H) := by rw [h]
  have h_AiI_lim : Tendsto (fun n => A (ψ_seq n) - I • (ψ_seq n : H))
                          atTop (𝓝 (φ_lim + (z - I) • ψ_lim)) := by
    have h1 : Tendsto u atTop (𝓝 φ_lim) := hφ_lim
    have h2 : Tendsto (fun n => (z - I) • (ψ_seq n : H)) atTop (𝓝 ((z - I) • ψ_lim)) :=
      Tendsto.const_smul hψ_lim (z - I)
    have h3 : Tendsto (fun n => u n + (z - I) • (ψ_seq n : H)) atTop
                      (𝓝 (φ_lim + (z - I) • ψ_lim)) := Tendsto.add h1 h2
    convert h3 using 1
    ext n
    exact h_AiI n
  have h_R_inverse : ∀ (ψ : H) (hψ : ψ ∈ A.domain),
                      R (A ⟨ψ, hψ⟩ - I • ψ) = ψ := by
    intro ψ hψ
    let η := A ⟨ψ, hψ⟩ - I • ψ
    have h_Rη_mem := Rminus_mem hminus η
    have h_Rη_eq := Rminus_eq hminus η
    exact resolvent_at_i_unique hsym η (R η) ψ h_Rη_mem hψ h_Rη_eq rfl
  have h_R_lim : Tendsto (fun n => R (A (ψ_seq n) - I • (ψ_seq n : H)))
                        atTop (𝓝 (R (φ_lim + (z - I) • ψ_lim))) :=
    R.continuous.tendsto _ |>.comp h_AiI_lim
  have h_R_eq : ∀ n, R (A (ψ_seq n) - I • (ψ_seq n : H)) = (ψ_seq n : H) := by
    intro n
    exact h_R_inverse (ψ_seq n : H) (ψ_seq n).property
  have h_ψ_lim_alt : Tendsto (fun n => (ψ_seq n : H)) atTop
      (𝓝 (R (φ_lim + (z - I) • ψ_lim))) := by
    convert h_R_lim using 1
    ext n
    exact (h_R_eq n).symm
  have h_ψ_lim_eq : ψ_lim = R (φ_lim + (z - I) • ψ_lim) :=
    tendsto_nhds_unique hψ_lim h_ψ_lim_alt
  have h_ψ_lim_domain : ψ_lim ∈ A.domain := by
    rw [h_ψ_lim_eq]
    exact Rminus_mem hminus (φ_lim + (z - I) • ψ_lim)
  have h_eq : A ⟨ψ_lim, h_ψ_lim_domain⟩ - z • ψ_lim = φ_lim := by
    have h_AiI_ψ_lim : A ⟨R (φ_lim + (z - I) • ψ_lim),
                        Rminus_mem hminus (φ_lim + (z - I) • ψ_lim)⟩ -
                       I • R (φ_lim + (z - I) • ψ_lim) = φ_lim + (z - I) • ψ_lim :=
      Rminus_eq hminus (φ_lim + (z - I) • ψ_lim)
    have h_op_eq : A ⟨ψ_lim, h_ψ_lim_domain⟩ =
                   A ⟨R (φ_lim + (z - I) • ψ_lim),
                          Rminus_mem hminus (φ_lim + (z - I) • ψ_lim)⟩ := by
      congr 1
      exact Subtype.ext h_ψ_lim_eq
    calc A ⟨ψ_lim, h_ψ_lim_domain⟩ - z • ψ_lim
        = A ⟨R (φ_lim + (z - I) • ψ_lim),
                Rminus_mem hminus (φ_lim + (z - I) • ψ_lim)⟩ -
        z • R (φ_lim + (z - I) • ψ_lim) := by
          have h_smul : z • ψ_lim = z • R (φ_lim + (z - I) • ψ_lim) := by
            rw [h_ψ_lim_eq]
            exact
              congrArg (HSMul.hSMul z)
                (congrArg (⇑R)
                  (congrArg (HAdd.hAdd φ_lim) (congrArg (HSMul.hSMul (z - I)) h_ψ_lim_eq)))
          rw [h_op_eq, h_smul]
      _ = (A ⟨R (φ_lim + (z - I) • ψ_lim),
                  Rminus_mem hminus (φ_lim + (z - I) • ψ_lim)⟩ -
          I • R (φ_lim + (z - I) • ψ_lim)) - (z - I) • R (φ_lim + (z - I) • ψ_lim) := by
        have hz_split : z • R (φ_lim + (z - I) • ψ_lim) =
                        I • R (φ_lim + (z - I) • ψ_lim) +
                        (z - I) • R (φ_lim + (z - I) • ψ_lim) := by
          rw [← add_smul]; congr 1; ring
        rw [hz_split]
        abel
      _ = (φ_lim + (z - I) • ψ_lim) - (z - I) • R (φ_lim + (z - I) • ψ_lim) := by
          rw [h_AiI_ψ_lim]
      _ = (φ_lim + (z - I) • ψ_lim) - (z - I) • ψ_lim := by rw [← h_ψ_lim_eq]
      _ = φ_lim := by abel
  exact ⟨⟨ψ_lim, h_ψ_lim_domain⟩, h_eq⟩

end Spectra.Resolvent
