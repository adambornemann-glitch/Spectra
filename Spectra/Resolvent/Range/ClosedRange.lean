/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
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

## Main statements

* `preimage_cauchySeq`: Preimages of Cauchy sequences under `(A - zI)` are Cauchy
* `range_sub_smul_closed`: The range of `(A - zI)` is closed

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII.3
-/
open InnerProductSpace Complex Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Spectra.Resolvent

/-- **Preimages of Cauchy sequences** under `A - zI` are Cauchy when `Im(z) ≠ 0`: the constant
`|Im z|` in the lower bound `|Im z| · ‖ψ‖ ≤ ‖(A - zI)ψ‖` (`lower_bound_estimate`) is exactly the
spectral gap that turns the map `A - zI` bounded-below into one whose *inverse* is
norm-controlled, which is what lets a Cauchy image sequence be pulled back to a Cauchy
preimage. -/
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
  have h_bound := lower_bound_estimate hsym z ((ψ_seq m : H) - (ψ_seq n : H)) h_sub_mem
  have h_diff : A ⟨(ψ_seq m : H) - (ψ_seq n : H), h_sub_mem⟩ -
                z • ((ψ_seq m : H) - (ψ_seq n : H)) =
                (A (ψ_seq m) - z • (ψ_seq m : H)) - (A (ψ_seq n) - z • (ψ_seq n : H)) := by
    have op_eq : A ⟨(ψ_seq m : H) - (ψ_seq n : H), h_sub_mem⟩ =
                 A (ψ_seq m) - A (ψ_seq n) :=
      (congrArg A (Subtype.ext rfl)).trans (A.map_sub (ψ_seq m) (ψ_seq n))
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

/-- The **range of `A - zI`** is closed, for `A` self-adjoint and `Im(z) ≠ 0`: given a convergent
sequence of images, `preimage_cauchySeq` recovers a Cauchy (hence, by completeness, convergent)
preimage sequence, and the limit is shown to lie in `dom A` by routing it through the bounded
resolvent `R(i)` rather than any a priori domain-closedness fact for the unbounded `A`. -/
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
      rw [funext hψ_seq]; exact hu_cauchy
    exact preimage_cauchySeq hsym z hz ψ_seq hu_cauchy'
  obtain ⟨ψ_lim, hψ_lim⟩ := cauchySeq_tendsto_of_complete hψ_cauchy
  -- The candidate preimage `ψ_lim` is only known as a Cauchy-sequence limit in `H`; nothing so
  -- far places it in `dom A`. We manufacture domain membership by routing through the bounded
  -- resolvent `R(i) = (A - iI)⁻¹`: `ψ_lim` is *defined* to equal `R(i)` applied to a computable
  -- limit, and `R(i)` always lands in `dom A`, so `ψ_lim ∈ dom A` for free (`h_ψ_lim_domain`
  -- below). This sidesteps needing any a priori domain-closedness fact for the unbounded `A`.
  let R := resolventAtI hsym hminus
  set η' := φ_lim + (z - I) • ψ_lim with hη'
  have h_AiI : ∀ n, A (ψ_seq n) - I • (ψ_seq n : H) = u n + (z - I) • (ψ_seq n : H) := by
    intro n
    have h := hψ_seq n
    calc A (ψ_seq n) - I • (ψ_seq n : H)
        = (A (ψ_seq n) - z • (ψ_seq n : H)) + (z - I) • (ψ_seq n : H) := by
            rw [sub_smul]; abel
      _ = u n + (z - I) • (ψ_seq n : H) := by rw [h]
  have h_AiI_lim : Tendsto (fun n => A (ψ_seq n) - I • (ψ_seq n : H)) atTop (𝓝 η') := by
    have h1 : Tendsto u atTop (𝓝 φ_lim) := hφ_lim
    have h2 : Tendsto (fun n => (z - I) • (ψ_seq n : H)) atTop (𝓝 ((z - I) • ψ_lim)) :=
      Tendsto.const_smul hψ_lim (z - I)
    exact (Tendsto.add h1 h2).congr fun n => (h_AiI n).symm
  have h_R_inverse : ∀ (ψ : H) (hψ : ψ ∈ A.domain),
                      R (A ⟨ψ, hψ⟩ - I • ψ) = ψ := by
    intro ψ hψ
    let η := A ⟨ψ, hψ⟩ - I • ψ
    have h_Rη_mem := Rminus_mem hminus η
    have h_Rη_eq := Rminus_eq hminus η
    exact resolvent_at_i_unique hsym η (R η) ψ h_Rη_mem hψ h_Rη_eq rfl
  have h_R_lim : Tendsto (fun n => R (A (ψ_seq n) - I • (ψ_seq n : H))) atTop (𝓝 (R η')) :=
    R.continuous.tendsto _ |>.comp h_AiI_lim
  have h_R_eq : ∀ n, R (A (ψ_seq n) - I • (ψ_seq n : H)) = (ψ_seq n : H) := by
    intro n
    exact h_R_inverse (ψ_seq n : H) (ψ_seq n).property
  have h_ψ_lim_alt : Tendsto (fun n => (ψ_seq n : H)) atTop (𝓝 (R η')) :=
    h_R_lim.congr h_R_eq
  have h_ψ_lim_eq : ψ_lim = Rminus hminus η' := tendsto_nhds_unique hψ_lim h_ψ_lim_alt
  have h_ψ_lim_domain : ψ_lim ∈ A.domain := h_ψ_lim_eq ▸ Rminus_mem hminus η'
  have h_eq : A ⟨ψ_lim, h_ψ_lim_domain⟩ - z • ψ_lim = φ_lim := by
    have h_AiI_ψ_lim : A ⟨Rminus hminus η', Rminus_mem hminus η'⟩ - I • Rminus hminus η' = η' :=
      Rminus_eq hminus η'
    have h_op_eq : A ⟨ψ_lim, h_ψ_lim_domain⟩ = A ⟨Rminus hminus η', Rminus_mem hminus η'⟩ :=
      congrArg A (Subtype.ext h_ψ_lim_eq)
    calc A ⟨ψ_lim, h_ψ_lim_domain⟩ - z • ψ_lim
        = A ⟨Rminus hminus η', Rminus_mem hminus η'⟩ - z • Rminus hminus η' := by
          rw [h_op_eq, h_ψ_lim_eq]
      _ = (A ⟨Rminus hminus η', Rminus_mem hminus η'⟩ - I • Rminus hminus η')
            - (z - I) • Rminus hminus η' := by
          have : I • Rminus hminus η' + (z - I) • Rminus hminus η' = z • Rminus hminus η' := by
            rw [← add_smul]; ring_nf
          rw [← this]; abel
      _ = η' - (z - I) • Rminus hminus η' := by rw [h_AiI_ψ_lim]
      _ = η' - (z - I) • ψ_lim := by rw [← h_ψ_lim_eq]
      _ = φ_lim := by rw [hη']; abel
  exact ⟨⟨ψ_lim, h_ψ_lim_domain⟩, h_eq⟩

end Spectra.Resolvent
