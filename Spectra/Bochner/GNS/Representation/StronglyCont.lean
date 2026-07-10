/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Bochner.GNS.Representation.Lemmas
import Spectra.Bochner.GNS.Representation.StronglyEx

/-!
# Strong Continuity of the GNS Translation Representation

This file proves strong continuity of the GNS translation representation on the completion
`UniformSpace.Completion (GNSQuotient hPD hH)`: for every `ψ`, the orbit map `t ↦
completionTranslate hPD hH t ψ` is continuous. This is the strong-continuity hypothesis a
Stone's-theorem argument needs to turn `completionTranslate` into a genuine one-parameter unitary
group.

## Main statements

* `pdInner_translate_left_continuous` — `t ↦ ⟨translate t α, β⟩_f` is continuous, by rewriting it
  as a finite double sum of translates of the continuous `f`.
* `quotientTranslate_continuous` — the orbit map of a quotient representative
  `t ↦ quotientTranslate t (mkQ α)` is continuous, via an ε–δ argument on `norm_sub_sq`.
* `completionTranslate_coe_continuous` — the same continuity, transported across the completion
  map at one fixed point `↑(mkQ α)` in the dense range of the quotient.
* `completionTranslate_dist` — `completionTranslate t` is an isometry of the completion.
* `completionTranslate_strong_continuous` — the headline result: continuity of `t ↦
  completionTranslate t ψ` for *every* `ψ` in the completion, obtained from the three lemmas above
  by the generic 3ε extension `strong_continuity_extends`.

## Implementation notes

The three-stage lift mirrors the GNS construction itself: finite-sum continuity of `pdInner`
(purely algebraic, no completion in sight) → an ε–δ argument on the pre-Hilbert quotient
(`quotientTranslate_continuous`) → density transport to the full completion
(`completionTranslate_coe_continuous`). The final step cannot avoid an ε/3-style argument: strong
continuity is only known on the dense image of the quotient, and
`completionTranslate_strong_continuous` needs it at *every* point of the completion, so
`strong_continuity_extends` approximates an arbitrary `ψ` by a dense `w`, using the isometry
(`completionTranslate_dist`) for the two outer legs of the triangle inequality and
continuity-on-the-dense-set for the middle leg.

## References

* Reed–Simon, *Methods of Modern Mathematical Physics I*, §VIII.4 (strong continuity of the
  translation representation)
-/
open Spectra.PositiveDefinite
namespace Spectra.Bochner.GNS

/-- The inner product `t ↦ ⟨translate t α, β⟩_f` is continuous.
    Each term in the double sum involves `f` at a shifted argument;
    `f` is continuous, the sum is finite. -/
lemma pdInner_translate_left_continuous {f : ℝ → ℂ}
    (hf : IsContinuous f) (α β : ℝ →₀ ℂ) :
    Continuous (fun t => pdInner f (translate t α) β) := by
  -- Rewrite as a double Finset.sum
  have heq : ∀ t, pdInner f (translate t α) β =
      ∑ r ∈ α.support, ∑ s ∈ β.support,
        starRingEnd ℂ (α r) * β s * f (s - (r + t)) := by
    intro t
    simp only [pdInner, translate]
    rw [Finsupp.sum_mapDomain_index
      (fun r => by simp [Finsupp.sum])
      (fun r c₁ c₂ => by
        simp only [Finsupp.sum, map_add, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro s _; ring)]
    -- Goal is now `Finsupp.sum ... = Finset.sum ...` over the same support/terms: the two
    -- `Finsupp.sum` unfoldings agree with the `Finset.sum` on `α.support`/`β.support`
    -- component-wise (real and imaginary parts each reduce definitionally).
    exact Eq.symm (Complex.ext rfl rfl)
  simp_rw [heq]
  apply continuous_finsetSum; intro r _
  apply continuous_finsetSum; intro s _
  exact continuous_const.mul
    (hf.continuity.comp (continuous_const.sub (continuous_const.add continuous_id)))

/-- For Finsupp α, the map t ↦ quotientTranslate t (mkQ α) is continuous ℝ → V. -/
lemma quotientTranslate_continuous {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (hf : IsContinuous f) (α : ℝ →₀ ℂ) :
    letI := gnsQuotientNACG hPD hH
    letI := gnsQuotientIPS hPD hH
    Continuous (fun t => quotientTranslate hPD hH t
      ((pdNullSubmodule hPD hH).mkQ α)) := by
  letI nacgV := gnsQuotientNACG hPD hH
  letI ipsV := gnsQuotientIPS hPD hH
  set mkQ := (pdNullSubmodule hPD hH).mkQ
  set qα := mkQ α
  rw [continuous_iff_continuousAt]; intro t₀
  rw [Metric.continuousAt_iff]; intro ε hε
  -- The cross term: t ↦ Re(pdInner f (translate t α) (translate t₀ α))
  set cross := fun t => (pdInner f (translate t α) (translate t₀ α)).re
  have hcross_cont : Continuous cross :=
    Complex.continuous_re.comp (pdInner_translate_left_continuous hf α (translate t₀ α))
  -- At t = t₀, cross = Re(pdInner f α α) = ‖qα‖² (by isometry + inner_self_eq_norm_sq)
  have hcross_eq : cross t₀ = ‖qα‖ ^ 2 := by
    change (pdInner f (translate t₀ α) (translate t₀ α)).re = _
    rw [pdInner_translate]
    rw [← @inner_self_eq_norm_sq ℂ]; rfl
  -- Choose δ from continuity of cross
  obtain ⟨δ, hδ, hδ_spec⟩ := Metric.continuousAt_iff.mp
    hcross_cont.continuousAt (ε ^ 2 / 2) (by positivity)
  refine ⟨δ, hδ, @fun t ht => ?_⟩
  rw [dist_eq_norm]
  -- Expand ‖x - y‖² via norm_sub_sq
  set x := quotientTranslate hPD hH t qα
  set y := quotientTranslate hPD hH t₀ qα
  have hx_norm : ‖x‖ = ‖qα‖ := quotientTranslate_norm hPD hH t qα
  have hy_norm : ‖y‖ = ‖qα‖ := quotientTranslate_norm hPD hH t₀ qα
  have hinner_re : RCLike.re (@inner ℂ _ ipsV.toInner x y) = cross t := by
    change (quotientInner hPD hH _ _).re = _
    rfl
  have hnorm_sq : ‖x - y‖ ^ 2 = 2 * ‖qα‖ ^ 2 - 2 * cross t := by
    rw [@norm_sub_sq ℂ, hx_norm, hy_norm, hinner_re]; ring
  -- From continuity: |cross t - cross t₀| < ε²/2
  have hcross_near : |cross t - cross t₀| < ε ^ 2 / 2 := by
    rw [← Real.dist_eq]; exact hδ_spec ht
  -- ‖x - y‖² = 2(cross t₀ - cross t) = 2(‖qα‖² - cross t)
  rw [← hcross_eq] at hnorm_sq
  -- ‖x - y‖² < ε²: unfold `hcross_near`'s absolute value to the two-sided bound
  -- `cross t₀ - cross t < ε²/2`, then substitute into `hnorm_sq = 2 * (cross t₀ - cross t)`.
  have _hnn : 0 ≤ ‖x - y‖ ^ 2 := sq_nonneg _
  have hnorm_bound : ‖x - y‖ ^ 2 < ε ^ 2 := by
    have := abs_lt.mp hcross_near
    linarith [this.2]
  -- ‖x - y‖ < ε
  nlinarith [sq_nonneg ‖x - y‖, sq_abs ε]

/-- For Finsupp α, t ↦ completionTranslate t (↑(mkQ α)) is continuous in the completion. -/
lemma completionTranslate_coe_continuous {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (hf : IsContinuous f) (α : ℝ →₀ ℂ) :
    letI := gnsQuotientNACG hPD hH
    letI := gnsQuotientIPS hPD hH
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    Continuous (fun t => completionTranslate hPD hH t
      (↑((pdNullSubmodule hPD hH).mkQ α) :
        UniformSpace.Completion (GNSQuotient hPD hH))) := by
  letI := gnsQuotientNACG hPD hH
  letI := gnsQuotientIPS hPD hH
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  -- completionTranslate t (↑(mkQ α)) = ↑(quotientTranslate t (mkQ α))
  have heq : (fun t => completionTranslate hPD hH t
      (↑((pdNullSubmodule hPD hH).mkQ α))) =
    (fun t => (↑(quotientTranslate hPD hH t
      ((pdNullSubmodule hPD hH).mkQ α)) :
        UniformSpace.Completion (GNSQuotient hPD hH))) := by
    ext t; exact completionTranslate_coe hPD hH t _
  rw [heq]
  exact (UniformSpace.Completion.continuous_coe _).comp
    (quotientTranslate_continuous hPD hH hf α)

/-- `completionTranslate t` preserves distances (isometry on the completion). -/
lemma completionTranslate_dist {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    letI := gnsQuotientNACG hPD hH
    letI := gnsQuotientIPS hPD hH
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    ∀ (x y : UniformSpace.Completion (GNSQuotient hPD hH)),
    dist (completionTranslate hPD hH t x) (completionTranslate hPD hH t y) =
    dist x y := by
  letI := gnsQuotientNACG hPD hH
  letI := gnsQuotientIPS hPD hH
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  -- ‖U(t)(x - y)‖² = ‖x - y‖² from inner product preservation
  have h := completionTranslate_inner hPD hH t (x - y) (x - y)
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    (by exact_mod_cast h)

/-- **Strong continuity**: for every ψ in the completion,
    t ↦ completionTranslate t ψ is continuous.

    A direct instance of the generic 3ε extension `Spectra.Bochner.GNS.strong_continuity_extends`:
    `completionTranslate` is norm-preserving (from `completionTranslate_dist`, specialized at `0`)
    and continuous on the dense range of the quotient embedding
    (`completionTranslate_coe_continuous`, via `mkQ`'s surjectivity). -/
theorem completionTranslate_strong_continuous {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (hf : IsContinuous f) :
    letI := gnsQuotientNACG hPD hH
    letI := gnsQuotientIPS hPD hH
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    ∀ (ψ : UniformSpace.Completion (GNSQuotient hPD hH)),
    Continuous (fun t => completionTranslate hPD hH t ψ) := by
  letI := gnsQuotientNACG hPD hH
  letI := gnsQuotientIPS hPD hH
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  have hiso : ∀ (t : ℝ) (ψ : UniformSpace.Completion (GNSQuotient hPD hH)),
      ‖completionTranslate hPD hH t ψ‖ = ‖ψ‖ := fun t ψ => by
    have h := completionTranslate_dist hPD hH t ψ 0
    rwa [map_zero, dist_zero_right, dist_zero_right] at h
  exact Spectra.Bochner.GNS.strong_continuity_extends
    (fun t => completionTranslate hPD hH t)
    hiso
    (Set.range ((↑) : GNSQuotient hPD hH → UniformSpace.Completion (GNSQuotient hPD hH)))
    (UniformSpace.Completion.denseRange_coe (α := GNSQuotient hPD hH))
    (by
      rintro φ ⟨v, rfl⟩
      obtain ⟨α, rfl⟩ := Submodule.mkQ_surjective (pdNullSubmodule hPD hH) v
      exact completionTranslate_coe_continuous hPD hH hf α)

end Spectra.Bochner.GNS
