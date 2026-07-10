/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.YosidaHille.Approximation.Exponential
import Spectra.Resolvent.Integral.Domain

/-!
# Uniqueness for Stone's lemma

A strongly continuous one-parameter unitary group is determined by its generator: two groups with
the same generator are equal. The proof differentiates the curve `σ ↦ V(t-σ)(W(σ)ψ)`, shows its
derivative vanishes (from the generator's defining derivative and the group law), concludes it is
constant, and so `V(t) = W(t)` on the dense generator domain — hence everywhere.

## Main statements

* `unitary_orbit_hasDerivAt` — the orbit `t ↦ U(t)x` solves `f'(t) = i·U(t)(gen U x)`.
* `generator_comm` — the generator commutes with the group: `gen U (U(s)x) = U(s)(gen U x)`.
* `group_apply_curve_hasDerivAt` — product/chain rule for `σ ↦ V(r σ)(v σ)`.
* `group_unique` — equal generators imply equal groups.

## References

* [Stone, "On one-parameter unitary groups in Hilbert space"][stone1932]
* [von Neumann, "Über Funktionen von Funktionaloperatoren"][vonneumann1932]
* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], lemma VIII.8

## Tags

Stone's lemma, unitary group, self-adjoint operator, spectral theory
-/
open InnerProductSpace Complex Filter Topology
open Spectra.OneParameterUnitaryGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.YosidaHille

/-- The orbit `t ↦ U(t)x` is differentiable, with derivative `i·U(s)(gen U x)`. -/
lemma unitary_orbit_hasDerivAt (U : OneParameterUnitaryGroup (H := H))
    (x : (generator U).domain) (s : ℝ) :
    HasDerivAt (fun t : ℝ => U.U t (x : H)) (I • U.U s (generator U x)) s := by
  -- (A) the s = 0 case, straight from generator_tendsto
  have hA0 : HasDerivAt (fun t : ℝ => U.U t (x : H)) (I • generator U x) 0 := by
    rw [hasDerivAt_iff_tendsto_slope]
    refine ((generator_tendsto U x).const_smul I).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t _
    have h0 : U.U (0 : ℝ) (x : H) = (x : H) := by rw [U.identity, ContinuousLinearMap.id_apply]
    rw [slope_def_module, sub_zero, h0]
    simp only [genDiffQuot, smul_smul]
    rw [show (t : ℝ)⁻¹ • (U.U t (x : H) - x) = ((t : ℂ)⁻¹) • (U.U t (x : H) - x) by
          rw [← Complex.coe_smul, Complex.ofReal_inv]]
    congr 1
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ Complex.I_ne_zero, one_mul]
  -- (B) push through U.U s, then the group law
  have hB : HasDerivAt (fun h : ℝ => U.U s (U.U h (x : H))) (I • U.U s (generator U x)) 0 := by
    have h := ((U.U s).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hA0
    simp only [ContinuousLinearMap.coe_restrictScalars', generator_domain, map_smul] at h
    exact HasDerivAt.congr_deriv h rfl
  have hgl : (fun h : ℝ => U.U s (U.U h (x : H))) = fun h : ℝ => U.U (s + h) (x : H) := by
    funext h; rw [U.group_law, ContinuousLinearMap.comp_apply]
  rw [hgl] at hB
  -- (C) translate from 0 back to s
  set e : ℝ → ℝ := fun t => t - s with he_def
  have he  : HasDerivAt e 1 s := by rw [he_def]; exact (hasDerivAt_id s).sub_const s
  have hes : e s = 0 := by rw [he_def]; simp
  have hB0 : HasDerivAt (fun h : ℝ => U.U (s + h) (x : H))
      (I • U.U s (generator U x)) (e s) := by rw [hes]; exact hB
  have hC := hB0.scomp s he
  simp only [Function.comp_def, one_smul, he_def] at hC
  rwa [show (fun t : ℝ => U.U (s + (t - s)) (x : H)) = fun t : ℝ => U.U t (x : H) by
        funext t; rw [show s + (t - s) = t from by ring]] at hC

/-- The generator commutes with the group: `gen U (U(s)x) = U(s)(gen U x)`. -/
lemma generator_comm (U : OneParameterUnitaryGroup (H := H)) (s : ℝ) (x : (generator U).domain) :
    generator U ⟨U.U s (x : H), generator_domain_invariant U s x⟩ = U.U s (generator U x) := by
  refine tendsto_nhds_unique
    (generator_tendsto U ⟨U.U s (x : H), generator_domain_invariant U s x⟩) ?_
  have hpt : genDiffQuot U (U.U s (x : H)) = fun r => U.U s (genDiffQuot U (x : H) r) := by
    funext r
    simp only [genDiffQuot_apply, map_smul]
    congr 1
    rw [map_sub]
    have hcomm : U.U r (U.U s (x : H)) = U.U s (U.U r (x : H)) := by
      have h1 : U.U r (U.U s (x : H)) = U.U (r + s) (x : H) := by
        rw [← ContinuousLinearMap.comp_apply, ← U.group_law]
      have h2 : U.U s (U.U r (x : H)) = U.U (s + r) (x : H) := by
        rw [← ContinuousLinearMap.comp_apply, ← U.group_law]
      rw [h1, h2, add_comm]
    rw [hcomm]
  rw [hpt]
  exact ((U.U s).continuous.tendsto _).comp (generator_tendsto U x)

open Asymptotics in
/-- Product/chain rule for the derivative of `σ ↦ V(r σ)(v σ)` along differentiable `v`, `r`. -/
lemma group_apply_curve_hasDerivAt (V : OneParameterUnitaryGroup (H := H))
    {v : ℝ → H} {v' : H} {r : ℝ → ℝ} {r' : ℝ} {s : ℝ}
    (hv : HasDerivAt v v' s) (hr : HasDerivAt r r' s)
    (hmem : v s ∈ (generator V).domain) :
    HasDerivAt (fun σ => V.U (r σ) (v σ))
      (r' • (I • V.U (r s) (generator V ⟨v s, hmem⟩)) + V.U (r s) v') s := by
  set η := generator V ⟨v s, hmem⟩ with _hη
  have hp : HasDerivAt (fun σ => V.U (r σ) (v s)) (r' • (I • V.U (r s) η)) s :=
    (unitary_orbit_hasDerivAt V ⟨v s, hmem⟩ (r s)).scomp s hr
  have hq : HasDerivAt (fun σ => V.U (r s) (v σ)) (V.U (r s) v') s := by
    have h := ((V.U (r s)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hv
    simp only [ContinuousLinearMap.coe_restrictScalars'] at h
    exact HasDerivAt.congr_deriv h rfl
  -- remainder R = (V(rσ) - V(rs))(vσ - vs) is o(σ - s)
  have hRem : (fun σ => V.U (r σ) (v σ) - V.U (r σ) (v s)
                - V.U (r s) (v σ) + V.U (r s) (v s)) =o[𝓝 s] (fun σ => σ - s) := by
    have hv_o : (fun σ => v σ - v s - (σ - s) • v') =o[𝓝 s] (fun σ => σ - s) :=
      hasDerivAt_iff_isLittleO.mp hv
    -- T1 : the o-remainder of v, hit by operators of norm 1 (so still o)
    have hT1 : (fun σ => V.U (r σ) (v σ - v s - (σ - s) • v')
                  - V.U (r s) (v σ - v s - (σ - s) • v')) =o[𝓝 s] (fun σ => σ - s) := by
      refine (IsBigO.of_bound 2 ?_).trans_isLittleO hv_o
      filter_upwards with σ
      calc ‖V.U (r σ) (v σ - v s - (σ - s) • v') - V.U (r s) (v σ - v s - (σ - s) • v')‖
          ≤ ‖V.U (r σ) (v σ - v s - (σ - s) • v')‖
              + ‖V.U (r s) (v σ - v s - (σ - s) • v')‖ := norm_sub_le _ _
        _ = ‖v σ - v s - (σ - s) • v'‖ + ‖v σ - v s - (σ - s) • v'‖ := by
            rw [norm_preserving, norm_preserving]
        _ = 2 * ‖v σ - v s - (σ - s) • v'‖ := by ring
    -- T2 : (σ-s) • [(V(rσ) - V(rs)) v'], bracket → 0 by strong continuity
    have hD : Tendsto (fun σ => V.U (r σ) v' - V.U (r s) v') (𝓝 s) (𝓝 0) := by
      have hc : Tendsto (fun σ => V.U (r σ) v') (𝓝 s) (𝓝 (V.U (r s) v')) :=
        (V.strong_continuous v').continuousAt.comp hr.continuousAt
      exact tendsto_sub_nhds_zero_iff.mpr hc
    have hT2 : (fun σ => (σ - s) • (V.U (r σ) v' - V.U (r s) v'))
        =o[𝓝 s] (fun σ => σ - s) := by
      rw [isLittleO_iff]
      intro ε hε
      have hDn : Tendsto (fun σ => ‖V.U (r σ) v' - V.U (r s) v'‖) (𝓝 s) (𝓝 0) := by
        simpa using hD.norm
      filter_upwards [hDn.eventually (eventually_lt_nhds hε)] with σ hσ
      rw [norm_smul]
      calc ‖(σ - s : ℝ)‖ * ‖V.U (r σ) v' - V.U (r s) v'‖
          ≤ ‖(σ - s : ℝ)‖ * ε := by gcongr
        _ = ε * ‖σ - s‖ := by ring
    refine (hT1.add hT2).congr_left fun σ => ?_
    change (V.U (r σ) (v σ - v s - (σ - s) • v') - V.U (r s) (v σ - v s - (σ - s) • v'))
        + (σ - s) • (V.U (r σ) v' - V.U (r s) v')
      = V.U (r σ) (v σ) - V.U (r σ) (v s) - V.U (r s) (v σ) + V.U (r s) (v s)
    simp only [map_sub, smul_sub]
    norm_num; abel_nf
  rw [hasDerivAt_iff_isLittleO] at hp hq ⊢
  refine ((hp.add hq).add hRem).congr_left fun σ => ?_
  norm_num; abel

open Spectra.Resolvent in
/-- A one-parameter unitary group is determined by its generator. -/
lemma group_unique (V W : OneParameterUnitaryGroup (H := H))
    (h : generator V = generator W) : V = W := by
  have hdom : (generator V).domain = (generator W).domain := by rw [h]
  suffices hU : V.U = W.U by
    obtain ⟨Vu, hV1, hV2, hV3, hV4⟩ := V
    obtain ⟨Wu, hW1, hW2, hW3, hW4⟩ := W
    subst hU; rfl
  funext t
  have hdense : Dense ((generator V).domain : Set H) := generatorDomain_dense_via_average V
  have hpt : ∀ ψ ∈ (generator V).domain, V.U t ψ = W.U t ψ := by
    intro ψ hψV
    have hψW : ψ ∈ (generator W).domain := hdom ▸ hψV
    set g : ℝ → H := fun σ => V.U (t - σ) (W.U σ ψ) with hg_def
    have hg_all : ∀ σ : ℝ, HasDerivAt g 0 σ := by
      intro σ
      have hmem : W.U σ ψ ∈ (generator V).domain := by
        rw [h]; exact generator_domain_invariant W σ ⟨ψ, hψW⟩
      have hcurve := group_apply_curve_hasDerivAt V
        (v := fun τ => W.U τ ψ) (v' := I • W.U σ (generator W ⟨ψ, hψW⟩))
        (r := fun τ => t - τ) (r' := -1) (s := σ)
        (unitary_orbit_hasDerivAt W ⟨ψ, hψW⟩ σ)
        ((hasDerivAt_id σ).const_sub t) hmem
      have hmem' : W.U σ ψ ∈ (generator W).domain := generator_domain_invariant W σ ⟨ψ, hψW⟩
      have hkey : generator V ⟨W.U σ ψ, hmem⟩ = W.U σ (generator W ⟨ψ, hψW⟩) := by
        have hVW : generator V ⟨W.U σ ψ, hmem⟩ = generator W ⟨W.U σ ψ, hmem'⟩ :=
          (le_of_eq h).2 (x := ⟨W.U σ ψ, hmem⟩) (y := ⟨W.U σ ψ, hmem'⟩) rfl
        rw [hVW]; exact generator_comm W σ ⟨ψ, hψW⟩
      rw [show (-1 : ℝ) • (I • V.U (t - σ) (generator V ⟨W.U σ ψ, hmem⟩))
            + V.U (t - σ) (I • W.U σ (generator W ⟨ψ, hψW⟩)) = 0 by
            rw [hkey, map_smul, neg_one_smul, neg_add_cancel]] at hcurve
      exact hcurve
    have hg0t : g 0 = g t :=
      is_const_of_deriv_eq_zero (fun σ => (hg_all σ).differentiableAt)
        (fun σ => (hg_all σ).deriv) 0 t
    simpa [hg_def, W.identity, V.identity, ContinuousLinearMap.id_apply,
      sub_zero, sub_self] using hg0t
  exact ContinuousLinearMap.ext fun ψ =>
    congrFun (Continuous.ext_on hdense (V.U t).continuous (W.U t).continuous hpt) ψ

end Spectra.YosidaHille
