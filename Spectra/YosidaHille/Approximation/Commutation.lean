/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.YosidaHille.Approximation.ExpBounded.Unitary

/-!
# Commutation properties for Duhamel's formula

Resolvents and Yosida approximants commute with the unitary exponentials, the skew-adjoint
exponentials are isometries, and — via Duhamel's formula — the symmetric approximants `Aₙˢʸᵐ`
generate a Cauchy sequence of unitaries. That Cauchy property is the analytic heart of the
convergence of the approximating evolutions.

## Main statements

* `yosidaApproxSym_commute` — the symmetric approximants commute with each other.
* `commute_exp` — anything commuting with `B` commutes with `exp(τB)`.
* `norm_expBounded_skewAdjoint` — the skew-adjoint exponential is an isometry.
* `norm_expBounded_pairwise_le` — the Duhamel estimate `‖exp(tBₘ)ψ - exp(tBₙ)ψ‖ ≤ |t|·‖(Bₘ-Bₙ)ψ‖`.
* `expBounded_yosidaApproxSym_cauchy_intrinsic` — `exp(i·Aₙˢʸᵐ·t)ψ` is Cauchy in `n`.
-/
open Complex MeasureTheory Filter Topology InnerProductSpace
open Spectra.Resolvent
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.YosidaHille.Approximation

/-- The symmetric Yosida approximants commute: `[Aₘˢʸᵐ, Aₙˢʸᵐ] = 0`. -/
lemma yosidaApproxSym_commute
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (m n : ℕ+) :
    Commute (yosidaApproxSym hsym hplus hminus m) (yosidaApproxSym hsym hplus hminus n) := by
  unfold yosidaApproxSym resolventAtIn resolventAtNegIn
  -- goal: Commute (c_m • (R(im) + R(-im))) (c_n • (R(in) + R(-in)))
  apply Commute.smul_left          -- strip c_m
  apply Commute.smul_right         -- strip c_n
  apply Commute.add_left           -- split R(im) + R(-im)
  · apply Commute.add_right        -- against R(in) + R(-in)
    · exact resolvent_commute hsym hplus hminus _ _ _ _   -- R(im),  R(in)
    · exact resolvent_commute hsym hplus hminus _ _ _ _   -- R(im),  R(-in)
  · apply Commute.add_right
    · exact resolvent_commute hsym hplus hminus _ _ _ _   -- R(-im), R(in)
    · exact resolvent_commute hsym hplus hminus _ _ _ _   -- R(-im), R(-in)


omit [CompleteSpace H] in
/-- If `C` commutes with `B`, it commutes with `exp(τB)`. -/
lemma commute_exp (C B : H →L[ℂ] H) (τ : ℝ) (h : Commute C B) :
    Commute C (expBounded B τ) := by
  rw [expBounded_eq_exp]
  exact (h.smul_right (τ : ℂ)).exp_right

/-- For skew-adjoint `B`, the exponential is an isometry: `‖exp(τB) v‖ = ‖v‖`. -/
lemma norm_expBounded_skewAdjoint (B : H →L[ℂ] H) (hB : B.adjoint = -B)
    (τ : ℝ) (v : H) : ‖expBounded B τ v‖ = ‖v‖ := by
  set u := expBounded B τ
  have hadj : u.adjoint.comp u = ContinuousLinearMap.id ℂ H :=
    (expBounded_skewAdjoint_unitary B hB τ).1
  have hfix : u.adjoint (u v) = v := by
    have := congrArg (fun T : H →L[ℂ] H => T v) hadj
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using this
  have key : ⟪u v, u v⟫_ℂ = ⟪v, v⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right u v (u v), hfix]
  have hsq : ‖u v‖ ^ 2 = ‖v‖ ^ 2 := by
    have h1 := congrArg RCLike.re key
    rwa [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at h1
  have := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this

/-- Duhamel estimate: for commuting skew-adjoint `Bₘ`, `Bₙ`,
`‖exp(tBₘ)ψ - exp(tBₙ)ψ‖ ≤ |t|·‖(Bₘ - Bₙ)ψ‖`. -/
lemma norm_expBounded_pairwise_le
    (Bm Bn : H →L[ℂ] H) (hcomm : Commute Bm Bn)
    (hm : Bm.adjoint = -Bm) (hn : Bn.adjoint = -Bn) (t : ℝ) (ψ : H) :
    ‖expBounded Bm t ψ - expBounded Bn t ψ‖ ≤ |t| * ‖(Bm - Bn) ψ‖ := by
  have hderiv : ∀ s : ℝ, HasDerivAt
      (fun s => expBounded Bn (t - s) (expBounded Bm s ψ))
      (expBounded Bn (t - s) (expBounded Bm s ((Bm - Bn) ψ))) s := by
    intro s
    have hf : HasDerivAt (fun s => expBounded Bn (t - s))
        (-(Bn.comp (expBounded Bn (t - s)))) s := by
      have h2 : HasDerivAt (fun s : ℝ => t - s) (-1) s := by
        simpa using (hasDerivAt_id s).const_sub t
      simpa [neg_one_smul, Function.comp_def] using
        (expBounded_hasDerivAt Bn (t - s)).scomp s h2
    have hu : HasDerivAt (fun s => expBounded Bm s ψ) (Bm (expBounded Bm s ψ)) s := by
      have h := ((ContinuousLinearMap.apply ℂ H ψ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
        (expBounded_hasDerivAt Bm s)
      exact HasDerivAt.congr_deriv h rfl
    have hcEm : Commute (Bm - Bn) (expBounded Bm s) :=
      (B_commute_expBounded Bm s).sub_left (commute_exp Bn Bm s hcomm.symm)
    have comm_Em : expBounded Bm s ((Bm - Bn) ψ) = (Bm - Bn) (expBounded Bm s ψ) := by
      have h := congrArg (fun T : H →L[ℂ] H => T ψ) hcEm
      simpa [ContinuousLinearMap.mul_apply] using h.symm
    have comm_En : expBounded Bn (t - s) (Bn (expBounded Bm s ψ))
        = Bn (expBounded Bn (t - s) (expBounded Bm s ψ)) := by
      have h := congrArg (fun T : H →L[ℂ] H => T (expBounded Bm s ψ))
                  (B_commute_expBounded Bn (t - s)).symm
      simpa [ContinuousLinearMap.mul_apply] using h
    -- rewrite the clean derivative into the raw clm_apply form, then discharge
    have hval : expBounded Bn (t - s) (expBounded Bm s ((Bm - Bn) ψ))
        = (-(Bn.comp (expBounded Bn (t - s)))) (expBounded Bm s ψ)
          + expBounded Bn (t - s) (Bm (expBounded Bm s ψ)) := by
      rw [comm_Em, ContinuousLinearMap.sub_apply, map_sub,
          ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply, comm_En]
      abel
    have hf' := (ContinuousLinearMap.restrictScalarsL ℂ H H ℝ ℝ).hasFDerivAt.comp_hasDerivAt s hf
    rw [hval]
    simpa using hf'.clm_apply hu
  have cont_g' : Continuous
      (fun s : ℝ => expBounded Bn (t - s) (expBounded Bm s ((Bm - Bn) ψ))) := by
    have cBn : Continuous (fun τ : ℝ => expBounded Bn τ) :=
      Differentiable.continuous fun τ => (expBounded_hasDerivAt Bn τ).differentiableAt
    have cBm : Continuous (fun τ : ℝ => expBounded Bm τ) :=
      Differentiable.continuous fun τ => (expBounded_hasDerivAt Bm τ).differentiableAt
    exact (cBn.comp (continuous_const.sub continuous_id)).clm_apply
          (cBm.clm_apply continuous_const)
  have hftc : (∫ s in (0:ℝ)..t, expBounded Bn (t - s) (expBounded Bm s ((Bm - Bn) ψ)))
      = expBounded Bm t ψ - expBounded Bn t ψ := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s => expBounded Bn (t - s) (expBounded Bm s ψ))
      (fun s _ => hderiv s) (cont_g'.intervalIntegrable 0 t)
    simpa [sub_self, sub_zero, expBounded_at_zero] using h
  have hnorm_const : ∀ s : ℝ,
      ‖expBounded Bn (t - s) (expBounded Bm s ((Bm - Bn) ψ))‖ = ‖(Bm - Bn) ψ‖ := by
    intro s
    rw [norm_expBounded_skewAdjoint Bn hn (t - s), norm_expBounded_skewAdjoint Bm hm s]
  calc ‖expBounded Bm t ψ - expBounded Bn t ψ‖
      = ‖∫ s in (0:ℝ)..t, expBounded Bn (t - s) (expBounded Bm s ((Bm - Bn) ψ))‖ := by
        rw [hftc]
    _ ≤ ‖(Bm - Bn) ψ‖ * |t - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro s _
        exact le_of_eq (hnorm_const s)
    _ = |t| * ‖(Bm - Bn) ψ‖ := by rw [sub_zero, mul_comm]

/-- The unitaries `exp(i·Aₙˢʸᵐ·t)ψ` form a Cauchy sequence in `n`, for every `ψ`. -/
lemma expBounded_yosidaApproxSym_cauchy_intrinsic
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (hdense : Dense (A.domain : Set H)) (t : ℝ) (ψ : H) :
    CauchySeq (fun n : ℕ+ =>
      expBounded (I • yosidaApproxSym hsym hplus hminus n) t ψ) := by
  let E : ℕ+ → (H →L[ℂ] H) :=
    fun n => expBounded (I • yosidaApproxSym hsym hplus hminus n) t
  change CauchySeq (fun n => E n ψ)
  -- each Eₙ is an isometry, so it preserves distances
  have hiso : ∀ (n : ℕ+) (a b : H), dist (E n a) (E n b) = dist a b := by
    intro n a b
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact expBounded_yosidaApproxSym_isometry hsym hplus hminus n t (a - b)
  -- the pairwise estimate, with the I-scalars and the spurious ‖I‖ stripped
  have hpair : ∀ (m n : ℕ+) (φ : H),
      dist (E m φ) (E n φ)
        ≤ |t| * dist (yosidaApproxSym hsym hplus hminus m φ)
                     (yosidaApproxSym hsym hplus hminus n φ) := by
    intro m n φ
    have hcomm : Commute (I • yosidaApproxSym hsym hplus hminus m)
        (I • yosidaApproxSym hsym hplus hminus n) :=
      ((yosidaApproxSym_commute hsym hplus hminus m n).smul_left I).smul_right I
    have h := norm_expBounded_pairwise_le
      (I • yosidaApproxSym hsym hplus hminus m) (I • yosidaApproxSym hsym hplus hminus n)
      hcomm (I_smul_yosidaApproxSym_skewAdjoint hsym hplus hminus m)
      (I_smul_yosidaApproxSym_skewAdjoint hsym hplus hminus n) t φ
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖E m φ - E n φ‖
        ≤ |t| * ‖(I • yosidaApproxSym hsym hplus hminus m
                  - I • yosidaApproxSym hsym hplus hminus n) φ‖ := h
      _ = |t| * ‖yosidaApproxSym hsym hplus hminus m φ
                  - yosidaApproxSym hsym hplus hminus n φ‖ := by
          rw [← smul_sub, ContinuousLinearMap.smul_apply, norm_smul, Complex.norm_I,
              one_mul, ContinuousLinearMap.sub_apply]
  -- on the domain, Aₙˢʸᵐ φ converges, hence is Cauchy, hence so is Eₙ φ
  have hdom : ∀ φ : H, φ ∈ A.domain → CauchySeq (fun n : ℕ+ => E n φ) := by
    intro φ hφ
    have hAcauchy : CauchySeq (fun n : ℕ+ => yosidaApproxSym hsym hplus hminus n φ) :=
      (yosidaApproxSym_tendsto_on_domain hsym hplus hminus hdense φ hφ).cauchySeq
    rw [Metric.cauchySeq_iff] at hAcauchy ⊢
    intro ε hε
    have hpos : (0:ℝ) < |t| + 1 := by positivity
    have hne : (|t| + 1) ≠ 0 := hpos.ne'
    obtain ⟨N, hN⟩ := hAcauchy (ε / (|t| + 1)) (div_pos hε hpos)
    refine ⟨N, fun m hm n hn => ?_⟩
    calc dist (E m φ) (E n φ)
        ≤ |t| * dist (yosidaApproxSym hsym hplus hminus m φ)
                     (yosidaApproxSym hsym hplus hminus n φ) := hpair m n φ
      _ ≤ (|t| + 1) * dist (yosidaApproxSym hsym hplus hminus m φ)
                     (yosidaApproxSym hsym hplus hminus n φ) :=
          mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
      _ < (|t| + 1) * (ε / (|t| + 1)) := mul_lt_mul_of_pos_left (hN m hm n hn) hpos
      _ = ε := by field_simp
  -- general ψ: 3ε against a dense domain point
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨φ, hφ_dom, hφ_close⟩ :=
    Metric.mem_closure_iff.mp (hdense ψ) (ε / 3) (by linarith)
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp (hdom φ hφ_dom)) (ε / 3) (by linarith)
  refine ⟨N, fun m hm n hn => ?_⟩
  calc dist (E m ψ) (E n ψ)
      ≤ dist (E m ψ) (E m φ) + dist (E m φ) (E n φ) + dist (E n φ) (E n ψ) :=
        dist_triangle4 _ _ _ _
    _ = dist ψ φ + dist (E m φ) (E n φ) + dist φ ψ := by rw [hiso m ψ φ, hiso n φ ψ]
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have h3 : dist φ ψ < ε / 3 := by rw [dist_comm]; exact hφ_close
        linarith [hN m hm n hn, hφ_close]
    _ = ε := by ring

end Spectra.YosidaHille.Approximation
