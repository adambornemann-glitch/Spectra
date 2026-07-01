/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: ProjValMeasure/PdInterface.lean
-/
import Spectra.PositiveDefinite.Unitary

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Analysis.Fourier.AddCircleMulti

open Complex MeasureTheory
open scoped InnerProductSpace ContinuousFunctionalCalculus
open Spectra.PositiveDefinite
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (U : H →L[ℂ] H)

namespace Spectra.ProjValMeasure


/-! ### The PVM interface -/

/-- Scaling the vector scales the correlation by `‖c‖²`. -/
private lemma unitaryCorrelation_smul [CompleteSpace H] (c : ℂ) (ψ : H) (n : ℤ) :
    unitaryCorrelation U (c • ψ) n = ↑(‖c‖ ^ 2) * unitaryCorrelation U ψ n := by
  simp only [unitaryCorrelation, ContinuousLinearMap.map_smul,
             inner_smul_left, inner_smul_right, ← mul_assoc]
  congr 1
  rw [← mul_comm (starRingEnd ℂ c) c]
  simp only [ofReal_pow]
  exact conj_mul' c

/-- Polarization for the matrix elements of any operator: the off-diagonal
`⟪T ψ, φ⟫` is a fixed combination of the diagonal quadratic form `z ↦ ⟪T z, z⟫`.
Generalizes `cross_measure_polarization` from `ProjValMeasure.lean`. -/
lemma inner_op_eq_polarization (T : H →L[ℂ] H) (ψ φ : H) :
    ⟪T ψ, φ⟫_ℂ =
      (1 / 4 : ℂ) *
        ( ⟪T (ψ + φ), ψ + φ⟫_ℂ - ⟪T (ψ - φ), ψ - φ⟫_ℂ
          - I * ⟪T (ψ + I • φ), ψ + I • φ⟫_ℂ
          + I * ⟪T (ψ - I • φ), ψ - I • φ⟫_ℂ ) := by
  have hI : (starRingEnd ℂ) I = -I := by change star I = -I; simp [Complex.conj_I]
  simp only [map_add, map_sub, map_smul,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, hI]
  ring_nf; simp only [Complex.I_sq]; ring

variable (μ : H → Measure ℝ)

/-- The polarized cross functional `g ↦ ∫ g dμ_{ψ,φ}`, assembled from the four
scalar spectral measures `μ_{ψ±φ}`, `μ_{ψ±iφ}`. -/
noncomputable def crossInner (g : ℝ → ℂ) (ψ φ : H) : ℂ :=
  (1 / 4 : ℂ) *
    ( (∫ θ, g θ ∂(μ (ψ + φ))) - (∫ θ, g θ ∂(μ (ψ - φ)))
      - I * (∫ θ, g θ ∂(μ (ψ + I • φ)))
      + I * (∫ θ, g θ ∂(μ (ψ - I • φ))) )

/-- **The bridge.** Any operator `T` reproducing the *diagonal* scalar integrals
reproduces the whole cross functional. The Riesz step need only hit the diagonal. -/
lemma crossInner_eq_inner_of_diag {g : ℝ → ℂ} {T : H →L[ℂ] H}
    (hdiag : ∀ z : H, ⟪T z, z⟫_ℂ = ∫ θ, g θ ∂(μ z)) (ψ φ : H) :
    crossInner μ g ψ φ = ⟪T ψ, φ⟫_ℂ := by
  rw [inner_op_eq_polarization T ψ φ]
  unfold crossInner
  rw [hdiag (ψ + φ), hdiag (ψ - φ), hdiag (ψ + I • φ), hdiag (ψ - I • φ)]


/-- `‖crossInner‖ ≤ ‖g‖∞·(‖ψ‖²+‖φ‖²)`; homogenizing in `(ψ,φ)` upgrades this to
the sesquilinear `2‖g‖∞·‖ψ‖·‖φ‖`. -/
lemma crossInner_norm_le {g : ℝ → ℂ} {C : ℝ} (_hC : 0 ≤ C) (hg : ∀ θ, ‖g θ‖ ≤ C)
    (hfin : ∀ z, IsFiniteMeasure (μ z))
    (hmass : ∀ z, ((μ z) Set.univ).toReal = ‖z‖ ^ 2) (ψ φ : H) :
    ‖crossInner μ g ψ φ‖ ≤ C * (‖ψ‖ ^ 2 + ‖φ‖ ^ 2) := by
  -- per-term bound: ‖∫ g dμ_z‖ ≤ C·‖z‖²
  have hterm : ∀ z : H, ‖∫ θ, g θ ∂(μ z)‖ ≤ C * ‖z‖ ^ 2 := by
    intro z
    haveI := hfin z
    have hb : ‖∫ θ, g θ ∂(μ z)‖ ≤ C * (μ z).real Set.univ :=
      norm_integral_le_of_norm_le_const (ae_of_all _ hg)
    rwa [measureReal_def, hmass z] at hb
  -- name the four scalar integrals
  unfold crossInner
  set P := ∫ θ, g θ ∂(μ (ψ + φ)) with hP
  set Q := ∫ θ, g θ ∂(μ (ψ - φ)) with hQ
  set R := ∫ θ, g θ ∂(μ (ψ + I • φ)) with hR
  set S := ∫ θ, g θ ∂(μ (ψ - I • φ)) with hS
  -- triangle inequality (|I| = 1)
  have eIR : ‖I * R‖ = ‖R‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have eIS : ‖I * S‖ = ‖S‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have hsum : ‖P - Q - I * R + I * S‖ ≤ ‖P‖ + ‖Q‖ + ‖R‖ + ‖S‖ := by
    have e1 : ‖P - Q - I * R + I * S‖ ≤ ‖P - Q - I * R‖ + ‖I * S‖ := norm_add_le _ _
    have e2 : ‖P - Q - I * R‖ ≤ ‖P - Q‖ + ‖I * R‖ := norm_sub_le _ _
    have e3 : ‖P - Q‖ ≤ ‖P‖ + ‖Q‖ := norm_sub_le _ _
    rw [eIR] at e2; rw [eIS] at e1
    linarith
  -- per-term bounds + parallelogram law
  have key : ‖P‖ + ‖Q‖ + ‖R‖ + ‖S‖ ≤ 4 * (C * (‖ψ‖ ^ 2 + ‖φ‖ ^ 2)) := by
    have hP' : ‖P‖ ≤ C * ‖ψ + φ‖ ^ 2 := by rw [hP]; exact hterm _
    have hQ' : ‖Q‖ ≤ C * ‖ψ - φ‖ ^ 2 := by rw [hQ]; exact hterm _
    have hR' : ‖R‖ ≤ C * ‖ψ + I • φ‖ ^ 2 := by rw [hR]; exact hterm _
    have hS' : ‖S‖ ≤ C * ‖ψ - I • φ‖ ^ 2 := by rw [hS]; exact hterm _
    have hIφ : ‖I • φ‖ = ‖φ‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    have hpar1 : ‖ψ + φ‖ ^ 2 + ‖ψ - φ‖ ^ 2 = 2 * (‖ψ‖ ^ 2 + ‖φ‖ ^ 2) :=
      parallelogram_law_with_norm ℂ ψ φ
    have hpar2 : ‖ψ + I • φ‖ ^ 2 + ‖ψ - I • φ‖ ^ 2 = 2 * (‖ψ‖ ^ 2 + ‖φ‖ ^ 2) := by
      rw [parallelogram_law_with_norm ℂ ψ (I • φ), hIφ]
    have hsum_eq :
        C * ‖ψ + φ‖ ^ 2 + C * ‖ψ - φ‖ ^ 2 + C * ‖ψ + I • φ‖ ^ 2 + C * ‖ψ - I • φ‖ ^ 2
          = 4 * (C * (‖ψ‖ ^ 2 + ‖φ‖ ^ 2)) := by
      have h4 : ‖ψ + φ‖ ^ 2 + ‖ψ - φ‖ ^ 2 + (‖ψ + I • φ‖ ^ 2 + ‖ψ - I • φ‖ ^ 2)
          = 4 * (‖ψ‖ ^ 2 + ‖φ‖ ^ 2) := by rw [hpar1, hpar2]; ring
      linear_combination C * h4
    linarith [hP', hQ', hR', hS', hsum_eq]
  -- assemble: ‖(1/4)·bracket‖ = (1/4)·‖bracket‖ ≤ (1/4)·4·C·(…) = C·(…)
  have h14 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by rw [norm_div, norm_one, Complex.norm_ofNat]
  rw [norm_mul, h14]
  calc (1 / 4) * ‖P - Q - I * R + I * S‖
      ≤ (1 / 4) * (4 * (C * (‖ψ‖ ^ 2 + ‖φ‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left (le_trans hsum key) (by norm_num)
    _ = C * (‖ψ‖ ^ 2 + ‖φ‖ ^ 2) := by ring

/-- **The functional-calculus L²-isometry.** `‖cfc f U z‖² = ⟪z, cfc |f|² U z⟫`.
Through your diagonal relation `⟪cfc h U z, z⟫ = ∫ (h∘e) dμ_z`, the right side is
`∫ |g|² dμ_z` — and *that* is what makes `cfc gₙ U z` a Cauchy sequence. -/
lemma cfc_norm_sq_eq_inner [CompleteSpace H]
    (U : H →L[ℂ] H) (_hU : IsStarNormal U)
    (f : ℂ → ℂ) (hf : ContinuousOn f (spectrum ℂ U)) (z : H) :
    ‖cfc f U z‖ ^ 2
      = (⟪z, cfc (fun x => (starRingEnd ℂ) (f x) * f x) U z⟫_ℂ).re := by
  have hadj : (cfc f U).adjoint = cfc (fun x => (starRingEnd ℂ) (f x)) U := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← cfc_star]
    exact cfc_congr fun ⦃x⦄ => congrFun rfl
  calc ‖cfc f U z‖ ^ 2
      = (⟪cfc f U z, cfc f U z⟫_ℂ).re := by
        rw [inner_self_eq_norm_sq_to_K]; norm_cast
    _ = (⟪z, (cfc f U).adjoint (cfc f U z)⟫_ℂ).re := by
        rw [ContinuousLinearMap.adjoint_inner_right]
    _ = (⟪z, cfc (fun x => (starRingEnd ℂ) (f x) * f x) U z⟫_ℂ).re := by
        have hconj : ContinuousOn (fun x => (starRingEnd ℂ) (f x)) (spectrum ℂ U) :=
          continuous_star.comp_continuousOn hf
        have hop : (cfc (fun x => (starRingEnd ℂ) (f x)) U).comp (cfc f U)
            = cfc (fun x => (starRingEnd ℂ) (f x) * f x) U := by
          rw [show (cfc (fun x => (starRingEnd ℂ) (f x)) U).comp (cfc f U)
                 = cfc (fun x => (starRingEnd ℂ) (f x)) U * cfc f U from rfl,
              ← cfc_mul (hf := hconj) (hg := hf)]
        rw [hadj, ← ContinuousLinearMap.comp_apply, hop]

/-- The diagonal `z ↦ ⟪z, A z⟫` of any operator obeys the parallelogram law —
the moment identity behind the measure-level parallelogram (take `A = Uⁿ`). -/
lemma diag_parallelogram (A : H →L[ℂ] H) (ψ φ : H) :
    ⟪ψ + φ, A (ψ + φ)⟫_ℂ + ⟪ψ - φ, A (ψ - φ)⟫_ℂ
      = 2 * ⟪ψ, A ψ⟫_ℂ + 2 * ⟪φ, A φ⟫_ℂ := by
  simp only [map_add, map_sub, inner_add_left, inner_add_right,
             inner_sub_left, inner_sub_right]
  ring

/-- Recommended: extract the finite-measure uniqueness hiding inside
`stieltjes_measure_eq_of_fourier_eq`. The Stieltjes structure is never used. -/
lemma measure_eq_of_fourier_eq (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (Set.Icc 0 (2*Real.pi))ᶜ = 0) (hν : ν (Set.Icc 0 (2*Real.pi))ᶜ = 0)
    (h0μ : μ {0} = 0) (h0ν : ν {0} = 0)
    (h : ∀ n : ℤ, ∫ θ in Set.Ioc 0 (2*Real.pi), exp (I*n*θ) ∂μ
                = ∫ θ in Set.Ioc 0 (2*Real.pi), exp (I*n*θ) ∂ν) :
    μ = ν := by
  classical
  set T : ℝ := 2 * Real.pi with hT          -- `set` folds 2π→T in all hyps (h_supp_*, h)
  haveI : Fact (0 < T) := ⟨by rw [hT]; positivity⟩
  -- quotient map and the section onto the fundamental domain (0,T]
  set q : ℝ → AddCircle T := ((↑) : ℝ → AddCircle T) with hq_def
  have hq : Measurable q := AddCircle.measurable_mk'
  set ι : AddCircle T → ℝ :=
    fun c => ((AddCircle.equivIoc T 0 c : Set.Ioc (0:ℝ) (0 + T)) : ℝ) with hι_def
  have hι : Measurable ι :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIoc T 0).measurable
  -- (1) both measures are concentrated on (0,T]
  have hconc : ∀ μ : Measure ℝ, μ (Set.Icc 0 T)ᶜ = 0 → μ {(0:ℝ)} = 0 →
      μ (Set.Ioc 0 T)ᶜ = 0 := by
    intro μ hIcc h0
    refine measure_mono_null ?_ (measure_union_null hIcc h0)
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and, not_le] at hx
    by_cases hx0 : x = 0
    · exact Or.inr hx0
    · refine Or.inl ?_
      simp only [Set.mem_compl_iff, Set.mem_Icc, not_and, not_le]
      exact fun hnn => hx (lt_of_le_of_ne hnn (Ne.symm hx0))
  have hcF : μ (Set.Ioc 0 T)ᶜ = 0 := hconc _ hμ h0μ
  have hcG : ν (Set.Ioc 0 T)ᶜ = 0 := hconc _ hν h0ν
  -- (2) characters pull back correctly:  fourier n (q x) = exp (I n x)
  have hchar : ∀ (n : ℤ) (x : ℝ), fourier n (q x) = Complex.exp (I * n * x) := by
    intro n x
    rw [hq_def, fourier_coe_apply, hT]                   -- exp(2π I n x / (2π))
    congr 1; field_simp
    simp only [ofReal_mul, ofReal_ofNat]
    ring
  haveI : IsFiniteMeasure (Measure.map q μ) := μ.isFiniteMeasure_map q
  haveI : IsFiniteMeasure (Measure.map q ν) := ν.isFiniteMeasure_map q
  -- (3) Fourier coeff of the pushforward = the interval Fourier integral
  have hpf : ∀ (μ : Measure ℝ) [IsFiniteMeasure μ], μ (Set.Ioc 0 T)ᶜ = 0 → ∀ n : ℤ,
      ∫ c, fourier n c ∂(Measure.map q μ) = ∫ θ in Set.Ioc 0 T, exp (I * n * θ) ∂μ := by
    intro μ _ hμ n
    rw [integral_map hq.aemeasurable (fourier n).continuous.aestronglyMeasurable]
    simp_rw [hchar n]
    exact integral_eq_setIntegral hμ fun x => cexp (I * ↑n * ↑x)
  have hpush_fourier : ∀ n : ℤ,
      ∫ c, fourier n c ∂(Measure.map q μ)
        = ∫ c, fourier n c ∂(Measure.map q ν) := by
    intro n; rw [hpf μ hcF n, hpf ν hcG n]; exact h n
  -- (4) equal Fourier coeffs ⟹ equal pushforwards on AddCircle T
  have hpush : Measure.map q μ = Measure.map q ν := by
    set νF := Measure.map q μ with hνF
    set νG := Measure.map q ν with hνG
    -- integration functionals are continuous (Lipschitz: ‖∫g‖ ≤ mass·‖g‖) and ℂ-linear,
    -- agree on range fourier, hence on span, hence on closure = ⊤  (span_fourier_closure_eq_top)
    have hCeq : ∀ g : C(AddCircle T, ℂ), ∫ c, g c ∂νF = ∫ c, g c ∂νG := by
      have hdense : Dense
          (Submodule.span ℂ (Set.range (fourier (T := T))) : Set C(AddCircle T, ℂ)) :=
        Submodule.dense_iff_topologicalClosure_eq_top.mpr span_fourier_closure_eq_top
      have hcont : Continuous (fun g : C(AddCircle T, ℂ) => ∫ c, g c ∂νF - ∫ c, g c ∂νG) := by
        have key : ∀ (ν : Measure (AddCircle T)) [IsFiniteMeasure ν],
            Continuous (fun g : C(AddCircle T, ℂ) => ∫ c, g c ∂ν) := by
          intro ν _
          refine LipschitzWith.continuous (K := (ν.real Set.univ).toNNReal)
            (LipschitzWith.of_dist_le_mul fun g g' => ?_)
          erw [dist_eq_norm,
              ← integral_sub ((BoundedContinuousFunction.mkOfCompact g).integrable ν)
                             ((BoundedContinuousFunction.mkOfCompact g').integrable ν)]
          calc ‖∫ c, (g c - g' c) ∂ν‖
              ≤ ∫ c, ‖g c - g' c‖ ∂ν := norm_integral_le_integral_norm _
            _ ≤ ∫ _ : AddCircle T, dist g g' ∂ν := by
                  refine integral_mono_of_nonneg (ae_of_all _ fun c => norm_nonneg _)
                    (integrable_const _) (ae_of_all _ fun c => ?_)
                  simp [dist_eq_norm]
                  rw [← ContinuousMap.sub_apply]
                  exact (g - g').norm_coe_le_norm c
            _ = ((ν.real Set.univ).toNNReal : ℝ) * dist g g' := by
                  rw [integral_const, smul_eq_mul, Real.coe_toNNReal _ measureReal_nonneg]
        exact (key νF).sub (key νG)
      -- continuous functions on the compact circle are integrable wrt the finite pushforwards
      have hInt : ∀ (g : C(AddCircle T, ℂ)) (ν : Measure (AddCircle T)) [IsFiniteMeasure ν],
          Integrable (fun c => g c) ν :=
        fun g ν _ => (BoundedContinuousFunction.mkOfCompact g).integrable ν
      have hzero : Set.EqOn (fun g : C(AddCircle T, ℂ) => ∫ c, g c ∂νF - ∫ c, g c ∂νG)
          (fun _ => 0) (Submodule.span ℂ (Set.range (fourier (T := T)))) := by
        intro g hg
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hg
        · rintro _ ⟨n, rfl⟩
          exact sub_eq_zero.mpr (hpush_fourier n)
        · simp
        · intro x y _ _ hx hy
          simp only [ContinuousMap.add_apply] at hx hy ⊢
          rw [integral_add (hInt x νF) (hInt y νF), integral_add (hInt x νG) (hInt y νG)]
          linear_combination hx + hy
        · intro a x _ hx
          simp only [ContinuousMap.smul_apply] at hx ⊢
          rw [integral_smul, integral_smul, ← smul_sub, hx, smul_zero]
      have : (fun g : C(AddCircle T, ℂ) => ∫ c, g c ∂νF - ∫ c, g c ∂νG) = (fun _ => 0) :=
        Continuous.ext_on hdense hcont continuous_const hzero
      intro g; have := congrFun this g; simpa [sub_eq_zero] using this
    -- real-valued ext lemma for finite Borel measures on AddCircle T
    apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    have hg := hCeq ((⟨Complex.ofReal, Complex.continuous_ofReal⟩ : C(ℝ, ℂ)).comp f.toContinuousMap)
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk,
               BoundedContinuousFunction.coe_toContinuousMap] at hg
    rw [integral_complex_ofReal, integral_complex_ofReal] at hg
    exact Complex.ofReal_inj.mp hg
  -- (5) lift back through ι∘q = id on (0,T]  (equivIoc_coe_eq), a.e. since concentrated there
  have hae : ∀ μ : Measure ℝ, μ (Set.Ioc 0 T)ᶜ = 0 →
      (fun x => ι (q x)) =ᵐ[μ] id := by
    intro μ hμ
    have hsub : {x : ℝ | ι (q x) ≠ id x} ⊆ (Set.Ioc 0 T)ᶜ := by
      intro x hx; by_contra hmem
      simp only [Set.mem_compl_iff, not_not] at hmem
      have hx0T : x ∈ Set.Ioc (0:ℝ) (0 + T) := by rwa [zero_add]
      apply hx
      simp only [hι_def, hq_def, id, AddCircle.equivIoc_coe_eq hx0T]
    exact measure_mono_null hsub hμ |> (ae_iff.mpr)
  have hback : ∀ μ : Measure ℝ, μ (Set.Ioc 0 T)ᶜ = 0 →
      Measure.map ι (Measure.map q μ) = μ := by
    intro μ hμ
    rw [Measure.map_map hι hq]
    erw [Measure.map_congr (hae μ hμ), Measure.map_id]
  calc μ = Measure.map ι (Measure.map q μ) := (hback _ hcF).symm
    _ = Measure.map ι (Measure.map q ν) := by rw [hpush]
    _ = ν := hback _ hcG

omit [InnerProductSpace ℂ H] in
/-- **Measure-level parallelogram**, fully self-contained: each former placeholder
is now an explicit hypothesis. Apply it with your actual spectral-measure lemmas. -/
lemma spectralMeasure_parallelogram
    (μ : H → Measure ℝ)
    (hfin  : ∀ z, IsFiniteMeasure (μ z))
    (hsupp : ∀ z, μ z (Set.Icc 0 (2 * Real.pi))ᶜ = 0)
    (hatom : ∀ z, μ z {(0 : ℝ)} = 0)
    (mom : H → ℤ → ℂ)
    (hmom : ∀ z (n : ℤ),
        ∫ θ in Set.Ioc 0 (2 * Real.pi), Complex.exp (I * n * θ) ∂(μ z) = mom z n)
    (hmom_par : ∀ (n : ℤ) (a b : H),
        mom (a + b) n + mom (a - b) n = 2 * mom a n + 2 * mom b n)
    (huniq : ∀ ν₁ ν₂ : Measure ℝ, IsFiniteMeasure ν₁ → IsFiniteMeasure ν₂ →
        ν₁ (Set.Icc 0 (2 * Real.pi))ᶜ = 0 → ν₂ (Set.Icc 0 (2 * Real.pi))ᶜ = 0 →
        ν₁ {(0 : ℝ)} = 0 → ν₂ {(0 : ℝ)} = 0 →
        (∀ n : ℤ, ∫ θ in Set.Ioc 0 (2 * Real.pi), Complex.exp (I * n * θ) ∂ν₁
                = ∫ θ in Set.Ioc 0 (2 * Real.pi), Complex.exp (I * n * θ) ∂ν₂) →
        ν₁ = ν₂)
    (ψ φ : H) :
    μ (ψ + φ) + μ (ψ - φ) = 2 • μ ψ + 2 • μ φ := by
  haveI := hfin (ψ + φ); haveI := hfin (ψ - φ); haveI := hfin ψ; haveI := hfin φ
  haveI : IsFiniteMeasure (2 • μ ψ) := by rw [two_nsmul]; infer_instance
  haveI : IsFiniteMeasure (2 • μ φ) := by rw [two_nsmul]; infer_instance
  refine huniq _ _ inferInstance inferInstance ?_ ?_ ?_ ?_ ?_
  · simp only [Measure.add_apply, hsupp, add_zero]
  · simp only [two_nsmul, Measure.add_apply, hsupp, add_zero]
  · simp only [Measure.add_apply, hatom, add_zero]
  · simp only [two_nsmul, Measure.add_apply, hatom, add_zero]
  · intro n
    have hint : ∀ z : H, Integrable (fun θ : ℝ => Complex.exp (I * n * θ))
        ((μ z).restrict (Set.Ioc 0 (2 * Real.pi))) := by
      intro z; haveI := hfin z
      refine (integrable_const (1 : ℝ)).mono'
        (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
        (ae_of_all _ fun θ => ?_)
      rw [Complex.norm_exp]; simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [Measure.restrict_add, integral_add_measure (hint _) (hint _),
        hmom (ψ + φ) n, hmom (ψ - φ) n,
        two_nsmul, two_nsmul,
        Measure.restrict_add, Measure.restrict_add, Measure.restrict_add,   -- three, not two
        integral_add_measure ((hint ψ).add_measure (hint ψ))
                             ((hint φ).add_measure (hint φ)),               -- outer: sums
        integral_add_measure (hint ψ) (hint ψ),                            -- ψ-branch
        integral_add_measure (hint φ) (hint φ),                            -- φ-branch
        hmom ψ n, hmom φ n]
    linear_combination hmom_par n ψ φ

end Spectra.ProjValMeasure
