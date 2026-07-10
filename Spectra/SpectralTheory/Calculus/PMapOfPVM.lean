/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.ProjValMeasure.Basic
import Spectra.SpectralTheory.Measure.Convergence
import Spectra.OneParameterUnitaryGroup.PVM
import Mathlib.MeasureTheory.Function.L1Space.Integrable
/-!
# Unbounded functional calculus of a projection-valued measure (R2)

Given a one-parameter unitary group `U_grp` with spectral PVM `U_grp.toPVM` and a measurable symbol
`f : ℝ → ℂ`, the **unbounded functional calculus** `∫ f dP = pmapOfPVM U_grp f` is the (generally
unbounded) operator with natural domain

  `D = { ξ : H | ∫ |f|² d(P.diag ξ) < ∞ }`,   `P.diag = borelMeasure U_grp`,

built as the strong `L²`-limit of the bounded calculus on the truncations `truncSym f n`. This is
the one piece of infrastructure missing for the Tomita–Takesaki square root `Δ^{½}` (R2): with
`U_grp` the unitary group of a self-adjoint `Δ` and `f := (Real.sqrt ·)`,
`pmapOfPVM U_grp f = Δ^{½}`.

This file builds, in order:

* the **natural domain** `pmapDomain P f` as a genuine `Submodule ℂ H`, resting on the diagonal
  measure facts `diag_smul` (scaling `P.diag (c•ξ) = ‖c‖²•P.diag ξ`) and `diag_add_le`
  (domination `P.diag (ξ+η) ≤ 2•(P.diag ξ + P.diag η)`), both from `norm_sq_proj_apply`;
* the **truncation symbols** `truncSym f n = f · 1_{‖f‖≤n}` and their `L²` estimates;
* the **operator** `pmapOfPVM U_grp f hf : H →ₗ.[ℂ] H` itself: `pmapTrunc_cauchySeq` shows the
  truncation sequence `Φ(truncSym f n) ξ` is Cauchy on the domain (its increments controlled by the
  tail `∫ ‖f − truncSym f N‖² dμ_ξ → 0`), so it converges by completeness; the limit is `ℂ`-linear
  in `ξ`, and the `L²` isometry `norm_sq_pmapOfPVM_apply` reads `‖(∫ f dP) ξ‖² = ∫ ‖f‖² dμ_ξ`.

## Roadmap (the rest of `pmapOfPVM`, planned)

1. domain `pmapDomain P f`, truncation symbols, and the Cauchy-limit operator — **this file**;
2. upgrade the pairing `⟪η, pmapOfPVM U_grp f ξ⟫ = limₙ spectralForm η ξ (truncSym f n)`
   (`inner_pmapOfPVM`) to the off-diagonal integral `"∫ f dμ_{η,ξ}"` (unbounded `spectralForm`);
3. self-adjointness (the natural domain is maximal) for real `f`, positivity, and the product law
   `(∫f)(∫g) = ∫ fg`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace Spectra.ProjValMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (P : ProjValMeasure H)

/-! ## Scaling and domination of the diagonal measures -/

/-- The diagonal measure vanishes at `0`. -/
@[simp] lemma diag_zero : P.diag 0 = 0 := by
  refine Measure.ext fun B hB => ?_
  have h : ((P.diag 0) B).toReal = 0 := by
    rw [← norm_sq_proj_apply P B hB 0, map_zero, norm_zero]; ring
  have : (P.diag 0) B = 0 :=
    ((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right (measure_ne_top _ _)
  simpa using this

/-- **Scaling.** `P.diag (c • ξ) = ‖c‖² • P.diag ξ` as measures. -/
lemma diag_smul (c : ℂ) (ξ : H) :
    P.diag (c • ξ) = (‖c‖₊ ^ 2 : ℝ≥0∞) • P.diag ξ := by
  refine Measure.ext fun B hB => ?_
  rw [Measure.smul_apply, smul_eq_mul]
  refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _))).mp ?_
  rw [ENNReal.toReal_mul, ← norm_sq_proj_apply P B hB (c • ξ),
    ← norm_sq_proj_apply P B hB ξ, map_smul, norm_smul, mul_pow]
  congr 1

/-- **Domination.** `P.diag (ξ + η) ≤ 2 • (P.diag ξ + P.diag η)`, from `‖a+b‖² ≤ 2(‖a‖²+‖b‖²)`. -/
lemma diag_add_le (ξ η : H) :
    P.diag (ξ + η) ≤ (2 : ℝ≥0∞) • (P.diag ξ + P.diag η) := by
  refine Measure.le_iff.mpr fun B hB => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.add_apply]
  have hfin : ((P.diag ξ) B + (P.diag η) B) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩
  refine (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.mul_ne_top (by simp) hfin)).mp ?_
  rw [← norm_sq_proj_apply P B hB (ξ + η), map_add, ENNReal.toReal_mul,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ← norm_sq_proj_apply P B hB ξ, ← norm_sq_proj_apply P B hB η]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [h2]
  have hsq : ‖P.proj B hB ξ + P.proj B hB η‖ ^ 2
      ≤ (‖P.proj B hB ξ‖ + ‖P.proj B hB η‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
  nlinarith [hsq, sq_nonneg (‖P.proj B hB ξ‖ - ‖P.proj B hB η‖)]

/-! ## The natural L² domain -/

/-- The **natural domain** `{ ξ | ∫ ‖f‖² d(P.diag ξ) < ∞ }` of the functional calculus `∫ f dP`,
as a `Submodule ℂ H`. -/
noncomputable def pmapDomain (f : ℝ → ℂ) : Submodule ℂ H where
  carrier := {ξ : H | Integrable (fun s => ‖f s‖ ^ 2) (P.diag ξ)}
  zero_mem' := by simp only [Set.mem_setOf_eq, diag_zero]; exact integrable_zero_measure
  add_mem' := by
    intro ξ η hξ hη
    simp only [Set.mem_setOf_eq] at hξ hη ⊢
    have hsum : Integrable (fun s => ‖f s‖ ^ 2) ((2 : ℝ≥0∞) • (P.diag ξ + P.diag η)) := by
      rw [integrable_smul_measure (by simp) (by simp)]
      exact hξ.add_measure hη
    exact hsum.mono_measure (P.diag_add_le ξ η)
  smul_mem' := by
    intro c ξ hξ
    simp only [Set.mem_setOf_eq] at hξ ⊢
    rcases eq_or_ne c 0 with rfl | hc
    · simp [diag_zero]
    · rw [P.diag_smul c ξ, integrable_smul_measure (by simpa using hc) (by simp)]
      exact hξ

@[simp] lemma mem_pmapDomain {f : ℝ → ℂ} {ξ : H} :
    ξ ∈ pmapDomain P f ↔ Integrable (fun s => ‖f s‖ ^ 2) (P.diag ξ) := Iff.rfl

end Spectra.ProjValMeasure

/-! ## Truncation symbols

The operator `∫ f dP` for unbounded `f` is built as the L²-limit of the *bounded* calculus applied
to truncations `f · 1_{‖f‖ ≤ n}`. These symbol-level lemmas are the inputs to that limit; they are
independent of any operator and live at the level of the symbol `f : ℝ → ℂ`. -/

namespace Spectra

/-- The truncation `truncSym f n = f · 1_{‖f‖ ≤ n}` — a bounded symbol agreeing with `f` where
`‖f‖ ≤ n` and vanishing elsewhere. -/
noncomputable def truncSym (f : ℝ → ℂ) (n : ℕ) : ℝ → ℂ :=
  fun s => if ‖f s‖ ≤ (n : ℝ) then f s else 0

@[simp] lemma truncSym_apply (f : ℝ → ℂ) (n : ℕ) (s : ℝ) :
    truncSym f n s = if ‖f s‖ ≤ (n : ℝ) then f s else 0 := rfl

/-- `truncSym f n` is bounded (by `n`). -/
lemma truncSym_bdd (f : ℝ → ℂ) (n : ℕ) : ∃ C, ∀ s, ‖truncSym f n s‖ ≤ C :=
  ⟨n, fun s => by
    rw [truncSym_apply]; split
    · assumption
    · simp⟩

/-- `‖truncSym f n s‖ ≤ ‖f s‖` pointwise. -/
lemma norm_truncSym_le (f : ℝ → ℂ) (n : ℕ) (s : ℝ) : ‖truncSym f n s‖ ≤ ‖f s‖ := by
  rw [truncSym_apply]; split
  · exact le_rfl
  · simp

/-- `truncSym f n` is measurable when `f` is. -/
lemma measurable_truncSym {f : ℝ → ℂ} (hf : Measurable f) (n : ℕ) :
    Measurable (truncSym f n) := by
  refine Measurable.ite ?_ hf measurable_const
  exact measurableSet_le (hf.norm) measurable_const

/-- Pointwise, `truncSym f n s → f s` as `n → ∞`
(for `n ≥ ‖f s‖` the truncation is exactly `f s`). -/
lemma tendsto_truncSym (f : ℝ → ℂ) (s : ℝ) :
    Filter.Tendsto (fun n => truncSym f n s) Filter.atTop (nhds (f s)) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop ⌈‖f s‖⌉₊] with n hn
  rw [truncSym_apply, if_pos]
  exact (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)

/-- For `n, m ≥ N`, the increment between two truncations is dominated pointwise by the `N`-th
tail `‖f s − truncSym f N s‖`.  (If `‖f s‖ ≤ N`, all three truncations equal `f s` and both sides
vanish; if `‖f s‖ > N`, the `N`-th tail is exactly `‖f s‖`, which dominates the increment since
each truncation is `f s` or `0`.)  This is the pointwise seed of the `L²` Cauchy estimate. -/
lemma norm_truncSym_sub_le (f : ℝ → ℂ) {n m N : ℕ} (hn : N ≤ n) (hm : N ≤ m) (s : ℝ) :
    ‖truncSym f n s - truncSym f m s‖ ≤ ‖f s - truncSym f N s‖ := by
  by_cases hle : ‖f s‖ ≤ (N : ℝ)
  · have key : ∀ k : ℕ, N ≤ k → truncSym f k s = f s := fun k hk => by
      rw [truncSym_apply, if_pos (hle.trans (by exact_mod_cast hk))]
    simp only [key n hn, key m hm, key N le_rfl, sub_self, norm_zero, le_refl]
  · have hN0 : truncSym f N s = 0 := by rw [truncSym_apply, if_neg hle]
    rw [hN0, sub_zero, truncSym_apply, truncSym_apply]
    split_ifs <;>
      simp only [sub_self, sub_zero, zero_sub, norm_zero, norm_neg] <;>
      first
        | exact le_refl _
        | exact norm_nonneg _

/-- The `N`-th `L²` tail integrand is dominated by `4‖f‖²` (triangle inequality together with
`‖truncSym f N‖ ≤ ‖f‖`) — the integrable majorant for the dominated-convergence argument. -/
lemma norm_sub_truncSym_sq_le (f : ℝ → ℂ) (N : ℕ) (s : ℝ) :
    ‖f s - truncSym f N s‖ ^ 2 ≤ 4 * ‖f s‖ ^ 2 := by
  have h2 : ‖f s - truncSym f N s‖ ≤ 2 * ‖f s‖ := by
    have ha := norm_sub_le (f s) (truncSym f N s)
    have hb := norm_truncSym_le f N s
    linarith
  nlinarith [norm_nonneg (f s - truncSym f N s), norm_nonneg (f s), h2]

end Spectra

/-! ## The Cauchy-limit (unbounded) functional calculus `∫ f dP`

For an unbounded measurable symbol `f : ℝ → ℂ` and a one-parameter unitary group `U_grp`, the
operator `∫ f dP` over the spectral PVM `U_grp.toPVM` is the strong `L²`-limit of the bounded
calculus on the truncations `truncSym f n`.  On the natural domain `pmapDomain U_grp.toPVM f`
(`= {ξ | ∫ ‖f‖² dμ_ξ < ∞}`, since `U_grp.toPVM.diag = borelMeasure U_grp` definitionally) the
sequence `Φ(truncSym f n) ξ` is Cauchy, its increments controlled by the tail
`∫ ‖f − truncSym f N‖² dμ_ξ → 0`; completeness gives the limit, which is `ℂ`-linear in `ξ`.

This is the one piece of infrastructure missing for the Tomita–Takesaki square root `Δ^{½}`:
with `U_grp` the unitary group of a self-adjoint `Δ` and `f := (Real.sqrt ·)`,
`pmapOfPVM U_grp f = Δ^{½}`. -/

namespace Spectra.QuantumMechanics.SpectralTheory

open Spectra Complex MeasureTheory Filter Topology
open Spectra.Borel Spectra.OneParameterUnitaryGroup
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- The bounded calculus applied to the `n`-th truncation of the symbol `f`. -/
noncomputable def pmapTrunc (f : ℝ → ℂ) (hf : Measurable f) (n : ℕ) : H →L[ℂ] H :=
  spectralCalculus U_grp (truncSym f n) (measurable_truncSym hf n) (truncSym_bdd f n)

@[simp] lemma pmapTrunc_apply (f : ℝ → ℂ) (hf : Measurable f) (n : ℕ) (ξ : H) :
    pmapTrunc U_grp f hf n ξ
      = spectralCalculus U_grp (truncSym f n) (measurable_truncSym hf n) (truncSym_bdd f n) ξ :=
  rfl

/-- **The Cauchy estimate.**  On the natural `L²` domain the truncation sequence
`Φ(truncSym f n) ξ` is Cauchy: `‖Φ(truncSym f n)ξ − Φ(truncSym f m)ξ‖ =
(∫ ‖truncSym f n − truncSym f m‖² dμ_ξ)^{1/2} ≤ (∫ ‖f − truncSym f N‖² dμ_ξ)^{1/2}` for
`n, m ≥ N`, and the right side tends to `0` by dominated convergence. -/
theorem pmapTrunc_cauchySeq (f : ℝ → ℂ) (hf : Measurable f) {ξ : H}
    (hξ : Integrable (fun s => ‖f s‖ ^ 2) (borelMeasure U_grp ξ)) :
    CauchySeq (fun n => pmapTrunc U_grp f hf n ξ) := by
  haveI : IsFiniteMeasure (borelMeasure U_grp ξ) := borelMeasure_isFiniteMeasure U_grp ξ
  -- Step 1: the increment as an `L²` norm.
  have hnorm : ∀ n m : ℕ,
      ‖pmapTrunc U_grp f hf n ξ - pmapTrunc U_grp f hf m ξ‖
        = Real.sqrt (∫ s, ‖truncSym f n s - truncSym f m s‖ ^ 2 ∂(borelMeasure U_grp ξ)) := by
    intro n m
    have hsub : pmapTrunc U_grp f hf n ξ - pmapTrunc U_grp f hf m ξ
        = spectralCalculus U_grp (fun s => truncSym f n s - truncSym f m s)
            ((measurable_truncSym hf n).sub (measurable_truncSym hf m))
            (bounded_sub (truncSym_bdd f n) (truncSym_bdd f m)) ξ := by
      rw [pmapTrunc_apply, pmapTrunc_apply, ← ContinuousLinearMap.sub_apply,
        ← spectralCalculus_sub U_grp (truncSym f n) (truncSym f m)
          (measurable_truncSym hf n) (truncSym_bdd f n)
          (measurable_truncSym hf m) (truncSym_bdd f m)
          ((measurable_truncSym hf n).sub (measurable_truncSym hf m))
          (bounded_sub (truncSym_bdd f n) (truncSym_bdd f m))]
    rw [hsub, ← Real.sqrt_sq (norm_nonneg _), norm_sq_spectralCalculus_apply]
  -- Step 2: integrability of every tail integrand.
  have htail_int : ∀ N : ℕ, Integrable (fun s => ‖f s - truncSym f N s‖ ^ 2)
      (borelMeasure U_grp ξ) := by
    intro N
    refine Integrable.mono' (hξ.const_mul 4)
      ((hf.sub (measurable_truncSym hf N)).norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact norm_sub_truncSym_sq_le f N s
  -- Step 3: monotone domination of the increment integral by the `N`-th tail integral.
  have hmono : ∀ n m N : ℕ, N ≤ n → N ≤ m →
      (∫ s, ‖truncSym f n s - truncSym f m s‖ ^ 2 ∂(borelMeasure U_grp ξ))
        ≤ ∫ s, ‖f s - truncSym f N s‖ ^ 2 ∂(borelMeasure U_grp ξ) := by
    intro n m N hn hm
    refine integral_mono_of_nonneg (Eventually.of_forall fun s => sq_nonneg _) (htail_int N)
      (Eventually.of_forall fun s => ?_)
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_truncSym_sub_le f hn hm s) 2
  -- Step 4: the tail integral tends to `0` (dominated convergence).
  have htail_tendsto : Tendsto
      (fun N => ∫ s, ‖f s - truncSym f N s‖ ^ 2 ∂(borelMeasure U_grp ξ)) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence
      (μ := borelMeasure U_grp ξ)
      (F := fun N s => ‖f s - truncSym f N s‖ ^ 2) (f := fun _ => (0 : ℝ))
      (bound := fun s => 4 * ‖f s‖ ^ 2)
      (fun N => ((hf.sub (measurable_truncSym hf N)).norm.pow_const 2).aestronglyMeasurable)
      (hξ.const_mul 4)
      (fun N => Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact norm_sub_truncSym_sq_le f N s)
      (Eventually.of_forall fun s => by
        have h0 : Tendsto (fun N => f s - truncSym f N s) atTop (𝓝 0) := by
          have hc : Tendsto (fun _ : ℕ => f s) atTop (𝓝 (f s)) := tendsto_const_nhds
          have h := hc.sub (tendsto_truncSym f s)
          rwa [sub_self] at h
        simpa using h0.norm.pow 2)
    simpa using h
  -- Assemble via the metric Cauchy criterion.
  refine cauchySeq_of_le_tendsto_0
    (fun N => Real.sqrt (∫ s, ‖f s - truncSym f N s‖ ^ 2 ∂(borelMeasure U_grp ξ)))
    (fun n m N hn hm => ?_) (by simpa using htail_tendsto.sqrt)
  rw [dist_eq_norm, hnorm n m]
  exact Real.sqrt_le_sqrt (hmono n m N hn hm)

/-- **The unbounded functional calculus** `∫ f dP : H →ₗ.[ℂ] H` of the spectral PVM `U_grp.toPVM`,
defined on the natural `L²` domain `pmapDomain U_grp.toPVM f` as the strong limit of the truncated
bounded calculus.  `ℂ`-linearity in `ξ` is built into the `LinearPMap` structure. -/
noncomputable def pmapOfPVM (f : ℝ → ℂ) (hf : Measurable f) : H →ₗ.[ℂ] H where
  domain := ProjValMeasure.pmapDomain U_grp.toPVM f
  toFun :=
    { toFun := fun ξ => limUnder atTop (fun n => pmapTrunc U_grp f hf n (ξ : H))
      map_add' := fun ξ η => by
        have hx := (pmapTrunc_cauchySeq U_grp f hf
          ξ.2).tendsto_limUnder
        have hy := (pmapTrunc_cauchySeq U_grp f hf
          η.2).tendsto_limUnder
        refine Filter.Tendsto.limUnder_eq ((hx.add hy).congr fun n => ?_)
        calc pmapTrunc U_grp f hf n (ξ : H) + pmapTrunc U_grp f hf n (η : H)
            = pmapTrunc U_grp f hf n ((ξ : H) + (η : H)) := (map_add _ _ _).symm
          _ = pmapTrunc U_grp f hf n ((↑(ξ + η) : H)) := by rw [Submodule.coe_add]
      map_smul' := fun c ξ => by
        simp only [RingHom.id_apply]
        have hx := (pmapTrunc_cauchySeq U_grp f hf
          ξ.2).tendsto_limUnder
        refine Filter.Tendsto.limUnder_eq ((hx.const_smul c).congr fun n => ?_)
        calc c • pmapTrunc U_grp f hf n (ξ : H)
            = pmapTrunc U_grp f hf n (c • (ξ : H)) := (map_smul _ _ _).symm
          _ = pmapTrunc U_grp f hf n ((↑(c • ξ) : H)) := by rw [Submodule.coe_smul] }

/-- The defining convergence: on the natural domain, the truncated calculus converges strongly to
`pmapOfPVM U_grp f hf ξ`. -/
theorem pmapOfPVM_apply_tendsto (f : ℝ → ℂ) (hf : Measurable f) {ξ : H}
    (hξ : Integrable (fun s => ‖f s‖ ^ 2) (borelMeasure U_grp ξ)) :
    Tendsto (fun n => pmapTrunc U_grp f hf n ξ) atTop
      (𝓝 (pmapOfPVM U_grp f hf ⟨ξ, (ProjValMeasure.mem_pmapDomain U_grp.toPVM).mpr hξ⟩)) := by
  exact (pmapTrunc_cauchySeq U_grp f hf hξ).tendsto_limUnder

/-- **The `L²` isometry of the calculus**: `‖(∫ f dP) ξ‖² = ∫ ‖f‖² dμ_ξ`.  The truncated identity
`‖Φ(truncSym f n)ξ‖² = ∫ ‖truncSym f n‖² dμ_ξ` passes to the limit — the left side by strong
convergence (`pmapOfPVM_apply_tendsto`), the right by dominated convergence
(`‖truncSym f n‖² ↑ ‖f‖²`, dominated by the integrable `‖f‖²`). -/
theorem norm_sq_pmapOfPVM_apply (f : ℝ → ℂ) (hf : Measurable f) {ξ : H}
    (hξ : Integrable (fun s => ‖f s‖ ^ 2) (borelMeasure U_grp ξ)) :
    ‖pmapOfPVM U_grp f hf ⟨ξ, (ProjValMeasure.mem_pmapDomain U_grp.toPVM).mpr hξ⟩‖ ^ 2
      = ∫ s, ‖f s‖ ^ 2 ∂(borelMeasure U_grp ξ) := by
  haveI : IsFiniteMeasure (borelMeasure U_grp ξ) := borelMeasure_isFiniteMeasure U_grp ξ
  set v := pmapOfPVM U_grp f hf ⟨ξ, (ProjValMeasure.mem_pmapDomain U_grp.toPVM).mpr hξ⟩ with hv
  have h1 : Tendsto (fun n => ‖pmapTrunc U_grp f hf n ξ‖ ^ 2) atTop (𝓝 (‖v‖ ^ 2)) := by
    have htend := pmapOfPVM_apply_tendsto U_grp f hf hξ
    rw [← hv] at htend
    exact htend.norm.pow 2
  have h2 : Tendsto (fun n => ‖pmapTrunc U_grp f hf n ξ‖ ^ 2) atTop
      (𝓝 (∫ s, ‖f s‖ ^ 2 ∂(borelMeasure U_grp ξ))) := by
    have heq : ∀ n, ‖pmapTrunc U_grp f hf n ξ‖ ^ 2
        = ∫ s, ‖truncSym f n s‖ ^ 2 ∂(borelMeasure U_grp ξ) := fun n => by
      rw [pmapTrunc_apply, norm_sq_spectralCalculus_apply]
    simp_rw [heq]
    refine tendsto_integral_of_dominated_convergence (fun s => ‖f s‖ ^ 2)
      (fun n => ((measurable_truncSym hf n).norm.pow_const 2).aestronglyMeasurable)
      hξ (fun n => Eventually.of_forall fun s => ?_) (Eventually.of_forall fun s => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_truncSym_le f n s) 2
    · exact (tendsto_truncSym f s).norm.pow 2
  exact tendsto_nhds_unique h1 h2

/-- **The defining pairing of the calculus** (limit form): `⟪η, (∫ f dP) ξ⟫ =
limₙ spectralForm η ξ (truncSym f n)` — the `L¹` identification `= "∫ f dμ_{η,ξ}"` is the next
step.  Together with the built-in `ℂ`-linearity of `pmapOfPVM` in `ξ` this is the polarized
characterization of the operator. -/
theorem inner_pmapOfPVM (f : ℝ → ℂ) (hf : Measurable f) (η : H) {ξ : H}
    (hξ : Integrable (fun s => ‖f s‖ ^ 2) (borelMeasure U_grp ξ)) :
    ⟪η, pmapOfPVM U_grp f hf ⟨ξ, (ProjValMeasure.mem_pmapDomain U_grp.toPVM).mpr hξ⟩⟫_ℂ
      = limUnder atTop (fun n => spectralForm U_grp η ξ (truncSym f n)) := by
  set v := pmapOfPVM U_grp f hf ⟨ξ, (ProjValMeasure.mem_pmapDomain U_grp.toPVM).mpr hξ⟩ with hv
  refine (Filter.Tendsto.limUnder_eq ?_).symm
  have htend := pmapOfPVM_apply_tendsto U_grp f hf hξ
  rw [← hv] at htend
  have hc : Continuous (fun y : H => ⟪η, y⟫_ℂ) := continuous_const.inner continuous_id
  refine ((hc.tendsto _).comp htend).congr fun n => ?_
  rw [Function.comp_apply, pmapTrunc_apply, inner_spectralCalculus]

/-- A symbol in the natural domain is itself integrable: `L² ⊆ L¹` on the finite measure `μ_ξ`,
via `‖f‖ ≤ 1 + ‖f‖²`. -/
theorem integrable_of_mem_pmapDomain (f : ℝ → ℂ) (hf : Measurable f) {ξ : H}
    (hξ : Integrable (fun s => ‖f s‖ ^ 2) (borelMeasure U_grp ξ)) :
    Integrable f (borelMeasure U_grp ξ) := by
  haveI : IsFiniteMeasure (borelMeasure U_grp ξ) := borelMeasure_isFiniteMeasure U_grp ξ
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add hξ) hf.aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  simp only [Pi.add_apply]
  nlinarith [norm_nonneg (f s), sq_nonneg (‖f s‖ - 1)]

/-- **The diagonal (quadratic-form) pairing**: `⟪ξ, (∫ f dP) ξ⟫ = ∫ f dμ_ξ`.  Specializing
`inner_pmapOfPVM` at `η = ξ` turns `spectralForm ξ ξ (truncSym f n)` into `∫ truncSym f n dμ_ξ`
(`spectralForm_self`); the limit is `∫ f dμ_ξ` by dominated convergence (`truncSym f n → f`,
dominated by `‖f‖ ∈ L¹` since `f ∈ L²` and `μ_ξ` is finite).  This is the quadratic form of the
calculus, the input to positivity and to the moment identities. -/
theorem inner_self_pmapOfPVM (f : ℝ → ℂ) (hf : Measurable f) {ξ : H}
    (hξ : Integrable (fun s => ‖f s‖ ^ 2) (borelMeasure U_grp ξ)) :
    ⟪ξ, pmapOfPVM U_grp f hf ⟨ξ, (ProjValMeasure.mem_pmapDomain U_grp.toPVM).mpr hξ⟩⟫_ℂ
      = ∫ s, f s ∂(borelMeasure U_grp ξ) := by
  haveI : IsFiniteMeasure (borelMeasure U_grp ξ) := borelMeasure_isFiniteMeasure U_grp ξ
  have hf_int : Integrable f (borelMeasure U_grp ξ) := integrable_of_mem_pmapDomain U_grp f hf hξ
  rw [inner_pmapOfPVM U_grp f hf ξ hξ]
  have hsf : ∀ n, spectralForm U_grp ξ ξ (truncSym f n)
      = ∫ s, truncSym f n s ∂(borelMeasure U_grp ξ) :=
    fun n => spectralForm_self U_grp ξ (measurable_truncSym hf n) (truncSym_bdd f n)
  simp_rw [hsf]
  refine Filter.Tendsto.limUnder_eq ?_
  refine tendsto_integral_of_dominated_convergence (fun s => ‖f s‖)
    (fun n => (measurable_truncSym hf n).aestronglyMeasurable) hf_int.norm
    (fun n => Eventually.of_forall fun s => norm_truncSym_le f n s)
    (Eventually.of_forall fun s => tendsto_truncSym f s)

/-- **Symmetry for real symbols.**  When `f` is real-valued (`conj ∘ f = f`), the operator
`∫ f dP` is a formal adjoint of itself — i.e. symmetric.  Each truncated calculus `Φ(truncSym f n)`
is self-adjoint (the truncation of a real symbol is real, `spectralCalculus_adjoint`), so
`⟪Φ(truncₙ)ξ, η⟫ = ⟪ξ, Φ(truncₙ)η⟫`; passing to the strong limit on both sides gives the symmetry
of `∫ f dP`.  This is the first half of "real `f` ⟹ self-adjoint". -/
theorem pmapOfPVM_isFormalAdjoint_self (f : ℝ → ℂ) (hf : Measurable f)
    (hreal : ∀ s, (starRingEnd ℂ) (f s) = f s) :
    (pmapOfPVM U_grp f hf).IsFormalAdjoint (pmapOfPVM U_grp f hf) := by
  intro x y
  have hx : Integrable (fun s => ‖f s‖ ^ 2) (borelMeasure U_grp (x : H)) := x.2
  have hy : Integrable (fun s => ‖f s‖ ^ 2) (borelMeasure U_grp (y : H)) := y.2
  -- every truncated calculus is self-adjoint, since the truncation of a real symbol is real
  have hselfadj : ∀ n, ContinuousLinearMap.adjoint (pmapTrunc U_grp f hf n)
      = pmapTrunc U_grp f hf n := by
    intro n
    have hcm : Measurable fun s => (starRingEnd ℂ) (truncSym f n s) :=
      Complex.continuous_conj.measurable.comp (measurable_truncSym hf n)
    have hcb : ∃ C, ∀ s, ‖(starRingEnd ℂ) (truncSym f n s)‖ ≤ C := by
      obtain ⟨C, hC⟩ := truncSym_bdd f n
      exact ⟨C, fun s => by rw [RCLike.norm_conj]; exact hC s⟩
    have hconj : (fun s => (starRingEnd ℂ) (truncSym f n s)) = truncSym f n := by
      funext s
      simp only [truncSym_apply]
      split_ifs
      · exact hreal s
      · simp
    change ContinuousLinearMap.adjoint
        (spectralCalculus U_grp (truncSym f n) (measurable_truncSym hf n) (truncSym_bdd f n))
      = spectralCalculus U_grp (truncSym f n) (measurable_truncSym hf n) (truncSym_bdd f n)
    rw [spectralCalculus_adjoint U_grp (truncSym f n) (measurable_truncSym hf n)
        (truncSym_bdd f n) hcm hcb]
    exact spectralCalculus_congr U_grp hconj hcm hcb (measurable_truncSym hf n) (truncSym_bdd f n)
  -- the truncated identity `⟪Φ(truncₙ)ξ, η⟫ = ⟪ξ, Φ(truncₙ)η⟫`
  have heq : ∀ n, ⟪pmapTrunc U_grp f hf n (x : H), (y : H)⟫_ℂ
      = ⟪(x : H), pmapTrunc U_grp f hf n (y : H)⟫_ℂ := by
    intro n
    have h := ContinuousLinearMap.adjoint_inner_left (pmapTrunc U_grp f hf n) (y : H) (x : H)
    rwa [hselfadj n] at h
  -- pass to the strong limit on both sides
  have h1 : Tendsto (fun n => ⟪pmapTrunc U_grp f hf n (x : H), (y : H)⟫_ℂ) atTop
      (𝓝 ⟪(pmapOfPVM U_grp f hf x : H), (y : H)⟫_ℂ) :=
    ((continuous_id.inner continuous_const).tendsto _).comp
      (pmapOfPVM_apply_tendsto U_grp f hf hx)
  have h2 : Tendsto (fun n => ⟪pmapTrunc U_grp f hf n (x : H), (y : H)⟫_ℂ) atTop
      (𝓝 ⟪(x : H), (pmapOfPVM U_grp f hf y : H)⟫_ℂ) :=
    (((continuous_const.inner continuous_id).tendsto _).comp
      (pmapOfPVM_apply_tendsto U_grp f hf hy)).congr fun n => (heq n).symm
  exact tendsto_nhds_unique h1 h2

/-- **Positivity of the quadratic form**: if the symbol has nonnegative real part everywhere
(`0 ≤ (f s).re`), then `0 ≤ Re ⟪ξ, (∫ f dP) ξ⟫`.  Immediate from the diagonal pairing
`inner_self_pmapOfPVM` and `integral_re`.  For the modular square root `f = √· ≥ 0` this is
`Δ^{½} ≥ 0`. -/
theorem re_inner_self_pmapOfPVM_nonneg (f : ℝ → ℂ) (hf : Measurable f)
    (hnn : ∀ s, 0 ≤ (f s).re) {ξ : H}
    (hξ : Integrable (fun s => ‖f s‖ ^ 2) (borelMeasure U_grp ξ)) :
    0 ≤ (⟪ξ, pmapOfPVM U_grp f hf
        ⟨ξ, (ProjValMeasure.mem_pmapDomain U_grp.toPVM).mpr hξ⟩⟫_ℂ).re := by
  rw [inner_self_pmapOfPVM U_grp f hf hξ, ← RCLike.re_eq_complex_re,
    ← integral_re (integrable_of_mem_pmapDomain U_grp f hf hξ)]
  exact integral_nonneg fun s => hnn s

end Spectra.QuantumMechanics.SpectralTheory
