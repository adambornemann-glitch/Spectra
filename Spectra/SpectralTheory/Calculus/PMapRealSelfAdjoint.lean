/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SpectralTheory.Calculus.MixedProduct
/-!
# Self-adjointness of the unbounded calculus of a real symbol

For a strongly-continuous one-parameter unitary group `U_grp` with generator `A` and a
**real-valued** measurable symbol `f : ℝ → ℂ` (`conj (f s) = f s`), the unbounded
functional-calculus operator `pmapOfPVM U_grp f = ∫ f dP` is **self-adjoint whenever its natural
`L²` domain is dense**.

The point is that everything except density is *unconditional*:

* **Symmetry** is `pmapOfPVM_isFormalAdjoint_self` (the symbol is real).
* **Surjectivity of `A_f ± i`** always holds, for *any* real symbol, via the bounded resolvent
  `R_± := Φ(1/(f·±i))`.  The symbol `1/(f s ± i)` is bounded by `1` because `‖f s ± i‖ ≥ 1`
  (the imaginary part is `±1`, since `f s` is real), and the **mixed bounded/unbounded product law**
  (`pmapOfPVM_spectralCalculus_of_mul_bounded`) gives `R_± h ∈ D(A_f)` and
  `(A_f ± i)(R_± h) = Φ((f±i)/(f±i)) h = Φ(1) h = h`.

So `pmapOfPVM_isSelfAdjoint_of_real` reduces self-adjointness of *any* real-symbol calculus to the
single obligation `Dense (D(A_f))`.  This J-free engine subsumes the bespoke
`modularSqrt_isSelfAdjoint` (symbol `√`) and, in `ModularReciprocal.lean`, delivers `Δ⁻¹` (symbol
`1/s`) and `Δ^{-½}` (symbol `1/√s`) from their respective density lemmas.

## Main statements

* `pmapOfPVM_add_I_surjective` / `pmapOfPVM_sub_I_surjective` — `A_f ± i` surjective
  (unconditional).
* `pmapOfPVM_isSelfAdjoint_of_real` — real symbol + dense domain ⟹ `A_f` self-adjoint.
-/

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal
open Spectra Spectra.Borel Spectra.OneParameterUnitaryGroup

namespace Spectra.QuantumMechanics.SpectralTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Real-number resolvent bounds (pure `ℂ`) -/

/-- If `z` is real (`conj z = z`) then `‖z + i‖ ≥ 1` (the imaginary part is `1`). -/
lemma one_le_norm_add_I_of_conj {z : ℂ} (hz : (starRingEnd ℂ) z = z) : (1 : ℝ) ≤ ‖z + I‖ := by
  have him0 : z.im = 0 := Complex.conj_eq_iff_im.mp hz
  have him : (z + I).im = 1 := by simp [him0]
  calc (1 : ℝ) = |(z + I).im| := by rw [him]; norm_num
    _ ≤ ‖z + I‖ := Complex.abs_im_le_norm _

/-- If `z` is real (`conj z = z`) then `‖z − i‖ ≥ 1` (the imaginary part is `−1`). -/
lemma one_le_norm_sub_I_of_conj {z : ℂ} (hz : (starRingEnd ℂ) z = z) : (1 : ℝ) ≤ ‖z - I‖ := by
  have him0 : z.im = 0 := Complex.conj_eq_iff_im.mp hz
  have him : (z - I).im = -1 := by simp [him0]
  calc (1 : ℝ) = |(z - I).im| := by rw [him]; norm_num
    _ ≤ ‖z - I‖ := Complex.abs_im_le_norm _

/-- If `z` is real then `‖z‖ ≤ ‖z + i‖` (`normSq(z+i) = z.re² + 1 ≥ z.re² = ‖z‖²`). -/
lemma norm_le_norm_add_I_of_conj {z : ℂ} (hz : (starRingEnd ℂ) z = z) : ‖z‖ ≤ ‖z + I‖ := by
  have him0 : z.im = 0 := Complex.conj_eq_iff_im.mp hz
  have h1 : ‖z‖ ^ 2 ≤ ‖z + I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
      him0]
    nlinarith
  nlinarith [norm_nonneg z, norm_nonneg (z + I), h1]

/-- If `z` is real then `‖z‖ ≤ ‖z − i‖`. -/
lemma norm_le_norm_sub_I_of_conj {z : ℂ} (hz : (starRingEnd ℂ) z = z) : ‖z‖ ≤ ‖z - I‖ := by
  have him0 : z.im = 0 := Complex.conj_eq_iff_im.mp hz
  have h1 : ‖z‖ ^ 2 ≤ ‖z - I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im,
      him0]
    nlinarith
  nlinarith [norm_nonneg z, norm_nonneg (z - I), h1]

lemma add_I_ne_zero_of_conj {z : ℂ} (hz : (starRingEnd ℂ) z = z) : z + I ≠ 0 := by
  intro h; have := one_le_norm_add_I_of_conj hz; rw [h, norm_zero] at this; linarith

lemma sub_I_ne_zero_of_conj {z : ℂ} (hz : (starRingEnd ℂ) z = z) : z - I ≠ 0 := by
  intro h; have := one_le_norm_sub_I_of_conj hz; rw [h, norm_zero] at this; linarith

/-! ### Boundedness / measurability of the resolvent symbols `1/(f ± i)`, `f/(f ± i)`

These take the real symbol `f` (with `hf`/`hconj` as needed) by explicit argument. -/

lemma resAddI_meas (f : ℝ → ℂ) (hf : Measurable f) :
    Measurable (fun s => (1 : ℂ) / (f s + I)) := measurable_const.div (hf.add measurable_const)

lemma resSubI_meas (f : ℝ → ℂ) (hf : Measurable f) :
    Measurable (fun s => (1 : ℂ) / (f s - I)) := measurable_const.div (hf.sub measurable_const)

lemma resAddI_bdd (f : ℝ → ℂ) (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s) :
    ∃ C, ∀ s, ‖(1 : ℂ) / (f s + I)‖ ≤ C := by
  refine ⟨1, fun s => ?_⟩
  rw [norm_div, NormOneClass.norm_one,
    div_le_one (by have := one_le_norm_add_I_of_conj (hconj s); linarith)]
  exact one_le_norm_add_I_of_conj (hconj s)

lemma resSubI_bdd (f : ℝ → ℂ) (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s) :
    ∃ C, ∀ s, ‖(1 : ℂ) / (f s - I)‖ ≤ C := by
  refine ⟨1, fun s => ?_⟩
  rw [norm_div, NormOneClass.norm_one,
    div_le_one (by have := one_le_norm_sub_I_of_conj (hconj s); linarith)]
  exact one_le_norm_sub_I_of_conj (hconj s)

lemma fResAddI_meas (f : ℝ → ℂ) (hf : Measurable f) :
    Measurable (fun s => f s * ((1 : ℂ) / (f s + I))) := hf.mul (resAddI_meas f hf)

lemma fResSubI_meas (f : ℝ → ℂ) (hf : Measurable f) :
    Measurable (fun s => f s * ((1 : ℂ) / (f s - I))) := hf.mul (resSubI_meas f hf)

lemma fResAddI_bdd (f : ℝ → ℂ) (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s) :
    ∃ C, ∀ s, ‖f s * ((1 : ℂ) / (f s + I))‖ ≤ C := by
  refine ⟨1, fun s => ?_⟩
  rw [mul_one_div, norm_div, div_le_one (by have := one_le_norm_add_I_of_conj (hconj s); linarith)]
  exact norm_le_norm_add_I_of_conj (hconj s)

lemma fResSubI_bdd (f : ℝ → ℂ) (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s) :
    ∃ C, ∀ s, ‖f s * ((1 : ℂ) / (f s - I))‖ ≤ C := by
  refine ⟨1, fun s => ?_⟩
  rw [mul_one_div, norm_div, div_le_one (by have := one_le_norm_sub_I_of_conj (hconj s); linarith)]
  exact norm_le_norm_sub_I_of_conj (hconj s)

lemma IResAddI_meas (f : ℝ → ℂ) (hf : Measurable f) :
    Measurable (fun s => I * ((1 : ℂ) / (f s + I))) := measurable_const.mul (resAddI_meas f hf)

lemma IResSubI_meas (f : ℝ → ℂ) (hf : Measurable f) :
    Measurable (fun s => I * ((1 : ℂ) / (f s - I))) := measurable_const.mul (resSubI_meas f hf)

lemma IResAddI_bdd (f : ℝ → ℂ) (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s) :
    ∃ C, ∀ s, ‖I * ((1 : ℂ) / (f s + I))‖ ≤ C := by
  obtain ⟨C, hC⟩ := resAddI_bdd f hconj
  exact ⟨‖I‖ * C, fun s => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC s) (norm_nonneg _)⟩

lemma IResSubI_bdd (f : ℝ → ℂ) (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s) :
    ∃ C, ∀ s, ‖I * ((1 : ℂ) / (f s - I))‖ ≤ C := by
  obtain ⟨C, hC⟩ := resSubI_bdd f hconj
  exact ⟨‖I‖ * C, fun s => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC s) (norm_nonneg _)⟩

/-! ### Surjectivity of `A_f ± i` (unconditional for a real symbol) -/

variable (U_grp : OneParameterUnitaryGroup (H := H))
variable (f : ℝ → ℂ) (hf : Measurable f) (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s)
include hconj

/-- **Surjectivity of `A_f + i`.**  The bounded resolvent vector `R h = Φ(1/(f+i)) h` lies in
`D(A_f)` (mixed-law domain membership) and `(A_f + i)(R h) = Φ((f+i)/(f+i)) h = Φ(1) h = h`. -/
theorem pmapOfPVM_add_I_surjective :
    ∀ h : H, ∃ ψ : (pmapOfPVM U_grp f hf).domain,
      pmapOfPVM U_grp f hf ψ + I • (ψ : H) = h := by
  intro h
  have hmem : spectralCalculus U_grp (fun s => (1 : ℂ) / (f s + I)) (resAddI_meas f hf)
        (resAddI_bdd f hconj) h
      ∈ ProjValMeasure.pmapDomain U_grp.toPVM f :=
    mem_pmapDomain_spectralCalculus U_grp f (fun s => (1 : ℂ) / (f s + I)) hf (resAddI_meas f hf)
      (resAddI_bdd f hconj) (fResAddI_bdd f hconj) h
  refine ⟨⟨_, hmem⟩, ?_⟩
  have hval : pmapOfPVM U_grp f hf ⟨_, hmem⟩
      = spectralCalculus U_grp (fun s => f s * ((1 : ℂ) / (f s + I))) (fResAddI_meas f hf)
          (fResAddI_bdd f hconj) h :=
    pmapOfPVM_spectralCalculus_of_mul_bounded U_grp f (fun s => (1 : ℂ) / (f s + I)) hf
      (resAddI_meas f hf) (resAddI_bdd f hconj) (fResAddI_meas f hf) (fResAddI_bdd f hconj) h hmem
  rw [hval]
  have hIR : I • spectralCalculus U_grp (fun s => (1 : ℂ) / (f s + I)) (resAddI_meas f hf)
        (resAddI_bdd f hconj) h
      = spectralCalculus U_grp (fun s => I * ((1 : ℂ) / (f s + I))) (IResAddI_meas f hf)
          (IResAddI_bdd f hconj) h := by
    rw [spectralCalculus_smul U_grp I (fun s => (1 : ℂ) / (f s + I)) (resAddI_meas f hf)
      (resAddI_bdd f hconj) (IResAddI_meas f hf) (IResAddI_bdd f hconj)]
    rfl
  change _ + I • spectralCalculus U_grp (fun s => (1 : ℂ) / (f s + I)) (resAddI_meas f hf)
    (resAddI_bdd f hconj) h = h
  rw [hIR, ← ContinuousLinearMap.add_apply,
    ← spectralCalculus_add U_grp (fun s => f s * ((1 : ℂ) / (f s + I)))
      (fun s => I * ((1 : ℂ) / (f s + I))) (fResAddI_meas f hf) (fResAddI_bdd f hconj)
      (IResAddI_meas f hf) (IResAddI_bdd f hconj)
      ((fResAddI_meas f hf).add (IResAddI_meas f hf))
      (bounded_add (fResAddI_bdd f hconj) (IResAddI_bdd f hconj))]
  have hcongr : (fun s => f s * ((1 : ℂ) / (f s + I)) + I * ((1 : ℂ) / (f s + I)))
      = (fun _ : ℝ => (1 : ℂ)) := by
    funext s
    have hne : f s + I ≠ 0 := add_I_ne_zero_of_conj (hconj s)
    field_simp
  rw [spectralCalculus_congr U_grp hcongr _ _ measurable_const ⟨1, fun _ => norm_one.le⟩,
    spectralCalculus_one, ContinuousLinearMap.id_apply]

/-- **Surjectivity of `A_f − i`.**  Mirror of the `+i` case with symbol `1/(f−i)`. -/
theorem pmapOfPVM_sub_I_surjective :
    ∀ h : H, ∃ ψ : (pmapOfPVM U_grp f hf).domain,
      pmapOfPVM U_grp f hf ψ - I • (ψ : H) = h := by
  intro h
  have hmem : spectralCalculus U_grp (fun s => (1 : ℂ) / (f s - I)) (resSubI_meas f hf)
        (resSubI_bdd f hconj) h
      ∈ ProjValMeasure.pmapDomain U_grp.toPVM f :=
    mem_pmapDomain_spectralCalculus U_grp f (fun s => (1 : ℂ) / (f s - I)) hf (resSubI_meas f hf)
      (resSubI_bdd f hconj) (fResSubI_bdd f hconj) h
  refine ⟨⟨_, hmem⟩, ?_⟩
  have hval : pmapOfPVM U_grp f hf ⟨_, hmem⟩
      = spectralCalculus U_grp (fun s => f s * ((1 : ℂ) / (f s - I))) (fResSubI_meas f hf)
          (fResSubI_bdd f hconj) h :=
    pmapOfPVM_spectralCalculus_of_mul_bounded U_grp f (fun s => (1 : ℂ) / (f s - I)) hf
      (resSubI_meas f hf) (resSubI_bdd f hconj) (fResSubI_meas f hf) (fResSubI_bdd f hconj) h hmem
  rw [hval]
  have hIR : I • spectralCalculus U_grp (fun s => (1 : ℂ) / (f s - I)) (resSubI_meas f hf)
        (resSubI_bdd f hconj) h
      = spectralCalculus U_grp (fun s => I * ((1 : ℂ) / (f s - I))) (IResSubI_meas f hf)
          (IResSubI_bdd f hconj) h := by
    rw [spectralCalculus_smul U_grp I (fun s => (1 : ℂ) / (f s - I)) (resSubI_meas f hf)
      (resSubI_bdd f hconj) (IResSubI_meas f hf) (IResSubI_bdd f hconj)]
    rfl
  change _ - I • spectralCalculus U_grp (fun s => (1 : ℂ) / (f s - I)) (resSubI_meas f hf)
    (resSubI_bdd f hconj) h = h
  rw [hIR, ← ContinuousLinearMap.sub_apply,
    ← spectralCalculus_sub U_grp (fun s => f s * ((1 : ℂ) / (f s - I)))
      (fun s => I * ((1 : ℂ) / (f s - I))) (fResSubI_meas f hf) (fResSubI_bdd f hconj)
      (IResSubI_meas f hf) (IResSubI_bdd f hconj)
      ((fResSubI_meas f hf).sub (IResSubI_meas f hf))
      (bounded_sub (fResSubI_bdd f hconj) (IResSubI_bdd f hconj))]
  have hcongr : (fun s => f s * ((1 : ℂ) / (f s - I)) - I * ((1 : ℂ) / (f s - I)))
      = (fun _ : ℝ => (1 : ℂ)) := by
    funext s
    have hne : f s - I ≠ 0 := sub_I_ne_zero_of_conj (hconj s)
    field_simp
  rw [spectralCalculus_congr U_grp hcongr _ _ measurable_const ⟨1, fun _ => norm_one.le⟩,
    spectralCalculus_one, ContinuousLinearMap.id_apply]

/-! ### The main theorem -/

/-- **The calculus of a real symbol is self-adjoint once its domain is dense.**  Von Neumann's
deficiency criterion: `A_f` is symmetric (real symbol) and `A_f ± i` are both surjective
(unconditional), so density is the only remaining obligation. -/
theorem pmapOfPVM_isSelfAdjoint_of_real
    (hdense : Dense ((pmapOfPVM U_grp f hf).domain : Set H)) :
    IsSelfAdjoint (pmapOfPVM U_grp f hf) :=
  isSelfAdjoint_of_surjective_addSub (pmapOfPVM U_grp f hf)
    (pmapOfPVM_isFormalAdjoint_self U_grp f hf hconj) hdense
    (pmapOfPVM_add_I_surjective U_grp f hf hconj) (pmapOfPVM_sub_I_surjective U_grp f hf hconj)

/-! ### Density of the natural domain via away-from-zero bands

For reciprocal-type symbols (`1/s`, `1/√s`, `log`, …) the natural `L²` domain of `pmapOfPVM U_grp f`
contains every band-projected vector `E([1/(n+1), n+1]) y`, because the symbol is bounded on the
band.  When every diagonal measure `μ_y` is **carried by `(0,∞)`** — no negative mass and no atom
at `0`, as for the modular operator (non-negative with trivial kernel) — the bands exhaust each
`μ_y`, so the domain is dense: a vector `y` orthogonal to the whole domain has
`μ_y([1/(n+1), n+1]) = ⟪y, E(band) y⟫ = 0` for every `n`, hence `μ_y((0,∞)) = 0`, hence
`‖y‖² = μ_y(ℝ) = 0`. -/

omit hconj

/-- The away-from-zero bands `[1/(n+1), n+1]` exhaust `(0,∞)`. -/
lemma iUnion_Icc_inv_eq_Ioi :
    (⋃ n : ℕ, Set.Icc ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1)) = Set.Ioi (0 : ℝ) := by
  ext s
  simp only [Set.mem_iUnion, Set.mem_Icc, Set.mem_Ioi]
  constructor
  · rintro ⟨n, h1, -⟩
    exact lt_of_lt_of_le (by positivity) h1
  · intro hs
    obtain ⟨n, hn⟩ := exists_nat_ge (max s s⁻¹)
    refine ⟨n, ?_, ((le_max_left s s⁻¹).trans hn).trans (by linarith)⟩
    exact inv_le_of_inv_le₀ hs (((le_max_right s s⁻¹).trans hn).trans (by linarith))

include hf in
/-- **Band membership**: `E([1/(n+1), n+1]) y ∈ D(∫f dP)` for any symbol `f` bounded on the
band (via the weighted-measure criterion `mem_pmapDomain_spectralCalculus`). -/
theorem spectralProjection_band_mem_pmapDomain {n : ℕ} {C : ℝ}
    (hC : ∀ s ∈ Set.Icc ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1), ‖f s‖ ≤ C) (y : H) :
    spectralProjection U_grp (Set.Icc ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1)) measurableSet_Icc y
      ∈ ProjValMeasure.pmapDomain U_grp.toPVM f := by
  have hfg_bdd : ∃ C', ∀ s,
      ‖f s * Set.indicator (Set.Icc ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1)) (fun _ => (1 : ℂ)) s‖ ≤ C' := by
    refine ⟨max C 0, fun s => ?_⟩
    by_cases hs : s ∈ Set.Icc ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1)
    · rw [Set.indicator_of_mem hs, mul_one]
      exact (hC s hs).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem hs, mul_zero, norm_zero]
      exact le_max_right _ _
  exact mem_pmapDomain_spectralCalculus U_grp f _ hf
    (measurable_const.indicator measurableSet_Icc) (indicator_one_bdd _) hfg_bdd y

/-- **Density of the natural domain** for a symbol bounded on each band `[1/(n+1), n+1]`, when
every diagonal measure is carried by `(0,∞)`.  A vector `y` orthogonal to the domain is in
particular orthogonal to every band projection `E([1/(n+1), n+1]) y` (which the band bound puts
in the domain), so `μ_y(band) = ⟪y, E(band) y⟫ = 0`; the bands exhaust `(0,∞)`, the carried-support
hypotheses kill `(-∞,0)` and `{0}`, and `‖y‖² = μ_y(ℝ) = 0`. -/
theorem pmapOfPVM_domain_dense_of_support_Ioi
    (hIio : ∀ y : H, borelMeasure U_grp y (Set.Iio (0 : ℝ)) = 0)
    (hzero : ∀ y : H, borelMeasure U_grp y ({0} : Set ℝ) = 0)
    (hband : ∀ n : ℕ, ∃ C, ∀ s ∈ Set.Icc ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1), ‖f s‖ ≤ C) :
    Dense ((pmapOfPVM U_grp f hf).domain : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro y hy
  haveI : IsFiniteMeasure (borelMeasure U_grp y) := borelMeasure_isFiniteMeasure U_grp y
  -- every band is `μ_y`-null: `E(band) y` lies in the domain, hence is orthogonal to `y`
  have hbandnull : ∀ n : ℕ, borelMeasure U_grp y (Set.Icc ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1)) = 0 := by
    intro n
    obtain ⟨C, hC⟩ := hband n
    have horth : ⟪y, spectralProjection U_grp (Set.Icc ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1))
        measurableSet_Icc y⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal' _ y).mp hy _
        (spectralProjection_band_mem_pmapDomain U_grp f hf hC y)
    rw [inner_spectralProjection_self] at horth
    have htoReal : (borelMeasure U_grp y (Set.Icc ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1))).toReal = 0 := by
      exact_mod_cast horth
    exact ((ENNReal.toReal_eq_zero_iff _).mp htoReal).resolve_right (measure_ne_top _ _)
  -- hence `μ_y((0,∞)) = 0`, and with the carried-support hypotheses `μ_y(ℝ) = 0`
  have hIoi : borelMeasure U_grp y (Set.Ioi (0 : ℝ)) = 0 := by
    rw [← iUnion_Icc_inv_eq_Ioi]
    exact measure_iUnion_null hbandnull
  have hsub : (Set.univ : Set ℝ) ⊆ Set.Iio 0 ∪ ({0} ∪ Set.Ioi 0) := by
    intro s _
    rcases lt_trichotomy s 0 with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have huniv0 : borelMeasure U_grp y (Set.univ : Set ℝ) = 0 := by
    have hle : borelMeasure U_grp y (Set.univ : Set ℝ)
        ≤ borelMeasure U_grp y (Set.Iio 0) + (borelMeasure U_grp y ({0} : Set ℝ)
            + borelMeasure U_grp y (Set.Ioi 0)) :=
      le_trans (measure_mono hsub)
        (le_trans (measure_union_le _ _) (by gcongr; exact measure_union_le _ _))
    rw [hIio y, hzero y, hIoi] at hle
    simpa using hle
  -- `‖y‖² = μ_y(ℝ) = 0`
  have hnormsq : ‖y‖ ^ 2 = 0 := by
    have h := norm_sq_spectralProjection U_grp (Set.univ : Set ℝ) MeasurableSet.univ y
    rw [spectralProjection_univ] at h
    simp only [ContinuousLinearMap.id_apply] at h
    rw [h, huniv0]
    simp
  have hnorm : ‖y‖ = 0 := by nlinarith [norm_nonneg y, hnormsq]
  exact norm_eq_zero.mp hnorm

end Spectra.QuantumMechanics.SpectralTheory
