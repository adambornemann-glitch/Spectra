/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.Cocycle.ModularReciprocal
import Spectra.Modular.Cocycle.ModularPolarExtension
/-!
# The inverse calculus for the modular square root: `Δ^{-½}Δ^{½} = 1` and `Δ^{½}Δ^{-½} = 1`

For a cyclic–separating vector `Ω` of a von Neumann algebra `M`, the modular operator
`Δ = modularOp M Ω` is self-adjoint, `≥ 0`, and injective, so its spectral measures are carried by
`(0,∞)` and both `Δ^{½} = pmapOfPVM (genToGroup Δ) √s` and `Δ^{-½} = pmapOfPVM (genToGroup Δ) 1/√s`
are genuine self-adjoint operators (`ModularSqrt.lean`, `ModularReciprocal.lean`).  This file
proves that they are **mutually inverse**:

  `Δ^{-½}(Δ^{½} y) = y` on `D(Δ^{½})`,   `Δ^{½}(Δ^{-½} z) = z` on `D(Δ^{-½})`,

and hence the range characterization `ran Δ^{½} = D(Δ^{-½})`.

Both twins are closed-graph limits of cut-off pairs.  For the first: with
`a_n = Φ(√s·1_{[0,n]})y` one has `a_n → Δ^{½}y` (dominated convergence of bounded approximants),
`a_n ∈ D(Δ^{-½})`, and `Δ^{-½}a_n = Φ(1_{(0,n]})y = E([-n,n])y → y` — the mixed bounded/unbounded
product law with the pointwise identity `(1/√s)·√s·1_{[0,n]} = 1_{(0,n]}`, plus the a.e. congruence
`1_{(0,n]} = 1_{[-n,n]}` off the `μ_y`-null set `(-∞,0]` — so the limit pair `(Δ^{½}y, y)` lies in
the closed graph of the self-adjoint `Δ^{-½}`.  For the second, the same scheme along the
away-from-zero bands `B_m = [1/(m+1), m+1]`: `b_m = Φ((1/√s)·1_{B_m})z → Δ^{-½}z` and
`Δ^{½}b_m = Φ(1_{B_m})z = E(B_m)z → z`, where the band projections exhaust because the bands
increase to `(0,∞)`, which carries `μ_z`: `‖E(B_m)z − z‖² = μ_z(B_mᶜ) → μ_z((-∞,0]) = 0`.

## Main statements

* `modularSqrt_mem_modularSqrtInv_domain`, `modularSqrtInv_modularSqrt_apply` —
  **`Δ^{-½}(Δ^{½} y) = y` pointwise on `D(Δ^{½})`**.
* `modularSqrtInv_mem_modularSqrt_domain`, `modularSqrt_modularSqrtInv_apply` —
  **`Δ^{½}(Δ^{-½} z) = z` pointwise on `D(Δ^{-½})`**.
* `mem_modularSqrtInv_domain_iff` — **`ran Δ^{½} = D(Δ^{-½})`**.
-/

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace
open Spectra.QuantumMechanics.SpectralTheory
open Spectra.YosidaHille
open Spectra.OneParameterUnitaryGroup
open Spectra.Borel

namespace Spectra.TomitaTakesaki

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}
variable (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)

/-- Local abbreviation for the modular unitary group `U = genToGroup Δ` (so
`modularSqrt = pmapOfPVM U √s`, `modularSqrtInv = pmapOfPVM U (1/√s)`). -/
private noncomputable abbrev modU : OneParameterUnitaryGroup (H := H) :=
  genToGroup (modularOp_isSelfAdjoint hcyc hsep)

/-! ### The square-root cut-off symbols `√s · 1_{[0,n]}(s)` -/

/-- The square-root cut-off symbol `√s · 1_{[0,n]}(s)`. -/
private noncomputable def sqrtCut (n : ℕ) : ℝ → ℂ :=
  fun s => (Real.sqrt s : ℂ) * Set.indicator (Set.Icc 0 (n : ℝ)) (fun _ => (1 : ℂ)) s

private lemma sqrtCut_meas (n : ℕ) : Measurable (sqrtCut n) :=
  measurable_sqrtC.mul (measurable_const.indicator measurableSet_Icc)

private lemma sqrtCut_bdd (n : ℕ) : ∃ C, ∀ s, ‖sqrtCut n s‖ ≤ C := by
  refine ⟨Real.sqrt (n : ℝ), fun s => ?_⟩
  rw [sqrtCut, norm_mul]
  by_cases hs : s ∈ Set.Icc 0 (n : ℝ)
  · rw [Set.indicator_of_mem hs, NormOneClass.norm_one, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg s)]
    exact Real.sqrt_le_sqrt hs.2
  · rw [Set.indicator_of_notMem hs, norm_zero, mul_zero]
    positivity

/-- `‖sqrtCut n s‖ ≤ ‖(√s : ℂ)‖` pointwise. -/
private lemma sqrtCut_dom (n : ℕ) (s : ℝ) : ‖sqrtCut n s‖ ≤ ‖(Real.sqrt s : ℂ)‖ := by
  rw [sqrtCut, norm_mul]
  by_cases hs : s ∈ Set.Icc 0 (n : ℝ)
  · rw [Set.indicator_of_mem hs, NormOneClass.norm_one, mul_one]
  · rw [Set.indicator_of_notMem hs, norm_zero, mul_zero]
    positivity

/-- `sqrtCut n s → (√s : ℂ)` pointwise (for `s < 0` both sides are the junk value `0`). -/
private lemma sqrtCut_lim (s : ℝ) :
    Tendsto (fun n => sqrtCut n s) atTop (𝓝 ((Real.sqrt s : ℂ))) := by
  by_cases hs : 0 ≤ s
  · refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop ⌈s⌉₊] with n hn
    have hmem : s ∈ Set.Icc 0 (n : ℝ) := ⟨hs, (Nat.le_ceil s).trans (by exact_mod_cast hn)⟩
    rw [sqrtCut, Set.indicator_of_mem hmem, mul_one]
  · have hzero : ((Real.sqrt s : ℂ)) = 0 := by
      rw [Real.sqrt_eq_zero_of_nonpos (not_le.mp hs).le, Complex.ofReal_zero]
    rw [hzero]
    refine tendsto_const_nhds.congr fun n => ?_
    rw [sqrtCut, hzero, zero_mul]

/-- `(1/√s) · sqrtCut n s = 1_{(0,n]}(s)` pointwise: on `(0,n]` the square root cancels
(`√s ≠ 0`); at `s = 0` the Lean junk value `(0 : ℂ)⁻¹ = 0` kills the product while `0 ∉ (0,n]`;
for `s < 0` the junk value `√s = 0` does, and for `s > n` both indicators vanish. -/
private lemma invSqrtMul_sqrtCut_eq_indicator (n : ℕ) :
    (fun s => ((Real.sqrt s : ℂ))⁻¹ * sqrtCut n s)
      = Set.indicator (Set.Ioc 0 (n : ℝ)) fun _ => (1 : ℂ) := by
  funext s
  by_cases hs : s ∈ Set.Ioc 0 (n : ℝ)
  · have hIcc : s ∈ Set.Icc 0 (n : ℝ) := ⟨hs.1.le, hs.2⟩
    rw [sqrtCut, Set.indicator_of_mem hIcc, Set.indicator_of_mem hs, mul_one,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hs.1))]
  · rw [Set.indicator_of_notMem hs]
    by_cases hIcc : s ∈ Set.Icc 0 (n : ℝ)
    · have hs0 : s = 0 := le_antisymm (not_lt.mp fun h => hs ⟨h, hIcc.2⟩) hIcc.1
      rw [sqrtCut, Set.indicator_of_mem hIcc, mul_one, hs0]
      simp
    · rw [sqrtCut, Set.indicator_of_notMem hIcc, mul_zero, mul_zero]

/-! ### The away-from-zero band cut-off symbols `(1/√s) · 1_{[1/(m+1), m+1]}(s)` -/

/-- Band bound for the reciprocal square-root symbol: `‖1/√s‖ ≤ √(m+1)` on `[1/(m+1), m+1]`. -/
private lemma invSqrtC_band_bound (m : ℕ) :
    ∀ s ∈ Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1),
      ‖((Real.sqrt s : ℂ))⁻¹‖ ≤ Real.sqrt ((m : ℝ) + 1) := by
  intro s hs
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg s)]
  have h1 : (Real.sqrt ((m : ℝ) + 1))⁻¹ ≤ Real.sqrt s := by
    rw [← Real.sqrt_inv]
    exact Real.sqrt_le_sqrt hs.1
  exact inv_le_of_inv_le₀ (Real.sqrt_pos.mpr (by positivity)) h1

/-- Eventual band membership: each `s > 0` lies in `[1/(m+1), m+1]` for all large `m`. -/
private lemma eventually_mem_band {s : ℝ} (hs : 0 < s) :
    ∀ᶠ m : ℕ in atTop, s ∈ Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1) := by
  filter_upwards [eventually_ge_atTop ⌈max s s⁻¹⌉₊] with m hm
  have hm' : max s s⁻¹ ≤ (m : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hm)
  constructor
  · exact inv_le_of_inv_le₀ hs (((le_max_right s s⁻¹).trans hm').trans (by linarith))
  · exact ((le_max_left s s⁻¹).trans hm').trans (by linarith)

/-- The reciprocal-square-root cut-off symbol `(1/√s)·1_{[1/(m+1), m+1]}(s)`. -/
private noncomputable def invSqrtCut (m : ℕ) : ℝ → ℂ :=
  fun s => ((Real.sqrt s : ℂ))⁻¹
    * Set.indicator (Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1)) (fun _ => (1 : ℂ)) s

private lemma invSqrtCut_meas (m : ℕ) : Measurable (invSqrtCut m) :=
  measurable_invSqrtC.mul (measurable_const.indicator measurableSet_Icc)

private lemma invSqrtCut_bdd (m : ℕ) : ∃ C, ∀ s, ‖invSqrtCut m s‖ ≤ C := by
  refine ⟨Real.sqrt ((m : ℝ) + 1), fun s => ?_⟩
  rw [invSqrtCut, norm_mul]
  by_cases hs : s ∈ Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1)
  · rw [Set.indicator_of_mem hs, NormOneClass.norm_one, mul_one]
    exact invSqrtC_band_bound m s hs
  · rw [Set.indicator_of_notMem hs, norm_zero, mul_zero]
    positivity

/-- `‖invSqrtCut m s‖ ≤ ‖(1/√s : ℂ)‖` pointwise. -/
private lemma invSqrtCut_dom (m : ℕ) (s : ℝ) : ‖invSqrtCut m s‖ ≤ ‖((Real.sqrt s : ℂ))⁻¹‖ := by
  rw [invSqrtCut, norm_mul]
  by_cases hs : s ∈ Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1)
  · rw [Set.indicator_of_mem hs, NormOneClass.norm_one, mul_one]
  · rw [Set.indicator_of_notMem hs, norm_zero, mul_zero]
    positivity

/-- `invSqrtCut m s → (1/√s : ℂ)` pointwise (for `s ≤ 0` both sides are the junk value `0`). -/
private lemma invSqrtCut_lim (s : ℝ) :
    Tendsto (fun m => invSqrtCut m s) atTop (𝓝 (((Real.sqrt s : ℂ))⁻¹)) := by
  by_cases hs : 0 < s
  · refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_mem_band hs] with m hm
    rw [invSqrtCut, Set.indicator_of_mem hm, mul_one]
  · have hzero : ((Real.sqrt s : ℂ))⁻¹ = 0 := by
      rw [Real.sqrt_eq_zero_of_nonpos (not_lt.mp hs), Complex.ofReal_zero, inv_zero]
    rw [hzero]
    refine tendsto_const_nhds.congr fun m => ?_
    rw [invSqrtCut, hzero, zero_mul]

/-- `√s · invSqrtCut m s = 1_{[1/(m+1), m+1]}(s)` pointwise: the band sits inside `(0,∞)`, where
`√s · (1/√s) = 1`; off the band both sides vanish. -/
private lemma sqrtMul_invSqrtCut_eq_indicator (m : ℕ) :
    (fun s => (Real.sqrt s : ℂ) * invSqrtCut m s)
      = Set.indicator (Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1)) fun _ => (1 : ℂ) := by
  funext s
  by_cases hs : s ∈ Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1)
  · have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs.1
    rw [invSqrtCut, Set.indicator_of_mem hs, mul_one,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hspos))]
  · rw [invSqrtCut, Set.indicator_of_notMem hs, mul_zero, mul_zero]

/-! ### The modular spectral measures charge nothing on `(-∞, 0]` -/

/-- The modular spectral measure of every vector kills `(-∞, 0]`: positivity kills `(-∞,0)`
(`borelMeasure_modular_Iio_zero`), injectivity kills the atom `{0}`
(`borelMeasure_modular_singleton_zero`). -/
private lemma borelMeasure_modular_Iic_zero (y : H) :
    borelMeasure (modU hcyc hsep) y (Set.Iic (0 : ℝ)) = 0 := by
  have h1 : borelMeasure (modU hcyc hsep) y (Set.Iio (0 : ℝ)) = 0 :=
    borelMeasure_modular_Iio_zero hcyc hsep y
  have h2 : borelMeasure (modU hcyc hsep) y ({0} : Set ℝ) = 0 :=
    borelMeasure_modular_singleton_zero hcyc hsep y
  rw [← Set.Iio_union_right]
  exact measure_union_null h1 h2

/-! ### The first twin `Δ^{-½}(Δ^{½}y) = y` — cut-off facts -/

/-- `Φ(sqrtCut n)y → Δ^{½}y` for `y ∈ D(Δ^{½})` (dominated convergence of the bounded
approximants to the unbounded calculus, dominator `√s ∈ L²(μ_y)`). -/
private theorem tendsto_sqrtCut_image (y : (modularSqrt hcyc hsep).domain) :
    Tendsto (fun n : ℕ =>
        spectralCalculus (modU hcyc hsep) (sqrtCut n) (sqrtCut_meas n) (sqrtCut_bdd n) (y : H))
      atTop (𝓝 (modularSqrt hcyc hsep y)) :=
  tendsto_spectralCalculus_pmapOfPVM_of_dominated (modU hcyc hsep)
    (fun s => (Real.sqrt s : ℂ)) measurable_sqrtC (ξ := (y : H))
    ((ProjValMeasure.mem_pmapDomain _).mp y.2)
    sqrtCut sqrtCut_meas sqrtCut_bdd sqrtCut_dom sqrtCut_lim

/-- `Φ(sqrtCut n)y ∈ D(Δ^{-½})` (the product `(1/√s)·sqrtCut n = 1_{(0,n]}` is bounded). -/
private theorem sqrtCut_mem_modularSqrtInv_domain (y : H) (n : ℕ) :
    spectralCalculus (modU hcyc hsep) (sqrtCut n) (sqrtCut_meas n) (sqrtCut_bdd n) y
      ∈ (modularSqrtInv hcyc hsep).domain := by
  have hfg_bdd : ∃ C, ∀ s, ‖((Real.sqrt s : ℂ))⁻¹ * sqrtCut n s‖ ≤ C := by
    have h := indicator_one_bdd (Set.Ioc (0 : ℝ) (n : ℝ))
    rw [← invSqrtMul_sqrtCut_eq_indicator n] at h
    exact h
  exact mem_pmapDomain_spectralCalculus (modU hcyc hsep) (fun s => ((Real.sqrt s : ℂ))⁻¹)
    (sqrtCut n) measurable_invSqrtC (sqrtCut_meas n) (sqrtCut_bdd n) hfg_bdd y

/-- The outer application collapses: `Δ^{-½}(Φ(sqrtCut n)y) = Φ(1_{(0,n]})y` (mixed
bounded/unbounded product law plus the pointwise symbol identity). -/
private theorem modularSqrtInv_sqrtCut_apply (y : H) (n : ℕ) :
    modularSqrtInv hcyc hsep
        ⟨spectralCalculus (modU hcyc hsep) (sqrtCut n) (sqrtCut_meas n) (sqrtCut_bdd n) y,
          sqrtCut_mem_modularSqrtInv_domain hcyc hsep y n⟩
      = spectralCalculus (modU hcyc hsep)
          (Set.indicator (Set.Ioc 0 (n : ℝ)) fun _ => (1 : ℂ))
          (measurable_const.indicator measurableSet_Ioc) (indicator_one_bdd _) y := by
  have hfg_meas : Measurable fun s => ((Real.sqrt s : ℂ))⁻¹ * sqrtCut n s := by
    have h : Measurable (Set.indicator (Set.Ioc (0 : ℝ) (n : ℝ)) fun _ => (1 : ℂ)) :=
      measurable_const.indicator measurableSet_Ioc
    rw [← invSqrtMul_sqrtCut_eq_indicator n] at h
    exact h
  have hfg_bdd : ∃ C, ∀ s, ‖((Real.sqrt s : ℂ))⁻¹ * sqrtCut n s‖ ≤ C := by
    have h := indicator_one_bdd (Set.Ioc (0 : ℝ) (n : ℝ))
    rw [← invSqrtMul_sqrtCut_eq_indicator n] at h
    exact h
  have hmix := pmapOfPVM_spectralCalculus_of_mul_bounded (modU hcyc hsep)
    (fun s => ((Real.sqrt s : ℂ))⁻¹) (sqrtCut n) measurable_invSqrtC (sqrtCut_meas n)
    (sqrtCut_bdd n) hfg_meas hfg_bdd y (sqrtCut_mem_modularSqrtInv_domain hcyc hsep y n)
  have hcongr := congrArg (fun T : H →L[ℂ] H => T y)
    (spectralCalculus_congr (modU hcyc hsep) (invSqrtMul_sqrtCut_eq_indicator n)
      hfg_meas hfg_bdd (measurable_const.indicator measurableSet_Ioc) (indicator_one_bdd _))
  exact hmix.trans hcongr

/-- The indicators `1_{[-n,n]}` and `1_{(0,n]}` agree `μ_y`-a.e.: they differ only on
`(-∞, 0]`, which is `μ_y`-null. -/
private lemma indicator_Icc_ae_eq_indicator_Ioc (y : H) (n : ℕ) :
    (Set.indicator (Set.Icc (-(n : ℝ)) (n : ℝ)) fun _ => (1 : ℂ))
      =ᵐ[borelMeasure (modU hcyc hsep) y]
        (Set.indicator (Set.Ioc 0 (n : ℝ)) fun _ => (1 : ℂ)) := by
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun s hs => ?_) (borelMeasure_modular_Iic_zero hcyc hsep y)
  simp only [Set.mem_setOf_eq] at hs
  rw [Set.mem_Iic, ← not_lt]
  intro hs0
  refine hs ?_
  by_cases hsn : s ≤ (n : ℝ)
  · rw [Set.indicator_of_mem (Set.mem_Icc.mpr ⟨by linarith, hsn⟩),
      Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hs0, hsn⟩)]
  · rw [Set.indicator_of_notMem (fun h => hsn (Set.mem_Icc.mp h).2),
      Set.indicator_of_notMem (fun h => hsn (Set.mem_Ioc.mp h).2)]

/-- **Vector convergence**: `Φ(1_{(0,n]})y → y` for every `y` — via the a.e. congruence with
`E([-n,n])y` and the two-sided exhaustion `tendsto_spectralProjection_Icc_univ`. -/
private theorem tendsto_indicator_Ioc_vector (y : H) :
    Tendsto (fun n : ℕ => spectralCalculus (modU hcyc hsep)
        (Set.indicator (Set.Ioc 0 (n : ℝ)) fun _ => (1 : ℂ))
        (measurable_const.indicator measurableSet_Ioc) (indicator_one_bdd _) y)
      atTop (𝓝 y) := by
  have heq : ∀ n : ℕ,
      spectralProjection (modU hcyc hsep) (Set.Icc (-(n : ℝ)) (n : ℝ)) measurableSet_Icc y
        = spectralCalculus (modU hcyc hsep)
            (Set.indicator (Set.Ioc 0 (n : ℝ)) fun _ => (1 : ℂ))
            (measurable_const.indicator measurableSet_Ioc) (indicator_one_bdd _) y := by
    intro n
    simp only [spectralProjection]
    exact spectralCalculus_congr_ae (modU hcyc hsep) _ _ _ _ _ _ y
      (indicator_Icc_ae_eq_indicator_Ioc hcyc hsep y n)
  exact (tendsto_spectralProjection_Icc_univ (modU hcyc hsep) y).congr heq

/-- The closed-graph limit for the first twin: `(Δ^{½}y, y) ∈ graph(Δ^{-½})`, as the limit of the
cut-off pairs `(Φ(sqrtCut n)y, Φ(1_{(0,n]})y)`. -/
private theorem modularSqrt_pair_mem_modularSqrtInv_graph (y : (modularSqrt hcyc hsep).domain) :
    (modularSqrt hcyc hsep y, (y : H)) ∈ (modularSqrtInv hcyc hsep).graph := by
  have hclosed : IsClosed ((modularSqrtInv hcyc hsep).graph : Set (H × H)) :=
    (modularSqrtInv_isSelfAdjoint hcyc hsep).isClosed
  have hmemgraph : ∀ n : ℕ,
      (spectralCalculus (modU hcyc hsep) (sqrtCut n) (sqrtCut_meas n) (sqrtCut_bdd n) (y : H),
        spectralCalculus (modU hcyc hsep) (Set.indicator (Set.Ioc 0 (n : ℝ)) fun _ => (1 : ℂ))
          (measurable_const.indicator measurableSet_Ioc) (indicator_one_bdd _) (y : H))
      ∈ (modularSqrtInv hcyc hsep).graph := by
    intro n
    rw [LinearPMap.mem_graph_iff]
    exact ⟨⟨_, sqrtCut_mem_modularSqrtInv_domain hcyc hsep (y : H) n⟩, rfl,
      modularSqrtInv_sqrtCut_apply hcyc hsep (y : H) n⟩
  have hconv : Tendsto (fun n : ℕ =>
      (spectralCalculus (modU hcyc hsep) (sqrtCut n) (sqrtCut_meas n) (sqrtCut_bdd n) (y : H),
        spectralCalculus (modU hcyc hsep) (Set.indicator (Set.Ioc 0 (n : ℝ)) fun _ => (1 : ℂ))
          (measurable_const.indicator measurableSet_Ioc) (indicator_one_bdd _) (y : H)))
      atTop (𝓝 (modularSqrt hcyc hsep y, (y : H))) := by
    rw [nhds_prod_eq]
    exact (tendsto_sqrtCut_image hcyc hsep y).prodMk
      (tendsto_indicator_Ioc_vector hcyc hsep (y : H))
  exact hclosed.mem_of_tendsto hconv (Eventually.of_forall hmemgraph)

/-! ### The first twin — deliverables -/

/-- **Membership**: `Δ^{½}y ∈ D(Δ^{-½})` for `y ∈ D(Δ^{½})` — the first component of the
closed-graph limit `(Δ^{½}y, y) ∈ graph(Δ^{-½})`. -/
theorem modularSqrt_mem_modularSqrtInv_domain (y : (modularSqrt hcyc hsep).domain) :
    (modularSqrt hcyc hsep y : H) ∈ (modularSqrtInv hcyc hsep).domain := by
  have h := modularSqrt_pair_mem_modularSqrtInv_graph hcyc hsep y
  rw [LinearPMap.mem_graph_iff] at h
  obtain ⟨z, hz1, -⟩ := h
  simp only at hz1
  rw [← hz1]
  exact z.2

/-- **The first inverse twin**: `Δ^{-½}(Δ^{½} y) = y` pointwise on `D(Δ^{½})` — the value read
off the closed-graph limit `(Δ^{½}y, y) ∈ graph(Δ^{-½})`. -/
theorem modularSqrtInv_modularSqrt_apply (y : (modularSqrt hcyc hsep).domain) :
    modularSqrtInv hcyc hsep
        ⟨modularSqrt hcyc hsep y, modularSqrt_mem_modularSqrtInv_domain hcyc hsep y⟩
      = (y : H) := by
  have h := modularSqrt_pair_mem_modularSqrtInv_graph hcyc hsep y
  rw [LinearPMap.mem_graph_iff] at h
  obtain ⟨z, hz1, hz2⟩ := h
  simp only at hz1 hz2
  rw [← hz2]
  congr 1
  exact Subtype.ext hz1.symm

/-! ### The second twin `Δ^{½}(Δ^{-½}z) = z` — cut-off facts -/

/-- `Φ(invSqrtCut m)z → Δ^{-½}z` for `z ∈ D(Δ^{-½})` (dominated convergence, dominator
`1/√s ∈ L²(μ_z)` — definitional from the domain membership). -/
private theorem tendsto_invSqrtCut_image (z : (modularSqrtInv hcyc hsep).domain) :
    Tendsto (fun m : ℕ => spectralCalculus (modU hcyc hsep) (invSqrtCut m) (invSqrtCut_meas m)
        (invSqrtCut_bdd m) (z : H)) atTop (𝓝 (modularSqrtInv hcyc hsep z)) :=
  tendsto_spectralCalculus_pmapOfPVM_of_dominated (modU hcyc hsep)
    (fun s => ((Real.sqrt s : ℂ))⁻¹) measurable_invSqrtC (ξ := (z : H))
    ((ProjValMeasure.mem_pmapDomain _).mp z.2)
    invSqrtCut invSqrtCut_meas invSqrtCut_bdd invSqrtCut_dom invSqrtCut_lim

/-- `Φ(invSqrtCut m)z ∈ D(Δ^{½})` (the product `√s·invSqrtCut m = 1_{B_m}` is bounded). -/
private theorem invSqrtCut_mem_modularSqrt_domain (z : H) (m : ℕ) :
    spectralCalculus (modU hcyc hsep) (invSqrtCut m) (invSqrtCut_meas m) (invSqrtCut_bdd m) z
      ∈ (modularSqrt hcyc hsep).domain := by
  have hfg_bdd : ∃ C, ∀ s, ‖(Real.sqrt s : ℂ) * invSqrtCut m s‖ ≤ C := by
    have h := indicator_one_bdd (Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1))
    rw [← sqrtMul_invSqrtCut_eq_indicator m] at h
    exact h
  exact mem_pmapDomain_spectralCalculus (modU hcyc hsep) (fun s => (Real.sqrt s : ℂ))
    (invSqrtCut m) measurable_sqrtC (invSqrtCut_meas m) (invSqrtCut_bdd m) hfg_bdd z

/-- The outer application collapses: `Δ^{½}(Φ(invSqrtCut m)z) = Φ(1_{B_m})z` (mixed
bounded/unbounded product law plus the pointwise symbol identity). -/
private theorem modularSqrt_invSqrtCut_apply (z : H) (m : ℕ) :
    modularSqrt hcyc hsep
        ⟨spectralCalculus (modU hcyc hsep) (invSqrtCut m) (invSqrtCut_meas m) (invSqrtCut_bdd m)
            z,
          invSqrtCut_mem_modularSqrt_domain hcyc hsep z m⟩
      = spectralCalculus (modU hcyc hsep)
          (Set.indicator (Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1)) fun _ => (1 : ℂ))
          (measurable_const.indicator measurableSet_Icc) (indicator_one_bdd _) z := by
  have hfg_meas : Measurable fun s => (Real.sqrt s : ℂ) * invSqrtCut m s := by
    have h : Measurable
        (Set.indicator (Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1)) fun _ => (1 : ℂ)) :=
      measurable_const.indicator measurableSet_Icc
    rw [← sqrtMul_invSqrtCut_eq_indicator m] at h
    exact h
  have hfg_bdd : ∃ C, ∀ s, ‖(Real.sqrt s : ℂ) * invSqrtCut m s‖ ≤ C := by
    have h := indicator_one_bdd (Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1))
    rw [← sqrtMul_invSqrtCut_eq_indicator m] at h
    exact h
  have hmix := pmapOfPVM_spectralCalculus_of_mul_bounded (modU hcyc hsep)
    (fun s => (Real.sqrt s : ℂ)) (invSqrtCut m) measurable_sqrtC (invSqrtCut_meas m)
    (invSqrtCut_bdd m) hfg_meas hfg_bdd z (invSqrtCut_mem_modularSqrt_domain hcyc hsep z m)
  have hcongr := congrArg (fun T : H →L[ℂ] H => T z)
    (spectralCalculus_congr (modU hcyc hsep) (sqrtMul_invSqrtCut_eq_indicator m)
      hfg_meas hfg_bdd (measurable_const.indicator measurableSet_Icc) (indicator_one_bdd _))
  exact hmix.trans hcongr

/-- The bands exhaust the open half-line: `⋃ m, [1/(m+1), m+1] = (0, ∞)`. -/
private lemma iUnion_band_eq_Ioi :
    (⋃ m : ℕ, Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1)) = Set.Ioi (0 : ℝ) := by
  ext s
  simp only [Set.mem_iUnion, Set.mem_Ioi]
  constructor
  · rintro ⟨m, hm⟩
    exact lt_of_lt_of_le (by positivity) hm.1
  · intro hs
    exact (eventually_mem_band hs).exists

/-- **Band-projection convergence**: `E(B_m)z = Φ(1_{B_m})z → z` for every `z`.  The bands
increase to `(0,∞)`, so `‖E(B_m)z − z‖² = μ_z(B_mᶜ) → μ_z((-∞,0]) = 0` by continuity from above
of the finite measure `μ_z` (the modular measures charge nothing on `(-∞,0]`). -/
private theorem tendsto_band_indicator_vector (z : H) :
    Tendsto (fun m : ℕ => spectralCalculus (modU hcyc hsep)
        (Set.indicator (Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1)) fun _ => (1 : ℂ))
        (measurable_const.indicator measurableSet_Icc) (indicator_one_bdd _) z)
      atTop (𝓝 z) := by
  haveI : IsFiniteMeasure (borelMeasure (modU hcyc hsep) z) :=
    borelMeasure_isFiniteMeasure _ _
  -- the band complements decrease to `(-∞, 0]`, which is `μ_z`-null
  have hanti : Antitone fun m : ℕ => (Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1))ᶜ := by
    intro i j hij
    have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    exact Set.compl_subset_compl.mpr
      (Set.Icc_subset_Icc (inv_anti₀ (by positivity) (by linarith)) (by linarith))
  have hInter : (⋂ m : ℕ, (Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1))ᶜ) = Set.Iic (0 : ℝ) := by
    rw [← Set.compl_iUnion, iUnion_band_eq_Ioi, Set.compl_Ioi]
  have hmeas := tendsto_measure_iInter_atTop (μ := borelMeasure (modU hcyc hsep) z)
    (fun m : ℕ => (measurableSet_Icc.compl).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hInter, borelMeasure_modular_Iic_zero hcyc hsep z] at hmeas
  have htoReal : Tendsto (fun m : ℕ =>
      ((borelMeasure (modU hcyc hsep) z)
        ((Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1))ᶜ)).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hmeas
    simpa [Function.comp_def] using h
  -- rewrite the vector distance as that measure
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ m : ℕ, ‖spectralCalculus (modU hcyc hsep)
      (Set.indicator (Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1)) fun _ => (1 : ℂ))
      (measurable_const.indicator measurableSet_Icc) (indicator_one_bdd _) z - z‖
      = Real.sqrt (((borelMeasure (modU hcyc hsep) z)
          ((Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1))ᶜ)).toReal) := by
    intro m
    have hsq : ‖spectralProjection (modU hcyc hsep) (Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1))ᶜ
        measurableSet_Icc.compl z‖ ^ 2
        = ((borelMeasure (modU hcyc hsep) z)
            ((Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1))ᶜ)).toReal :=
      norm_sq_spectralProjection (modU hcyc hsep) _ measurableSet_Icc.compl z
    have hc : spectralCalculus (modU hcyc hsep)
        (Set.indicator (Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1)) fun _ => (1 : ℂ))
        (measurable_const.indicator measurableSet_Icc) (indicator_one_bdd _) z - z
        = - spectralProjection (modU hcyc hsep) (Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1))ᶜ
            measurableSet_Icc.compl z := by
      rw [spectralProjection_compl (modU hcyc hsep) (Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1))
        measurableSet_Icc]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, neg_sub]
      rfl
    rw [hc, norm_neg, ← Real.sqrt_sq (norm_nonneg (spectralProjection (modU hcyc hsep)
      (Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1))ᶜ measurableSet_Icc.compl z)), hsq]
  simp_rw [hnorm]
  have h := (Real.continuous_sqrt.tendsto 0).comp htoReal
  simpa [Function.comp_def, Real.sqrt_zero] using h

/-- The closed-graph limit for the second twin: `(Δ^{-½}z, z) ∈ graph(Δ^{½})`, as the limit of
the cut-off pairs `(Φ(invSqrtCut m)z, Φ(1_{B_m})z)`. -/
private theorem modularSqrtInv_pair_mem_modularSqrt_graph (z : (modularSqrtInv hcyc hsep).domain) :
    (modularSqrtInv hcyc hsep z, (z : H)) ∈ (modularSqrt hcyc hsep).graph := by
  have hclosed : IsClosed ((modularSqrt hcyc hsep).graph : Set (H × H)) :=
    (modularSqrt_isSelfAdjoint hcyc hsep).isClosed
  have hmemgraph : ∀ m : ℕ,
      (spectralCalculus (modU hcyc hsep) (invSqrtCut m) (invSqrtCut_meas m) (invSqrtCut_bdd m)
          (z : H),
        spectralCalculus (modU hcyc hsep)
          (Set.indicator (Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1)) fun _ => (1 : ℂ))
          (measurable_const.indicator measurableSet_Icc) (indicator_one_bdd _) (z : H))
      ∈ (modularSqrt hcyc hsep).graph := by
    intro m
    rw [LinearPMap.mem_graph_iff]
    exact ⟨⟨_, invSqrtCut_mem_modularSqrt_domain hcyc hsep (z : H) m⟩, rfl,
      modularSqrt_invSqrtCut_apply hcyc hsep (z : H) m⟩
  have hconv : Tendsto (fun m : ℕ =>
      (spectralCalculus (modU hcyc hsep) (invSqrtCut m) (invSqrtCut_meas m) (invSqrtCut_bdd m)
          (z : H),
        spectralCalculus (modU hcyc hsep)
          (Set.indicator (Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1)) fun _ => (1 : ℂ))
          (measurable_const.indicator measurableSet_Icc) (indicator_one_bdd _) (z : H)))
      atTop (𝓝 (modularSqrtInv hcyc hsep z, (z : H))) := by
    rw [nhds_prod_eq]
    exact (tendsto_invSqrtCut_image hcyc hsep z).prodMk
      (tendsto_band_indicator_vector hcyc hsep (z : H))
  exact hclosed.mem_of_tendsto hconv (Eventually.of_forall hmemgraph)

/-! ### The second twin — deliverables -/

/-- **Membership**: `Δ^{-½}z ∈ D(Δ^{½})` for `z ∈ D(Δ^{-½})` — the first component of the
closed-graph limit `(Δ^{-½}z, z) ∈ graph(Δ^{½})`. -/
theorem modularSqrtInv_mem_modularSqrt_domain (z : (modularSqrtInv hcyc hsep).domain) :
    (modularSqrtInv hcyc hsep z : H) ∈ (modularSqrt hcyc hsep).domain := by
  have h := modularSqrtInv_pair_mem_modularSqrt_graph hcyc hsep z
  rw [LinearPMap.mem_graph_iff] at h
  obtain ⟨w, hw1, -⟩ := h
  simp only at hw1
  rw [← hw1]
  exact w.2

/-- **The second inverse twin**: `Δ^{½}(Δ^{-½} z) = z` pointwise on `D(Δ^{-½})` — the value read
off the closed-graph limit `(Δ^{-½}z, z) ∈ graph(Δ^{½})`. -/
theorem modularSqrt_modularSqrtInv_apply (z : (modularSqrtInv hcyc hsep).domain) :
    modularSqrt hcyc hsep
        ⟨modularSqrtInv hcyc hsep z, modularSqrtInv_mem_modularSqrt_domain hcyc hsep z⟩
      = (z : H) := by
  have h := modularSqrtInv_pair_mem_modularSqrt_graph hcyc hsep z
  rw [LinearPMap.mem_graph_iff] at h
  obtain ⟨w, hw1, hw2⟩ := h
  simp only at hw1 hw2
  rw [← hw2]
  congr 1
  exact Subtype.ext hw1.symm

/-! ### The range characterization `ran Δ^{½} = D(Δ^{-½})` -/

/-- **Range characterization**: `z ∈ D(Δ^{-½})` iff `z ∈ ran Δ^{½}`.  Forward: `y := Δ^{-½}z`
works by the second twin; backward: `Δ^{½}y ∈ D(Δ^{-½})` by the first membership. -/
theorem mem_modularSqrtInv_domain_iff (z : H) :
    z ∈ (modularSqrtInv hcyc hsep).domain
      ↔ ∃ y : (modularSqrt hcyc hsep).domain, modularSqrt hcyc hsep y = z := by
  constructor
  · intro hz
    exact ⟨⟨modularSqrtInv hcyc hsep ⟨z, hz⟩,
        modularSqrtInv_mem_modularSqrt_domain hcyc hsep ⟨z, hz⟩⟩,
      modularSqrt_modularSqrtInv_apply hcyc hsep ⟨z, hz⟩⟩
  · rintro ⟨y, rfl⟩
    exact modularSqrt_mem_modularSqrtInv_domain hcyc hsep y

end Spectra.TomitaTakesaki
