/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.Cocycle.ModularSqrtSquare
import Spectra.Modular.Cocycle.PolarIsometry
import Spectra.SpectralTheory.Calculus.PMapRealSelfAdjoint
/-!
# The reciprocal modular calculus `Δ⁻¹`, `Δ^{-½}` (Stage 0)

For a cyclic–separating vector `Ω` of a von Neumann algebra `M`, the modular operator
`Δ = modularOp M Ω` is self-adjoint, `≥ 0`, and **injective** (`modularOp_injective`), so `s = 0` is
a null point of its spectral measure.  Hence the reciprocal symbols `1/s` and `1/√s` are a.e.-finite
and define genuine unbounded self-adjoint operators

  `Δ⁻¹  := modularOpInv   = pmapOfPVM (genToGroup Δ) (1/s)`,
  `Δ^{-½} := modularSqrtInv = pmapOfPVM (genToGroup Δ) (1/√s)`.

This J-free layer supplies the operators needed to **state** the final Tomita relation
`J Δ J⁻¹ = Δ⁻¹` / `J Δ^{½} J⁻¹ = Δ^{-½}`.  Self-adjointness is delivered by the generic real-symbol
engine `pmapOfPVM_isSelfAdjoint_of_real` (surjectivity of `A ± i` is unconditional because the
reciprocal symbols are real), with **density of the domains** discharged by the away-from-zero band
engine `pmapOfPVM_domain_dense_of_support_Ioi`: the modular spectral measures are carried by `(0,∞)`
(`borelMeasure_modular_Iio_zero`, `borelMeasure_modular_singleton_zero`), and both reciprocal
symbols are bounded on each band `[1/(n+1), n+1]`.

## Main statements

* `modularOpInv`, `modularSqrtInv` — `Δ⁻¹`, `Δ^{-½}` as `LinearPMap`s.
* `modularOpInv_domain_dense`, `modularSqrtInv_domain_dense` — the domains are dense.
* `modularOpInv_isSelfAdjoint`, `modularSqrtInv_isSelfAdjoint` — **`Δ⁻¹` and `Δ^{-½}` are
  self-adjoint** (unconditional).
* `modularSqrtInv_sq_apply` — **`Δ^{-½}(Δ^{-½}x) = Δ⁻¹x` on `D(Δ⁻¹)`**, by the closed-graph limit of
  the away-from-zero cut-off pairs `(Φ((1/√s)·1_B)x, Φ((1/s)·1_B)x)` along the bands
  `B = [1/(m+1), m+1]` (mirror of the `(Δ^{½})² = Δ` argument in `ModularSqrtSquare.lean`).
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

/-! ### Measurability and reality of the reciprocal symbols `1/s`, `1/√s` -/

/-- The symbol `s ↦ (s : ℂ)⁻¹` is measurable. -/
lemma measurable_invC : Measurable (fun s : ℝ => ((s : ℂ))⁻¹) := Complex.measurable_ofReal.inv

/-- The symbol `s ↦ ((√s : ℂ))⁻¹` is measurable. -/
lemma measurable_invSqrtC : Measurable (fun s : ℝ => ((Real.sqrt s : ℂ))⁻¹) := measurable_sqrtC.inv

/-- The symbol `1/s` is real (`conj = id`), the reality needed by the self-adjointness engine. -/
lemma conj_invC (s : ℝ) : (starRingEnd ℂ) ((s : ℂ))⁻¹ = ((s : ℂ))⁻¹ := by
  rw [map_inv₀, Complex.conj_ofReal]

/-- The symbol `1/√s` is real (`conj = id`). -/
lemma conj_invSqrtC (s : ℝ) : (starRingEnd ℂ) ((Real.sqrt s : ℂ))⁻¹ = ((Real.sqrt s : ℂ))⁻¹ := by
  rw [map_inv₀, Complex.conj_ofReal]

/-! ### The reciprocal modular operators -/

/-- **The inverse modular operator** `Δ⁻¹ := pmapOfPVM (genToGroup Δ) (1/s)`. -/
noncomputable def modularOpInv (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) : H →ₗ.[ℂ] H :=
  pmapOfPVM (genToGroup (modularOp_isSelfAdjoint hcyc hsep)) (fun s => ((s : ℂ))⁻¹) measurable_invC

/-- **The inverse modular square root** `Δ^{-½} := pmapOfPVM (genToGroup Δ) (1/√s)`. -/
noncomputable def modularSqrtInv (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) : H →ₗ.[ℂ] H :=
  pmapOfPVM (genToGroup (modularOp_isSelfAdjoint hcyc hsep)) (fun s => ((Real.sqrt s : ℂ))⁻¹)
    measurable_invSqrtC

/-! ### Self-adjointness (conditional on domain density) -/

/-- **`Δ⁻¹` is self-adjoint** once its domain is dense.  Via the generic real-symbol engine
`pmapOfPVM_isSelfAdjoint_of_real` (the reciprocal symbol `1/s` is real, so `Δ⁻¹ ± i` are surjective
unconditionally).  Density is discharged below (`modularOpInv_domain_dense`). -/
theorem modularOpInv_isSelfAdjoint_of_dense (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)
    (hdense : Dense ((modularOpInv hcyc hsep).domain : Set H)) :
    IsSelfAdjoint (modularOpInv hcyc hsep) :=
  pmapOfPVM_isSelfAdjoint_of_real (genToGroup (modularOp_isSelfAdjoint hcyc hsep))
    (fun s => ((s : ℂ))⁻¹) measurable_invC conj_invC hdense

/-- **`Δ^{-½}` is self-adjoint** once its domain is dense (same engine, symbol `1/√s`). -/
theorem modularSqrtInv_isSelfAdjoint_of_dense (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)
    (hdense : Dense ((modularSqrtInv hcyc hsep).domain : Set H)) :
    IsSelfAdjoint (modularSqrtInv hcyc hsep) :=
  pmapOfPVM_isSelfAdjoint_of_real (genToGroup (modularOp_isSelfAdjoint hcyc hsep))
    (fun s => ((Real.sqrt s : ℂ))⁻¹) measurable_invSqrtC conj_invSqrtC hdense

/-! ### Band bounds for the reciprocal symbols -/

/-- Band bound for the reciprocal symbol: `‖1/s‖ ≤ n+1` on `[1/(n+1), n+1]`. -/
private lemma invC_band_bound (n : ℕ) :
    ∀ s ∈ Set.Icc ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1), ‖((s : ℂ))⁻¹‖ ≤ (n : ℝ) + 1 := by
  intro s hs
  have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs.1
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hspos]
  exact inv_le_of_inv_le₀ (by positivity) hs.1

/-- Band bound for the reciprocal square-root symbol: `‖1/√s‖ ≤ √(n+1)` on `[1/(n+1), n+1]`. -/
private lemma invSqrtC_band_bound (n : ℕ) :
    ∀ s ∈ Set.Icc ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1),
      ‖((Real.sqrt s : ℂ))⁻¹‖ ≤ Real.sqrt ((n : ℝ) + 1) := by
  intro s hs
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg s)]
  have h1 : (Real.sqrt ((n : ℝ) + 1))⁻¹ ≤ Real.sqrt s := by
    rw [← Real.sqrt_inv]
    exact Real.sqrt_le_sqrt hs.1
  exact inv_le_of_inv_le₀ (Real.sqrt_pos.mpr (by positivity)) h1

/-! ### Density of the reciprocal domains -/

/-- **`D(Δ⁻¹)` is dense.**  The modular spectral measures are carried by `(0,∞)` (positivity kills
`(-∞,0)`, injectivity kills the atom `{0}`), and `1/s` is bounded on each band `[1/(n+1), n+1]`,
so the away-from-zero band engine applies. -/
theorem modularOpInv_domain_dense (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    Dense ((modularOpInv hcyc hsep).domain : Set H) :=
  pmapOfPVM_domain_dense_of_support_Ioi (genToGroup (modularOp_isSelfAdjoint hcyc hsep))
    (fun s => ((s : ℂ))⁻¹) measurable_invC
    (fun y => borelMeasure_modular_Iio_zero hcyc hsep y)
    (fun y => borelMeasure_modular_singleton_zero hcyc hsep y)
    (fun n => ⟨(n : ℝ) + 1, invC_band_bound n⟩)

/-- **`D(Δ^{-½})` is dense** (same engine, symbol `1/√s`). -/
theorem modularSqrtInv_domain_dense (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    Dense ((modularSqrtInv hcyc hsep).domain : Set H) :=
  pmapOfPVM_domain_dense_of_support_Ioi (genToGroup (modularOp_isSelfAdjoint hcyc hsep))
    (fun s => ((Real.sqrt s : ℂ))⁻¹) measurable_invSqrtC
    (fun y => borelMeasure_modular_Iio_zero hcyc hsep y)
    (fun y => borelMeasure_modular_singleton_zero hcyc hsep y)
    (fun n => ⟨Real.sqrt ((n : ℝ) + 1), invSqrtC_band_bound n⟩)

/-! ### Self-adjointness (unconditional) -/

/-- **`Δ⁻¹` is self-adjoint.** -/
theorem modularOpInv_isSelfAdjoint (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    IsSelfAdjoint (modularOpInv hcyc hsep) :=
  modularOpInv_isSelfAdjoint_of_dense hcyc hsep (modularOpInv_domain_dense hcyc hsep)

/-- **`Δ^{-½}` is self-adjoint.** -/
theorem modularSqrtInv_isSelfAdjoint (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    IsSelfAdjoint (modularSqrtInv hcyc hsep) :=
  modularSqrtInv_isSelfAdjoint_of_dense hcyc hsep (modularSqrtInv_domain_dense hcyc hsep)

/-! ### The domain inclusion `D(Δ⁻¹) ⊆ D(Δ^{-½})`

Pointwise `‖1/√s‖² ≤ 1 + ‖1/s‖²` (`1/s ≤ 1/s²` on `(0,1]`, `1/s ≤ 1` on `[1,∞)`, and the Lean
junk value `1/√s = 0` for `s ≤ 0`), so `L²(μ_x)`-membership of `1/s` implies that of `1/√s`
(`μ_x` is finite). -/

/-- Pointwise domination `‖1/√s‖² ≤ 1 + ‖1/s‖²`. -/
private lemma norm_invSqrtC_sq_le (s : ℝ) :
    ‖((Real.sqrt s : ℂ))⁻¹‖ ^ 2 ≤ 1 + ‖((s : ℂ))⁻¹‖ ^ 2 := by
  rw [norm_inv, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg s)]
  by_cases hs : 0 < s
  · rw [abs_of_pos hs, ← Real.sqrt_inv, Real.sq_sqrt (inv_nonneg.mpr hs.le)]
    nlinarith [sq_nonneg (s⁻¹ - 1), inv_nonneg.mpr hs.le]
  · rw [Real.sqrt_eq_zero_of_nonpos (not_lt.mp hs)]
    simp only [inv_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity

variable (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)

/-- Local abbreviation for the modular unitary group `U = genToGroup Δ` (so
`modularOpInv = pmapOfPVM U (1/s)`, `modularSqrtInv = pmapOfPVM U (1/√s)`). -/
private noncomputable abbrev modU : OneParameterUnitaryGroup (H := H) :=
  genToGroup (modularOp_isSelfAdjoint hcyc hsep)

/-- `x ∈ D(Δ⁻¹)` puts `1/√s` in `L²(μ_x)`: `∫‖1/√s‖² dμ_x ≤ ∫(1 + ‖1/s‖²) dμ_x < ∞`. -/
private lemma invSqrt_integrable_of_mem (x : (modularOpInv hcyc hsep).domain) :
    Integrable (fun s => ‖((Real.sqrt s : ℂ))⁻¹‖ ^ 2)
      (borelMeasure (modU hcyc hsep) (x : H)) := by
  haveI : IsFiniteMeasure (borelMeasure (modU hcyc hsep) (x : H)) :=
    borelMeasure_isFiniteMeasure _ _
  have hx : Integrable (fun s : ℝ => ‖((s : ℂ))⁻¹‖ ^ 2) (borelMeasure (modU hcyc hsep) (x : H)) :=
    (ProjValMeasure.mem_pmapDomain _).mp x.2
  refine ((integrable_const (1 : ℝ)).add hx).mono'
    (measurable_invSqrtC.norm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Pi.add_apply]
  exact norm_invSqrtC_sq_le s

/-- **`D(Δ⁻¹) ⊆ D(Δ^{-½})`.** -/
theorem modularOpInv_domain_le_modularSqrtInv_domain :
    (modularOpInv hcyc hsep).domain ≤ (modularSqrtInv hcyc hsep).domain := fun x hx =>
  (ProjValMeasure.mem_pmapDomain _).mpr (invSqrt_integrable_of_mem hcyc hsep ⟨x, hx⟩)

/-! ### The away-from-zero cut-off symbols

`invSqrtCut m = (1/√s)·1_B`, `invCut m = (1/s)·1_B` along the bands `B = [1/(m+1), m+1]`, and the
positive-reciprocal symbol `posInv = (1/s)·1_{(0,∞)}` (the `μ`-a.e. shadow of `1/s` for the modular
measures, needed because `invCut m → 1/s` fails pointwise on `(-∞,0)`). -/

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

/-- The reciprocal cut-off symbol `(1/s)·1_{[1/(m+1), m+1]}(s)`. -/
private noncomputable def invCut (m : ℕ) : ℝ → ℂ :=
  fun s => ((s : ℂ))⁻¹
    * Set.indicator (Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1)) (fun _ => (1 : ℂ)) s

private lemma invCut_meas (m : ℕ) : Measurable (invCut m) :=
  measurable_invC.mul (measurable_const.indicator measurableSet_Icc)

private lemma invCut_bdd (m : ℕ) : ∃ C, ∀ s, ‖invCut m s‖ ≤ C := by
  refine ⟨(m : ℝ) + 1, fun s => ?_⟩
  rw [invCut, norm_mul]
  by_cases hs : s ∈ Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1)
  · rw [Set.indicator_of_mem hs, NormOneClass.norm_one, mul_one]
    exact invC_band_bound m s hs
  · rw [Set.indicator_of_notMem hs, norm_zero, mul_zero]
    positivity

/-- The positive-reciprocal symbol `(1/s)·1_{(0,∞)}(s)`. -/
private noncomputable def posInv : ℝ → ℂ :=
  fun s => ((s : ℂ))⁻¹ * Set.indicator (Set.Ioi (0 : ℝ)) (fun _ => (1 : ℂ)) s

private lemma posInv_meas : Measurable posInv :=
  measurable_invC.mul (measurable_const.indicator measurableSet_Ioi)

/-- `‖posInv s‖ ≤ ‖(1/s : ℂ)‖` pointwise. -/
private lemma posInv_dom (s : ℝ) : ‖posInv s‖ ≤ ‖((s : ℂ))⁻¹‖ := by
  rw [posInv, norm_mul]
  by_cases hs : s ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem hs, NormOneClass.norm_one, mul_one]
  · rw [Set.indicator_of_notMem hs, norm_zero, mul_zero]
    positivity

/-- `‖invCut m s‖ ≤ ‖posInv s‖` pointwise (the band sits inside `(0,∞)`). -/
private lemma invCut_posInv_dom (m : ℕ) (s : ℝ) : ‖invCut m s‖ ≤ ‖posInv s‖ := by
  rw [invCut, posInv, norm_mul, norm_mul]
  by_cases hs : s ∈ Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1)
  · have hs' : s ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (lt_of_lt_of_le (by positivity) hs.1)
    rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs']
  · rw [Set.indicator_of_notMem hs, norm_zero, mul_zero]
    positivity

/-- `invCut m s → posInv s` pointwise. -/
private lemma invCut_lim (s : ℝ) : Tendsto (fun m => invCut m s) atTop (𝓝 (posInv s)) := by
  by_cases hs : 0 < s
  · refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_mem_band hs] with m hm
    rw [posInv, invCut, Set.indicator_of_mem hm, Set.indicator_of_mem (Set.mem_Ioi.mpr hs)]
  · have h1 : posInv s = 0 := by
      rw [posInv, Set.indicator_of_notMem (fun h => hs (Set.mem_Ioi.mp h)), mul_zero]
    rw [h1]
    refine tendsto_const_nhds.congr fun m => ?_
    have hnot : s ∉ Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1) := fun h =>
      hs (lt_of_lt_of_le (by positivity) h.1)
    rw [invCut, Set.indicator_of_notMem hnot, mul_zero]

/-- `(1/√s) · invSqrtCut m s = invCut m s`: the reciprocal square-root cut-off squares to the
reciprocal cut-off (`(1/√s)² = 1/s` on the band, which sits inside `(0,∞)`). -/
private lemma invSqrtMul_invSqrtCut_eq_invCut (m : ℕ) :
    (fun s => ((Real.sqrt s : ℂ))⁻¹ * invSqrtCut m s) = invCut m := by
  funext s
  by_cases hs : s ∈ Set.Icc ((m : ℝ) + 1)⁻¹ ((m : ℝ) + 1)
  · have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs.1
    rw [invSqrtCut, invCut, Set.indicator_of_mem hs, mul_one, mul_one, ← mul_inv,
      ← Complex.ofReal_mul, Real.mul_self_sqrt hspos.le]
  · rw [invSqrtCut, invCut, Set.indicator_of_notMem hs, mul_zero, mul_zero, mul_zero]

/-! ### The closed-graph limit `(Δ^{-½})² = Δ⁻¹` -/

/-- `posInv` agrees with the reciprocal symbol `μ_x`-a.e. for every `x`: the modular measure
charges no negative reals, and at `0` both symbols vanish (`(0 : ℂ)⁻¹ = 0`). -/
private lemma posInv_ae_eq_inv (x : H) :
    posInv =ᵐ[borelMeasure (modU hcyc hsep) x] (fun s => ((s : ℂ))⁻¹) := by
  have hμ : borelMeasure (modU hcyc hsep) x (Set.Iio (0 : ℝ)) = 0 :=
    borelMeasure_modular_Iio_zero hcyc hsep x
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun s hs => ?_) hμ
  simp only [Set.mem_setOf_eq] at hs
  rw [Set.mem_Iio, ← not_le]
  intro hs0
  refine hs ?_
  rcases eq_or_lt_of_le hs0 with heq | hlt
  · rw [posInv, ← heq]
    simp
  · rw [posInv, Set.indicator_of_mem (Set.mem_Ioi.mpr hlt), mul_one]

/-- `x ∈ D(Δ⁻¹)` puts `posInv` in `L²(μ_x)` (dominated by `1/s`). -/
private lemma posInv_mem_pmapDomain (x : (modularOpInv hcyc hsep).domain) :
    (x : H) ∈ ProjValMeasure.pmapDomain (modU hcyc hsep).toPVM posInv := by
  rw [ProjValMeasure.mem_pmapDomain]
  have hx : Integrable (fun s : ℝ => ‖((s : ℂ))⁻¹‖ ^ 2) (borelMeasure (modU hcyc hsep) (x : H)) :=
    (ProjValMeasure.mem_pmapDomain _).mp x.2
  refine hx.mono' (posInv_meas.norm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (posInv_dom s) 2

/-- `pmapOfPVM U posInv x = Δ⁻¹ x` for `x ∈ D(Δ⁻¹)`: `posInv =ᵐ 1/s` and the unbounded calculus
is a.e.-stable (`pmapOfPVM_congr_ae`). -/
private theorem pmapOfPVM_posInv_eq_modularOpInv (x : (modularOpInv hcyc hsep).domain)
    (hpos : (x : H) ∈ ProjValMeasure.pmapDomain (modU hcyc hsep).toPVM posInv) :
    pmapOfPVM (modU hcyc hsep) posInv posInv_meas ⟨(x : H), hpos⟩ = modularOpInv hcyc hsep x := by
  rw [pmapOfPVM_congr_ae (modU hcyc hsep) posInv (fun s => ((s : ℂ))⁻¹) posInv_meas
      measurable_invC hpos x.2 (posInv_ae_eq_inv hcyc hsep (x : H))]
  rfl

/-- `Φ(invSqrtCut m)x → Δ^{-½}x` for `x ∈ D(Δ⁻¹)` (dominated convergence of the bounded
approximants to the unbounded calculus). -/
private theorem tendsto_invSqrtCut_modularSqrtInv (x : (modularOpInv hcyc hsep).domain) :
    Tendsto (fun m => spectralCalculus (modU hcyc hsep) (invSqrtCut m) (invSqrtCut_meas m)
        (invSqrtCut_bdd m) (x : H)) atTop
      (𝓝 (modularSqrtInv hcyc hsep
        ⟨(x : H), modularOpInv_domain_le_modularSqrtInv_domain hcyc hsep x.2⟩)) :=
  tendsto_spectralCalculus_pmapOfPVM_of_dominated (modU hcyc hsep)
    (fun s => ((Real.sqrt s : ℂ))⁻¹) measurable_invSqrtC (ξ := (x : H))
    (invSqrt_integrable_of_mem hcyc hsep x)
    invSqrtCut invSqrtCut_meas invSqrtCut_bdd invSqrtCut_dom invSqrtCut_lim

/-- `Φ(invSqrtCut m)x ∈ D(Δ^{-½})` (the product `(1/√s)·invSqrtCut m = invCut m` is bounded). -/
private theorem invSqrtCut_mem_modularSqrtInv_domain (x : (modularOpInv hcyc hsep).domain)
    (m : ℕ) :
    spectralCalculus (modU hcyc hsep) (invSqrtCut m) (invSqrtCut_meas m) (invSqrtCut_bdd m) (x : H)
      ∈ (modularSqrtInv hcyc hsep).domain := by
  have hfg_bdd : ∃ C, ∀ s, ‖((Real.sqrt s : ℂ))⁻¹ * invSqrtCut m s‖ ≤ C := by
    have h := invCut_bdd m
    rw [← invSqrtMul_invSqrtCut_eq_invCut m] at h
    exact h
  exact mem_pmapDomain_spectralCalculus (modU hcyc hsep) (fun s => ((Real.sqrt s : ℂ))⁻¹)
    (invSqrtCut m) measurable_invSqrtC (invSqrtCut_meas m) (invSqrtCut_bdd m) hfg_bdd (x : H)

/-- The outer application collapses: `Δ^{-½}(Φ(invSqrtCut m)x) = Φ(invCut m)x` (mixed
bounded/unbounded product law). -/
private theorem modularSqrtInv_invSqrtCut_apply (x : (modularOpInv hcyc hsep).domain) (m : ℕ) :
    modularSqrtInv hcyc hsep
        ⟨spectralCalculus (modU hcyc hsep) (invSqrtCut m) (invSqrtCut_meas m) (invSqrtCut_bdd m)
            (x : H),
          invSqrtCut_mem_modularSqrtInv_domain hcyc hsep x m⟩
      = spectralCalculus (modU hcyc hsep) (invCut m) (invCut_meas m) (invCut_bdd m) (x : H) := by
  have hfg_meas : Measurable fun s => ((Real.sqrt s : ℂ))⁻¹ * invSqrtCut m s := by
    have h := invCut_meas m
    rw [← invSqrtMul_invSqrtCut_eq_invCut m] at h
    exact h
  have hfg_bdd : ∃ C, ∀ s, ‖((Real.sqrt s : ℂ))⁻¹ * invSqrtCut m s‖ ≤ C := by
    have h := invCut_bdd m
    rw [← invSqrtMul_invSqrtCut_eq_invCut m] at h
    exact h
  have hmix := pmapOfPVM_spectralCalculus_of_mul_bounded (modU hcyc hsep)
    (fun s => ((Real.sqrt s : ℂ))⁻¹) (invSqrtCut m) measurable_invSqrtC (invSqrtCut_meas m)
    (invSqrtCut_bdd m) hfg_meas hfg_bdd (x : H)
    (invSqrtCut_mem_modularSqrtInv_domain hcyc hsep x m)
  have hcongr := congrArg (fun T : H →L[ℂ] H => T (x : H))
    (spectralCalculus_congr (modU hcyc hsep) (invSqrtMul_invSqrtCut_eq_invCut m)
      hfg_meas hfg_bdd (invCut_meas m) (invCut_bdd m))
  exact hmix.trans hcongr

/-- `Φ(invCut m)x → Δ⁻¹x`: dominated convergence toward `pmapOfPVM U posInv x`, which equals
`Δ⁻¹x` a.e. -/
private theorem tendsto_invCut_modularOpInv (x : (modularOpInv hcyc hsep).domain) :
    Tendsto (fun m => spectralCalculus (modU hcyc hsep) (invCut m) (invCut_meas m) (invCut_bdd m)
        (x : H)) atTop (𝓝 (modularOpInv hcyc hsep x)) := by
  have h := tendsto_spectralCalculus_pmapOfPVM_of_dominated (modU hcyc hsep) posInv posInv_meas
    (ξ := (x : H)) ((ProjValMeasure.mem_pmapDomain _).mp (posInv_mem_pmapDomain hcyc hsep x))
    invCut invCut_meas invCut_bdd invCut_posInv_dom invCut_lim
  rw [pmapOfPVM_posInv_eq_modularOpInv hcyc hsep x (posInv_mem_pmapDomain hcyc hsep x)] at h
  exact h

/-! ### The two Stage-0 square deliverables -/

/-- **Membership**: `Δ^{-½}x ∈ D(Δ^{-½})` for `x ∈ D(Δ⁻¹)`.  From closedness of the self-adjoint
`Δ^{-½}`: the cut-off vectors `a_m = Φ(invSqrtCut m)x ∈ D(Δ^{-½})` converge to `Δ^{-½}x`, and their
images `Δ^{-½}a_m = Φ(invCut m)x` converge to `Δ⁻¹x`, so the limit point `(Δ^{-½}x, Δ⁻¹x)` lies in
the (closed) graph. -/
theorem modularSqrtInv_mem_domain_of_mem_modularOpInv (x : (modularOpInv hcyc hsep).domain) :
    (modularSqrtInv hcyc hsep
        ⟨(x : H), modularOpInv_domain_le_modularSqrtInv_domain hcyc hsep x.2⟩ : H)
      ∈ (modularSqrtInv hcyc hsep).domain := by
  set U := modU hcyc hsep with _hU
  set S := modularSqrtInv hcyc hsep with _hS
  have hclosed : IsClosed (S.graph : Set (H × H)) :=
    (modularSqrtInv_isSelfAdjoint hcyc hsep).isClosed
  set a : ℕ → H := fun m =>
    spectralCalculus U (invSqrtCut m) (invSqrtCut_meas m) (invSqrtCut_bdd m) (x : H) with _ha
  set b : ℕ → H := fun m =>
    spectralCalculus U (invCut m) (invCut_meas m) (invCut_bdd m) (x : H) with _hb
  have hmemgraph : ∀ m, (a m, b m) ∈ S.graph := by
    intro m
    rw [LinearPMap.mem_graph_iff]
    exact ⟨⟨a m, invSqrtCut_mem_modularSqrtInv_domain hcyc hsep x m⟩, rfl,
      modularSqrtInv_invSqrtCut_apply hcyc hsep x m⟩
  have hconv : Tendsto (fun m => (a m, b m)) atTop
      (𝓝 (S ⟨(x : H), modularOpInv_domain_le_modularSqrtInv_domain hcyc hsep x.2⟩,
        modularOpInv hcyc hsep x)) := by
    rw [nhds_prod_eq]
    exact (tendsto_invSqrtCut_modularSqrtInv hcyc hsep x).prodMk
      (tendsto_invCut_modularOpInv hcyc hsep x)
  have hlimmem : (S ⟨(x : H), modularOpInv_domain_le_modularSqrtInv_domain hcyc hsep x.2⟩,
      modularOpInv hcyc hsep x) ∈ S.graph :=
    hclosed.mem_of_tendsto hconv (Filter.Eventually.of_forall hmemgraph)
  rw [LinearPMap.mem_graph_iff] at hlimmem
  obtain ⟨z, hz1, hz2⟩ := hlimmem
  simp only at hz1 hz2
  rw [← hz1]
  exact z.2

/-- **Stage 0: `(Δ^{-½})² = Δ⁻¹` pointwise on `D(Δ⁻¹)`.**  Same closed-graph limit:
`(Δ^{-½}x, Δ⁻¹x) ∈ graph(Δ^{-½})` means precisely `Δ^{-½}⟨Δ^{-½}x, _⟩ = Δ⁻¹x`. -/
theorem modularSqrtInv_sq_apply (x : (modularOpInv hcyc hsep).domain) :
    modularSqrtInv hcyc hsep
        ⟨modularSqrtInv hcyc hsep
            ⟨(x : H), modularOpInv_domain_le_modularSqrtInv_domain hcyc hsep x.2⟩,
          modularSqrtInv_mem_domain_of_mem_modularOpInv hcyc hsep x⟩
      = modularOpInv hcyc hsep x := by
  set U := modU hcyc hsep with _hU
  set S := modularSqrtInv hcyc hsep with _hS
  have hclosed : IsClosed (S.graph : Set (H × H)) :=
    (modularSqrtInv_isSelfAdjoint hcyc hsep).isClosed
  set a : ℕ → H := fun m =>
    spectralCalculus U (invSqrtCut m) (invSqrtCut_meas m) (invSqrtCut_bdd m) (x : H) with _ha
  set b : ℕ → H := fun m =>
    spectralCalculus U (invCut m) (invCut_meas m) (invCut_bdd m) (x : H) with _hb
  have hmemgraph : ∀ m, (a m, b m) ∈ S.graph := by
    intro m
    rw [LinearPMap.mem_graph_iff]
    exact ⟨⟨a m, invSqrtCut_mem_modularSqrtInv_domain hcyc hsep x m⟩, rfl,
      modularSqrtInv_invSqrtCut_apply hcyc hsep x m⟩
  have hconv : Tendsto (fun m => (a m, b m)) atTop
      (𝓝 (S ⟨(x : H), modularOpInv_domain_le_modularSqrtInv_domain hcyc hsep x.2⟩,
        modularOpInv hcyc hsep x)) := by
    rw [nhds_prod_eq]
    exact (tendsto_invSqrtCut_modularSqrtInv hcyc hsep x).prodMk
      (tendsto_invCut_modularOpInv hcyc hsep x)
  have hlimmem : (S ⟨(x : H), modularOpInv_domain_le_modularSqrtInv_domain hcyc hsep x.2⟩,
      modularOpInv hcyc hsep x) ∈ S.graph :=
    hclosed.mem_of_tendsto hconv (Filter.Eventually.of_forall hmemgraph)
  rw [LinearPMap.mem_graph_iff] at hlimmem
  obtain ⟨z, hz1, hz2⟩ := hlimmem
  simp only at hz1 hz2
  rw [← hz2]
  congr 1
  exact Subtype.ext hz1.symm

end Spectra.TomitaTakesaki
