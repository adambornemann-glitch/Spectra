/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.Cocycle.ModularSqrt
import Spectra.Modular.Cocycle.ModularSqrtSquare
import Spectra.Modular.Cocycle.PolarIsometry
import Spectra.Modular.Cocycle.ModularFlowVacuum
import Spectra.SpectralTheory.Calculus.MixedProduct
import Spectra.SpectralTheory.Measure.GeneratorLink
/-!
# The Rieffel–van Daele bounded picture: `R = 2(1+Δ)⁻¹`, `T = 2Δ^{½}(1+Δ)⁻¹`

An **engine for the base-`M` Tomita theorem build** (fields 6/7/8 of `ModularData`, the
`Δ^{it} M Δ^{-it} = M` / `JMJ = M'` package): the Rieffel–van Daele route replaces the unbounded
pair `(Δ, Δ^{½})` by the *bounded* self-adjoint calculus elements

  `R := Φ(2/(1+s))`,   `T := Φ(2√s/(1+s))`,

of the modular unitary group `U_Δ = genToGroup (modularOp_isSelfAdjoint hcyc hsep)`.  The raw
symbols blow up at `s = -1`, so both are truncated by the indicator of `[0,∞)`; the junk below `0`
is invisible because the modular spectral measures are carried by `(0,∞)`
(`borelMeasure_modular_Iio_zero`, `borelMeasure_modular_singleton_zero`).

## Main statements

* `rvdR`, `rvdT` — the truncated calculus elements, with `rvdR_norm_le : ‖R‖ ≤ 2` and
  `rvdT_norm_le : ‖T‖ ≤ 1`.
* `rvdR_adjoint`, `rvdT_adjoint` — both are self-adjoint (real symbols).
* `rvdT_sq` — the algebraic identity `T² = R(2 - R)`.
* `rvdR_comm_modularFlow`, `rvdT_comm_modularFlow` — both commute with the flow `Δ^{it}`.
* `rvdR_apply_mem_modularOp_domain` / `modularOp_rvdR_apply` — **resolvent gluing**:
  `Rξ ∈ D(Δ)` and `Δ(Rξ) = 2ξ - Rξ` (i.e. `(1+Δ)R = 2`).
* `rvdR_apply_mem_modularSqrt_domain` / `modularSqrt_rvdR_apply` — `Rξ ∈ D(Δ^{½})` and
  `Δ^{½}(Rξ) = Tξ`.
* `rvdR_injective`, `rvdT_injective`, `denseRange_rvdR`, `denseRange_rvdT` — both are injective
  with dense range (symbols strictly positive on the spectral support `(0,∞)`).

Also included (generic layer): `spectralCalculus_congr_ae_forall` — the operator-level a.e.
congruence lemma for the bounded calculus.
-/

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace
open Spectra.YosidaHille
open Spectra.OneParameterUnitaryGroup
open Spectra.Borel
open Spectra.Borel.SpectralMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Generic layer: operator-level a.e. congruence -/

namespace Spectra.QuantumMechanics.SpectralTheory

variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- **Operator-level a.e. congruence.**  If two bounded symbols agree `μ_ξ`-a.e. for *every*
vector `ξ`, the calculus elements coincide as operators.  Pointwise this is
`spectralCalculus_congr_ae`. -/
theorem spectralCalculus_congr_ae_forall {g₁ g₂ : ℝ → ℂ}
    (h₁m : Measurable g₁) (h₁b : ∃ C, ∀ ω, ‖g₁ ω‖ ≤ C)
    (h₂m : Measurable g₂) (h₂b : ∃ C, ∀ ω, ‖g₂ ω‖ ≤ C)
    (hae : ∀ ξ : H, g₁ =ᵐ[borelMeasure U_grp ξ] g₂) :
    spectralCalculus U_grp g₁ h₁m h₁b = spectralCalculus U_grp g₂ h₂m h₂b :=
  ContinuousLinearMap.ext fun ξ =>
    spectralCalculus_congr_ae U_grp g₁ g₂ h₁m h₁b h₂m h₂b ξ (hae ξ)

end Spectra.QuantumMechanics.SpectralTheory

namespace Spectra.TomitaTakesaki

open Spectra.QuantumMechanics.SpectralTheory

variable {M : VonNeumannAlgebra H} {Ω : H}

/-! ## The Rieffel–van Daele symbols

Both symbols are truncated by `1_{[0,∞)}`: the raw `2/(1+s)` has a pole at `s = -1`, and the
truncation costs nothing since the modular spectral measures live on `(0,∞)`. -/

/-- The resolvent symbol `1_{[0,∞)}(s) · 2/(1+s)` of `R = 2(1+Δ)⁻¹`. -/
private noncomputable def rvdRSym : ℝ → ℂ :=
  Set.indicator (Set.Ici 0) fun s => 2 / (1 + (s : ℂ))

/-- The geometric-mean symbol `1_{[0,∞)}(s) · 2√s/(1+s)` of `T = 2Δ^{½}(1+Δ)⁻¹`. -/
private noncomputable def rvdTSym : ℝ → ℂ :=
  Set.indicator (Set.Ici 0) fun s => 2 * (Real.sqrt s : ℂ) / (1 + (s : ℂ))

/-- `1 + s ≠ 0` in `ℂ` for real `s ≥ 0`. -/
private lemma one_add_ofReal_ne_zero {s : ℝ} (hs : 0 ≤ s) : (1 : ℂ) + (s : ℂ) ≠ 0 := by
  rw [show (1 : ℂ) + (s : ℂ) = ((1 + s : ℝ) : ℂ) by push_cast; ring]
  exact Complex.ofReal_ne_zero.mpr (by linarith)

/-- `‖1 + s‖ = 1 + s` in `ℂ` for real `s ≥ 0`. -/
private lemma norm_one_add_ofReal {s : ℝ} (hs : 0 ≤ s) : ‖(1 : ℂ) + (s : ℂ)‖ = 1 + s := by
  rw [show (1 : ℂ) + (s : ℂ) = ((1 + s : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by linarith)]

private lemma measurable_rvdRSym : Measurable rvdRSym := by
  refine Measurable.indicator ?_ measurableSet_Ici
  simp only [div_eq_mul_inv]
  exact measurable_const.mul (measurable_const.add Complex.measurable_ofReal).inv

private lemma measurable_rvdTSym : Measurable rvdTSym := by
  refine Measurable.indicator ?_ measurableSet_Ici
  simp only [div_eq_mul_inv]
  exact (measurable_const.mul measurable_sqrtC).mul
    (measurable_const.add Complex.measurable_ofReal).inv

/-- On `[0,∞)` the resolvent symbol has norm `2/(1+s)`. -/
private lemma norm_rvdRSym_of_nonneg {s : ℝ} (hs : 0 ≤ s) : ‖rvdRSym s‖ = 2 / (1 + s) := by
  rw [rvdRSym, Set.indicator_of_mem (Set.mem_Ici.mpr hs), norm_div, norm_one_add_ofReal hs]
  norm_num

/-- On `[0,∞)` the geometric-mean symbol has norm `2√s/(1+s)`. -/
private lemma norm_rvdTSym_of_nonneg {s : ℝ} (hs : 0 ≤ s) :
    ‖rvdTSym s‖ = 2 * Real.sqrt s / (1 + s) := by
  rw [rvdTSym, Set.indicator_of_mem (Set.mem_Ici.mpr hs), norm_div, norm_mul,
    norm_one_add_ofReal hs, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg s)]
  norm_num

/-- The pointwise bound `‖rvdRSym‖ ≤ 2`. -/
private lemma norm_rvdRSym_le (s : ℝ) : ‖rvdRSym s‖ ≤ 2 := by
  by_cases hs : (0 : ℝ) ≤ s
  · rw [norm_rvdRSym_of_nonneg hs, div_le_iff₀ (by linarith)]
    linarith
  · rw [rvdRSym, Set.indicator_of_notMem (by simpa using hs), norm_zero]
    norm_num

/-- The pointwise bound `‖rvdTSym‖ ≤ 1` — AM–GM: `2√s ≤ 1 + s`. -/
private lemma norm_rvdTSym_le (s : ℝ) : ‖rvdTSym s‖ ≤ 1 := by
  by_cases hs : (0 : ℝ) ≤ s
  · rw [norm_rvdTSym_of_nonneg hs, div_le_one (by linarith)]
    nlinarith [Real.sq_sqrt hs, Real.sqrt_nonneg s, sq_nonneg (Real.sqrt s - 1)]
  · rw [rvdTSym, Set.indicator_of_notMem (by simpa using hs), norm_zero]
    norm_num

private lemma rvdRSym_bdd : ∃ C, ∀ ω, ‖rvdRSym ω‖ ≤ C := ⟨2, norm_rvdRSym_le⟩

private lemma rvdTSym_bdd : ∃ C, ∀ ω, ‖rvdTSym ω‖ ≤ C := ⟨1, norm_rvdTSym_le⟩

private lemma two_bdd : ∃ C, ∀ _ : ℝ, ‖(2 : ℂ)‖ ≤ C := ⟨2, fun _ => by norm_num⟩

private lemma twoMulOne_bdd : ∃ C, ∀ ω : ℝ, ‖(2 : ℂ) * (fun _ : ℝ => (1 : ℂ)) ω‖ ≤ C :=
  ⟨2, fun _ => by norm_num⟩

/-! ### Symbol identities -/

/-- Both symbols are real: `conj ∘ rvdRSym = rvdRSym`. -/
private lemma conj_rvdRSym : (fun s => (starRingEnd ℂ) (rvdRSym s)) = rvdRSym := by
  funext s
  rw [rvdRSym]
  by_cases hs : s ∈ Set.Ici (0 : ℝ)
  · rw [Set.indicator_of_mem hs, map_div₀, map_add, map_one, Complex.conj_ofReal, map_ofNat]
  · rw [Set.indicator_of_notMem hs, map_zero]

/-- `conj ∘ rvdTSym = rvdTSym`. -/
private lemma conj_rvdTSym : (fun s => (starRingEnd ℂ) (rvdTSym s)) = rvdTSym := by
  funext s
  rw [rvdTSym]
  by_cases hs : s ∈ Set.Ici (0 : ℝ)
  · rw [Set.indicator_of_mem hs, map_div₀, map_mul, map_add, map_one, Complex.conj_ofReal,
      Complex.conj_ofReal, map_ofNat]
  · rw [Set.indicator_of_notMem hs, map_zero]

/-- The square identity at the symbol level, pointwise EVERYWHERE (both sides vanish off
`[0,∞)`, and on `[0,∞)` it is `(2√s/(1+s))² = (2/(1+s))(2 - 2/(1+s))`). -/
private lemma rvdTSym_mul_self :
    (fun s => rvdTSym s * rvdTSym s) = fun s => rvdRSym s * ((2 : ℂ) - rvdRSym s) := by
  funext s
  rw [rvdTSym, rvdRSym]
  by_cases hs : s ∈ Set.Ici (0 : ℝ)
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
    have hs0 : (0 : ℝ) ≤ s := hs
    have hne := one_add_ofReal_ne_zero hs0
    have hsq : ((Real.sqrt s : ℝ) : ℂ) * ((Real.sqrt s : ℝ) : ℂ) = (s : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hs0]
    field_simp
    linear_combination hsq
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, zero_mul, zero_mul]

/-- The gluing identity `s · rvdRSym s = 2 - rvdRSym s` on `[0,∞)` (i.e. `(1+s)·2/(1+s) = 2`). -/
private lemma idMul_rvdRSym_eq_of_nonneg {s : ℝ} (hs : 0 ≤ s) :
    (s : ℂ) * rvdRSym s = (2 : ℂ) - rvdRSym s := by
  rw [rvdRSym, Set.indicator_of_mem (Set.mem_Ici.mpr hs)]
  have hne := one_add_ofReal_ne_zero hs
  field_simp
  ring

/-- The multiplier identity `√s · rvdRSym s = rvdTSym s`, pointwise EVERYWHERE (off `[0,∞)`
both sides are `0` since `rvdRSym` and the indicator vanish). -/
private lemma sqrtMul_rvdRSym_eq_rvdTSym :
    (fun s => (Real.sqrt s : ℂ) * rvdRSym s) = rvdTSym := by
  funext s
  rw [rvdRSym, rvdTSym]
  by_cases hs : s ∈ Set.Ici (0 : ℝ)
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
    ring
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, mul_zero]

private lemma measurable_idMulRvdRSym : Measurable fun l : ℝ => (l : ℂ) * rvdRSym l :=
  Complex.measurable_ofReal.mul measurable_rvdRSym

/-- The bound `‖s · rvdRSym s‖ ≤ 2`: on `[0,∞)` it is `2s/(1+s) ≤ 2`, off it the symbol is `0`. -/
private lemma idMulRvdRSym_bdd : ∃ C, ∀ ω : ℝ, ‖(ω : ℂ) * rvdRSym ω‖ ≤ C := by
  refine ⟨2, fun ω => ?_⟩
  by_cases hs : (0 : ℝ) ≤ ω
  · rw [norm_mul, norm_rvdRSym_of_nonneg hs, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hs, ← mul_div_assoc, div_le_iff₀ (by linarith)]
    linarith
  · rw [rvdRSym, Set.indicator_of_notMem (by simpa using hs), mul_zero, norm_zero]
    norm_num

private lemma measurable_sqrtMulRvdRSym :
    Measurable fun s : ℝ => (Real.sqrt s : ℂ) * rvdRSym s :=
  measurable_sqrtC.mul measurable_rvdRSym

/-- The bound `‖√s · rvdRSym s‖ ≤ 1` — the product IS the `T` symbol. -/
private lemma sqrtMulRvdRSym_bdd : ∃ C, ∀ s : ℝ, ‖(Real.sqrt s : ℂ) * rvdRSym s‖ ≤ C :=
  ⟨1, fun s => by rw [show (Real.sqrt s : ℂ) * rvdRSym s = rvdTSym s from
    congrFun sqrtMul_rvdRSym_eq_rvdTSym s]; exact norm_rvdTSym_le s⟩

/-- The `T` symbol is nonzero on `(0,∞)`. -/
private lemma rvdTSym_ne_zero {s : ℝ} (hs : 0 < s) : rvdTSym s ≠ 0 := by
  rw [rvdTSym, Set.indicator_of_mem (Set.mem_Ici.mpr hs.le)]
  exact div_ne_zero
    (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hs)))
    (one_add_ofReal_ne_zero hs.le)

/-- The `R` symbol is nonzero on `(0,∞)`. -/
private lemma rvdRSym_ne_zero {s : ℝ} (hs : 0 < s) : rvdRSym s ≠ 0 := by
  rw [rvdRSym, Set.indicator_of_mem (Set.mem_Ici.mpr hs.le)]
  exact div_ne_zero two_ne_zero (one_add_ofReal_ne_zero hs.le)

/-! ## The operators `R` and `T` -/

variable (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)

/-- Local abbreviation for the modular unitary group `U_Δ = genToGroup Δ`. -/
private noncomputable abbrev modU : OneParameterUnitaryGroup (H := H) :=
  genToGroup (modularOp_isSelfAdjoint hcyc hsep)

/-- **The Rieffel–van Daele resolvent** `R := Φ(1_{[0,∞)} · 2/(1+s)) = 2(1+Δ)⁻¹`, a bounded
calculus element of the modular group. -/
noncomputable def rvdR : H →L[ℂ] H :=
  spectralCalculus (modU hcyc hsep) rvdRSym measurable_rvdRSym rvdRSym_bdd

/-- **The Rieffel–van Daele geometric mean** `T := Φ(1_{[0,∞)} · 2√s/(1+s)) = 2Δ^{½}(1+Δ)⁻¹`. -/
noncomputable def rvdT : H →L[ℂ] H :=
  spectralCalculus (modU hcyc hsep) rvdTSym measurable_rvdTSym rvdTSym_bdd

/-- `‖R‖ ≤ 2`. -/
theorem rvdR_norm_le : ‖rvdR hcyc hsep‖ ≤ 2 :=
  norm_spectralCalculus_le (modU hcyc hsep) rvdRSym measurable_rvdRSym rvdRSym_bdd norm_rvdRSym_le

/-- `‖T‖ ≤ 1`. -/
theorem rvdT_norm_le : ‖rvdT hcyc hsep‖ ≤ 1 :=
  norm_spectralCalculus_le (modU hcyc hsep) rvdTSym measurable_rvdTSym rvdTSym_bdd norm_rvdTSym_le

/-! ## Self-adjointness -/

/-- `R` is self-adjoint (its symbol is real). -/
theorem rvdR_adjoint : ContinuousLinearMap.adjoint (rvdR hcyc hsep) = rvdR hcyc hsep := by
  unfold rvdR
  rw [spectralCalculus_adjoint (modU hcyc hsep) rvdRSym measurable_rvdRSym rvdRSym_bdd
    (Complex.continuous_conj.measurable.comp measurable_rvdRSym)
    ⟨2, fun ω => by rw [RCLike.norm_conj]; exact norm_rvdRSym_le ω⟩]
  exact spectralCalculus_congr (modU hcyc hsep) conj_rvdRSym
    (Complex.continuous_conj.measurable.comp measurable_rvdRSym)
    ⟨2, fun ω => by rw [RCLike.norm_conj]; exact norm_rvdRSym_le ω⟩
    measurable_rvdRSym rvdRSym_bdd

/-- `T` is self-adjoint (its symbol is real). -/
theorem rvdT_adjoint : ContinuousLinearMap.adjoint (rvdT hcyc hsep) = rvdT hcyc hsep := by
  unfold rvdT
  rw [spectralCalculus_adjoint (modU hcyc hsep) rvdTSym measurable_rvdTSym rvdTSym_bdd
    (Complex.continuous_conj.measurable.comp measurable_rvdTSym)
    ⟨1, fun ω => by rw [RCLike.norm_conj]; exact norm_rvdTSym_le ω⟩]
  exact spectralCalculus_congr (modU hcyc hsep) conj_rvdTSym
    (Complex.continuous_conj.measurable.comp measurable_rvdTSym)
    ⟨1, fun ω => by rw [RCLike.norm_conj]; exact norm_rvdTSym_le ω⟩
    measurable_rvdTSym rvdTSym_bdd

/-! ## The algebraic identity `T² = R(2 - R)` -/

/-- `Φ(const 2) = 2 • 1`. -/
private lemma spectralCalculus_const_two :
    spectralCalculus (modU hcyc hsep) (fun _ : ℝ => (2 : ℂ)) measurable_const two_bdd
      = (2 : ℂ) • (1 : H →L[ℂ] H) := by
  have h1 := spectralCalculus_congr (modU hcyc hsep)
    (show (fun _ : ℝ => (2 : ℂ)) = fun l : ℝ => (2 : ℂ) * (fun _ : ℝ => (1 : ℂ)) l from
      funext fun l => by norm_num)
    measurable_const two_bdd measurable_const twoMulOne_bdd
  have h2 := spectralCalculus_smul (modU hcyc hsep) 2 (fun _ : ℝ => (1 : ℂ))
    measurable_const ⟨1, fun _ => norm_one.le⟩ measurable_const twoMulOne_bdd
  rw [h1, h2, spectralCalculus_one, ContinuousLinearMap.one_def]

/-- **The square identity** `T² = R(2 - R)` — multiplicativity of the calculus plus the symbol
identity `(2√s/(1+s))² = (2/(1+s))(2 - 2/(1+s))` (both sides vanish off `[0,∞)`, including at
`s = 0` where both are `0`). -/
theorem rvdT_sq :
    rvdT hcyc hsep * rvdT hcyc hsep
      = rvdR hcyc hsep * ((2 : ℂ) • (1 : H →L[ℂ] H) - rvdR hcyc hsep) := by
  unfold rvdT rvdR
  rw [spectralCalculus_mul (modU hcyc hsep) rvdTSym rvdTSym measurable_rvdTSym rvdTSym_bdd
      measurable_rvdTSym rvdTSym_bdd (measurable_rvdTSym.mul measurable_rvdTSym)
      (bounded_mul rvdTSym_bdd rvdTSym_bdd),
    spectralCalculus_congr (modU hcyc hsep) rvdTSym_mul_self
      (measurable_rvdTSym.mul measurable_rvdTSym) (bounded_mul rvdTSym_bdd rvdTSym_bdd)
      (measurable_rvdRSym.mul (measurable_const.sub measurable_rvdRSym))
      (bounded_mul rvdRSym_bdd (bounded_sub two_bdd rvdRSym_bdd)),
    ← spectralCalculus_mul (modU hcyc hsep) (fun l => (2 : ℂ) - rvdRSym l) rvdRSym
      (measurable_const.sub measurable_rvdRSym) (bounded_sub two_bdd rvdRSym_bdd)
      measurable_rvdRSym rvdRSym_bdd
      (measurable_rvdRSym.mul (measurable_const.sub measurable_rvdRSym))
      (bounded_mul rvdRSym_bdd (bounded_sub two_bdd rvdRSym_bdd)),
    spectralCalculus_sub (modU hcyc hsep) (fun _ : ℝ => (2 : ℂ)) rvdRSym measurable_const two_bdd
      measurable_rvdRSym rvdRSym_bdd (measurable_const.sub measurable_rvdRSym)
      (bounded_sub two_bdd rvdRSym_bdd),
    spectralCalculus_const_two hcyc hsep]

/-! ## Commutation with the modular flow -/

/-- `T` commutes with the modular flow `Δ^{it}`. -/
theorem rvdT_comm_modularFlow [Nontrivial H] (t : ℝ) :
    rvdT hcyc hsep * (modularFlow hcyc hsep).U t
      = (modularFlow hcyc hsep).U t * rvdT hcyc hsep := by
  unfold rvdT
  rw [modularFlow_U_eq_spectralCalculus hcyc hsep t]
  exact spectralCalculus_comm (modU hcyc hsep) (logExpSym t) rvdTSym
    (measurable_logExpSym t) (logExpSym_bdd t) measurable_rvdTSym rvdTSym_bdd

/-- `R` commutes with the modular flow `Δ^{it}`. -/
theorem rvdR_comm_modularFlow [Nontrivial H] (t : ℝ) :
    rvdR hcyc hsep * (modularFlow hcyc hsep).U t
      = (modularFlow hcyc hsep).U t * rvdR hcyc hsep := by
  unfold rvdR
  rw [modularFlow_U_eq_spectralCalculus hcyc hsep t]
  exact spectralCalculus_comm (modU hcyc hsep) (logExpSym t) rvdRSym
    (measurable_logExpSym t) (logExpSym_bdd t) measurable_rvdRSym rvdRSym_bdd

/-! ## Resolvent gluing: `(1+Δ)R = 2` and `Δ^{½}R = T` -/

/-- Symbols agreeing on `[0,∞)` agree a.e. for every modular spectral measure (which charges
no negative reals: `borelMeasure_modular_Iio_zero`). -/
private lemma ae_eq_modular {g₁ g₂ : ℝ → ℂ} (h : ∀ s : ℝ, 0 ≤ s → g₁ s = g₂ s) (ξ : H) :
    g₁ =ᵐ[borelMeasure (modU hcyc hsep) ξ] g₂ := by
  have hμ : borelMeasure (modU hcyc hsep) ξ (Set.Iio (0 : ℝ)) = 0 :=
    borelMeasure_modular_Iio_zero hcyc hsep ξ
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun s hs => ?_) hμ
  simp only [Set.mem_setOf_eq] at hs
  rw [Set.mem_Iio]
  by_contra hle
  exact hs (h s (not_lt.mp hle))

/-- **`Rξ ∈ D(Δ)`** — through the generator: `s · rvdRSym s` is bounded, so `Φ(rvdRSym)ξ` is a
spectrally bounded vector, and `D(generator U_Δ) = D(Δ)` by Stone. -/
theorem rvdR_apply_mem_modularOp_domain (ξ : H) :
    rvdR hcyc hsep ξ ∈ (modularOp M Ω).domain := by
  have h := spectralCalculus_mem_generatorDomain (modU hcyc hsep) rvdRSym
    measurable_rvdRSym rvdRSym_bdd measurable_idMulRvdRSym idMulRvdRSym_bdd ξ
  have hgen : generator (modU hcyc hsep) = modularOp M Ω :=
    generator_genToGroup (modularOp_isSelfAdjoint hcyc hsep)
  rw [← hgen]
  exact h

/-- **The gluing identity `Δ(Rξ) = 2ξ - Rξ`** (i.e. `(1+Δ)Rξ = 2ξ`): the generator acts through
the calculus with symbol `s · rvdRSym s`, which agrees with `2 - rvdRSym s` on `[0,∞)`, hence
a.e. for every modular spectral measure. -/
theorem modularOp_rvdR_apply (ξ : H) :
    modularOp M Ω ⟨rvdR hcyc hsep ξ, rvdR_apply_mem_modularOp_domain hcyc hsep ξ⟩
      = (2 : ℂ) • ξ - rvdR hcyc hsep ξ := by
  have hgen : generator (modU hcyc hsep) = modularOp M Ω :=
    generator_genToGroup (modularOp_isSelfAdjoint hcyc hsep)
  have hval : generator (modU hcyc hsep)
      ⟨spectralCalculus (modU hcyc hsep) rvdRSym measurable_rvdRSym rvdRSym_bdd ξ,
        spectralCalculus_mem_generatorDomain (modU hcyc hsep) rvdRSym measurable_rvdRSym
          rvdRSym_bdd measurable_idMulRvdRSym idMulRvdRSym_bdd ξ⟩
      = modularOp M Ω ⟨rvdR hcyc hsep ξ, rvdR_apply_mem_modularOp_domain hcyc hsep ξ⟩ :=
    (le_of_eq hgen).2 rfl
  rw [← hval, generator_spectralCalculus (modU hcyc hsep) rvdRSym measurable_rvdRSym rvdRSym_bdd
    measurable_idMulRvdRSym idMulRvdRSym_bdd ξ,
    spectralCalculus_congr_ae (modU hcyc hsep) (fun l => (l : ℂ) * rvdRSym l)
      (fun l => (2 : ℂ) - rvdRSym l) measurable_idMulRvdRSym idMulRvdRSym_bdd
      (measurable_const.sub measurable_rvdRSym) (bounded_sub two_bdd rvdRSym_bdd) ξ
      (ae_eq_modular hcyc hsep (fun s hs => idMul_rvdRSym_eq_of_nonneg hs) ξ),
    spectralCalculus_sub (modU hcyc hsep) (fun _ : ℝ => (2 : ℂ)) rvdRSym measurable_const two_bdd
      measurable_rvdRSym rvdRSym_bdd (measurable_const.sub measurable_rvdRSym)
      (bounded_sub two_bdd rvdRSym_bdd),
    ContinuousLinearMap.sub_apply, spectralCalculus_const_two hcyc hsep]
  rfl

/-- **`Rξ ∈ D(Δ^{½})`** — the product symbol `√s · rvdRSym s` is bounded (it IS the `T`
symbol), so `mem_pmapDomain_spectralCalculus` applies. -/
theorem rvdR_apply_mem_modularSqrt_domain (ξ : H) :
    rvdR hcyc hsep ξ ∈ (modularSqrt hcyc hsep).domain :=
  mem_pmapDomain_spectralCalculus (modU hcyc hsep) (fun s => (Real.sqrt s : ℂ)) rvdRSym
    measurable_sqrtC measurable_rvdRSym rvdRSym_bdd sqrtMulRvdRSym_bdd ξ

/-- **`Δ^{½}(Rξ) = Tξ`** — the mixed bounded/unbounded product law collapses
`pmapOfPVM √ ∘ Φ(rvdRSym)` to the bounded `Φ(√s · rvdRSym s) = Φ(rvdTSym) = T` (the product
symbol equals the `T` symbol pointwise everywhere: off `[0,∞)` both vanish). -/
theorem modularSqrt_rvdR_apply (ξ : H) :
    modularSqrt hcyc hsep ⟨rvdR hcyc hsep ξ, rvdR_apply_mem_modularSqrt_domain hcyc hsep ξ⟩
      = rvdT hcyc hsep ξ := by
  have hmix := pmapOfPVM_spectralCalculus_of_mul_bounded (modU hcyc hsep)
    (fun s => (Real.sqrt s : ℂ)) rvdRSym measurable_sqrtC measurable_rvdRSym rvdRSym_bdd
    measurable_sqrtMulRvdRSym sqrtMulRvdRSym_bdd ξ
    (rvdR_apply_mem_modularSqrt_domain hcyc hsep ξ)
  have hcongr := congrArg (fun A : H →L[ℂ] H => A ξ)
    (spectralCalculus_congr (modU hcyc hsep) sqrtMul_rvdRSym_eq_rvdTSym
      measurable_sqrtMulRvdRSym sqrtMulRvdRSym_bdd measurable_rvdTSym rvdTSym_bdd)
  exact hmix.trans hcongr

/-! ## Injectivity and dense range -/

/-- A calculus element whose symbol is nonzero on `(0,∞)` kills only `0`: from `Φ(g)ξ = 0`,
`∫‖g‖² dμ_ξ = 0`, so `μ_ξ` vanishes on `(0,∞)`; positivity and injectivity of `Δ` kill
`(-∞,0)` and `{0}`, so `‖ξ‖² = μ_ξ(ℝ) = 0`. -/
private lemma eq_zero_of_spectralCalculus_eq_zero {g : ℝ → ℂ}
    (hm : Measurable g) (hb : ∃ C, ∀ ω, ‖g ω‖ ≤ C)
    (hpos : ∀ s : ℝ, 0 < s → g s ≠ 0) {ξ : H}
    (h0 : spectralCalculus (modU hcyc hsep) g hm hb ξ = 0) : ξ = 0 := by
  haveI : IsFiniteMeasure (borelMeasure (modU hcyc hsep) ξ) :=
    borelMeasure_isFiniteMeasure (modU hcyc hsep) ξ
  -- the `L²` mass of the symbol vanishes
  have hint : (∫ s, ‖g s‖ ^ 2 ∂(borelMeasure (modU hcyc hsep) ξ)) = 0 := by
    rw [← norm_sq_spectralCalculus_apply (modU hcyc hsep) g hm hb ξ, h0, norm_zero]
    norm_num
  have hInt : Integrable (fun s => ‖g s‖ ^ 2) (borelMeasure (modU hcyc hsep) ξ) := by
    obtain ⟨C, hC⟩ := hb
    refine (integrable_const (C ^ 2)).mono' (hm.norm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [hC s, norm_nonneg (g s)]
  have hae : (fun s => ‖g s‖ ^ 2) =ᵐ[borelMeasure (modU hcyc hsep) ξ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun s => by positivity) hInt).mp hint
  -- hence `μ_ξ((0,∞)) = 0`, since the symbol is nonzero there
  have hIoi : borelMeasure (modU hcyc hsep) ξ (Set.Ioi (0 : ℝ)) = 0 := by
    have hset := ae_iff.mp hae
    refine measure_mono_null (fun s hs => ?_) hset
    simp only [Set.mem_setOf_eq, Pi.zero_apply]
    exact fun heq => hpos s hs (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp heq))
  -- the other pieces vanish by the modular support theorems
  have hIio : borelMeasure (modU hcyc hsep) ξ (Set.Iio (0 : ℝ)) = 0 :=
    borelMeasure_modular_Iio_zero hcyc hsep ξ
  have hatom : borelMeasure (modU hcyc hsep) ξ ({0} : Set ℝ) = 0 :=
    borelMeasure_modular_singleton_zero hcyc hsep ξ
  have huniv : borelMeasure (modU hcyc hsep) ξ (Set.univ : Set ℝ) = 0 := by
    have hsub : (Set.univ : Set ℝ) ⊆ Set.Iio 0 ∪ ({0} ∪ Set.Ioi 0) := fun s _ => by
      rcases lt_trichotomy s 0 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    refine le_zero_iff.mp ?_
    calc borelMeasure (modU hcyc hsep) ξ (Set.univ : Set ℝ)
        ≤ borelMeasure (modU hcyc hsep) ξ (Set.Iio 0)
            + (borelMeasure (modU hcyc hsep) ξ ({0} : Set ℝ)
              + borelMeasure (modU hcyc hsep) ξ (Set.Ioi 0)) :=
          (measure_mono hsub).trans ((measure_union_le _ _).trans
            (by gcongr; exact measure_union_le _ _))
      _ = 0 := by rw [hIio, hatom, hIoi]; simp
  -- so `‖ξ‖² = 0`
  have hnorm : ‖ξ‖ ^ 2 = 0 := by
    rw [← borelMeasure_mass (modU hcyc hsep) ξ, huniv]
    simp
  exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hnorm)

/-- **`T` is injective** (its symbol is strictly positive on the spectral support `(0,∞)`). -/
theorem rvdT_injective : Function.Injective (rvdT hcyc hsep) := by
  intro x y hxy
  have hz : rvdT hcyc hsep (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_spectralCalculus_eq_zero hcyc hsep measurable_rvdTSym
    rvdTSym_bdd (fun s hs => rvdTSym_ne_zero hs) hz)

/-- **`R` is injective**. -/
theorem rvdR_injective : Function.Injective (rvdR hcyc hsep) := by
  intro x y hxy
  have hz : rvdR hcyc hsep (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_spectralCalculus_eq_zero hcyc hsep measurable_rvdRSym
    rvdRSym_bdd (fun s hs => rvdRSym_ne_zero hs) hz)

/-- Self-adjoint + injective ⟹ dense range: `(ran A)ᗮ = ker A† = ker A = ⊥`. -/
private lemma denseRange_of_selfAdjoint_injective {A : H →L[ℂ] H}
    (hA : ContinuousLinearMap.adjoint A = A) (hinj : Function.Injective A) :
    DenseRange A := by
  have hker : A.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact hinj
  have horth : A.rangeᗮ = ⊥ := by
    rw [ContinuousLinearMap.orthogonal_range, hA, hker]
  have hdense : Dense ((A.range : Submodule ℂ H) : Set H) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (Submodule.topologicalClosure_eq_top_iff.mpr horth)
  simpa [DenseRange, LinearMap.coe_range] using hdense

/-- **`T` has dense range.** -/
theorem denseRange_rvdT : DenseRange (rvdT hcyc hsep) :=
  denseRange_of_selfAdjoint_injective (rvdT_adjoint hcyc hsep) (rvdT_injective hcyc hsep)

/-- **`R` has dense range.** -/
theorem denseRange_rvdR : DenseRange (rvdR hcyc hsep) :=
  denseRange_of_selfAdjoint_injective (rvdR_adjoint hcyc hsep) (rvdR_injective hcyc hsep)

end Spectra.TomitaTakesaki
