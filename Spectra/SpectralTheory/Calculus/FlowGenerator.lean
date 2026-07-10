/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SpectralTheory.Calculus.SquareSpectralMap
import Spectra.SpectralTheory.Calculus.PMapRealSelfAdjoint
import Spectra.Bochner.Borel.Measure.Basic
import Spectra.YosidaHille.Unique
import Spectra.Resolvent.Integral.Domain
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
/-!
# The generator of a spectral flow: `generator V = ∫ φ dE_U`

This file proves the **general Stone-type theorem for the spectral exponential flow of a real
symbol**.  Fix a one-parameter unitary group `U` with spectral measure `E_U` and a *real-valued*
measurable symbol `φ : ℝ → ℂ` (`conj (φ s) = φ s`).  The one-parameter unitary group whose action
is `V.U t = ∫ e^{i t φ(s)} dE_U(s) = Φ_U(exp(i t φ))` (the **spectral flow** of the symbol `φ`) has
generator the unbounded functional calculus of `φ`:

> `generator V = pmapOfPVM U φ = ∫ φ(s) dE_U(s)`.

The proof is entirely resolvent-theoretic, reusing the finished unbounded-calculus infrastructure:

* the resolvent of `A_φ := pmapOfPVM U φ` at any non-real `z` is the bounded calculus
  `Φ_U(1/(φ − z))` (`selfAdjointResolvent_pmapOfPVM_real_eq`), via the mixed bounded/unbounded
  product law — a `φ`-parametrised copy of `selfAdjointResolvent_sq_eq`;
* the spectral (Bochner–Herglotz) measure of the flow `V` is the `φ`-pushforward of `E_U`
  (`borelMeasure_flowSymbol_eq_map`), by matching characteristic functions — a copy of
  `borelMeasure_stoneGroup_eq_map`;
* the two facts identify the diagonals of `(generator V − i)⁻¹` and `(A_φ − i)⁻¹`, and
  `eq_of_selfAdjointResolvent_eq` (a self-adjoint operator is determined by its resolvent at `i`)
  finishes.

## Instances

* `φ = id` (`fun s => s`) recovers **Stone's theorem** — the flow is `U` itself
  (`genToGroup_eq_spectralCalculus_char`) and the generator is `∫ s dE_U = generator U`.
* `φ = log` gives the **modular Hamiltonian** `generator (Δ^{it}) = log Δ` of Tomita–Takesaki
  (`Spectra/Modular/Cocycle/ModularHamiltonian.lean`).
-/

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal
open Spectra Spectra.Borel Spectra.OneParameterUnitaryGroup Spectra.YosidaHille
open Spectra.Essential Spectra.Resolvent Spectra.Borel.SpectralMeasure

namespace Spectra.QuantumMechanics.SpectralTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The flow symbol `s ↦ e^{i t φ(s)}` -/

/-- The **spectral-flow symbol** of a symbol `φ` at parameter `t`: `s ↦ exp(i t φ(s))`. -/
noncomputable def flowSymbol (φ : ℝ → ℂ) (t : ℝ) : ℝ → ℂ :=
  fun s => cexp (I * (t : ℂ) * φ s)

/-- The flow symbol is measurable. -/
lemma measurable_flowSymbol (φ : ℝ → ℂ) (hφ : Measurable φ) (t : ℝ) :
    Measurable (flowSymbol φ t) :=
  Complex.measurable_exp.comp (measurable_const.mul hφ)

/-- The flow symbol is unimodular (its exponent is imaginary, since `φ` is real), hence bounded. -/
lemma flowSymbol_bdd (φ : ℝ → ℂ) (hconj : ∀ s, (starRingEnd ℂ) (φ s) = φ s) (t : ℝ) :
    ∃ C, ∀ s, ‖flowSymbol φ t s‖ ≤ C := by
  refine ⟨1, fun s => le_of_eq ?_⟩
  rw [flowSymbol, norm_exp]
  have him0 : (φ s).im = 0 := Complex.conj_eq_iff_im.mp (hconj s)
  have hre : (I * (t : ℂ) * φ s).re = 0 := by simp [Complex.mul_re, Complex.mul_im, him0]
  rw [hre, Real.exp_zero]

/-- A real complex number is its own real-coercion: `((φ s).re : ℂ) = φ s`. -/
lemma ofReal_re_of_conj {c : ℂ} (hc : (starRingEnd ℂ) c = c) : ((c.re : ℝ) : ℂ) = c :=
  Complex.ext (Complex.ofReal_re _)
    (by rw [Complex.ofReal_im]; exact (Complex.conj_eq_iff_im.mp hc).symm)

/-! ## Resolvent-symbol arithmetic for a real symbol `φ` (`Im z ≠ 0`)

These are `φ`-parametrised copies of the `s ↦ s²` lemmas in `SquarePushforward.lean`; the only fact
used is that `φ` is real, so `(φ s − z).im = −z.im`. -/

variable (f : ℝ → ℂ)

/-- `(φ s − z).im = −z.im` (a real value contributes no imaginary part). -/
lemma real_sub_im (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s) (z : ℂ) (s : ℝ) :
    (f s - z).im = -z.im := by
  have him0 : (f s).im = 0 := Complex.conj_eq_iff_im.mp (hconj s)
  rw [Complex.sub_im, him0, zero_sub]

/-- `φ s − z ≠ 0` when `Im z ≠ 0`. -/
lemma real_sub_ne_zero (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s) {z : ℂ} (hz : z.im ≠ 0) (s : ℝ) :
    f s - z ≠ 0 := by
  intro h
  apply hz
  have him := real_sub_im f hconj z s
  rw [h, Complex.zero_im] at him
  linarith

/-- The resolvent symbol is bounded: `‖1/(φ s − z)‖ ≤ |Im z|⁻¹`. -/
lemma norm_inv_real_sub_le (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s) {z : ℂ} (hz : z.im ≠ 0)
    (s : ℝ) : ‖(f s - z)⁻¹‖ ≤ |z.im|⁻¹ := by
  rw [norm_inv]
  have hpos : 0 < |z.im| := abs_pos.mpr hz
  have hge : |z.im| ≤ ‖f s - z‖ := by
    have h1 : |(f s - z).im| ≤ ‖f s - z‖ := Complex.abs_im_le_norm _
    rwa [real_sub_im f hconj z s, abs_neg] at h1
  simp only [← one_div]
  exact one_div_le_one_div_of_le hpos hge

/-- Partial fractions: `φ s · 1/(φ s − z) = 1 + z · 1/(φ s − z)`. -/
lemma real_mul_inv_eq (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s) {z : ℂ} (hz : z.im ≠ 0) (s : ℝ) :
    f s * (f s - z)⁻¹ = 1 + z * (f s - z)⁻¹ := by
  have hne := real_sub_ne_zero f hconj hz s
  field_simp
  ring

lemma measurable_inv_real_sub (hf : Measurable f) (z : ℂ) :
    Measurable (fun s : ℝ => (f s - z)⁻¹) := (hf.sub measurable_const).inv

lemma bdd_inv_real_sub (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s) {z : ℂ} (hz : z.im ≠ 0) :
    ∃ C, ∀ s : ℝ, ‖(f s - z)⁻¹‖ ≤ C := ⟨|z.im|⁻¹, norm_inv_real_sub_le f hconj hz⟩

lemma bdd_f_mul_inv (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s) {z : ℂ} (hz : z.im ≠ 0) :
    ∃ C, ∀ s : ℝ, ‖f s * (f s - z)⁻¹‖ ≤ C := by
  refine ⟨1 + ‖z‖ * |z.im|⁻¹, fun s => ?_⟩
  rw [real_mul_inv_eq f hconj hz s]
  calc ‖(1 : ℂ) + z * (f s - z)⁻¹‖
      ≤ ‖(1 : ℂ)‖ + ‖z * (f s - z)⁻¹‖ := norm_add_le _ _
    _ = 1 + ‖z‖ * ‖(f s - z)⁻¹‖ := by rw [norm_mul, NormOneClass.norm_one]
    _ ≤ 1 + ‖z‖ * |z.im|⁻¹ := by gcongr; exact norm_inv_real_sub_le f hconj hz s

lemma bdd_const_mul_inv_real_sub (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s) {z : ℂ}
    (hz : z.im ≠ 0) :
    ∃ C, ∀ s : ℝ, ‖z * (f s - z)⁻¹‖ ≤ C := by
  refine ⟨‖z‖ * |z.im|⁻¹, fun s => ?_⟩
  rw [norm_mul]; gcongr; exact norm_inv_real_sub_le f hconj hz s

lemma bdd_one_add_const_mul_inv_real_sub (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s) {z : ℂ}
    (hz : z.im ≠ 0) : ∃ C, ∀ s : ℝ, ‖(1 : ℂ) + z * (f s - z)⁻¹‖ ≤ C := by
  refine ⟨1 + ‖z‖ * |z.im|⁻¹, fun s => ?_⟩
  calc ‖(1 : ℂ) + z * (f s - z)⁻¹‖
      ≤ ‖(1 : ℂ)‖ + ‖z * (f s - z)⁻¹‖ := norm_add_le _ _
    _ = 1 + ‖z‖ * ‖(f s - z)⁻¹‖ := by rw [norm_mul, NormOneClass.norm_one]
    _ ≤ 1 + ‖z‖ * |z.im|⁻¹ := by gcongr; exact norm_inv_real_sub_le f hconj hz s

/-! ## The resolvent identity for `A_φ := pmapOfPVM U φ` -/

variable (U : OneParameterUnitaryGroup (H := H))

/-- **Domain membership** `Φ_U(1/(φ − z)) ξ ∈ D(A_φ)`. -/
theorem resolvent_real_mem (hf : Measurable f) (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s)
    {z : ℂ} (hz : z.im ≠ 0) (ξ : H) :
    spectralCalculus U (fun s => (f s - z)⁻¹) (measurable_inv_real_sub f hf z)
        (bdd_inv_real_sub f hconj hz) ξ
      ∈ (pmapOfPVM U f hf).domain :=
  mem_pmapDomain_spectralCalculus U f (fun s => (f s - z)⁻¹) hf (measurable_inv_real_sub f hf z)
    (bdd_inv_real_sub f hconj hz) (bdd_f_mul_inv f hconj hz) ξ

/-- **The resolvent identity** `A_φ (Φ_U(1/(φ−z)) ξ) = ξ + z • Φ_U(1/(φ−z)) ξ`, i.e.
`Φ_U(1/(φ−z))` is the right inverse of `A_φ − z`.  Copy of `resolvent_sq_identity`. -/
theorem resolvent_real_identity (hf : Measurable f) (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s)
    {z : ℂ} (hz : z.im ≠ 0) (ξ : H) :
    pmapOfPVM U f hf
        ⟨spectralCalculus U (fun s => (f s - z)⁻¹) (measurable_inv_real_sub f hf z)
            (bdd_inv_real_sub f hconj hz) ξ, resolvent_real_mem f U hf hconj hz ξ⟩
      = ξ + z • spectralCalculus U (fun s => (f s - z)⁻¹) (measurable_inv_real_sub f hf z)
          (bdd_inv_real_sub f hconj hz) ξ := by
  rw [pmapOfPVM_spectralCalculus_of_mul_bounded U f (fun s => (f s - z)⁻¹) hf
      (measurable_inv_real_sub f hf z) (bdd_inv_real_sub f hconj hz)
      (hf.mul (measurable_inv_real_sub f hf z)) (bdd_f_mul_inv f hconj hz) ξ
      (resolvent_real_mem f U hf hconj hz ξ)]
  have hpt : (fun s : ℝ => f s * (f s - z)⁻¹) = (fun s : ℝ => (1 : ℂ) + z * (f s - z)⁻¹) :=
    funext (real_mul_inv_eq f hconj hz)
  rw [spectralCalculus_congr U hpt (hf.mul (measurable_inv_real_sub f hf z))
      (bdd_f_mul_inv f hconj hz)
      (measurable_const.add ((measurable_inv_real_sub f hf z).const_mul z))
      (bdd_one_add_const_mul_inv_real_sub f hconj hz),
    spectralCalculus_add U (fun _ => (1 : ℂ)) (fun s => z * (f s - z)⁻¹)
      measurable_const ⟨1, fun _ => le_of_eq NormOneClass.norm_one⟩
      ((measurable_inv_real_sub f hf z).const_mul z) (bdd_const_mul_inv_real_sub f hconj hz)
      (measurable_const.add ((measurable_inv_real_sub f hf z).const_mul z))
      (bdd_one_add_const_mul_inv_real_sub f hconj hz),
    spectralCalculus_one,
    spectralCalculus_smul U z (fun s => (f s - z)⁻¹) (measurable_inv_real_sub f hf z)
      (bdd_inv_real_sub f hconj hz) ((measurable_inv_real_sub f hf z).const_mul z)
      (bdd_const_mul_inv_real_sub f hconj hz)]
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]

/-- **The self-adjoint resolvent bridge** `(A_φ − z)⁻¹ = Φ_U(1/(φ−z))`.  Copy of
`selfAdjointResolvent_sq_eq`.  Needs density of `D(A_φ)` (to know `A_φ` is self-adjoint). -/
theorem selfAdjointResolvent_pmapOfPVM_real_eq (hf : Measurable f)
    (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s)
    (hdense : Dense ((pmapOfPVM U f hf).domain : Set H)) {z : ℂ} (hz : z.im ≠ 0) (ξ : H) :
    selfAdjointResolvent (pmapOfPVM_isSelfAdjoint_of_real U f hf hconj hdense) z hz ξ
      = spectralCalculus U (fun s => (f s - z)⁻¹) (measurable_inv_real_sub f hf z)
          (bdd_inv_real_sub f hconj hz) ξ := by
  have hli := selfAdjointResolvent_left_inverse
    (pmapOfPVM_isSelfAdjoint_of_real U f hf hconj hdense)
    z hz ⟨spectralCalculus U (fun s => (f s - z)⁻¹) (measurable_inv_real_sub f hf z)
      (bdd_inv_real_sub f hconj hz) ξ, resolvent_real_mem f U hf hconj hz ξ⟩
  rw [resolvent_real_identity f U hf hconj hz ξ] at hli
  simpa using hli

/-- **The resolvent diagonal identity** `⟪ξ, Φ_U(1/(φ−z)) ξ⟫ = ∫ (φ s − z)⁻¹ dμ^U_ξ`. -/
theorem inner_resolvent_real (hf : Measurable f) (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s)
    {z : ℂ} (hz : z.im ≠ 0) (ξ : H) :
    ⟪ξ, spectralCalculus U (fun s => (f s - z)⁻¹) (measurable_inv_real_sub f hf z)
        (bdd_inv_real_sub f hconj hz) ξ⟫_ℂ
      = ∫ s, (f s - z)⁻¹ ∂(borelMeasure U ξ) := by
  rw [inner_spectralCalculus U _ (measurable_inv_real_sub f hf z) (bdd_inv_real_sub f hconj hz) ξ ξ,
    spectralForm_self U ξ (measurable_inv_real_sub f hf z) (bdd_inv_real_sub f hconj hz)]

/-! ## The spectral measure of the flow is the `φ`-pushforward of `E_U` -/

/-- **The flow-measure pushforward.**  If `V.U t = Φ_U(exp(i t φ))` for all `t` (the flow of the
real symbol `φ`), then the Bochner–Herglotz measure of `V` is the `φ`-pushforward of that of `U`:

`borelMeasure V ξ = (fun s => (φ s).re)_* (borelMeasure U ξ)`.

Both measures have characteristic function `t ↦ ⟪ξ, V.U t ξ⟫`: the left by `borelMeasure_fourier`,
the right by `integral_map` + the flow hypothesis + `spectralForm_self`, so `Measure.ext_of_charFun`
identifies them.  Copy of `borelMeasure_stoneGroup_eq_map`. -/
theorem borelMeasure_flowSymbol_eq_map (V : OneParameterUnitaryGroup (H := H))
    (hf : Measurable f) (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s)
    (hflow : ∀ t : ℝ, V.U t = spectralCalculus U (flowSymbol f t) (measurable_flowSymbol f hf t)
      (flowSymbol_bdd f hconj t)) (ξ : H) :
    borelMeasure V ξ = Measure.map (fun s => (f s).re) (borelMeasure U ξ) := by
  have hfre : Measurable (fun s : ℝ => (f s).re) := Complex.measurable_re.comp hf
  haveI : IsFiniteMeasure (borelMeasure V ξ) := borelMeasure_isFiniteMeasure V ξ
  haveI : IsFiniteMeasure (Measure.map (fun s => (f s).re) (borelMeasure U ξ)) := by
    constructor
    rw [Measure.map_apply hfre MeasurableSet.univ, Set.preimage_univ]
    exact measure_lt_top _ _
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have hV : charFun (borelMeasure V ξ) t = ⟪ξ, V.U t ξ⟫_ℂ := by
    rw [charFun_apply_real, borelMeasure_fourier V ξ t]
    exact integral_congr_ae (Filter.Eventually.of_forall fun l => by ring_nf)
  have hMap : charFun (Measure.map (fun s => (f s).re) (borelMeasure U ξ)) t = ⟪ξ, V.U t ξ⟫_ℂ := by
    rw [hflow t, inner_spectralCalculus U (flowSymbol f t) (measurable_flowSymbol f hf t)
        (flowSymbol_bdd f hconj t) ξ ξ,
      spectralForm_self U ξ (measurable_flowSymbol f hf t) (flowSymbol_bdd f hconj t),
      charFun_apply_real,
      integral_map hfre.aemeasurable (by fun_prop)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [flowSymbol]
    rw [ofReal_re_of_conj (hconj s)]
    ring_nf
  rw [hV, hMap]

/-! ## The generator of the spectral flow -/

/-- **The generator of a spectral flow is the functional calculus of its symbol.**

Let `U` be a one-parameter unitary group, `φ : ℝ → ℂ` a real measurable symbol whose unbounded
calculus `A_φ := pmapOfPVM U φ` has dense (natural `L²`) domain, and let `V` be the flow
`V.U t = Φ_U(exp(i t φ))`.  Then

`generator V = pmapOfPVM U φ`.

This is the resolvent-theoretic Stone theorem for the symbol `φ`: both `generator V` and `A_φ` are
self-adjoint, and they share the resolvent at `z = i` — `(generator V − i)⁻¹` has diagonal
`∫ (s − i)⁻¹ d(borelMeasure V)` (the round-trip `genToGroup (generator V) = V`), which the
pushforward `borelMeasure V = φ_*(borelMeasure U)` turns into `∫ (φ − i)⁻¹ d(borelMeasure U)`, the
diagonal of `(A_φ − i)⁻¹ = Φ_U(1/(φ − i))`. -/
theorem generator_eq_pmapOfPVM_of_flowSymbol (V : OneParameterUnitaryGroup (H := H))
    (hf : Measurable f) (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s)
    (hdense : Dense ((pmapOfPVM U f hf).domain : Set H))
    (hflow : ∀ t : ℝ, V.U t = spectralCalculus U (flowSymbol f t) (measurable_flowSymbol f hf t)
      (flowSymbol_bdd f hconj t)) :
    generator V = pmapOfPVM U f hf := by
  have hK : IsSelfAdjoint (generator V) := generator_isSelfAdjoint V
  have hL : IsSelfAdjoint (pmapOfPVM U f hf) := pmapOfPVM_isSelfAdjoint_of_real U f hf hconj hdense
  -- the round-trip `genToGroup (generator V) = V`
  have hround : genToGroup hK = V :=
    group_unique (genToGroup hK) V (generator_genToGroup hK)
  refine eq_of_selfAdjointResolvent_eq hK hL (op_ext_of_inner_self fun ξ => ?_)
  -- RHS: resolvent of `A_φ` at `i` is `∫ (φ − i)⁻¹ dμ^U_ξ`
  have hRHS : ⟪ξ, selfAdjointResolvent hL I I_im_ne_zero ξ⟫_ℂ
      = ∫ s, (f s - I)⁻¹ ∂(borelMeasure U ξ) := by
    rw [selfAdjointResolvent_pmapOfPVM_real_eq f U hf hconj hdense I_im_ne_zero ξ,
      inner_resolvent_real f U hf hconj I_im_ne_zero ξ]
  -- LHS: resolvent of `generator V` at `i` is `∫ (s − i)⁻¹ d(borelMeasure V)`
  have hLHS : ⟪ξ, selfAdjointResolvent hK I I_im_ne_zero ξ⟫_ℂ
      = ∫ s, ((s : ℂ) - I)⁻¹ ∂(borelMeasure V ξ) := by
    rw [spectralPVM_resolvent_formula hK I I_im_ne_zero ξ, spectralPVM_diag]
    exact congrArg (fun W => ∫ s, ((s : ℂ) - I)⁻¹ ∂(borelMeasure W ξ)) hround
  rw [hLHS, hRHS, borelMeasure_flowSymbol_eq_map f U V hf hconj hflow ξ,
    integral_map
      (show Measurable (fun s : ℝ => (f s).re) from Complex.measurable_re.comp hf).aemeasurable
      (show Measurable (fun s : ℝ => ((s : ℂ) - I)⁻¹) from
        (Complex.measurable_ofReal.sub measurable_const).inv).aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  change ((((f s).re : ℝ) : ℂ) - I)⁻¹ = (f s - I)⁻¹
  rw [ofReal_re_of_conj (hconj s)]

end Spectra.QuantumMechanics.SpectralTheory
