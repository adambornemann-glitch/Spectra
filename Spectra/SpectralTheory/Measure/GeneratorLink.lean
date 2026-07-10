/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/

/-
Spectra: GeneratorLink.lean
The generator of a one-parameter unitary group acts through the bounded functional
calculus on spectrally bounded vectors.

-/
import Spectra.SpectralTheory.Measure.Convergence
/-!
# The generator through the calculus

The unbounded generator `A` of `U` (Stone) is reached from the *bounded* calculus alone:
for any bounded measurable symbol `g` such that `λ ↦ λ·g(λ)` is also bounded (the
*spectrally bounded* condition — e.g. `g = 1_B` for bounded `B`),

  `Φ(g)φ ∈ D(A)`   and   `A (Φ(g)φ) = Φ(λ·g(λ)) φ` — "`A = ∫ λ dE(λ)`".

## Proof shape

The whole argument is one application of `tendsto_spectralCalculus_apply` along `𝓝[≠] 0`:

1. **Algebra** (`genDiffQuot_spectralCalculus`): for every `t` (including `t = 0`, where
   `(i·0)⁻¹ = 0` makes both sides vanish),
   `genDiffQuot U (Φ(g)φ) t = Φ((e^{iλt} − 1)/(it) · g(λ)) φ`,
   by `spectralCalculus_char`/`_mul`/`_sub`/`_smul`.
2. **Pointwise limit** (`tendsto_char_diffQuot`): `(e^{iλt} − 1)/(it) → λ` as `t → 0` —
   the difference quotient of `t ↦ e^{iλt}` at `0`, via `hasDerivAt_iff_tendsto_slope`.
3. **Uniform bound** (`norm_genDiffQuot_symbol_le`): `‖(e^{iλt}−1)/(it)·g(λ)‖ ≤ 2·C` for
   ALL `t, λ`, from `‖e^{ix} − 1‖ ≤ 2|x|` and `‖λ·g(λ)‖ ≤ C`.

Membership in the domain is then `mem_generatorDomain.mpr`, and the value is
`tendsto_nhds_unique` against `generator_tendsto` — the Conjugate.lean idiom.

## Main statements (sorry count 0)

* `tendsto_genDiffQuot_spectralCalculus` — the convergence engine.
* `spectralCalculus_mem_generatorDomain`, `generator_spectralCalculus` — membership + value.
* `spectralProjection_mem_generatorDomain`, `generator_spectralProjection` — the
  specialization to `ψ = E(B)φ`, `B` bounded: the form consumed by the Dirac file.
-/
open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace
open Spectra.Borel
open SpectralMeasure
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open Spectra.OneParameterUnitaryGroup
namespace Spectra.QuantumMechanics.SpectralTheory
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-! ## The scalar limit -/

/-- The character's difference quotient: `(e^{iλt} − 1)/(it) → λ` as `t → 0`.  This is
`hasDerivAt_iff_tendsto_slope` for `t ↦ e^{iλt}` at `0`, rescaled by `I⁻¹`. -/
lemma tendsto_char_diffQuot (lam : ℝ) :
    Tendsto (fun t : ℝ => (I * (t : ℂ))⁻¹ * (cexp (I * lam * t) - 1)) (𝓝[≠] (0 : ℝ))
      (𝓝 (lam : ℂ)) := by
  have h3 := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul (I * (lam : ℂ))).cexp
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    Complex.ofReal_one, mul_one, one_mul] at h3
  -- h3 : HasDerivAt (fun t : ℝ => cexp (I * ↑lam * ↑t)) (I * ↑lam) 0
  have hslope := hasDerivAt_iff_tendsto_slope.mp h3
  have hmul := hslope.const_mul ((I : ℂ)⁻¹)
  have hval : (I : ℂ)⁻¹ * (I * lam) = lam := by
    rw [← mul_assoc, inv_mul_cancel₀ I_ne_zero, one_mul]
  rw [hval] at hmul
  refine hmul.congr fun t => ?_
  simp only [slope, vsub_eq_sub, sub_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    Complex.real_smul, Complex.ofReal_inv, mul_inv]
  ring

/-! ## The uniform bound -/

/-- `‖e^{ix} − 1‖ ≤ 2|x|` for ALL real `x`: `Complex.norm_exp_sub_one_le` when `|x| ≤ 1`,
and the crude triangle bound `≤ 2 < 2|x|` otherwise. -/
lemma norm_char_sub_one_le (x : ℝ) : ‖cexp (I * x) - 1‖ ≤ 2 * |x| := by
  have hIx : ‖I * (x : ℂ)‖ = |x| := by
    simp only [norm_mul, Complex.norm_I, one_mul]
    erw [RCLike.norm_ofReal]
  rcases le_or_gt ‖I * (x : ℂ)‖ 1 with h | h
  · have hb := Complex.norm_exp_sub_one_le h
    rwa [hIx] at hb
  · have _habs : (1 : ℝ) < |x| := by rwa [hIx] at h
    have hexp : ‖cexp (I * (x : ℂ))‖ = 1 := by
      have h0 : (I * (x : ℂ)).re = 0 := by
        simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im]
      rw [Complex.norm_exp, h0, Real.exp_zero]
    calc ‖cexp (I * x) - 1‖ ≤ ‖cexp (I * (x : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp only [hexp]; norm_num
      _ ≤ 2 * |x| := by nlinarith

/-- The uniform symbol bound: `‖(e^{iλt} − 1)/(it) · g(λ)‖ ≤ 2C` for ALL `t` and `λ`,
given `‖λ·g(λ)‖ ≤ C`.  At `t = 0` the coefficient `(i·0)⁻¹ = 0` kills the term. -/
lemma norm_genDiffQuot_symbol_le (g : ℝ → ℂ) {Cg : ℝ} (hC : ∀ ω, ‖(ω : ℝ) * g ω‖ ≤ Cg)
    (t lam : ℝ) :
    ‖(I * (t : ℂ))⁻¹ * (cexp (I * lam * t) * g lam - g lam)‖ ≤ 2 * Cg := by
  have hCg0 : 0 ≤ Cg := (norm_nonneg _).trans (hC 0)
  rcases eq_or_ne t 0 with rfl | ht
  · simp only [Complex.ofReal_zero, mul_zero, inv_zero, zero_mul, norm_zero]
    linarith
  · have hfact : cexp (I * lam * t) * g lam - g lam = (cexp (I * lam * t) - 1) * g lam := by
      ring
    rw [hfact, norm_mul, norm_mul, norm_inv]
    have hIt : ‖I * (t : ℂ)‖ = |t| := by
      simp only [norm_mul, Complex.norm_I, one_mul]
      erw [RCLike.norm_ofReal]
    have hg : |lam| * ‖g lam‖ ≤ Cg := by
      have h := hC lam
      simp only [norm_mul, norm_real] at h
      apply RCLike.ofReal_le_ofReal.mp h
    have hchar : ‖cexp (I * lam * t) - 1‖ ≤ 2 * (|lam| * |t|) := by
      have h := norm_char_sub_one_le (lam * t)
      rwa [show ((lam * t : ℝ) : ℂ) = (lam : ℂ) * (t : ℂ) from by push_cast; ring,
        ← mul_assoc, abs_mul] at h
    rw [hIt]
    have ht0 : (0 : ℝ) < |t| := abs_pos.mpr ht
    have htne : |t| ≠ 0 := ht0.ne'
    calc |t|⁻¹ * (‖cexp (I * lam * t) - 1‖ * ‖g lam‖)
        ≤ |t|⁻¹ * (2 * (|lam| * |t|) * ‖g lam‖) := by gcongr
      _ = 2 * (|lam| * ‖g lam‖) := by field_simp
      _ ≤ 2 * Cg := by linarith

/-! ## The symbol family -/

/-- Measurability of the difference-quotient symbol. -/
lemma genDiffQuot_symbol_measurable (g : ℝ → ℂ) (hm : Measurable g) (t : ℝ) :
    Measurable fun l : ℝ => (I * (t : ℂ))⁻¹ * (cexp (I * l * t) * g l - g l) :=
  measurable_const.mul (((char_measurable t).mul hm).sub hm)

/-- Boundedness of the difference-quotient symbol, uniformly in `t`. -/
lemma genDiffQuot_symbol_bdd (g : ℝ → ℂ) {Cg : ℝ} (hC : ∀ ω, ‖(ω : ℝ) * g ω‖ ≤ Cg) (t : ℝ) :
    ∃ C, ∀ (ω : ℝ) , ‖(I * (t : ℂ))⁻¹ * (cexp (I * ω * t) * g ω - g ω)‖ ≤ C :=
  ⟨2 * Cg, fun ω => norm_genDiffQuot_symbol_le g hC t ω⟩

/-- Pointwise limit of the difference-quotient symbol: `(e^{iλt}−1)/(it)·g(λ) → λ·g(λ)`. -/
lemma tendsto_genDiffQuot_symbol (g : ℝ → ℂ) (lam : ℝ) :
    Tendsto (fun t : ℝ => (I * (t : ℂ))⁻¹ * (cexp (I * lam * t) * g lam - g lam))
      (𝓝[≠] (0 : ℝ)) (𝓝 ((lam : ℂ) * g lam)) := by
  have h := (tendsto_char_diffQuot lam).mul_const (g lam)
  refine h.congr fun t => ?_
  ring

/-! ## The operator identity -/

/-- **The difference quotient acts through the calculus**: for every `t` (including
`t = 0`, where both sides vanish),

  `genDiffQuot U (Φ(g)φ) t = Φ( (e^{iλt} − 1)/(it) · g(λ) ) φ`.

Pure bookkeeping: `U(t) = Φ(e^{it·})`, multiplicativity, subtractivity, homogeneity. -/
lemma genDiffQuot_spectralCalculus (g : ℝ → ℂ) (hm : Measurable g)
    (hb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (φ : H) (t : ℝ)
    (hGm : Measurable fun l : ℝ => (I * (t : ℂ))⁻¹ * (cexp (I * l * t) * g l - g l))
    (hGb : ∃ C, ∀ (ω : ℝ), ‖(I * (t : ℂ))⁻¹ * (cexp (I * ω * t) * g ω - g ω)‖ ≤ C) :
    genDiffQuot U_grp (spectralCalculus U_grp g hm hb φ) t
      = spectralCalculus U_grp
          (fun l => (I * (t : ℂ))⁻¹ * (cexp (I * l * t) * g l - g l)) hGm hGb φ := by
  rw [genDiffQuot_apply, ← spectralCalculus_char U_grp t, ← ContinuousLinearMap.mul_apply,
    spectralCalculus_mul U_grp g (fun l => cexp (I * l * t)) hm hb (char_measurable t)
      (char_bdd t) ((char_measurable t).mul hm) (bounded_mul (char_bdd t) hb),
    ← ContinuousLinearMap.sub_apply,
    ← spectralCalculus_sub U_grp (fun l => cexp (I * l * t) * g l) g
      ((char_measurable t).mul hm) (bounded_mul (char_bdd t) hb) hm hb
      (((char_measurable t).mul hm).sub hm)
      (bounded_sub (bounded_mul (char_bdd t) hb) hb),
    ← ContinuousLinearMap.smul_apply,
    ← spectralCalculus_smul U_grp ((I * (t : ℂ))⁻¹) (fun l => cexp (I * l * t) * g l - g l)
      (((char_measurable t).mul hm).sub hm) (bounded_sub (bounded_mul (char_bdd t) hb) hb)
      hGm hGb]

/-! ## The generator on spectrally bounded vectors -/

/-- **The convergence engine**: the difference quotient of `Φ(g)φ` converges to
`Φ(λ·g(λ))φ` along `𝓝[≠] 0`.  One application of `tendsto_spectralCalculus_apply`. -/
theorem tendsto_genDiffQuot_spectralCalculus (g : ℝ → ℂ)
    (hm : Measurable g) (hb : ∃ C, ∀ ω, ‖g ω‖ ≤ C)
    (hidm : Measurable fun l : ℝ => (l : ℂ) * g l)
    (hidb : ∃ C, ∀ ω, ‖ω * g ω‖ ≤ C) (φ : H) :
    Tendsto (genDiffQuot U_grp (spectralCalculus U_grp g hm hb φ)) (𝓝[≠] (0 : ℝ))
      (𝓝 (spectralCalculus U_grp (fun l => (l : ℂ) * g l) hidm hidb φ)) := by
  obtain ⟨Cg, hCg⟩ := id hidb
  have hconv := tendsto_spectralCalculus_apply U_grp
    (G := fun t l => (I * (t : ℝ))⁻¹ * (cexp (I * l * t) * g l - g l))
    (g := fun l => (l : ℂ) * g l)
    (fun t => genDiffQuot_symbol_measurable g hm t)
    (fun t => genDiffQuot_symbol_bdd g hCg t)
    hidm hidb
    (C := 2 * Cg) (fun t lam => norm_genDiffQuot_symbol_le g hCg t lam)
    (fun lam => tendsto_genDiffQuot_symbol g lam) φ
  exact hconv.congr fun t =>
    (genDiffQuot_spectralCalculus U_grp g hm hb φ t
      (genDiffQuot_symbol_measurable g hm t) (genDiffQuot_symbol_bdd g hCg t)).symm

/-- **Spectrally bounded vectors lie in the generator's domain.** -/
theorem spectralCalculus_mem_generatorDomain (g : ℝ → ℂ)
    (hm : Measurable g) (hb : ∃ C, ∀ ω, ‖g ω‖ ≤ C)
    (hidm : Measurable fun l : ℝ => (l : ℂ) * g l)
    (hidb : ∃ C, ∀ ω, ‖ω * g ω‖ ≤ C) (φ : H) :
    spectralCalculus U_grp g hm hb φ ∈ generatorDomain U_grp :=
  mem_generatorDomain.mpr
    ⟨spectralCalculus U_grp (fun l => (l : ℂ) * g l) hidm hidb φ,
      tendsto_genDiffQuot_spectralCalculus U_grp g hm hb hidm hidb φ⟩

/-- **The generator acts through the calculus**: `A (Φ(g)φ) = Φ(λ·g(λ)) φ`.
This is `"A = ∫ λ dE(λ)"` on spectrally bounded vectors. -/
theorem generator_spectralCalculus (g : ℝ → ℂ)
    (hm : Measurable g) (hb : ∃ C, ∀ ω, ‖g ω‖ ≤ C)
    (hidm : Measurable fun l : ℝ => (l : ℂ) * g l)
    (hidb : ∃ C, ∀ ω, ‖ω * g ω‖ ≤ C) (φ : H) :
    generator U_grp ⟨spectralCalculus U_grp g hm hb φ,
        spectralCalculus_mem_generatorDomain U_grp g hm hb hidm hidb φ⟩
      = spectralCalculus U_grp (fun l => (l : ℂ) * g l) hidm hidb φ :=
  tendsto_nhds_unique
    (generator_tendsto U_grp
      ⟨_, spectralCalculus_mem_generatorDomain U_grp g hm hb hidm hidb φ⟩)
    (tendsto_genDiffQuot_spectralCalculus U_grp g hm hb hidm hidb φ)

/-! ## Specialization to spectral projections -/

/-- The identity symbol cut off by a bounded set is bounded. -/
lemma id_indicator_bdd {B : Set ℝ} {R : ℝ} (hR : ∀ x ∈ B, |x| ≤ R) :
    ∃ C, ∀ ω, ‖ω * Set.indicator B (fun _ => (1 : ℂ)) ω‖ ≤ C := by
  classical
  refine ⟨max R 0, fun ω => ?_⟩
  rw [Set.indicator_apply]
  split_ifs with hω
  · rw [mul_one]
    erw [RCLike.norm_ofReal]
    exact (hR ω hω).trans (le_max_left _ _)
  · rw [mul_zero, norm_zero]
    exact le_max_right _ _

/-- The identity symbol cut off by a measurable set is measurable. -/
lemma id_indicator_measurable {B : Set ℝ} (hB : MeasurableSet B) :
    Measurable fun l : ℝ => (l : ℂ) * Set.indicator B (fun _ => (1 : ℂ)) l :=
  Complex.measurable_ofReal.mul (measurable_const.indicator hB)

/-- **Range of a bounded spectral projection lies in the generator's domain** — the
hypothesis the Dirac file needs in place of its old axioms. -/
theorem spectralProjection_mem_generatorDomain {B : Set ℝ} (hB : MeasurableSet B)
    {R : ℝ} (hR : ∀ x ∈ B, |x| ≤ R) (φ : H) :
    spectralProjection U_grp B hB φ ∈ generatorDomain U_grp :=
  spectralCalculus_mem_generatorDomain U_grp _ (measurable_const.indicator hB)
    (indicator_one_bdd B) (id_indicator_measurable hB) (id_indicator_bdd hR) φ

/-- **The generator on the range of a bounded spectral projection**:
`A (E(B)φ) = Φ(λ·1_B(λ)) φ`. -/
theorem generator_spectralProjection {B : Set ℝ} (hB : MeasurableSet B)
    {R : ℝ} (hR : ∀ x ∈ B, |x| ≤ R) (φ : H) :
    generator U_grp ⟨spectralProjection U_grp B hB φ,
        spectralProjection_mem_generatorDomain U_grp hB hR φ⟩
      = spectralCalculus U_grp (fun l => (l : ℂ) * Set.indicator B (fun _ => (1 : ℂ)) l)
          (id_indicator_measurable hB) (id_indicator_bdd hR) φ :=
  generator_spectralCalculus U_grp _ (measurable_const.indicator hB) (indicator_one_bdd B)
    (id_indicator_measurable hB) (id_indicator_bdd hR) φ

/-! ## Commutation with the generator on its full domain

The lemmas above act on *spectrally bounded* vectors `Φ(g)φ` (requiring `λ·g` bounded).
The complementary fact — for ANY bounded symbol `g`, the operator `Φ(g)` maps the
generator's domain into itself and commutes with the generator there — needs no growth
condition on `λ·g` at all.  This mirrors `generator_domain_invariant` (the `U(s)` case),
with the group-commutation `Φ(g) U(t) = U(t) Φ(g)` supplied by
`spectralCalculus_char` + `spectralCalculus_comm`.  It is the ingredient that lets the
resolvent argument approximate an arbitrary domain vector by its truncations
`E([−N,N])ψ`. -/

/-- `Φ(g)` commutes with the group: `Φ(g) (U(t) x) = U(t) (Φ(g) x)`. -/
lemma spectralCalculus_group_comm (g : ℝ → ℂ) (hm : Measurable g)
    (hb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (t : ℝ) (x : H) :
    spectralCalculus U_grp g hm hb (U_grp.U t x)
      = U_grp.U t (spectralCalculus U_grp g hm hb x) := by
  have hop : spectralCalculus U_grp g hm hb * U_grp.U t
      = U_grp.U t * spectralCalculus U_grp g hm hb := by
    rw [← spectralCalculus_char U_grp t]
    exact spectralCalculus_comm U_grp _ g (char_measurable t) (char_bdd t) hm hb
  have h := congrArg (fun A : H →L[ℂ] H => A x) hop
  simpa only [ContinuousLinearMap.mul_apply] using h

/-- `Φ(g)` commutes with the difference quotient. -/
lemma genDiffQuot_spectralCalculus_comm (g : ℝ → ℂ) (hm : Measurable g)
    (hb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (x : H) :
    genDiffQuot U_grp (spectralCalculus U_grp g hm hb x)
      = fun t => spectralCalculus U_grp g hm hb (genDiffQuot U_grp x t) := by
  funext t
  simp only [genDiffQuot_apply, map_smul, map_sub]
  rw [spectralCalculus_group_comm U_grp g hm hb t x]

/-- The convergence engine for commutation: `genDiffQuot (Φ(g)x) → Φ(g)(Ax)` for
`x ∈ D(A)`, by continuity of `Φ(g)`. -/
lemma tendsto_genDiffQuot_spectralCalculus_comm (g : ℝ → ℂ) (hm : Measurable g)
    (hb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (x : (generator U_grp).domain) :
    Tendsto (genDiffQuot U_grp (spectralCalculus U_grp g hm hb (x : H))) (𝓝[≠] (0 : ℝ))
      (𝓝 (spectralCalculus U_grp g hm hb (generator U_grp x))) := by
  rw [genDiffQuot_spectralCalculus_comm]
  exact ((spectralCalculus U_grp g hm hb).continuous.tendsto _).comp
    (generator_tendsto U_grp x)

/-- **`Φ(g)` preserves the generator's domain** — any bounded measurable `g`, no growth
condition. -/
theorem spectralCalculus_mem_generatorDomain_of_mem (g : ℝ → ℂ) (hm : Measurable g)
    (hb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (x : (generator U_grp).domain) :
    spectralCalculus U_grp g hm hb (x : H) ∈ generatorDomain U_grp :=
  mem_generatorDomain.mpr ⟨spectralCalculus U_grp g hm hb (generator U_grp x),
    tendsto_genDiffQuot_spectralCalculus_comm U_grp g hm hb x⟩

/-- **`Φ(g)` commutes with the generator on its domain**: `A (Φ(g)x) = Φ(g) (Ax)`. -/
theorem generator_spectralCalculus_comm (g : ℝ → ℂ) (hm : Measurable g)
    (hb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (x : (generator U_grp).domain) :
    generator U_grp ⟨spectralCalculus U_grp g hm hb (x : H),
        spectralCalculus_mem_generatorDomain_of_mem U_grp g hm hb x⟩
      = spectralCalculus U_grp g hm hb (generator U_grp x) :=
  tendsto_nhds_unique
    (generator_tendsto U_grp ⟨_, spectralCalculus_mem_generatorDomain_of_mem U_grp g hm hb x⟩)
    (tendsto_genDiffQuot_spectralCalculus_comm U_grp g hm hb x)

/-- Specialization: `E(B)` preserves the generator's domain — any measurable `B`,
bounded or not. -/
theorem spectralProjection_mem_generatorDomain_of_mem {B : Set ℝ} (hB : MeasurableSet B)
    (x : (generator U_grp).domain) :
    spectralProjection U_grp B hB (x : H) ∈ generatorDomain U_grp :=
  spectralCalculus_mem_generatorDomain_of_mem U_grp _
    (measurable_const.indicator hB) (indicator_one_bdd B) x

/-- Specialization: `A (E(B)x) = E(B) (Ax)` on the domain. -/
theorem generator_spectralProjection_comm {B : Set ℝ} (hB : MeasurableSet B)
    (x : (generator U_grp).domain) :
    generator U_grp ⟨spectralProjection U_grp B hB (x : H),
        spectralProjection_mem_generatorDomain_of_mem U_grp hB x⟩
      = spectralProjection U_grp B hB (generator U_grp x) :=
  generator_spectralCalculus_comm U_grp _
    (measurable_const.indicator hB) (indicator_one_bdd B) x

end Spectra.QuantumMechanics.SpectralTheory
