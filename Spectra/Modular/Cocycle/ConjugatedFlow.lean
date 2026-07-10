/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.Cocycle.ModularConjugationInvolutive
import Spectra.Modular.Cocycle.ModularHamiltonian
import Spectra.SpectralTheory.Measure.Convergence
/-!
# The conjugated flow: `J Δ^{it} = Δ^{it} J`  (ladder T6a — the flow-commutation engine)

This file is an **engine for the base-`M` Tomita theorem build** (fields 6/7/8 of `ModularData`
— see the vault plan): it proves the flow-commutation identity

> `J Δ^{it} = Δ^{it} J`  (`modularConjugation_comm_modularFlow`),

which classically is only available *inside* the polar-decomposition machinery; here the banked
`J`-package (`J² = 1`, `⟪Ju, Jv⟫ = ⟪v, u⟫`, `J Δ J⁻¹ = Δ⁻¹`) unlocks it up front.  It gates the
KMS co-target and collapses every downstream `J`-flip.

## The six-rung ladder

1. `modularConjGroup` — for a one-parameter unitary group `W`, the conjugated group
   `t ↦ J W(−t) J⁻¹`.  **Sign conventions**: `J` is *antilinear*, so conjugation flips `i ↦ −i`
   in the generator's difference quotient; the built-in time flip `t ↦ −t` flips it back.  Net
   effect: `generator (J W(−t) J⁻¹) = J (generator W) J⁻¹` with **no** sign.
2. `generator_modularConjGroup` — that generator transport, proved from the difference-quotient
   *definition* of the generator (`genDiffQuot (conj) z t = J (genDiffQuot W (J⁻¹z) (−t))`,
   antilinearity and the time flip cancelling), plus maximality of self-adjoint operators.
3. `modularConjGroup_genToGroup_modularOp` — **`J e^{−isΔ} J⁻¹ = e^{isΔ⁻¹}`** as groups:
   the conjugate of `e^{isΔ}` has generator `J Δ J⁻¹ = Δ⁻¹` (`conjModularOp_eq_modularOpInv`),
   and a group is determined by its generator (`group_unique`).
4. `flowGroup` (generic, `Spectra.QuantumMechanics.SpectralTheory`) — the spectral flow
   `t ↦ Φ_U(e^{itφ})` of a *real* symbol `φ`, packaged as a one-parameter unitary group, with
   `generator_flowGroup : generator (flowGroup U φ) = ∫ φ dE_U` (the `FlowGenerator` engine at
   `hflow := rfl`).  Instantiated at `φ = 1/s`: `genToGroup Δ⁻¹ = flowGroup U_Δ (1/s)`
   (`genToGroup_modularOpInv_eq_flowGroup`), i.e. `e^{itΔ⁻¹} = Φ_{U_Δ}(exp(it/s))`.
5. `borelMeasure_modularConjugation_eq_map` — the **measure pushforward**
   `μ_{Jξ} = (s ↦ s⁻¹)_* μ_ξ` for the Bochner–Herglotz measures of `U_Δ = e^{isΔ}`: rungs 3+4
   compute the characteristic function of `μ_{Jξ}` (the antiunitary flip conjugates it, the
   time flip un-conjugates it), and `borelMeasure_flowSymbol_eq_map` + `Measure.ext_of_charFun`
   identify the measure.
6. `modularConjugation_comm_modularFlow` — the headline.  `Δ^{it} = Φ_{U_Δ}(exp(it·log s))`
   (`modularFlow_U_eq_spectralCalculus`), so the diagonal of `J Δ^{it} J⁻¹` is
   `conj ∫ e^{it log s} dμ_{Jξ} = ∫ e^{−it log s} d((1/s)_*μ_ξ) = ∫ e^{it log s} dμ_ξ`
   (rung 5 + `Real.log_inv`, the conjugation flip and the `s ↦ 1/s` flip cancelling), which is
   the diagonal of `Δ^{it}`; polarization (`op_ext_of_inner_self`) finishes.

The junk values are aligned throughout: `Real.log_inv` holds for **all** reals (`log 0 = 0`,
`0⁻¹ = 0`), so the rung-6 symbol identity `exp(i(−t)·log(s⁻¹)) = exp(it·log s)` needs no
support hypothesis.
-/

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace
open Spectra.QuantumMechanics.SpectralTheory
open Spectra.OneParameterUnitaryGroup
open Spectra.YosidaHille
open Spectra.Borel
open Spectra.Borel.SpectralMeasure
open Spectra.Resolvent

namespace Spectra.QuantumMechanics.SpectralTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : OneParameterUnitaryGroup (H := H)) (f : ℝ → ℂ)

/-! ## Rung 4 (generic): the spectral flow of a real symbol as a one-parameter unitary group

`FlowGenerator.lean` computes the generator of any group whose action is `Φ_U(exp(itφ))`; this
section supplies the missing *existence* half: the spectral exponentials of a real symbol `φ`
genuinely form a strongly continuous one-parameter unitary group (`flowGroup`), so that
`genToGroup (∫ φ dE_U) = flowGroup U φ` by uniqueness. -/

/-- The flow symbol at `t = 0` is the constant `1`. -/
lemma flowSymbol_zero : flowSymbol f 0 = fun _ => (1 : ℂ) := funext fun s => by
  simp [flowSymbol]

/-- The flow symbols are multiplicative in the parameter: `e^{i(s+t)φ} = e^{isφ} · e^{itφ}`. -/
lemma flowSymbol_add (s t x : ℝ) :
    flowSymbol f (s + t) x = flowSymbol f s x * flowSymbol f t x := by
  simp only [flowSymbol, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- For a real symbol, conjugation reverses the parameter: `conj e^{itφ} = e^{i(−t)φ}`. -/
lemma conj_flowSymbol (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s) (t x : ℝ) :
    (starRingEnd ℂ) (flowSymbol f t x) = flowSymbol f (-t) x := by
  simp only [flowSymbol, ← Complex.exp_conj]
  congr 1
  rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, hconj x]
  push_cast
  ring

/-- For a real symbol the flow symbol is unimodular: `‖e^{itφ(x)}‖ ≤ 1`, pointwise form. -/
lemma norm_flowSymbol_le_one (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s) (t x : ℝ) :
    ‖flowSymbol f t x‖ ≤ 1 := by
  have him0 : (f x).im = 0 := Complex.conj_eq_iff_im.mp (hconj x)
  have hre : (I * (t : ℂ) * f x).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, him0]
  rw [flowSymbol, norm_exp, hre, Real.exp_zero]

/-- The reversed flow symbol is the pointwise inverse: `e^{i(−t)φ} · e^{itφ} = 1`. -/
lemma flowSymbol_neg_mul_self (t x : ℝ) :
    flowSymbol f (-t) x * flowSymbol f t x = 1 := by
  rw [← flowSymbol_add f (-t) t x, neg_add_cancel]
  exact congrFun (flowSymbol_zero f) x

/-- **The spectral flow of a real symbol, as a one-parameter unitary group**:
`(flowGroup U φ).U t = Φ_U(exp(itφ))`.  Group law and unitarity are the symbol algebra of the
bounded calculus (`Φ` is multiplicative and a `*`-map); strong continuity is dominated
convergence in the `L²(μ_ξ)` identity (`tendsto_spectralCalculus_apply`). -/
noncomputable def flowGroup (hf : Measurable f)
    (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s) : OneParameterUnitaryGroup (H := H) where
  U t := spectralCalculus U (flowSymbol f t) (measurable_flowSymbol f hf t)
    (flowSymbol_bdd f hconj t)
  unitary t ψ φ := by
    have hcfun : (fun l => (starRingEnd ℂ) (flowSymbol f t l)) = flowSymbol f (-t) :=
      funext fun x => conj_flowSymbol f hconj t x
    have hcm : Measurable fun l => (starRingEnd ℂ) (flowSymbol f t l) := by
      rw [hcfun]; exact measurable_flowSymbol f hf (-t)
    have hcb : ∃ C, ∀ ω, ‖(starRingEnd ℂ) (flowSymbol f t ω)‖ ≤ C :=
      ⟨1, fun ω => by
        rw [conj_flowSymbol f hconj t ω]; exact norm_flowSymbol_le_one f hconj (-t) ω⟩
    have hadj : ContinuousLinearMap.adjoint
        (spectralCalculus U (flowSymbol f t) (measurable_flowSymbol f hf t)
          (flowSymbol_bdd f hconj t))
        = spectralCalculus U (flowSymbol f (-t)) (measurable_flowSymbol f hf (-t))
          (flowSymbol_bdd f hconj (-t)) :=
      (spectralCalculus_adjoint U (flowSymbol f t) (measurable_flowSymbol f hf t)
        (flowSymbol_bdd f hconj t) hcm hcb).trans
        (spectralCalculus_congr U hcfun hcm hcb (measurable_flowSymbol f hf (-t))
          (flowSymbol_bdd f hconj (-t)))
    have hUU : spectralCalculus U (flowSymbol f (-t)) (measurable_flowSymbol f hf (-t))
          (flowSymbol_bdd f hconj (-t))
        * spectralCalculus U (flowSymbol f t) (measurable_flowSymbol f hf t)
          (flowSymbol_bdd f hconj t) = ContinuousLinearMap.id ℂ H := by
      rw [spectralCalculus_mul U (flowSymbol f t) (flowSymbol f (-t))
          (measurable_flowSymbol f hf t) (flowSymbol_bdd f hconj t)
          (measurable_flowSymbol f hf (-t)) (flowSymbol_bdd f hconj (-t))
          ((measurable_flowSymbol f hf (-t)).mul (measurable_flowSymbol f hf t))
          (bounded_mul (flowSymbol_bdd f hconj (-t)) (flowSymbol_bdd f hconj t)),
        spectralCalculus_congr U (funext fun x => flowSymbol_neg_mul_self f t x)
          ((measurable_flowSymbol f hf (-t)).mul (measurable_flowSymbol f hf t))
          (bounded_mul (flowSymbol_bdd f hconj (-t)) (flowSymbol_bdd f hconj t))
          measurable_const ⟨1, fun _ => norm_one.le⟩,
        spectralCalculus_one]
    have h1 := (ContinuousLinearMap.adjoint_inner_right
      (spectralCalculus U (flowSymbol f t) (measurable_flowSymbol f hf t)
        (flowSymbol_bdd f hconj t)) ψ
      (spectralCalculus U (flowSymbol f t) (measurable_flowSymbol f hf t)
        (flowSymbol_bdd f hconj t) φ)).symm
    have h2 := congrArg (fun T : H →L[ℂ] H => T φ) hUU
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.id_apply] at h2
    rw [h1, hadj, h2]
  group_law s t :=
    (spectralCalculus_congr U (funext fun x => flowSymbol_add f s t x)
      (measurable_flowSymbol f hf (s + t)) (flowSymbol_bdd f hconj (s + t))
      ((measurable_flowSymbol f hf s).mul (measurable_flowSymbol f hf t))
      (bounded_mul (flowSymbol_bdd f hconj s) (flowSymbol_bdd f hconj t))).trans
      (spectralCalculus_mul U (flowSymbol f t) (flowSymbol f s)
        (measurable_flowSymbol f hf t) (flowSymbol_bdd f hconj t)
        (measurable_flowSymbol f hf s) (flowSymbol_bdd f hconj s)
        ((measurable_flowSymbol f hf s).mul (measurable_flowSymbol f hf t))
        (bounded_mul (flowSymbol_bdd f hconj s) (flowSymbol_bdd f hconj t))).symm
  identity :=
    (spectralCalculus_congr U (flowSymbol_zero f) (measurable_flowSymbol f hf 0)
      (flowSymbol_bdd f hconj 0) measurable_const ⟨1, fun _ => norm_one.le⟩).trans
      (spectralCalculus_one U)
  strong_continuous ψ := by
    refine continuous_iff_continuousAt.mpr fun t₀ => ?_
    have hlim : ∀ x : ℝ, Tendsto (fun τ : ℝ => flowSymbol f τ x) (𝓝 t₀)
        (𝓝 (flowSymbol f t₀ x)) := fun x =>
      ((Complex.continuous_exp.comp
        ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)).tendsto t₀)
    exact tendsto_spectralCalculus_apply U (fun τ => measurable_flowSymbol f hf τ)
      (fun τ => flowSymbol_bdd f hconj τ) (measurable_flowSymbol f hf t₀)
      (flowSymbol_bdd f hconj t₀) (fun τ x => norm_flowSymbol_le_one f hconj τ x) hlim ψ

/-- The action of the flow group is the spectral calculus of the flow symbol (definitional). -/
@[simp] lemma flowGroup_U (hf : Measurable f) (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s)
    (t : ℝ) :
    (flowGroup U f hf hconj).U t = spectralCalculus U (flowSymbol f t)
      (measurable_flowSymbol f hf t) (flowSymbol_bdd f hconj t) := rfl

/-- **The generator of the flow group is the unbounded calculus of its symbol**:
`generator (flowGroup U φ) = ∫ φ dE_U`.  The `FlowGenerator` engine at `hflow := rfl`. -/
theorem generator_flowGroup (hf : Measurable f) (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s)
    (hdense : Dense ((pmapOfPVM U f hf).domain : Set H)) :
    generator (flowGroup U f hf hconj) = pmapOfPVM U f hf :=
  generator_eq_pmapOfPVM_of_flowSymbol f U (flowGroup U f hf hconj) hf hconj hdense
    fun _ => rfl

/-- **Stone's group of a real unbounded calculus is its spectral flow**:
`e^{it·∫φdE_U} = Φ_U(exp(itφ))`, by `group_unique` on `generator_flowGroup`. -/
theorem genToGroup_pmapOfPVM_real_eq_flowGroup (hf : Measurable f)
    (hconj : ∀ s, (starRingEnd ℂ) (f s) = f s)
    (hdense : Dense ((pmapOfPVM U f hf).domain : Set H)) :
    genToGroup (pmapOfPVM_isSelfAdjoint_of_real U f hf hconj hdense)
      = flowGroup U f hf hconj :=
  group_unique _ _ (by rw [generator_genToGroup, generator_flowGroup U f hf hconj hdense])

end Spectra.QuantumMechanics.SpectralTheory

namespace Spectra.TomitaTakesaki

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}
variable (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)

/-! ## Rung 1: the conjugated group `t ↦ J W(−t) J⁻¹`

Defined for the concrete `J := modularConjugation` (whose antiunitary inner identity and
involutivity are banked), avoiding generic-antiunitary plumbing.  The time flip is what makes
the *group law* come out right for an antilinear conjugation — and it cancels the antilinear
`i`-flip in the generator, giving `generator = J (generator W) J⁻¹` with no sign. -/

/-- **The `J`-conjugated group** `(modularConjGroup W).U t = J W(−t) J⁻¹`.  Unitarity is the
antiunitary inner flip applied twice; the group law uses only `J⁻¹ J = 1`. -/
noncomputable def modularConjGroup (W : OneParameterUnitaryGroup (H := H)) :
    OneParameterUnitaryGroup (H := H) where
  U t := jConj (modularConjugation hcyc hsep) (W.U (-t))
  unitary t ψ φ := by
    simp only [jConj_apply]
    rw [inner_modularConjugation hcyc hsep, W.unitary, modularConjugation_symm_eq hcyc hsep]
    exact inner_modularConjugation hcyc hsep φ ψ
  group_law s t := ContinuousLinearMap.ext fun ψ => by
    simp only [jConj_apply, ContinuousLinearMap.comp_apply,
      LinearIsometryEquiv.symm_apply_apply]
    rw [neg_add, W.group_law, ContinuousLinearMap.comp_apply]
  identity := ContinuousLinearMap.ext fun ψ => by
    simp only [jConj_apply, neg_zero, W.identity, ContinuousLinearMap.id_apply,
      LinearIsometryEquiv.apply_symm_apply]
  strong_continuous ψ := by
    simp only [jConj_apply]
    exact (modularConjugation hcyc hsep).continuous.comp
      ((W.strong_continuous _).comp continuous_neg)

/-- The action of the conjugated group (definitional). -/
@[simp] lemma modularConjGroup_U (W : OneParameterUnitaryGroup (H := H)) (t : ℝ) :
    (modularConjGroup hcyc hsep W).U t
      = jConj (modularConjugation hcyc hsep) (W.U (-t)) := rfl

/-! ## Rung 2: generator transport `generator (J W(−t) J⁻¹) = J (generator W) J⁻¹` -/

/-- Negation preserves the punctured neighbourhood filter of `0`. -/
private lemma tendsto_neg_punctured :
    Tendsto (fun t : ℝ => -t) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simpa using ht

/-- **The difference-quotient transport**: the antilinear `J` flips the `i` in the quotient
`(V(t)z − z)/(it)`, and the built-in time flip `t ↦ −t` flips it back:
`genDiffQuot (modularConjGroup W) z t = J (genDiffQuot W (J⁻¹z) (−t))`. -/
private lemma modularConjGroup_genDiffQuot (W : OneParameterUnitaryGroup (H := H))
    (z : H) (t : ℝ) :
    genDiffQuot (modularConjGroup hcyc hsep W) z t
      = modularConjugation hcyc hsep
          (genDiffQuot W ((modularConjugation hcyc hsep).symm z) (-t)) := by
  simp only [genDiffQuot_apply, modularConjGroup_U, jConj_apply]
  rw [map_smulₛₗ, map_sub, (modularConjugation hcyc hsep).apply_symm_apply]
  congr 1
  rw [map_inv₀]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- **Rung 2 — generator transport through the antiunitary conjugation**:
`generator (modularConjGroup W) = conjPMap J (generator W)`, i.e. `J (generator W) J⁻¹`.
Proof: on `J(D(generator W))` the transported difference quotient converges to the transported
value (`⊆`), and both operators are self-adjoint (`conjPMap_isSelfAdjoint` for the left,
Stone's theorem for the right), so maximality (`IsSelfAdjoint.eq_of_le`) upgrades `⊆` to `=`. -/
theorem generator_modularConjGroup (W : OneParameterUnitaryGroup (H := H)) :
    generator (modularConjGroup hcyc hsep W)
      = conjPMap (modularConjugation hcyc hsep) (generator W) := by
  have hkey : ∀ (z : H) (hz : (modularConjugation hcyc hsep).symm z ∈ (generator W).domain),
      Tendsto (genDiffQuot (modularConjGroup hcyc hsep W) z) (𝓝[≠] (0 : ℝ))
        (𝓝 (modularConjugation hcyc hsep
          (generator W ⟨(modularConjugation hcyc hsep).symm z, hz⟩))) := by
    intro z hz
    have hbase :
        Tendsto (fun t : ℝ => genDiffQuot W ((modularConjugation hcyc hsep).symm z) (-t))
          (𝓝[≠] (0 : ℝ))
          (𝓝 (generator W ⟨(modularConjugation hcyc hsep).symm z, hz⟩)) :=
      (generator_tendsto W ⟨(modularConjugation hcyc hsep).symm z, hz⟩).comp
        tendsto_neg_punctured
    have hJ := ((modularConjugation hcyc hsep).continuous.tendsto _).comp hbase
    exact hJ.congr fun t => (modularConjGroup_genDiffQuot hcyc hsep W z t).symm
  have hle : conjPMap (modularConjugation hcyc hsep) (generator W)
      ≤ generator (modularConjGroup hcyc hsep W) := by
    refine ⟨fun z hz => ?_, fun x y hxy => ?_⟩
    · rw [generator_domain, mem_generatorDomain]
      exact ⟨_, hkey z hz⟩
    · rw [conjPMap_apply]
      have h1 := hkey (x : H) x.2
      have h2 : genDiffQuot (modularConjGroup hcyc hsep W) (x : H)
          = genDiffQuot (modularConjGroup hcyc hsep W) (y : H) := by rw [hxy]
      rw [h2] at h1
      exact tendsto_nhds_unique h1 (generator_tendsto (modularConjGroup hcyc hsep W) y)
  exact (IsSelfAdjoint.eq_of_le
    (conjPMap_isSelfAdjoint (inner_modularConjugation hcyc hsep) (generator_isSelfAdjoint W))
    (generator_isSelfAdjoint (modularConjGroup hcyc hsep W)) hle).symm

/-! ## Rung 3: `J e^{−isΔ} J⁻¹ = e^{isΔ⁻¹}` -/

/-- **Rung 3 — the conjugate of `Δ`'s Stone group is `Δ⁻¹`'s Stone group**:
`modularConjGroup (e^{isΔ}) = e^{isΔ⁻¹}`.  Generator transport (rung 2) turns the left side's
generator into `J Δ J⁻¹ = Δ⁻¹` (`conjModularOp_eq_modularOpInv`), and a one-parameter unitary
group is determined by its generator (`group_unique`). -/
theorem modularConjGroup_genToGroup_modularOp :
    modularConjGroup hcyc hsep (genToGroup (modularOp_isSelfAdjoint hcyc hsep))
      = genToGroup (modularOpInv_isSelfAdjoint hcyc hsep) := by
  refine group_unique _ _ ?_
  rw [generator_modularConjGroup, generator_genToGroup, generator_genToGroup]
  exact conjModularOp_eq_modularOpInv hcyc hsep

/-- **Rung 3, pointwise**: `e^{itΔ}(Jξ) = J(e^{−itΔ⁻¹}ξ)` — the form the measure argument
consumes. -/
theorem genToGroup_modularOp_U_conjugation (t : ℝ) (ξ : H) :
    (genToGroup (modularOp_isSelfAdjoint hcyc hsep)).U t (modularConjugation hcyc hsep ξ)
      = modularConjugation hcyc hsep
          ((genToGroup (modularOpInv_isSelfAdjoint hcyc hsep)).U (-t) ξ) := by
  rw [← modularConjGroup_genToGroup_modularOp hcyc hsep, modularConjGroup_U, neg_neg,
    jConj_apply, modularConjugation_involutive, modularConjugation_symm_eq]

/-! ## Rung 4 (modular instance): `e^{itΔ⁻¹} = Φ_{U_Δ}(exp(it/s))` -/

/-- **Rung 4 — the `Δ⁻¹`-group is a spectral flow on `Δ`'s own group**:
`genToGroup Δ⁻¹ = flowGroup U_Δ (1/s)`, since `Δ⁻¹ = pmapOfPVM U_Δ (1/s)` by definition and
generators determine groups. -/
theorem genToGroup_modularOpInv_eq_flowGroup :
    genToGroup (modularOpInv_isSelfAdjoint hcyc hsep)
      = flowGroup (genToGroup (modularOp_isSelfAdjoint hcyc hsep)) (fun s => ((s : ℂ))⁻¹)
          measurable_invC conj_invC := by
  refine group_unique _ _ ?_
  rw [generator_genToGroup,
    generator_flowGroup (genToGroup (modularOp_isSelfAdjoint hcyc hsep))
      (fun s => ((s : ℂ))⁻¹) measurable_invC conj_invC (modularOpInv_domain_dense hcyc hsep)]
  rfl

/-! ## Rung 5: the measure pushforward `μ_{Jξ} = (s ↦ s⁻¹)_* μ_ξ` -/

/-- `μ_{Jξ} = μ^{Δ⁻¹-group}_ξ`: matching characteristic functions.  For each `t`,
`⟪Jξ, e^{itΔ}(Jξ)⟫ = ⟪Jξ, J(e^{−itΔ⁻¹}ξ)⟫ = ⟪e^{−itΔ⁻¹}ξ, ξ⟫ = conj ⟪ξ, e^{−itΔ⁻¹}ξ⟫`
(rung 3 + the antiunitary inner flip), and conjugating the Fourier transform of a positive
measure at `−t` gives its value at `t`. -/
private lemma borelMeasure_modularConjugation_eq_invGroup (ξ : H) :
    borelMeasure (genToGroup (modularOp_isSelfAdjoint hcyc hsep))
        (modularConjugation hcyc hsep ξ)
      = borelMeasure (genToGroup (modularOpInv_isSelfAdjoint hcyc hsep)) ξ := by
  haveI := borelMeasure_isFiniteMeasure (genToGroup (modularOp_isSelfAdjoint hcyc hsep))
    (modularConjugation hcyc hsep ξ)
  haveI := borelMeasure_isFiniteMeasure (genToGroup (modularOpInv_isSelfAdjoint hcyc hsep)) ξ
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have hL : charFun (borelMeasure (genToGroup (modularOp_isSelfAdjoint hcyc hsep))
      (modularConjugation hcyc hsep ξ)) t
      = ⟪modularConjugation hcyc hsep ξ,
          (genToGroup (modularOp_isSelfAdjoint hcyc hsep)).U t
            (modularConjugation hcyc hsep ξ)⟫_ℂ := by
    rw [charFun_apply_real, borelMeasure_fourier]
    exact integral_congr_ae (Eventually.of_forall fun l => by ring_nf)
  have hmid : ⟪modularConjugation hcyc hsep ξ,
      (genToGroup (modularOp_isSelfAdjoint hcyc hsep)).U t
        (modularConjugation hcyc hsep ξ)⟫_ℂ
      = (starRingEnd ℂ)
          ⟪ξ, (genToGroup (modularOpInv_isSelfAdjoint hcyc hsep)).U (-t) ξ⟫_ℂ := by
    rw [genToGroup_modularOp_U_conjugation hcyc hsep t ξ,
      inner_modularConjugation hcyc hsep]
    exact (inner_conj_symm _ _).symm
  have hR : charFun (borelMeasure (genToGroup (modularOpInv_isSelfAdjoint hcyc hsep)) ξ) t
      = (starRingEnd ℂ)
          ⟪ξ, (genToGroup (modularOpInv_isSelfAdjoint hcyc hsep)).U (-t) ξ⟫_ℂ := by
    rw [charFun_apply_real, borelMeasure_fourier _ ξ (-t), ← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun l => ?_)
    beta_reduce
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [hL, hmid, ← hR]

/-- **Rung 5 — the antiunitary pushes the modular spectral measure through `s ↦ s⁻¹`**:
`borelMeasure U_Δ (Jξ) = (s ↦ s⁻¹)_* (borelMeasure U_Δ ξ)`.  Chain: `μ_{Jξ} = μ^{Δ⁻¹-grp}_ξ`
(characteristic functions, via rung 3) and `μ^{Δ⁻¹-grp}_ξ = (1/s)_* μ_ξ`
(`borelMeasure_flowSymbol_eq_map`, via rung 4). -/
theorem borelMeasure_modularConjugation_eq_map (ξ : H) :
    borelMeasure (genToGroup (modularOp_isSelfAdjoint hcyc hsep))
        (modularConjugation hcyc hsep ξ)
      = Measure.map (fun s : ℝ => s⁻¹)
          (borelMeasure (genToGroup (modularOp_isSelfAdjoint hcyc hsep)) ξ) := by
  have hflow : ∀ t : ℝ, (genToGroup (modularOpInv_isSelfAdjoint hcyc hsep)).U t
      = spectralCalculus (genToGroup (modularOp_isSelfAdjoint hcyc hsep))
          (flowSymbol (fun s => ((s : ℂ))⁻¹) t)
          (measurable_flowSymbol _ measurable_invC t) (flowSymbol_bdd _ conj_invC t) := by
    intro t
    rw [genToGroup_modularOpInv_eq_flowGroup hcyc hsep]
    rfl
  have hA : borelMeasure (genToGroup (modularOpInv_isSelfAdjoint hcyc hsep)) ξ
      = Measure.map (fun s : ℝ => (((s : ℂ))⁻¹).re)
          (borelMeasure (genToGroup (modularOp_isSelfAdjoint hcyc hsep)) ξ) :=
    borelMeasure_flowSymbol_eq_map (fun s => ((s : ℂ))⁻¹)
      (genToGroup (modularOp_isSelfAdjoint hcyc hsep))
      (genToGroup (modularOpInv_isSelfAdjoint hcyc hsep)) measurable_invC conj_invC hflow ξ
  have hre : (fun s : ℝ => (((s : ℂ))⁻¹).re) = fun s : ℝ => s⁻¹ :=
    funext fun s => by rw [← Complex.ofReal_inv, Complex.ofReal_re]
  rw [borelMeasure_modularConjugation_eq_invGroup hcyc hsep ξ, hA, hre]

/-! ## Rung 6: the headline `J Δ^{it} = Δ^{it} J` -/

/-- `conj (e^{it·log s}) = e^{i(−t)·log s}` — the conjugation flip on the modular symbol. -/
private lemma conj_logExpSym (t s : ℝ) :
    (starRingEnd ℂ) (logExpSym t s) = logExpSym (-t) s := by
  simp only [logExpSym, ← Complex.exp_conj]
  congr 1
  rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
  push_cast
  ring

/-- `e^{i(−t)·log(s⁻¹)} = e^{it·log s}` — junk-aligned for **all** `s` (`Real.log_inv` holds
unconditionally, `log 0 = 0` and `0⁻¹ = 0`). -/
private lemma logExpSym_neg_inv (t s : ℝ) : logExpSym (-t) s⁻¹ = logExpSym t s := by
  simp only [logExpSym, Real.log_inv]
  congr 1
  push_cast
  ring

/-- **The modular conjugation commutes with the modular flow, operator form**:
`J Δ^{it} J⁻¹ = Δ^{it}`.  Diagonal matrix elements: the antiunitary flip conjugates the
spectral integral and moves it to `μ_{Jξ}`; rung 5 pushes `μ_{Jξ}` forward through `s ↦ s⁻¹`;
and `conj ∘ (s ↦ s⁻¹)` fixes the symbol `e^{it·log s}` (`Real.log_inv`).  Polarization
(`op_ext_of_inner_self`) upgrades the diagonal identity to the operator identity. -/
theorem jConj_modularFlow [Nontrivial H] (t : ℝ) :
    jConj (modularConjugation hcyc hsep) ((modularFlow hcyc hsep).U t)
      = (modularFlow hcyc hsep).U t := by
  have hint : ∀ η : H, ⟪η, (modularFlow hcyc hsep).U t η⟫_ℂ
      = ∫ s, logExpSym t s
          ∂(borelMeasure (genToGroup (modularOp_isSelfAdjoint hcyc hsep)) η) := fun η => by
    rw [modularFlow_U_eq_spectralCalculus hcyc hsep t,
      inner_spectralCalculus _ (logExpSym t) (measurable_logExpSym t) (logExpSym_bdd t) η η,
      spectralForm_self _ η (measurable_logExpSym t) (logExpSym_bdd t)]
  refine op_ext_of_inner_self fun ζ => ?_
  rw [jConj_apply, modularConjugation_symm_eq]
  have hflip : ⟪ζ, modularConjugation hcyc hsep
      ((modularFlow hcyc hsep).U t (modularConjugation hcyc hsep ζ))⟫_ℂ
      = (starRingEnd ℂ) ⟪modularConjugation hcyc hsep ζ,
          (modularFlow hcyc hsep).U t (modularConjugation hcyc hsep ζ)⟫_ℂ :=
    calc ⟪ζ, modularConjugation hcyc hsep
          ((modularFlow hcyc hsep).U t (modularConjugation hcyc hsep ζ))⟫_ℂ
        = ⟪modularConjugation hcyc hsep (modularConjugation hcyc hsep ζ),
            modularConjugation hcyc hsep
              ((modularFlow hcyc hsep).U t (modularConjugation hcyc hsep ζ))⟫_ℂ := by
          rw [modularConjugation_involutive]
      _ = ⟪(modularFlow hcyc hsep).U t (modularConjugation hcyc hsep ζ),
            modularConjugation hcyc hsep ζ⟫_ℂ := inner_modularConjugation hcyc hsep _ _
      _ = (starRingEnd ℂ) ⟪modularConjugation hcyc hsep ζ,
            (modularFlow hcyc hsep).U t (modularConjugation hcyc hsep ζ)⟫_ℂ :=
          (inner_conj_symm _ _).symm
  rw [hflip, hint (modularConjugation hcyc hsep ζ), hint ζ, ← integral_conj]
  have hstep1 : ∫ s, (starRingEnd ℂ) (logExpSym t s)
      ∂(borelMeasure (genToGroup (modularOp_isSelfAdjoint hcyc hsep))
        (modularConjugation hcyc hsep ζ))
      = ∫ s, logExpSym (-t) s
        ∂(borelMeasure (genToGroup (modularOp_isSelfAdjoint hcyc hsep))
          (modularConjugation hcyc hsep ζ)) :=
    integral_congr_ae (Eventually.of_forall fun s => conj_logExpSym t s)
  have hstep2 : ∫ s, logExpSym (-t) s
      ∂(borelMeasure (genToGroup (modularOp_isSelfAdjoint hcyc hsep))
        (modularConjugation hcyc hsep ζ))
      = ∫ s, logExpSym (-t) s⁻¹
        ∂(borelMeasure (genToGroup (modularOp_isSelfAdjoint hcyc hsep)) ζ) := by
    rw [borelMeasure_modularConjugation_eq_map hcyc hsep ζ,
      integral_map measurable_inv.aemeasurable
        (measurable_logExpSym (-t)).aestronglyMeasurable]
  rw [hstep1, hstep2]
  exact integral_congr_ae (Eventually.of_forall fun s => logExpSym_neg_inv t s)

/-- ★ **`J Δ^{it} = Δ^{it} J`** — the flow-commutation identity (ladder T6a), pointwise and
unconditional (`Subsingleton H` is trivial; `Nontrivial H` is `jConj_modularFlow` read at
`Jξ` through `J² = 1`).  This is the engine the base-`M` Tomita theorem build (fields 6/7/8 of
`ModularData`) consumes. -/
theorem modularConjugation_comm_modularFlow (t : ℝ) (ξ : H) :
    modularConjugation hcyc hsep ((modularFlow hcyc hsep).U t ξ)
      = (modularFlow hcyc hsep).U t (modularConjugation hcyc hsep ξ) := by
  rcases subsingleton_or_nontrivial H with _ | _
  · exact Subsingleton.elim _ _
  · have h := congrArg (fun T : H →L[ℂ] H => T (modularConjugation hcyc hsep ξ))
      (jConj_modularFlow hcyc hsep t)
    simp only [jConj_apply] at h
    rw [modularConjugation_symm_eq, modularConjugation_involutive] at h
    exact h

end Spectra.TomitaTakesaki
