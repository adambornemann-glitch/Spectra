/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.CayleyTransform.BorelCalculus
import Spectra.OneParameterUnitaryGroup.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
/-!
# One-parameter unitary groups from the Borel functional calculus

The bounded Borel calculus `Spectra.BorelCFC.borelCalculus` of a normal operator `V` turns a
*family of unimodular symbols* `g : ℝ → spectrum ℂ V → ℂ` into a strongly continuous one-parameter
unitary group, provided the family is **multiplicative** in the parameter (`g (s+t) = g s · g t`),
**normalized** (`g 0 = 1`), and **pointwise continuous** in the parameter. Unitarity comes from
unimodularity (`‖g t z‖ = 1`), the group law from `borelCalculus_mul`, and strong continuity from
the dominated-convergence engine `tendsto_borelCalculus_apply`.

This is the spectral-order route to Stone's theorem ("spectral resolution first, group as its
corollary"): the modular flow `Δ^{it}` of Tomita–Takesaki is the instance `g t z = (λ z)^{it}`
(`λ = inverseMobius z`, the spectrum of `Δ` pulled back through the Cayley map), and ordinary
Hamiltonian evolution `e^{itA}` is the instance `g t z = exp (i t (λ z))`. Both symbol families are
unimodular, multiplicative, and continuous, so `borelUnitaryGroup` packages either into an honest
`OneParameterUnitaryGroup`.

See `Spectra/Modular/TomitaTakesaki/ROADMAP.md` (milestone R1).
-/

open Complex MeasureTheory Filter Topology InnerProductSpace
open scoped InnerProductSpace ComplexConjugate

open Spectra.Cayley

namespace Spectra.BorelCFC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The one-parameter unitary group of a unimodular, multiplicative symbol family.**

From a normal operator `V` and a parameter-family of symbols `g : ℝ → spectrum ℂ V → ℂ` that is
measurable, **unimodular** (`‖g t z‖ = 1`), **normalized** (`g 0 = 1`), **multiplicative**
(`g (s+t) = g s · g t`), and **continuous in the parameter** (`t ↦ g t z` continuous for each `z`),
the operators `t ↦ borelCalculus V hn (g t)` form a strongly continuous one-parameter unitary group
on `H`. -/
noncomputable def borelUnitaryGroup (V : H →L[ℂ] H) (hn : IsStarNormal V)
    (g : ℝ → spectrum ℂ V → ℂ)
    (hmeas : ∀ t, Measurable (g t))
    (hunimod : ∀ t z, ‖g t z‖ = 1)
    (hzero : ∀ z, g 0 z = 1)
    (hmul : ∀ s t z, g (s + t) z = g s z * g t z)
    (hcont : ∀ z, Continuous fun t => g t z) :
    OneParameterUnitaryGroup H :=
  let hgb : ∀ t, ∃ C, ∀ z, ‖g t z‖ ≤ C := fun t => ⟨1, fun z => le_of_eq (hunimod t z)⟩
  { U := fun t => borelCalculus V hn (g t) (hmeas t) (hgb t)
    unitary := by
      intro t ψ φ
      -- `(U t)⋆ ∘ (U t) = borelCalculus (conj (g t) · g t) = borelCalculus 1 = id`
      have hcm : Measurable fun z => conj (g t z) :=
        Complex.continuous_conj.measurable.comp (hmeas t)
      have hcb : ∃ C, ∀ z, ‖conj (g t z)‖ ≤ C :=
        ⟨1, fun z => by rw [RCLike.norm_conj]; exact le_of_eq (hunimod t z)⟩
      have hm : Measurable fun z => conj (g t z) * g t z := hcm.mul (hmeas t)
      have hb : ∃ C, ∀ z, ‖conj (g t z) * g t z‖ ≤ C :=
        ⟨1, fun z => by rw [norm_mul, RCLike.norm_conj, hunimod t z, one_mul]⟩
      have hsymbol : (fun z => conj (g t z) * g t z) = fun _ => (1 : ℂ) := by
        funext z
        have h1 : conj (g t z) * g t z = ((‖g t z‖ ^ 2 : ℝ) : ℂ) := by
          rw [RCLike.conj_mul]; norm_cast
        rw [h1, hunimod t z]; norm_num
      have hadj : (borelCalculus V hn (g t) (hmeas t) (hgb t)).adjoint.comp
          (borelCalculus V hn (g t) (hmeas t) (hgb t)) = ContinuousLinearMap.id ℂ H := by
        rw [borelCalculus_adjoint V hn (g t) (hmeas t) (hgb t) hcm hcb,
          borelCalculus_mul V hn (fun z => conj (g t z)) (g t) hcm hcb (hmeas t) (hgb t) hm hb,
          borelCalculus_congr V hn hsymbol hm hb measurable_const ⟨1, fun _ => by simp⟩,
          borelCalculus_one V hn]
      calc ⟪borelCalculus V hn (g t) (hmeas t) (hgb t) ψ,
              borelCalculus V hn (g t) (hmeas t) (hgb t) φ⟫_ℂ
          = ⟪ψ, (borelCalculus V hn (g t) (hmeas t) (hgb t)).adjoint
              (borelCalculus V hn (g t) (hmeas t) (hgb t) φ)⟫_ℂ :=
            (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
        _ = ⟪ψ, ((borelCalculus V hn (g t) (hmeas t) (hgb t)).adjoint.comp
              (borelCalculus V hn (g t) (hmeas t) (hgb t))) φ⟫_ℂ := rfl
        _ = ⟪ψ, φ⟫_ℂ := by rw [hadj, ContinuousLinearMap.id_apply]
    group_law := by
      intro s t
      have hm : Measurable fun z => g s z * g t z := (hmeas s).mul (hmeas t)
      have hb : ∃ C, ∀ z, ‖g s z * g t z‖ ≤ C :=
        ⟨1, fun z => by rw [norm_mul, hunimod s z, hunimod t z, one_mul]⟩
      rw [borelCalculus_mul V hn (g s) (g t) (hmeas s) (hgb s) (hmeas t) (hgb t) hm hb]
      exact borelCalculus_congr V hn (funext fun z => hmul s t z) (hmeas (s + t)) (hgb (s + t))
        hm hb
    identity := by
      rw [borelCalculus_congr V hn (funext hzero) (hmeas 0) (hgb 0) measurable_const
            ⟨1, fun _ => by simp⟩,
        borelCalculus_one V hn]
    strong_continuous := by
      intro ψ
      rw [continuous_iff_continuousAt]
      intro t₀
      exact tendsto_borelCalculus_apply V hn (l := 𝓝 t₀) (G := g) (g := g t₀)
        (fun t => hmeas t) (fun t => hgb t) (hmeas t₀) (hgb t₀)
        (C := 1) (fun t z => le_of_eq (hunimod t z))
        (fun z => (hcont z).continuousAt) ψ }

/-- The operator at parameter `t` of `borelUnitaryGroup` is `borelCalculus V hn (g t)`. -/
@[simp] lemma borelUnitaryGroup_U (V : H →L[ℂ] H) (hn : IsStarNormal V)
    (g : ℝ → spectrum ℂ V → ℂ) (hmeas : ∀ t, Measurable (g t))
    (hunimod : ∀ t z, ‖g t z‖ = 1) (hzero : ∀ z, g 0 z = 1)
    (hmul : ∀ s t z, g (s + t) z = g s z * g t z) (hcont : ∀ z, Continuous fun t => g t z) (t : ℝ) :
    (borelUnitaryGroup V hn g hmeas hunimod hzero hmul hcont).U t
      = borelCalculus V hn (g t) (hmeas t) ⟨1, fun z => le_of_eq (hunimod t z)⟩ :=
  rfl

/-! ## The modular flow `Δ^{it}`

The **modular symbol** is `λ^{it} = exp (i t · log λ)`, where `λ = inverseMobius z` is the spectral
value of the operator pulled back through the Cayley map. We define it in exponential form (via
`Real.log` of the real part), which makes it manifestly unimodular, multiplicative, and continuous
*for any* normal `V`; under positivity of the pulled-back spectrum it agrees with the genuine power
`(↑λ)^{it}` (`modularSymbol_eq_cpow`), and `borelModularGroup` is then the Tomita–Takesaki modular
flow `Δ^{it}` of the operator whose Cayley transform is `V`. -/

/-- The modular symbol `λ^{it} = exp(i t · log λ)`, `λ = inverseMobius z` (via its real part). -/
noncomputable def modularSymbol (V : H →L[ℂ] H) (t : ℝ) (z : spectrum ℂ V) : ℂ :=
  exp (I * (t : ℂ) * (↑(Real.log (inverseMobius (z : ℂ)).re) : ℂ))

omit [CompleteSpace H] in
/-- The modular symbol `modularSymbol V t` is measurable in `z`. -/
lemma measurable_modularSymbol (V : H →L[ℂ] H) (t : ℝ) : Measurable (modularSymbol V t) := by
  have hiM : Measurable fun z : spectrum ℂ V => inverseMobius (z : ℂ) := by
    have : Measurable fun w : ℂ => inverseMobius w := by
      unfold inverseMobius
      exact (measurable_const.mul (measurable_const.add measurable_id)).div
        (measurable_const.sub measurable_id)
    exact this.comp measurable_subtype_coe
  unfold modularSymbol
  exact measurable_exp.comp <| measurable_const.mul <|
    measurable_ofReal.comp <| Real.measurable_log.comp <| measurable_re.comp hiM

omit [CompleteSpace H] in
/-- The modular symbol is unimodular: `‖modularSymbol V t z‖ = 1`. -/
lemma norm_modularSymbol (V : H →L[ℂ] H) (t : ℝ) (z : spectrum ℂ V) :
    ‖modularSymbol V t z‖ = 1 := by
  rw [modularSymbol, norm_exp]
  have hre : (I * (t : ℂ) * (↑(Real.log (inverseMobius (z : ℂ)).re) : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

omit [CompleteSpace H] in
/-- The modular symbol is normalized: `modularSymbol V 0 z = 1`. -/
lemma modularSymbol_zero (V : H →L[ℂ] H) (z : spectrum ℂ V) : modularSymbol V 0 z = 1 := by
  simp [modularSymbol]

omit [CompleteSpace H] in
/-- The modular symbol is multiplicative: `modularSymbol V (s + t) z = modularSymbol V s z *
modularSymbol V t z`. -/
lemma modularSymbol_add (V : H →L[ℂ] H) (s t : ℝ) (z : spectrum ℂ V) :
    modularSymbol V (s + t) z = modularSymbol V s z * modularSymbol V t z := by
  rw [modularSymbol, modularSymbol, modularSymbol, ← Complex.exp_add]
  congr 1
  push_cast
  ring

omit [CompleteSpace H] in
/-- The modular symbol is continuous in the parameter: `t ↦ modularSymbol V t z` is continuous. -/
lemma continuous_modularSymbol (V : H →L[ℂ] H) (z : spectrum ℂ V) :
    Continuous fun t => modularSymbol V t z := by
  unfold modularSymbol
  exact continuous_exp.comp ((continuous_const.mul continuous_ofReal).mul continuous_const)

/-- **The modular flow `Δ^{it}`** of the operator with Cayley transform `V`, as a strongly
continuous one-parameter unitary group, built from the Borel calculus via the modular symbol
`λ^{it}`. (It is the genuine modular flow when the pulled-back spectrum is positive; in general it
is the strongly continuous unitary group of the symbol `exp(i t · log⁺ λ)`.) -/
noncomputable def borelModularGroup (V : H →L[ℂ] H) (hn : IsStarNormal V) :
    OneParameterUnitaryGroup H :=
  borelUnitaryGroup V hn (modularSymbol V) (measurable_modularSymbol V) (norm_modularSymbol V)
    (modularSymbol_zero V) (modularSymbol_add V) (continuous_modularSymbol V)

/-- The operator at parameter `t` of `borelModularGroup` is
`borelCalculus V hn (modularSymbol V t)`. -/
@[simp] lemma borelModularGroup_U (V : H →L[ℂ] H) (hn : IsStarNormal V) (t : ℝ) :
    (borelModularGroup V hn).U t
      = borelCalculus V hn (modularSymbol V t) (measurable_modularSymbol V t)
          ⟨1, fun z => le_of_eq (norm_modularSymbol V t z)⟩ :=
  rfl

omit [CompleteSpace H] in
/-- **Faithfulness of the modular symbol.** On a positive pulled-back spectral value
`λ = inverseMobius z`, the modular symbol is the genuine complex power `(↑λ)^{it}`. -/
lemma modularSymbol_eq_cpow (V : H →L[ℂ] H) (t : ℝ) (z : spectrum ℂ V)
    (hz : 0 < (inverseMobius (z : ℂ)).re) :
    modularSymbol V t z = (↑((inverseMobius (z : ℂ)).re) : ℂ) ^ (I * (t : ℂ)) := by
  rw [modularSymbol, cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hz)),
    ← Complex.ofReal_log hz.le]
  congr 1
  ring

end Spectra.BorelCFC
