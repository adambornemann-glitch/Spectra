import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

open scoped InnerProductSpace
open TopologicalSpace Filter Complex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.Riesz

/-- **Riesz–Markov positivity, raw form.** For `g` continuous on `σ(U)`, applying the
nonnegative function `z ↦ conj(g z)·g z` to a normal operator `U` realizes the quadratic
form `⟪ξ, ·ξ⟫` as the squared norm `‖g(U) ξ‖²`. This is the C*-identity `star T * T ≥ 0`
read through the functional calculus; with `g = √f` it is exactly what makes the Riesz
functional `f ↦ ⟪ξ, f(U) ξ⟫` positive. -/
lemma cfc_conjMul_inner_eq_normSq
    (U : H →L[ℂ] H) (_hn : IsStarNormal U) (g : ℂ → ℂ)
    (hg : ContinuousOn g (spectrum ℂ U)) (ξ : H) :
    ⟪ξ, cfc (fun z => star (g z) * g z) U ξ⟫_ℂ = (‖cfc g U ξ‖ : ℂ) ^ 2 := by
  have hop : cfc (fun z => star (g z) * g z) U = star (cfc g U) * cfc g U := by
    rw [cfc_mul (fun z => star (g z)) g U hg.star hg, cfc_star g U]
  rw [hop, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]; rfl

/-- **Riesz–Markov positivity.** For real-valued `f ≥ 0` continuous on `σ(U)`, the form
`Re⟪ξ, f(U) ξ⟫` is nonnegative — the positivity the Riesz functional requires.
On the spectrum `f = conj(√f)·√f`, so the squared-norm identity finishes it. -/
lemma cfc_re_inner_ofReal_nonneg
    (U : H →L[ℂ] H) (hn : IsStarNormal U) (f : ℂ → ℝ)
    (hf : ContinuousOn f (spectrum ℂ U)) (hf0 : ∀ z ∈ spectrum ℂ U, 0 ≤ f z)
    (ξ : H) :
    0 ≤ (⟪ξ, cfc (fun z => (f z : ℂ)) U ξ⟫_ℂ).re := by
  have hgc : ContinuousOn (fun z => (Real.sqrt (f z) : ℂ)) (spectrum ℂ U) :=
    Complex.continuous_ofReal.comp_continuousOn hf.sqrt
  have hcongr : (spectrum ℂ U).EqOn (fun z => (f z : ℂ))
      (fun z => star ((Real.sqrt (f z) : ℂ)) * (Real.sqrt (f z) : ℂ)) := by
    intro z hz
    show (f z : ℂ) = (starRingEnd ℂ) (Real.sqrt (f z) : ℂ) * (Real.sqrt (f z) : ℂ)
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hf0 z hz)]
  rw [cfc_congr hcongr,
      cfc_conjMul_inner_eq_normSq U hn (fun z => (Real.sqrt (f z) : ℂ)) hgc ξ,
      ← Complex.ofReal_pow, Complex.ofReal_re]
  positivity

/-- Squared-norm identity at the bundled-calculus level: `cfcHom` is a `*`-homomorphism, so
`conj φ · φ` lands on `star T * T` and the form is `‖cfcHom hn φ ξ‖²`. -/
lemma cfcHom_conjMul_inner_eq_normSq
    (U : H →L[ℂ] H) (hn : IsStarNormal U) (φ : C(spectrum ℂ U, ℂ)) (ξ : H) :
    ⟪ξ, (cfcHom hn (star φ * φ)) ξ⟫_ℂ = (‖(cfcHom hn φ) ξ‖ : ℂ) ^ 2 := by
  rw [map_mul, map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K]; rfl

/-- Complexification of real continuous functions on `σ(U)`, as a continuous ℝ-linear map. -/
noncomputable def complexify (U : H →L[ℂ] H) :
    C(spectrum ℂ U, ℝ) →L[ℝ] C(spectrum ℂ U, ℂ) :=
  ContinuousLinearMap.compLeftContinuous ℝ ↥(spectrum ℂ U) Complex.ofRealCLM

omit [CompleteSpace H] in
@[simp] lemma complexify_apply (U : H →L[ℂ] H) (ψ : C(spectrum ℂ U, ℝ))
    (z : spectrum ℂ U) : complexify U ψ z = (ψ z : ℂ) := rfl

/-- The Riesz functional `ψ ↦ Re⟪ξ, ψ(U) ξ⟫` on real continuous functions on the spectrum,
packaged as an ℝ-linear map — the input Riesz–Markov needs. -/
noncomputable def rieszFunctional (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ : H) :
    C(spectrum ℂ U, ℝ) →ₗ[ℝ] ℝ where
  toFun ψ := (⟪ξ, (cfcHom hn (complexify U ψ)) ξ⟫_ℂ).re
  map_add' ψ₁ ψ₂ := by
    simp only [map_add, ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
  map_smul' r ψ := by
    have h := LinearMapClass.map_smul_of_tower (cfcHom hn) r (complexify U ψ)
    simp only [map_smul, h, ContinuousLinearMap.smul_apply,
               inner_smul_right_eq_smul, Complex.smul_re, RingHom.id_apply, smul_eq_mul]

lemma rieszFunctional_nonneg (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ : H)
    (ψ : C(spectrum ℂ U, ℝ)) (hψ : 0 ≤ ψ) :
    0 ≤ rieszFunctional U hn ξ ψ := by
  have hψ' : ∀ z, 0 ≤ ψ z := fun z => hψ z
  let s : C(spectrum ℂ U, ℝ) := ⟨fun z => Real.sqrt (ψ z), by fun_prop⟩
  have key : complexify U ψ = star (complexify U s) * complexify U s := by
    ext z
    show (ψ z : ℂ) = (starRingEnd ℂ) ((Real.sqrt (ψ z) : ℝ) : ℂ) * ((Real.sqrt (ψ z) : ℝ) : ℂ)
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hψ' z)]
  show 0 ≤ (⟪ξ, cfcHom hn (complexify U ψ) ξ⟫_ℂ).re
  rw [key, cfcHom_conjMul_inner_eq_normSq U hn (complexify U s) ξ,
      ← Complex.ofReal_pow, Complex.ofReal_re]
  positivity

end Spectra.Riesz
