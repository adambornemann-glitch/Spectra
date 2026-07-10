/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# The scalar spectral measure, via Riesz–Markov–Kakutani

For a bounded star-normal operator `U` and a vector `ξ`, this file constructs the scalar spectral
measure `μ_ξ` on `σ(U)` by applying the Riesz–Markov–Kakutani representation theorem
(`RealRMK.rieszMeasure`) to the positive linear functional `ψ ↦ Re⟪ξ, ψ(U)ξ⟫` on `C(σ(U), ℝ)`.
Positivity of this functional is the C*-identity `star T * T ≥ 0` read through the continuous
functional calculus (`cfc_re_inner_ofReal_nonneg`).

It then develops the basic calculus of `μ_ξ`: the defining integral identity, total mass
`μ_ξ(σ(U)) = ‖ξ‖²`, the complex-valued extension `∫ f dμ_ξ = ⟪ξ, f(U) ξ⟫`, and polarization to the
off-diagonal measures `μ_{ξ,η}`, expressing `⟪ξ, f(U) η⟫` as a combination of four diagonal
integrals, together with a Cauchy–Schwarz-derived boundedness estimate for that form.

## Main definitions

* `spectralMeasure U hn ξ` : the scalar spectral measure `μ_ξ` on `σ(U)`.

## Main results

* `integral_spectralMeasure_complex` : `∫ z, f z ∂μ_ξ = ⟪ξ, cfcHom hn f ξ⟫_ℂ`.
* `spectralMeasure_real_univ` : `μ_ξ(σ(U)) = ‖ξ‖²`.
* `inner_cfcHom_polarized` : the off-diagonal form `⟪ξ, f(U) η⟫` via the four polarized diagonal
  integrals.
* `norm_inner_cfcHom_le` : `‖⟪ξ, f(U) η⟫‖ ≤ ‖f‖ * ‖ξ‖ * ‖η‖`.
-/

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
    change (f z : ℂ) = (starRingEnd ℂ) (Real.sqrt (f z) : ℂ) * (Real.sqrt (f z) : ℂ)
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
/-- `complexify U ψ` evaluated at `z` is the complexification `(ψ z : ℂ)` of the real value. -/
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

/-
One fragility to log, not a bug: rieszFunctional_nonneg's hψ is fed as fun z => hφ z,
which only typechecks because 0 ≤ ψ on ContinuousMap/C_c is definitionally the pointwise
∀ z, 0 ≤ ψ z. It compiles today; if a Mathlib bump ever bundles that order behind a
non-defeq wrapper, this is the line that breaks first. Cheap insurance is
ContinuousMap.le_def.mp/.mpr at those spots. Relatedly, the .toContinuousMap/ccToC
friction will keep recurring — on a compact σ(U) you may want a single helper
restating the property over C(σU,ℝ) directly, so C_c stops leaking into every
downstream lemma.
-/
lemma rieszFunctional_nonneg (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ : H)
    (ψ : C(spectrum ℂ U, ℝ)) (hψ : 0 ≤ ψ) :
    0 ≤ rieszFunctional U hn ξ ψ := by
  have hψ' : ∀ z, 0 ≤ ψ z := fun z => hψ z
  let s : C(spectrum ℂ U, ℝ) := ⟨fun z => Real.sqrt (ψ z), by fun_prop⟩
  have key : complexify U ψ = star (complexify U s) * complexify U s := by
    ext z
    change (ψ z : ℂ) = (starRingEnd ℂ) ((Real.sqrt (ψ z) : ℝ) : ℂ) * ((Real.sqrt (ψ z) : ℝ) : ℂ)
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hψ' z)]
  change 0 ≤ (⟪ξ, cfcHom hn (complexify U ψ) ξ⟫_ℂ).re
  rw [key, cfcHom_conjMul_inner_eq_normSq U hn (complexify U s) ξ,
      ← Complex.ofReal_pow, Complex.ofReal_re]
  positivity

open scoped CompactlySupported
open MeasureTheory

/-- The coercion `C_c(σU,ℝ) → C(σU,ℝ)` as an ℝ-linear map (C_c inherits +/• from C). -/
def ccToC (U : H →L[ℂ] H) : C_c(spectrum ℂ U, ℝ) →ₗ[ℝ] C(spectrum ℂ U, ℝ) where
  toFun := CompactlySupportedContinuousMap.toContinuousMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The scalar spectral measure** `μ_ξ` on `σ(U)`: Riesz–Markov applied to the positive
functional `ψ ↦ Re⟪ξ, ψ(U) ξ⟫`. -/
noncomputable def spectralMeasure (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ : H) :
    Measure (spectrum ℂ U) :=
  RealRMK.rieszMeasure <| PositiveLinearMap.mk₀
    ((rieszFunctional U hn ξ).comp (ccToC U))
    (fun φ hφ => rieszFunctional_nonneg U hn ξ φ.toContinuousMap (fun z => hφ z))

/-- **Defining property.** Integrating `ψ` against `μ_ξ` returns the quadratic form. -/
lemma integral_spectralMeasure (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ : H)
    (ψ : C_c(spectrum ℂ U, ℝ)) :
    ∫ z, ψ z ∂(spectralMeasure U hn ξ)
      = (⟪ξ, cfcHom hn (complexify U ψ.toContinuousMap) ξ⟫_ℂ).re :=
  RealRMK.integral_rieszMeasure _ ψ

/-- Defining property over **all** continuous functions on `σ(U)` (compact ⇒ `C = C_c`).
This is the form downstream lemmas use, so `C_c` stops leaking into every statement. -/
lemma integral_spectralMeasure_continuous
    (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ : H) (g : C(spectrum ℂ U, ℝ)) :
    ∫ z, g z ∂(spectralMeasure U hn ξ) = (⟪ξ, cfcHom hn (complexify U g) ξ⟫_ℂ).re := by
  simpa using integral_spectralMeasure U hn ξ
    (⟨g, HasCompactSupport.of_compactSpace g⟩ : C_c(spectrum ℂ U, ℝ))

/-- `σ(U)` is a compact space and the Riesz measure is content-based, hence finite on
compacts. -/
instance instIsFiniteMeasureOnCompacts_spectralMeasure
    (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ : H) :
    IsFiniteMeasureOnCompacts (spectralMeasure U hn ξ) := by
  have : (spectralMeasure U hn ξ).Regular := by
     unfold spectralMeasure RealRMK.rieszMeasure; infer_instance
  infer_instance

/-- `μ_ξ` is a finite measure: `σ(U)` is compact, so its total mass is finite. -/
instance instIsFiniteMeasure_spectralMeasure
    (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ : H) :
    IsFiniteMeasure (spectralMeasure U hn ξ) :=
  ⟨isCompact_univ.measure_lt_top⟩

/-- **Diagonal is real for real symbols.** For real `g`, `g(U)` is self-adjoint, so
`⟪ξ, g(U) ξ⟫` is real and equals `∫ g dμ_ξ`. The bridge polarization needs. -/
lemma inner_cfcHom_complexify_real
    (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ : H) (g : C(spectrum ℂ U, ℝ)) :
    ⟪ξ, cfcHom hn (complexify U g) ξ⟫_ℂ
      = ((∫ z, g z ∂(spectralMeasure U hn ξ) : ℝ) : ℂ) := by
  set T := cfcHom hn (complexify U g) with hT
  have hφ : star (complexify U g) = complexify U g := by
    ext z
    change star ((g z : ℂ)) = ((g z : ℂ))
    rw [show star ((g z : ℂ)) = (starRingEnd ℂ) (g z : ℂ) from rfl, Complex.conj_ofReal]
  have hsa : IsSelfAdjoint T := by
    rw [hT, isSelfAdjoint_iff, ← map_star, hφ]
  have hre : (⟪ξ, T ξ⟫_ℂ).re = ∫ z, g z ∂(spectralMeasure U hn ξ) :=
    (integral_spectralMeasure_continuous U hn ξ g).symm
  have hreal : (starRingEnd ℂ) ⟪ξ, T ξ⟫_ℂ = ⟪ξ, T ξ⟫_ℂ := by
    rw [inner_conj_symm]
    nth_rewrite 1 [← hsa.adjoint_eq]
    rw [ContinuousLinearMap.adjoint_inner_left]
  rw [← Complex.conj_eq_iff_re.mp hreal, hre]

/-- **Total mass.** `μ_ξ(σ(U)) = ‖ξ‖²` — the falsifiable normalization check, and what
forces `E univ = 1` in Stage 4. -/
lemma spectralMeasure_real_univ
    (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ : H) :
    (spectralMeasure U hn ξ).real Set.univ = ‖ξ‖ ^ 2 := by
  have h := integral_spectralMeasure_continuous U hn ξ 1
  simp only [ContinuousMap.one_apply] at h
  rw [integral_const, smul_eq_mul, mul_one] at h
  rw [h]
  have hc1 : complexify U (1 : C(spectrum ℂ U, ℝ)) = 1 := by
    ext _z; simp [complexify_apply]
  rw [hc1, map_one, ContinuousLinearMap.one_apply]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) ξ

/-- Real continuous functions on the (compact) spectrum are integrable against `μ_ξ`. -/
lemma spectral_integrable_real
    (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ : H) (g : C(spectrum ℂ U, ℝ)) :
    Integrable (fun z => g z) (spectralMeasure U hn ξ) :=
  g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)

/-- **Complex form.** `∫ f dμ_ξ = ⟪ξ, f(U) ξ⟫` for every continuous complex `f` — the
on-ramp to polarization. Both sides split along real/imaginary parts and meet on the
real diagonal. -/
lemma integral_spectralMeasure_complex
    (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ : H) (f : C(spectrum ℂ U, ℂ)) :
    ∫ z, f z ∂(spectralMeasure U hn ξ) = ⟪ξ, cfcHom hn f ξ⟫_ℂ := by
  set μ := spectralMeasure U hn ξ with _hμ
  let fr : C(spectrum ℂ U, ℝ) := ⟨fun z => (f z).re, by fun_prop⟩
  let fi : C(spectrum ℂ U, ℝ) := ⟨fun z => (f z).im, by fun_prop⟩
  have hsplit : f = complexify U fr + Complex.I • complexify U fi := by
    ext z
    simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, complexify_apply, smul_eq_mul]
    change f z = ((f z).re : ℂ) + Complex.I * ((f z).im : ℂ)
    rw [mul_comm]; exact (Complex.re_add_im (f z)).symm
  have hint_r := spectral_integrable_real U hn ξ fr
  have hint_i := spectral_integrable_real U hn ξ fi
  have hRHS : ⟪ξ, cfcHom hn f ξ⟫_ℂ
      = ((∫ z, fr z ∂μ : ℝ) : ℂ) + Complex.I * ((∫ z, fi z ∂μ : ℝ) : ℂ) := by
    rw [hsplit, map_add, map_smul, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, inner_add_right, inner_smul_right,
        inner_cfcHom_complexify_real, inner_cfcHom_complexify_real]
  have hLHS : ∫ z, f z ∂μ
      = ((∫ z, fr z ∂μ : ℝ) : ℂ) + Complex.I * ((∫ z, fi z ∂μ : ℝ) : ℂ) := by
    rw [hsplit]
    simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, complexify_apply, smul_eq_mul]
    erw [integral_add (Complex.ofRealCLM.integrable_comp hint_r)
          ((Complex.ofRealCLM.integrable_comp hint_i).const_mul Complex.I),
        integral_complex_ofReal, integral_const_mul, integral_complex_ofReal]
    abel
  rw [hLHS, hRHS]

/- # Polarization -/

/-- Right-slot complex polarization: `⟪ξ, T η⟫` from the four diagonals `⟪z, T z⟫`.
Mathlib's `inner_map_polarization'` is left-slot (`⟪T x, y⟫`); this is its image under the
adjoint, putting the diagonal on the right where `⟪ζ, f(U) ζ⟫ = ∫ f dμ_ζ` lives. -/
lemma inner_polarization_right (T : H →L[ℂ] H) (ξ η : H) :
    ⟪ξ, T η⟫_ℂ =
      (⟪ξ + η, T (ξ + η)⟫_ℂ - ⟪ξ - η, T (ξ - η)⟫_ℂ
        - Complex.I * ⟪ξ + Complex.I • η, T (ξ + Complex.I • η)⟫_ℂ
        + Complex.I * ⟪ξ - Complex.I • η, T (ξ - Complex.I • η)⟫_ℂ) / 4 := by
  have key := inner_map_polarization' (T.adjoint : H →ₗ[ℂ] H) ξ η
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.adjoint_inner_left] at key
  exact key

/-- **Polarized-diagonal identity.** The off-diagonal form `⟪ξ, f(U) η⟫` expressed through
the four diagonal spectral integrals. This is the spine of Piece 2: every later statement
about `μ_{ξ,η}` rests on it. -/
lemma inner_cfcHom_polarized (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ η : H)
    (f : C(spectrum ℂ U, ℂ)) :
    ⟪ξ, cfcHom hn f η⟫_ℂ =
      ( ∫ z, f z ∂(spectralMeasure U hn (ξ + η))
        - ∫ z, f z ∂(spectralMeasure U hn (ξ - η))
        - Complex.I * ∫ z, f z ∂(spectralMeasure U hn (ξ + Complex.I • η))
        + Complex.I * ∫ z, f z ∂(spectralMeasure U hn (ξ - Complex.I • η)) ) / 4 := by
  rw [inner_polarization_right (cfcHom hn f) ξ η,
      ← integral_spectralMeasure_complex U hn (ξ + η) f,
      ← integral_spectralMeasure_complex U hn (ξ - η) f,
      ← integral_spectralMeasure_complex U hn (ξ + Complex.I • η) f,
      ← integral_spectralMeasure_complex U hn (ξ - Complex.I • η) f]

/-- **Boundedness of the spectral form.** `‖⟪ξ, f(U) η⟫‖ ≤ ‖f‖ · ‖ξ‖ · ‖η‖`, from the isometry
of `cfcHom` and Cauchy–Schwarz. This is the bound Stage 3's Fréchet–Riesz step consumes when
it turns the polarized form into the operator `g(U)` for bounded Borel `g`. -/
lemma norm_inner_cfcHom_le (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ η : H)
    (f : C(spectrum ℂ U, ℂ)) :
    ‖⟪ξ, cfcHom hn f η⟫_ℂ‖ ≤ ‖f‖ * ‖ξ‖ * ‖η‖ := by
  calc ‖⟪ξ, cfcHom hn f η⟫_ℂ‖
      ≤ ‖ξ‖ * ‖cfcHom hn f η‖           := norm_inner_le_norm ξ _
    _ ≤ ‖ξ‖ * (‖cfcHom hn f‖ * ‖η‖)     := by gcongr; exact (cfcHom hn f).le_opNorm η
    _ ≤ ‖ξ‖ * (‖f‖ * ‖η‖)               := by gcongr; exact (norm_cfcHom U f hn).le
    _ = ‖f‖ * ‖ξ‖ * ‖η‖                 := by ring

end Spectra.Riesz
