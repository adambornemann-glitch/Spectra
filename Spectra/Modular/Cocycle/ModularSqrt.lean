/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SpectralTheory.Calculus.PMapSquareRoot
import Spectra.Modular.TomitaTakesaki.VonNeumannTstarT
import Spectra.Modular.TomitaTakesaki.ModularOperator
/-!
# The modular square root `Δ^{½}` (R2)

For a cyclic–separating vector `Ω` of a von Neumann algebra `M`, the modular operator
`Δ = S⋆S = modularOp M Ω` is self-adjoint and `≥ 0` (von Neumann's `T⋆T` theorem, the GATE).
Feeding `Δ`'s unitary group `genToGroup` to the unbounded `√` calculus
(`Spectra.SpectralTheory.Calculus.PMapSquareRoot`) gives the **modular square root**

  `Δ^{½} := modularSqrt = pmapOfPVM (genToGroup Δ) √`,

and the general form identity `‖A^{½}x‖² = Re⟪x, A x⟫` specializes — via `Re⟪Δ x, x⟫ = ‖S x‖²` — to

  `‖Δ^{½} x‖ = ‖S x‖`   (`norm_modularSqrt_eq_norm_tomita`).

This is exactly the isometry `Δ^{½}x ↦ S x` extended to the unitary `W` of the polar decomposition
`S = J Δ^{½}` (R3), the input to `LinearEquiv.extendOfIsometry`.
-/

open Complex MeasureTheory
open scoped InnerProductSpace
open Spectra.QuantumMechanics.SpectralTheory
open Spectra.YosidaHille
open Spectra.OneParameterUnitaryGroup

namespace Spectra.TomitaTakesaki

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

/-- **The modular form is a squared norm**: `Re⟪Δ x, x⟫ = ‖S x‖²`.  The value behind
`modularOp_nonneg` — `Δ x = S⋆(S x)`, so `⟪Δ x, x⟫ = ⟪S x, S x⟫ = ‖S x‖²`. -/
theorem modularOp_re_inner_eq_normSq (hcyc : IsCyclic M Ω) (w : (modularOp M Ω).domain)
    (hwS : (w : H) ∈ (tomitaClosure M Ω).domain) :
    (⟪modularOp M Ω w, (w : H)⟫_ℂ).re = ‖tomitaClosure M Ω ⟨(w : H), hwS⟩‖ ^ 2 := by
  obtain ⟨⟨hxS, hSx⟩, _⟩ := w.2
  rw [modularOp_apply w hxS hSx]
  have hdense : Dense ((tomitaClosure M Ω).domain : Set H) := tomitaClosure_domain_dense hcyc
  have hfa := LinearPMap.adjoint_isFormalAdjoint (T := tomitaClosure M Ω) hdense
    ⟨(tomitaClosure M Ω) ⟨(w : H), hxS⟩, hSx⟩ ⟨(w : H), hxS⟩
  rw [hfa, modularForm_eq_norm_sq ⟨(w : H), hxS⟩, ← Complex.ofReal_pow, Complex.ofReal_re]

/-- **The modular square root** `Δ^{½} := pmapOfPVM (genToGroup Δ) √` — the unbounded `√` calculus
of the spectral measure of the non-negative self-adjoint `Δ = modularOp M Ω`. -/
noncomputable def modularSqrt (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) : H →ₗ.[ℂ] H :=
  pmapOfPVM (genToGroup (modularOp_isSelfAdjoint hcyc hsep))
    (fun s => (Real.sqrt s : ℂ)) measurable_sqrtC

/-- **The polar isometry** `‖Δ^{½} x‖² = ‖S x‖²`.  The general form identity
`norm_sq_pmapOfPVM_sqrt` (`‖A^{½}x‖² = Re⟪x, A x⟫`, valid since `Δ ≥ 0` by `modularOp_nonneg`)
composed with `Re⟪Δ x, x⟫ = ‖S x‖²` (`modularOp_re_inner_eq_normSq`). -/
theorem norm_sq_modularSqrt (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)
    (x : (generator (genToGroup (modularOp_isSelfAdjoint hcyc hsep))).domain)
    (hxS : (x : H) ∈ (tomitaClosure M Ω).domain) :
    ‖modularSqrt hcyc hsep ⟨(x : H),
        (ProjValMeasure.mem_pmapDomain _).mpr (sqrt_integrable_of_mem_generator _ x)⟩‖ ^ 2
      = ‖tomitaClosure M Ω ⟨(x : H), hxS⟩‖ ^ 2 := by
  have hgen : generator (genToGroup (modularOp_isSelfAdjoint hcyc hsep)) = modularOp M Ω :=
    generator_genToGroup _
  have hpos : ∀ z : (generator (genToGroup (modularOp_isSelfAdjoint hcyc hsep))).domain,
      0 ≤ (⟪(z : H), generator (genToGroup (modularOp_isSelfAdjoint hcyc hsep)) z⟫_ℂ).re := by
    rintro ⟨ψ, hψ'⟩
    have hψ : ψ ∈ (modularOp M Ω).domain := by rw [← hgen]; exact hψ'
    have hval : generator (genToGroup (modularOp_isSelfAdjoint hcyc hsep)) ⟨ψ, hψ'⟩
        = modularOp M Ω ⟨ψ, hψ⟩ := (le_of_eq hgen).2 rfl
    rw [hval, ← inner_conj_symm, Complex.conj_re]
    exact modularOp_nonneg hcyc ⟨ψ, hψ⟩
  obtain ⟨ψ, hψ'⟩ := x
  unfold modularSqrt
  rw [norm_sq_pmapOfPVM_sqrt _ hpos ⟨ψ, hψ'⟩]
  have hψ : ψ ∈ (modularOp M Ω).domain := by rw [← hgen]; exact hψ'
  have hval : generator (genToGroup (modularOp_isSelfAdjoint hcyc hsep)) ⟨ψ, hψ'⟩
      = modularOp M Ω ⟨ψ, hψ⟩ := (le_of_eq hgen).2 rfl
  rw [hval, ← inner_conj_symm, Complex.conj_re]
  exact modularOp_re_inner_eq_normSq hcyc ⟨ψ, hψ⟩ hxS

/-- **The polar isometry** `‖Δ^{½} x‖ = ‖S x‖` — the norm form of `norm_sq_modularSqrt`, the
hypothesis `LinearEquiv.extendOfIsometry` needs to extend `Δ^{½}x ↦ S x` to the unitary `W`. -/
theorem norm_modularSqrt_eq_norm_tomita (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)
    (x : (generator (genToGroup (modularOp_isSelfAdjoint hcyc hsep))).domain)
    (hxS : (x : H) ∈ (tomitaClosure M Ω).domain) :
    ‖modularSqrt hcyc hsep ⟨(x : H),
        (ProjValMeasure.mem_pmapDomain _).mpr (sqrt_integrable_of_mem_generator _ x)⟩‖
      = ‖tomitaClosure M Ω ⟨(x : H), hxS⟩‖ := by
  have h := norm_sq_modularSqrt hcyc hsep x hxS
  have h1 : (0 : ℝ) ≤ ‖modularSqrt hcyc hsep ⟨(x : H),
      (ProjValMeasure.mem_pmapDomain _).mpr (sqrt_integrable_of_mem_generator _ x)⟩‖ :=
    norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖tomitaClosure M Ω ⟨(x : H), hxS⟩‖ := norm_nonneg _
  nlinarith [h, h1, h2, sq_nonneg (‖modularSqrt hcyc hsep ⟨(x : H),
    (ProjValMeasure.mem_pmapDomain _).mpr (sqrt_integrable_of_mem_generator _ x)⟩‖
    - ‖tomitaClosure M Ω ⟨(x : H), hxS⟩‖)]

end Spectra.TomitaTakesaki
