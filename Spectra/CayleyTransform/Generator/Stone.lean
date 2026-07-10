/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.CayleyTransform.Generator.InverseAction   -- cayley, stoneExp, stoneGroup, resolventSymbol
import Spectra.CayleyTransform.Generator.Resolvent     -- selfAdjointResolvent_eq_borelCalculus (keystone)
import Spectra.CayleyTransform.Generator.Pushforward   -- the group-free helpers: inverseMobiusReal, borelMeasure_stoneGroup_eq_map
import Spectra.Resolvent.SpectralRepresentation       -- inner_resolvent_diag_eq_integral
import Spectra.SpectralTheory.StoneFormula.Identities -- resolvent_left_inverse / _mem_domain / _solves
import Spectra.Resolvent.Integral.Domain              -- generator, generator_isSelfAdjoint, ranges
/-!
# `generator (stoneGroup hA) = A`, proved without the Yosida group

This closes the spectral construction **on its own terms**.  The single new fact is that the
generator of `stoneGroup hA` has the same resolvent as `A`:

  `(generator (stoneGroup hA) − z)⁻¹ = selfAdjointResolvent hA z`,    `Im z ≠ 0`, `i + z ≠ 0`,

obtained by comparing diagonals — the left through the generic group identity
`inner_resolvent_diag_eq_integral`, the right through the keystone
`selfAdjointResolvent_eq_borelCalculus`, the two joined by the pushforward
`borelMeasure_stoneGroup_eq_map`.  A self-adjoint operator is determined by its resolvent
(`resolvent_left_inverse` + `resolvent_mem_domain` + `resolvent_solves`), giving
`A ≤ generator (stoneGroup hA)`, and `IsSelfAdjoint.eq_of_le` finishes.

`genToGroup` does not appear. The consistency `stoneGroup_eq_genToGroup` (`StoneBridge/Basic.lean`)
is then a one-line corollary of the two independent generator computations, via `group_unique`.
-/
open Complex MeasureTheory Filter Topology InnerProductSpace
open scoped InnerProductSpace
open Spectra Spectra.Resolvent Spectra.YosidaHille
open Spectra.QuantumMechanics.SpectralTheory Spectra.BorelCFC
open Spectra.OneParameterUnitaryGroup Spectra.Borel
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H}
namespace Spectra.Cayley


/-! ## The resolvent of the spectral generator is the resolvent of `A` -/

/-- **The keystone of this file.**  The group-theoretic resolvent of `generator (stoneGroup hA)`
coincides with the operator-theoretic `selfAdjointResolvent hA`.  Both diagonals are integrals of
the Cauchy kernel: the left against the group's spectral measure
(`inner_resolvent_diag_eq_integral`),
the right against the Cayley spectral measure (`selfAdjointResolvent_eq_borelCalculus` +
`inner_borelCalculus_self`), and the two measures are pushforwards under `inverseMobius`. -/
theorem generator_resolvent_eq_selfAdjoint [Nontrivial H] (hA : IsSelfAdjoint A)
    (z : ℂ) (hz : z.im ≠ 0) (hzi : I + z ≠ 0) :
    Resolvent.resolvent z hz (generator_isFormalAdjoint (stoneGroup hA))
        (range_plus_i_eq_top (stoneGroup hA)) (range_minus_i_eq_top (stoneGroup hA))
      = selfAdjointResolvent hA z hz := by
  refine op_ext_of_inner_self fun ξ => ?_
  have hzr : ∀ x : ℝ, ((x : ℂ) - z) ≠ 0 := fun x hx => by
    rw [sub_eq_zero] at hx; exact hz (by rw [← hx, Complex.ofReal_im])
  have hcont : Continuous (fun x : ℝ => ((x : ℂ) - z)⁻¹) :=
    (Complex.continuous_ofReal.sub continuous_const).inv₀ hzr
  rw [inner_resolvent_diag_eq_integral (stoneGroup hA) z hz ξ,
    selfAdjointResolvent_eq_borelCalculus hA z hz hzi,
    inner_borelCalculus_self (cayley hA) (cayley_isStarNormal hA) (resolventSymbol hA z)
      (resolventSymbol_measurable hA z) (resolventSymbol_bdd hA z hz),
    borelMeasure_stoneGroup_eq_map hA ξ,
    integral_map (inverseMobiusReal_measurable hA).aemeasurable hcont.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [resolventSymbol]
  rw [inverseMobiusReal_coe hA w]

/-! ## `A ≤ generator (stoneGroup hA)` -/

/-- A self-adjoint operator is determined by its resolvent: with the resolvents identified at
`z = i` (where `i + i = 2i ≠ 0`), `resolvent_left_inverse` sends `A ψ − i ψ ↦ ψ` and
`resolvent_mem_domain` / `resolvent_solves` read the same `ψ` back as a domain point of the
spectral generator with the same value. -/
theorem A_le_generator_stoneGroup [Nontrivial H] (hA : IsSelfAdjoint A) :
    A ≤ generator (stoneGroup hA) := by
  have hz : (I : ℂ).im ≠ 0 := by simp
  have hzi : I + I ≠ 0 := by
    rw [show I + I = (2 : ℂ) * I from by ring]; exact mul_ne_zero two_ne_zero I_ne_zero
  have hres := generator_resolvent_eq_selfAdjoint hA I hz hzi
  -- abbreviations for the spectral generator's deficiency witnesses
  set hsymB := generator_isFormalAdjoint (stoneGroup hA)
  set hplusB := range_plus_i_eq_top (stoneGroup hA)
  set hminusB := range_minus_i_eq_top (stoneGroup hA)
  refine ⟨fun v hv => ?_, fun x y hxy => ?_⟩
  · -- domain inclusion
    have h1 : selfAdjointResolvent hA I hz (A ⟨v, hv⟩ - I • v) = v :=
      resolvent_left_inverse (isFormalAdjoint_of_isSelfAdjoint hA)
        (isSelfAdjoint_to_surjective hA).1 (isSelfAdjoint_to_surjective hA).2 I hz ⟨v, hv⟩
    have hRB : Resolvent.resolvent I hz hsymB hplusB hminusB (A ⟨v, hv⟩ - I • v) = v := by
      rw [hres]; exact h1
    rw [← hRB]
    exact resolvent_mem_domain hsymB hplusB hminusB I hz _
  · -- value agreement: `A x = generator (stoneGroup hA) y` for `(x : H) = (y : H)`
    set φ : H := A x - I • (x : H) with hφ
    have h1 : selfAdjointResolvent hA I hz φ = (x : H) :=
      resolvent_left_inverse (isFormalAdjoint_of_isSelfAdjoint hA)
        (isSelfAdjoint_to_surjective hA).1 (isSelfAdjoint_to_surjective hA).2 I hz x
    have hRB : Resolvent.resolvent I hz hsymB hplusB hminusB φ = (x : H) := by rw [hres]; exact h1
    have hmem := resolvent_mem_domain hsymB hplusB hminusB I hz φ
    have hsolve := resolvent_solves hsymB hplusB hminusB I hz φ
    -- the domain point produced by the resolvent is exactly `y`
    have hey : (⟨Resolvent.resolvent I hz hsymB hplusB hminusB φ, hmem⟩
        : (generator (stoneGroup hA)).domain) = y := Subtype.ext (by simp only [hRB, hxy])
    rw [hey, hRB] at hsolve            -- hsolve : generator (stoneGroup hA) y - I • (x : H) = φ
    -- cancel the common `- I • (x : H)` against `φ = A x - I • (x : H)`
    have : generator (stoneGroup hA) y - I • (x : H) = A x - I • (x : H) := by rw [hsolve, hφ]
    exact (sub_left_inj.mp this).symm

/-! ## The generator, and the difference-quotient limit -/

/-- **The generator of the spectral group is `A`** — no Yosida group involved. -/
theorem generator_stoneGroup [Nontrivial H] (hA : IsSelfAdjoint A) :
    generator (stoneGroup hA) = A :=
  (IsSelfAdjoint.eq_of_le hA (generator_isSelfAdjoint (stoneGroup hA))
    (A_le_generator_stoneGroup hA)).symm

/-- The defining difference-quotient limit, now a corollary of the *direct* generator computation
(identical statement to your `Stone.lean`, but no longer routed through `genToGroup`). -/
theorem stoneExp_genDiffQuot_tendsto [Nontrivial H] (hA : IsSelfAdjoint A)
    (ψ : H) (hψ : ψ ∈ A.domain) :
    Tendsto (genDiffQuot (stoneGroup hA) ψ) (𝓝[≠] (0 : ℝ)) (𝓝 (A ⟨ψ, hψ⟩)) := by
  have hψgen : ψ ∈ (generator (stoneGroup hA)).domain := by
    rw [generator_stoneGroup hA]; exact hψ
  have hval : generator (stoneGroup hA) ⟨ψ, hψgen⟩ = A ⟨ψ, hψ⟩ :=
    (le_of_eq (generator_stoneGroup hA)).2 (x := ⟨ψ, hψgen⟩) (y := ⟨ψ, hψ⟩) rfl
  rw [← hval]
  exact generator_tendsto (stoneGroup hA) ⟨ψ, hψgen⟩

end Spectra.Cayley
