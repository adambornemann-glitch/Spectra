/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SpectralTheory.Calculus.PMapBounded
import Spectra.CayleyTransform.Generator.Pushforward
import Spectra.CayleyTransform.BorelCalculus
import Spectra.StoneBridge.Basic
/-!
# Closing the square: `pmapOfPVM`/`spectralCalculus` ↔ `borelCalculus`/`cfcHom`, via Cayley

Two bounded functional calculi already exist in this library, on two different domains:

* `spectralCalculus U_grp g` (`SpectralTheory/Calculus/Bounded.lean`) — a bounded Borel symbol
  `g : ℝ → ℂ` of *any* `OneParameterUnitaryGroup`, integrated against the group's own diagonal
  measure `borelMeasure U_grp`. This is what `pmapOfPVM` (P1) reduces to on bounded symbols, and
  what the rest of the library actually consumes.
* `borelCalculus (cayley hA) (cayley_isStarNormal hA) g` (`CayleyTransform/BorelCalculus.lean`) —
  a bounded Borel symbol `g : spectrum ℂ (cayley hA) → ℂ` of the *bounded unitary* Cayley
  transform, integrated against its Riesz–Markov measure. This one already matches Mathlib's own
  continuous functional calculus on continuous symbols (`borelCalculus_eq_cfcHom`).

Nothing connected them. This file does: `spectralCalculus (stoneGroup hA)` and
`borelCalculus (cayley hA)` are literally the *same* operator, for a symbol and its Möbius
pullback — via the pushforward identity `borelMeasure_stoneGroup_eq_map` (P0/P5's own tool) and a
change-of-variables integral. Composed with `stoneGroup_eq_genToGroup` (P0) and P1's reduction,
this identifies the library's own unbounded functional calculus `pmapOfPVM` with Mathlib's `cfcHom`
on Cayley — the capstone P4 was reaching for, and (per von Neumann's actual program) the natural
conclusion of the whole Cayley-transform bridge.

## Scope honesty

The `cfcHom`-matching corollaries require the pulled-back symbol `g ∘ inverseMobiusReal hA` to be
*continuous on the whole Cayley spectrum*, stated as an explicit hypothesis. This is a genuine
restriction, not automatic: `inverseMobiusReal` itself is discontinuous at the excluded point
`w = 1` on the unit circle, and for *unbounded* `A` that point is typically in the spectrum of
`cayley hA` (the "junk point" the Cayley-transform concept notes already flag). The unconditional
bridge (`spectralCalculus_stoneGroup_eq_borelCalculus`) needs no such hypothesis — it is a measure-
theoretic fact, not a topological one.

## Main results

* `spectralCalculus_stoneGroup_eq_borelCalculus` — the unconditional bridge, any bounded
  measurable symbol.
* `spectralCalculus_stoneGroup_eq_cfcHom` — matches `cfcHom` when the pullback is continuous.
* `pmapOfPVM_apply_eq_borelCalculus_of_bounded` — the capstone: `pmapOfPVM (genToGroup hA)` on
  bounded symbols equals Cayley's `borelCalculus`, composing P1 with the bridge above.
* `pmapOfPVM_apply_eq_cfcHom_of_bounded` — the full capstone, to Mathlib's own `cfcHom`.
-/
open MeasureTheory
open Spectra Spectra.Borel Spectra.OneParameterUnitaryGroup Spectra.BorelCFC
open Spectra.Cayley Spectra.YosidaHille
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H}

namespace Spectra.QuantumMechanics.SpectralTheory

/-- **The bridge.** `spectralCalculus (stoneGroup hA)` of a bounded measurable `g : ℝ → ℂ` equals
`borelCalculus (cayley hA)` of the pulled-back symbol `g ∘ inverseMobiusReal hA` — both sides are
characterized by their diagonal integral (`spectralForm_self`, `inner_borelCalculus_self`), and
the two integrals agree by the pushforward identity `borelMeasure_stoneGroup_eq_map` plus a
change of variables. Unconditional: no continuity anywhere. -/
theorem spectralCalculus_stoneGroup_eq_borelCalculus (hA : IsSelfAdjoint A)
    (g : ℝ → ℂ) (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ s, ‖g s‖ ≤ C) :
    spectralCalculus (stoneGroup hA) g hg_meas hg_bdd
      = borelCalculus (cayley hA) (cayley_isStarNormal hA)
          (fun z => g (inverseMobiusReal hA z))
          (hg_meas.comp (inverseMobiusReal_measurable hA))
          (hg_bdd.imp fun _ hC z => hC (inverseMobiusReal hA z)) := by
  refine op_ext_of_inner_self fun ξ => ?_
  rw [inner_spectralCalculus, spectralForm_self (stoneGroup hA) ξ hg_meas hg_bdd,
    borelMeasure_stoneGroup_eq_map hA ξ,
    integral_map (inverseMobiusReal_measurable hA).aemeasurable (by fun_prop),
    inner_borelCalculus_self]

/-- **Matches `cfcHom`, when the pullback is continuous.** The one genuine restriction (see the
module docstring): `g ∘ inverseMobiusReal hA` must be continuous on the whole Cayley spectrum,
including the junk point `w = 1` that `inverseMobiusReal` is discontinuous at. Under that
hypothesis, `spectralCalculus (stoneGroup hA) g` is literally Mathlib's own continuous functional
calculus of the pulled-back symbol. -/
theorem spectralCalculus_stoneGroup_eq_cfcHom (hA : IsSelfAdjoint A)
    (g : ℝ → ℂ) (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ s, ‖g s‖ ≤ C)
    (hcont : Continuous (fun z : spectrum ℂ (cayley hA) => g (inverseMobiusReal hA z))) :
    spectralCalculus (stoneGroup hA) g hg_meas hg_bdd
      = cfcHom (cayley_isStarNormal hA)
          (⟨fun z => g (inverseMobiusReal hA z), hcont⟩ : C(spectrum ℂ (cayley hA), ℂ)) := by
  rw [spectralCalculus_stoneGroup_eq_borelCalculus hA g hg_meas hg_bdd]
  exact borelCalculus_eq_cfcHom (cayley hA) (cayley_isStarNormal hA)
    (⟨fun z => g (inverseMobiusReal hA z), hcont⟩ : C(spectrum ℂ (cayley hA), ℂ))

/-- **The capstone.** The library's own unbounded functional calculus `pmapOfPVM`, on bounded
symbols, equals the Cayley-specific `borelCalculus` — composing P1's reduction to
`spectralCalculus`, `stoneGroup_eq_genToGroup` (P0) to swap groups, and the bridge above. -/
theorem pmapOfPVM_apply_eq_borelCalculus_of_bounded [Nontrivial H] (hA : IsSelfAdjoint A)
    (g : ℝ → ℂ) (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ s, ‖g s‖ ≤ C) (ξ : H)
    (hξ : ξ ∈ ProjValMeasure.pmapDomain (genToGroup hA).toPVM g) :
    pmapOfPVM (genToGroup hA) g hg_meas ⟨ξ, hξ⟩
      = borelCalculus (cayley hA) (cayley_isStarNormal hA)
          (fun z => g (inverseMobiusReal hA z))
          (hg_meas.comp (inverseMobiusReal_measurable hA))
          (hg_bdd.imp fun _ hC z => hC (inverseMobiusReal hA z)) ξ := by
  rw [pmapOfPVM_apply_eq_spectralCalculus_of_bounded (genToGroup hA) g hg_meas hg_bdd ξ hξ,
    ← stoneGroup_eq_genToGroup hA, spectralCalculus_stoneGroup_eq_borelCalculus hA g hg_meas hg_bdd]

/-- **The full capstone.** `pmapOfPVM (genToGroup hA)` — the library's own unbounded functional
calculus of a self-adjoint operator — equals Mathlib's own continuous functional calculus,
pulled back through the Cayley transform, whenever the pullback is continuous. This is the
statement the Cayley directory was ultimately built to reach. -/
theorem pmapOfPVM_apply_eq_cfcHom_of_bounded [Nontrivial H] (hA : IsSelfAdjoint A)
    (g : ℝ → ℂ) (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ s, ‖g s‖ ≤ C)
    (hcont : Continuous (fun z : spectrum ℂ (cayley hA) => g (inverseMobiusReal hA z))) (ξ : H)
    (hξ : ξ ∈ ProjValMeasure.pmapDomain (genToGroup hA).toPVM g) :
    pmapOfPVM (genToGroup hA) g hg_meas ⟨ξ, hξ⟩
      = cfcHom (cayley_isStarNormal hA)
          (⟨fun z => g (inverseMobiusReal hA z), hcont⟩ : C(spectrum ℂ (cayley hA), ℂ)) ξ := by
  rw [pmapOfPVM_apply_eq_spectralCalculus_of_bounded (genToGroup hA) g hg_meas hg_bdd ξ hξ,
    ← stoneGroup_eq_genToGroup hA, spectralCalculus_stoneGroup_eq_cfcHom hA g hg_meas hg_bdd hcont]

end Spectra.QuantumMechanics.SpectralTheory
