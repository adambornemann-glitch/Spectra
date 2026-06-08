/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: PeriodicStrip/API.lean
-/
import Spectra.ModularTheory.KMS.PeriodicStrip.Defs
import Spectra.ModularTheory.KMS.PeriodicStrip.IndexProps
import Spectra.ModularTheory.KMS.PeriodicStrip.ExtensionProps
import Spectra.ModularTheory.KMS.PeriodicStrip.Hadamard

open Complex Set Filter Topology Int MeasureTheory
namespace Spectra.PeriodicHolomorphic

/-! ## The Main Theorem -/

/-- **Periodic Strip Extension Theorem**

If F is holomorphic on the open strip, continuous on the closed strip,
bounded, and satisfies F(t) = F(t + iβ) for all real t, then F extends
to a bounded entire function that agrees with F on the strip.

Combined with Liouville's theorem, this implies F is constant.
-/
lemma periodic_strip_extension
    (F : ℂ → ℂ) (hβ : 0 < β)
    (_hholo : DifferentiableOn ℂ F (Strip β))
    (hcont : ContinuousOn F (ClosedStrip β))
    (hbdd : BddAbove (norm '' (F '' ClosedStrip β)))
    (hperiod : ∀ t : ℝ, F (realToLower t) = F (realToUpper β t))
    /- Morera: the periodic extension is entire -/
    (hEntire : Differentiable ℂ (periodicExtension F β)) :
    ∃ G : ℂ → ℂ,
      Differentiable ℂ G ∧
      Bornology.IsBounded (Set.range G) ∧
      (∀ z ∈ ClosedStrip β, G z = F z) :=
  ⟨periodicExtension F β,
   hEntire,
   periodicExtension_bounded F hβ hbdd,
   fun _z hz => periodicExtension_eq_on_strip F hβ hcont hperiod hz⟩


/-! ## Application: Periodic Functions on Strips are Constant -/

/-- A holomorphic function on a strip with matching boundary values is constant.

This is the key result used in proving KMS states are time-invariant.
-/
lemma periodic_strip_is_constant
    (F : ℂ → ℂ) (hβ : 0 < β)
    (hholo : DifferentiableOn ℂ F (Strip β))
    (hcont : ContinuousOn F (ClosedStrip β))
    (hbdd : BddAbove (norm '' (F '' ClosedStrip β)))
    (hperiod : ∀ t : ℝ, F (realToLower t) = F (realToUpper β t))
    /- Morera: the periodic extension is entire -/
    (hEntire : Differentiable ℂ (periodicExtension F β)) :
    ∃ c : ℂ, ∀ z ∈ ClosedStrip β, F z = c := by
  -- Get the bounded entire extension
  obtain ⟨G, G_entire, G_bdd, G_extends⟩ :=
    periodic_strip_extension F hβ hholo hcont hbdd hperiod hEntire
  -- By Liouville, G is constant
  have G_const : ∀ z w : ℂ, G z = G w :=
    fun z w => G_entire.apply_eq_apply_of_bounded G_bdd z w
  -- F agrees with G on the strip, so F is also constant there
  use G 0
  intro z hz
  rw [(G_extends z hz).symm, G_const z 0]

end Spectra.PeriodicHolomorphic
