/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.Cocycle.ModularConjugationInvolutive
import Spectra.Modular.Cocycle.ModularFlowVacuum
import Spectra.Modular.Cocycle.ModularVacuum
import Spectra.Modular.TomitaTakesaki.ModularFlow
/-!
# Constructing `ModularData` — the R4 existence theorem, up to Tomita's theorem

`ModularData M Ω` bundles eight fields.  Five of them are now **constructed and proved** for any
cyclic separating vector:

1. the modular conjugation `J = modularConjugation` (from the polar decomposition `S = JΔ^{½}`);
2. the modular flow `Δ^{it} = modularFlow` (Cayley → Borel calculus on the self-adjoint `Δ`);
3. **`J² = 1`** (`modularConjugation_involutive` — the Field-3 polar-uniqueness argument);
4. `J Ω = Ω` (`modularConjugation_fixes_vacuum`);
5. `Δ^{it} Ω = Ω` (`modularFlow_fixes_vacuum`).

The remaining three fields are **Tomita's theorem** (`Δ^{it} M Δ^{-it} = M`, both directions) and
**the commutation theorem** (`J M J = M'`).  These are genuinely open research targets of the
project (the RvD / predual programme — see the vault plan); `tomitaTakesaki_exists_of_invariance`
takes exactly them as *typed hypotheses* and discharges everything else.  The full
`tomitaTakesaki_exists` (no hypotheses) is obtained the day those two theorems land — the gap is
now **exactly** these three named statements, nothing else.

## Main statements

* `tomitaTakesaki_exists_of_invariance` — `IsCyclic → IsSeparating → (Tomita) → (commutation) →
  Nonempty (ModularData M Ω)`, with fields 1–5 discharged by the construction.
-/

namespace Spectra.TomitaTakesaki

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

/-- **The R4 existence theorem, up to Tomita's theorem.**  For a cyclic separating `Ω`, the
constructed modular objects `(J, Δ^{it})` inhabit `ModularData M Ω` as soon as the two remaining
fundamental theorems — Tomita invariance `Δ^{it} M Δ^{-it} = M` and the commutation theorem
`J M J = M'` — are supplied.  All five structural fields (including the Field-3 involution
`J² = 1`) are discharged by the construction; the hypotheses are exactly the open research
frontier, isolated as named statements about the *constructed* flow and conjugation. -/
theorem tomitaTakesaki_exists_of_invariance (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)
    (hinto : ∀ (t : ℝ) (x : H →L[ℂ] H), x ∈ M →
      (modularFlow hcyc hsep).U t * x * (modularFlow hcyc hsep).U (-t) ∈ M)
    (honto : ∀ (t : ℝ) (x : H →L[ℂ] H), x ∈ M →
      (modularFlow hcyc hsep).U (-t) * x * (modularFlow hcyc hsep).U t ∈ M)
    (hcomm : ∀ x : H →L[ℂ] H,
      x ∈ M ↔ jConj (modularConjugation hcyc hsep) x ∈ M.commutant) :
    Nonempty (ModularData M Ω) :=
  ⟨{ J := modularConjugation hcyc hsep
     modularFlow := modularFlow hcyc hsep
     J_involutive := modularConjugation_involutive hcyc hsep
     J_fixes_vacuum := modularConjugation_fixes_vacuum hcyc hsep
     modularFlow_fixes_vacuum := modularFlow_fixes_vacuum hcyc hsep
     modularFlow_maps_into := hinto
     modularFlow_maps_onto := honto
     modularConjugation_eq_commutant := hcomm }⟩

end Spectra.TomitaTakesaki
