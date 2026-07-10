/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.TomitaTakesaki.VonNeumannTstarT
import Spectra.CayleyTransform.Defs
import Spectra.CayleyTransform.UnitaryGroup
import Spectra.YosidaHille.Helpers
/-!
# The modular flow `Δ^{it}` (R1-link)

With the modular operator `Δ = modularOp M Ω` now constructed as a **self-adjoint**, non-negative
`LinearPMap` (`modularOp_isSelfAdjoint`, von Neumann's `T⋆T` theorem), the **modular flow**
`Δ^{it}` is obtained by feeding `Δ`'s Cayley transform into the project's finished Borel
functional-calculus engine `borelModularGroup`:

* self-adjointness gives vanishing deficiency indices
  (`isSelfAdjoint_to_surjective`: `Δ ± iI` are surjective);
* hence `cayleyTransform` yields a bounded **star-normal** `V` (`cayleyTransform_isStarNormal`);
* `borelModularGroup V` is the strongly continuous one-parameter unitary group of the modular
  symbol `λ^{it}` — the modular flow `Δ^{it}`, exactly the object the field
  `ModularData.modularFlow` expects.

This discharges the **R1-link** step of the Tomita–Takesaki construction: the modular flow is now a
*constructed* `Spectra.OneParameterUnitaryGroup H`, no longer an axiomatized field.

## Remaining for the full identification

Identifying `(modularFlow …).U t` with the genuine complex power `Δ^{it}` (in `cpow` form, via
`modularSymbol_eq_cpow`) requires positivity of the *pulled-back* spectrum
`(inverseMobius z).re > 0` for `z ∈ spectrum V`. Non-negativity of `Δ` (`modularOp_nonneg`) supplies
this through the spectral mapping of the Cayley transform; that identification is developed
alongside the fundamental theorems (R4 — `modularFlow_fixes_vacuum`, Tomita's theorem).
-/

open scoped InnerProductSpace
open Spectra.Cayley Spectra.BorelCFC Spectra.YosidaHille

namespace Spectra.TomitaTakesaki

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

/-- **The modular flow `Δ^{it}`.** The strongly continuous one-parameter unitary group obtained from
the modular operator `Δ = modularOp M Ω` (self-adjoint by von Neumann's `T⋆T` theorem,
`modularOp_isSelfAdjoint`) via its Cayley transform and the Borel functional calculus. This is the
constructed object that inhabits `ModularData.modularFlow`. -/
noncomputable def modularFlow (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    Spectra.OneParameterUnitaryGroup H :=
  borelModularGroup
    (cayleyTransform (modularOp_isSymmetric hcyc)
      (isSelfAdjoint_to_surjective (modularOp_isSelfAdjoint hcyc hsep)).1)
    (cayleyTransform_isStarNormal (modularOp_isSymmetric hcyc)
      (isSelfAdjoint_to_surjective (modularOp_isSelfAdjoint hcyc hsep)).1
      (isSelfAdjoint_to_surjective (modularOp_isSelfAdjoint hcyc hsep)).2)

variable (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)

/-- Each `Δ^{it}` is unitary (preserves the inner product). -/
lemma modularFlow_unitary (t : ℝ) (ψ φ : H) :
    ⟪(modularFlow hcyc hsep).U t ψ, (modularFlow hcyc hsep).U t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ :=
  (modularFlow hcyc hsep).unitary t ψ φ

/-- The group law `Δ^{i(s+t)} = Δ^{is} Δ^{it}`. -/
lemma modularFlow_group_law (s t : ℝ) :
    (modularFlow hcyc hsep).U (s + t)
      = ((modularFlow hcyc hsep).U s).comp ((modularFlow hcyc hsep).U t) :=
  (modularFlow hcyc hsep).group_law s t

/-- `Δ^{i·0} = 1`. -/
lemma modularFlow_zero : (modularFlow hcyc hsep).U 0 = ContinuousLinearMap.id ℂ H :=
  (modularFlow hcyc hsep).identity

/-- The modular flow is strongly continuous in the parameter. -/
lemma modularFlow_strong_continuous (ψ : H) :
    Continuous (fun t : ℝ => (modularFlow hcyc hsep).U t ψ) :=
  (modularFlow hcyc hsep).strong_continuous ψ

end Spectra.TomitaTakesaki
