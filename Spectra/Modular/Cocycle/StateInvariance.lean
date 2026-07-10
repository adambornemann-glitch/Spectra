/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.Cocycle.SpatialAutomorphism
import Spectra.Modular.Cocycle.ModularFlowVacuum
import Spectra.Modular.TomitaTakesaki.Basic
import Spectra.Modular.TomitaTakesaki.ModularFlow
/-!
# Vector-state invariance of the modular automorphism group (E3)

For the vector state `ω(x) = ⟪Ω, x Ω⟫` and the spatial modular automorphism
`σ_t = Ad(Δ^{it}) : x ↦ Δ^{it} x Δ^{-it}` (packaged as `modularAut` in
`SpatialAutomorphism.lean`), this file proves the KMS-zeroth-law invariance

  `ω (σ_t x) = ω (x)`.

The mechanism is one line of physics: `Δ^{it} Ω = Ω`, so the right factor `Δ^{-it}` is absorbed
by the vector `Ω`, and the left factor `Δ^{it}` is absorbed by unitarity of the flow after
rewriting the bra `Ω = Δ^{it} Ω`.

## Main statements

The result is stated three ways, from generic to bundled:

* `inner_modularAut_vacuum` — for **any** one-parameter unitary group `U` fixing a vector `Ω`
  (`∀ t, U t Ω = Ω`), the vector state of `Ω` is invariant under `modularAut U t`.
* `inner_modularAut_modularFlow_vacuum` — **E3, unconditional** for the *constructed* modular
  flow `Δ^{it} = modularFlow hcyc hsep`: no `ModularData` hypothesis is needed, since
  `Δ^{it} Ω = Ω` is a proved theorem (`modularFlow_fixes_vacuum`).
* `ModularData.inner_modularAut_vacuum` — the conditional bundle form, for any `D : ModularData
  M Ω`, using the structure field `D.modularFlow_fixes_vacuum`.

None of these restrict `x` to the algebra `M`: invariance of the vector state holds for every
bounded operator, so the `x ∈ M` restriction (and Tomita's `σ_t(M) = M`) is orthogonal to E3.
-/

open ContinuousLinearMap
open scoped InnerProductSpace

namespace Spectra.TomitaTakesaki

open Spectra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Generic form: any unitary flow fixing `Ω` -/

/-- **Vector-state invariance, generic form.** If a one-parameter unitary group `U` fixes the
vector `Ω`, then the vector state `ω(x) = ⟪Ω, x Ω⟫` is invariant under the spatial automorphism
`σ_t = Ad(U t)`: `ω (σ_t x) = ω x` for every bounded operator `x`. -/
theorem inner_modularAut_vacuum (U : OneParameterUnitaryGroup H) {Ω : H}
    (hfix : ∀ t : ℝ, U.U t Ω = Ω) (t : ℝ) (x : H →L[ℂ] H) :
    ⟪Ω, (modularAut U t x) Ω⟫_ℂ = ⟪Ω, x Ω⟫_ℂ := by
  rw [modularAut_apply]
  have habs : (U.U t * x * U.U (-t)) Ω = U.U t (x Ω) := by
    simp only [ContinuousLinearMap.mul_apply, hfix (-t)]
  calc ⟪Ω, (U.U t * x * U.U (-t)) Ω⟫_ℂ
      = ⟪U.U t Ω, U.U t (x Ω)⟫_ℂ := by rw [habs, hfix t]
    _ = ⟪Ω, x Ω⟫_ℂ := U.unitary t Ω (x Ω)

/-! ### E3, unconditional: the constructed modular flow -/

variable {M : VonNeumannAlgebra H} {Ω : H}

/-- **E3: the vector state is invariant under the modular flow** — with **no** `ModularData`
hypothesis.  The constructed `Δ^{it} = modularFlow hcyc hsep` and the proved vacuum fixing
`Δ^{it} Ω = Ω` (`modularFlow_fixes_vacuum`) suffice:
`⟪Ω, (Δ^{it} x Δ^{-it}) Ω⟫ = ⟪Ω, x Ω⟫` for every bounded operator `x`. -/
theorem inner_modularAut_modularFlow_vacuum (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)
    (t : ℝ) (x : H →L[ℂ] H) :
    ⟪Ω, (modularAut (modularFlow hcyc hsep) t x) Ω⟫_ℂ = ⟪Ω, x Ω⟫_ℂ :=
  inner_modularAut_vacuum _ (modularFlow_fixes_vacuum hcyc hsep) t x

/-! ### Bundled form: any `ModularData` -/

/-- **Vector-state invariance, bundled form.** For any modular data `D : ModularData M Ω`, the
vector state of `Ω` is invariant under the modular automorphism group of `D.modularFlow`, via
the structure field `D.modularFlow_fixes_vacuum`. -/
theorem ModularData.inner_modularAut_vacuum (D : ModularData M Ω) (t : ℝ) (x : H →L[ℂ] H) :
    ⟪Ω, (modularAut D.modularFlow t x) Ω⟫_ℂ = ⟪Ω, x Ω⟫_ℂ :=
  Spectra.TomitaTakesaki.inner_modularAut_vacuum _ D.modularFlow_fixes_vacuum t x

end Spectra.TomitaTakesaki
