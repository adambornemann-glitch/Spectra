/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.OneParameterUnitaryGroup.Basic
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.VonNeumannAlgebra.Basic
/-!
# The spatial modular automorphism `σ_t = Ad(U t)` (E2)

For a one-parameter unitary group `U = {U(t)}` on a Hilbert space `H` (e.g. the modular flow
`Δ^{it}`), the spatial conjugation `x ↦ U(t) x U(t)⁻¹` is a `*`-algebra automorphism of the bounded
operators `H →L[ℂ] H`.  This file packages it as an honest `StarAlgEquiv`:

  `modularAut U t : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H)`,   `modularAut U t x = U t * x * U (-t)`.

The heavy lifting is Mathlib's `Unitary.conjStarAlgAut` (conjugation by a unitary element is a
`*`-automorphism, `x ↦ u * x * star u`); the only content here is exhibiting `U t` as a genuine
`unitary (H →L[ℂ] H)` — its inverse is `U (-t) = (U t)†` — and reading the group law through the
functor `t ↦ Ad(U t)`.

## Design: carrier-agnostic, gate-free

`modularAut` is stated for an **arbitrary** `OneParameterUnitaryGroup H`, so the same builder serves
the base modular flow on `H`, the amplified flow on `H2 H = H ⊕ H`, and any other carrier — it is
the `E2` lego the library previously lacked (only the antilinear `jConj` and the
`ModularData`-consuming `modularAutomorphism_mem` existed).  The invariance / Tomita landing
`Δ^{it} M Δ^{-it} = M` is **not** discharged here: `modularAut_mapsTo_of_invariance` takes it as an
explicit hypothesis, keeping this file entirely off the research gates.

## Main statements

* `modularAut U t` — the spatial `*`-automorphism `Ad(U t)`.
* `modularAut_apply` — `modularAut U t x = U t * x * U (-t)`.
* `modularAut_zero`, `modularAut_add` — `Ad(U ·)` is a one-parameter group of automorphisms.
* `modularAut_mapsTo_of_invariance` — under a hypothesised invariance, `σ_t` maps a von Neumann
  algebra into itself (the shape a genuine Tomita theorem would discharge).
-/

open ContinuousLinearMap
open scoped InnerProductSpace

namespace Spectra.TomitaTakesaki

open Spectra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### `U t` as a unitary element -/

/-- `U s * U t = U (s + t)` in the operator ring (the group law, phrased with `*`). -/
lemma U_mul (U : OneParameterUnitaryGroup H) (s t : ℝ) : U.U s * U.U t = U.U (s + t) := by
  ext x
  simpa [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply]
    using (DFunLike.congr_fun (U.group_law s t) x).symm

/-- `U t * U (-t) = 1`: the forward inverse relation. -/
lemma U_mul_U_neg (U : OneParameterUnitaryGroup H) (t : ℝ) : U.U t * U.U (-t) = 1 := by
  rw [U_mul, add_neg_cancel, U.identity, ← ContinuousLinearMap.one_def]

/-- `U (-t) * U t = 1`: the backward inverse relation. -/
lemma U_neg_mul_U (U : OneParameterUnitaryGroup H) (t : ℝ) : U.U (-t) * U.U t = 1 := by
  have h := U_mul_U_neg U (-t); rwa [neg_neg] at h

/-- `U t` is a unitary element of `H →L[ℂ] H` (its adjoint `U (-t)` is a two-sided inverse). -/
lemma unitaryElt_mem (U : OneParameterUnitaryGroup H) (t : ℝ) :
    U.U t ∈ unitary (H →L[ℂ] H) := by
  simp only [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint, ← U.inverse_eq_adjoint]
  exact ⟨U_neg_mul_U U t, U_mul_U_neg U t⟩

/-- `U t` packaged as an element of the unitary group of `H →L[ℂ] H`. -/
noncomputable def unitaryElt (U : OneParameterUnitaryGroup H) (t : ℝ) :
    unitary (H →L[ℂ] H) :=
  ⟨U.U t, unitaryElt_mem U t⟩

@[simp] lemma coe_unitaryElt (U : OneParameterUnitaryGroup H) (t : ℝ) :
    ((unitaryElt U t : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = U.U t := rfl

/-- The inverse (= star) of `unitaryElt U t` is `U (-t)`. -/
@[simp] lemma coe_star_unitaryElt (U : OneParameterUnitaryGroup H) (t : ℝ) :
    ((star (unitaryElt U t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = U.U (-t) := by
  rw [Unitary.coe_star, coe_unitaryElt, ContinuousLinearMap.star_eq_adjoint, ← U.inverse_eq_adjoint]

/-! ### The spatial `*`-automorphism `Ad(U t)` -/

/-- The **spatial modular automorphism** `σ_t = Ad(U t) : x ↦ U t * x * U (-t)`, as a `*`-algebra
automorphism of `H →L[ℂ] H`.  Built from Mathlib's `Unitary.conjStarAlgAut`. -/
noncomputable def modularAut (U : OneParameterUnitaryGroup H) (t : ℝ) :
    (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H) :=
  Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (unitaryElt U t)

@[simp] theorem modularAut_apply (U : OneParameterUnitaryGroup H) (t : ℝ) (x : H →L[ℂ] H) :
    modularAut U t x = U.U t * x * U.U (-t) := by
  simp only [modularAut, Unitary.conjStarAlgAut_apply, coe_unitaryElt,
    ContinuousLinearMap.star_eq_adjoint, ← U.inverse_eq_adjoint]

/-- At `t = 0` the automorphism is the identity. -/
@[simp] theorem modularAut_zero (U : OneParameterUnitaryGroup H) :
    modularAut U 0 = StarAlgEquiv.refl := by
  ext x
  simp only [modularAut_apply, neg_zero, U.identity, StarAlgEquiv.coe_refl, id_eq,
    ← ContinuousLinearMap.one_def, one_mul, mul_one]

/-- `Ad(U ·)` is a one-parameter group: `σ_{s+t} = σ_s ∘ σ_t` (composition of automorphisms). -/
theorem modularAut_add (U : OneParameterUnitaryGroup H) (s t : ℝ) :
    modularAut U (s + t) = (modularAut U s).trans (modularAut U t) := by
  ext x
  simp only [modularAut_apply, StarAlgEquiv.trans_apply]
  rw [show s + t = t + s from add_comm s t, ← U_mul U t s,
    show -(t + s) = -s + -t from by ring, ← U_mul U (-s) (-t)]
  noncomm_ring

/-! ### Conditional Tomita landing

The invariance `U t * M * U (-t) ⊆ M` (Tomita's theorem) is a research node; here it is a
**hypothesis**, never discharged.  Given it, `σ_t` restricts to a self-map of `M`. -/

/-- If the unitary flow leaves a von Neumann algebra `M` invariant (a Tomita-type hypothesis), then
the spatial automorphism `σ_t` maps `M` into itself. -/
theorem modularAut_mapsTo_of_invariance (U : OneParameterUnitaryGroup H) (M : VonNeumannAlgebra H)
    (hinv : ∀ (t : ℝ) (x : H →L[ℂ] H), x ∈ M → U.U t * x * U.U (-t) ∈ M) (t : ℝ) :
    Set.MapsTo (modularAut U t) (M : Set (H →L[ℂ] H)) (M : Set (H →L[ℂ] H)) := by
  intro x hx
  rw [SetLike.mem_coe] at hx ⊢
  rw [modularAut_apply]
  exact hinv t x hx

end Spectra.TomitaTakesaki
