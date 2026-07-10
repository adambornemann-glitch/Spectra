/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Diagonal.IntegralZ.Shift

/-!
# The head/tail split of the general-`z` resolvent difference quotient

This file rewrites the raw difference quotient `(ih)⁻¹ • (U(h)R(z)φ − R(z)φ)` of the general-`z`
resolvent integral, via the shift lemmas of `Shift.lean`, into the boundary/bulk split that
`GeneratorLim.lean` needs to take the `h → 0` limit and land on the generator identity
`generator_limit_resolventIntegralZ`. Concretely, `GeneratorLim.lean` invokes
`genZ_diffQuotient_pos`/`_neg` (via `.symm`) to rewrite the difference-quotient goal before
applying `Tendsto.congr'`.

The two cases swap which piece is "moving" and which is "fixed": `genZ_diffQuotient_pos` has a
*moving* boundary term over `Set.Ici h` and a *fixed* bulk term over `Set.Ioc 0 h`, while
`genZ_diffQuotient_neg` has a *moving* bulk term over `Set.Ioc h 0` and a *fixed* boundary term
over `Set.Ici 0`.

## Main statements

* `genZ_diffQuotient_pos` — the `h > 0` split into a boundary `Set.Ici h` term and a bulk
  `Set.Ioc 0 h` term.
* `genZ_diffQuotient_neg` — the `h < 0` split into a `Set.Ioc h 0` term and a boundary `Set.Ici 0`
  term.
-/

open Complex
open Spectra.OneParameterUnitaryGroup
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.Resolvent

variable (U_grp : OneParameterUnitaryGroup (H := H))

omit [CompleteSpace H] in
/-- The **reused scalar-smul identity** `(ih)⁻¹ • (-i) • w = -(h⁻¹ • w)`, applying the scalar fact
`genZ_scalar` to an `H`-valued vector. Both `genZ_diffQuotient_pos` and `genZ_diffQuotient_neg` use
this twice each, once per split term. -/
private lemma smul_diffQuotient_scalar (h : ℝ) (w : H) :
    (I * (h : ℂ))⁻¹ • (-I) • w = -((h : ℂ)⁻¹ • w) := by
  rw [smul_smul, genZ_scalar h, neg_smul]

/-- For `h > 0` the difference quotient `(I·h)⁻¹ · (U(h) - 1)` applied to `resolventIntegralZ z φ`
splits into a boundary `Set.Ici h` term and a bulk `Set.Ioc 0 h` term. -/
lemma genZ_diffQuotient_pos {z : ℂ} (hz : z.im < 0) (φ : H) (h : ℝ) (hh : h > 0) :
    ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralZ U_grp z φ) -
        resolventIntegralZ U_grp z φ) =
      -((h : ℂ)⁻¹ • (cexp (I * z * (h : ℂ)) - 1) •
          ∫ t in Set.Ici h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) +
      ((h : ℂ)⁻¹ • ∫ t in Set.Ioc 0 h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) := by
  rw [unitary_shift_resolventIntegralZ U_grp hz φ h hh, smul_sub,
      smul_diffQuotient_scalar h
        ((cexp (I * z * (h : ℂ)) - 1) •
          ∫ t in Set.Ici h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ),
      smul_diffQuotient_scalar h (∫ t in Set.Ioc 0 h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ),
      sub_neg_eq_add]

/-- For `h < 0` the difference quotient `(I·h)⁻¹ · (U(h) - 1)` applied to `resolventIntegralZ z φ`
splits into a `Set.Ioc h 0` term and a boundary `Set.Ici 0` term. -/
lemma genZ_diffQuotient_neg {z : ℂ} (hz : z.im < 0) (φ : H) (h : ℝ) (hh : h < 0) :
    ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralZ U_grp z φ) -
        resolventIntegralZ U_grp z φ) =
      (-(h : ℂ)⁻¹ • cexp (I * z * (h : ℂ)) •
          ∫ t in Set.Ioc h 0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) +
      (-(h : ℂ)⁻¹ • (cexp (I * z * (h : ℂ)) - 1) •
          ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) := by
  rw [unitary_shift_resolventIntegralZ_neg U_grp hz φ h hh, smul_add,
      smul_diffQuotient_scalar h
        (cexp (I * z * (h : ℂ)) • ∫ t in Set.Ioc h 0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ),
      smul_diffQuotient_scalar h
        ((cexp (I * z * (h : ℂ)) - 1) •
          ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ),
      neg_smul, neg_smul]

end Spectra.Resolvent
