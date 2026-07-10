/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Diagonal.IntegralZ.Tendsto

/-!
# Bulk difference-quotient limits for the general-`z` resolvent integral

This file proves the two "bulk" `Tendsto` facts that feed the generator-recovery argument in
`GeneratorLim.lean`: as `h → 0` from either side, the scaled bulk integral term appearing in the
difference quotient of `resolventIntegralZ` converges to `-(iz) • ∫_{Ici 0} e^{-izt}U(t)φ dt`.

The two cases are proved by essentially the same computation — a scalar bulk-derivative limit
`(e^{izh}-1)/h → iz` smul'd against a convergent integral — but they are genuinely asymmetric in
their hypotheses. `genZ_bulk_pos` integrates over the *moving* set `Set.Ici h`, so it needs
`z.im < 0` to invoke tail-integrability as `h → 0⁺` (via `tendsto_integral_Ici_expZ_unitary`).
`genZ_bulk_neg` integrates over the *fixed* set `Set.Ici 0` throughout, so the integral factor is
simply a constant as `h → 0⁻` and no integrability hypothesis on `z` is required at all.

## Main statements

* `genZ_bulk_pos` — the right-sided (`h → 0⁺`) bulk limit, over the moving set `Set.Ici h`.
* `genZ_bulk_neg` — the left-sided (`h → 0⁻`) bulk limit, over the fixed set `Set.Ici 0`.
-/

open Complex Filter Topology
open Spectra.OneParameterUnitaryGroup
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.Resolvent

variable (U_grp : OneParameterUnitaryGroup (H := H))

omit [CompleteSpace H] in
/-- The shared final step of `genZ_bulk_pos`/`genZ_bulk_neg`: once a `Tendsto` for the raw
`div`-quotient smul'd against the integral has been established, rewriting `div_eq_inv_mul` and
regrouping the `smul` matches the `-((h:ℂ)⁻¹ • ...)`-shaped goal. -/
private lemma congr_div_smul {f : ℝ → ℂ} {g : ℝ → H} {s : Set ℝ} {c : H}
    (h_prod : Tendsto (fun h : ℝ => (f h / (h : ℂ)) • g h) (𝓝[s] (0 : ℝ)) (𝓝 c)) :
    Tendsto (fun h : ℝ => (h : ℂ)⁻¹ • f h • g h) (𝓝[s] (0 : ℝ)) (𝓝 c) := by
  apply Tendsto.congr' _ h_prod
  filter_upwards [self_mem_nhdsWithin] with h _hh
  rw [div_eq_inv_mul, ← smul_smul]

/-- For `Im z < 0`, the right difference quotient of `∫_{Ici h} e^{-izt}U(t)φ dt` tends to
`-(iz)•∫_{Ici 0} e^{-izt}U(t)φ dt` as `h → 0⁺`. -/
lemma genZ_bulk_pos {z : ℂ} (hz : z.im < 0) (φ : H) :
    Tendsto (fun h : ℝ => -((h : ℂ)⁻¹ • (cexp (I * z * (h : ℂ)) - 1) •
        ∫ t in Set.Ici h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ))
      (𝓝[>] 0)
      (𝓝 (-((I * z) • ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ))) := by
  apply Tendsto.neg
  have he_cplx : Tendsto (fun h : ℝ => (cexp (I * z * (h : ℂ)) - 1) / (h : ℂ))
      (𝓝[>] 0) (𝓝 (I * z)) :=
    tendsto_cexp_mul_sub_one_div.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))
  have hi : Tendsto (fun h : ℝ => ∫ t in Set.Ici h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)
      (𝓝[>] 0) (𝓝 (∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)) :=
    (tendsto_integral_Ici_expZ_unitary U_grp hz φ).mono_left nhdsWithin_le_nhds
  have h_prod : Tendsto (fun h : ℝ => ((cexp (I * z * (h : ℂ)) - 1) / (h : ℂ)) •
      ∫ t in Set.Ici h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)
      (𝓝[>] 0)
      (𝓝 ((I * z) • ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)) :=
    Tendsto.smul he_cplx hi
  exact congr_div_smul h_prod

/-- The left difference quotient of `(e^{izh}-1)•∫_{Ici 0} e^{-izt}U(t)φ dt` tends to
`-(iz)•∫_{Ici 0} e^{-izt}U(t)φ dt` as `h → 0⁻`. Unlike `genZ_bulk_pos`, this needs no `z.im < 0`
hypothesis: the integral here is over the *fixed* set `Set.Ici 0`, not the *moving* `Set.Ici h`,
so it is simply constant in `h` and no tail-integrability argument is required. -/
lemma genZ_bulk_neg {z : ℂ} (φ : H) :
    Tendsto (fun h : ℝ => -(h : ℂ)⁻¹ • (cexp (I * z * (h : ℂ)) - 1) •
        ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)
      (𝓝[<] 0)
      (𝓝 (-((I * z) • ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ))) := by
  have he_cplx : Tendsto (fun h : ℝ => (cexp (I * z * (h : ℂ)) - 1) / (h : ℂ))
      (𝓝[<] 0) (𝓝 (I * z)) :=
    tendsto_cexp_mul_sub_one_div.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_lt hx))
  have h_prod : Tendsto (fun h : ℝ => ((cexp (I * z * (h : ℂ)) - 1) / (h : ℂ)) •
      ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)
      (𝓝[<] 0)
      (𝓝 ((I * z) • ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)) :=
    Tendsto.smul he_cplx tendsto_const_nhds
  have h_inner := congr_div_smul h_prod
  apply Tendsto.congr' _ h_inner.neg
  filter_upwards with h
  rw [neg_smul]

end Spectra.Resolvent
