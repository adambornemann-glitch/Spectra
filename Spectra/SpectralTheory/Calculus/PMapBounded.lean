/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SpectralTheory.Calculus.PMapOfPVM
/-!
# `pmapOfPVM` agrees with the bounded calculus `spectralCalculus` on bounded symbols

The unbounded functional calculus `pmapOfPVM U_grp f hf` is built as the strong `L²`-limit of the
bounded calculus `spectralCalculus U_grp` applied to the truncations `truncSym f n`. When `f`
itself is bounded, the truncations stabilize: for `n ≥ ⌈C⌉₊` (`C` a global bound on `f`), every
`s` already satisfies `‖f s‖ ≤ n`, so `truncSym f n = f` on the nose and the "limit" sequence is
eventually constant. This collapses `pmapOfPVM` to `spectralCalculus` on bounded symbols, and with
it inherits `spectralCalculus_mul` — the **product law** the general unbounded calculus is still
missing (`Spectra-Vault/Projects/Modular Theory/Project.md`, R2 remainder).

**Scope honesty.** This closes the product law only for *bounded* symbols. The general unbounded
product law `(∫f dP)(∫g dP) = ∫(f·g) dP` — needed, for instance, for `(Δ^{½})² = Δ` where `√` is
unbounded on an unbounded spectrum — remains open; nothing here should be read as discharging it.

## Main results

* `integrable_sq_of_bounded` — a bounded measurable symbol is always `L²`-integrable against every
  diagonal measure (finite measure + bounded integrand).
* `mem_pmapDomain_of_bounded` — consequently the *whole space* lies in `pmapDomain` for bounded `f`.
* `pmapOfPVM_apply_eq_spectralCalculus_of_bounded` — **the reduction**: on any membership witness,
  `pmapOfPVM U_grp f hf ⟨ξ, hξ⟩ = spectralCalculus U_grp f hf hbdd ξ`.
* `pmapOfPVM_mul_of_bounded` — **the product law for bounded symbols**: composing `pmapOfPVM f`
  after `pmapOfPVM g` equals `pmapOfPVM (f · g)`, transported from `spectralCalculus_mul`.
-/
open Spectra Complex MeasureTheory Filter Topology
open Spectra.Borel Spectra.OneParameterUnitaryGroup
open scoped InnerProductSpace

namespace Spectra.QuantumMechanics.SpectralTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-! ## Bounded symbols are always in the natural domain -/

/-- A bounded measurable symbol is `L²`-integrable against every diagonal measure: the diagonal
measures are finite (`borelMeasure_isFiniteMeasure`), and a bounded measurable integrand is
integrable against any finite measure. -/
theorem integrable_sq_of_bounded (f : ℝ → ℂ) (hf : Measurable f)
    (hbdd : ∃ C, ∀ s, ‖f s‖ ≤ C) (ξ : H) :
    Integrable (fun s => ‖f s‖ ^ 2) (borelMeasure U_grp ξ) := by
  haveI : IsFiniteMeasure (borelMeasure U_grp ξ) := borelMeasure_isFiniteMeasure U_grp ξ
  obtain ⟨C, hC⟩ := hbdd
  refine Integrable.mono' (integrable_const (C ^ 2)) (hf.norm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [hC s, norm_nonneg (f s)]

/-- Consequently, every `ξ` lies in `pmapDomain U_grp.toPVM f` when `f` is bounded — the natural
domain is the *whole space* for bounded symbols. -/
theorem mem_pmapDomain_of_bounded (f : ℝ → ℂ) (hf : Measurable f)
    (hbdd : ∃ C, ∀ s, ‖f s‖ ≤ C) (ξ : H) :
    ξ ∈ ProjValMeasure.pmapDomain U_grp.toPVM f :=
  (ProjValMeasure.mem_pmapDomain U_grp.toPVM).mpr (integrable_sq_of_bounded U_grp f hf hbdd ξ)

/-! ## The reduction to the bounded calculus -/

/-- **The reduction.** For a bounded symbol, `pmapOfPVM` agrees with `spectralCalculus` at every
point. The truncation sequence defining `pmapOfPVM` is eventually *constant* once the truncation
index exceeds the global bound `C` on `f` (`truncSym f n = f` for `n ≥ ⌈C⌉₊`), so its limit is
that constant value, which by definition is `spectralCalculus U_grp f hf hbdd ξ`;
`pmapOfPVM_apply_tendsto` identifies the same limit with `pmapOfPVM U_grp f hf ⟨ξ, hξ⟩`, and
uniqueness of limits closes the equality. -/
theorem pmapOfPVM_apply_eq_spectralCalculus_of_bounded (f : ℝ → ℂ) (hf : Measurable f)
    (hbdd : ∃ C, ∀ s, ‖f s‖ ≤ C) (ξ : H) (hξ : ξ ∈ ProjValMeasure.pmapDomain U_grp.toPVM f) :
    pmapOfPVM U_grp f hf ⟨ξ, hξ⟩ = spectralCalculus U_grp f hf hbdd ξ := by
  have htend2 := pmapOfPVM_apply_tendsto U_grp f hf hξ
  have hev : ∀ᶠ n : ℕ in atTop, spectralCalculus U_grp f hf hbdd ξ = pmapTrunc U_grp f hf n ξ := by
    obtain ⟨C, hC⟩ := hbdd
    filter_upwards [Filter.eventually_ge_atTop ⌈C⌉₊] with n hn
    have htrunc_eq : truncSym f n = f := by
      funext s
      rw [truncSym_apply, if_pos ((hC s).trans ((Nat.le_ceil C).trans (Nat.cast_le.mpr hn)))]
    rw [pmapTrunc_apply, spectralCalculus_congr U_grp htrunc_eq.symm hf ⟨C, hC⟩
      (measurable_truncSym hf n) (truncSym_bdd f n)]
  have htend1 : Tendsto (fun n => pmapTrunc U_grp f hf n ξ) atTop
      (𝓝 (spectralCalculus U_grp f hf hbdd ξ)) :=
    Filter.Tendsto.congr' hev tendsto_const_nhds
  exact tendsto_nhds_unique htend2 htend1

/-! ## The product law for bounded symbols -/

/-- **The product law, for bounded symbols.** `pmapOfPVM f` composed with `pmapOfPVM g` equals
`pmapOfPVM (f · g)` — transported from `spectralCalculus_mul` through the reduction lemma above,
applied three times. The membership hypotheses are automatic (`mem_pmapDomain_of_bounded`) but
left generic here so the statement composes with any witness. -/
theorem pmapOfPVM_mul_of_bounded (f g : ℝ → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hfbdd : ∃ C, ∀ s, ‖f s‖ ≤ C) (hgbdd : ∃ C, ∀ s, ‖g s‖ ≤ C)
    (hfg : Measurable fun s => f s * g s) (hfgbdd : ∃ C, ∀ s, ‖f s * g s‖ ≤ C)
    (ξ : H) (hξg : ξ ∈ ProjValMeasure.pmapDomain U_grp.toPVM g)
    (hξfg : (pmapOfPVM U_grp g hg ⟨ξ, hξg⟩ : H) ∈ ProjValMeasure.pmapDomain U_grp.toPVM f)
    (hξprod : ξ ∈ ProjValMeasure.pmapDomain U_grp.toPVM (fun s => f s * g s)) :
    pmapOfPVM U_grp f hf ⟨pmapOfPVM U_grp g hg ⟨ξ, hξg⟩, hξfg⟩
      = pmapOfPVM U_grp (fun s => f s * g s) hfg ⟨ξ, hξprod⟩ := by
  -- Rewrite the *outer* `pmapOfPVM f` application first: this discharges `hξfg` from the goal in
  -- one step, before its type (which mentions the inner `pmapOfPVM g` value) could obstruct a
  -- dependent rewrite of that inner value.
  rw [pmapOfPVM_apply_eq_spectralCalculus_of_bounded U_grp f hf hfbdd _ hξfg,
    pmapOfPVM_apply_eq_spectralCalculus_of_bounded U_grp g hg hgbdd ξ hξg,
    pmapOfPVM_apply_eq_spectralCalculus_of_bounded U_grp (fun s => f s * g s) hfg hfgbdd ξ hξprod,
    ← ContinuousLinearMap.mul_apply, spectralCalculus_mul U_grp g f hg hgbdd hf hfbdd hfg hfgbdd]

end Spectra.QuantumMechanics.SpectralTheory
