/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Bochner.GNS.PreHilbert.Linearity

/-!
# Conjugate Symmetry of the GNS Pre-Inner Product

Once `f : ℝ → ℂ` is Hermitian (`f(-t) = conj(f(t))`), the GNS pre-inner product `pdInner f`
is conjugate-symmetric, `⟨β, α⟩ = conj ⟨α, β⟩`. Combined with the right-linearity established
unconditionally in `Linearity.lean`, this upgrades `pdInner f` to a genuine sesquilinear form:
conjugate-linear in the first argument, linear in the second.

## Main statements

* `pdInner_conj_symm` — `⟨β, α⟩_f = conj ⟨α, β⟩_f`.
* `pdInner_add_left`, `pdInner_smul_left`, `pdInner_sub_left` — conjugate-linearity of
  `pdInner f` in its first argument, derived from `pdInner_conj_symm` plus the
  right-linearity lemmas of `Linearity.lean`.
-/

open Finsupp
open Spectra.PositiveDefinite

namespace Spectra.Bochner.GNS

-- §4  Conjugate symmetry

/-- **Conjugate symmetry**: `⟨β, α⟩_f = conj ⟨α, β⟩_f`.

This is where the Hermitian condition `f(-t) = conj(f(t))` enters. -/
lemma pdInner_conj_symm {f : ℝ → ℂ} (hH : IsHermitian f) (α β : ℝ →₀ ℂ) :
    pdInner f β α = starRingEnd ℂ (pdInner f α β) := by
  simp only [pdInner, Finsupp.sum]
  simp_rw [map_sum (starRingEnd ℂ), map_mul, starRingEnd_self_apply]
  simp_rw [show ∀ s t : ℝ, starRingEnd ℂ (f (s - t)) = f (t - s) from
    fun s t => by rw [← hH (s - t), neg_sub]]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro t _
  ring

/-- Conjugate-linearity in the first argument (corollary of symmetry + linearity):
`⟨α₁ + α₂, β⟩ = ⟨α₁, β⟩ + ⟨α₂, β⟩`. -/
lemma pdInner_add_left {f : ℝ → ℂ} (hH : IsHermitian f) (α₁ α₂ β : ℝ →₀ ℂ) :
    pdInner f (α₁ + α₂) β = pdInner f α₁ β + pdInner f α₂ β := by
  rw [pdInner_conj_symm hH, pdInner_add_right, map_add,
      pdInner_conj_symm hH α₁, pdInner_conj_symm hH α₂]
  simp only [starRingEnd_self_apply]

/-- Conjugate scalar multiplication in first argument:
`⟨c • α, β⟩ = c̄ · ⟨α, β⟩`. -/
lemma pdInner_smul_left {f : ℝ → ℂ} (hH : IsHermitian f) (c : ℂ) (α β : ℝ →₀ ℂ) :
    pdInner f (c • α) β = starRingEnd ℂ c * pdInner f α β := by
  rw [pdInner_conj_symm hH, pdInner_smul_right, map_mul,
      pdInner_conj_symm hH α]
  simp only [starRingEnd_self_apply]

/-- Conjugate-linearity (subtraction) in the first argument (corollary of symmetry +
linearity): `⟨α - β, γ⟩ = ⟨α, γ⟩ - ⟨β, γ⟩`. -/
lemma pdInner_sub_left {f : ℝ → ℂ} (hH : IsHermitian f) (α β γ : ℝ →₀ ℂ) :
    pdInner f (α - β) γ = pdInner f α γ - pdInner f β γ := by
  rw [sub_eq_add_neg, pdInner_add_left hH, show -β = (-1 : ℂ) • β from by ext; simp,
      pdInner_smul_left hH, map_neg, map_one, neg_one_mul]
  ring

end Spectra.Bochner.GNS
