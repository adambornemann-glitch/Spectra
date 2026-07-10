/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Bochner.GNS.PreHilbert.PosSemiDef

/-!
# The Translation Action on the GNS Pre-Hilbert Space

Establishes the basic algebraic and metric properties of `translate t = Finsupp.mapDomain (· + t)`:
it is additive and homogeneous (jointly, ℂ-linear), unital, forms a one-parameter group under
composition, and is an isometry of `pdInner`. Together these are exactly the facts needed to
later build the ℂ-linear map `translateLM`, the descended `quotientTranslate`, and the unitary
representation of `(ℝ, +)` in `Representation/Lemmas.lean`.

## Main statements

* `translate_add`, `translate_smul` — jointly, `translate t` is ℂ-linear.
* `translate_zero` — `U(0) = id`.
* `translate_translate` — the group law `U(s) ∘ U(t) = U(s + t)`.
* `pdInner_translate` — `U(t)` is an isometry of `pdInner f`.
-/

open Finsupp

namespace Spectra.Bochner.GNS

-- §6  The translation action

/-- Translation on a point mass: `U(t)(c · δ_s) = c · δ_{s+t}`. -/
@[simp]
lemma translate_single (t s : ℝ) (c : ℂ) :
    translate t (Finsupp.single s c) = Finsupp.single (s + t) c := by
  unfold translate
  exact Finsupp.mapDomain_single

/-- Translation is additive: `U(t)(α + β) = U(t)α + U(t)β`. -/
lemma translate_add (t : ℝ) (α β : ℝ →₀ ℂ) :
    translate t (α + β) = translate t α + translate t β := by
  unfold translate
  exact Finsupp.mapDomain_add

/-- Translation is ℂ-homogeneous: `U(t)(c · α) = c · U(t)α`. Together with `translate_add`,
this makes `translate t` ℂ-linear. -/
lemma translate_smul (t : ℝ) (c : ℂ) (α : ℝ →₀ ℂ) :
    translate t (c • α) = c • translate t α := by
  unfold translate
  exact Finsupp.mapDomain_smul c α

/-- Identity: `U(0) = id`. -/
@[simp]
lemma translate_zero (α : ℝ →₀ ℂ) :
    translate 0 α = α := by
  unfold translate
  simp only [add_zero]
  ext x; exact mapDomain_apply (fun ⦃a₁ a₂⦄ a => a) α x

/-- Group law: `U(s)(U(t)(α)) = U(s + t)(α)`.

Proof: `mapDomain (· + s) ∘ mapDomain (· + t) = mapDomain (· + (t + s))`
since `(x + t) + s = x + (t + s)`. Then use `t + s = s + t`. -/
lemma translate_translate (s t : ℝ) (α : ℝ →₀ ℂ) :
    translate s (translate t α) = translate (s + t) α := by
  unfold translate
  rw [← @mapDomain_comp]
  congr 1; funext x
  change x + t + s = x + (s + t)
  ring

/-- Absorbing a `mapDomain (· + t)` shift into a `Finsupp.sum`, provided the summand `h` is
zero at `0` and linear in the coefficient:
`(mapDomain (·+t) γ).sum h = γ.sum (fun a m => h (a + t) m)`. Both sums unfolded in
`pdInner_translate` (the outer shift by `t`, the inner shift by `r + t`) instantiate this one
shape, with `h` built from `pdInner`'s summand `starRingEnd ℂ · * · * f (· - ·)`. -/
private lemma sum_mapDomain_shift (γ : ℝ →₀ ℂ) (t : ℝ) (h : ℝ → ℂ → ℂ)
    (h_zero : ∀ s, h s 0 = 0) (h_add : ∀ s c₁ c₂, h s (c₁ + c₂) = h s c₁ + h s c₂) :
    (mapDomain (· + t) γ).sum h = γ.sum (fun a m => h (a + t) m) :=
  Finsupp.sum_mapDomain_index h_zero h_add

/-- **Translation isometry**: `⟨U(t)α, U(t)β⟩_f = ⟨α, β⟩_f`.

The kernel `f(s - r)` is translation-invariant: `(s+t) - (r+t) = s - r`.
So translating both arguments does not change the inner product.

This is why `U(t)` extends to a unitary operator on the completion. -/
lemma pdInner_translate {f : ℝ → ℂ} (t : ℝ) (α β : ℝ →₀ ℂ) :
    pdInner f (translate t α) (translate t β) = pdInner f α β := by
  simp only [pdInner, translate]
  rw [Finsupp.sum_mapDomain_index
    (fun r => by simp [Finsupp.sum])
    (fun r c₁ c₂ => by
      simp only [Finsupp.sum, map_add, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro s _; ring)]
  have h_inner : ∀ (r : ℝ) (cr : ℂ),
      (mapDomain (· + t) β).sum (fun s ds => starRingEnd ℂ cr * ds * f (s - (r + t))) =
      β.sum (fun s ds => starRingEnd ℂ cr * ds * f (s - r)) := by
    intro r cr
    have key := sum_mapDomain_shift β t (fun s ds => starRingEnd ℂ cr * ds * f (s - (r + t)))
      (fun s => by simp) (fun s c₁ c₂ => by ring)
    simpa [add_sub_add_right_eq_sub] using key
  simp_rw [h_inner]

end Spectra.Bochner.GNS
