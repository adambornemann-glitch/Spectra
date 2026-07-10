/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Bochner.GNS.PreHilbert.Evolution

/-!
# Linearity of the GNS Pre-Inner Product in the Second Argument

Establishes that `pdInner f` is linear in its second argument, for an arbitrary
`f : ℝ → ℂ` (no Hermitian hypothesis is needed here, matching the physics convention
of `Defs.lean`: conjugate-linear in the first slot, linear in the second). Conjugate-linearity
in the *first* slot is derived separately in `Conjugate.lean`, once `IsHermitian f` is
available to relate the two slots via `pdInner_conj_symm`.

## Main statements

* `pdInner_add_right` — `⟨α, β₁ + β₂⟩ = ⟨α, β₁⟩ + ⟨α, β₂⟩`.
* `pdInner_smul_right` — `⟨α, c • β⟩ = c · ⟨α, β⟩`.
* `pdInner_sub_right` — `⟨α, β₁ - β₂⟩ = ⟨α, β₁⟩ - ⟨α, β₂⟩`.
-/

open Finsupp

namespace Spectra.Bochner.GNS

-- §3  Zero and linearity

/-- `⟨0, β⟩ = 0`: the outer `Finsupp.sum` over the zero finsupp is the empty sum. -/
lemma pdInner_zero_left (f : ℝ → ℂ) (β : ℝ →₀ ℂ) :
    pdInner f 0 β = 0 := by
  unfold pdInner; simp [Finsupp.sum]

/-- `⟨α, 0⟩ = 0`: each inner `Finsupp.sum` over the zero finsupp vanishes. -/
lemma pdInner_zero_right (f : ℝ → ℂ) (α : ℝ →₀ ℂ) :
    pdInner f α 0 = 0 := by
  unfold pdInner; simp [Finsupp.sum_zero_index]

/-- Linearity in the second argument: `⟨α, β₁ + β₂⟩ = ⟨α, β₁⟩ + ⟨α, β₂⟩`.

Proof: expand the inner sum using `Finsupp.sum_add_index`. -/
lemma pdInner_add_right (f : ℝ → ℂ) (α β₁ β₂ : ℝ →₀ ℂ) :
    pdInner f α (β₁ + β₂) = pdInner f α β₁ + pdInner f α β₂ := by
  simp only [pdInner]
  -- Step 1: split inner sum — need ∀ t ct so simp_rw can rewrite under the outer binder
  have h_inner : ∀ (t : ℝ) (ct : ℂ),
      (β₁ + β₂).sum (fun s ds => starRingEnd ℂ ct * ds * f (s - t)) =
      β₁.sum (fun s ds => starRingEnd ℂ ct * ds * f (s - t)) +
      β₂.sum (fun s ds => starRingEnd ℂ ct * ds * f (s - t)) :=
    fun t ct => Finsupp.sum_add_index (fun s => by simp)
      (fun s _d₁ d₂ => by ring_nf; simp only [implies_true])
  simp_rw [h_inner]
  -- Step 2: distribute outer α.sum over the pointwise addition
  simp only [Finsupp.sum]
  exact Finset.sum_add_distrib

/-- Scalar multiplication in the second argument: `⟨α, c • β⟩ = c · ⟨α, β⟩`.

Proof: `(c • β)(s) = c · β(s)`, so each term picks up a factor of `c`,
which factors out of the double sum. -/
lemma pdInner_smul_right (f : ℝ → ℂ) (α : ℝ →₀ ℂ) (c : ℂ) (β : ℝ →₀ ℂ) :
    pdInner f α (c • β) = c * pdInner f α β := by
  simp only [pdInner]
  -- Step 1: inner sum — peel c out of (c • β).sum using sum_smul_index
  have h_inner : ∀ (t : ℝ) (ct : ℂ),
      (c • β).sum (fun s ds => starRingEnd ℂ ct * ds * f (s - t)) =
      c * β.sum (fun s ds => starRingEnd ℂ ct * ds * f (s - t)) := by
    intro t ct
    rw [Finsupp.sum_smul_index (fun s => by simp)]
    simp only [Finsupp.sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s _; ring
  -- Step 2: rewrite under the outer binder, then factor c out of the outer sum
  simp_rw [h_inner]
  simp only [Finsupp.sum, Finset.mul_sum]

/-- Linearity (subtraction) in the second argument: `⟨α, β₁ - β₂⟩ = ⟨α, β₁⟩ - ⟨α, β₂⟩`. -/
lemma pdInner_sub_right (f : ℝ → ℂ) (α β₁ β₂ : ℝ →₀ ℂ) :
    pdInner f α (β₁ - β₂) = pdInner f α β₁ - pdInner f α β₂ := by
  rw [sub_eq_add_neg, pdInner_add_right, show -β₂ = (-1 : ℂ) • β₂ from by ext; simp,
      pdInner_smul_right]
  ring

end Spectra.Bochner.GNS
