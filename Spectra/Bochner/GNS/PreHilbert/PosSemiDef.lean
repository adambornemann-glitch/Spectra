/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Bochner.GNS.PreHilbert.Conjugate

/-!
# Positive Semi-Definiteness of the GNS Pre-Inner Product

Once `f : ℝ → ℂ` is positive definite, the self-pairing `⟨α, α⟩_f` has non-negative real
part. We get there by reindexing the `Finsupp.sum`-based `pdInner f α α` as a finite `Fin N`
double sum over the support of `α`, which is exactly the quadratic form appearing in the
`IsPositiveDefinite` hypothesis. Combined with the conjugate symmetry of `Conjugate.lean`, the
self-pairing is also shown to be real (zero imaginary part).

## Main statements

* `pdInner_self_re_nonneg` — `0 ≤ Re ⟨α, α⟩_f` whenever `f` is positive definite.
* `pdInner_self_im_eq_zero` — `Im ⟨α, α⟩_f = 0` whenever `f` is Hermitian.
-/

open Spectra.PositiveDefinite

namespace Spectra.Bochner.GNS

-- §5  Positive semi-definiteness

/-- **Bridge lemma**: reindex a `pdInner` self-pairing as a `Fin N` double sum.

Given `α : ℝ →₀ ℂ` with `α.support.card = N`, we enumerate the support
via `α.support.equivFin` and express `⟨α, α⟩_f` as:

  `Σ_{j,k : Fin N} conj(c_j) · c_k · f(t_k - t_j)`

where `t_j` are the support points and `c_j = α(t_j)`. This is exactly
the quadratic form appearing in the `PositiveDefinite` condition.

Kept public (rather than `private`) as a reusable reindexing bridge for other
PD-quadratic-form arguments over `pdInner`, even though this file's own proof of
`pdInner_self_re_nonneg` is its only current caller. -/
lemma pdInner_self_eq_fin_sum (f : ℝ → ℂ) (α : ℝ →₀ ℂ) :
    pdInner f α α =
    let S := α.support
    let N := S.card
    let e := S.equivFin
    ∑ j : Fin N, ∑ k : Fin N,
      starRingEnd ℂ (α (e.symm j)) * (α (e.symm k)) *
      f ((e.symm k : ℝ) - (e.symm j : ℝ)) := by
  simp only [pdInner, Finsupp.sum]
  set S := α.support
  set e := S.equivFin
  have h_re : ∀ g : ℝ → ℂ, ∑ t ∈ S, g t = ∑ j : Fin S.card, g ↑(e.symm j) := by
    intro g
    rw [← Finset.sum_coe_sort S (f := g)]
    exact Fintype.sum_equiv e (fun i => g i) (fun j => g ↑(e.symm j))
      (fun i => by simp)
  -- Apply twice: once for the outer sum, once for each inner sum
  rw [h_re]; congr 1; ext j; exact h_re _

/-- **Positive semi-definiteness**: `0 ≤ Re ⟨α, α⟩_f` for all `α`.

This is the GNS counterpart of the `PositiveDefinite` condition:
the PD hypothesis gives non-negativity of finite quadratic forms,
and `⟨α, α⟩` is exactly such a form. -/
theorem pdInner_self_re_nonneg {f : ℝ → ℂ} (hPD : IsPositiveDefinite f)
    (α : ℝ →₀ ℂ) : 0 ≤ (pdInner f α α).re := by
  rw [pdInner_self_eq_fin_sum]; dsimp only
  set e := α.support.equivFin
  have h := hPD α.support.card
    (fun j => -(↑(e.symm j) : ℝ))
    (fun j => α (e.symm j))
  convert h using 2
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  congr 1
  abel_nf

/-- The imaginary part of `⟨α, α⟩_f` vanishes (consequence of conjugate symmetry).

From `⟨α, α⟩ = conj ⟨α, α⟩` (self-conjugate), it follows that `⟨α, α⟩` is real.
This requires Hermitian symmetry of `f`. -/
lemma pdInner_self_im_eq_zero {f : ℝ → ℂ} (hH : IsHermitian f) (α : ℝ →₀ ℂ) :
    (pdInner f α α).im = 0 := by
  -- `z = conj z` forces `z.im = -z.im`, i.e. `z.im = 0`; extract this from `h` via `Complex.im`.
  have h := pdInner_conj_symm hH α α
  have := congr_arg Complex.im h
  simp [Complex.conj_im] at this
  linarith

end Spectra.Bochner.GNS
