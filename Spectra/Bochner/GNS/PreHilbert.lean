/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Bochner.GNS.PreHilbert.NormEst

/-!
# Cauchy-Schwarz for the GNS Pre-Inner Product

This umbrella file re-exports the whole `PreHilbert/` chapter (`Defs.lean` through
`NormEst.lean`, the pre-inner product, translation action, cyclic vector and norm estimate)
and adds the one result that needs all of it together: the real Cauchy-Schwarz inequality
`(Re⟨α, β⟩)² ≤ Re⟨α, α⟩ · Re⟨β, β⟩` for `pdInner f`. The proof needs both `IsPositiveDefinite`
(non-negativity of the quadratic form `λ ↦ Re⟨α + λβ, α + λβ⟩`, from `pdInner_self_re_nonneg`)
and `IsHermitian` (to fold the cross term `Re⟨α, β⟩` via `pdInner_conj_symm`).

For the individual constructions (`pdInner`, `translate`, `cyclicVector`, the key identity
`f(t) = ⟨ξ, U(t)ξ⟩`) and their own documentation, see `PreHilbert/Defs.lean`. The null space
`N = {α : ⟨α, α⟩ = 0}` is handled in `Hilbert/NullSpace.lean`, and the completion to a Hilbert
space in `Hilbert/Constructor.lean`.

## Main statements

* `pdInner_cauchy_schwarz_re` — `(Re⟨α, β⟩)² ≤ Re⟨α, α⟩ · Re⟨β, β⟩`.

## References

* Folland, *A Course in Abstract Harmonic Analysis*, §3.3
* Reed & Simon, *Methods of Modern Mathematical Physics I*, §II.6
* Berg, Christensen & Ressel, *Harmonic Analysis on Semigroups*, Ch. 3

## Tags

GNS construction, positive definite function, pre-Hilbert space,
Bochner's theorem, cyclic representation
-/

open Spectra.PositiveDefinite

namespace Spectra.Bochner.GNS

/-- Cauchy-Schwarz for the PD pre-inner product:
    `(Re⟨α, β⟩)² ≤ Re⟨α,α⟩ · Re⟨β,β⟩`.
    Proof: the real quadratic `lambda ↦ Re⟨α + lambdaβ, α + lambdaβ⟩ ≥ 0` has non-positive
    discriminant. -/
lemma pdInner_cauchy_schwarz_re {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (α β : ℝ →₀ ℂ) :
    (pdInner f α β).re ^ 2 ≤ (pdInner f α α).re * (pdInner f β β).re := by
  have hexpand : ∀ lambda : ℝ,
      (pdInner f (α + (↑lambda : ℂ) • β) (α + (↑lambda : ℂ) • β)).re =
      (pdInner f α α).re + 2 * (pdInner f α β).re * lambda +
      (pdInner f β β).re * lambda ^ 2 := by
    intro lambda
    simp only [pdInner_add_left hH, pdInner_add_right,
               pdInner_smul_right, pdInner_smul_left hH, Complex.conj_ofReal]
    rw [pdInner_conj_symm hH α β]
    simp only [Complex.add_re, Complex.mul_re,
               Complex.ofReal_re, Complex.ofReal_im,
               Complex.conj_re, zero_mul, sub_zero]
    ring
  have hq : ∀ lambda : ℝ,
      0 ≤ (pdInner f α α).re + 2 * (pdInner f α β).re * lambda +
      (pdInner f β β).re * lambda ^ 2 := by
    intro lambda; rw [← hexpand]; exact pdInner_self_re_nonneg hPD _
  set A := (pdInner f α α).re
  set B := (pdInner f α β).re
  set C := (pdInner f β β).re
  have hC_nn : 0 ≤ C := pdInner_self_re_nonneg hPD β
  -- Geometric picture: `C = 0` degenerates the parabola `λ ↦ A + 2Bλ + Cλ²` to a line, which
  -- non-negativity at both signs of `λ` forces flat (`B = 0`); `C > 0` evaluates the genuine
  -- parabola at its vertex `λ = -B/C`, where non-negativity becomes the discriminant bound.
  by_cases hC0 : C = 0
  · -- C = 0: quadratic degenerates to linear, forces B = 0
    have hlin : ∀ lambda : ℝ, 0 ≤ A + 2 * B * lambda := by simpa [hC0] using hq
    have hB : B = 0 := by
      by_contra hB
      have _h2B : (2 : ℝ) * B ≠ 0 := mul_ne_zero two_ne_zero hB
      linarith [hlin (-(A + 1) / (2 * B)),
        show A + 2 * B * (-(A + 1) / (2 * B)) = -1 from by field_simp; ring]
    simp [hB, hC0]
  · -- C > 0: evaluate at lambda = -B/C, clear denominators
    have hC_pos : 0 < C := lt_of_le_of_ne hC_nn (Ne.symm hC0)
    have h := hq (-B / C)
    have h_simp : A + 2 * B * (-B / C) + C * (-B / C) ^ 2 = A - B ^ 2 / C := by
      field_simp; ring
    rw [h_simp] at h
    rwa [sub_nonneg, div_le_iff₀ hC_pos] at h

end Spectra.Bochner.GNS
