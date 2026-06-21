/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.Unitary.Basic
import Spectra.CayleyTransform.Mobius

open InnerProductSpace Complex
open Spectra.Operator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Spectra.Cayley

/-- A complex number with zero imaginary part equals the coercion of its real part. -/
lemma Complex.eq_coe_re_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : z = ↑z.re := by
  exact ext rfl hz

/-- The Möbius image of a set of reals under `μ ↦ (μ - i)/(μ + i)`. -/
def cayleyImage (B : Set ℝ) : Set ℂ :=
  {w : ℂ | ∃ μ ∈ B, w = (↑μ - I) * (↑μ + I)⁻¹}

/-- The inverse Möbius image of a set of complex numbers. -/
def inverseCayleyImage (S : Set ℂ) : Set ℝ :=
  {μ : ℝ | (↑μ - I) * (↑μ + I)⁻¹ ∈ S}

end Spectra.Cayley
