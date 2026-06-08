/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: CayleyTransform/BoundedBelow.lean
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

/-- `cayleyImage` and `inverseCayleyImage` are inverses on the unit circle minus {1}. -/
lemma cayleyImage_inverseCayleyImage (S : Set ℂ) (hS : S ⊆ {w | ‖w‖ = 1 ∧ w ≠ 1}) :
    cayleyImage (inverseCayleyImage S) = S := by
  ext w
  constructor
  rintro ⟨μ, hμ_mem, rfl⟩
  exact hμ_mem
  intro hw
  obtain ⟨hw_norm, hw_ne⟩ := hS hw
  use (inverseMobius w).re
  have him : (inverseMobius w).im = 0 := inverseMobius_real w hw_norm hw_ne
  have hμ_eq : (↑(inverseMobius w).re : ℂ) = inverseMobius w :=
    (Complex.eq_coe_re_of_im_eq_zero him).symm
  have h_mobius_eq : (↑(inverseMobius w).re - I) * (↑(inverseMobius w).re + I)⁻¹ = w := by
    calc (↑(inverseMobius w).re - I) * (↑(inverseMobius w).re + I)⁻¹
        = (inverseMobius w - I) * (inverseMobius w + I)⁻¹ := by rw [hμ_eq]
      _ = w := mobius_inverseMobius w hw_norm hw_ne
  constructor
  simp only [inverseCayleyImage, Set.mem_setOf_eq]
  rw [h_mobius_eq]
  exact hw
  exact h_mobius_eq.symm

end Spectra.Cayley
