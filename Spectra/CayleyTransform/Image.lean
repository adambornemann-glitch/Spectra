/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.CayleyTransform.Mobius

/-!
# Set-level images under the Cayley/Möbius map

## Main definitions

* `cayleyImage`: the image of a set of reals under the Möbius map `μ ↦ (μ - i)/(μ + i)`.
* `inverseCayleyImage`: the preimage of a set of complex numbers under the same map.
* `cayleyImage_inverseCayleyImage`: `cayleyImage` really does recover `S` from
  `inverseCayleyImage S`, for any `S` contained in the unit circle minus `{1}`.

## Implementation notes

Both definitions are stated as the `Set.image`/`Set.preimage` of the scalar Möbius map from
`CayleyTransform/Mobius.lean`, so they inherit the standard `Set.image`/`Set.preimage` API
(`Set.image_mono`, `Set.mem_image_of_mem`, `Set.preimage_mono`, …) for free instead of needing
bespoke lemmas proved from the existential set-builder form.

## References

* `CayleyTransform/Mobius.lean`, for the underlying map and its algebraic properties.
-/

open Complex

namespace Spectra.Cayley

/-- A complex number with zero imaginary part equals the coercion of its real part. -/
lemma eq_coe_re_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : z = ↑z.re :=
  (Complex.conj_eq_iff_re.1 (Complex.conj_eq_iff_im.2 hz)).symm

/-- The image of a set of reals under the Möbius map `μ ↦ (μ - i)/(μ + i)`. -/
def cayleyImage (B : Set ℝ) : Set ℂ :=
  (fun μ : ℝ => (↑μ - I) * (↑μ + I)⁻¹) '' B

/-- The preimage of a set of complex numbers under the Möbius map `μ ↦ (μ - i)/(μ + i)`;
recovers `S` (via `cayleyImage_inverseCayleyImage` below) from `cayleyImage (inverseCayleyImage S)`
whenever `S` lies in the unit circle minus `{1}`. -/
def inverseCayleyImage (S : Set ℂ) : Set ℝ :=
  (fun μ : ℝ => (↑μ - I) * (↑μ + I)⁻¹) ⁻¹' S

/-- `cayleyImage` and `inverseCayleyImage` are inverses on the unit circle minus `{1}`: every
`S` contained there is recovered as the Cayley image of its own inverse-Cayley image. -/
lemma cayleyImage_inverseCayleyImage (S : Set ℂ) (hS : S ⊆ {w | ‖w‖ = 1 ∧ w ≠ 1}) :
    cayleyImage (inverseCayleyImage S) = S := by
  ext w
  refine ⟨fun ⟨_μ, hμ, hμw⟩ => hμw ▸ hμ, fun hw => ?_⟩
  obtain ⟨hw_norm, hw_ne⟩ := hS hw
  have him : (inverseMobius w).im = 0 := inverseMobius_real w hw_norm hw_ne
  have hμ_eq : (↑(inverseMobius w).re : ℂ) = inverseMobius w :=
    (eq_coe_re_of_im_eq_zero him).symm
  have h_mobius_eq : (↑(inverseMobius w).re - I) * (↑(inverseMobius w).re + I)⁻¹ = w := by
    rw [hμ_eq, mobius_inverseMobius w hw_ne]
  refine ⟨(inverseMobius w).re, ?_, h_mobius_eq⟩
  change (↑(inverseMobius w).re - I) * (↑(inverseMobius w).re + I)⁻¹ ∈ S
  rw [h_mobius_eq]
  exact hw

end Spectra.Cayley
