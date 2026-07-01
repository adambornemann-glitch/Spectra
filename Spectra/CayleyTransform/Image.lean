/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.CayleyTransform.Mobius

/-!
# Set-level images under the Cayley/Möbius map

## Main definitions

* `cayleyImage`: the image of a set of reals under the Möbius map `μ ↦ (μ - i)/(μ + i)`.
* `inverseCayleyImage`: the preimage of a set of complex numbers under the same map.

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
recovers `B` (up to the map's injectivity on `B`) from `cayleyImage B`. -/
def inverseCayleyImage (S : Set ℂ) : Set ℝ :=
  (fun μ : ℝ => (↑μ - I) * (↑μ + I)⁻¹) ⁻¹' S

end Spectra.Cayley
