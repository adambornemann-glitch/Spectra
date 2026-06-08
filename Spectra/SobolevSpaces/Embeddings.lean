/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
File: Spectra/SoboleveSpaces/Embeddings.lean
-/
import Spectra.SobolevSpaces.DensityResults
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

open MeasureTheory Complex
open scoped Pointwise ContDiff

namespace Spectra.Sobolev

/-! ### Sobolev embedding -/

/-! ### Fourier characterisation (interface for Laplacian self-adjointness)

The Fourier transform provides the cleanest route to proving that -Δ
is self-adjoint on H². Under Fourier:

  H²(ℝ³) ↔ { f̂ ∈ L² : (1+|ξ|²)f̂ ∈ L² }
  (-Δf)^ = |ξ|² f̂

This makes -Δ unitarily equivalent to multiplication by |ξ|², which
is manifestly self-adjoint. We axiomatize the key consequences here;
Phase 4 fills them in once Mathlib's Plancherel theorem on ℝ³ is
interfaced.
-/

/-- H² is characterised in Fourier space by the finiteness of ∫(1+|ξ|²)²|f̂|² dξ.

    This is used to prove:
    - Self-adjointness of -Δ on H²
    - The resolvent bound for -Δ
    - The spectrum σ(-Δ) = [0,∞) -/
theorem sobolevH2_fourier_char :
    ∀ f : L2_R3, MemSobolevH2 f ↔
      sorry :=  -- ∫(1+|ξ|²)²|f̂(ξ)|² dξ < ∞
  sorry

/-! ### H¹ inner product (Hilbert space structure) -/

/-- The H¹ inner product: ⟨f, g⟩_{H¹} = ⟨f, g⟩_{L²} + Σᵢ ⟨∂ᵢf, ∂ᵢg⟩_{L²}.

    Under this inner product, H¹ is a Hilbert space. This is used
    for coercivity estimates in the variational formulation. -/
noncomputable def sobolevH1Inner (f g : L2_R3) (hf : MemSobolevH1 f) (hg : MemSobolevH1 g) : ℂ :=
  inner (𝕜 := ℂ) f g +
  ∑ i : Fin 3, inner (𝕜 := ℂ) (weakGradient f hf i) (weakGradient g hg i)

/-- H¹ is complete under the H¹ inner product. -/
def sobolevH1_complete :
    ∀ (seq : ℕ → L2_R3) (hseq : ∀ n, MemSobolevH1 (seq n)),
    -- if Cauchy in H¹ norm, then converges in H¹
    sorry := by
  sorry

end Spectra.Sobolev
