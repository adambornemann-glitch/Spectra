import Mathlib
import Spectra.QuantumMechanics.Hydrogen.Laplacian.FreeGreens
import Spectra.QuantumMechanics.Hydrogen.Laplacian.ResolventL2
import Spectra.SpectralTheory.YoungConvolution

/-!
# Option B endgame: the Fourier-defined free Green's function is the resolvent kernel

This file carries out the "Option B" construction described in the project roadmap, which
identifies the free resolvent `(−Δ − z)⁻¹` with convolution against the Fourier-defined free
Green's function `G̃_z := 𝓕⁻¹ m_z`, where `m_z(ξ) = (laplacianSymbol ξ − z)⁻¹` is the resolvent
symbol.  It deliberately avoids the explicit Yukawa kernel `e^{−√(−z)|x|}/(4π|x|)` and the
attendant `S²` sphere integral (which is the wall behind `freeGreensFunction_is_resolvent_kernel`).

* `freeGreensFunctionL2 z hz : L2_R3` — `𝓕⁻¹` of the resolvent symbol `m_z ∈ L²` (**B0**).
* `fourierL2_freeGreensFunctionL2` — `𝓕 G̃_z =ᵐ m_z` (**B0**, proved).
* `fourier_conv_schwartz_pointwise` — for Schwartz `φ, χ`, the function-level Fourier transform of
  the convolution is the product `𝓕φ · 𝓕χ` (proved; the Schwartz base case for the density route).
* `freeGreensFunctionL2_is_resolvent_kernel` — the kernel identity `R_z ψ =ᵐ G̃_z ⋆ ψ` (**B3**).

## The remaining wall (`fourier_conv_L2_eq`)

`freeGreensFunctionL2_is_resolvent_kernel` is reduced, by Fourier injectivity together with the
operator-theoretic half `fourierL2_selfAdjointResolvent` (which gives `𝓕(R_z ψ) =ᵐ m_z · 𝓕ψ`), to
the **L² convolution theorem**

  `fourier_conv_L2_eq` :  for `g, ψ ∈ L²(ℝ³)`,  `G̃_z ⋆ ψ ∈ L²`  and  `𝓕(G̃_z ⋆ ψ) =ᵐ 𝓕G̃_z · 𝓕ψ`.

This is **absent from Mathlib** and is the sole remaining `sorry` here.  The density route prove it
on the Schwartz base case (`fourier_conv_schwartz_pointwise`) and extends to `L²` — but extending in
*both* slots requires the convolution map `L² × L² → L²` to be continuous, which is **false**
(`L² ⋆ L² ⊆ C₀`, not `L²`).  One slot must be `L¹` to get Young-continuity
(`Spectra.CompactOperator.young_L1_conv_L2`), and neither `G̃_z` nor `ψ` is known to be `L¹`
(`G̃_z` is the abstract `𝓕⁻¹ m_z`, with `m_z ∼ |ξ|⁻²` *not* `L¹` on `ℝ³`).  This is the precise
analytic gap.
-/

noncomputable section
open MeasureTheory Complex Filter SchwartzMap
open Spectra.Sobolev
open Spectra.YosidaHille Spectra.OneParameterUnitaryGroup
  Spectra.Resolvent Spectra.QuantumMechanics.Observable
  Spectra.QuantumMechanics.SpectralTheory
open FourierTransform
open scoped Convolution FourierTransform SchwartzMap

namespace Spectra.QuantumMechanics.Hydrogen

/-! ## B0: the Fourier-defined free Green's function as an `L²` element -/

/-- **B0.**  The Fourier-defined free Green's function `G̃_z := 𝓕⁻¹ m_z`, where
`m_z(ξ) = (laplacianSymbol ξ − z)⁻¹` is the resolvent symbol (which is `L²` by
`memLp_inv_laplacianSymbol_sub`).  No explicit Yukawa formula is used. -/
def freeGreensFunctionL2 (z : ℂ) (hz : z.im ≠ 0) : L2_R3 :=
  fourierL2.symm ((memLp_inv_laplacianSymbol_sub z hz).toLp _)

/-- **B0.**  `𝓕 G̃_z =ᵐ m_z`: the Fourier transform of `G̃_z` is the resolvent symbol, a.e. -/
theorem fourierL2_freeGreensFunctionL2 (z : ℂ) (hz : z.im ≠ 0) :
    (fourierL2 (freeGreensFunctionL2 z hz) : R3 → ℂ)
      =ᵐ[volume] fun ξ => ((laplacianSymbol ξ : ℂ) - z)⁻¹ := by
  rw [freeGreensFunctionL2, LinearIsometryEquiv.apply_symm_apply]
  exact MemLp.coeFn_toLp _

/-! ## The Schwartz base case of the convolution–Fourier theorem -/

/-- For Schwartz `φ, χ`, the (function-level) Fourier transform of the convolution `φ ⋆ χ` is the
pointwise product `𝓕φ · 𝓕χ`.  This is the base case for the density route to the `L²` convolution
theorem; it is `SchwartzMap.fourier_convolution` re-expressed pointwise via `mul`. -/
theorem fourier_conv_schwartz_pointwise (φ χ : 𝓢(R3, ℂ)) (x : R3) :
    𝓕 ((φ : R3 → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (χ : R3 → ℂ)) x
      = 𝓕 (φ : R3 → ℂ) x * 𝓕 (χ : R3 → ℂ) x := by
  have h1 := SchwartzMap.fourier_convolution_apply (ContinuousLinearMap.mul ℂ ℂ) φ χ x
  rw [SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply] at h1
  rw [← h1, ContinuousLinearMap.mul_apply', SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]

/-! ## The L² convolution–Fourier theorem (the wall) and the kernel identity -/

/-- **The L² convolution theorem (WALL).**  For `g, ψ ∈ L²(ℝ³)` the pointwise convolution
`g ⋆ ψ` lies in `L²` and its `L²` Fourier transform is the product `𝓕g · 𝓕ψ`.

This statement is **not available in Mathlib** and is the only `sorry` in this file.  See the module
docstring for the precise obstruction (`L² ⋆ L² ⊆ C₀`, not `L²`; the density route needs one `L¹`
slot for Young-continuity, which neither factor provides). -/
theorem fourier_conv_L2_eq (g ψ : L2_R3) :
    ∃ h : MemLp ((g : R3 → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (ψ : R3 → ℂ)) 2 volume,
      (fourierL2 (h.toLp _) : R3 → ℂ)
        =ᵐ[volume] fun ξ => (fourierL2 g : R3 → ℂ) ξ * (fourierL2 ψ : R3 → ℂ) ξ :=
  sorry

/-- **B3.**  The Fourier-defined free Green's function is the integral kernel of the free resolvent:

  `R_z ψ (x) =ᵐ ∫ y, G̃_z (x − y) · ψ y`.

Reduces, via `fourier_conv_L2_eq` (the wall) and the operator-theoretic half
`fourierL2_selfAdjointResolvent`, to Fourier injectivity.  This is the Option B analogue of the
open `freeGreensFunction_is_resolvent_kernel`, but stated for `G̃_z` instead of the explicit Yukawa
kernel, so it never touches the `S²` sphere integral. -/
theorem freeGreensFunctionL2_is_resolvent_kernel (z : ℂ) (hz : z.im ≠ 0) (ψ : L2_R3) :
    ∀ᵐ x : R3,
      (selfAdjointResolvent laplacian_isSelfAdjoint z hz ψ : R3 → ℂ) x =
      ∫ y, (freeGreensFunctionL2 z hz : R3 → ℂ) (x - y) * (ψ : R3 → ℂ) y := by
  -- the convolution lives in L² and Fourier-transforms to the product (the wall)
  obtain ⟨hconvMem, hF⟩ := fourier_conv_L2_eq (freeGreensFunctionL2 z hz) ψ
  -- 𝓕 of the convolution L²-element equals m_z · 𝓕ψ, a.e.
  have hconv_symbol : (fourierL2 (hconvMem.toLp _) : R3 → ℂ)
      =ᵐ[volume] fun ξ => ((laplacianSymbol ξ : ℂ) - z)⁻¹ * (fourierL2 ψ : R3 → ℂ) ξ := by
    filter_upwards [hF, fourierL2_freeGreensFunctionL2 z hz] with ξ hξ hG
    rw [hξ, hG]
  -- 𝓕 of the resolvent equals m_z · 𝓕ψ, a.e. (operator-theoretic half)
  have hres_symbol := fourierL2_selfAdjointResolvent z hz ψ
  -- hence the two L² Fourier transforms agree a.e., so the L² elements agree
  have hFeq : fourierL2 (hconvMem.toLp _)
      = fourierL2 (selfAdjointResolvent laplacian_isSelfAdjoint z hz ψ) := by
    apply Lp.ext
    filter_upwards [hconv_symbol, hres_symbol] with ξ h1 h2
    rw [h1, h2]
  have hLp : (hconvMem.toLp _ : L2_R3)
      = selfAdjointResolvent laplacian_isSelfAdjoint z hz ψ := fourierL2.injective hFeq
  -- transport to the pointwise a.e. statement
  have h1 : ((hconvMem.toLp _ : L2_R3) : R3 → ℂ)
      =ᵐ[volume] (selfAdjointResolvent laplacian_isSelfAdjoint z hz ψ : R3 → ℂ) := by
    rw [hLp]
  have h2 := hconvMem.coeFn_toLp
  filter_upwards [h1, h2] with x hx1 hx2
  rw [← hx1, hx2, convolution_mul_swap]

end Spectra.QuantumMechanics.Hydrogen
