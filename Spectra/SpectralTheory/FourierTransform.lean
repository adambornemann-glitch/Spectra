/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerTheorem/FourierTransform.lean
-/
import Spectra.SpectralTheory.FourierTransform.PoissonKernel.Lemmas
import Spectra.SpectralTheory.FourierTransform.PoissonKernel.Basic
import Spectra.SpectralTheory.FourierTransform.ArctanPrim
import Spectra.SpectralTheory.FourierTransform.Bridge
import Spectra.SpectralTheory.FourierTransform.ArctanLim
import Spectra.SpectralTheory.FourierTransform.Distribution
import Spectra.SpectralTheory.FourierTransform.ContPoints
import Spectra.SpectralTheory.FourierTransform.IsUnique
/-!
# Fourier Uniqueness for Finite Measures

A finite positive Borel measure on ℝ is uniquely determined by its
characteristic function (Fourier–Stieltjes transform).

This file discharges the axiom `measure_eq_of_fourier_eq` from
`PositiveDefinite.lean`.

## Main result

* `fourier_uniqueness`: If `∀ t, ∫ e^{iωt} dμ = ∫ e^{iωt} dν`, then `μ = ν`.

## Proof strategy — Poisson regularization

We use the Poisson/Lorentzian kernel `P_ε(x) = (1/π) · ε/(x² + ε²)`,
whose Fourier transform is `e^{-ε|t|}`. This connects the characteristic
function to the distribution function via:

```
∫_a^b (P_ε * μ)(s) ds  =  ∫ [arctan((b-ω)/ε) - arctan((a-ω)/ε)] / π  dμ(ω)
```

The left side depends only on the characteristic function (via Fubini),
and the right side converges to `μ(a,b]` as `ε → 0⁺` (by DCT + arctan limits).

So same characteristic function ⟹ same values on `(a,b]` ⟹ same measure
(via `Measure.ext_of_Ioc`).

## Architecture

```
§1  Poisson kernel: definition, properties, Fourier transform
§2  Arctan primitive: ∫_a^b P_ε(x-ω) dx = [arctan]/π
§3  Poisson–Fourier bridge: Poisson integral from characteristic function
§4  Arctan limits: recovery of 1_{(a,b]} as ε → 0
§5  Distribution function agreement at continuity points
§6  Extension to all (a,b] via right-continuity
§7  Main theorem via Measure.ext_of_Ioc
```

## References

* Lévy, P. "Calcul des Probabilités" (1925), §24 (inversion formula)
* Rudin, *Real and Complex Analysis*, 3rd ed., §9.5
* Connects to `lorentzian` already defined in `Routes.lean`

## Tags

Fourier uniqueness, characteristic function, Lévy inversion, Poisson kernel
-/
