/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: SpectralTheory/HerglotzTheorem/Stieltjes.lean
-/
import Spectra.SpectralTheory.HerglotzTheorem.Stieltjes.CumulativeDistFun
import Spectra.SpectralTheory.HerglotzTheorem.Stieltjes.Hellys
import Spectra.SpectralTheory.HerglotzTheorem.Stieltjes.Measure
import Spectra.SpectralTheory.HerglotzTheorem.Stieltjes.IntegralConv
import Spectra.SpectralTheory.HerglotzTheorem.Stieltjes.Lemma
/-!
# Herglotz's lemma via Stieltjes Functions

This file replaces the weak-⋆ compactness argument (which requires
Riesz–Markov) with a **distribution function / Helly selection** approach
that uses only:

  - `Monotone.stieltjesFunction` (Mathlib: right-regularization)
  - `StieltjesFunction.measure` (Mathlib: Borel measure from CDF)
  - `coordinatewise_convergent_subseq` (already proved in HerglotzMeasure.lean)
  - Dominated convergence (Mathlib)

## Strategy

Given the Fejér mean measures `σ_N` from HerglotzMeasure.lean:

1. **Define CDFs**: `F_N(x) = σ_N([0, x])` for `x ∈ [0, 2π]`, extended
   to `0` for `x < 0` and `‖ψ‖²` for `x > 2π`.

2. **Properties of F_N**: Each `F_N` is monotone non-decreasing, continuous
   (the density is continuous), `F_N(0) = 0`, `F_N(2π) = ‖ψ‖²`.

3. **Helly extraction**: Apply `coordinatewise_convergent_subseq` to
   `{F_N(q)}` for `q` ranging over a countable dense set (the rationals
   in `[0, 2π]`). Extract a subsequence converging at all rationals.

4. **Extend to all reals**: Define `F(x) = inf_{q > x, q ∈ ℚ} lim F_{N_k}(q)`.
   This is automatically right-continuous and monotone.

5. **Stieltjes measure**: `Monotone.stieltjesFunction` + `.measure` gives
   the Borel measure `μ_ψ`.

6. **Fourier verification**: For each `n ∈ ℤ`,
   `∫ e^{inθ} dμ_ψ = lim_k ∫ e^{inθ} dσ_{N_k} = lim_k w_{N_k}(n) c(n) = c(n)`.

   The key tool is: `∫ f dF_{N_k} → ∫ f dF` when `F_{N_k} → F` pointwise
   at continuity points and `f` is bounded continuous. This is a consequence
   of integration by parts + dominated convergence, and does NOT require
   Riesz–Markov.

## Dependencies

This file imports from `HerglotzMeasure.lean`:
  - `fejerMeasure`, `fejerMeasure_total`, `fejerMeasure_fourier`
  - `fejerMeanDensity_nonneg`, `fejerMeanDensity_continuous`
  - `fejerWeight_tendsto`, `unitaryCorrelation`
  - `coordinatewise_convergent_subseq`

It does NOT import or depend on:
  - Riesz–Markov representation lemma
  - Banach–Alaoglu / weak-⋆ compactness
  - Continuous functional calculus
  - Bochner's lemma

## References

* G. HerglotzTheorem, *Über Potenzreihen mit positivem, reellen Teil im
  Einheitskreis*, Leipziger Berichte **63** (1911), 501–511
* E. Helly, *Über lineare Funktionaloperationen*, Sitzungsberichte
  der Wiener Akademie **121** (1912), 265–297
* P. Billingsley, *Probability and Measure*, §25

## Tags

HerglotzTheorem lemma, Stieltjes function, Helly selection lemma,
distribution function, spectral measure
-/
