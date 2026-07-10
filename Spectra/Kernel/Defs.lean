/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Defs
/-!
# Resolvent Kernel Definitions

The shared off-real-axis evaluation points and scalar resolvent integrand that
`Kernel.Resolvent`, `Kernel.Lorentzian`, and `Kernel.Arctan` build their analysis on top of.
This file holds no theorems of its own — just the four building blocks below.

## Main definitions

* `OffRealAxis`: re-export of `Resolvent.OffRealAxis`, the subtype `{z : ℂ // z.im ≠ 0}`,
  shared so the `Kernel` and `Resolvent` namespaces use a single underlying type.
* `offRealPoint`, `offRealPointNeg`: construct `t + iε` and `t - iε` as `OffRealAxis` points.
* `resolventIntegrand`: the kernel `(s - z)⁻¹`.

## Physical interpretation

Evaluating the resolvent at `z = t ± iε` and letting `ε → 0⁺` is the standard route from the
resolvent to spectral information (Stieltjes inversion): the imaginary part of the boundary
value is a Lorentzian approximate identity concentrating at `t`. That limit and the Lorentzian
kernel itself are developed in `Kernel.Lorentzian`; this file only fixes the evaluation points
and the raw kernel they feed.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VII.
* Stone, "Linear Transformations in Hilbert Space" (1932).

## Tags

resolvent, off-real axis, Cauchy transform, kernel
-/
open Complex
namespace Spectra.Kernels

/-- A complex number with non-zero imaginary part.
Re-export of `Spectra.Resolvent.OffRealAxis` (the subtype `{z : ℂ // z.im ≠ 0}`),
shared so the Kernel and Resolvent modules use a single type. Declared as `abbrev`, not
`def`, so it stays reducibly transparent with `Resolvent.OffRealAxis` — no coercions or
separate instance search needed to move a term between the two namespaces. -/
abbrev OffRealAxis := Spectra.Resolvent.OffRealAxis

/-- Construct `t + iε` as an off-real point. -/
def offRealPoint (t : ℝ) (ε : ℝ) (hε : ε > 0) : OffRealAxis :=
  ⟨↑t + ↑ε * I, by simpa [Complex.add_im] using ne_of_gt hε⟩

/-- Construct `t - iε` as an off-real point. -/
def offRealPointNeg (t : ℝ) (ε : ℝ) (hε : ε > 0) : OffRealAxis :=
  ⟨↑t - ↑ε * I, by simpa [Complex.sub_im] using ne_of_gt hε⟩

/-! ### Resolvent kernel -/

/-- The resolvent integrand `(s - z)⁻¹`. -/
noncomputable def resolventIntegrand (z : ℂ) : ℝ → ℂ :=
  fun s => ((s : ℂ) - z)⁻¹

end Spectra.Kernels
