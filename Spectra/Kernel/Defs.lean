/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Analytic
import Spectra.Resolvent.Defs
/-!
# Resolvent Kernel Analysis

This file develops the analytical properties of the resolvent kernel `(s - z)⁻¹`
and the associated Lorentzian approximation to the delta function.

## Main definitions

* `offRealPoint`: Helper to construct `t + iε` as an `OffRealAxis` point
* `offRealPointNeg`: Helper to construct `t - iε` as an `OffRealAxis` point
* `resolvent_integrand`: The kernel `(s - z)⁻¹`

## Main statements

### Resolvent kernel
* `resolvent_integrand_bound`: `|(s - z)⁻¹| ≤ 1/|Im(z)|` for all `s ∈ ℝ`
* `resolvent_kernel_im`: `Im((s - (t + iε))⁻¹) = ε/((s-t)² + ε²)`
* `resolvent_kernel_diff`: `(s - (t+iε))⁻¹ - (s - (t-iε))⁻¹ = 2iε/((s-t)² + ε²)`

### Lorentzian kernel
* `lorentzian_nonneg`: The Lorentzian is non-negative
* `lorentzian_bound`: The Lorentzian is bounded by `1/ε`
* `lorentzian_total_integral`: `∫ ε/((s-t)² + ε²) ds = π` (axiom)
* `lorentzian_concentration`: Lorentzian concentrates at `t` as `ε → 0` (axiom)
* `lorentzian_approx_delta`: `(1/π) · ε/((s-t)² + ε²) → δ(s-t)` as `ε → 0`

### Arctan integration
* `lorentzian_arctan_integral`: `∫_a^b ε/((s-t)² + ε²) dt = arctan(...) - arctan(...)`
* `arctan_indicator_limit`: The arctan kernel converges to the indicator function
* `arctan_kernel_bound`: The arctan kernel is uniformly bounded by 1

## Physical interpretation

The Lorentzian kernel `ε/((s-t)² + ε²)` is the imaginary part of the resolvent
kernel at `z = t + iε`. As `ε → 0`, it becomes an approximation to the delta
function `δ(s-t)`, which is the key to extracting spectral information from
the resolvent.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VII
* Stone, "Linear Transformations in Hilbert Space" (1932)

## Tags

resolvent, Lorentzian, approximate identity, Poisson kernel
-/
open Complex MeasureTheory Filter Topology TopologicalSpace
open scoped NNReal ENNReal InnerProductSpace
namespace Spectra.Kernels

/-- A complex number with non-zero imaginary part.
Re-export of `Spectra.Resolvent.OffRealAxis` (the subtype `{z : ℂ // z.im ≠ 0}`),
shared so the Kernel and Resolvent modules use a single type. -/
abbrev OffRealAxis := Spectra.Resolvent.OffRealAxis

/-- Construct `t + iε` as an off-real point. -/
def offRealPoint (t : ℝ) (ε : ℝ) (hε : ε > 0) : OffRealAxis :=
  ⟨↑t + ↑ε * I, by simp [Complex.add_im]; exact ne_of_gt hε⟩

/-- Construct `t - iε` as an off-real point. -/
def offRealPointNeg (t : ℝ) (ε : ℝ) (hε : ε > 0) : OffRealAxis :=
  ⟨↑t - ↑ε * I, by simp [Complex.sub_im]; exact ne_of_gt hε⟩

/-! ### Resolvent kernel -/

/-- The resolvent integrand `(s - z)⁻¹`. -/
noncomputable def resolvent_integrand (z : ℂ) : ℝ → ℂ :=
  fun s => ((s : ℂ) - z)⁻¹

end Spectra.Kernels
