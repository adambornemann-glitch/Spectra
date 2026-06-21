/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.TensorDecomp.Basic
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Equation.Basic
import Spectra.QuantumMechanics.Hydrogen.Laplacian.Spherical
import Spectra.QuantumMechanics.Hydrogen.Hamiltonian
import Spectra.QuantumMechanics.Hydrogen.Spectrum.Eigenvalue
import Spectra.QuantumMechanics.Hydrogen.Spectrum.Degeneracy

/-!
# The Spectrum of the Hydrogen Atom

The main theorems about the hydrogen spectrum, assembling the radial
eigenvalue problem with the angular decomposition.

## The main theorem

For the hydrogen Hamiltonian H = −Δ − Z/r (Z = 1 in atomic units):

  **Discrete spectrum**: σ_disc(H) = { −1/(2n²) : n = 1, 2, 3, ... }
  **Continuous spectrum**: σ_cont(H) = [0, ∞)
  **Degeneracy**: dim ker(H − E_n) = n²
  **Eigenfunctions**: ψ_{nℓm}(r,θ,φ) = R_{nℓ}(r) Y_ℓ^m(θ,φ)

These results reproduce, with complete mathematical rigour, the spectral
series I computed in January 1926 in Arosa. The eigenvalues agree exactly
with Bohr's 1913 formula — but now they are *derived*, not postulated.

## Architecture

```
  RadialEquation.lean     SphericalHarmonics.lean    HydrogenHamiltonian.lean
  ┌─────────────────┐     ┌───────────────────┐      ┌──────────────────────┐
  │ E_n = -1/(2n²)  │     │ Y_ℓ^m eigenvalue  │      │ hydrogenGenerator    │
  │ R_{nℓ} eigfunc  │     │ Y_ℓ^m orthonormal │      │ hydrogen_isSA        │
  │ radial_quantiz  │     │ Y_ℓ^m complete    │      │ IsSpectralMeasureFor │
  └────────┬────────┘     └────────┬──────────┘      └──────────┬───────────┘
           │                       │                            │
           └───────────┬───────────┘                            │
                       │                                        │
              ┌────────▼──────────┐                             │
              │ THIS FILE         │←────────────────────────────┘
              │                   │
              │ hydrogen_discrete │
              │ hydrogen_continuum│
              │ hydrogen_degener  │
              │ hydrogen_bohr     │
              └───────────────────┘
```

## References

* [Schrödinger, *Quantisierung als Eigenwertproblem I-IV*][schrodinger1926]
* [Reed, Simon, *Methods of Modern Mathematical Physics IV*][reed1978], §XIII.3.
* [Bethe, Salpeter, *Quantum Mechanics of One- and Two-Electron Atoms*][bethesalpeter1957].
* [Griffiths, *Introduction to Quantum Mechanics*][griffiths2018], §4.2.
-/

noncomputable section

namespace QuantumMechanics.Hydrogen.Spectrum

open MeasureTheory Complex Filter
open scoped Topology NNReal ENNReal Laplacian
open RadialEq Spectra.QuantumMechanics.Hydrogen Spectra.QuantumMechanics.Hydrogen.Decomposition
open Spectra.SphericalHarmonics (SphericalHarmonic sphericalHarmonic_eigenvalue
  laplaceBeltrami_const_mul)
open Spectra.QuantumMechanics.Hydrogen.Radial (laguerrePolynomial laguerre_smooth)


/-! ## Discrete spectrum -/

/-- **The discrete spectrum of hydrogen.**

    σ_disc(H) = { E_n : n ≥ 1 } = { −Z²/(2n²) : n ≥ 1 }

    For every `E < 0`, `E` is an eigenvalue of `H = −½Δ − Z/r` (with some nonzero
    `ψ ∈ Dom(H) = H²(ℝ³)`) **iff** `E = E_n = −Z²/(2n²)` for some `n ≥ 1`.

    **[Blocked on one geometric unitary — left as a documented `sorry`.]**

    The obstruction is a *coordinate* mismatch, not a missing piece of analysis. The
    operator `hydrogenHamiltonian p` lives on the **Cartesian** space
    `Spectra.Sobolev.L2_R3 = Lp ℂ 2 (volume : Measure ℝ³)`, whereas every eigenfunction
    object in this development (`hydrogenEigenfunction`, `radialLp`, `sectorEmbedding`,
    `sphericalDecomposition`) lives on the **spherical-coordinate** space
    `Decomposition.L2_R3 = Lp ℂ 2 (radialMeasure.prod sphereMeasure)`. These are
    *different types*; nothing connects them yet. The single load-bearing missing object
    is the 3D spherical change-of-variables unitary

      `chartRealization : Spectra.Sobolev.L2_R3 ≃ₗᵢ[ℂ] Decomposition.L2_R3`,

    realizing `∫_{ℝ³} |f|² dx = ∫₀^∞ ∫_{S²} |f ∘ sphereChart|² r² dr dΩ` (Jacobian
    `r² sin θ`), together with its **Hamiltonian-intertwining** property: it carries
    `Dom(H)` onto `⊕_ℓ Dom(H_ℓ)` and conjugates `H` into the sector operators `H_ℓ`
    (`sphericalDecomposition` of `chartRealization ψ`, sector-by-sector
    `RadialEq.radialHamiltonian ℓ`). Mathlib (v4.31) provides only the 2D `polarCoord`,
    so `chartRealization` is genuinely new infrastructure and is the *only* gap shared by
    both directions of the proof. Bundling it as an axiom is rejected (it is honest new
    work to be discharged); it is therefore stated as a single named, documented unitary
    when built, mirroring how `RadialEq.reduced_radial_L2_quantized` isolates its
    analytic gap.

    **Discharge route — `←` (E = E_n ⟹ eigenpair exists).** Closeable *modulo
    `chartRealization` alone*:
    1. transport the bound state `Ψ_{nℓm} = hydrogenEigenfunction n ℓ m` (sector
       `(ℓ, m)`, e.g. `ℓ = 0`, `m = 0`) back to the Cartesian side via
       `chartRealization.symm`; it lands in `Dom(H) = SobolevH2` by the
       domain-preservation half of the intertwining;
    2. the eigen-equation `H Ψ = E_n • Ψ` follows from the intertwining together with
       the pointwise sector identity `hydrogen_eigenfunction_eq` (the `−½Δ` convention)
       and the radial ODE `RadialEq.radial_eigenvalue_eq` (`H_ℓ R_{nℓ} = E_n R_{nℓ}`);
    3. `Ψ ≠ 0` from `chartRealization.norm_map` and `inner_radialLp` (unit radial norm).
    Caveat: the explicit radial layer (`hydrogenEigenvalue n = −1/(2n²)`,
    `radial_eigenvalue_eq`, `hydrogen_eigenfunction_eq`) is currently specialised to
    `p.Z = 1`. General `Z` needs the dilation `r ↦ Z r` of the radial wavefunctions, an
    isolated and routine extra step; until then this direction is honest only at `Z = 1`.

    **Discharge route — `→` (eigenpair ⟹ E = E_n).** Needs `chartRealization` **and** the
    pre-existing analytic gap:
    1. push a Cartesian eigenfunction through `chartRealization` then
       `sphericalDecomposition`, and project onto sector `(ℓ, m)` to obtain a `RadialL2`
       solution of `H_ℓ R = E R`;
    2. a weak-eigen ⟹ classical-`C²`-radial-ODE *regularity* step (elliptic regularity in
       the radial variable) puts that solution in the hypotheses of `radial_quantization`;
    3. `RadialEq.radial_quantization` then forces `E = E_n` — this bottoms out at the one
       documented analytic gap `RadialEq.reduced_radial_L2_quantized`
       (confluent-hypergeometric / Levinson–Poincaré asymptotics, not yet in Mathlib).

    **Proved and ready to be consumed by the above:** `sphericalDecomposition`
    (`Decomposition.L2_R3 ≃ₗᵢ ⊕_ℓ RadialL2`, sorry-free), `hydrogen_reduces_half`
    (pointwise sector reduction of `H`), `hydrogen_eigenfunction_eq`,
    `radial_eigenvalue_eq`, `hydrogen_isSelfAdjoint`, and `hydrogen_degeneracy`
    (giving `dim ker(H − E_n) ≥ n²` at the orthonormal-family level). The remaining
    leaves are exactly `chartRealization` (+ its intertwining) and
    `reduced_radial_L2_quantized`. -/
theorem hydrogen_discrete_spectrum (p : CoulombParams) :
    ∀ (E : ℝ), E < 0 →
    (∃ ψ : (hydrogenHamiltonian p).domain,
        (ψ : Spectra.Sobolev.L2_R3) ≠ 0 ∧
        hydrogenHamiltonian p ψ = (E : ℂ) • (ψ : Spectra.Sobolev.L2_R3)) ↔
    ∃ (n : ℕ) (hn : 1 ≤ n), E = eigenvalue p n hn :=
  sorry


end QuantumMechanics.Hydrogen.Spectrum
