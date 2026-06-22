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
import Spectra.QuantumMechanics.Hydrogen.Spectrum.RadialEigenfunction

/-!
# The Spectrum of the Hydrogen Atom

The main theorems about the hydrogen spectrum, assembling the radial
eigenvalue problem with the angular decomposition.

## The main theorem

For the hydrogen Hamiltonian H = −Δ − Z/r (Z = 1 in atomic units):

  **Discrete spectrum**: σ_disc(H) = { −1/(2n²) : n = 1, 2, 3, ... }


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

    **[The `←` direction is fully proved for every `Z`; only the `→` direction remains a
    documented `sorry`.]**

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

    **Discharge route — `←` (E = E_n ⟹ eigenpair exists): PROVED for every `Z`.** This is
    `Spectrum.hydrogen_bound_state p n hn` (in `RadialEigenfunction.lean`): for every charge
    `Z = p.Z > 0` and `n ≥ 1`, `E_n = −Z²/(2n²)` is a genuine eigenvalue of `H = −½Δ − Z/r`,
    realized by the explicit nonzero `H²` bound state with radial profile `c·R_{n0}(Z·‖x‖)` (the
    `Z = 1` `s`-state dilated by `r ↦ Z r`). Sorry-free and axiom-clean. It is the
    `bound_state_of_radial_profile` abstraction applied to the dilated profile: the `MemSobolevH2`
    regularity (smooth-cutoff IBP, `master_ibp`, with `∂ᵢf, ∂ⱼ∂ᵢf ∈ L²` from the exponential decay
    of `R_{n0}` and its derivatives), the `weakLaplacian` computation, the dilated classical radial
    eigen-identity (chain rule + `radial_eigenvalue_eq` at the scaled radius), and `Ψ ≠ 0` (the
    profile is continuous and `R_{n0}` is not `L²`-trivial).  `hydrogen_bound_state_Z1` is the
    `Z = 1` corollary.

    **Discharge route — `→` (eigenpair ⟹ E = E_n).** Every *analytic* input is now proved; what
    remains is bridge plumbing:
    1. push a Cartesian eigenfunction through `chartRealization` (proved) then
       `sphericalDecomposition`, and project onto sector `(ℓ, m)` to obtain a `RadialL2`
       solution of `H_ℓ R = E R` — the Hamiltonian-intertwining / sector-projection step;
    2. a weak-eigen ⟹ classical-`C²`-radial-ODE *regularity* step (elliptic regularity in
       the radial variable) puts that solution in the hypotheses of `radial_quantization`;
    3. `RadialEq.radial_quantization` then forces `E = E_n` — and that is itself **proved**
       (sorry-free), its analytic core `RadialEq.reduced_radial_L2_quantized` discharged via
       the `₁F₁`/Kummer machinery of `Spectra.Kummer` (a regular Kummer solution grows like
       `r^{ℓ+1}` unless its parameter terminates; a Wronskian + Grönwall uniqueness argument).

    **Proved and ready to be consumed by the above:** `chartRealization` (the 3D spherical `L²`
    unitary, sorry-free), `hydrogen_bound_state` (the **full `←` direction, every `Z`**),
    `sphericalDecomposition` (`Decomposition.L2_R3 ≃ₗᵢ ⊕_ℓ RadialL2`), `hydrogen_reduces_half`
    (pointwise sector reduction of `H`), `hydrogen_eigenfunction_eq`, `radial_eigenvalue_eq`,
    `RadialEq.radial_quantization` (with `reduced_radial_L2_quantized`), `hydrogen_isSelfAdjoint`,
    and `hydrogen_degeneracy` (`dim ker(H − E_n) ≥ n²`). The `←` direction and the *radial* analytic
    gap are both fully discharged; the *only* remaining leaves — both for `→` — are: (i) the
    `chartRealization` Hamiltonian-intertwining / sector projection [structural]; (ii) the
    weak-eigen ⟹ classical-`C²`-radial **elliptic regularity** step — a genuine analytic theorem
    (`radial_quantization` needs a *pointwise* `C²` ODE solution, `HasDerivAt`-level), the single
    remaining hard input, not in Mathlib. -/
theorem hydrogen_discrete_spectrum (p : CoulombParams) :
    ∀ (E : ℝ), E < 0 →
    ((∃ ψ : (hydrogenHamiltonian p).domain,
        (ψ : Spectra.Sobolev.L2_R3) ≠ 0 ∧
        hydrogenHamiltonian p ψ = (E : ℂ) • (ψ : Spectra.Sobolev.L2_R3)) ↔
    ∃ (n : ℕ) (hn : 1 ≤ n), E = eigenvalue p n hn) := by
  intro E _hE
  constructor
  · -- `→` (eigenpair ⟹ `E = E_n`): the open, research-grade direction.  Needs the
    -- `chartRealization` Hamiltonian-intertwining / sector projection together with the
    -- weak-eigen ⟹ classical-`C²`-radial elliptic-regularity step that feeds
    -- `RadialEq.radial_quantization` (which is itself already proved).  See the docstring.
    sorry
  · -- `←` (`E = E_n` ⟹ eigenpair exists): **proved for every charge `Z`**, via
    -- `hydrogen_bound_state` (the explicit nonzero `H²` `s`-state of profile `c·R_{n0}(Z·‖x‖)`).
    rintro ⟨n, hn, rfl⟩
    exact hydrogen_bound_state p n hn


end QuantumMechanics.Hydrogen.Spectrum
