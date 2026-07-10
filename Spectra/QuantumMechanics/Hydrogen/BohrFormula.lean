/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Spectrum.Eigenvalue

/-!
# The Bohr Formula and Balmer's Series

The Bohr formula for the energy of a photon absorbed or emitted in a transition between two
hydrogen energy levels, and its historical special case, Balmer's 1885 series for the visible
lines (transitions to `n = 2`). Both are direct algebraic consequences of `eigenvalue`
(`Spectrum/Eigenvalue.lean`), which carries the actual spectral-theory content — the eigenvalues
`E_n = −Z²/(2n²)`, derived from the radial quantization condition
(`RadialProblem/Equation/Basic.lean`'s `radial_quantization`). This file adds no new analysis, only
the elementary difference identity that turns a list of eigenvalues into a spectral-line law.

## Main definitions

None — this file only proves consequences of `eigenvalue`.

## Main statements

* `hydrogen_bohr_formula` — the energy difference `E_n − E_m = (Z²/2)(1/m² − 1/n²)` between any
  two hydrogen energy levels, for all `n, m ≥ 1` (no ordering between `n` and `m` is needed — the
  identity is symmetric under swapping them).
* `balmer_series` — the `m = 2` (visible-light) special case for hydrogen (`Z = 1`), the modern
  energy-conservation counterpart of Balmer's original empirical wavelength law.

## References

* Bohr, "On the Constitution of Atoms and Molecules" (1913), Philosophical Magazine, part I.
* Balmer, "Notiz über die Spectrallinien des Wasserstoffs" (1885), Annalen der Physik.
* [Griffiths, *Introduction to Quantum Mechanics*][griffiths2018], §4.2.
-/

namespace QuantumMechanics.Hydrogen.Spectrum

open Spectra.QuantumMechanics.Hydrogen

/-! ## The Bohr formula -/

/-- **The Bohr formula for spectral lines.** The energy difference between any two hydrogen
energy levels is

  `E_n − E_m = (Z²/2)(1/m² − 1/n²)`,

for all `n, m ≥ 1` — swapping `n` and `m` negates both sides, so no ordering hypothesis is needed.
Physically, `|E_n − E_m|` is the energy of the photon connecting levels `n` and `m`: emitted if
the atom falls from the higher level to the lower one, absorbed if it rises the other way (both
directions exchange a photon of the *same* energy). Taking `n > m` recovers the traditional
"photon emitted in a transition `n → m`" reading, `ΔE = E_n − E_m > 0`. The frequency is
`ν = ΔE/(2πℏ) = ΔE/(2π)` in atomic units. For hydrogen (`Z = 1`):

  `E_n − E_m = (1/2)(1/m² − 1/n²)`

Taking `m` as the lower level, this reproduces:
- Lyman series (`m = 1`): ultraviolet
- Balmer series (`m = 2`): visible
- Paschen series (`m = 3`): infrared
- Brackett series (`m = 4`): far infrared -/
theorem hydrogen_bohr_formula (p : CoulombParams) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    eigenvalue p n hn - eigenvalue p m hm =
    p.Z ^ 2 / 2 * (1 / (m : ℝ) ^ 2 - 1 / (n : ℝ) ^ 2) := by
  simp only [eigenvalue]
  field_simp
  ring

/-- **Balmer's series** (empirical, 1885): the historical law for the wavelengths of the visible
hydrogen spectral lines, `1/λ = R_∞(1/2² − 1/n²)` for `n = 3, 4, 5, …`, predating Bohr's theory
by three decades. Its modern counterpart is the `m = 2` case of `hydrogen_bohr_formula`: the
energy of the photon emitted in a transition `n → 2` for hydrogen (`Z = 1`) is

  `E_n − E_2 = (1/2)(1/4 − 1/n²)`.

(The wavelength form `1/λ = R_∞(1/4 − 1/n²)` follows from this via `E = hc/λ`; it is not
formalized here, since neither `c` nor `h` appears among this file's atomic-unit eigenvalues —
only the energy-difference identity above is proved.) -/
theorem balmer_series (n : ℕ) (hn : 3 ≤ n) :
    eigenvalue ⟨1, one_pos⟩ n (by omega) - eigenvalue ⟨1, one_pos⟩ 2 (by omega) =
    (1 : ℝ) / 2 * (1 / 4 - 1 / (n : ℝ) ^ 2) := by
  have h := hydrogen_bohr_formula ⟨1, one_pos⟩ n 2 (by omega) (by omega)
  norm_num at h ⊢
  exact h

end QuantumMechanics.Hydrogen.Spectrum
