/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Equation.Reduced.Continuum

/-!
# Reduced Radial Equation

Umbrella module for the reduced hydrogen radial equation development.

The implementation is split into:

* `Equation.Reduced.Quantization` — reduced ODE, Kummer machinery, and `radial_quantization`.
* `Equation.Reduced.Continuum` — `E ≥ 0` continuum exclusion for reduced and radial solutions.

## Main definitions

* `kummerRadial` — the regular Kummer-model reduced radial solution.

## Main statements

* `reduced_ode` — the radial equation transformed to the reduced Schrödinger form.
* `reduced_radial_L2_quantized` — negative-energy reduced `L²` solutions are quantized.
* `reduced_radial_continuum` — nonnegative-energy reduced `L²` solutions vanish.
* `radial_quantization` — classical radial bound states occur exactly at `E_n`.
* `radial_continuum` — no nonzero classical `L²` solutions exist for `E ≥ 0`.

## References

* [Schrödinger, *Quantisierung als Eigenwertproblem I*][schrodinger1926]
* [Griffiths, *Introduction to Quantum Mechanics*][griffiths2018], §4.2.
-/
