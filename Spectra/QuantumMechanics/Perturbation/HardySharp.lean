/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Perturbation.HardyInequality
import Spectra.SobolevSpaces.WeakDerivative
import Spectra.SobolevSpaces.IntegrationByParts
import Spectra.SobolevSpaces.DensityResults
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

open MeasureTheory Complex Filter ContinuousLinearMap
open MeasurableSet ContDiffBump Topology
open Spectra.Sobolev
open scoped Topology NNReal ENNReal TopologicalSpace ProbabilityTheory Pointwise ContDiff

namespace Spectra.QuantumMechanics.Hydrogen

/-! ## Sharpness of the constant -/
/-- **The constant 4 is sharp.**

    There is no C < 4 such that ∫|ψ|²/|x|² ≤ C ∫|∇ψ|² for all ψ ∈ H¹.

    **Discharge route:**
    The optimising sequence is ψ_n(x) = |x|^{−1/2 + 1/n} · χ(|x|)
    where χ is a smooth cutoff. As n → ∞:
      ∫|ψ_n|²/|x|² / ∫|∇ψ_n|² → 4 = (d−2)⁻² · 4 for d = 3.

    The optimizer is |x|^{−1/2} which is in H¹_loc but not H¹,
    hence the infimum is not attained. -/
theorem hardy_constant_sharp :
    ∀ C : ℝ, (∀ (ψ : L2_R3) (hψ : MemSobolevH1 ψ),
      hardyIntegral ψ ≤ C * gradientNormSq ψ hψ) → 4 ≤ C :=
  sorry

end Spectra.QuantumMechanics.Hydrogen
