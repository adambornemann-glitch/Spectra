/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Laplacian.FreeGreens.L2
import Spectra.QuantumMechanics.Perturbation.TruncatedCoulombL2
import Spectra.SpectralTheory.TranslationKernel

/-!
# The truncated resolvent kernel is `L²(ℝ³ × ℝ³)`

The operator `Vⁿ · (−Δ − z)⁻¹` — truncated Coulomb potential times the free resolvent — is the
integral operator whose kernel is `Kₙ(x, y) = Vⁿ(x) · G_z(x − y)`, where `Vⁿ = truncCoulomb p n`
(brick M3) and `G_z = freeGreensFunction z` (brick M2). This file is **brick M5**: that kernel lies
in `L²(ℝ³ × ℝ³)`, with the exact tensor-norm identity `‖Kₙ‖₂ = ‖Vⁿ‖₂ · ‖G_z‖₂`.

Both facts are immediate from the translation-invariant product-kernel engine
`Spectra.CompactOperator.memLp_kernel_mul_sub` / `eLpNorm_kernel_mul_sub`, since `Kₙ` has exactly
the shape `(x, y) ↦ a x · b (x − y)`.

This `L²` membership feeds `Spectra.CompactOperator.isCompactOperator_integralOperator` (the A3
gate) to make each `Vⁿ · R_z` compact; the norm identity controls the operator-norm limit
`Vⁿ · R_z → V · R_z` in the final assembly (brick M8).
-/

noncomputable section

open MeasureTheory
open Spectra.Sobolev
open Spectra.CompactOperator

namespace Spectra.QuantumMechanics.Hydrogen

/-- **Brick M5.** The truncated resolvent kernel `Kₙ(x, y) = Vⁿ(x) · G_z(x − y)` lies in
`L²(ℝ³ × ℝ³)`. -/
lemma truncKernel_memLp (p : CoulombParams) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    MemLp (fun q : R3 × R3 => truncCoulomb p n q.1 * freeGreensFunction z (q.1 - q.2)) 2
      ((volume : Measure R3).prod (volume : Measure R3)) :=
  memLp_kernel_mul_sub (truncCoulomb_memLp p n) (memL2_freeGreensFunction z hz)

/-- The exact `L²` tensor-norm of the truncated resolvent kernel:
`‖Kₙ‖₂ = ‖Vⁿ‖₂ · ‖G_z‖₂`. -/
lemma eLpNorm_truncKernel (p : CoulombParams) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    eLpNorm (fun q : R3 × R3 => truncCoulomb p n q.1 * freeGreensFunction z (q.1 - q.2)) 2
        ((volume : Measure R3).prod (volume : Measure R3))
      = eLpNorm (truncCoulomb p n) 2 volume * eLpNorm (freeGreensFunction z) 2 volume :=
  eLpNorm_kernel_mul_sub (truncCoulomb_memLp p n) (memL2_freeGreensFunction z hz)

end Spectra.QuantumMechanics.Hydrogen
