import Spectra.KMS.AnalyticElements

open Complex Set Filter Topology MeasureTheory
open Spectra.KMS

variable {A : Type*} [CStarAlgebra A]

-- Test the pointwise derivative computation
example (α : Dynamics A) (a : A) (n : ℕ) (z : ℂ) (t : ℝ) :
    HasDerivAt (fun z => Complex.exp (-(n : ℂ) * (((t : ℂ)) - z) ^ 2) • α.evolve t a)
      (((2 * (n : ℂ) * (((t : ℂ)) - z)) * Complex.exp (-(n : ℂ) * (((t : ℂ)) - z) ^ 2)) • α.evolve t a) z := by
  have hinner : HasDerivAt (fun z : ℂ => -(n : ℂ) * (((t : ℂ)) - z) ^ 2)
      (2 * (n : ℂ) * (((t : ℂ)) - z)) z := by
    have h1 : HasDerivAt (fun z : ℂ => ((t : ℂ)) - z) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub (t : ℂ)
    have h2 : HasDerivAt (fun z : ℂ => (((t : ℂ)) - z) ^ 2)
        (2 * (((t : ℂ)) - z) ^ 1 * (-1)) z := h1.pow 2
    have h3 := h2.const_mul (-(n : ℂ))
    convert h3 using 1
    ring
  have hexp := hinner.cexp
  have := hexp.smul_const (α.evolve t a)
  convert this using 2
  ring
