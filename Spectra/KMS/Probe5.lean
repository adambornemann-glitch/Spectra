import Spectra.KMS.AnalyticElements

open Complex Set Filter Topology MeasureTheory
open Spectra.KMS

example (t : ℝ) : ‖(t : ℂ)‖ = |t| := by rw [Complex.norm_real]
example (t : ℝ) : ‖(t : ℂ)‖ = |t| := by rw [RCLike.norm_ofReal]
