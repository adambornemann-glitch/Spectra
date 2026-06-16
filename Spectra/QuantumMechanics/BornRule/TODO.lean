/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/

/-! ## §6  Roadmap — documented targets, blocked on absent infrastructure

These are deliberately *not* live declarations: their types do not yet exist, so a `sorry`
stub would fail to elaborate rather than scaffold.  Recorded here as intended signatures so
the dependency is explicit.

`[needs infra: trace-class / DensityOperator]`  Mixed-state Born rule.
```
noncomputable def bornMeasureMixed (P : ProjValMeasure H) (ρ : DensityOperator H) : Measure ℝ
theorem bornMixed_apply (...) : ((bornMeasureMixed P ρ) B).toReal = (ρ.toOp * P.proj B hB).trace.re
theorem bornMeasureMixed_pure (ψ) : bornMeasureMixed P (DensityOperator.pure ψ) = bornMeasure P ψ
```
This is the Gleason form and the only form `InformationGeometry.CramerRao.Quantum` can use.

`[needs infra: POVM / effects]`  Generalized measurements.
```
noncomputable def bornMeasurePOVM (M : POVM H ι) (ρ : DensityOperator H) : Measure ι
```

`[needs infra: joint spectral measure of a commuting family]`  The relational layer.
```
theorem commute_iff_joint_law (A B : UnboundedObservable H) :
    Commute A B ↔ ∃ μ : H → Measure (ℝ × ℝ), (marginals are the bornMeasures)
```
The forward direction feeds `BellsTheorem`; the failure of the backward direction for
non-commuting `A, B` is the content the CHSH/Tsirelson bounds quantify.

`[needs infra: InformationGeometry.StatisticalModel API]`  The weld.
```
noncomputable def toStatisticalModel (A : UnboundedObservable H) (ψ : H) :
    InformationGeometry.StatisticalModel ℝ
```
The functor `(state, observable) ↦ classical model` that connects the spectral half of
Spectra to the statistical half.
-/
