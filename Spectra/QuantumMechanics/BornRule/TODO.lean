/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/

/-! ## §6  Roadmap — documented targets, blocked on absent infrastructure

These are deliberately *not* live declarations: their types do not yet exist, so a `sorry`
stub would fail to elaborate rather than scaffold.  Recorded here as intended signatures so
the dependency is explicit.


`[needs infra: InformationGeometry.StatisticalModel API]`  The weld.
```
noncomputable def toStatisticalModel (A : SelfAdjointOperator H) (ψ : H) :
    InformationGeometry.StatisticalModel ℝ
```
The functor `(state, observable) ↦ classical model` that connects the spectral half of
Spectra to the statistical half.
-/
