/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.TomitaTakesaki.Closable
/-!
# The Tomita closure `S`: closedness, density, and the modular quadratic form

The modular operator is `Δ = S⋆ S`, where `S` is the closed Tomita operator `tomitaClosure M Ω`
(H2). This file is the **form layer**: it records the closedness and density of `S`, and the
non-negativity of the quadratic form `q(x) = ⟪S x, S x⟫ = ‖S x‖²` that `Δ` represents.

* `tomitaClosure_isClosed` — `S` is a **closed** operator;
* `tomitaClosure_domain_dense` — `S` is **densely defined**;
* `modularForm_nonneg` — the quadratic form `q(x) = ⟪S x, S x⟫ = ‖S x‖²` is **non-negative**
  (this is the form `Δ` represents, so `Δ ≥ 0`);
* `modularForm_eq_norm_sq` — that quadratic form is literally `‖S x‖²`.

## Downstream: von Neumann's `T⋆T` theorem

Constructing `Δ` as a self-adjoint operator from `S` is **von Neumann's theorem**: for a closed,
densely-defined `T`, the operator `T⋆ T` is self-adjoint and non-negative. This is carried out in
`VonNeumannTstarT.lean`, which imports this file and:

1. builds `Δ` as a `LinearPMap` by restricting `S` to the proper domain
   `{x ∈ D(S) : S x ∈ D(S⋆)}` and post-composing with `S⋆` (`modularOp`);
2. proves `Δ` symmetric and `≥ 0` (`modularOp_isSymmetric`, `modularOp_nonneg`), then upgrades to
   self-adjoint via von Neumann's graph argument (`one_add_modularOp_surjective`,
   `modularOp_isSelfAdjoint`), discharging ROADMAP milestone H3.

Downstream of that (`Δ^{½}`, the polar decomposition `S = J Δ^{½}`, and discharging
`ModularData`) lives in `Spectra/Modular/Cocycle/`. See `ROADMAP.md` (H3, R2–R4).
-/

open scoped InnerProductSpace
open Spectra.Conj

namespace Spectra.TomitaTakesaki

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The closed Tomita operator `S = S̄` is a **closed** operator (when `Ω` is cyclic and
separating). -/
theorem tomitaClosure_isClosed {M : VonNeumannAlgebra H} {Ω : H}
    (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) : (tomitaClosure M Ω).IsClosed :=
  (tomitaOp_isClosable hcyc hsep).closure_isClosed

/-- The closed Tomita operator `S` is **densely defined** (its domain contains the dense domain of
the original Tomita operator). -/
theorem tomitaClosure_domain_dense {M : VonNeumannAlgebra H} {Ω : H}
    (hcyc : IsCyclic M Ω) : Dense ((tomitaClosure M Ω).domain : Set H) :=
  (tomitaOp_domain_dense M Ω hcyc).mono
    (SetLike.coe_subset_coe.mpr (LinearPMap.le_closure (tomitaOp M Ω)).1)

/-- **The modular form is non-negative.** `q(x) = ⟪S x, S x⟫ = ‖S x‖² ≥ 0` — the quadratic form
represented by the modular operator `Δ = S⋆ S` (`VonNeumannTstarT.modularOp`), witnessing `Δ ≥ 0`.
This is the form-level shadow of `modularOp_nonneg` in `VonNeumannTstarT.lean`, which computes
`Re ⟪Δ x, x⟫ = ‖S x‖²` via the formal-adjoint identity and reduces to this fact. -/
theorem modularForm_nonneg {M : VonNeumannAlgebra H} {Ω : H}
    (x : (tomitaClosure M Ω).domain) :
    0 ≤ RCLike.re ⟪tomitaClosure M Ω x, tomitaClosure M Ω x⟫_ℂ :=
  inner_self_nonneg

/-- The modular form is the squared norm of `S x`: `⟪S x, S x⟫ = ‖S x‖²`. Used in
`Spectra/Modular/Cocycle/ModularSqrt.lean` to relate the modular-operator form to `‖·‖²` when
building `Δ^{½}`. -/
theorem modularForm_eq_norm_sq {M : VonNeumannAlgebra H} {Ω : H}
    (x : (tomitaClosure M Ω).domain) :
    ⟪tomitaClosure M Ω x, tomitaClosure M Ω x⟫_ℂ
      = (‖tomitaClosure M Ω x‖ : ℂ) ^ 2 :=
  inner_self_eq_norm_sq_to_K _

end Spectra.TomitaTakesaki
