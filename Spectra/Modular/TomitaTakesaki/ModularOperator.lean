/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
-/
import Spectra.Modular.TomitaTakesaki.Closable
/-!
# Toward the modular operator `Δ = S⋆ S` (H3)

The modular operator is `Δ = S⋆ S`, where `S` is the closed Tomita operator `tomitaClosure M Ω`
(H2). This file records the facts that put us at the doorstep of `Δ`:

* `tomitaClosure_isClosed` — `S` is a **closed** operator;
* `tomitaClosure_domain_dense` — `S` is **densely defined**;
* `modularForm_nonneg` — the quadratic form `q(x) = ⟪S x, S x⟫ = ‖S x‖²` is **non-negative**
  (this is the form `Δ` represents, so `Δ ≥ 0`).

## What remains: von Neumann's `T⋆T` theorem

Constructing `Δ` as a self-adjoint operator from `S` is **von Neumann's theorem**: for a closed,
densely-defined `T`, the operator `T⋆ T` is self-adjoint and non-negative. Two obstacles, both
genuine and both absent from Mathlib:

1. **Forming `Δ` as a `LinearPMap`.** `LinearPMap.comp` cannot build `S⋆ ∘ S` directly — its
   hypothesis `∀ x ∈ D(S), S x ∈ D(S⋆)` is false (the domain of `T⋆T` is the *proper* subspace
   `{x ∈ D(S) : S x ∈ D(S⋆)}`). One must restrict `S` to that subspace first.
2. **Self-adjointness.** `Δ` is manifestly *symmetric* (`⟪Δx,y⟫ = ⟪Sx,Sy⟫ = ⟪x,Δy⟫`) and `≥ 0`,
   but upgrading symmetric `+ ≥ 0` to *self-adjoint* requires `(1 + Δ)` surjective — the heart of
   von Neumann's theorem, proved classically via the orthogonal decomposition
   `H ⊕ \overline{H} = Γ(S) ⊕ J Γ(S⋆)` of the closed graph. This is a substantial standalone
   development.

So the construction chain `M0 → R1 → H1 → E1 → H2` has reduced the existence of the modular operator
to exactly this one classical theorem. Downstream (`Δ^{½}`, the polar decomposition `S = J Δ^{½}`,
and discharging `ModularData`) is gated on it. See `ROADMAP.md` (H3, R2–R4).
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
represented by the (not-yet-constructed) modular operator `Δ = S⋆ S`, witnessing `Δ ≥ 0`. -/
theorem modularForm_nonneg {M : VonNeumannAlgebra H} {Ω : H}
    (x : (tomitaClosure M Ω).domain) :
    0 ≤ RCLike.re ⟪tomitaClosure M Ω x, tomitaClosure M Ω x⟫_ℂ :=
  inner_self_nonneg

/-- The modular form is the squared norm of `S x`: `⟪S x, S x⟫ = ‖S x‖²`. -/
theorem modularForm_eq_norm_sq {M : VonNeumannAlgebra H} {Ω : H}
    (x : (tomitaClosure M Ω).domain) :
    ⟪tomitaClosure M Ω x, tomitaClosure M Ω x⟫_ℂ
      = (‖tomitaClosure M Ω x‖ : ℂ) ^ 2 :=
  inner_self_eq_norm_sq_to_K _

end Spectra.TomitaTakesaki
