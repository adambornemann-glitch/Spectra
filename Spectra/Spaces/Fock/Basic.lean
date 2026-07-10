/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Tensor.Power
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The full Fock space `fullFock 𝕜 H`

The **full Fock space** over a one-particle Hilbert space `H`:

`fullFock 𝕜 H := lp (fun n : ℕ => HilbertTensorPower 𝕜 n H) 2`,

the ℓ²-direct sum (Hilbert sum) of the `n`-particle sectors — the completed tensor powers
of `Spectra/Spaces/Tensor/Power.lean`. It is a Hilbert space by pure instance inheritance:
Mathlib's `lp · 2` machinery supplies the inner product and completeness from the sectors'.

As far as we are aware this is the first analytic (norm-complete, inner-product) Fock space
in any proof assistant: PhysLib's `WickAlgebra` is purely formal, and the one other Lean
Fock space (VirasoroProject) is a norm-free Verma module.

The bosonic and fermionic subspaces (symmetric/antisymmetric sectors, via the permutation
unitaries `HilbertTensorPower.permUnitary`), the vacuum, and the finite-particle core are
built in subsequent files of `Spectra/Spaces/Fock/`.
-/

noncomputable section

open scoped TensorProduct

namespace Spectra

variable (𝕜 H : Type*) [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The **full Fock space** over the one-particle space `H`: the Hilbert sum of the
`n`-particle sectors `HilbertTensorPower 𝕜 n H` over all `n : ℕ`. -/
abbrev fullFock := lp (fun n : ℕ => HilbertTensorPower 𝕜 n H) 2

-- Sanity: the Hilbert-space structure is found by instance resolution alone.
example : NormedAddCommGroup (fullFock 𝕜 H) := inferInstance
example : InnerProductSpace 𝕜 (fullFock 𝕜 H) := inferInstance
example : CompleteSpace (fullFock 𝕜 H) := inferInstance

end Spectra
