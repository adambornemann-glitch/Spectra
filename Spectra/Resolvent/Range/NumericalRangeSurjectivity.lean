/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.NumericalRange

/-!
# Existence and uniqueness from the numerical range

The numerical-range analogue of `Spectra.Resolvent.self_adjoint_range_all_z`
(`Resolvent/Range/Surjectivity.lean`): for self-adjoint `A` and `z` outside
`closure (numericalRange A)`, the equation `(A - z)ψ = φ` has a unique solution for every `φ`.
Uniqueness comes directly from `injOn_sub_smul_of_notMem_closure_numericalRange`; existence comes
from gluing `numericalRange_range_isClosed` and `numericalRange_range_dense` into
`ran(A - z) = univ`.

## Main statements

* `numericalRange_solution_unique` : solutions to `(A - z)ψ = φ` are unique.
* `numericalRange_range_all_z` : **main theorem** — a unique solution exists for every `φ`.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII.3.
-/

open Spectra.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.Resolvent

omit [CompleteSpace H] in
/-- Solutions to `(A - z)ψ = φ` are unique when `z ∉ closure (numericalRange A)`. -/
lemma numericalRange_solution_unique {A : H →ₗ.[ℂ] H}
    (hne : (numericalRange A).Nonempty) (z : ℂ) (hz : z ∉ closure (numericalRange A)) (φ : H)
    (ψ ψ' : A.domain)
    (hψ : A ψ - z • (ψ : H) = φ)
    (hψ' : A ψ' - z • (ψ' : H) = φ) : ψ = ψ' := by
  apply Subtype.ext
  apply injOn_sub_smul_of_notMem_closure_numericalRange hne hz ψ.2 ψ'.2
  rw [hψ, hψ']

/-- **Main theorem**: for self-adjoint `A` and `z` outside `closure (numericalRange A)`, the
equation `(A - z)ψ = φ` has a unique solution for every `φ`. -/
theorem numericalRange_range_all_z
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hne : (numericalRange A).Nonempty) (z : ℂ) (hz : z ∉ closure (numericalRange A)) :
    ∀ φ : H, ∃! (ψ : A.domain), A ψ - z • (ψ : H) = φ := by
  intro φ
  have h_range_closed := numericalRange_range_isClosed hA z hne hz
  have h_dense := numericalRange_range_dense hA z hne hz
  have h_eq_univ : Set.range (fun (ψ : A.domain) => A ψ - z • (ψ : H)) = Set.univ := by
    have h_closure := h_dense.closure_eq
    rw [IsClosed.closure_eq h_range_closed] at h_closure
    exact h_closure
  have h_exists : ∃ (ψ : A.domain), A ψ - z • (ψ : H) = φ := by
    have hmem : φ ∈ Set.univ := Set.mem_univ φ
    rw [← h_eq_univ] at hmem
    exact Set.mem_range.mp hmem
  obtain ⟨ψ, hψ⟩ := h_exists
  exact ⟨ψ, hψ, fun ψ' hψ' => (numericalRange_solution_unique hne z hz φ ψ ψ' hψ hψ').symm⟩

end Spectra.Resolvent
