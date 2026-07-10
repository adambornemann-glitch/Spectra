/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.AdjointClosure
import Spectra.YosidaHille.Helpers
import Spectra.Operator.KatoRellich

/-!
# Essential self-adjointness

`B` is **essentially self-adjoint** iff its closure `B.closure` is self-adjoint — the standard
notion (Reed–Simon, Theorem VIII.3): a symmetric, densely-defined `B` is essentially self-adjoint
iff its deficiency indices vanish, i.e. `ran(B + i)` and `ran(B - i)` are each *dense* in `H`
(not necessarily all of `H` — that stronger condition gives `B` itself self-adjoint, already
covered by `Spectra.Operator.isSelfAdjoint_of_surjective_addSub_smul`).

## Main definitions

* `IsEssentiallySelfAdjoint`

## Main statements

* `isEssentiallySelfAdjoint_of_denseRange_addSub` — the dense-range von Neumann criterion: a
  symmetric, densely-defined `B` with `ran(B ± i)` dense is essentially self-adjoint.

## Proof idea

`B.closure` is closed (`symmetric_isClosable`) and symmetric (`B.closure ≤ B.closure.adjoint`,
via `closure_adjoint_eq_adjoint` transporting `B.closure ≤ B.adjoint`). So `Spectra.YosidaHille.
op_range_isClosed` already gives `ran(B.closure ± i)` *closed*; the hypotheses `hplus`/`hminus`
transport (via `B ≤ B.closure`) to give it *dense* too. Closed + dense = all of `H`, i.e. full
surjectivity — which feeds directly into the library's own
`isSelfAdjoint_of_surjective_addSub_smul` (at height `μ = 1`) to conclude.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Theorem VIII.3.
* [Weidmann, *Linear Operators in Hilbert Spaces*][weidmann1980].
-/
open Complex
open Spectra.YosidaHille
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.Operator

/-- `B` is **essentially self-adjoint**: its closure is self-adjoint. -/
def IsEssentiallySelfAdjoint (B : H →ₗ.[ℂ] H) : Prop := IsSelfAdjoint B.closure

/-- **The dense-range von Neumann criterion.** A symmetric, densely-defined `B` with
`ran(B + i)` and `ran(B - i)` each dense (not necessarily surjective) is essentially
self-adjoint. -/
theorem isEssentiallySelfAdjoint_of_denseRange_addSub {B : H →ₗ.[ℂ] H}
    (hsym : B.IsFormalAdjoint B) (hdense : Dense (B.domain : Set H))
    (hplus : Dense (Set.range fun x : B.domain => B x + I • (x : H)))
    (hminus : Dense (Set.range fun x : B.domain => B x - I • (x : H))) :
    IsEssentiallySelfAdjoint B := by
  have hclosable : B.IsClosable := symmetric_isClosable hsym hdense
  have hcl_le_adj : B.closure ≤ B.adjoint := closure_le_adjoint hsym hdense
  have hcl_adj_eq : B.closure.adjoint = B.adjoint := closure_adjoint_eq_adjoint hdense hclosable
  have hdenseC : Dense (B.closure.domain : Set H) := dense_closure_domain hdense
  have hcl_le_cladj : B.closure ≤ B.closure.adjoint := hcl_adj_eq ▸ hcl_le_adj
  have hsymC : B.closure.IsFormalAdjoint B.closure :=
    isFormalAdjoint_of_le_adjoint hdenseC hcl_le_cladj
  have hclosedC : IsClosed (B.closure.graph : Set (H × H)) := hclosable.closure_isClosed
  -- `ran(B.closure ± I)` is closed (symmetric + closed graph) …
  have hclosed_plus :
      IsClosed (Set.range fun x : B.closure.domain => B.closure x + I • (x : H)) := by
    have h := op_range_isClosed hsymC hclosedC (-I) (by simp)
    simpa [neg_smul, sub_neg_eq_add] using h
  have hclosed_minus : IsClosed (Set.range fun x : B.closure.domain => B.closure x - I • (x : H)) :=
    op_range_isClosed hsymC hclosedC I (by simp)
  -- … and dense (transported from `hplus`/`hminus` along `B ≤ B.closure`).
  have hdense_plus : Dense (Set.range fun x : B.closure.domain => B.closure x + I • (x : H)) := by
    apply hplus.mono
    rintro φ ⟨x, rfl⟩
    refine ⟨⟨(x : H), (B.le_closure).1 x.2⟩, ?_⟩
    have heq : B.closure (⟨(x : H), (B.le_closure).1 x.2⟩ : B.closure.domain) = B x :=
      ((B.le_closure).2 (x := x) (y := ⟨(x : H), (B.le_closure).1 x.2⟩) rfl).symm
    simp only [heq]
  have hdense_minus : Dense (Set.range fun x : B.closure.domain => B.closure x - I • (x : H)) := by
    apply hminus.mono
    rintro φ ⟨x, rfl⟩
    refine ⟨⟨(x : H), (B.le_closure).1 x.2⟩, ?_⟩
    have heq : B.closure (⟨(x : H), (B.le_closure).1 x.2⟩ : B.closure.domain) = B x :=
      ((B.le_closure).2 (x := x) (y := ⟨(x : H), (B.le_closure).1 x.2⟩) rfl).symm
    simp only [heq]
  -- closed + dense = the whole space, i.e. full surjectivity.
  have hsurj_plus : ∀ φ : H, ∃ ψ : B.closure.domain, B.closure ψ + I • (ψ : H) = φ := by
    intro φ
    have huniv : Set.range (fun x : B.closure.domain => B.closure x + I • (x : H)) = Set.univ := by
      rw [← hclosed_plus.closure_eq]; exact hdense_plus.closure_eq
    have hmem : φ ∈ Set.range (fun x : B.closure.domain => B.closure x + I • (x : H)) := by
      rw [huniv]; trivial
    obtain ⟨ψ, hψ⟩ := hmem
    exact ⟨ψ, hψ⟩
  have hsurj_minus : ∀ φ : H, ∃ ψ : B.closure.domain, B.closure ψ - I • (ψ : H) = φ := by
    intro φ
    have huniv : Set.range (fun x : B.closure.domain => B.closure x - I • (x : H)) = Set.univ := by
      rw [← hclosed_minus.closure_eq]; exact hdense_minus.closure_eq
    have hmem : φ ∈ Set.range (fun x : B.closure.domain => B.closure x - I • (x : H)) := by
      rw [huniv]; trivial
    obtain ⟨ψ, hψ⟩ := hmem
    exact ⟨ψ, hψ⟩
  exact isSelfAdjoint_of_surjective_addSub_smul B.closure hsymC hdenseC 1
    (by simpa using hsurj_plus) (by simpa using hsurj_minus)

end Spectra.Operator
