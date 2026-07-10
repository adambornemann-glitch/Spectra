/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.EssentialSelfAdjointness

/-!
# Essential self-adjointness of a sum, on a common domain

The Kato–Rellich *companion*: given two symmetric operators `A`, `B` on a common dense domain
(in particular, `A` and `B` may themselves be the restrictions of bigger self-adjoint operators
to a shared *core* — the "common core" scenario is exactly this special case, obtained by
pre-restricting via `LinearPMap.domRestrict` before calling into this file), `A + B` is again
symmetric on that common domain. Unlike Kato–Rellich, essential self-adjointness of the sum is
**not automatic** from relative-boundedness here: Nelson's counterexample (Reed–Simon VIII.6,
already flagged in `Operator/Composite.lean`'s docstring) shows two individually-nice symmetric
operators on a shared core can have a sum that fails essential self-adjointness on that core.
So the deficiency condition — dense range of `(A + B) ± i` — must be verified *directly*, exactly
as Kato–Rellich requires its relative-bound hypothesis to be verified directly. What this file
supplies is the well-posedness of the sum plus the reduction of essential self-adjointness to
that single, honestly-stated deficiency condition.

## Main definitions

* `sumOp A B` — the operator `A + B`, defined on `A.domain ⊓ B.domain`.

## Main statements

* `sumOp_apply` — the defining formula.
* `sumOp_isFormalAdjoint` — the sum of two symmetric operators is symmetric.
* `isEssentiallySelfAdjoint_sumOp_of_denseRange_addSub` — **the companion theorem**: given the
  deficiency condition for the sum directly, `A + B` is essentially self-adjoint.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII.6.
* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975], Theorem X.12.
-/
open Complex
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.Operator

/-- The sum `A + B` of two operators, defined on the common domain `A.domain ⊓ B.domain`. -/
def sumOp (A B : H →ₗ.[ℂ] H) : H →ₗ.[ℂ] H where
  domain := A.domain ⊓ B.domain
  toFun := A.toFun.comp (Submodule.inclusion inf_le_left)
    + B.toFun.comp (Submodule.inclusion inf_le_right)

omit [CompleteSpace H] in
@[simp] lemma sumOp_domain (A B : H →ₗ.[ℂ] H) : (sumOp A B).domain = A.domain ⊓ B.domain := rfl

omit [CompleteSpace H] in
/-- The defining formula: `(A + B) x = A x + B x`. -/
lemma sumOp_apply (A B : H →ₗ.[ℂ] H) (x : (sumOp A B).domain) :
    sumOp A B x = A ⟨(x : H), (Submodule.mem_inf.mp x.2).1⟩
      + B ⟨(x : H), (Submodule.mem_inf.mp x.2).2⟩ := rfl

omit [CompleteSpace H] in
/-- The sum of two symmetric operators is symmetric on their common domain. -/
theorem sumOp_isFormalAdjoint {A B : H →ₗ.[ℂ] H} (hA : A.IsFormalAdjoint A)
    (hB : B.IsFormalAdjoint B) : (sumOp A B).IsFormalAdjoint (sumOp A B) := by
  intro x y
  rw [sumOp_apply, sumOp_apply, inner_add_left, inner_add_right,
    hA ⟨(x : H), (Submodule.mem_inf.mp x.2).1⟩ ⟨(y : H), (Submodule.mem_inf.mp y.2).1⟩,
    hB ⟨(x : H), (Submodule.mem_inf.mp x.2).2⟩ ⟨(y : H), (Submodule.mem_inf.mp y.2).2⟩]

/-- **The Kato–Rellich companion.** Given symmetric `A`, `B` on a common domain, if the
deficiency condition for the sum is verified *directly* — `ran((A+B) ± i)` dense — then
`A + B` is essentially self-adjoint. This is deliberately not automatic from `A`, `B` being
individually nice: see the module docstring (Nelson's counterexample). -/
theorem isEssentiallySelfAdjoint_sumOp_of_denseRange_addSub {A B : H →ₗ.[ℂ] H}
    (hA : A.IsFormalAdjoint A) (hB : B.IsFormalAdjoint B)
    (hdense : Dense ((sumOp A B).domain : Set H))
    (hplus : Dense (Set.range fun x : (sumOp A B).domain => sumOp A B x + I • (x : H)))
    (hminus : Dense (Set.range fun x : (sumOp A B).domain => sumOp A B x - I • (x : H))) :
    IsEssentiallySelfAdjoint (sumOp A B) :=
  isEssentiallySelfAdjoint_of_denseRange_addSub (sumOp_isFormalAdjoint hA hB) hdense hplus hminus

end Spectra.Operator
