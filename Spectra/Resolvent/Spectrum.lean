/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Range
import Spectra.YosidaHille.Helpers
/-!
# The spectrum of an unbounded self-adjoint operator

`Spectra.Resolvent.spectrum A : Set ℝ` is the complement (within ℝ) of the **resolvent set**
`resolventSet A : Set ℂ` — the set of `z` for which `A - z` admits a two-sided bounded inverse.

Mathlib's `spectrum`/`resolventSet` live on *algebra elements*; an unbounded operator is a
`LinearPMap` with no everywhere-defined multiplication, so they do not apply.  We use the
operator-theoretic definition directly.

For a self-adjoint `A`, `A - z` is bijective with bounded inverse for **every** `z` with
`Im z ≠ 0` (`mem_resolventSet_of_im_ne_zero`, witnessed by the resolvent built in
`Resolvent.Range`).  Hence the spectrum is genuinely a subset of the real line — which is why
`spectrum` is valued in `Set ℝ`.

## Main definitions

* `Spectra.Resolvent.resolventSet`
* `Spectra.Resolvent.spectrum`

## Main statements

* `mem_resolventSet_of_im_ne_zero` : off the real axis lies in the resolvent set (self-adjoint `A`).
* `mem_resolventSet_of_isFormalAdjoint_of_surjective` : the same fact from raw formal-adjoint and
  `±i`-surjectivity hypotheses, without assuming the packaged `IsSelfAdjoint` predicate — this is
  where the analytic work (via `resolvent`, `Resolvent.Range`) actually happens, and
  `mem_resolventSet_of_im_ne_zero` is a one-line specialization of it.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII.
-/
open Complex
open Spectra.YosidaHille
namespace Spectra.Resolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The **resolvent set** of `A`: those `z : ℂ` for which `A - z` admits a two-sided bounded
inverse `R : H →L[ℂ] H` — a left inverse on `dom A` and a right inverse on all of `H`
(with `R φ` landing back in `dom A`). -/
def resolventSet (A : H →ₗ.[ℂ] H) : Set ℂ :=
  { z | ∃ R : H →L[ℂ] H,
      (∀ ψ : A.domain, R (A ψ - z • (ψ : H)) = (ψ : H)) ∧
      (∀ φ : H, ∃ h : R φ ∈ A.domain, A ⟨R φ, h⟩ - z • R φ = φ) }

/-- The **spectrum** of `A`, as a subset of `ℝ`: the real `λ` for which `A - λ` is *not*
boundedly invertible.  For self-adjoint `A` every non-real point is in the resolvent set
(`mem_resolventSet_of_im_ne_zero`), so this captures the entire spectrum. -/
def spectrum (A : H →ₗ.[ℂ] H) : Set ℝ := { lam : ℝ | (lam : ℂ) ∉ resolventSet A }

/-- For a formally self-adjoint `A` with `±i` deficiency-surjectivity, every `z` off the real
axis is in the resolvent set — witnessed by the resolvent `R(z)`, which is a genuine two-sided
inverse (`resolvent_sub_smul_apply` for the right inverse, uniqueness from
`self_adjoint_range_all_z` for the left). Takes the raw formal-adjoint and surjectivity
hypotheses directly, rather than the packaged `IsSelfAdjoint A`; see
`mem_resolventSet_of_im_ne_zero` for the convenience form built from that predicate. -/
theorem mem_resolventSet_of_isFormalAdjoint_of_surjective {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    {z : ℂ} (hz : z.im ≠ 0) : z ∈ resolventSet A := by
  refine ⟨resolvent z hz hsym hplus hminus, ?_, ?_⟩
  · intro ψ
    have heq := resolvent_sub_smul_apply z hz hsym hplus hminus (A ψ - z • (ψ : H))
    have huniq := (self_adjoint_range_all_z hsym hplus hminus z hz (A ψ - z • (ψ : H))).unique
      heq rfl
    exact congrArg Subtype.val huniq
  · intro φ
    exact ⟨resolvent_apply_mem_domain z hz hsym hplus hminus φ,
      resolvent_sub_smul_apply z hz hsym hplus hminus φ⟩

/-- For a self-adjoint `A`, every `z` off the real axis is in the resolvent set.  Self-adjointness
supplies the formal-adjoint and `±i`-surjectivity hypotheses, so no extra assumptions are needed. -/
theorem mem_resolventSet_of_im_ne_zero {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {z : ℂ} (hz : z.im ≠ 0) : z ∈ resolventSet A := by
  have hsym : A.IsFormalAdjoint A := by
    have h := A.adjoint_isFormalAdjoint hA.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp hA] at h
  exact mem_resolventSet_of_isFormalAdjoint_of_surjective hsym (isSelfAdjoint_to_surjective hA).1
    (isSelfAdjoint_to_surjective hA).2 hz

end Spectra.Resolvent
