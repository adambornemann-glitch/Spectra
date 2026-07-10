/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Range.NumericalRangeSurjectivity
import Spectra.Resolvent.Spectrum

/-!
# The resolvent, from the numerical range

The numerical-range analogue of `Resolvent/Range.lean` + `Resolvent/Spectrum.lean`'s
`mem_resolventSet_of_im_ne_zero`: builds the bounded resolvent `R(z) = (A - z)⁻¹` for self-adjoint
`A` and `z` outside `closure (numericalRange A)`, then uses it to prove the **marquee theorem**
of the numerical-range project — the spectrum of a self-adjoint operator lies inside the closure
of its numerical range.

## Main definitions

* `numResolvent` : the resolvent operator, as a bounded linear map.

## Main statements

* `numResolvent_sub_smul_apply` : `(A - z)(R(z)φ) = φ`, the right-inverse property.
* `numericalRange_mem_resolventSet` : `z ∈ resolventSet A` for `z ∉ closure (numericalRange A)`.
* `spectrum_subset_closure_numericalRange` : **the marquee theorem** —
  `spectrum A ⊆ {λ | (λ : ℂ) ∈ closure (numericalRange A)}`.

## Implementation notes

Constructed exactly as `Resolvent/Range.lean`'s `resolvent`, via `LinearMap.mkContinuous` from the
existence and uniqueness in `numericalRange_range_all_z`, with `1 / Metric.infDist z
(numericalRange A)` in place of `1 / |z.im|` as the continuity bound.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII.3, Problem 8.
* [Kato, *Perturbation Theory for Linear Operators*][kato1995], Section V.3.
-/

open Spectra.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.Resolvent

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hne : (numericalRange A).Nonempty)
  (z : ℂ) (hz : z ∉ closure (numericalRange A))

/-- The vector `ψ ∈ dom(A)` solving `(A - z)ψ = φ`, for self-adjoint `A`,
`z ∉ closure (numericalRange A)`. -/
private noncomputable def numResolventSolution (φ : H) : H :=
  ((Classical.choose (numericalRange_range_all_z hA hne z hz φ).exists : A.domain) : H)

/-- `numResolventSolution` lies in the domain of `A`. -/
private lemma numResolventSolution_mem (φ : H) :
    numResolventSolution hA hne z hz φ ∈ A.domain :=
  (Classical.choose (numericalRange_range_all_z hA hne z hz φ).exists : A.domain).property

/-- `numResolventSolution` solves the resolvent equation: `(A - z)ψ = φ`. -/
private lemma numResolventSolution_eq (φ : H) :
    A ⟨numResolventSolution hA hne z hz φ, numResolventSolution_mem hA hne z hz φ⟩
      - z • numResolventSolution hA hne z hz φ = φ :=
  Classical.choose_spec (numericalRange_range_all_z hA hne z hz φ).exists

/-- `numResolventSolution` is additive in its target `φ`. -/
private lemma numResolventSolution_add (φ₁ φ₂ : H) :
    numResolventSolution hA hne z hz (φ₁ + φ₂)
      = numResolventSolution hA hne z hz φ₁ + numResolventSolution hA hne z hz φ₂ := by
  set a := numResolventSolution hA hne z hz φ₁
  set b := numResolventSolution hA hne z hz φ₂
  have ha_mem := numResolventSolution_mem hA hne z hz φ₁
  have hb_mem := numResolventSolution_mem hA hne z hz φ₂
  have ha_eq := numResolventSolution_eq hA hne z hz φ₁
  have hb_eq := numResolventSolution_eq hA hne z hz φ₂
  have hab_mem : a + b ∈ A.domain := A.domain.add_mem ha_mem hb_mem
  have hab_eq : A ⟨a + b, hab_mem⟩ - z • (a + b) = φ₁ + φ₂ := by
    have op_add : A ⟨a + b, hab_mem⟩ = A ⟨a, ha_mem⟩ + A ⟨b, hb_mem⟩ := by
      rw [← A.map_add]; rfl
    rw [op_add, smul_add]
    rw [show A ⟨a, ha_mem⟩ + A ⟨b, hb_mem⟩ - (z • a + z • b)
          = (A ⟨a, ha_mem⟩ - z • a) + (A ⟨b, hb_mem⟩ - z • b) by abel]
    rw [ha_eq, hb_eq]
  have huniq := (numericalRange_range_all_z hA hne z hz (φ₁ + φ₂)).unique
    (numResolventSolution_eq hA hne z hz (φ₁ + φ₂)) hab_eq
  exact congrArg Subtype.val huniq

/-- `numResolventSolution` respects scalar multiplication of its target `φ`. -/
private lemma numResolventSolution_smul (c : ℂ) (φ : H) :
    numResolventSolution hA hne z hz (c • φ) = c • numResolventSolution hA hne z hz φ := by
  set s := numResolventSolution hA hne z hz φ
  have hs_mem := numResolventSolution_mem hA hne z hz φ
  have hs_eq := numResolventSolution_eq hA hne z hz φ
  have hcs_mem : c • s ∈ A.domain := A.domain.smul_mem c hs_mem
  have hcs_eq : A ⟨c • s, hcs_mem⟩ - z • (c • s) = c • φ := by
    have op_smul : A ⟨c • s, hcs_mem⟩ = c • A ⟨s, hs_mem⟩ := by
      rw [← A.map_smul]; rfl
    rw [op_smul, smul_comm z c, ← smul_sub, hs_eq]
  have huniq := (numericalRange_range_all_z hA hne z hz (c • φ)).unique
    (numResolventSolution_eq hA hne z hz (c • φ)) hcs_eq
  exact congrArg Subtype.val huniq

/-- The resolvent bound at the vector level:
`‖numResolventSolution …‖ ≤ (1 / dist(z, W(A))) · ‖φ‖`. -/
private lemma numResolventSolution_norm_le (φ : H) :
    ‖numResolventSolution hA hne z hz φ‖ ≤ (1 / Metric.infDist z (numericalRange A)) * ‖φ‖ := by
  have hmem := numResolventSolution_mem hA hne z hz φ
  have heq := numResolventSolution_eq hA hne z hz φ
  have hbound := infDist_mul_norm_le_norm_sub_smul z (numResolventSolution hA hne z hz φ) hmem
  rw [heq] at hbound
  have hpos : 0 < Metric.infDist z (numericalRange A) :=
    (Metric.infDist_pos_iff_notMem_closure hne).mp hz
  calc ‖numResolventSolution hA hne z hz φ‖
      = (1 / Metric.infDist z (numericalRange A))
          * (Metric.infDist z (numericalRange A) * ‖numResolventSolution hA hne z hz φ‖) := by
        field_simp
    _ ≤ (1 / Metric.infDist z (numericalRange A)) * ‖φ‖ := by
        apply mul_le_mul_of_nonneg_left hbound
        positivity

/-- The resolvent operator `R(z) = (A - zI)⁻¹` for self-adjoint `A` and
`z ∉ closure (numericalRange A)`. -/
noncomputable def numResolvent : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := numResolventSolution hA hne z hz
      map_add' := numResolventSolution_add hA hne z hz
      map_smul' := fun c φ => by simpa using numResolventSolution_smul hA hne z hz c φ }
    (1 / Metric.infDist z (numericalRange A))
    (numResolventSolution_norm_le hA hne z hz)

/-- The resolvent satisfies `‖R(z)‖ ≤ 1 / dist(z, W(A))`. -/
theorem numResolvent_bound :
    ‖numResolvent hA hne z hz‖ ≤ 1 / Metric.infDist z (numericalRange A) :=
  LinearMap.mkContinuous_norm_le _ (div_nonneg zero_le_one Metric.infDist_nonneg)
    (numResolventSolution_norm_le hA hne z hz)

/-- `R(z) φ` lies in `dom A` — the resolvent is a *right* inverse landing in the domain. -/
theorem numResolvent_apply_mem_domain (φ : H) :
    numResolvent hA hne z hz φ ∈ A.domain :=
  numResolventSolution_mem hA hne z hz φ

/-- `(A - z)(R(z) φ) = φ` — the resolvent is a right inverse of `A - z`. -/
theorem numResolvent_sub_smul_apply (φ : H) :
    A ⟨numResolvent hA hne z hz φ, numResolvent_apply_mem_domain hA hne z hz φ⟩
      - z • (numResolvent hA hne z hz φ) = φ :=
  numResolventSolution_eq hA hne z hz φ

/-- For self-adjoint `A`, every `z` outside `closure (numericalRange A)` is in the resolvent
set — witnessed by the resolvent `numResolvent`, a genuine two-sided inverse
(`numResolvent_sub_smul_apply` for the right inverse, uniqueness from
`numericalRange_range_all_z` for the left). -/
theorem numericalRange_mem_resolventSet {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hne : (numericalRange A).Nonempty) (z : ℂ) (hz : z ∉ closure (numericalRange A)) :
    z ∈ resolventSet A := by
  refine ⟨numResolvent hA hne z hz, ?_, ?_⟩
  · intro ψ
    have heq := numResolvent_sub_smul_apply hA hne z hz (A ψ - z • (ψ : H))
    have huniq := (numericalRange_range_all_z hA hne z hz (A ψ - z • (ψ : H))).unique heq rfl
    exact congrArg Subtype.val huniq
  · intro φ
    exact ⟨numResolvent_apply_mem_domain hA hne z hz φ, numResolvent_sub_smul_apply hA hne z hz φ⟩

/-- **The marquee theorem.** The spectrum of a self-adjoint operator lies inside the closure of
its numerical range: `spectrum A ⊆ closure (W(A))`. -/
theorem spectrum_subset_closure_numericalRange {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hne : (numericalRange A).Nonempty) :
    ∀ lam ∈ spectrum A, (lam : ℂ) ∈ closure (numericalRange A) := by
  intro lam hlam
  by_contra hzlam
  exact hlam (numericalRange_mem_resolventSet hA hne (lam : ℂ) hzlam)

end Spectra.Resolvent
