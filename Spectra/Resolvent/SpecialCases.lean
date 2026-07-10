/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.NormExpansion
/-!
# Resolvent at ±i

This file constructs the resolvent operators at `z = ±i` directly from the
self-adjointness criterion. These special cases are used to bootstrap the
general resolvent construction.

## Design

`z = i` and `z = -i` are mirror images of the same construction: `(A - sI)⁻¹` for a purely
imaginary unit `s`, built from an existence hypothesis `∀ φ, ∃ ψ, Aψ - sψ = φ` together with the
contraction bound `‖ψ‖ ≤ ‖Aψ - sψ‖` that symmetry (`NormExpansion.lean`) supplies at `s = ±i`. The
`## Shared construction` section below builds this once, generically in `s` and in an abstract
bound hypothesis; `## Resolvent at i` and `## Resolvent at -i` are one-line specializations at
`s = I` and `s = -I` respectively (the latter via the algebraic identity `-(-I) = I`, since the
existing `hplus`/`hminus` hypotheses are phrased as `Aψ + Iψ = φ`/`Aψ - Iψ = φ`, not `Aψ - sψ = φ`
literally). Every public name below keeps its original type signature; only the proof terms
change.

**A second, independent route to the same fact exists.** `YosidaHille/Helpers.lean`'s
`op_lower_bound`/`selfAdjoint_surjective_sub_smul` prove the analogous bound and surjectivity for
*general* `z` off the real axis, by a different technique (a Cauchy-estimate/closed-range
argument, not the symmetric cross-term-vanishing identity `NormExpansion.lean` uses here). Both
routes currently feed `CayleyTransform` independently; unifying them is a library-wide decision
(which route the deficiency-index criterion should canonically rest on) outside this file's own
scope, not attempted here.

## Main definitions

* `resolventAtImaginary`: the shared internal building block — `(A - sI)⁻¹` for an abstract purely
  imaginary `s`, generic in an existence hypothesis and a contraction bound; `resolventAtI` and
  `resolventAtNegI` below are its only two instantiations so far, at `s = I` and `s = -I`, but any
  future purely-imaginary unit can reuse it directly.
* `resolventAtI`: The resolvent `R(i) = (A - iI)⁻¹`
* `resolventAtNegI`: The resolvent `R(-i) = (A + iI)⁻¹`
* `Rminus`, `Rplus`: the underlying bare-vector solutions `R(i)φ`, `R(-i)φ`

## Main statements

* `resolventAtImaginary_unique`, `resolventAtImaginary_bound`, `resolventAtImaginary_left_inverse`:
  the generic uniqueness/contraction/left-inverse facts for `resolventAtImaginary`, from which the
  `i`/`-i` statements below are one-line specializations
* `resolvent_at_i_unique`, `resolvent_at_neg_i_unique`: solutions to `(A ∓ iI)ψ = φ` are unique
* `resolvent_at_i_bound`, `resolvent_at_neg_i_bound`: both resolvents are contractions,
  `‖R(±i)‖ ≤ 1`
* `resolvent_at_i_left_inverse`, `resolvent_at_neg_i_left_inverse`: `R(∓i)` left-inverts `A ± iI`
  on the domain

## Implementation notes

The self-adjointness criterion states that `ran(A ± iI) = H`. We use `Classical.choose` to
extract solutions and prove they are unique using the lower bound estimate from `NormExpansion`.
-/
open InnerProductSpace Complex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Spectra.Resolvent

/-! ## Shared construction: the resolvent at a purely imaginary unit `s` -/

section Imaginary

variable {A : H →ₗ.[ℂ] H} {s : ℂ}

/-- Solutions to `(A - sI)ψ = φ` are unique, given the contraction bound `‖ψ‖ ≤ ‖Aψ - sψ‖`
(supplied at `s = I` by `norm_le_norm_sub_I_smul`, at `s = -I` by `norm_le_norm_add_I_smul`). -/
lemma resolventAtImaginary_unique
    (hbound : ∀ ψ : A.domain, ‖(ψ : H)‖ ≤ ‖A ψ - s • (ψ : H)‖)
    (φ ψ₁ ψ₂ : H) (hψ₁ : ψ₁ ∈ A.domain) (hψ₂ : ψ₂ ∈ A.domain)
    (h₁ : A ⟨ψ₁, hψ₁⟩ - s • ψ₁ = φ) (h₂ : A ⟨ψ₂, hψ₂⟩ - s • ψ₂ = φ) :
    ψ₁ = ψ₂ := by
  have h_sub_mem : ψ₁ - ψ₂ ∈ A.domain := A.domain.sub_mem hψ₁ hψ₂
  have h_factor : A ⟨ψ₁ - ψ₂, h_sub_mem⟩ - s • (ψ₁ - ψ₂) = 0 := by
    have op_sub := A.map_sub ⟨ψ₁, hψ₁⟩ ⟨ψ₂, hψ₂⟩
    calc A ⟨ψ₁ - ψ₂, h_sub_mem⟩ - s • (ψ₁ - ψ₂)
        = (A ⟨ψ₁, hψ₁⟩ - A ⟨ψ₂, hψ₂⟩) - s • (ψ₁ - ψ₂) :=
          congrFun (congrArg HSub.hSub op_sub) (s • (ψ₁ - ψ₂))
      _ = (A ⟨ψ₁, hψ₁⟩ - A ⟨ψ₂, hψ₂⟩) - (s • ψ₁ - s • ψ₂) := by rw [smul_sub]
      _ = (A ⟨ψ₁, hψ₁⟩ - s • ψ₁) - (A ⟨ψ₂, hψ₂⟩ - s • ψ₂) := by abel
      _ = φ - φ := by rw [h₁, h₂]
      _ = 0 := sub_self φ
  have h_le := hbound ⟨ψ₁ - ψ₂, h_sub_mem⟩
  have : ‖ψ₁ - ψ₂‖ ≤ 0 := by
    calc ‖ψ₁ - ψ₂‖
        ≤ ‖A ⟨ψ₁ - ψ₂, h_sub_mem⟩ - s • (ψ₁ - ψ₂)‖ := h_le
      _ = ‖(0 : H)‖ := by rw [h_factor]
      _ = 0 := norm_zero
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm this (norm_nonneg _)))

/-- The `(A - sI)⁻¹φ` solution, as a bare vector in `H`. -/
noncomputable def Rimag (hex : ∀ φ : H, ∃ ψ : A.domain, A ψ - s • (ψ : H) = φ) (φ : H) : H :=
  ↑(Classical.choose (hex φ))

/-- `Rimag hex φ` lies in `dom A`. -/
lemma Rimag_mem (hex : ∀ φ : H, ∃ ψ : A.domain, A ψ - s • (ψ : H) = φ) (φ : H) :
    Rimag hex φ ∈ A.domain :=
  (Classical.choose (hex φ)).property

/-- `Rimag hex φ` satisfies `(A - sI)(Rimag hex φ) = φ`. -/
lemma Rimag_eq (hex : ∀ φ : H, ∃ ψ : A.domain, A ψ - s • (ψ : H) = φ) (φ : H) :
    A ⟨Rimag hex φ, Rimag_mem hex φ⟩ - s • Rimag hex φ = φ :=
  Classical.choose_spec (hex φ)

/-- The resolvent `(A - sI)⁻¹`, built from the existence hypothesis and the contraction bound.
Both the `i` and `-i` resolvents below are one-line specializations of this constructor. -/
noncomputable def resolventAtImaginary
    (hbound : ∀ ψ : A.domain, ‖(ψ : H)‖ ≤ ‖A ψ - s • (ψ : H)‖)
    (hex : ∀ φ : H, ∃ ψ : A.domain, A ψ - s • (ψ : H) = φ) : H →L[ℂ] H where
  toFun φ := Rimag hex φ
  map_add' φ₁ φ₂ := by
    set a := Rimag hex φ₁
    set b := Rimag hex φ₂
    have m₁ : a ∈ A.domain := Rimag_mem hex φ₁
    have m₂ : b ∈ A.domain := Rimag_mem hex φ₂
    have e₁ : A ⟨a, m₁⟩ - s • a = φ₁ := Rimag_eq hex φ₁
    have e₂ : A ⟨b, m₂⟩ - s • b = φ₂ := Rimag_eq hex φ₂
    have m_add : a + b ∈ A.domain := A.domain.add_mem m₁ m₂
    have e_add : A ⟨a + b, m_add⟩ - s • (a + b) = φ₁ + φ₂ := by
      have op_add := A.map_add ⟨a, m₁⟩ ⟨b, m₂⟩
      calc A ⟨a + b, m_add⟩ - s • (a + b)
          = (A ⟨a, m₁⟩ + A ⟨b, m₂⟩) - s • (a + b) :=
            congrFun (congrArg HSub.hSub op_add) (s • (a + b))
        _ = (A ⟨a, m₁⟩ + A ⟨b, m₂⟩) - (s • a + s • b) := by rw [smul_add]
        _ = (A ⟨a, m₁⟩ - s • a) + (A ⟨b, m₂⟩ - s • b) := by abel
        _ = φ₁ + φ₂ := by rw [e₁, e₂]
    exact (resolventAtImaginary_unique hbound (φ₁ + φ₂) (a + b) (Rimag hex (φ₁ + φ₂))
      m_add (Rimag_mem hex (φ₁ + φ₂)) e_add (Rimag_eq hex (φ₁ + φ₂))).symm
  map_smul' c φ := by
    set a := Rimag hex φ
    have m : a ∈ A.domain := Rimag_mem hex φ
    have e : A ⟨a, m⟩ - s • a = φ := Rimag_eq hex φ
    have m_smul : c • a ∈ A.domain := A.domain.smul_mem c m
    have e_smul : A ⟨c • a, m_smul⟩ - s • (c • a) = c • φ := by
      have op_smul := A.map_smul c ⟨a, m⟩
      calc A ⟨c • a, m_smul⟩ - s • (c • a)
          = c • A ⟨a, m⟩ - s • (c • a) :=
            congrFun (congrArg HSub.hSub op_smul) (s • (c • a))
        _ = c • A ⟨a, m⟩ - c • (s • a) := by rw [smul_comm]
        _ = c • (A ⟨a, m⟩ - s • a) := by rw [smul_sub]
        _ = c • φ := by rw [e]
    exact (resolventAtImaginary_unique hbound (c • φ) (c • a) (Rimag hex (c • φ))
      m_smul (Rimag_mem hex (c • φ)) e_smul (Rimag_eq hex (c • φ))).symm
  cont := by
    have lipschitz : LipschitzWith 1 (fun φ => Rimag hex φ) := by
      refine LipschitzWith.of_edist_le fun φ₁ φ₂ => ?_
      set a := Rimag hex φ₁
      set b := Rimag hex φ₂
      have m₁ : a ∈ A.domain := Rimag_mem hex φ₁
      have m₂ : b ∈ A.domain := Rimag_mem hex φ₂
      have e₁ : A ⟨a, m₁⟩ - s • a = φ₁ := Rimag_eq hex φ₁
      have e₂ : A ⟨b, m₂⟩ - s • b = φ₂ := Rimag_eq hex φ₂
      have m_sub : a - b ∈ A.domain := A.domain.sub_mem m₁ m₂
      have e_sub : A ⟨a - b, m_sub⟩ - s • (a - b) = φ₁ - φ₂ := by
        have op_sub := A.map_sub ⟨a, m₁⟩ ⟨b, m₂⟩
        calc A ⟨a - b, m_sub⟩ - s • (a - b)
            = (A ⟨a, m₁⟩ - A ⟨b, m₂⟩) - s • (a - b) :=
              congrFun (congrArg HSub.hSub op_sub) (s • (a - b))
          _ = (A ⟨a, m₁⟩ - A ⟨b, m₂⟩) - (s • a - s • b) := by rw [smul_sub]
          _ = (A ⟨a, m₁⟩ - s • a) - (A ⟨b, m₂⟩ - s • b) := by abel
          _ = φ₁ - φ₂ := by rw [e₁, e₂]
      have bound : ‖a - b‖ ≤ ‖φ₁ - φ₂‖ := by
        calc ‖a - b‖
            ≤ ‖A ⟨a - b, m_sub⟩ - s • (a - b)‖ := hbound ⟨a - b, m_sub⟩
          _ = ‖φ₁ - φ₂‖ := by rw [e_sub]
      rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
      exact ENNReal.ofReal_le_ofReal bound
    exact lipschitz.continuous

/-- The resolvent at a purely imaginary unit is a contraction: `‖(A - sI)⁻¹‖ ≤ 1`. -/
lemma resolventAtImaginary_bound
    (hbound : ∀ ψ : A.domain, ‖(ψ : H)‖ ≤ ‖A ψ - s • (ψ : H)‖)
    (hex : ∀ φ : H, ∃ ψ : A.domain, A ψ - s • (ψ : H) = φ) :
    ‖resolventAtImaginary hbound hex‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro φ
  let ψ := resolventAtImaginary hbound hex φ
  have h_mem : ψ ∈ A.domain := Rimag_mem hex φ
  have h_eq : A ⟨ψ, h_mem⟩ - s • ψ = φ := Rimag_eq hex φ
  calc ‖resolventAtImaginary hbound hex φ‖ = ‖ψ‖ := rfl
    _ ≤ ‖A ⟨ψ, h_mem⟩ - s • ψ‖ := hbound ⟨ψ, h_mem⟩
    _ = ‖φ‖ := by rw [h_eq]
    _ = 1 * ‖φ‖ := by ring

/-- `(A - sI)⁻¹` left-inverts `A - sI` on the domain: `(A - sI)⁻¹((A - sI)ψ) = ψ`. -/
lemma resolventAtImaginary_left_inverse
    (hbound : ∀ ψ : A.domain, ‖(ψ : H)‖ ≤ ‖A ψ - s • (ψ : H)‖)
    (hex : ∀ φ : H, ∃ ψ : A.domain, A ψ - s • (ψ : H) = φ)
    (ψ : H) (hψ : ψ ∈ A.domain) :
    resolventAtImaginary hbound hex (A ⟨ψ, hψ⟩ - s • ψ) = ψ := by
  set φ := A ⟨ψ, hψ⟩ - s • ψ
  set χ := resolventAtImaginary hbound hex φ
  have hχ_mem : χ ∈ A.domain := Rimag_mem hex φ
  have hχ_eq : A ⟨χ, hχ_mem⟩ - s • χ = φ := Rimag_eq hex φ
  exact resolventAtImaginary_unique hbound φ χ ψ hχ_mem hψ hχ_eq rfl

end Imaginary

/-! ## Resolvent at i -/

/-- The minus-resolvent solution `(A - iI)⁻¹ φ`, as a bare vector in `H`. -/
noncomputable def Rminus {A : H →ₗ.[ℂ] H}
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (φ : H) : H :=
  Rimag (s := I) hminus φ

/-- The minus-resolvent solution `Rminus hminus φ` lies in `dom A`. -/
lemma Rminus_mem {A : H →ₗ.[ℂ] H}
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (φ : H) :
    Rminus hminus φ ∈ A.domain :=
  Rimag_mem (s := I) hminus φ

/-- The minus-resolvent solution satisfies `(A - iI)(Rminus hminus φ) = φ`. -/
lemma Rminus_eq {A : H →ₗ.[ℂ] H}
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (φ : H) :
    A ⟨Rminus hminus φ, Rminus_mem hminus φ⟩ - I • Rminus hminus φ = φ :=
  Rimag_eq (s := I) hminus φ

/-- Solutions to `(A - iI)ψ = φ` are unique. -/
lemma resolvent_at_i_unique {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (φ ψ₁ ψ₂ : H)
    (hψ₁ : ψ₁ ∈ A.domain) (hψ₂ : ψ₂ ∈ A.domain)
    (h₁ : A ⟨ψ₁, hψ₁⟩ - I • ψ₁ = φ)
    (h₂ : A ⟨ψ₂, hψ₂⟩ - I • ψ₂ = φ) :
    ψ₁ = ψ₂ :=
  resolventAtImaginary_unique (s := I) (norm_le_norm_sub_I_smul hsym) φ ψ₁ ψ₂ hψ₁ hψ₂ h₁ h₂

/-- The resolvent at `z = i`, `R(i) = (A - iI)⁻¹`, built from the
self-adjointness criterion. -/
noncomputable def resolventAtI {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) : H →L[ℂ] H :=
  resolventAtImaginary (s := I) (norm_le_norm_sub_I_smul hsym) hminus

/-! ## Resolvent at -i -/

/-- The existence hypothesis at `-i`, converted to the `(A - sI)ψ = φ` shape at `s = -I`
(`A ψ - (-I) • ψ = A ψ + I • ψ`, algebraically). -/
private lemma hplus_toImaginary {A : H →ₗ.[ℂ] H}
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) :
    ∀ φ : H, ∃ ψ : A.domain, A ψ - (-I) • (ψ : H) = φ := fun φ => by
  obtain ⟨ψ, hψ⟩ := hplus φ
  exact ⟨ψ, by rwa [neg_smul, sub_neg_eq_add]⟩

/-- The contraction bound at `-i`, converted to the `‖ψ‖ ≤ ‖Aψ - sψ‖` shape at `s = -I`. -/
private lemma bound_negI {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) :
    ∀ ψ : A.domain, ‖(ψ : H)‖ ≤ ‖A ψ - (-I) • (ψ : H)‖ := fun ψ => by
  rw [neg_smul, sub_neg_eq_add]; exact norm_le_norm_add_I_smul hsym ψ

/-- The plus-resolvent solution `(A + iI)⁻¹ φ`, as a bare vector in `H`. -/
noncomputable def Rplus {A : H →ₗ.[ℂ] H}
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (φ : H) : H :=
  Rimag (s := -I) (hplus_toImaginary hplus) φ

/-- The plus-resolvent solution `Rplus hplus φ` lies in `dom A`. -/
lemma Rplus_mem {A : H →ₗ.[ℂ] H}
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (φ : H) :
    Rplus hplus φ ∈ A.domain :=
  Rimag_mem (s := -I) (hplus_toImaginary hplus) φ

/-- The plus-resolvent solution satisfies `(A + iI)(Rplus hplus φ) = φ`. -/
lemma Rplus_eq {A : H →ₗ.[ℂ] H}
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (φ : H) :
    A ⟨Rplus hplus φ, Rplus_mem hplus φ⟩ + I • Rplus hplus φ = φ := by
  have h := Rimag_eq (s := -I) (hplus_toImaginary hplus) φ
  rwa [neg_smul, sub_neg_eq_add] at h

/-- Solutions to `(A + iI)ψ = φ` are unique. -/
lemma resolvent_at_neg_i_unique {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (φ ψ₁ ψ₂ : H)
    (hψ₁ : ψ₁ ∈ A.domain) (hψ₂ : ψ₂ ∈ A.domain)
    (h₁ : A ⟨ψ₁, hψ₁⟩ + I • ψ₁ = φ)
    (h₂ : A ⟨ψ₂, hψ₂⟩ + I • ψ₂ = φ) :
    ψ₁ = ψ₂ :=
  resolventAtImaginary_unique (s := -I) (bound_negI hsym) φ ψ₁ ψ₂ hψ₁ hψ₂
    (by rwa [neg_smul, sub_neg_eq_add]) (by rwa [neg_smul, sub_neg_eq_add])

/-- The resolvent at `z = -i`, `R(-i) = (A + iI)⁻¹`, built from the
self-adjointness criterion. -/
noncomputable def resolventAtNegI {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) : H →L[ℂ] H :=
  resolventAtImaginary (s := -I) (bound_negI hsym) (hplus_toImaginary hplus)

/-! ## Bounds -/

/-- The resolvent at `i` is a contraction: `‖R(i)‖ ≤ 1`. -/
lemma resolvent_at_i_bound {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) :
    ‖resolventAtI hsym hminus‖ ≤ 1 :=
  resolventAtImaginary_bound (s := I) (norm_le_norm_sub_I_smul hsym) hminus

/-- The resolvent at `-i` is a contraction: `‖R(-i)‖ ≤ 1`. -/
lemma resolvent_at_neg_i_bound {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) :
    ‖resolventAtNegI hsym hplus‖ ≤ 1 :=
  resolventAtImaginary_bound (s := -I) (bound_negI hsym) (hplus_toImaginary hplus)

/-! ## Left inverse property -/

/-- `R(i)` left-inverts `A - iI` on the domain: `R(i)((A - iI)ψ) = ψ`. -/
lemma resolvent_at_i_left_inverse {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (ψ : H) (hψ : ψ ∈ A.domain) :
    resolventAtI hsym hminus (A ⟨ψ, hψ⟩ - I • ψ) = ψ :=
  resolventAtImaginary_left_inverse (s := I) (norm_le_norm_sub_I_smul hsym) hminus ψ hψ

/-- `R(-i)` left-inverts `A + iI` on the domain: `R(-i)((A + iI)ψ) = ψ`. -/
lemma resolvent_at_neg_i_left_inverse {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (ψ : H) (hψ : ψ ∈ A.domain) :
    resolventAtNegI hsym hplus (A ⟨ψ, hψ⟩ + I • ψ) = ψ := by
  have h := resolventAtImaginary_left_inverse (s := -I) (bound_negI hsym) (hplus_toImaginary hplus)
    ψ hψ
  rwa [neg_smul, sub_neg_eq_add] at h

end Spectra.Resolvent
