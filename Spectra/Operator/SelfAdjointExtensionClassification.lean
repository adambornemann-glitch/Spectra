/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.VonNeumannExtensionSelfAdjoint
import Spectra.Operator.SelfAdjointExtension

/-!
# Von Neumann's classification of self-adjoint extensions

This file completes the von Neumann extension theory (N3d): the correspondence
`V ↦ A_V` between deficiency unitaries and self-adjoint extensions is a **bijection**.

*Completeness*: every self-adjoint extension `B ≥ A` equals the von Neumann extension at the
deficiency identification `inducedDeficiencyEquiv` it induces (the restriction of its own
Cayley transform) — on the nose for closed `A`
(`eq_vonNeumannExtension_inducedDeficiencyEquiv`), after closure in general
(`eq_closure_vonNeumannExtension_inducedDeficiencyEquiv`). The engine is the **Cayley defect**
computation: for the Cayley transform `C` of `B` and any `φ = Bψ + iψ`,

  `φ - Cφ = 2i·ψ ∈ D(B)`   and   `B(φ - Cφ) = iφ + iCφ`,

so every defect vector `η - Vη = η - C η` of the induced identification lies in `D(B)` with
the correct action — giving `A_V ≤ B`, whence equality by maximality of self-adjoint
operators (`Spectra.YosidaHille.IsSelfAdjoint.eq_of_le`).

*Injectivity*: `A_V = A_W` forces `V = W` (`vonNeumannExtension_injective`), because
`δ = Wη - Vη` lies in `N₋(A) ∩ D(A_V)`, where the (symmetric!) extension acts as `A*` does on
`N₋(A)` — as `-i` — and symmetric operators admit no nonreal eigenvalues
(`eq_zero_of_mem_deficiencySubspaceMinus_of_mem_vonNeumannDomain`). No closedness is needed
for injectivity.

*Classification*: for closed symmetric densely-defined `A` the two halves package into
`∃! V, B = A_V` (`existsUnique_vonNeumannExtension_eq`) and into an explicit bijection

  `{B // IsSelfAdjoint B ∧ A ≤ B} ≃ (N₊(A) ≃ₗᵢ[ℂ] N₋(A))`

(`selfAdjointExtensionEquiv`) — von Neumann's classification theorem in full.

## Main statements

* `sub_cayleyEquiv_mem_domain` / `apply_sub_cayleyEquiv` — the Cayley defect lemmas.
* `vonNeumannExtension_inducedDeficiencyEquiv_le` — `A_{V_B} ≤ B`.
* `eq_vonNeumannExtension_inducedDeficiencyEquiv` — completeness for closed `A`.
* `eq_closure_vonNeumannExtension_inducedDeficiencyEquiv` — completeness in general.
* `vonNeumannExtension_injective` — injectivity of `V ↦ A_V`.
* `existsUnique_vonNeumannExtension_eq` — `∃! V, B = A_V` (closed `A`).
* `selfAdjointExtensionEquiv` — **von Neumann's classification**, as an `Equiv`.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975], Theorem X.2.
* [Akhiezer, Glazman, *Theory of Linear Operators in Hilbert Space*][akhiezer1993].
-/

open Complex
open scoped InnerProductSpace

namespace Spectra.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The Cayley defect `φ - Cφ` of a self-adjoint operator

For `B` symmetric with surjective `B ± i` and `C` its Cayley transform, writing `φ = Bψ + iψ`
gives `Cφ = Bψ - iψ`, hence `φ - Cφ = 2i·ψ ∈ D(B)` and `B(φ - Cφ) = 2i·Bψ = iφ + iCφ`. -/

omit [CompleteSpace H] in
/-- **Collapse formula**: if `φ = Bψ + iψ`, the Cayley defect is `φ - Cφ = (2i)·ψ`. -/
lemma sub_cayleyEquiv_eq_two_smul {B : H →ₗ.[ℂ] H} (hsym : B.IsFormalAdjoint B)
    (hplus : ∀ φ : H, ∃ ψ : B.domain, B ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : B.domain, B ψ - I • (ψ : H) = φ)
    {φ : H} {ψ : B.domain} (hψ : B ψ + I • (ψ : H) = φ) :
    φ - cayleyEquiv hsym hplus hminus φ = (2 * I) • (ψ : H) := by
  rw [cayleyEquiv_apply, ← hψ,
    Spectra.Cayley.cayleyTransform_apply_resolvent hsym hplus ψ]
  module

omit [CompleteSpace H] in
/-- The Cayley defect `φ - Cφ` lies in the domain of `B`. -/
lemma sub_cayleyEquiv_mem_domain {B : H →ₗ.[ℂ] H} (hsym : B.IsFormalAdjoint B)
    (hplus : ∀ φ : H, ∃ ψ : B.domain, B ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : B.domain, B ψ - I • (ψ : H) = φ) (φ : H) :
    φ - cayleyEquiv hsym hplus hminus φ ∈ B.domain := by
  obtain ⟨ψ, hψ⟩ := hplus φ
  rw [sub_cayleyEquiv_eq_two_smul hsym hplus hminus hψ]
  exact B.domain.smul_mem _ ψ.2

omit [CompleteSpace H] in
/-- Action on the Cayley defect: `B (φ - Cφ) = iφ + iCφ`. -/
lemma apply_sub_cayleyEquiv {B : H →ₗ.[ℂ] H} (hsym : B.IsFormalAdjoint B)
    (hplus : ∀ φ : H, ∃ ψ : B.domain, B ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : B.domain, B ψ - I • (ψ : H) = φ) (φ : H)
    (h : φ - cayleyEquiv hsym hplus hminus φ ∈ B.domain) :
    B ⟨φ - cayleyEquiv hsym hplus hminus φ, h⟩
      = I • φ + I • (cayleyEquiv hsym hplus hminus φ) := by
  obtain ⟨ψ, hψ⟩ := hplus φ
  have hEφ : cayleyEquiv hsym hplus hminus φ = B ψ - I • (ψ : H) := by
    rw [cayleyEquiv_apply, ← hψ]
    exact Spectra.Cayley.cayleyTransform_apply_resolvent hsym hplus ψ
  have harg : (⟨φ - cayleyEquiv hsym hplus hminus φ, h⟩ : B.domain) = (2 * I) • ψ :=
    Subtype.ext ((sub_cayleyEquiv_eq_two_smul hsym hplus hminus hψ).trans
      (Submodule.coe_smul (2 * I) ψ).symm)
  rw [harg, LinearPMap.map_smul, hEφ, ← hψ]
  module

/-! ### Completeness -/

/-- The von Neumann extension at the induced deficiency identification is contained in the
extension that induced it: every defect vector `η - Vη` is a Cayley defect of `B`, hence lies
in `D(B)` with the matching action. -/
theorem vonNeumannExtension_inducedDeficiencyEquiv_le {A B : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A) (hdense : Dense (A.domain : Set H))
    (hB : IsSelfAdjoint B) (hAB : A ≤ B) :
    vonNeumannExtension A hsym hdense (inducedDeficiencyEquiv hdense hB hAB) ≤ B := by
  -- every defect vector `η - Vη` is a Cayley defect of `B`, hence lies in `D(B)`
  have hdefect : ∀ η : deficiencySubspacePlus A,
      (η : H) - ((inducedDeficiencyEquiv hdense hB hAB η : deficiencySubspaceMinus A) : H)
        ∈ B.domain := by
    intro η
    rw [inducedDeficiencyEquiv_apply_coe]
    exact sub_cayleyEquiv_mem_domain _ _ _ (η : H)
  refine ⟨?_, ?_⟩
  · -- domain inclusion: `D(A) ⊔ ran(1 - V) ≤ D(B)`
    intro v hv
    obtain ⟨x, η, rfl⟩ := vonNeumannDomain_cases A
      (show v ∈ vonNeumannDomain A (inducedDeficiencyEquiv hdense hB hAB) from hv)
    have hmem := B.domain.add_mem (hAB.1 x.2) (hdefect η)
    rwa [← add_sub_assoc] at hmem
  · -- value agreement: `A_V (x + η - Vη) = Ax + iη + iVη = B(x) + B(η - Vη) = B w`
    intro u w huw
    obtain ⟨x, η, hu⟩ := vonNeumannDomain_cases A
      (show (u : H) ∈ vonNeumannDomain A (inducedDeficiencyEquiv hdense hB hAB) from u.2)
    rw [vonNeumannExtension_apply_add_defect A hsym hdense
      (inducedDeficiencyEquiv hdense hB hAB) x η u hu]
    have hx : (x : H) ∈ B.domain := hAB.1 x.2
    have hd := hdefect η
    have hregroup : (x : H) + (η : H)
        - ((inducedDeficiencyEquiv hdense hB hAB η : deficiencySubspaceMinus A) : H)
        = (x : H) + ((η : H)
          - ((inducedDeficiencyEquiv hdense hB hAB η : deficiencySubspaceMinus A) : H)) := by
      rw [add_sub_assoc]
    have hwsum : w = ⟨(x : H), hx⟩
        + ⟨(η : H)
            - ((inducedDeficiencyEquiv hdense hB hAB η : deficiencySubspaceMinus A) : H), hd⟩ :=
      Subtype.ext ((huw.symm.trans hu).trans hregroup)
    have hAx : A x = B ⟨(x : H), hx⟩ := hAB.2 (x := x) (y := ⟨(x : H), hx⟩) rfl
    have hBd : B ⟨(η : H)
        - ((inducedDeficiencyEquiv hdense hB hAB η : deficiencySubspaceMinus A) : H), hd⟩
        = I • (η : H)
          + I • ((inducedDeficiencyEquiv hdense hB hAB η : deficiencySubspaceMinus A) : H) := by
    -- `simp only` (not `rw`) for the rewrite under the dependent membership proof
      simp only [inducedDeficiencyEquiv_apply_coe]
      exact apply_sub_cayleyEquiv _ _ _ _ _
    rw [hwsum, LinearPMap.map_add, ← hAx, hBd, add_assoc]

/-- **Completeness, general form**: every self-adjoint extension of a symmetric
densely-defined operator is the closure of a von Neumann extension — the one at the
deficiency identification induced by its own Cayley transform. -/
theorem eq_closure_vonNeumannExtension_inducedDeficiencyEquiv {A B : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A) (hdense : Dense (A.domain : Set H))
    (hB : IsSelfAdjoint B) (hAB : A ≤ B) :
    B = (vonNeumannExtension A hsym hdense (inducedDeficiencyEquiv hdense hB hAB)).closure := by
  have hBclosed : B.IsClosed := hB.isClosed
  have hle : (vonNeumannExtension A hsym hdense (inducedDeficiencyEquiv hdense hB hAB)).closure
      ≤ B := by
    have h := hBclosed.isClosable.closure_mono
      (vonNeumannExtension_inducedDeficiencyEquiv_le hsym hdense hB hAB)
    rwa [IsClosed.closure_eq_self hBclosed] at h
  exact (Spectra.YosidaHille.IsSelfAdjoint.eq_of_le
    (vonNeumannExtension_isEssentiallySelfAdjoint A hsym hdense
      (inducedDeficiencyEquiv hdense hB hAB)) hB hle).symm

/-- **Completeness, closed case**: every self-adjoint extension of a CLOSED symmetric
densely-defined operator IS a von Neumann extension. -/
theorem eq_vonNeumannExtension_inducedDeficiencyEquiv {A B : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A) (hdense : Dense (A.domain : Set H))
    (hclosed : IsClosed (A.graph : Set (H × H)))
    (hB : IsSelfAdjoint B) (hAB : A ≤ B) :
    B = vonNeumannExtension A hsym hdense (inducedDeficiencyEquiv hdense hB hAB) :=
  (Spectra.YosidaHille.IsSelfAdjoint.eq_of_le
    (vonNeumannExtension_isSelfAdjoint A hsym hdense hclosed
      (inducedDeficiencyEquiv hdense hB hAB))
    hB (vonNeumannExtension_inducedDeficiencyEquiv_le hsym hdense hB hAB)).symm

/-! ### Injectivity -/

/-- A deficiency vector in `N₋(A)` lying in the extension domain must vanish: the extension is
symmetric, but `A*` acts on `N₋(A)` as `-i`, and symmetric operators have no nonreal
eigenvalues. -/
theorem eq_zero_of_mem_deficiencySubspaceMinus_of_mem_vonNeumannDomain
    (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A) (hdense : Dense (A.domain : Set H))
    (V : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A)
    {χ : H} (hχ : χ ∈ deficiencySubspaceMinus A) (hdom : χ ∈ vonNeumannDomain A V) :
    χ = 0 := by
  have hdom' : χ ∈ (vonNeumannExtension A hsym hdense V).domain := hdom
  -- `A_V` acts on `χ` as the adjoint does: `A_V χ = -iχ`
  have hval : vonNeumannExtension A hsym hdense V ⟨χ, hdom'⟩ = (-I) • χ :=
    (vonNeumannExtension_apply A hsym hdense V ⟨χ, hdom'⟩).trans
      (adjoint_apply_of_mem_deficiencySubspaceMinus A hχ _)
  -- symmetry of the extension at `(χ, χ)`
  have hkey : ⟪vonNeumannExtension A hsym hdense V ⟨χ, hdom'⟩, χ⟫_ℂ
      = ⟪χ, vonNeumannExtension A hsym hdense V ⟨χ, hdom'⟩⟫_ℂ :=
    vonNeumannExtension_isFormalAdjoint A hsym hdense V ⟨χ, hdom'⟩ ⟨χ, hdom'⟩
  rw [hval, inner_smul_left, inner_smul_right, Complex.conj_neg_I] at hkey
  -- `hkey : I * ⟪χ, χ⟫ = -I * ⟪χ, χ⟫`, so `2i⟪χ, χ⟫ = 0` and `⟪χ, χ⟫ = 0`
  have hs := sub_eq_zero.mpr hkey
  have h2 : (2 * I) * ⟪χ, χ⟫_ℂ = 0 :=
    calc (2 * I) * ⟪χ, χ⟫_ℂ = I * ⟪χ, χ⟫_ℂ - -I * ⟪χ, χ⟫_ℂ := by ring
    _ = 0 := hs
  have hinner : ⟪χ, χ⟫_ℂ = 0 :=
    (mul_eq_zero.mp h2).resolve_left (mul_ne_zero two_ne_zero I_ne_zero)
  exact inner_self_eq_zero.mp hinner

/-- **Injectivity of the von Neumann correspondence**: distinct deficiency unitaries give
distinct extensions. If `A_V = A_W`, then `δ = Wη - Vη` lies in `N₋(A) ∩ D(A_V)`, hence
vanishes. No closedness of `A` is needed, and the equality of extensions is consumed only
through the equality of their domains. -/
theorem vonNeumannExtension_injective (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) :
    Function.Injective (vonNeumannExtension A hsym hdense) := by
  intro V W h
  -- the extensions agree, so their domains agree
  have hdomeq : vonNeumannDomain A V = vonNeumannDomain A W := by
    have h' := congrArg LinearPMap.domain h
    rwa [vonNeumannExtension_domain, vonNeumannExtension_domain] at h'
  refine LinearIsometryEquiv.ext fun η => Subtype.ext ?_
  -- both defect vectors `η - Vη` and `η - Wη` lie in `D(A_V)`
  have hdV : (η : H) - ((V η : deficiencySubspaceMinus A) : H) ∈ vonNeumannDomain A V := by
    simpa using mem_vonNeumannDomain A V 0 η
  have hdW : (η : H) - ((W η : deficiencySubspaceMinus A) : H) ∈ vonNeumannDomain A V := by
    rw [hdomeq]
    simpa using mem_vonNeumannDomain A W 0 η
  -- hence their difference `δ = Wη - Vη ∈ N₋(A)` lies in `D(A_V)`, so `δ = 0`
  have hδdom : ((W η : deficiencySubspaceMinus A) : H)
      - ((V η : deficiencySubspaceMinus A) : H) ∈ vonNeumannDomain A V := by
    have hsub := Submodule.sub_mem _ hdV hdW
    have hrw : ((η : H) - ((V η : deficiencySubspaceMinus A) : H))
        - ((η : H) - ((W η : deficiencySubspaceMinus A) : H))
        = ((W η : deficiencySubspaceMinus A) : H)
          - ((V η : deficiencySubspaceMinus A) : H) := by
      abel
    rwa [hrw] at hsub
  have hδmem : ((W η : deficiencySubspaceMinus A) : H)
      - ((V η : deficiencySubspaceMinus A) : H) ∈ deficiencySubspaceMinus A :=
    Submodule.sub_mem _ (W η).2 (V η).2
  have hδ0 := eq_zero_of_mem_deficiencySubspaceMinus_of_mem_vonNeumannDomain
    A hsym hdense V hδmem hδdom
  exact (sub_eq_zero.mp hδ0).symm

/-! ### The classification -/

/-- **Existence and uniqueness**: for a closed, symmetric, densely-defined operator, every
self-adjoint extension arises from exactly one deficiency unitary. -/
theorem existsUnique_vonNeumannExtension_eq {A B : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A) (hdense : Dense (A.domain : Set H))
    (hclosed : IsClosed (A.graph : Set (H × H)))
    (hB : IsSelfAdjoint B) (hAB : A ≤ B) :
    ∃! V : (deficiencySubspacePlus A) ≃ₗᵢ[ℂ] (deficiencySubspaceMinus A),
      B = vonNeumannExtension A hsym hdense V :=
  ⟨inducedDeficiencyEquiv hdense hB hAB,
    eq_vonNeumannExtension_inducedDeficiencyEquiv hsym hdense hclosed hB hAB,
    fun _ hW => vonNeumannExtension_injective A hsym hdense
      (hW.symm.trans
        (eq_vonNeumannExtension_inducedDeficiencyEquiv hsym hdense hclosed hB hAB))⟩

/-- **Von Neumann's classification of self-adjoint extensions.** For a closed, symmetric,
densely-defined operator, the self-adjoint extensions correspond bijectively to the unitary
identifications of the deficiency subspaces: `V ↦ A_V` with inverse `B ↦` (restriction of
`B`'s Cayley transform). -/
noncomputable def selfAdjointExtensionEquiv (A : H →ₗ.[ℂ] H)
    (hsym : A.IsFormalAdjoint A) (hdense : Dense (A.domain : Set H))
    (hclosed : IsClosed (A.graph : Set (H × H))) :
    {B : H →ₗ.[ℂ] H // IsSelfAdjoint B ∧ A ≤ B} ≃
      ((deficiencySubspacePlus A) ≃ₗᵢ[ℂ] (deficiencySubspaceMinus A)) where
  toFun B := inducedDeficiencyEquiv hdense B.2.1 B.2.2
  invFun V := ⟨vonNeumannExtension A hsym hdense V,
    vonNeumannExtension_isSelfAdjoint A hsym hdense hclosed V,
    le_vonNeumannExtension A hsym hdense V⟩
  left_inv B := Subtype.ext
    (eq_vonNeumannExtension_inducedDeficiencyEquiv hsym hdense hclosed B.2.1 B.2.2).symm
  right_inv V := (vonNeumannExtension_injective A hsym hdense
    (eq_vonNeumannExtension_inducedDeficiencyEquiv hsym hdense hclosed
      (vonNeumannExtension_isSelfAdjoint A hsym hdense hclosed V)
      (le_vonNeumannExtension A hsym hdense V))).symm

end Spectra.Operator
