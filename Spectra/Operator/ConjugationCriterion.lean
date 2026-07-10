/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.SelfAdjointExtension
import Spectra.SpectralTheory.Antilinear.Conjugation
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Von Neumann's conjugation criterion

A symmetric, densely-defined operator that commutes with a **conjugation** (an antiunitary
involution `C : H → H`, `Spectra.QuantumMechanics.SpectralTheory.Conjugation`) admits
self-adjoint extensions (`exists_le_isSelfAdjoint_of_conjugation`). This is von Neumann's
classical criterion (Reed–Simon, Theorem X.3); it applies in particular to every Schrödinger
operator `-Δ + V` with a *real* potential, with `C` the pointwise complex conjugation on `L²`.

## The route

* A conjugation swaps the deficiency subspaces: `C(N₊(A)) ⊆ N₋(A)` and back
  (`conj_mem_deficiencySubspaceMinus` / `..Plus`). No adjoint computation is needed — `Cχ` is
  checked to be orthogonal to `ran(A ∓ i)` by a four-line inner-product computation using the
  cross-term identities of `Spectra.Operator.VonNeumannExtensionSelfAdjoint`, and the existing
  identifications `N∓ = ran(A ∓ i)ᗮ` finish.
* The restriction of `C` is an antiunitary equivalence `N₊(A) ≃ₗᵢ⋆[ℂ] N₋(A)`
  (`conjDeficiencyEquiv`).
* **An antiunitary equivalence of Hilbert spaces upgrades to a linear one**
  (`nonempty_linearIsometryEquiv_of_antiunitary`): push a Hilbert basis of `K` through `W` —
  the image family is orthonormal (the inner identity conjugates, and `conj` fixes `0` and
  `1`) and total (a vector orthogonal to the image pulls back to a vector with vanishing
  `ℓ²`-coordinates), hence a Hilbert basis of `L`; composing the two `ℓ²`-representations
  gives `K ≃ₗᵢ[ℂ] L`. This is the seed of the Hilbert-dimension story: it is exactly
  "antiunitarily equivalent spaces have equal orthonormal-basis cardinality" in disguise.
* Von Neumann's extension theorem (`exists_le_isSelfAdjoint_of_nonempty_deficiencyEquiv`)
  concludes.

## Main statements

* `nonempty_linearIsometryEquiv_of_antiunitary` — antiunitarily equivalent Hilbert spaces are
  unitarily equivalent.
* `deficiencySubspacePlus_isClosed` / `..Minus..` — the deficiency subspaces are closed.
* `conj_mem_deficiencySubspaceMinus` / `..Plus` — a commuting conjugation swaps `N₊ ↔ N₋`.
* `conjDeficiencyEquiv` — the restricted antiunitary `N₊(A) ≃ₗᵢ⋆[ℂ] N₋(A)`.
* `exists_le_isSelfAdjoint_of_conjugation` — **von Neumann's conjugation criterion**.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975], Theorem X.3.
* [Akhiezer, Glazman, *Theory of Linear Operators in Hilbert Space*][akhiezer1993].
-/

open Complex
open scoped InnerProductSpace
open Spectra.QuantumMechanics.SpectralTheory

namespace Spectra.Operator

/-! ### Antiunitarily equivalent Hilbert spaces are unitarily equivalent -/

/-- **An antiunitary equivalence of complex Hilbert spaces upgrades to a linear isometric
equivalence.** Push a Hilbert basis of `K` through `W`: the image family is orthonormal and
total in `L`, hence a Hilbert basis, and composing the `ℓ²`-representations of the two bases
produces a `ℂ`-linear unitary. (The inner identity `⟪Wx, Wy⟫ = ⟪y, x⟫` is taken as a
hypothesis, as Mathlib's `inner_map_map` is linear-only.) -/
theorem nonempty_linearIsometryEquiv_of_antiunitary {K L : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    (W : K ≃ₗᵢ⋆[ℂ] L) (hinner : ∀ x y : K, ⟪W x, W y⟫_ℂ = ⟪y, x⟫_ℂ) :
    Nonempty (K ≃ₗᵢ[ℂ] L) := by
  classical
  obtain ⟨s, b, -⟩ := exists_hilbertBasis ℂ K
  -- the image family is orthonormal
  have honf : Orthonormal ℂ (fun i : s => W (b i)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [show ⟪W (b i), W (b j)⟫_ℂ = ⟪b j, b i⟫_ℂ from hinner _ _,
      orthonormal_iff_ite.mp b.orthonormal j i]
    by_cases h : i = j
    · simp [h]
    · rw [if_neg (fun hh => h hh.symm), if_neg h]
  -- the image family is total: an orthogonal vector has vanishing `ℓ²`-coordinates
  have htot : (Submodule.span ℂ (Set.range fun i : s => W (b i)))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    rw [Submodule.mem_orthogonal] at hy
    have hyi : ∀ i : s, ⟪(b i : K), W.symm y⟫_ℂ = 0 := by
      intro i
      have h1 : ⟪W (b i), y⟫_ℂ = 0 :=
        hy _ (Submodule.subset_span (Set.mem_range_self i))
      have h2 : ⟪W (b i), W (W.symm y)⟫_ℂ = ⟪W.symm y, b i⟫_ℂ := hinner _ _
      rw [W.apply_symm_apply] at h2
      have h3 : ⟪W.symm y, (b i : K)⟫_ℂ = 0 := by rw [← h2]; exact h1
      have h4 := congrArg (starRingEnd ℂ) h3
      rwa [inner_conj_symm, map_zero] at h4
    have hrepr : b.repr (W.symm y) = 0 := by
      refine lp.ext (funext fun i => ?_)
      rw [b.repr_apply_apply]
      change ⟪b i, W.symm y⟫_ℂ = (0 : ℂ)
      exact hyi i
    have hsy : W.symm y = 0 := by
      have h := congrArg b.repr.symm hrepr
      rwa [b.repr.symm_apply_apply, map_zero] at h
    have h := congrArg W hsy
    rwa [W.apply_symm_apply, map_zero] at h
  -- assemble the linear unitary through the two `ℓ²`-representations
  exact ⟨b.repr.trans (HilbertBasis.mkOfOrthogonalEqBot honf htot).repr.symm⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The deficiency subspaces are closed -/

/-- `N₊(A)` is closed: it is an orthogonal complement. -/
theorem deficiencySubspacePlus_isClosed (A : H →ₗ.[ℂ] H)
    (hdense : Dense (A.domain : Set H)) :
    IsClosed ((deficiencySubspacePlus A : Submodule ℂ H) : Set H) := by
  rw [deficiencySubspacePlus_eq_orthogonal A hdense]
  exact Submodule.isClosed_orthogonal _

/-- `N₋(A)` is closed: it is an orthogonal complement. -/
theorem deficiencySubspaceMinus_isClosed (A : H →ₗ.[ℂ] H)
    (hdense : Dense (A.domain : Set H)) :
    IsClosed ((deficiencySubspaceMinus A : Submodule ℂ H) : Set H) := by
  rw [deficiencySubspaceMinus_eq_orthogonal A hdense]
  exact Submodule.isClosed_orthogonal _

/-! ### A commuting conjugation swaps the deficiency subspaces -/

variable (A : H →ₗ.[ℂ] H) (C : Conjugation H)

omit [CompleteSpace H] in
/-- The conjugation inner identity, in `FunLike` form. -/
theorem conjugation_inner (u v : H) : ⟪C u, C v⟫_ℂ = ⟪v, u⟫_ℂ :=
  C.inner_map u v

/-- **A commuting conjugation maps `N₊(A)` into `N₋(A)`**: `Cχ` is orthogonal to `ran(A - i)`
by a direct inner-product computation (antilinearity swaps the sign of `i`), and
`ran(A - i)ᗮ = N₋(A)`. -/
theorem conj_mem_deficiencySubspaceMinus (hdense : Dense (A.domain : Set H))
    (hdom : ∀ x ∈ A.domain, C x ∈ A.domain)
    (hcomm : ∀ x : A.domain, A ⟨C (x : H), hdom _ x.2⟩ = C (A x))
    {χ : H} (hχ : χ ∈ deficiencySubspacePlus A) :
    C χ ∈ deficiencySubspaceMinus A := by
  apply orthogonal_le_deficiencySubspaceMinus A hdense
  rw [Submodule.mem_orthogonal]
  rintro y ⟨ψ, rfl⟩
  -- `Aψ = C(A(Cψ))` via commutation + involution
  set ψ' : A.domain := ⟨C (ψ : H), hdom _ ψ.2⟩ with _hψ'
  have hAψ : A ψ = C (A ψ') := by
    rw [← hcomm ψ']
    congr 1
    exact Subtype.ext (C.involutive (ψ : H)).symm
  -- first summand: `⟪Aψ, Cχ⟫ = ⟪χ, Aψ'⟫ = -i⟪χ, Cψ⟫`
  have h1 : ⟪A ψ, C χ⟫_ℂ = -I * ⟪χ, C (ψ : H)⟫_ℂ := by
    rw [hAψ, conjugation_inner C (A ψ') χ]
    exact deficiencySubspacePlus_inner_apply A hdense ⟨χ, hχ⟩ ψ'
  -- second summand: `⟪ψ, Cχ⟫ = ⟪χ, Cψ⟫`
  have h2 : ⟪(ψ : H), C χ⟫_ℂ = ⟪χ, C (ψ : H)⟫_ℂ := by
    conv_lhs => rw [← C.apply_apply (ψ : H)]
    exact conjugation_inner C (C (ψ : H)) χ
  rw [inner_sub_left, inner_smul_left, h1, h2, Complex.conj_I]
  ring

/-- **A commuting conjugation maps `N₋(A)` into `N₊(A)`** (mirror). -/
theorem conj_mem_deficiencySubspacePlus (hdense : Dense (A.domain : Set H))
    (hdom : ∀ x ∈ A.domain, C x ∈ A.domain)
    (hcomm : ∀ x : A.domain, A ⟨C (x : H), hdom _ x.2⟩ = C (A x))
    {χ : H} (hχ : χ ∈ deficiencySubspaceMinus A) :
    C χ ∈ deficiencySubspacePlus A := by
  apply orthogonal_le_deficiencySubspacePlus A hdense
  rw [Submodule.mem_orthogonal]
  rintro y ⟨ψ, rfl⟩
  set ψ' : A.domain := ⟨C (ψ : H), hdom _ ψ.2⟩ with _hψ'
  have hAψ : A ψ = C (A ψ') := by
    rw [← hcomm ψ']
    congr 1
    exact Subtype.ext (C.involutive (ψ : H)).symm
  have h1 : ⟪A ψ, C χ⟫_ℂ = I * ⟪χ, C (ψ : H)⟫_ℂ := by
    rw [hAψ, conjugation_inner C (A ψ') χ]
    exact deficiencySubspaceMinus_inner_apply A hdense ⟨χ, hχ⟩ ψ'
  have h2 : ⟪(ψ : H), C χ⟫_ℂ = ⟪χ, C (ψ : H)⟫_ℂ := by
    conv_lhs => rw [← C.apply_apply (ψ : H)]
    exact conjugation_inner C (C (ψ : H)) χ
  rw [inner_sub_left, inner_smul_left, h1, h2]
  simp only [map_neg, Complex.conj_I, neg_neg]
  ring

/-! ### The restricted antiunitary `N₊(A) ≃ₗᵢ⋆[ℂ] N₋(A)` -/

/-- The restriction of a commuting conjugation to the deficiency subspaces, as an antiunitary
equivalence `N₊(A) ≃ₗᵢ⋆[ℂ] N₋(A)` (inverse: the same conjugation, by involutivity). -/
noncomputable def conjDeficiencyEquiv (hdense : Dense (A.domain : Set H))
    (hdom : ∀ x ∈ A.domain, C x ∈ A.domain)
    (hcomm : ∀ x : A.domain, A ⟨C (x : H), hdom _ x.2⟩ = C (A x)) :
    (deficiencySubspacePlus A) ≃ₗᵢ⋆[ℂ] (deficiencySubspaceMinus A) where
  toLinearEquiv :=
    { toFun := fun η => ⟨C (η : H),
        conj_mem_deficiencySubspaceMinus A C hdense hdom hcomm η.2⟩
      map_add' := fun η η' => Subtype.ext (C.map_add (η : H) (η' : H))
      map_smul' := fun c η => Subtype.ext (C.map_smul c (η : H))
      invFun := fun ξ => ⟨C (ξ : H),
        conj_mem_deficiencySubspacePlus A C hdense hdom hcomm ξ.2⟩
      left_inv := fun η => Subtype.ext (C.involutive (η : H))
      right_inv := fun ξ => Subtype.ext (C.involutive (ξ : H)) }
  norm_map' := fun η => by
    rw [Submodule.coe_norm, Submodule.coe_norm]
    exact C.norm_map (η : H)

/-- The restricted conjugation acts as `C`. -/
@[simp]
theorem conjDeficiencyEquiv_apply_coe (hdense : Dense (A.domain : Set H))
    (hdom : ∀ x ∈ A.domain, C x ∈ A.domain)
    (hcomm : ∀ x : A.domain, A ⟨C (x : H), hdom _ x.2⟩ = C (A x))
    (η : deficiencySubspacePlus A) :
    ((conjDeficiencyEquiv A C hdense hdom hcomm η : deficiencySubspaceMinus A) : H)
      = C (η : H) :=
  rfl

/-- The restricted conjugation inherits the antiunitary inner identity. -/
theorem inner_conjDeficiencyEquiv (hdense : Dense (A.domain : Set H))
    (hdom : ∀ x ∈ A.domain, C x ∈ A.domain)
    (hcomm : ∀ x : A.domain, A ⟨C (x : H), hdom _ x.2⟩ = C (A x))
    (η η' : deficiencySubspacePlus A) :
    ⟪conjDeficiencyEquiv A C hdense hdom hcomm η,
      conjDeficiencyEquiv A C hdense hdom hcomm η'⟫_ℂ = ⟪η', η⟫_ℂ := by
  rw [Submodule.coe_inner, Submodule.coe_inner,
    conjDeficiencyEquiv_apply_coe, conjDeficiencyEquiv_apply_coe]
  exact conjugation_inner C (η : H) (η' : H)

/-! ### Von Neumann's conjugation criterion -/

/-- **Von Neumann's conjugation criterion** (Reed–Simon, Theorem X.3): a symmetric,
densely-defined operator commuting with a conjugation `C` admits self-adjoint extensions.
The conjugation restricts to an antiunitary equivalence `N₊(A) ≃ₗᵢ⋆ N₋(A)`, which upgrades
to a linear unitary via a Hilbert-basis transport, and von Neumann's extension theorem
applies. Covers Schrödinger operators with real potentials (with `C` the pointwise complex
conjugation on `L²`). -/
theorem exists_le_isSelfAdjoint_of_conjugation (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H))
    (hdom : ∀ x ∈ A.domain, C x ∈ A.domain)
    (hcomm : ∀ x : A.domain, A ⟨C (x : H), hdom _ x.2⟩ = C (A x)) :
    ∃ B : H →ₗ.[ℂ] H, IsSelfAdjoint B ∧ A ≤ B := by
  haveI : CompleteSpace (deficiencySubspacePlus A) :=
    (deficiencySubspacePlus_isClosed A hdense).isComplete.completeSpace_coe
  haveI : CompleteSpace (deficiencySubspaceMinus A) :=
    (deficiencySubspaceMinus_isClosed A hdense).isComplete.completeSpace_coe
  exact exists_le_isSelfAdjoint_of_nonempty_deficiencyEquiv A hsym hdense
    (nonempty_linearIsometryEquiv_of_antiunitary
      (conjDeficiencyEquiv A C hdense hdom hcomm)
      (inner_conjDeficiencyEquiv A C hdense hdom hcomm))

end Spectra.Operator
