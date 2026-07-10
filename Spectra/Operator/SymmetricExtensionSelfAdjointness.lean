/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.SymmetricExtension

/-!
# Which partial von Neumann extensions are self-adjoint?

For a closed, symmetric, densely-defined `A : H →ₗ.[ℂ] H`, the partial von Neumann extension
`A_V = A*|_{D(A) ⊔ (1-V)F}` (`Spectra.Operator.vonNeumannExtensionOn`) along an isometry
`V : F →ₗᵢ[ℂ] N₋(A)` on `F ≤ N₊(A)` is self-adjoint **iff** `V` is a full deficiency unitary:

  `IsSelfAdjoint A_V ↔ F = N₊(A) ∧ Function.Surjective V`
  (`vonNeumannExtensionOn_isSelfAdjoint_iff`).

Together with `vonNeumannExtensionOn_isFormalAdjoint` and the second von Neumann formula
(`Spectra.Operator.exists_eq_vonNeumannExtensionOn`) this completes the classification picture:
among ALL symmetric extensions — which are exactly the `A_V` — the self-adjoint ones are
exactly those with full unitary `V`.

## Proof shapes — no casts, no classification machinery

*⟸* re-runs the surjectivity engine of `Spectra.Operator.VonNeumannExtensionSelfAdjoint`
directly on `A_V`: the reach lemmas produce `A_V u ± iu = (Aψ ± iψ) + n` for defect vectors
`n`, the hypotheses `N₊(A) ≤ F` and surjectivity of `V` supply the defect vectors on both
sides, and von Neumann's criterion `isSelfAdjoint_of_surjective_addSub_smul` concludes. The
submodule equality `F = N₊(A)` is consumed only through `≤` — no transport along it ever
happens.

*⟹* is a direct orthogonality argument needing **no closedness**: self-adjointness makes
`A_V ± i` surjective, so `(2i)·n` is reached for any defect vector `n`; decomposing the
solution through the action formula collapses `A_V u ± iu` to `(A x ± ix) + (2i)·(defect)`,
and the difference of defect vectors lies in `ran(A ± i) ∩ ran(A ± i)ᗮ = 0`, forcing
`n ∈ F` (resp. `n ∈ ran V`).

## Main statements

* `vonNeumannExtensionOn_exists_plus_eq` / `..minus_eq` — the reach lemmas for partial `V`.
* `vonNeumannExtensionOn_surjective_plus` / `..minus` — surjectivity of `A_V ± i` for closed
  `A`, given `N₊(A) ≤ F` (plus) and surjectivity of `V` (minus).
* `vonNeumannExtensionOn_isSelfAdjoint` — the ⟸ direction.
* `deficiencySubspacePlus_le_of_vonNeumannExtensionOn_isSelfAdjoint` — ⟹, the `F` half.
* `surjective_of_vonNeumannExtensionOn_isSelfAdjoint` — ⟹, the `V` half.
* `vonNeumannExtensionOn_isSelfAdjoint_iff` — **the characterization**.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975], Theorem X.2.
* [Akhiezer, Glazman, *Theory of Linear Operators in Hilbert Space*][akhiezer1993], Section 80.
-/

open Complex
open scoped InnerProductSpace

namespace Spectra.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →ₗ.[ℂ] H) {F : Submodule ℂ H}

/-! ### The reach lemmas -/

/-- For `ψ ∈ D(A)` and `n ∈ F` there is `u ∈ D(A_V)` with `A_V u + iu = (Aψ + iψ) + n`. -/
theorem vonNeumannExtensionOn_exists_plus_eq (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hF : F ≤ deficiencySubspacePlus A)
    (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A) (ψ : A.domain) {n : H} (hn : n ∈ F) :
    ∃ u : (vonNeumannExtensionOn A hsym hdense hF V).domain,
      vonNeumannExtensionOn A hsym hdense hF V u + I • (u : H)
        = A ψ + I • (ψ : H) + n := by
  set η : F := (-(I / 2)) • (⟨n, hn⟩ : F) with hη
  obtain ⟨u, hu⟩ : ∃ u : (vonNeumannExtensionOn A hsym hdense hF V).domain,
      (u : H) = (ψ : H) + (η : H) - ((V η : deficiencySubspaceMinus A) : H) :=
    ⟨⟨_, mem_vonNeumannDomainOn A V ψ η⟩, rfl⟩
  have hcoeη : (η : H) = -(I / 2) • n := by
    rw [hη]; exact Submodule.coe_smul _ _
  have hcollapse : I • (η : H) + I • (η : H) = n := by
    rw [hcoeη, smul_smul, ← add_smul]
    have h2 : I * -(I / 2) + I * -(I / 2) = 1 := by
      have h3 : I * -(I / 2) + I * -(I / 2) = -(I * I) := by ring
      rw [h3, Complex.I_mul_I, neg_neg]
    rw [h2, one_smul]
  refine ⟨u, ?_⟩
  rw [vonNeumannExtensionOn_apply_add_defect A hsym hdense hF V ψ η u hu, hu, ← hcollapse,
    smul_sub, smul_add]
  abel

/-- For `ψ ∈ D(A)`, surjective `V`, and `n ∈ N₋(A)` there is `u ∈ D(A_V)` with
`A_V u - iu = (Aψ - iψ) + n`. -/
theorem vonNeumannExtensionOn_exists_minus_eq (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hF : F ≤ deficiencySubspacePlus A)
    (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A) (hVsurj : Function.Surjective V)
    (ψ : A.domain) {n : H} (hn : n ∈ deficiencySubspaceMinus A) :
    ∃ u : (vonNeumannExtensionOn A hsym hdense hF V).domain,
      vonNeumannExtensionOn A hsym hdense hF V u - I • (u : H)
        = A ψ - I • (ψ : H) + n := by
  set ζ : deficiencySubspaceMinus A := (-(I / 2)) • (⟨n, hn⟩ : deficiencySubspaceMinus A)
    with hζ
  obtain ⟨η, hVη⟩ := hVsurj ζ
  obtain ⟨u, hu⟩ : ∃ u : (vonNeumannExtensionOn A hsym hdense hF V).domain,
      (u : H) = (ψ : H) + (η : H) - ((V η : deficiencySubspaceMinus A) : H) :=
    ⟨⟨_, mem_vonNeumannDomainOn A V ψ η⟩, rfl⟩
  have hcoeVη : ((V η : deficiencySubspaceMinus A) : H) = -(I / 2) • n := by
    rw [hVη, hζ]; exact Submodule.coe_smul _ _
  have hcollapse : I • ((V η : deficiencySubspaceMinus A) : H)
      + I • ((V η : deficiencySubspaceMinus A) : H) = n := by
    rw [hcoeVη, smul_smul, ← add_smul]
    have h2 : I * -(I / 2) + I * -(I / 2) = 1 := by
      have h3 : I * -(I / 2) + I * -(I / 2) = -(I * I) := by ring
      rw [h3, Complex.I_mul_I, neg_neg]
    rw [h2, one_smul]
  refine ⟨u, ?_⟩
  rw [vonNeumannExtensionOn_apply_add_defect A hsym hdense hF V ψ η u hu, hu, ← hcollapse,
    smul_sub, smul_add]
  abel

/-! ### Surjectivity of `A_V ± i` for closed `A` -/

/-- Surjectivity of `A_V + i` for closed `A`, given `N₊(A) ≤ F`: decompose over
`H = ran(A + i) ⊕ N₊(A)` and reach the defect part inside `F`. -/
theorem vonNeumannExtensionOn_surjective_plus (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hclosed : IsClosed (A.graph : Set (H × H)))
    (hF : F ≤ deficiencySubspacePlus A) (hFtop : deficiencySubspacePlus A ≤ F)
    (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    ∀ φ : H, ∃ u : (vonNeumannExtensionOn A hsym hdense hF V).domain,
      vonNeumannExtensionOn A hsym hdense hF V u + I • (u : H) = φ := by
  intro φ
  have hMclosed : IsClosed ((Spectra.Resolvent.rangeSubmodule (A := A) (-I)) : Set H) :=
    Spectra.YosidaHille.op_range_isClosed hsym hclosed (-I) (by simp)
  haveI : CompleteSpace (Spectra.Resolvent.rangeSubmodule (A := A) (-I)) :=
    hMclosed.isComplete.completeSpace_coe
  obtain ⟨m, hm, n, hn, hφ⟩ := Submodule.exists_add_mem_mem_orthogonal
    (K := Spectra.Resolvent.rangeSubmodule (A := A) (-I)) φ
  obtain ⟨ψ, hψ⟩ := hm
  have hψ' : A ψ - (-I) • (ψ : H) = m := hψ
  obtain ⟨u, hu⟩ := vonNeumannExtensionOn_exists_plus_eq A hsym hdense hF V ψ
    (hFtop (orthogonal_le_deficiencySubspacePlus A hdense hn))
  refine ⟨u, ?_⟩
  rw [hu, hφ, ← hψ', neg_smul, sub_neg_eq_add]

/-- Surjectivity of `A_V - i` for closed `A`, given surjective `V`: mirror over
`H = ran(A - i) ⊕ N₋(A)`. -/
theorem vonNeumannExtensionOn_surjective_minus (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hclosed : IsClosed (A.graph : Set (H × H)))
    (hF : F ≤ deficiencySubspacePlus A) (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A)
    (hVsurj : Function.Surjective V) :
    ∀ φ : H, ∃ u : (vonNeumannExtensionOn A hsym hdense hF V).domain,
      vonNeumannExtensionOn A hsym hdense hF V u - I • (u : H) = φ := by
  intro φ
  have hMclosed : IsClosed ((Spectra.Resolvent.rangeSubmodule (A := A) I) : Set H) :=
    Spectra.YosidaHille.op_range_isClosed hsym hclosed I (by simp)
  haveI : CompleteSpace (Spectra.Resolvent.rangeSubmodule (A := A) I) :=
    hMclosed.isComplete.completeSpace_coe
  obtain ⟨m, hm, n, hn, hφ⟩ := Submodule.exists_add_mem_mem_orthogonal
    (K := Spectra.Resolvent.rangeSubmodule (A := A) I) φ
  obtain ⟨ψ, hψ⟩ := hm
  have hψ' : A ψ - I • (ψ : H) = m := hψ
  obtain ⟨u, hu⟩ := vonNeumannExtensionOn_exists_minus_eq A hsym hdense hF V hVsurj ψ
    (orthogonal_le_deficiencySubspaceMinus A hdense hn)
  refine ⟨u, ?_⟩
  rw [hu, hφ, ← hψ']

/-! ### The ⟸ direction -/

/-- **A full deficiency unitary gives a self-adjoint extension**: for closed `A`, if
`N₊(A) ≤ F` and `V` is surjective, then `A_V` is self-adjoint. -/
theorem vonNeumannExtensionOn_isSelfAdjoint (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hclosed : IsClosed (A.graph : Set (H × H)))
    (hF : F ≤ deficiencySubspacePlus A) (hFtop : deficiencySubspacePlus A ≤ F)
    (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A) (hVsurj : Function.Surjective V) :
    IsSelfAdjoint (vonNeumannExtensionOn A hsym hdense hF V) :=
  isSelfAdjoint_of_surjective_addSub_smul (vonNeumannExtensionOn A hsym hdense hF V)
    (vonNeumannExtensionOn_isFormalAdjoint A hsym hdense hF V)
    (vonNeumannExtensionOn_dense_domain A hsym hdense hF V) 1
    (by simpa using vonNeumannExtensionOn_surjective_plus A hsym hdense hclosed hF hFtop V)
    (by simpa using
      vonNeumannExtensionOn_surjective_minus A hsym hdense hclosed hF V hVsurj)

/-! ### The ⟹ direction (no closedness needed) -/

/-- **Self-adjointness of `A_V` forces `F = N₊(A)`** (stated as the nontrivial inclusion).
Solve `A_V u + iu = (2i)·n`; the action formula collapses the left side to
`(Ax + ix) + (2i)·η`, and `(2i)·η - (2i)·n ∈ N₊(A) ∩ ran(A + i) = 0` forces `n = η ∈ F`. -/
theorem deficiencySubspacePlus_le_of_vonNeumannExtensionOn_isSelfAdjoint
    (hsym : A.IsFormalAdjoint A) (hdense : Dense (A.domain : Set H))
    (hF : F ≤ deficiencySubspacePlus A) (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A)
    (hSA : IsSelfAdjoint (vonNeumannExtensionOn A hsym hdense hF V)) :
    deficiencySubspacePlus A ≤ F := by
  intro n hn
  obtain ⟨u, hu⟩ := (Spectra.YosidaHille.isSelfAdjoint_to_surjective hSA).1
    (((2 : ℂ) * I) • n)
  obtain ⟨x, η, hcases⟩ := vonNeumannDomainOn_cases A u.2
  have hval := vonNeumannExtensionOn_apply_add_defect A hsym hdense hF V x η u hcases
  -- collapse `A_V u + iu` to `(Ax + ix) + (2i)·η`
  have hsum : A x + I • (x : H) + ((2 : ℂ) * I) • ((η : H)) = ((2 : ℂ) * I) • n := by
    have h2 : ((2 : ℂ) * I) • ((η : H)) = I • (η : H) + I • (η : H) := by
      rw [mul_smul, two_smul]
    rw [h2]
    calc A x + I • (x : H) + (I • (η : H) + I • (η : H))
        = (A x + I • (η : H) + I • ((V η : deficiencySubspaceMinus A) : H))
          + I • ((x : H) + (η : H) - ((V η : deficiencySubspaceMinus A) : H)) := by
          rw [smul_sub, smul_add]; abel
      _ = vonNeumannExtensionOn A hsym hdense hF V u + I • (u : H) := by
          rw [← hval, ← hcases]
      _ = ((2 : ℂ) * I) • n := hu
  -- the defect difference lies in `ran(A + i) ∩ ran(A + i)ᗮ = 0`
  have hkey : (A x - (-I) • (x : H))
      + (((2 : ℂ) * I) • ((η : H)) - ((2 : ℂ) * I) • n) = 0 := by
    rw [neg_smul, sub_neg_eq_add]
    calc A x + I • (x : H) + (((2 : ℂ) * I) • ((η : H)) - ((2 : ℂ) * I) • n)
        = (A x + I • (x : H) + ((2 : ℂ) * I) • ((η : H))) - ((2 : ℂ) * I) • n := by abel
      _ = 0 := by rw [hsum, sub_self]
  have hmK : A x - (-I) • (x : H) ∈ Spectra.Resolvent.rangeSubmodule (A := A) (-I) :=
    ⟨x, rfl⟩
  have hwN : ((2 : ℂ) * I) • ((η : H)) - ((2 : ℂ) * I) • n ∈ deficiencySubspacePlus A :=
    (deficiencySubspacePlus A).sub_mem
      ((deficiencySubspacePlus A).smul_mem _ (hF η.2))
      ((deficiencySubspacePlus A).smul_mem _ hn)
  have hwOrth : ((2 : ℂ) * I) • ((η : H)) - ((2 : ℂ) * I) • n
      ∈ (Spectra.Resolvent.rangeSubmodule (A := A) (-I))ᗮ :=
    deficiencySubspacePlus_le_orthogonal A hdense hwN
  have hweq : ((2 : ℂ) * I) • ((η : H)) - ((2 : ℂ) * I) • n = -(A x - (-I) • (x : H)) :=
    eq_neg_of_add_eq_zero_right hkey
  have hwK : ((2 : ℂ) * I) • ((η : H)) - ((2 : ℂ) * I) • n
      ∈ Spectra.Resolvent.rangeSubmodule (A := A) (-I) := by
    rw [hweq]
    exact (Spectra.Resolvent.rangeSubmodule (A := A) (-I)).neg_mem hmK
  have hw0 : ((2 : ℂ) * I) • ((η : H)) - ((2 : ℂ) * I) • n = 0 :=
    inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hwK hwOrth)
  have heq : ((2 : ℂ) * I) • ((η : H)) = ((2 : ℂ) * I) • n := sub_eq_zero.mp hw0
  have hηn : ((η : F) : H) = n :=
    smul_right_injective H (mul_ne_zero two_ne_zero Complex.I_ne_zero) heq
  rw [← hηn]
  exact η.2

/-- **Self-adjointness of `A_V` forces `V` surjective**: mirror at the minus sign — solve
`A_V u - iu = (2i)·ξ` and collapse to `(Ax - ix) + (2i)·Vη`. -/
theorem surjective_of_vonNeumannExtensionOn_isSelfAdjoint
    (hsym : A.IsFormalAdjoint A) (hdense : Dense (A.domain : Set H))
    (hF : F ≤ deficiencySubspacePlus A) (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A)
    (hSA : IsSelfAdjoint (vonNeumannExtensionOn A hsym hdense hF V)) :
    Function.Surjective V := by
  intro ξ
  obtain ⟨u, hu⟩ := (Spectra.YosidaHille.isSelfAdjoint_to_surjective hSA).2
    (((2 : ℂ) * I) • ((ξ : H)))
  obtain ⟨x, η, hcases⟩ := vonNeumannDomainOn_cases A u.2
  have hval := vonNeumannExtensionOn_apply_add_defect A hsym hdense hF V x η u hcases
  -- collapse `A_V u - iu` to `(Ax - ix) + (2i)·Vη`
  have hsum : A x - I • (x : H)
      + ((2 : ℂ) * I) • ((V η : deficiencySubspaceMinus A) : H)
      = ((2 : ℂ) * I) • ((ξ : H)) := by
    have h2 : ((2 : ℂ) * I) • ((V η : deficiencySubspaceMinus A) : H)
        = I • ((V η : deficiencySubspaceMinus A) : H)
          + I • ((V η : deficiencySubspaceMinus A) : H) := by
      rw [mul_smul, two_smul]
    rw [h2]
    calc A x - I • (x : H) + (I • ((V η : deficiencySubspaceMinus A) : H)
          + I • ((V η : deficiencySubspaceMinus A) : H))
        = (A x + I • (η : H) + I • ((V η : deficiencySubspaceMinus A) : H))
          - I • ((x : H) + (η : H) - ((V η : deficiencySubspaceMinus A) : H)) := by
          rw [smul_sub, smul_add]; abel
      _ = vonNeumannExtensionOn A hsym hdense hF V u - I • (u : H) := by
          rw [← hval, ← hcases]
      _ = ((2 : ℂ) * I) • ((ξ : H)) := hu
  have hkey : (A x - I • (x : H))
      + (((2 : ℂ) * I) • ((V η : deficiencySubspaceMinus A) : H)
        - ((2 : ℂ) * I) • ((ξ : H))) = 0 := by
    calc (A x - I • (x : H)) + (((2 : ℂ) * I) • ((V η : deficiencySubspaceMinus A) : H)
          - ((2 : ℂ) * I) • ((ξ : H)))
        = (A x - I • (x : H) + ((2 : ℂ) * I) • ((V η : deficiencySubspaceMinus A) : H))
          - ((2 : ℂ) * I) • ((ξ : H)) := by abel
      _ = 0 := by rw [hsum, sub_self]
  have hmK : A x - I • (x : H) ∈ Spectra.Resolvent.rangeSubmodule (A := A) I := ⟨x, rfl⟩
  have hwN : ((2 : ℂ) * I) • ((V η : deficiencySubspaceMinus A) : H)
      - ((2 : ℂ) * I) • ((ξ : H)) ∈ deficiencySubspaceMinus A :=
    (deficiencySubspaceMinus A).sub_mem
      ((deficiencySubspaceMinus A).smul_mem _ (V η).2)
      ((deficiencySubspaceMinus A).smul_mem _ ξ.2)
  have hwOrth : ((2 : ℂ) * I) • ((V η : deficiencySubspaceMinus A) : H)
      - ((2 : ℂ) * I) • ((ξ : H)) ∈ (Spectra.Resolvent.rangeSubmodule (A := A) I)ᗮ :=
    deficiencySubspaceMinus_le_orthogonal A hdense hwN
  have hweq : ((2 : ℂ) * I) • ((V η : deficiencySubspaceMinus A) : H)
      - ((2 : ℂ) * I) • ((ξ : H)) = -(A x - I • (x : H)) :=
    eq_neg_of_add_eq_zero_right hkey
  have hwK : ((2 : ℂ) * I) • ((V η : deficiencySubspaceMinus A) : H)
      - ((2 : ℂ) * I) • ((ξ : H)) ∈ Spectra.Resolvent.rangeSubmodule (A := A) I := by
    rw [hweq]
    exact (Spectra.Resolvent.rangeSubmodule (A := A) I).neg_mem hmK
  have hw0 : ((2 : ℂ) * I) • ((V η : deficiencySubspaceMinus A) : H)
      - ((2 : ℂ) * I) • ((ξ : H)) = 0 :=
    inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hwK hwOrth)
  have heq : ((2 : ℂ) * I) • ((V η : deficiencySubspaceMinus A) : H)
      = ((2 : ℂ) * I) • ((ξ : H)) := sub_eq_zero.mp hw0
  have hVηξ : ((V η : deficiencySubspaceMinus A) : H) = (ξ : H) :=
    smul_right_injective H (mul_ne_zero two_ne_zero Complex.I_ne_zero) heq
  exact ⟨η, Subtype.ext hVηξ⟩

/-! ### The characterization -/

/-- **Self-adjointness of the partial von Neumann extension, characterized** (closed `A`):
`A_V` is self-adjoint iff `V` is a full deficiency unitary — `F = N₊(A)` and `V` surjective.
Closedness is consumed only by the ⟸ direction. -/
theorem vonNeumannExtensionOn_isSelfAdjoint_iff (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hclosed : IsClosed (A.graph : Set (H × H)))
    (hF : F ≤ deficiencySubspacePlus A) (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    IsSelfAdjoint (vonNeumannExtensionOn A hsym hdense hF V)
      ↔ F = deficiencySubspacePlus A ∧ Function.Surjective V := by
  constructor
  · intro hSA
    exact ⟨le_antisymm hF
        (deficiencySubspacePlus_le_of_vonNeumannExtensionOn_isSelfAdjoint
          A hsym hdense hF V hSA),
      surjective_of_vonNeumannExtensionOn_isSelfAdjoint A hsym hdense hF V hSA⟩
  · rintro ⟨hFeq, hVs⟩
    exact vonNeumannExtensionOn_isSelfAdjoint A hsym hdense hclosed hF hFeq.ge V hVs

end Spectra.Operator
