/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.VonNeumannExtension

/-!
# Self-adjointness of the von Neumann extension `A_V`

This file proves that the von Neumann extension `A_V` of a symmetric, densely-defined
`A : H →ₗ.[ℂ] H` along a unitary deficiency identification `V : N₊(A) ≃ₗᵢ[ℂ] N₋(A)`
(`Spectra.Operator.vonNeumannExtension`) is:

* **symmetric**, unconditionally (`vonNeumannExtension_isFormalAdjoint`);
* **self-adjoint** when `A` is closed (`vonNeumannExtension_isSelfAdjoint`);
* **essentially self-adjoint** with no closedness hypothesis at all
  (`vonNeumannExtension_isEssentiallySelfAdjoint`).

## Proof shapes

*Symmetry* is the classical boundary-form computation: decomposing `u = x + η - Vη` and
`w = y + ξ - Vξ` and expanding `⟪A_V u, w⟫ - ⟪u, A_V w⟫` through the action formula, the
`D(A)`-`D(A)` term dies by symmetry of `A`, all `D(A)`-defect cross terms cancel via the
adjoint eigenvalue equations `A*χ = ±iχ` on `N±(A)`, and the surviving defect-defect remainder
is `-2i(⟪η,ξ⟫ - ⟪Vη,Vξ⟫)`, killed by the isometry of `V`.

*Self-adjointness* does **not** compute `(A_V)*` directly. The key algebra
`A_V u + iu = (Aψ + iψ) + 2iη` and `A_V u - iu = (Aψ - iψ) + 2iVη` shows `ran(A_V ± i)`
contains `ran(A ± i) + N±(A)`; for closed `A` the ranges `ran(A ± i)` are closed
(`Spectra.YosidaHille.op_range_isClosed`) and `N±(A)` are exactly their orthogonal
complements (`deficiencySubspacePlus_eq_orthogonal` / `..Minus..`), so `A_V ± i` is fully
surjective and von Neumann's criterion `isSelfAdjoint_of_surjective_addSub_smul` (at height
`μ = 1`) concludes. Without closedness the same containment still forces `ran(A_V ± i)` to be
*dense* (anything orthogonal to it lies in `N±(A)` — which is itself inside the range), which
feeds `isEssentiallySelfAdjoint_of_denseRange_addSub` instead.

## Main statements

* `vonNeumannExtension_isFormalAdjoint` — `A_V` is symmetric.
* `vonNeumannExtension_surjective_plus` / `..minus` — `ran(A_V ± i) = H` for closed `A`.
* `vonNeumannExtension_isSelfAdjoint` — **von Neumann's extension theorem, existence half**:
  for closed symmetric `A`, every unitary `V : N₊(A) ≃ₗᵢ[ℂ] N₋(A)` yields a self-adjoint
  extension.
* `vonNeumannExtension_denseRange_plus` / `..minus` — `ran(A_V ± i)` dense, no closedness.
* `vonNeumannExtension_isEssentiallySelfAdjoint` — without closedness, `A_V` is essentially
  self-adjoint.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975], Theorem X.2.
* [Akhiezer, Glazman, *Theory of Linear Operators in Hilbert Space*][akhiezer1993].
-/

open Complex
open scoped InnerProductSpace

namespace Spectra.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Cross-term inner product identities against the deficiency subspaces -/

/-- For `χ ∈ N₊(A)` and `ψ ∈ D(A)`: `⟪χ, Aψ⟫ = -i⟪χ, ψ⟫`, from `A*χ = iχ` and
conjugate-linearity of the inner product in its first slot. -/
theorem deficiencySubspacePlus_inner_apply (A : H →ₗ.[ℂ] H)
    (hdense : Dense (A.domain : Set H)) (χ : deficiencySubspacePlus A) (ψ : A.domain) :
    ⟪(χ : H), A ψ⟫_ℂ = -I * ⟪(χ : H), (ψ : H)⟫_ℂ := by
  have hdom : (χ : H) ∈ A.adjoint.domain :=
    mem_adjoint_domain_of_mem_deficiencySubspacePlus A χ.2
  have hfa := LinearPMap.adjoint_isFormalAdjoint hdense ⟨(χ : H), hdom⟩ ψ
  rw [← hfa, adjoint_apply_of_mem_deficiencySubspacePlus A χ.2 hdom, inner_smul_left]
  simp

/-- For `χ ∈ N₊(A)` and `ψ ∈ D(A)`: `⟪Aψ, χ⟫ = i⟪ψ, χ⟫` (conjugate of
`deficiencySubspacePlus_inner_apply`). -/
theorem inner_apply_deficiencySubspacePlus (A : H →ₗ.[ℂ] H)
    (hdense : Dense (A.domain : Set H)) (χ : deficiencySubspacePlus A) (ψ : A.domain) :
    ⟪A ψ, (χ : H)⟫_ℂ = I * ⟪(ψ : H), (χ : H)⟫_ℂ := by
  have h2 := congrArg (starRingEnd ℂ) (deficiencySubspacePlus_inner_apply A hdense χ ψ)
  rw [inner_conj_symm, map_mul, inner_conj_symm] at h2
  rw [h2]; simp

/-- For `χ ∈ N₋(A)` and `ψ ∈ D(A)`: `⟪χ, Aψ⟫ = i⟪χ, ψ⟫`, from `A*χ = -iχ`. -/
theorem deficiencySubspaceMinus_inner_apply (A : H →ₗ.[ℂ] H)
    (hdense : Dense (A.domain : Set H)) (χ : deficiencySubspaceMinus A) (ψ : A.domain) :
    ⟪(χ : H), A ψ⟫_ℂ = I * ⟪(χ : H), (ψ : H)⟫_ℂ := by
  have hdom : (χ : H) ∈ A.adjoint.domain :=
    mem_adjoint_domain_of_mem_deficiencySubspaceMinus A χ.2
  have hfa := LinearPMap.adjoint_isFormalAdjoint hdense ⟨(χ : H), hdom⟩ ψ
  rw [← hfa, adjoint_apply_of_mem_deficiencySubspaceMinus A χ.2 hdom, inner_smul_left]
  simp

/-- For `χ ∈ N₋(A)` and `ψ ∈ D(A)`: `⟪Aψ, χ⟫ = -i⟪ψ, χ⟫` (conjugate of
`deficiencySubspaceMinus_inner_apply`). -/
theorem inner_apply_deficiencySubspaceMinus (A : H →ₗ.[ℂ] H)
    (hdense : Dense (A.domain : Set H)) (χ : deficiencySubspaceMinus A) (ψ : A.domain) :
    ⟪A ψ, (χ : H)⟫_ℂ = -I * ⟪(ψ : H), (χ : H)⟫_ℂ := by
  have h2 := congrArg (starRingEnd ℂ) (deficiencySubspaceMinus_inner_apply A hdense χ ψ)
  rw [inner_conj_symm, map_mul, inner_conj_symm] at h2
  rw [h2]; simp

/-- The deficiency isometry `V` preserves ambient inner products:
`⟪Vη, Vξ⟫_H = ⟪η, ξ⟫_H`. -/
theorem inner_coe_map_map (A : H →ₗ.[ℂ] H)
    (V : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A)
    (η ξ : deficiencySubspacePlus A) :
    ⟪((V η : deficiencySubspaceMinus A) : H), ((V ξ : deficiencySubspaceMinus A) : H)⟫_ℂ
      = ⟪(η : H), (ξ : H)⟫_ℂ := by
  have h := V.inner_map_map η ξ
  rwa [Submodule.coe_inner, Submodule.coe_inner] at h

/-! ### Symmetry of the extension -/

/-- **The von Neumann extension is symmetric**: `⟪A_V u, w⟫ = ⟪u, A_V w⟫` for all
`u, w ∈ D(A_V)`. Decomposing `u = x + η - Vη` and `w = y + ξ - Vξ`, the dom-dom term is
symmetry of `A`, the dom-defect cross terms cancel via `A*χ = ±iχ` on `N±(A)`, and the
defect-defect remainder dies against the isometry of `V`. -/
theorem vonNeumannExtension_isFormalAdjoint (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H))
    (V : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    (vonNeumannExtension A hsym hdense V).IsFormalAdjoint
      (vonNeumannExtension A hsym hdense V) := by
  intro u w
  have hu' : (u : H) ∈ vonNeumannDomain A V := u.2
  have hw' : (w : H) ∈ vonNeumannDomain A V := w.2
  obtain ⟨x, η, hu⟩ := vonNeumannDomain_cases A hu'
  obtain ⟨y, ξ, hw⟩ := vonNeumannDomain_cases A hw'
  rw [vonNeumannExtension_apply_add_defect A hsym hdense V x η u hu,
    vonNeumannExtension_apply_add_defect A hsym hdense V y ξ w hw, hu, hw]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, Complex.conj_I]
  rw [hsym x y, inner_apply_deficiencySubspacePlus A hdense ξ x,
    inner_apply_deficiencySubspaceMinus A hdense (V ξ) x,
    deficiencySubspacePlus_inner_apply A hdense η y,
    deficiencySubspaceMinus_inner_apply A hdense (V η) y,
    inner_coe_map_map A V η ξ]
  ring

/-! ### The key algebra: hitting a deficiency vector with `A_V ± i`

For `u = ψ + η - Vη` the action formula gives `A_V u = Aψ + iη + iVη`, so the `Vη` terms
cancel in `A_V u + iu` and the `η` terms cancel in `A_V u - iu`:

  `A_V u + iu = (Aψ + iψ) + 2iη`,   `A_V u - iu = (Aψ - iψ) + 2iVη`.

Choosing `η` (resp. `Vη`) to be `-(i/2)·n` turns the tail into exactly `n`. -/

/-- For any `ψ ∈ D(A)` and `n ∈ N₊(A)` there is `u ∈ D(A_V)` with
`A_V u + iu = (Aψ + iψ) + n`. -/
theorem vonNeumannExtension_exists_plus_eq (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H))
    (V : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A)
    (ψ : A.domain) {n : H} (hn : n ∈ deficiencySubspacePlus A) :
    ∃ u : (vonNeumannExtension A hsym hdense V).domain,
      vonNeumannExtension A hsym hdense V u + I • (u : H) = A ψ + I • (ψ : H) + n := by
  set η : deficiencySubspacePlus A := (-(I / 2)) • (⟨n, hn⟩ : deficiencySubspacePlus A) with hη
  obtain ⟨u, hu⟩ : ∃ u : (vonNeumannExtension A hsym hdense V).domain,
      (u : H) = (ψ : H) + (η : H) - ((V η : deficiencySubspaceMinus A) : H) :=
    ⟨⟨_, mem_vonNeumannDomain A V ψ η⟩, rfl⟩
  have hcoeη : (η : H) = -(I / 2) • n := by
    rw [hη]; exact Submodule.coe_smul _ _
  have hcollapse : I • (η : H) + I • (η : H) = n := by
    rw [hcoeη, smul_smul, ← add_smul]
    have h2 : I * -(I / 2) + I * -(I / 2) = 1 := by
      have h3 : I * -(I / 2) + I * -(I / 2) = -(I * I) := by ring
      rw [h3, Complex.I_mul_I, neg_neg]
    rw [h2, one_smul]
  refine ⟨u, ?_⟩
  rw [vonNeumannExtension_apply_add_defect A hsym hdense V ψ η u hu, hu, ← hcollapse,
    smul_sub, smul_add]
  abel

/-- For any `ψ ∈ D(A)` and `n ∈ N₋(A)` there is `u ∈ D(A_V)` with
`A_V u - iu = (Aψ - iψ) + n`. -/
theorem vonNeumannExtension_exists_minus_eq (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H))
    (V : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A)
    (ψ : A.domain) {n : H} (hn : n ∈ deficiencySubspaceMinus A) :
    ∃ u : (vonNeumannExtension A hsym hdense V).domain,
      vonNeumannExtension A hsym hdense V u - I • (u : H) = A ψ - I • (ψ : H) + n := by
  set ζ : deficiencySubspaceMinus A := (-(I / 2)) • (⟨n, hn⟩ : deficiencySubspaceMinus A) with hζ
  set η : deficiencySubspacePlus A := V.symm ζ with hη
  have hVη : V η = ζ := by rw [hη]; exact V.apply_symm_apply ζ
  obtain ⟨u, hu⟩ : ∃ u : (vonNeumannExtension A hsym hdense V).domain,
      (u : H) = (ψ : H) + (η : H) - ((V η : deficiencySubspaceMinus A) : H) :=
    ⟨⟨_, mem_vonNeumannDomain A V ψ η⟩, rfl⟩
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
  rw [vonNeumannExtension_apply_add_defect A hsym hdense V ψ η u hu, hu, ← hcollapse,
    smul_sub, smul_add]
  abel

/-! ### Surjectivity of `A_V ± i` for closed `A` -/

/-- Surjectivity of `A_V + i` for closed `A`: decompose `φ` over
`H = ran(A + i) ⊕ ran(A + i)ᗮ` and recall `ran(A + i)ᗮ = N₊(A)`. -/
theorem vonNeumannExtension_surjective_plus (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hclosed : IsClosed (A.graph : Set (H × H)))
    (V : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    ∀ φ : H, ∃ u : (vonNeumannExtension A hsym hdense V).domain,
      vonNeumannExtension A hsym hdense V u + I • (u : H) = φ := by
  intro φ
  -- `ran(A + i)` is closed, hence complete, hence admits an orthogonal projection
  have hMclosed : IsClosed ((Spectra.Resolvent.rangeSubmodule (A := A) (-I)) : Set H) :=
    Spectra.YosidaHille.op_range_isClosed hsym hclosed (-I) (by simp)
  haveI : CompleteSpace (Spectra.Resolvent.rangeSubmodule (A := A) (-I)) :=
    hMclosed.isComplete.completeSpace_coe
  -- decompose `φ = m + n` with `m ∈ ran(A + i)` and `n ⊥ ran(A + i)`
  obtain ⟨m, hm, n, hn, hφ⟩ := Submodule.exists_add_mem_mem_orthogonal
    (K := Spectra.Resolvent.rangeSubmodule (A := A) (-I)) φ
  obtain ⟨ψ, hψ⟩ := hm
  have hψ' : A ψ - (-I) • (ψ : H) = m := hψ
  -- the orthogonal part is a deficiency vector, so the key algebra reaches `m + n`
  obtain ⟨u, hu⟩ := vonNeumannExtension_exists_plus_eq A hsym hdense V ψ
    (orthogonal_le_deficiencySubspacePlus A hdense hn)
  refine ⟨u, ?_⟩
  rw [hu, hφ, ← hψ', neg_smul, sub_neg_eq_add]

/-- Surjectivity of `A_V - i` for closed `A`: mirror over
`H = ran(A - i) ⊕ N₋(A)`, with `V.symm` supplying the defect vector. -/
theorem vonNeumannExtension_surjective_minus (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hclosed : IsClosed (A.graph : Set (H × H)))
    (V : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    ∀ φ : H, ∃ u : (vonNeumannExtension A hsym hdense V).domain,
      vonNeumannExtension A hsym hdense V u - I • (u : H) = φ := by
  intro φ
  have hMclosed : IsClosed ((Spectra.Resolvent.rangeSubmodule (A := A) I) : Set H) :=
    Spectra.YosidaHille.op_range_isClosed hsym hclosed I (by simp)
  haveI : CompleteSpace (Spectra.Resolvent.rangeSubmodule (A := A) I) :=
    hMclosed.isComplete.completeSpace_coe
  obtain ⟨m, hm, n, hn, hφ⟩ := Submodule.exists_add_mem_mem_orthogonal
    (K := Spectra.Resolvent.rangeSubmodule (A := A) I) φ
  obtain ⟨ψ, hψ⟩ := hm
  have hψ' : A ψ - I • (ψ : H) = m := hψ
  obtain ⟨u, hu⟩ := vonNeumannExtension_exists_minus_eq A hsym hdense V ψ
    (orthogonal_le_deficiencySubspaceMinus A hdense hn)
  refine ⟨u, ?_⟩
  rw [hu, hφ, ← hψ']

/-! ### Self-adjointness (closed case) -/

/-- **Von Neumann's extension theorem, existence half.** The von Neumann extension `A_V` of a
closed, symmetric, densely-defined `A` along any unitary `V : N₊(A) ≃ₗᵢ[ℂ] N₋(A)` is
self-adjoint: `A_V` is symmetric and `A_V ± i` are surjective, so von Neumann's criterion
(`isSelfAdjoint_of_surjective_addSub_smul` at `μ = 1`) applies. -/
theorem vonNeumannExtension_isSelfAdjoint (A : H →ₗ.[ℂ] H)
    (hsym : A.IsFormalAdjoint A) (hdense : Dense (A.domain : Set H))
    (hclosed : IsClosed (A.graph : Set (H × H)))
    (V : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    IsSelfAdjoint (vonNeumannExtension A hsym hdense V) :=
  isSelfAdjoint_of_surjective_addSub_smul (vonNeumannExtension A hsym hdense V)
    (vonNeumannExtension_isFormalAdjoint A hsym hdense V)
    (vonNeumannExtension_dense_domain A hsym hdense V) 1
    (by simpa using vonNeumannExtension_surjective_plus A hsym hdense hclosed V)
    (by simpa using vonNeumannExtension_surjective_minus A hsym hdense hclosed V)

/-! ### Dense ranges without closedness -/

/-- Without closedness of `A`, the range of `A_V + i` is still dense: any `χ` orthogonal to it
is orthogonal to `ran(A + i)`, hence lies in `N₊(A)` — but `N₊(A)` itself sits inside the
range, so `⟪χ, χ⟫ = 0`. -/
theorem vonNeumannExtension_denseRange_plus (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H))
    (V : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    Dense (Set.range fun u : (vonNeumannExtension A hsym hdense V).domain =>
      vonNeumannExtension A hsym hdense V u + I • (u : H)) := by
  -- the orthogonal complement of the `A_V - (-i)` range submodule is trivial
  have hbot : (Spectra.Resolvent.rangeSubmodule
      (A := vonNeumannExtension A hsym hdense V) (-I))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro χ hχ
    -- χ is orthogonal to `ran(A + i)` (the `D(A)` part of the `A_V` range) …
    have hχM : χ ∈ (Spectra.Resolvent.rangeSubmodule (A := A) (-I))ᗮ := by
      rw [Submodule.mem_orthogonal]
      rintro y ⟨ψ, rfl⟩
      have hmem : (ψ : H) ∈ (vonNeumannExtension A hsym hdense V).domain :=
        domain_le_vonNeumannDomain A V ψ.2
      have heq : vonNeumannExtension A hsym hdense V ⟨(ψ : H), hmem⟩ = A ψ :=
        ((le_vonNeumannExtension A hsym hdense V).2 (x := ψ)
          (y := ⟨(ψ : H), hmem⟩) rfl).symm
      have hy : A ψ - (-I) • (ψ : H) ∈ Spectra.Resolvent.rangeSubmodule
          (A := vonNeumannExtension A hsym hdense V) (-I) := by
        refine ⟨⟨(ψ : H), hmem⟩, ?_⟩
        change vonNeumannExtension A hsym hdense V ⟨(ψ : H), hmem⟩ - (-I) • (ψ : H)
            = A ψ - (-I) • (ψ : H)
        rw [heq]
      exact Submodule.inner_right_of_mem_orthogonal hy hχ
    -- … hence χ ∈ N₊(A); but N₊(A) sits inside the `A_V` range (take ψ = 0), so χ ⊥ χ.
    obtain ⟨u, hu⟩ := vonNeumannExtension_exists_plus_eq A hsym hdense V 0
      (orthogonal_le_deficiencySubspacePlus A hdense hχM)
    have hχR : χ ∈ Spectra.Resolvent.rangeSubmodule
        (A := vonNeumannExtension A hsym hdense V) (-I) := by
      refine ⟨u, ?_⟩
      change vonNeumannExtension A hsym hdense V u - (-I) • (u : H) = χ
      rw [neg_smul, sub_neg_eq_add, hu]
      simp [LinearPMap.map_zero]
    exact inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hχR hχ)
  -- trivial complement ⟹ dense submodule
  have htop : (Spectra.Resolvent.rangeSubmodule
      (A := vonNeumannExtension A hsym hdense V) (-I)).topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hbot]
    exact Submodule.bot_orthogonal_eq_top
  have hdR : Dense ((Spectra.Resolvent.rangeSubmodule
      (A := vonNeumannExtension A hsym hdense V) (-I)) : Set H) := by
    rw [dense_iff_closure_eq]
    have hcoe : closure ((Spectra.Resolvent.rangeSubmodule
        (A := vonNeumannExtension A hsym hdense V) (-I)) : Set H)
        = ((Spectra.Resolvent.rangeSubmodule
            (A := vonNeumannExtension A hsym hdense V) (-I)).topologicalClosure : Set H) :=
      (Submodule.topologicalClosure_coe _).symm
    rw [hcoe, htop]
    rfl
  -- the coe of the range submodule IS the `A_V - (-i)` range; convert `- (-i)` to `+ i`
  have hdR' : Dense (Set.range fun u : (vonNeumannExtension A hsym hdense V).domain =>
      vonNeumannExtension A hsym hdense V u - (-I) • (u : H)) := hdR
  simpa [neg_smul, sub_neg_eq_add] using hdR'

/-- Without closedness of `A`, the range of `A_V - i` is dense (mirror of
`vonNeumannExtension_denseRange_plus` via `V.symm`). -/
theorem vonNeumannExtension_denseRange_minus (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H))
    (V : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    Dense (Set.range fun u : (vonNeumannExtension A hsym hdense V).domain =>
      vonNeumannExtension A hsym hdense V u - I • (u : H)) := by
  have hbot : (Spectra.Resolvent.rangeSubmodule
      (A := vonNeumannExtension A hsym hdense V) I)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro χ hχ
    have hχM : χ ∈ (Spectra.Resolvent.rangeSubmodule (A := A) I)ᗮ := by
      rw [Submodule.mem_orthogonal]
      rintro y ⟨ψ, rfl⟩
      have hmem : (ψ : H) ∈ (vonNeumannExtension A hsym hdense V).domain :=
        domain_le_vonNeumannDomain A V ψ.2
      have heq : vonNeumannExtension A hsym hdense V ⟨(ψ : H), hmem⟩ = A ψ :=
        ((le_vonNeumannExtension A hsym hdense V).2 (x := ψ)
          (y := ⟨(ψ : H), hmem⟩) rfl).symm
      have hy : A ψ - I • (ψ : H) ∈ Spectra.Resolvent.rangeSubmodule
          (A := vonNeumannExtension A hsym hdense V) I := by
        refine ⟨⟨(ψ : H), hmem⟩, ?_⟩
        change vonNeumannExtension A hsym hdense V ⟨(ψ : H), hmem⟩ - I • (ψ : H)
            = A ψ - I • (ψ : H)
        rw [heq]
      exact Submodule.inner_right_of_mem_orthogonal hy hχ
    obtain ⟨u, hu⟩ := vonNeumannExtension_exists_minus_eq A hsym hdense V 0
      (orthogonal_le_deficiencySubspaceMinus A hdense hχM)
    have hχR : χ ∈ Spectra.Resolvent.rangeSubmodule
        (A := vonNeumannExtension A hsym hdense V) I := by
      refine ⟨u, ?_⟩
      change vonNeumannExtension A hsym hdense V u - I • (u : H) = χ
      rw [hu]
      simp [LinearPMap.map_zero]
    exact inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hχR hχ)
  have htop : (Spectra.Resolvent.rangeSubmodule
      (A := vonNeumannExtension A hsym hdense V) I).topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hbot]
    exact Submodule.bot_orthogonal_eq_top
  have hdR : Dense ((Spectra.Resolvent.rangeSubmodule
      (A := vonNeumannExtension A hsym hdense V) I) : Set H) := by
    rw [dense_iff_closure_eq]
    have hcoe : closure ((Spectra.Resolvent.rangeSubmodule
        (A := vonNeumannExtension A hsym hdense V) I) : Set H)
        = ((Spectra.Resolvent.rangeSubmodule
            (A := vonNeumannExtension A hsym hdense V) I).topologicalClosure : Set H) :=
      (Submodule.topologicalClosure_coe _).symm
    rw [hcoe, htop]
    rfl
  exact hdR

/-! ### Essential self-adjointness (no closedness) -/

/-- **Without closedness, the von Neumann extension is essentially self-adjoint**: its ranges
`ran(A_V ± i)` are dense, so the dense-range von Neumann criterion applies. (For closed `A`,
`vonNeumannExtension_isSelfAdjoint` gives full self-adjointness instead.) -/
theorem vonNeumannExtension_isEssentiallySelfAdjoint (A : H →ₗ.[ℂ] H)
    (hsym : A.IsFormalAdjoint A) (hdense : Dense (A.domain : Set H))
    (V : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    IsEssentiallySelfAdjoint (vonNeumannExtension A hsym hdense V) :=
  isEssentiallySelfAdjoint_of_denseRange_addSub
    (vonNeumannExtension_isFormalAdjoint A hsym hdense V)
    (vonNeumannExtension_dense_domain A hsym hdense V)
    (vonNeumannExtension_denseRange_plus A hsym hdense V)
    (vonNeumannExtension_denseRange_minus A hsym hdense V)

end Spectra.Operator
