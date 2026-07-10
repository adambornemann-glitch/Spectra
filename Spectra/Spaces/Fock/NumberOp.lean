/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Fock.Sector
import Spectra.Operator.SelfAdjoint

/-!
# The number operator on the full Fock space

The **number operator** `N` on `fullFock 𝕜 H`: the unbounded diagonal multiplier
`(ξₙ)ₙ ↦ (n • ξₙ)ₙ` weighting each `n`-particle sector by its particle number. Fock Spaces
milestone M3 step 3.

`N` is realized as a Mathlib `LinearPMap` on its maximal domain `numberDomain` (those `ξ` with
`(n • ξₙ)ₙ` still square-summable). The domain contains every sector
(`fockSector_mem_numberDomain`), hence the finite-particle core, so it is dense
(`dense_numberDomain`). Sector vectors are eigenvectors of eigenvalue `n`:
`N (fockSector n x) = n • fockSector n x` (`numberOp_fockSector`), and the vacuum is a
`0`-eigenvector (`numberOp_fockVacuum`).

The headline is genuine **self-adjointness** (`numberOp_isSelfAdjoint`), in the house
formulation of `Spectra/Operator/SelfAdjoint.lean`: Mathlib's `IsSelfAdjoint` for the
`LinearPMap` star structure, i.e. `N† = N` including the domain equality. Symmetry
(`N ⊆ N†`) is the termwise computation `numberOp_isFormalAdjoint_self`; the reverse inclusion
tests a putative adjoint vector against every sector: `⟪N†η, fockSector n x⟫ = ⟪η, n • …⟫`
forces `(N†η)ₙ = n • ηₙ` for all `n` (`adjoint_numberOp_apply`), so `η` already lies in
`numberDomain` and `N†η = Nη`. Positivity of the quadratic form (`N ≥ 0`) is
`re_inner_self_numberOp_nonneg`. For `𝕜 = ℂ` the operator is bundled into the house
`SelfAdjointOperator` structure as `numberOperator`, so the symmetric-operator toolkit
(uncertainty relations, generator layer) applies directly.

## Deferred (documented, not attempted here)

* **Spectrum `= ℕ`** — needs the `LinearPMap` spectrum machinery wired to diagonal
  multipliers; the eigen-relations `numberOp_fockSector` are the `⊇` seed.
* **`N = dΓ(1)`** — consistency with second quantization is milestone M6.
* **Restriction to `boseFock` / `fermiFock`** — the symmetric/antisymmetric sectors are
  `N`-invariant; the restricted operators belong with the symmetrizer layer.
-/

noncomputable section

open scoped ENNReal

namespace Spectra

section NumberOp

variable (𝕜 H : Type*) [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-! ## The domain -/

/-- The **domain of the number operator**: those `ξ` in the full Fock space whose
number-weighted family `(n • ξₙ)ₙ` is still square-summable. This is the maximal domain of
the diagonal multiplier `ξ ↦ (n • ξₙ)ₙ`. -/
def numberDomain : Submodule 𝕜 (fullFock 𝕜 H) where
  carrier := {ξ | Memℓp (fun n : ℕ => (n : 𝕜) • ξ n) 2}
  zero_mem' := by
    change Memℓp (fun n : ℕ => (n : 𝕜) • (0 : fullFock 𝕜 H) n) 2
    have h : (fun n : ℕ => (n : 𝕜) • (0 : fullFock 𝕜 H) n)
        = (0 : ∀ n, HilbertTensorPower 𝕜 n H) :=
      funext fun n => smul_zero _
    rw [h]; exact zero_memℓp
  add_mem' {ξ η} hξ hη := by
    change Memℓp (fun n : ℕ => (n : 𝕜) • (ξ + η : fullFock 𝕜 H) n) 2
    have h : (fun n : ℕ => (n : 𝕜) • (ξ + η : fullFock 𝕜 H) n)
        = (fun n : ℕ => (n : 𝕜) • ξ n) + fun n : ℕ => (n : 𝕜) • η n :=
      funext fun n => smul_add _ _ _
    rw [h]; exact Memℓp.add hξ hη
  smul_mem' c ξ hξ := by
    change Memℓp (fun n : ℕ => (n : 𝕜) • (c • ξ : fullFock 𝕜 H) n) 2
    have h : (fun n : ℕ => (n : 𝕜) • (c • ξ : fullFock 𝕜 H) n)
        = c • fun n : ℕ => (n : 𝕜) • ξ n :=
      funext fun n => by
        change (n : 𝕜) • (c • ξ n) = c • ((n : 𝕜) • ξ n)
        exact smul_comm _ _ _
    rw [h]; exact Memℓp.const_smul hξ c

/-- Membership in `numberDomain`, `Memℓp` shape: the number-weighted family is in `ℓ²`. -/
theorem mem_numberDomain_iff {ξ : fullFock 𝕜 H} :
    ξ ∈ numberDomain 𝕜 H ↔ Memℓp (fun n : ℕ => (n : 𝕜) • ξ n) 2 :=
  Iff.rfl

/-- Membership in `numberDomain`, summability shape: `∑ n² ‖ξₙ‖² < ∞`. -/
theorem mem_numberDomain_iff_summable {ξ : fullFock 𝕜 H} :
    ξ ∈ numberDomain 𝕜 H ↔ Summable fun n : ℕ => (n : ℝ) ^ 2 * ‖ξ n‖ ^ 2 := by
  have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  rw [mem_numberDomain_iff, memℓp_gen_iff h2]
  refine summable_congr fun n => ?_
  rw [ENNReal.toReal_ofNat, Real.rpow_two, norm_smul, RCLike.norm_natCast, mul_pow]

/-- The number-weighted family of a sector vector is the sector embedding of the weighted
vector: `(m • (fockSector n x)ₘ)ₘ = fockSector n (n • x)` as bare families. -/
theorem natCast_smul_fockSector_apply (n : ℕ) (x : HilbertTensorPower 𝕜 n H) :
    (fun m : ℕ => (m : 𝕜) • fockSector 𝕜 H n x m) = ⇑(fockSector 𝕜 H n ((n : 𝕜) • x)) := by
  funext m
  by_cases h : m = n
  · subst h
    rw [fockSector_apply_same, fockSector_apply_same]
  · rw [fockSector_apply_ne 𝕜 H h, fockSector_apply_ne 𝕜 H h, smul_zero]

/-- Sector vectors lie in the domain of the number operator: their weighted family is
supported in the single sector `n`. -/
theorem fockSector_mem_numberDomain (n : ℕ) (x : HilbertTensorPower 𝕜 n H) :
    fockSector 𝕜 H n x ∈ numberDomain 𝕜 H := by
  rw [mem_numberDomain_iff, natCast_smul_fockSector_apply]
  exact lp.memℓp _

/-- The vacuum lies in the domain of the number operator. -/
theorem fockVacuum_mem_numberDomain : fockVacuum 𝕜 H ∈ numberDomain 𝕜 H :=
  fockSector_mem_numberDomain 𝕜 H 0 (vacuumPower 𝕜 H)

/-- The finite-particle core is contained in the domain of the number operator. -/
theorem finParticle_le_numberDomain : finParticle 𝕜 H ≤ numberDomain 𝕜 H := by
  refine iSup_le fun n => ?_
  rintro ξ ⟨x, rfl⟩
  exact fockSector_mem_numberDomain 𝕜 H n x

/-- ★ **The number operator is densely defined**: its domain contains the dense
finite-particle core. -/
theorem dense_numberDomain : Dense (numberDomain 𝕜 H : Set (fullFock 𝕜 H)) :=
  (dense_finParticle 𝕜 H).mono (finParticle_le_numberDomain 𝕜 H)

/-! ## The operator -/

/-- The **number operator** on the full Fock space: the unbounded diagonal multiplier
`(ξₙ)ₙ ↦ (n • ξₙ)ₙ` on its maximal domain `numberDomain`, as a `LinearPMap`. -/
def numberOp : fullFock 𝕜 H →ₗ.[𝕜] fullFock 𝕜 H where
  domain := numberDomain 𝕜 H
  toFun :=
    { toFun := fun ξ => (⟨fun n : ℕ => (n : 𝕜) • (ξ : fullFock 𝕜 H) n,
        (mem_numberDomain_iff 𝕜 H).mp ξ.2⟩ : fullFock 𝕜 H)
      map_add' := fun ξ η => by
        refine lp.ext (funext fun n => ?_)
        change (n : 𝕜) • ((ξ : fullFock 𝕜 H) n + (η : fullFock 𝕜 H) n)
            = (n : 𝕜) • (ξ : fullFock 𝕜 H) n + (n : 𝕜) • (η : fullFock 𝕜 H) n
        exact smul_add _ _ _
      map_smul' := fun c ξ => by
        refine lp.ext (funext fun n => ?_)
        change (n : 𝕜) • (c • (ξ : fullFock 𝕜 H) n) = c • ((n : 𝕜) • (ξ : fullFock 𝕜 H) n)
        exact smul_comm _ _ _ }

@[simp]
theorem numberOp_domain : (numberOp 𝕜 H).domain = numberDomain 𝕜 H :=
  rfl

/-- Density of the domain, restated in the exact `LinearPMap` form consumed by Mathlib's
adjoint machinery (this keeps the unifier from re-deriving the identification at each
adjoint call site). -/
theorem dense_numberOp_domain : Dense ((numberOp 𝕜 H).domain : Set (fullFock 𝕜 H)) :=
  dense_numberDomain 𝕜 H

@[simp]
theorem numberOp_apply_coe (ξ : (numberOp 𝕜 H).domain) (n : ℕ) :
    numberOp 𝕜 H ξ n = (n : 𝕜) • (ξ : fullFock 𝕜 H) n :=
  rfl

/-! ## Eigen-relations -/

/-- **Sectors are eigenspaces of the number operator**: `N (fockSector n x) = n • fockSector
n x`. The `n`-particle sector has particle number `n`. -/
theorem numberOp_fockSector (n : ℕ) (x : HilbertTensorPower 𝕜 n H) :
    numberOp 𝕜 H ⟨fockSector 𝕜 H n x, fockSector_mem_numberDomain 𝕜 H n x⟩
      = (n : 𝕜) • fockSector 𝕜 H n x := by
  refine lp.ext ?_
  change (fun m : ℕ => (m : 𝕜) • fockSector 𝕜 H n x m) = ⇑((n : 𝕜) • fockSector 𝕜 H n x)
  rw [natCast_smul_fockSector_apply, map_smul]

/-- **The vacuum is the ground state of the number operator**: `N Ω = 0` — the vacuum has
particle number `0`. -/
theorem numberOp_fockVacuum :
    numberOp 𝕜 H ⟨fockVacuum 𝕜 H, fockVacuum_mem_numberDomain 𝕜 H⟩ = 0 := by
  have h := numberOp_fockSector 𝕜 H 0 (vacuumPower 𝕜 H)
  rw [Nat.cast_zero, zero_smul] at h
  exact h

/-! ## Symmetry, self-adjointness, positivity -/

/-- **The number operator is symmetric**: `⟪Nξ, η⟫ = ⟪ξ, Nη⟫` on the domain, in the house
currency `LinearPMap.IsFormalAdjoint` (the `symmetric` field of
`Spectra/Operator/Symmetric.lean`). Termwise: `(n : 𝕜)` is conjugation-fixed. -/
theorem numberOp_isFormalAdjoint_self :
    (numberOp 𝕜 H).IsFormalAdjoint (numberOp 𝕜 H) := by
  intro ξ η
  rw [lp.inner_eq_tsum (𝕜 := 𝕜), lp.inner_eq_tsum (𝕜 := 𝕜)]
  refine tsum_congr fun n => ?_
  rw [numberOp_apply_coe, numberOp_apply_coe, inner_smul_left, inner_smul_right, map_natCast]

/-- **Any adjoint vector is diagonal-weighted**: for `η ∈ D(N†)`, testing against the sector
vectors forces `(N†η)ₙ = n • ηₙ` for every `n`. This is the mathematical core of
self-adjointness: the adjoint can act in no other way than `N` itself. -/
theorem adjoint_numberOp_apply (η : (numberOp 𝕜 H).adjoint.domain) (n : ℕ) :
    (numberOp 𝕜 H).adjoint η n = (n : 𝕜) • (η : fullFock 𝕜 H) n := by
  refine ext_inner_right 𝕜 fun x => ?_
  have hfa : inner 𝕜 ((numberOp 𝕜 H).adjoint η : fullFock 𝕜 H)
        (lp.single 2 n x : fullFock 𝕜 H)
      = inner 𝕜 (η : fullFock 𝕜 H)
        (numberOp 𝕜 H ⟨fockSector 𝕜 H n x, fockSector_mem_numberDomain 𝕜 H n x⟩) :=
    LinearPMap.adjoint_isFormalAdjoint (dense_numberOp_domain 𝕜 H) η
      ⟨fockSector 𝕜 H n x, fockSector_mem_numberDomain 𝕜 H n x⟩
  rw [numberOp_fockSector, fockSector_eq_single, inner_smul_right] at hfa
  simp only [lp.inner_single_right] at hfa
  rw [inner_smul_left, map_natCast]
  exact hfa

/-- Every vector in the adjoint domain already lies in `numberDomain`: its weighted family
equals the adjoint image, which is square-summable. -/
theorem mem_numberDomain_of_mem_adjoint_domain {η : fullFock 𝕜 H}
    (hη : η ∈ (numberOp 𝕜 H).adjoint.domain) : η ∈ numberDomain 𝕜 H := by
  rw [mem_numberDomain_iff]
  have hfun : (fun n : ℕ => (n : 𝕜) • η n)
      = ⇑((numberOp 𝕜 H).adjoint ⟨η, hη⟩ : fullFock 𝕜 H) := by
    funext n
    exact (adjoint_numberOp_apply 𝕜 H ⟨η, hη⟩ n).symm
  rw [hfun]
  exact lp.memℓp _

/-- ★★ **The number operator is self-adjoint** — in the house formulation of
`Spectra/Operator/SelfAdjoint.lean`: Mathlib's `IsSelfAdjoint` for the `LinearPMap` star
structure, i.e. `N† = N` including the domain equality. Symmetry gives `N ≤ N†`; conversely
any `η ∈ D(N†)` satisfies `(N†η)ₙ = n • ηₙ` (`adjoint_numberOp_apply`), so `η ∈ D(N)` and
`N†η = Nη`. -/
theorem numberOp_isSelfAdjoint : IsSelfAdjoint (numberOp 𝕜 H) := by
  rw [LinearPMap.isSelfAdjoint_def]
  refine le_antisymm ?_
    ((numberOp_isFormalAdjoint_self 𝕜 H).le_adjoint (dense_numberOp_domain 𝕜 H))
  apply LinearPMap.le_of_eqLocus_ge
  intro η hη
  have hmem : η ∈ numberDomain 𝕜 H := mem_numberDomain_of_mem_adjoint_domain 𝕜 H hη
  refine ⟨hη, hmem, ?_⟩
  refine lp.ext (funext fun n => ?_)
  rw [adjoint_numberOp_apply, numberOp_apply_coe]

/-- **Positivity of the number operator**: `0 ≤ re ⟪ξ, Nξ⟫` on the domain — the expected
particle number is nonnegative. (Same quadratic-form currency as
`re_inner_self_pmapOfPVM_nonneg`.) -/
theorem re_inner_self_numberOp_nonneg (ξ : (numberOp 𝕜 H).domain) :
    0 ≤ RCLike.re (inner 𝕜 (ξ : fullFock 𝕜 H) (numberOp 𝕜 H ξ)) := by
  have hre : RCLike.re (∑' n, inner 𝕜 ((ξ : fullFock 𝕜 H) n) (numberOp 𝕜 H ξ n))
      = ∑' n, RCLike.re (inner 𝕜 ((ξ : fullFock 𝕜 H) n) (numberOp 𝕜 H ξ n)) :=
    RCLike.reCLM.map_tsum (lp.summable_inner _ _)
  rw [lp.inner_eq_tsum (𝕜 := 𝕜), hre]
  refine tsum_nonneg fun n => ?_
  rw [numberOp_apply_coe, inner_smul_right, inner_self_eq_norm_sq_to_K]
  have h : ((n : 𝕜) * (‖(ξ : fullFock 𝕜 H) n‖ : 𝕜) ^ 2)
      = (((n : ℝ) * ‖(ξ : fullFock 𝕜 H) n‖ ^ 2 : ℝ) : 𝕜) := by
    push_cast
    ring
  rw [h, RCLike.ofReal_re]
  positivity

end NumberOp

/-! ## The house bundle (`𝕜 = ℂ`) -/

section Bundle

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The number operator bundled into the house `SelfAdjointOperator` structure of
`Spectra/Operator/SelfAdjoint.lean` (complex scalars), so the symmetric-operator toolkit —
uncertainty relations, the observable/generator layer — applies to it directly. -/
def numberOperator : Operator.SelfAdjointOperator (fullFock ℂ H) where
  toLinearPMap := numberOp ℂ H
  selfAdjoint := numberOp_isSelfAdjoint ℂ H

@[simp]
theorem numberOperator_toLinearPMap : (numberOperator H).toLinearPMap = numberOp ℂ H :=
  rfl

end Bundle

end Spectra
