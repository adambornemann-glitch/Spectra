/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Eigenbasis of a compact self-adjoint operator

The **spectral theorem** for a compact self-adjoint operator `T` on a complex Hilbert space `H`
says that `H` admits an orthonormal basis of eigenvectors of `T`. This file assembles that
eigenbasis as a bundled `HilbertBasis`, together with the real eigenvalue attached to each basis
vector and the eigen-equation `T (eᵢ) = λᵢ • eᵢ`.

The construction is completely general: it takes an arbitrary bounded operator `T : H →L[ℂ] H`
together with hypotheses `IsSelfAdjoint T` and `IsCompactOperator T`, so it depends on nothing
beyond Mathlib. Positivity / trace-one facts (eigenvalues nonnegative, summing to one) are layered
on top of this file elsewhere.

## Main definitions

* `Spectra.InformationGeometry.Quantum.eigenIndex T` — the index type of the eigenbasis, a sigma
  type `Σ μ : ℂ, β μ` where `β μ` indexes a chosen Hilbert basis of the `μ`-eigenspace.
* `eigenbasis hsa hc` — the orthonormal eigenbasis of `H`, a `HilbertBasis (eigenIndex T) ℂ H`.
* `eigenvalue hsa hc` — the (real) eigenvalue attached to each basis vector.

## Main results

* `apply_eigenbasis hsa hc i` — the eigen-equation `T (eᵢ) = (λᵢ : ℂ) • eᵢ`.
* `inner_eigenbasis_self hsa hc i` — the Rayleigh form `⟪eᵢ, T eᵢ⟫ = λᵢ`.
-/

open scoped InnerProductSpace

namespace Spectra.InformationGeometry.Quantum

open Module.End Submodule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hsa : IsSelfAdjoint T) (hc : IsCompactOperator T)

/-- The `μ`-eigenspace of a bounded operator is a closed subspace, hence a complete space. -/
private theorem completeSpace_eigenspace (μ : ℂ) :
    CompleteSpace ↥(eigenspace (T : Module.End ℂ H) μ) := by
  have hker : eigenspace (T : Module.End ℂ H) μ
      = LinearMap.ker (T - μ • (1 : H →L[ℂ] H)).toLinearMap := by
    rw [eigenspace_def]
    congr 1
  have hclosed : IsClosed (eigenspace (T : Module.End ℂ H) μ : Set H) := by
    rw [hker]
    exact (T - μ • (1 : H →L[ℂ] H)).isClosed_ker
  haveI : IsClosed (eigenspace (T : Module.End ℂ H) μ : Set H) := hclosed
  exact hclosed.completeSpace_coe

/-- For each eigenvalue `μ`, a chosen Hilbert basis of the `μ`-eigenspace, indexed by a set. -/
private noncomputable def eigenspaceBasisIndex (μ : ℂ) : Set ↥(eigenspace (T : Module.End ℂ H) μ) :=
  haveI := completeSpace_eigenspace T μ
  (exists_hilbertBasis ℂ ↥(eigenspace (T : Module.End ℂ H) μ)).choose

private noncomputable def eigenspaceBasis (μ : ℂ) :
    HilbertBasis (eigenspaceBasisIndex T μ) ℂ ↥(eigenspace (T : Module.End ℂ H) μ) :=
  haveI := completeSpace_eigenspace T μ
  (exists_hilbertBasis ℂ ↥(eigenspace (T : Module.End ℂ H) μ)).choose_spec.choose

/-- The index type of the eigenbasis: a sigma type over eigenvalues `μ : ℂ` of a per-eigenspace
Hilbert basis. -/
def eigenIndex : Type _ := Σ μ : ℂ, eigenspaceBasisIndex T μ

/-- The candidate eigenbasis vectors: for `⟨μ, a⟩`, the image in `H` of the `a`-th basis vector of
the `μ`-eigenspace. -/
private noncomputable def eigenVec : eigenIndex T → H :=
  fun p => ((eigenspace (T : Module.End ℂ H) p.1).subtypeₗᵢ) (eigenspaceBasis T p.1 p.2)

/-- The candidate eigenbasis vectors are orthonormal. -/
private theorem orthonormal_eigenVec (hsa : IsSelfAdjoint T) :
    Orthonormal ℂ (eigenVec T) := by
  have hsymm : T.IsSymmetric := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa
  exact hsymm.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal
    (fun μ => (eigenspaceBasis T μ).orthonormal)

/-- Each eigenspace lies inside the topological closure of the span of the candidate vectors. -/
private theorem eigenspace_le_topologicalClosure (μ : ℂ) :
    eigenspace (T : Module.End ℂ H) μ
      ≤ (span ℂ (Set.range (eigenVec T))).topologicalClosure := by
  intro x hx
  set Eμ := eigenspace (T : Module.End ℂ H) μ with _hEμ
  -- `⟨x, hx⟩` lies in the closure of the span of the μ-eigenspace basis.
  have hmem : (⟨x, hx⟩ : ↥Eμ) ∈ (span ℂ (Set.range (eigenspaceBasis T μ))).topologicalClosure := by
    rw [(eigenspaceBasis T μ).dense_span]; trivial
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hmem
  -- Push forward along the continuous inclusion `subtypeL`.
  have himg : Eμ.subtypeL ⟨x, hx⟩
      ∈ closure (Eμ.subtypeL '' (span ℂ (Set.range (eigenspaceBasis T μ)) : Set ↥Eμ)) :=
    image_closure_subset_closure_image (Eμ.subtypeL.continuous)
      (Set.mem_image_of_mem _ hmem)
  -- The image of the span sits inside the span of the candidate vectors.
  have hsub : Eμ.subtypeL '' (span ℂ (Set.range (eigenspaceBasis T μ)) : Set ↥Eμ)
      ⊆ (span ℂ (Set.range (eigenVec T)) : Set H) := by
    rintro y ⟨z, hz, rfl⟩
    have : Eμ.subtypeL z ∈ (span ℂ (Set.range (eigenVec T))) := by
      have hmap : Submodule.map (Eμ.subtypeL : ↥Eμ →ₗ[ℂ] H)
          (span ℂ (Set.range (eigenspaceBasis T μ)))
          ≤ span ℂ (Set.range (eigenVec T)) := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro w ⟨b, hb, rfl⟩
        obtain ⟨a, rfl⟩ := hb
        exact ⟨⟨μ, a⟩, rfl⟩
      exact hmap ⟨z, hz, rfl⟩
    exact this
  have hfin : Eμ.subtypeL ⟨x, hx⟩ ∈ closure (span ℂ (Set.range (eigenVec T)) : Set H) :=
    closure_mono hsub himg
  rw [Submodule.subtypeL_apply] at hfin
  rwa [← SetLike.mem_coe, Submodule.topologicalClosure_coe]

/-- The span of the candidate vectors has trivial orthogonal complement. -/
private theorem orthogonal_span_eigenVec_eq_bot (hsa : IsSelfAdjoint T) (hc : IsCompactOperator T) :
    (span ℂ (Set.range (eigenVec T)))ᗮ = ⊥ := by
  have hsymm : T.IsSymmetric := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa
  have hbot : (⨆ μ, eigenspace (T : Module.End ℂ H) μ)ᗮ = ⊥ :=
    ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hsymm
  -- The span's closure is everything.
  have hclosure : (span ℂ (Set.range (eigenVec T))).topologicalClosure = ⊤ := by
    -- `⨆ μ eigenspace ≤ closure (span v)`.
    have hle : (⨆ μ, eigenspace (T : Module.End ℂ H) μ)
        ≤ (span ℂ (Set.range (eigenVec T))).topologicalClosure := by
      refine iSup_le fun μ => ?_
      exact eigenspace_le_topologicalClosure T μ
    -- Take closures; the RHS is already closed.
    have hle2 : (⨆ μ, eigenspace (T : Module.End ℂ H) μ).topologicalClosure
        ≤ (span ℂ (Set.range (eigenVec T))).topologicalClosure := by
      exact Submodule.topologicalClosure_minimal _ hle
        (span ℂ (Set.range (eigenVec T))).isClosed_topologicalClosure
    -- The LHS closure is `⊤` by the spectral theorem.
    have htop : (⨆ μ, eigenspace (T : Module.End ℂ H) μ).topologicalClosure = ⊤ := by
      rw [← Submodule.orthogonal_orthogonal_eq_closure, hbot, Submodule.bot_orthogonal_eq_top]
    rw [htop] at hle2
    exact top_le_iff.mp hle2
  -- `Kᗮ = (closure K)ᗮ = ⊤ᗮ = ⊥`.
  rw [← Submodule.orthogonal_closure, hclosure, Submodule.top_orthogonal_eq_bot]

/-- **The eigenbasis** of a compact self-adjoint operator `T`: an orthonormal Hilbert basis of `H`
consisting of eigenvectors of `T`. -/
noncomputable def eigenbasis (hsa : IsSelfAdjoint T) (hc : IsCompactOperator T) :
    HilbertBasis (eigenIndex T) ℂ H :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_eigenVec T hsa)
    (orthogonal_span_eigenVec_eq_bot T hsa hc)

@[simp]
theorem coe_eigenbasis (hsa : IsSelfAdjoint T) (hc : IsCompactOperator T) :
    ⇑(eigenbasis T hsa hc) = eigenVec T :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- Each eigenbasis vector lies in the eigenspace of its index. -/
private theorem eigenbasis_mem_eigenspace (hsa : IsSelfAdjoint T) (hc : IsCompactOperator T)
    (i : eigenIndex T) :
    eigenbasis T hsa hc i ∈ eigenspace (T : Module.End ℂ H) i.1 := by
  rw [coe_eigenbasis]
  exact (eigenspaceBasis T i.1 i.2).2

/-- The eigenvalue index `μ` of each eigenbasis vector is a genuine (nonzero-eigenvector)
eigenvalue, hence real: `(↑μ.re : ℂ) = μ`. -/
private theorem eigenIndex_fst_re (hsa : IsSelfAdjoint T) (hc : IsCompactOperator T)
    (i : eigenIndex T) : ((i.1.re : ℂ)) = i.1 := by
  have hsymm : T.IsSymmetric := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa
  -- The eigenbasis vector is a unit vector, hence nonzero.
  have hne : eigenbasis T hsa hc i ≠ 0 := by
    have := (eigenbasis T hsa hc).orthonormal.left i
    intro h
    rw [h, norm_zero] at this
    norm_num at this
  have hev : HasEigenvector (T : Module.End ℂ H) i.1 (eigenbasis T hsa hc i) :=
    ⟨eigenbasis_mem_eigenspace T hsa hc i, hne⟩
  have hconj : (starRingEnd ℂ) i.1 = i.1 :=
    hsymm.conj_eigenvalue_eq_self (hasEigenvalue_of_hasEigenvector hev)
  exact (Complex.conj_eq_iff_re.mp hconj)

/-- The (real) eigenvalue attached to each eigenbasis vector.

The self-adjointness (`hsa`) and compactness (`hc`) hypotheses are retained in the signature to
keep the call shape uniform with `eigenbasis`/`apply_eigenbasis`; the value itself is just the real
part of the eigenvalue index. -/
noncomputable def eigenvalue (_hsa : IsSelfAdjoint T) (_hc : IsCompactOperator T) :
    eigenIndex T → ℝ := fun i => i.1.re

/-- **The eigen-equation.** Applying `T` to an eigenbasis vector scales it by the (real)
eigenvalue. -/
theorem apply_eigenbasis (hsa : IsSelfAdjoint T) (hc : IsCompactOperator T) (i : eigenIndex T) :
    T (eigenbasis T hsa hc i) = (eigenvalue T hsa hc i : ℂ) • eigenbasis T hsa hc i := by
  have hmem := eigenbasis_mem_eigenspace T hsa hc i
  rw [mem_eigenspace_iff] at hmem
  have hmem' : T (eigenbasis T hsa hc i) = i.1 • eigenbasis T hsa hc i := hmem
  rw [hmem', eigenvalue, eigenIndex_fst_re T hsa hc i]

/-- **Rayleigh form of the eigenvalue.** The inner product of an eigenbasis vector with its image
under `T` is exactly the eigenvalue. -/
theorem inner_eigenbasis_self (hsa : IsSelfAdjoint T) (hc : IsCompactOperator T)
    (i : eigenIndex T) :
    ⟪eigenbasis T hsa hc i, T (eigenbasis T hsa hc i)⟫_ℂ = (eigenvalue T hsa hc i : ℂ) := by
  rw [apply_eigenbasis, inner_smul_right]
  have hnorm : ⟪eigenbasis T hsa hc i, eigenbasis T hsa hc i⟫_ℂ = 1 := by
    have := (eigenbasis T hsa hc).orthonormal.1 i
    rw [inner_self_eq_norm_sq_to_K, this]
    norm_num
  rw [hnorm, mul_one]

end Spectra.InformationGeometry.Quantum
