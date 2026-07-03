/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
File: Spectra/Spaces/Sobolev/Submodule.lean
-/
import Spectra.Spaces.Sobolev.Operations
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
open MeasureTheory

namespace Spectra.Sobolev

/-! ### Sobolev space membership predicates -/

/-- Predicate: f ∈ H¹(ℝ³).
    All first-order weak derivatives exist and are in L². -/
def MemSobolevH1 (f : L2_R3) : Prop :=
  ∀ i : Fin 3, ∃ g : L2_R3, HasWeakDerivative f i g

/-- Predicate: f ∈ H²(ℝ³).
    All weak derivatives up to order 2 exist and are in L². -/
def MemSobolevH2 (f : L2_R3) : Prop :=
  MemSobolevH1 f ∧
  ∀ i j : Fin 3, ∃ g : L2_R3, HasWeakSecondDerivative f i j g

/-- H¹(ℝ³) as a ℂ-submodule of L²(ℝ³). -/
def SobolevH1 : Submodule ℂ L2_R3 where
  carrier := { f | MemSobolevH1 f }
  zero_mem' := fun i => ⟨0, hasWeakDerivative_zero i⟩
  add_mem' := fun {f₁ f₂} hf₁ hf₂ i =>
    ⟨(hf₁ i).choose + (hf₂ i).choose,
     hasWeakDerivative_add f₁ f₂ i _ _ (hf₁ i).choose_spec (hf₂ i).choose_spec⟩
  smul_mem' := fun c {f} hf i =>
    ⟨c • (hf i).choose,
     hasWeakDerivative_smul c f i _ (hf i).choose_spec⟩


/-- H²(ℝ³) as a ℂ-submodule of L²(ℝ³). -/
def SobolevH2 : Submodule ℂ L2_R3 where
  carrier := { f | MemSobolevH2 f }
  zero_mem' := by
    refine ⟨fun i => ⟨0, hasWeakDerivative_zero i⟩, fun i j => ⟨0, ?_⟩⟩
    exact ⟨0, hasWeakDerivative_zero i, hasWeakDerivative_zero j⟩
  add_mem' := fun {f₁ f₂} ⟨h1a, h1b⟩ ⟨h2a, h2b⟩ => by
    refine ⟨fun i => ⟨(h1a i).choose + (h2a i).choose,
      hasWeakDerivative_add f₁ f₂ i _ _ (h1a i).choose_spec (h2a i).choose_spec⟩,
      fun i j => ?_⟩
    obtain ⟨g₁, mid₁, hd₁, hd₁'⟩ := h1b i j
    obtain ⟨g₂, mid₂, hd₂, hd₂'⟩ := h2b i j
    exact ⟨g₁ + g₂, mid₁ + mid₂,
      hasWeakDerivative_add f₁ f₂ i mid₁ mid₂ hd₁ hd₂,
      hasWeakDerivative_add mid₁ mid₂ j g₁ g₂ hd₁' hd₂'⟩
  smul_mem' := fun c {f} ⟨ha, hb⟩ => by
    refine ⟨fun i => ⟨c • (ha i).choose,
      hasWeakDerivative_smul c f i _ (ha i).choose_spec⟩,
      fun i j => ?_⟩
    obtain ⟨g, mid, hd, hd'⟩ := hb i j
    exact ⟨c • g, c • mid,
      hasWeakDerivative_smul c f i mid hd,
      hasWeakDerivative_smul c mid j g hd'⟩

/-- H² ⊆ H¹ as submodules. -/
lemma sobolevH2_le_H1 : SobolevH2 ≤ SobolevH1 := by
  intro f hf
  exact hf.1

/-! ### The weak gradient and Dirichlet integral -/

/-- Extract the weak gradient of an H¹ function.
    Returns the triple (∂₁f, ∂₂f, ∂₃f) as L² functions. -/
noncomputable def weakGradient (f : L2_R3) (hf : MemSobolevH1 f) : Fin 3 → L2_R3 :=
  fun i => (hf i).choose

/-- The chosen gradient component is indeed the weak derivative. -/
lemma weakGradient_spec (f : L2_R3) (hf : MemSobolevH1 f) (i : Fin 3) :
    HasWeakDerivative f i (weakGradient f hf i) :=
  (hf i).choose_spec

/-- The gradient (Dirichlet) norm squared: ∫|∇ψ|² dx = Σᵢ ‖∂ᵢψ‖²_{L²}.

    This is the quadratic form associated to -Δ. For ψ ∈ H²:
      ⟨-Δψ, ψ⟩ = ∫|∇ψ|² dx
    which is the content of `gradient_norm_sq_eq_laplacian_inner` below. -/
noncomputable def gradientNormSq (f : L2_R3) (hf : MemSobolevH1 f) : ℝ :=
  ∑ i : Fin 3, ‖weakGradient f hf i‖ ^ 2

/-- The gradient norm squared is non-negative. -/
lemma gradientNormSq_nonneg (f : L2_R3) (hf : MemSobolevH1 f) :
    0 ≤ gradientNormSq f hf := by
  simp only [gradientNormSq]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _


/-- The weak Laplacian: -Δf = -Σᵢ ∂ᵢ²f. -/
noncomputable def weakLaplacian (f : L2_R3) (hf : MemSobolevH2 f) : L2_R3 :=
  -∑ i : Fin 3, (hf.2 i i).choose

/-- The Laplacian is additive. -/
lemma weakLaplacian_add (f g : L2_R3) (hf : MemSobolevH2 f) (hg : MemSobolevH2 g) :
    weakLaplacian (f + g) (SobolevH2.add_mem hf hg) =
    weakLaplacian f hf + weakLaplacian g hg := by
  simp only [weakLaplacian]
  rw [← neg_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨midf, hdf, hdf'⟩ := (hf.2 i i).choose_spec
  obtain ⟨midg, hdg, hdg'⟩ := (hg.2 i i).choose_spec
  exact hasWeakSecondDerivative_unique (f + g) i i _ _
    ((SobolevH2.add_mem hf hg).2 i i).choose_spec
    ⟨midf + midg,
     hasWeakDerivative_add f g i midf midg hdf hdg,
     hasWeakDerivative_add midf midg i _ _ hdf' hdg'⟩


/-- The Laplacian commutes with scalar multiplication. -/
lemma weakLaplacian_smul (c : ℂ) (f : L2_R3) (hf : MemSobolevH2 f) :
    weakLaplacian (c • f) (SobolevH2.smul_mem c hf) =
    c • weakLaplacian f hf := by
  simp only [weakLaplacian, smul_neg, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨mid, hd_first, hd_second⟩ := (hf.2 i i).choose_spec
  exact hasWeakSecondDerivative_unique (c • f) i i _ _
    ((SobolevH2.smul_mem c hf).2 i i).choose_spec
    ⟨c • mid,
     hasWeakDerivative_smul c f i mid hd_first,
     hasWeakDerivative_smul c mid i _ hd_second⟩


/-- The Laplacian as a linear map on the H² submodule.

    This is the operator that becomes `Generator.op` for the
    free-particle evolution exp(itΔ). -/
noncomputable def laplacianLinearMap : SobolevH2 →ₗ[ℂ] L2_R3 where
  toFun := fun ⟨f, hf⟩ => weakLaplacian f hf
  map_add' := fun ⟨f, hf⟩ ⟨g, hg⟩ => weakLaplacian_add f g hf hg
  map_smul' := fun c ⟨f, hf⟩ => weakLaplacian_smul c f hf

end Spectra.Sobolev
