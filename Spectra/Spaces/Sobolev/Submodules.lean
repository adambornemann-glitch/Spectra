/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Sobolev.Operations
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Sobolev Spaces as Submodules, and the Weak Laplacian

This file upgrades the membership predicates `MemSobolevH1`/`MemSobolevH2` (from
`WeakDerivative.lean`/`Operations.lean`) into genuine `Submodule ℂ (l2Rn d)` structures, extracts
the weak gradient and its Dirichlet norm, and assembles the weak Laplacian `-Δ` into a bundled
linear map on `H²(ℝ^d)` — the exact operator later wired into the free-particle/hydrogen generator
(at `d = 3`). Everything is generic in the dimension `d`.

## Main definitions

* `MemSobolevH1`, `MemSobolevH2`: membership predicates for `H¹(ℝ^d)`/`H²(ℝ^d)`, asserting existence
  of all first-order (resp. up to second-order) weak derivatives in `l2Rn d`.
* `SobolevH1`, `SobolevH2`: the same, packaged `Submodule ℂ (l2Rn d)` (closed under `0`, `+`, `•`).
* `weakGradient`, `gradientNormSq`: the weak gradient `∇f` of an `H¹` function and its Dirichlet
  energy `∫|∇f|² = Σᵢ‖∂ᵢf‖²`, both taken unbundled over `(f, hf : MemSobolevH1 f)`.
* `weakGradientLM`: a bundled wrapper for `weakGradient`, taking `f : SobolevH1` directly.
* `weakLaplacian`: the weak `-Δf = -Σᵢ∂ᵢ²f` for `f` with `hf : MemSobolevH2 f`.
* `laplacianLinearMap`: `-Δ` bundled as a `SobolevH2 →ₗ[ℂ] l2Rn d`.

## Main results

* `sobolevH2_le_sobolevH1`: `H² ⊆ H¹` as submodules.
* `weakLaplacian_add`, `weakLaplacian_smul`: `-Δ` is additive and homogeneous, which is exactly
  what makes `laplacianLinearMap` well-defined as a linear map.
* `gradientNormSq_nonneg`: the Dirichlet energy is non-negative.

## Implementation notes

`weakGradient` and `gradientNormSq` are kept **unbundled** — taking a raw `f : l2Rn d` together with
a separate membership proof `hf : MemSobolevH1 f` — because most call sites
(`IntegrationByParts.lean`, `Embeddings.lean`, the Hydrogen/Dirac developments) already carry `f`
and `hf` as independent hypotheses from earlier reasoning (e.g. `f` arrives as a component of an
unbundled sum, or `hf` is produced mid-proof by a density/limit argument), so demanding a
`SobolevH1` term up front would just force an extra `⟨f, hf⟩` repackaging at every use.
`laplacianLinearMap`, by contrast, is the *capstone* object — the operator handed to
`LinearPMap`/`SelfAdjointOperator` machinery downstream, which is expressed natively in terms of
`Submodule`s (`domain`, `IsSelfAdjoint` on `LinearPMap`, …) — so bundling it over `SobolevH2` is the
natural fit there. To bridge the two styles without forcing a breaking change on the unbundled API,
`weakGradientLM` is provided as an additive, bundled wrapper around `weakGradient` for callers that
already hold a `SobolevH1` term.

## References

* [Adams, Fournier, *Sobolev Spaces*][adams2003]
* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975]
* [Lieb, Loss, *Analysis*][lieb2001], Chapter 7.
-/

open MeasureTheory

namespace Spectra.Sobolev

variable {d : ℕ}

/-! ### Sobolev space membership predicates -/

/-- Predicate: f ∈ H¹(ℝ^d).
    All first-order weak derivatives exist and are in L². -/
def MemSobolevH1 (f : l2Rn d) : Prop :=
  ∀ i : Fin d, ∃ g : l2Rn d, HasWeakDerivative f i g

/-- Predicate: f ∈ H²(ℝ^d).
    All weak derivatives up to order 2 exist and are in L². -/
def MemSobolevH2 (f : l2Rn d) : Prop :=
  MemSobolevH1 f ∧
  ∀ i j : Fin d, ∃ g : l2Rn d, HasWeakSecondDerivative f i j g

/-- H¹(ℝ^d) as a ℂ-submodule of L²(ℝ^d). -/
def SobolevH1 : Submodule ℂ (l2Rn d) where
  carrier := { f | MemSobolevH1 f }
  zero_mem' := fun i => ⟨0, hasWeakDerivative_zero i⟩
  add_mem' := fun {f₁ f₂} hf₁ hf₂ i =>
    ⟨(hf₁ i).choose + (hf₂ i).choose,
     hasWeakDerivative_add f₁ f₂ i _ _ (hf₁ i).choose_spec (hf₂ i).choose_spec⟩
  smul_mem' := fun c {f} hf i =>
    ⟨c • (hf i).choose,
     hasWeakDerivative_smul c f i _ (hf i).choose_spec⟩

/-- H²(ℝ^d) as a ℂ-submodule of L²(ℝ^d). -/
def SobolevH2 : Submodule ℂ (l2Rn d) where
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
lemma sobolevH2_le_sobolevH1 : SobolevH2 (d := d) ≤ SobolevH1 := by
  intro f hf
  exact hf.1

/-! ### The weak gradient and Dirichlet integral -/

/-- Extract the weak gradient of an H¹ function.
    Returns the tuple (∂₁f, …, ∂_d f) as L² functions. -/
noncomputable def weakGradient (f : l2Rn d) (hf : MemSobolevH1 f) : Fin d → l2Rn d :=
  fun i => (hf i).choose

/-- The chosen gradient component is indeed the weak derivative. -/
lemma weakGradient_spec (f : l2Rn d) (hf : MemSobolevH1 f) (i : Fin d) :
    HasWeakDerivative f i (weakGradient f hf i) :=
  (hf i).choose_spec

/-- Bundled wrapper for `weakGradient`, taking a `SobolevH1` term directly instead of an
    `l2Rn d` function paired with a separate `MemSobolevH1` proof. Additive alongside the unbundled
    `weakGradient` (see the module docstring's Implementation notes for why both forms coexist). -/
noncomputable def weakGradientLM (f : SobolevH1 (d := d)) : Fin d → l2Rn d :=
  weakGradient f.1 f.2

/-- The gradient (Dirichlet) norm squared: ∫|∇ψ|² dx = Σᵢ ‖∂ᵢψ‖²_{L²}.

    This is the quadratic form associated to -Δ. For ψ ∈ H²:
      ⟨-Δψ, ψ⟩ = ∫|∇ψ|² dx
    which is the content of `gradient_norm_sq_eq_laplacian_inner` below. -/
noncomputable def gradientNormSq (f : l2Rn d) (hf : MemSobolevH1 f) : ℝ :=
  ∑ i : Fin d, ‖weakGradient f hf i‖ ^ 2

/-- The gradient norm squared is non-negative. -/
lemma gradientNormSq_nonneg (f : l2Rn d) (hf : MemSobolevH1 f) :
    0 ≤ gradientNormSq f hf := by
  simp only [gradientNormSq]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The weak Laplacian, i.e. **-Δ**: `weakLaplacian f hf = -Δf = -Σᵢ ∂ᵢ²f`. The defined object
    already carries the sign convention — this is *negative* Δ, not Δ itself. -/
noncomputable def weakLaplacian (f : l2Rn d) (hf : MemSobolevH2 f) : l2Rn d :=
  -∑ i : Fin d, (hf.2 i i).choose

/-- The Laplacian is additive. -/
lemma weakLaplacian_add (f g : l2Rn d) (hf : MemSobolevH2 f) (hg : MemSobolevH2 g) :
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
lemma weakLaplacian_smul (c : ℂ) (f : l2Rn d) (hf : MemSobolevH2 f) :
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

/-- **-Δ** as a linear map on the H² submodule: `laplacianLinearMap ⟨f, hf⟩ = -Δf`, matching the
    sign convention of `weakLaplacian` above.

    This is the operator that becomes `Generator.op` for the
    free-particle evolution exp(itΔ) (at `d = 3`). -/
noncomputable def laplacianLinearMap : SobolevH2 (d := d) →ₗ[ℂ] l2Rn d where
  toFun := fun ⟨f, hf⟩ => weakLaplacian f hf
  map_add' := fun ⟨f, hf⟩ ⟨g, hg⟩ => weakLaplacian_add f g hf hg
  map_smul' := fun c ⟨f, hf⟩ => weakLaplacian_smul c f hf

end Spectra.Sobolev
