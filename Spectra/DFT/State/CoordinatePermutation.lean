/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Sobolev.WeakDerivative
import Spectra.Spaces.Fock.Symmetrizer
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Coordinate-permutation unitaries and the antisymmetric `L²` space

Substrate for the Density Functional Theory coordinate realization (lane **S0**, sub-milestone iii).
The eventual S0 goal is a unitary `altPower ℂ N l2R3 ≃ₗᵢ L²_a((ℝ³)^N)` between the abstract
fermionic Fock sector and the *antisymmetric* `L²` functions of `N` particles. The full isometry is
blocked on a genuine measure-theoretic density fact (the span of simple tensors is dense in
`L²(μ × ν)`) with no mathlib support — deferred. This file builds the two pieces that are gate-free
and load-bearing:

1. A general **`Lp`-unitary from a measure-preserving measurable equivalence**
   (`Spectra.lpEquivₗᵢOfMeasurePreserving`): mathlib ships only the one-directional
   `Lp.compMeasurePreservingₗᵢ`, so the bidirectional `≃ₗᵢ` is a genuine gap-fill, reusable well
   beyond DFT.

2. The **coordinate-permutation action** `coordPerm σ` on the `N`-body space `L²(Fin N → ℝ³)` — the
   `L²`-side mirror of the tensor-power `permUnitary` — and the intrinsically defined
   **antisymmetric `L²` subspace** `antisymL2 N := {f | ∀ σ, coordPerm σ f = sign(σ) • f}`, proved a
   *closed* subspace (hence a Hilbert space in its own right). This is exactly the target of
   `Φ(altPower)` once the deferred coordinate isometry `Φ` lands.

The `N`-body configuration space is modeled as `Fin N → R3` with the product Lebesgue measure; a
permutation `σ` reindexes the particle slots (`MeasurableEquiv.piCongrLeft`), which is measure-
preserving because all factors carry the same measure (`volume_measurePreserving_piCongrLeft`).

## Main definitions

* `Spectra.lpEquivₗᵢOfMeasurePreserving` — `Lp E 2 ν ≃ₗᵢ[𝕜] Lp E 2 μ` from `e : α ≃ᵐ β`,
  `MeasurePreserving e μ ν`.
* `Spectra.DFT.nBodyL2 N` — the `N`-body space `L²(Fin N → ℝ³)`.
* `Spectra.DFT.coordPerm σ` — the coordinate-permutation unitary.
* `Spectra.DFT.antisymL2 N` — the antisymmetric `L²` subspace.

## Main results

* `Spectra.DFT.isClosed_antisymL2` — `antisymL2 N` is closed; hence a complete inner-product space.
-/

open MeasureTheory
open scoped ENNReal

namespace Spectra

/-- The round-trip identity behind `lpEquivₗᵢOfMeasurePreserving`: precomposition with `e` undoes
precomposition with `e.symm`, exactly (not merely a.e.), because `e` is a measurable *equivalence*.
-/
private theorem compMeasurePreservingₗᵢ_apply_symm (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) (y : Lp E 2 μ) :
    Lp.compMeasurePreservingₗᵢ 𝕜 (⇑e) he
        (Lp.compMeasurePreservingₗᵢ 𝕜 (⇑e.symm) (MeasurePreserving.symm e he) y) = y := by
  have key : Lp.compMeasurePreservingₗᵢ 𝕜 (⇑e) he
        (Lp.compMeasurePreservingₗᵢ 𝕜 (⇑e.symm) (MeasurePreserving.symm e he) y)
      = Lp.compMeasurePreserving (⇑e) he
          (Lp.compMeasurePreserving (⇑e.symm) (MeasurePreserving.symm e he) y) := rfl
  rw [key]
  refine Lp.ext ?_
  have e1 := Lp.coeFn_compMeasurePreserving
    (Lp.compMeasurePreserving (⇑e.symm) (MeasurePreserving.symm e he) y) he
  have e2 := Lp.coeFn_compMeasurePreserving y (MeasurePreserving.symm e he)
  have e3 := he.quasiMeasurePreserving.ae_eq_comp e2
  filter_upwards [e1, e3] with p h1 h3
  simp only [Function.comp_apply] at h1 h3 ⊢
  rw [h1, h3, e.symm_apply_apply]

/-- **An `Lp` unitary from a measure-preserving measurable equivalence.** Given `e : α ≃ᵐ β` that
pushes `μ` to `ν`, precomposition with `e` is a linear isometry `Lp E 2 ν →ₗᵢ Lp E 2 μ`, and
precomposition with `e.symm` is its inverse, so together they form a unitary
`Lp E 2 ν ≃ₗᵢ Lp E 2 μ`. Mathlib provides only the one-directional `Lp.compMeasurePreservingₗᵢ`;
this packages the equivalence, a reusable gap-fill (an upstream candidate to sit beside
`compMeasurePreservingₗᵢ`). -/
noncomputable def lpEquivₗᵢOfMeasurePreserving (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) :
    Lp E 2 ν ≃ₗᵢ[𝕜] Lp E 2 μ :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ 𝕜 (⇑e) he)
    (fun y => ⟨Lp.compMeasurePreservingₗᵢ 𝕜 (⇑e.symm) (MeasurePreserving.symm e he) y,
      compMeasurePreservingₗᵢ_apply_symm 𝕜 e he y⟩)

/-- The forward direction of `lpEquivₗᵢOfMeasurePreserving` acts a.e. as precomposition with `e`. -/
theorem lpEquivₗᵢOfMeasurePreserving_coeFn (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) (g : Lp E 2 ν) :
    lpEquivₗᵢOfMeasurePreserving 𝕜 e he g =ᵐ[μ] g ∘ e :=
  Lp.coeFn_compMeasurePreserving g he

/-- The inverse direction of `lpEquivₗᵢOfMeasurePreserving` acts a.e. as precomposition with
`e.symm`. (The abstract `ofSurjective` inverse coincides with the concrete `e.symm`-pullback by
injectivity of the forward isometry.) -/
theorem lpEquivₗᵢOfMeasurePreserving_symm_coeFn (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) (g : Lp E 2 μ) :
    (lpEquivₗᵢOfMeasurePreserving 𝕜 e he).symm g =ᵐ[ν] g ∘ e.symm := by
  have hsymm : (lpEquivₗᵢOfMeasurePreserving 𝕜 e he).symm g
      = Lp.compMeasurePreservingₗᵢ 𝕜 (⇑e.symm) (MeasurePreserving.symm e he) g := by
    refine (lpEquivₗᵢOfMeasurePreserving 𝕜 e he).injective ?_
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact (compMeasurePreservingₗᵢ_apply_symm 𝕜 e he g).symm
  rw [hsymm]
  exact Lp.coeFn_compMeasurePreserving g (MeasurePreserving.symm e he)

end Spectra

namespace Spectra.DFT

open Spectra.Sobolev Spectra.HilbertTensorPower

-- Note: the `MeasureSpace` structure here rests on the custom `MeasurableSpace R3 := borel R3`
-- instance from `Spaces/Sobolev/WeakDerivative.lean`; the whole `coordPerm` construction relies on
-- that Borel structure being the one reconciled with `R3`'s finite-dimensional Haar `volume`.

/-- The **`N`-body configuration space** `L²((ℝ³)^N)`, modeled as `L²` of `Fin N → ℝ³` with the
product Lebesgue measure (`volume = Measure.pi (fun _ => volume)`). A genuine complex Hilbert space.
-/
noncomputable abbrev nBodyL2 (N : ℕ) : Type :=
  Lp ℂ 2 (volume : Measure (Fin N → R3))

/-- The **coordinate-permutation unitary** on the `N`-body `L²` space: the permutation `σ` reindexes
the particle coordinate slots, `(coordPerm σ f)(x) = f(x ∘ σ⁻¹)` a.e. This is the `L²`-side avatar
of the tensor-power `permUnitary` (up to the relabeling `σ ↦ σ⁻¹`: `piCongrLeft σ` pulls back by
`σ⁻¹`). It is measure-preserving because all `N` coordinate factors carry the same Lebesgue measure.
-/
noncomputable def coordPerm {N : ℕ} (σ : Equiv.Perm (Fin N)) : nBodyL2 N ≃ₗᵢ[ℂ] nBodyL2 N :=
  Spectra.lpEquivₗᵢOfMeasurePreserving ℂ (MeasurableEquiv.piCongrLeft (fun _ => R3) σ)
    (volume_measurePreserving_piCongrLeft (fun _ => R3) σ)

/-- The **antisymmetric `L²` functions**: those `f` obeying `coordPerm σ f = sign(σ) • f` for every
particle permutation `σ` (fermionic exchange antisymmetry). This is the intrinsic `L²`-side avatar
of the fermionic Fock sector `altPower` — the image `Φ(altPower)` once the deferred coordinate
realization `Φ` lands (`mem_altPower_iff_forall` transports to exactly this condition). -/
def antisymL2 (N : ℕ) : Submodule ℂ (nBodyL2 N) where
  carrier := {f | ∀ σ : Equiv.Perm (Fin N), coordPerm σ f = permSign ℂ σ • f}
  zero_mem' := by intro σ; simp
  add_mem' := by intro f g hf hg σ; rw [map_add, hf σ, hg σ, smul_add]
  smul_mem' := by intro c f hf σ; rw [map_smul, hf σ, smul_comm]

lemma mem_antisymL2_iff {N : ℕ} {f : nBodyL2 N} :
    f ∈ antisymL2 N ↔ ∀ σ : Equiv.Perm (Fin N), coordPerm σ f = permSign ℂ σ • f := Iff.rfl

/-- **The antisymmetric `L²` subspace is closed.** It is the intersection over all permutations `σ`
of the closed eigenrelations `coordPerm σ f = sign(σ) • f` (each an equalizer of two continuous
maps). Consequently `antisymL2 N` is a complete inner-product space — a Hilbert space in its own
right, the natural home for the fermionic density map. -/
theorem isClosed_antisymL2 (N : ℕ) : IsClosed (antisymL2 N : Set (nBodyL2 N)) := by
  have hset : (antisymL2 N : Set (nBodyL2 N))
      = ⋂ σ : Equiv.Perm (Fin N), {f | coordPerm σ f = permSign ℂ σ • f} := by
    ext f; simp only [SetLike.mem_coe, mem_antisymL2_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hset]
  refine isClosed_iInter (fun σ => ?_)
  exact isClosed_eq (coordPerm σ).continuous (continuous_const_smul _)

/-- The antisymmetric `L²` subspace is a complete space (closed subspace of a Hilbert space). -/
instance instCompleteSpaceAntisymL2 (N : ℕ) : CompleteSpace (antisymL2 N) :=
  (isClosed_antisymL2 N).completeSpace_coe

end Spectra.DFT
