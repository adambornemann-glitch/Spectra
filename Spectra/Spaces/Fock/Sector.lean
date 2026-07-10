/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Fock.BoseFermi

/-!
# Fock sectors, the vacuum, and the finite-particle core

The sector embeddings of the `n`-particle spaces into the Fock spaces of
`Spectra/Spaces/Fock/Basic.lean` and `BoseFermi.lean`, the vacuum vectors, and the dense
finite-particle cores. Fock Spaces milestone M3 step 1.

The generic layer wraps Mathlib's `lp.single` into a bundled linear isometry
(`lp.singleLinearIsometry`) and proves that the ranges of the `lp.single` span densely
(`lp.dense_iSup_range_lsingle`, immediate from `lp.hasSum_single`), plus the `p = 2`
orthogonality of distinct sectors. Mathlib has neither the bundled isometry nor the density
statement, so — mirroring `LinearIsometryEquiv.lpCongrRight` in
`Spectra/Spaces/HilbertSum/Congr.lean` — this layer lives in the root namespace as a
Mathlib-upstream candidate, in the scalar generality (`NormedRing` + `IsBoundedSMul`) of
Mathlib's `lp` module structure.

## Main definitions

* `lp.singleLinearIsometry` — `lp.single` as a linear isometry `E i →ₗᵢ[𝕜] lp E p`.
* `Spectra.fockSector` / `Spectra.boseSector` / `Spectra.fermiSector` — the `n`-particle
  sector embeddings into `fullFock` / `boseFock` / `fermiFock`.
* `Spectra.vacuumPower` — the empty tensor, the vacuum of the `0`-particle sector;
  `Spectra.fockVacuum` / `Spectra.boseVacuum` / `Spectra.fermiVacuum` — the vacuum vectors.
* `Spectra.finParticle` / `Spectra.boseFinParticle` / `Spectra.fermiFinParticle` — the
  finite-particle cores: the algebraic spans (`⨆` of sector ranges) inside the Fock spaces.

## Main results

* `lp.dense_iSup_range_lsingle` — the ranges of `lp.single` span densely in `lp E p` for
  `p ≠ ∞`.
* `lp.inner_single_single_of_ne` — distinct `lp`-sectors are orthogonal (`p = 2`).
* `Spectra.inner_fockSector_same` / `Spectra.inner_fockSector_of_ne` — the sector
  embeddings preserve inner products, and distinct sectors are orthogonal.
* `Spectra.norm_vacuumPower` / `norm_fockVacuum` / `norm_boseVacuum` / `norm_fermiVacuum` —
  the vacua are unit vectors.
* `Spectra.dense_finParticle` / `dense_boseFinParticle` / `dense_fermiFinParticle` — the
  finite-particle cores are dense in their Fock spaces.
-/

noncomputable section

open scoped ENNReal

/-! ## Generic `lp` layer: `lp.single` as a linear isometry, density, orthogonality -/

section GenericLp

variable {α 𝕜 : Type*} {E : α → Type*} {p : ℝ≥0∞}
variable [∀ i, NormedAddCommGroup (E i)] [DecidableEq α]

namespace lp

section Single

variable [NormedRing 𝕜] [∀ i, Module 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜 (E i)] [Fact (1 ≤ p)]

variable (𝕜 p) in
/-- `lp.single p i` as a linear isometry `E i →ₗᵢ[𝕜] lp E p`: the element supported at the
single index `i`. (Mathlib bundles `lp.single` only as `lp.lsingle`, a plain linear map,
and as `lp.singleContinuousLinearMap`; the isometry content is `lp.norm_single`.) -/
protected def singleLinearIsometry (i : α) : E i →ₗᵢ[𝕜] lp E p where
  toLinearMap := lp.lsingle p i
  norm_map' x := lp.norm_single (zero_lt_one.trans_le Fact.out) i x

@[simp]
theorem singleLinearIsometry_apply (i : α) (x : E i) :
    lp.singleLinearIsometry 𝕜 p i x = lp.single p i x :=
  rfl

@[simp]
theorem singleLinearIsometry_toLinearMap (i : α) :
    (lp.singleLinearIsometry 𝕜 p i : E i →ₗᵢ[𝕜] lp E p).toLinearMap = lp.lsingle p i :=
  rfl

variable (𝕜) in
/-- ★ **Density of the finitely-supported elements**: for `p ≠ ∞` the ranges of the
coordinate inclusions `lp.single p i` span a dense submodule of `lp E p`. Immediate from
`lp.hasSum_single`: the finitely-supported partial sums of `f` converge to `f`. -/
theorem dense_iSup_range_lsingle (hp : p ≠ ∞) :
    Dense (↑(⨆ i : α, LinearMap.range (lp.lsingle (𝕜 := 𝕜) (E := E) p i)) : Set (lp E p)) :=
  fun f =>
    mem_closure_of_tendsto (lp.hasSum_single hp f) <| Filter.Eventually.of_forall fun _ =>
      SetLike.mem_coe.mpr <| Submodule.sum_mem _ fun i _ =>
        Submodule.mem_iSup_of_mem i <| LinearMap.mem_range_self _ (f i)

end Single

section L2

variable [RCLike 𝕜] [∀ i, InnerProductSpace 𝕜 (E i)]

/-- Distinct `lp`-sectors are orthogonal: singles at distinct indices have vanishing inner
product in `lp E 2`. (For equal indices the inner product is preserved — that is the generic
`LinearIsometry.inner_map_map` applied to `lp.singleLinearIsometry`.) -/
theorem inner_single_single_of_ne {i j : α} (h : i ≠ j) (a : E i) (b : E j) :
    inner 𝕜 (lp.single 2 i a : lp E 2) (lp.single 2 j b) = 0 := by
  rw [lp.inner_single_left, lp.single_apply_ne 2 j b h, inner_zero_right]

end L2

end lp

end GenericLp

/-! ## The Fock sector embeddings -/

namespace Spectra

variable (𝕜 H : Type*) [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The **`n`-particle sector embedding** into the full Fock space: `lp.single` at index
`n`, as a linear isometry `HilbertTensorPower 𝕜 n H →ₗᵢ[𝕜] fullFock 𝕜 H`. -/
def fockSector (n : ℕ) : HilbertTensorPower 𝕜 n H →ₗᵢ[𝕜] fullFock 𝕜 H :=
  lp.singleLinearIsometry (E := fun k => HilbertTensorPower 𝕜 k H) 𝕜 2 n

/-- The sector embedding is `lp.single` (definitionally). -/
theorem fockSector_eq_single (n : ℕ) (x : HilbertTensorPower 𝕜 n H) :
    fockSector 𝕜 H n x = lp.single 2 n x :=
  rfl

@[simp]
theorem fockSector_apply_same (n : ℕ) (x : HilbertTensorPower 𝕜 n H) :
    fockSector 𝕜 H n x n = x :=
  lp.single_apply_self (E := fun k => HilbertTensorPower 𝕜 k H) 2 n x

/-- Off the embedding index, a sector vector has vanishing components. -/
theorem fockSector_apply_ne {m n : ℕ} (h : m ≠ n) (x : HilbertTensorPower 𝕜 n H) :
    fockSector 𝕜 H n x m = 0 :=
  lp.single_apply_ne (E := fun k => HilbertTensorPower 𝕜 k H) 2 n x h

/-- The sector embedding preserves inner products: it is unitary onto its range. -/
theorem inner_fockSector_same (n : ℕ) (x y : HilbertTensorPower 𝕜 n H) :
    inner 𝕜 (fockSector 𝕜 H n x) (fockSector 𝕜 H n y) = inner 𝕜 x y :=
  (fockSector 𝕜 H n).inner_map_map x y

/-- **Distinct sectors are orthogonal** in the full Fock space. -/
theorem inner_fockSector_of_ne {m n : ℕ} (h : m ≠ n) (x : HilbertTensorPower 𝕜 m H)
    (y : HilbertTensorPower 𝕜 n H) :
    inner 𝕜 (fockSector 𝕜 H m x) (fockSector 𝕜 H n y) = 0 :=
  lp.inner_single_single_of_ne (E := fun k => HilbertTensorPower 𝕜 k H) h x y

/-- The **bosonic `n`-particle sector embedding** into the bosonic Fock space. -/
def boseSector (n : ℕ) : HilbertTensorPower.symPower 𝕜 n H →ₗᵢ[𝕜] boseFock 𝕜 H :=
  lp.singleLinearIsometry (E := fun k => ↥(HilbertTensorPower.symPower 𝕜 k H)) 𝕜 2 n

/-- The **fermionic `n`-particle sector embedding** into the fermionic Fock space. -/
def fermiSector (n : ℕ) : HilbertTensorPower.altPower 𝕜 n H →ₗᵢ[𝕜] fermiFock 𝕜 H :=
  lp.singleLinearIsometry (E := fun k => ↥(HilbertTensorPower.altPower 𝕜 k H)) 𝕜 2 n

/-! ## The vacuum -/

/-- The **vacuum of the `0`-particle sector**: the empty pure tensor in
`HilbertTensorPower 𝕜 0 H`. -/
def vacuumPower : HilbertTensorPower 𝕜 0 H :=
  HilbertTensorPower.tprod 𝕜 fun i => i.elim0

/-- The empty tensor is a unit vector: the empty product of norms is `1`. -/
@[simp]
theorem norm_vacuumPower : ‖vacuumPower 𝕜 H‖ = 1 := by
  simp [vacuumPower]

/-- The empty tensor is (vacuously) bosonic: at rank `0` the symmetric sector is `⊤`. -/
theorem vacuumPower_mem_symPower :
    vacuumPower 𝕜 H ∈ HilbertTensorPower.symPower 𝕜 0 H := by
  rw [HilbertTensorPower.symPower_zero]
  exact Submodule.mem_top

/-- The empty tensor is (vacuously) fermionic: at rank `0` the antisymmetric sector is `⊤`. -/
theorem vacuumPower_mem_altPower :
    vacuumPower 𝕜 H ∈ HilbertTensorPower.altPower 𝕜 0 H := by
  rw [HilbertTensorPower.altPower_zero]
  exact Submodule.mem_top

/-- The **vacuum vector** of the full Fock space: the empty tensor in the `0`-particle
sector. -/
def fockVacuum : fullFock 𝕜 H :=
  fockSector 𝕜 H 0 (vacuumPower 𝕜 H)

/-- The vacuum is a unit vector. -/
@[simp]
theorem norm_fockVacuum : ‖fockVacuum 𝕜 H‖ = 1 := by
  rw [fockVacuum, (fockSector 𝕜 H 0).norm_map, norm_vacuumPower]

/-- The **bosonic vacuum**: the empty tensor, embedded in the `0`-particle sector of the
bosonic Fock space (bosonic by `symPower_zero`). -/
def boseVacuum : boseFock 𝕜 H :=
  boseSector 𝕜 H 0 ⟨vacuumPower 𝕜 H, vacuumPower_mem_symPower 𝕜 H⟩

/-- The bosonic vacuum is a unit vector. -/
@[simp]
theorem norm_boseVacuum : ‖boseVacuum 𝕜 H‖ = 1 := by
  rw [boseVacuum, (boseSector 𝕜 H 0).norm_map]
  exact norm_vacuumPower 𝕜 H

/-- The **fermionic vacuum**: the empty tensor, embedded in the `0`-particle sector of the
fermionic Fock space (fermionic by `altPower_zero`). -/
def fermiVacuum : fermiFock 𝕜 H :=
  fermiSector 𝕜 H 0 ⟨vacuumPower 𝕜 H, vacuumPower_mem_altPower 𝕜 H⟩

/-- The fermionic vacuum is a unit vector. -/
@[simp]
theorem norm_fermiVacuum : ‖fermiVacuum 𝕜 H‖ = 1 := by
  rw [fermiVacuum, (fermiSector 𝕜 H 0).norm_map]
  exact norm_vacuumPower 𝕜 H

/-! ## The finite-particle core -/

/-- The **finite-particle core** of the full Fock space: the algebraic span (`⨆` of the
sector ranges) of the finitely-many-particle states. -/
def finParticle : Submodule 𝕜 (fullFock 𝕜 H) :=
  ⨆ n, LinearMap.range (fockSector 𝕜 H n).toLinearMap

/-- Sector vectors lie in the finite-particle core. -/
theorem fockSector_mem_finParticle (n : ℕ) (x : HilbertTensorPower 𝕜 n H) :
    fockSector 𝕜 H n x ∈ finParticle 𝕜 H :=
  Submodule.mem_iSup_of_mem n (LinearMap.mem_range_self _ x)

/-- ★ The finite-particle core is dense in the full Fock space. -/
theorem dense_finParticle : Dense (finParticle 𝕜 H : Set (fullFock 𝕜 H)) :=
  lp.dense_iSup_range_lsingle 𝕜 ENNReal.ofNat_ne_top

/-- The **bosonic finite-particle core**: the algebraic span of the bosonic sectors inside
the bosonic Fock space. The natural domain for the exponential vectors of milestone M3. -/
def boseFinParticle : Submodule 𝕜 (boseFock 𝕜 H) :=
  ⨆ n, LinearMap.range (boseSector 𝕜 H n).toLinearMap

/-- Bosonic sector vectors lie in the bosonic finite-particle core. -/
theorem boseSector_mem_boseFinParticle (n : ℕ) (x : HilbertTensorPower.symPower 𝕜 n H) :
    boseSector 𝕜 H n x ∈ boseFinParticle 𝕜 H :=
  Submodule.mem_iSup_of_mem n (LinearMap.mem_range_self _ x)

/-- ★ The bosonic finite-particle core is dense in the bosonic Fock space. -/
theorem dense_boseFinParticle : Dense (boseFinParticle 𝕜 H : Set (boseFock 𝕜 H)) :=
  lp.dense_iSup_range_lsingle 𝕜 ENNReal.ofNat_ne_top

/-- The **fermionic finite-particle core**: the algebraic span of the fermionic sectors
inside the fermionic Fock space. -/
def fermiFinParticle : Submodule 𝕜 (fermiFock 𝕜 H) :=
  ⨆ n, LinearMap.range (fermiSector 𝕜 H n).toLinearMap

/-- Fermionic sector vectors lie in the fermionic finite-particle core. -/
theorem fermiSector_mem_fermiFinParticle (n : ℕ) (x : HilbertTensorPower.altPower 𝕜 n H) :
    fermiSector 𝕜 H n x ∈ fermiFinParticle 𝕜 H :=
  Submodule.mem_iSup_of_mem n (LinearMap.mem_range_self _ x)

/-- ★ The fermionic finite-particle core is dense in the fermionic Fock space. -/
theorem dense_fermiFinParticle : Dense (fermiFinParticle 𝕜 H : Set (fermiFock 𝕜 H)) :=
  lp.dense_iSup_range_lsingle 𝕜 ENNReal.ofNat_ne_top

end Spectra
