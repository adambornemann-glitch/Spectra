/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Fock.BoseFermi
import Spectra.Spaces.Sobolev.WeakDerivative

/-!
# The `N`-electron antisymmetric state space

The named carrier object of Density Functional Theory (lane **S1**): the Hilbert space `ℋ_N` of
`N` identical fermions — the Pauli-allowed, totally **antisymmetric** sector of the `N`-fold tensor
power of a one-particle space `𝓗₁`. This is a thin, hydrogen-free packaging of the Fock machinery
in `Spaces/Fock/`, giving DFT a single stable name to build on.

Following the project's spin decision, the space is defined **generically over an abstract
one-particle space `𝓗₁`** and instantiated at the physical orbital space `l2R3 = L²(ℝ³)`
(`electronSpace`); the physical spin-½ space `L²(ℝ³;ℂ²) = l2R3 ⊗ ℂ²` differs only by a
finite-dimensional `(ℂ²)^{⊗N}` rider and is deferred to the spin tensor factor. `𝓗₁` need not even
be complete — completeness of `ℋ_N` is supplied by the tensor-power completion.

The one genuinely new term here is the **normalized Slater determinant** `slaterDet x = √(N!) •
altProj(⨂ᵢ xᵢ)`: the antisymmetrizer `altProj` carries `‖altProj(⨂x)‖² = (N!)⁻¹` (Parthasarathy
convention), so the `√(N!)` factor makes the Slater determinant of an orthonormal family a genuine
**unit reference state**, with `n_Slater = n` once the density map (S4) lands. Pauli exclusion is
`slaterDet x = 0` whenever two orbitals coincide.

## Main definitions

* `Spectra.DFT.NElectronSpace 𝓗₁ N` — the antisymmetric `N`-fermion space `ℋ_N := altPower ℂ N 𝓗₁`.
* `Spectra.DFT.electronSpace N` — the physical orbital instantiation `NElectronSpace l2R3 N`.
* `Spectra.DFT.slaterDet x` — the normalized Slater determinant of `x : Fin N → 𝓗₁`.

## Main results

* Instance re-exposure: `NElectronSpace 𝓗₁ N` is a complete inner-product space (Pauli sector).
* `norm_slaterDet` — `‖slaterDet x‖ = 1` for an orthonormal family (unit reference state).
* `slaterDet_eq_zero` — Pauli exclusion: `slaterDet x = 0` if two orbitals coincide.
* `NElectronSpace_ne_bot` — the space is nontrivial when `𝓗₁` holds `N` orthonormal vectors.

## References

* [Lieb, Seiringer, *The Stability of Matter in Quantum Mechanics*][lieb2010].
* [Parthasarathy, *An Introduction to Quantum Stochastic Calculus*][parthasarathy1992] (the
  `(n!)⁻¹` antisymmetrizer normalization).
-/

open scoped InnerProductSpace Nat
open Spectra.HilbertTensorPower

namespace Spectra.DFT

/-- The **`N`-electron antisymmetric (fermionic) state space** `ℋ_N`: the Pauli-allowed, totally
antisymmetric sector of the `N`-fold tensor power of the one-particle space `𝓗₁`. Generic over an
abstract `𝓗₁` (no completeness needed on `𝓗₁`); the physical instantiations are `l2R3` (orbital)
and `l2R3 ⊗ ℂ²` (spin-½). A genuine complete inner-product space — see the instance re-exposure
below. -/
noncomputable abbrev NElectronSpace (𝓗₁ : Type*) [NormedAddCommGroup 𝓗₁] [InnerProductSpace ℂ 𝓗₁]
    (N : ℕ) : Submodule ℂ (HilbertTensorPower ℂ N 𝓗₁) :=
  altPower ℂ N 𝓗₁

/-- The physical **orbital** `N`-electron space, `ℋ_N` instantiated at the one-particle space
`l2R3 = L²(ℝ³)`. The spin-½ space `L²(ℝ³;ℂ²)` adds only a finite-dimensional `(ℂ²)^{⊗N}` factor. -/
noncomputable abbrev electronSpace (N : ℕ) :
    Submodule ℂ (HilbertTensorPower ℂ N Spectra.Sobolev.l2R3) :=
  NElectronSpace Spectra.Sobolev.l2R3 N

section Instances

variable (𝓗₁ : Type*) [NormedAddCommGroup 𝓗₁] [InnerProductSpace ℂ 𝓗₁] (N : ℕ)

-- The `N`-electron space is a genuine complete inner-product space: `NormedAddCommGroup` and
-- `InnerProductSpace ℂ` are inherited from the submodule, and `CompleteSpace` from the closedness
-- of `altPower` (registered globally in `Spaces/Fock/BoseFermi.lean`). All found by inference.
noncomputable example : NormedAddCommGroup (NElectronSpace 𝓗₁ N) := inferInstance
noncomputable example : InnerProductSpace ℂ (NElectronSpace 𝓗₁ N) := inferInstance
noncomputable example : CompleteSpace (NElectronSpace 𝓗₁ N) := inferInstance

end Instances

variable {𝓗₁ : Type*} [NormedAddCommGroup 𝓗₁] [InnerProductSpace ℂ 𝓗₁]

/-- The **normalized Slater determinant** of a family `x : Fin N → 𝓗₁` of one-particle orbitals:
`slaterDet x = √(N!) • altProj(⨂ᵢ xᵢ)`, an element of the fermionic sector `ℋ_N`. The `√(N!)`
prefactor cancels the antisymmetrizer's `(N!)⁻¹` normalization, so `slaterDet` of an **orthonormal**
family is a unit vector (`norm_slaterDet`). -/
noncomputable def slaterDet {N : ℕ} (x : Fin N → 𝓗₁) : NElectronSpace 𝓗₁ N :=
  (Real.sqrt (N ! : ℝ) : ℂ) • ⟨altProj ℂ N 𝓗₁ (tprod ℂ x), altProj_mem_altPower _⟩

/-- The underlying vector of the Slater determinant: `√(N!) • altProj(⨂ᵢ xᵢ)`. -/
theorem slaterDet_coe {N : ℕ} (x : Fin N → 𝓗₁) :
    (slaterDet x : HilbertTensorPower ℂ N 𝓗₁)
      = (Real.sqrt (N ! : ℝ) : ℂ) • altProj ℂ N 𝓗₁ (tprod ℂ x) := rfl

/-- **The normalized Slater determinant is a unit vector.** For an orthonormal family of orbitals,
`‖slaterDet x‖ = 1`: the `√(N!)` prefactor exactly cancels `‖altProj(⨂x)‖ = √((N!)⁻¹)`. This is the
"normalized Slater reference state" of the Pauli sector. -/
theorem norm_slaterDet {N : ℕ} {x : Fin N → 𝓗₁} (hx : Orthonormal ℂ x) :
    ‖slaterDet x‖ = 1 := by
  have hfac : (0 : ℝ) < (N ! : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have hnorm_scalar : ‖(Real.sqrt (N ! : ℝ) : ℂ)‖ = Real.sqrt (N ! : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hnorm_alt : ‖altProj ℂ N 𝓗₁ (tprod ℂ x)‖ = Real.sqrt ((N ! : ℝ)⁻¹) := by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_altProj_tprod x hx]
  rw [show ‖slaterDet x‖ = ‖(slaterDet x : HilbertTensorPower ℂ N 𝓗₁)‖ from rfl, slaterDet_coe,
    norm_smul, hnorm_scalar, hnorm_alt, ← Real.sqrt_mul hfac.le,
    mul_inv_cancel₀ (ne_of_gt hfac), Real.sqrt_one]

/-- **Pauli exclusion.** If two orbitals of the family coincide, the Slater determinant vanishes:
`slaterDet x = 0`. A direct consequence of `altProj(⨂x) = 0` at a repeated tensor factor. -/
theorem slaterDet_eq_zero {N : ℕ} (x : Fin N → 𝓗₁) {i j : Fin N} (hij : i ≠ j)
    (h : x i = x j) : slaterDet x = 0 := by
  have h0 : (slaterDet x : HilbertTensorPower ℂ N 𝓗₁) = 0 := by
    rw [slaterDet_coe, altProj_tprod_eq_zero x i j hij h, smul_zero]
  exact ZeroMemClass.coe_eq_zero.mp h0

/-- The `N`-electron space is **nontrivial** as soon as `𝓗₁` contains `N` orthonormal vectors
(i.e. `dim 𝓗₁ ≥ N`): its Slater determinants are nonzero. Re-exposes `altPower_ne_bot`. -/
theorem NElectronSpace_ne_bot {N : ℕ} (x : Fin N → 𝓗₁) (hx : Orthonormal ℂ x) :
    NElectronSpace 𝓗₁ N ≠ ⊥ :=
  altPower_ne_bot x hx

end Spectra.DFT
