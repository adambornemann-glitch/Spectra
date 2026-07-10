/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Laplacian.Basic
import Spectra.QuantumMechanics.Hydrogen.Laplacian.HalfLaplacian
import Spectra.OneParameterUnitaryGroup.Basic
import Spectra.YosidaHille.Basic
import Spectra.QuantumMechanics.Perturbation.Hardy.Inequality.Basic
import Spectra.Operator.KatoRellich
import Spectra.Spaces.Sobolev.DensityResults
import Spectra.Operator.SelfAdjoint
import Spectra.SpectralTheory.ResolventForm
import Spectra.Resolvent.Range

/-!
# The Coulomb Potential: Relative Boundedness

This file constructs the Coulomb potential V = −Z/r as a linear map on
H²(ℝ³), verifies the Kato–Rellich hypotheses, and *applies* the theorem:

  `hydrogen_isSelfAdjoint : IsSelfAdjoint (perturbedOp halfLaplacianPMap (coulombPotential p))`

i.e. H = −½Δ − Z/r, the textbook-normalized hydrogen Hamiltonian, is self-adjoint on H²(ℝ³) for
every nuclear charge Z > 0 (and, via `coulomb_kato_rellich`, the un-normalized H = −Δ + λV is
self-adjoint on H²(ℝ³) for every real coupling λ).

## Architecture

```
  Hardy/Inequality/                KatoRellich.lean
  ┌────────────────────┐           ┌─────────────────────────┐
  │ hardy_operator_    │           │ IsRelativelyBounded     │
  │   bound            │──(a)────→ │ IsSymmetricOn           │
  │ inverseR/inverseRSq│           │ kato_rellich_bound_zero │
  └────────────────────┘           └────────────┬────────────┘
            ↓                                   │
  ┌────────────────────┐                        │
  │ THIS FILE          │                        │
  │ coulombPotential   │───(b)──────────────────┘
  │ coulomb_symmetric  │
  │ coulomb_relative_  │           ┌─────────────────────────┐
  │   bound_is_zero    │──────────→│ hydrogen_isSelfAdjoint  │
  └────────────────────┘           └─────────────────────────┘
```

(a) Hardy gives ‖(1/r)ψ‖ ≤ ε‖−Δψ‖ + C_ε‖ψ‖ (relative bound 0).
(b) This file packages it in the exact shapes `kato_rellich` consumes.

## Design note (vs. the previous version)

The old file carried a "transport to Generator.domain" layer
(`coulombOnGeneratorDomain` and friends), because the generator's domain
equality with `SobolevH2` was a propositional theorem.  In the current
architecture `laplacianPMap.domain = SobolevH2` holds by `rfl`, so
`coulombPotential p : SobolevH2 →ₗ[ℂ] l2R3` *is* a
`laplacianPMap.domain →ₗ[ℂ] l2R3`.  The transport layer is deleted, and
the corresponding sorries with it.

## Main definitions

* `CoulombParams` — the nuclear charge Z > 0.
* `coulombMultiplier` — the function x ↦ −Z/|x| (real-valued; key for symmetry).
* `coulombPotential` — V = −Z/r as a linear map `SobolevH2 →ₗ[ℂ] l2R3`.

## Main statements

* `coulomb_isSymmetricOn` — V is symmetric on Dom(−Δ).
* `coulomb_relative_bound_is_zero` — V is (−Δ)-bounded with relative bound 0.
* `coulomb_kato_rellich` — −Δ + λV is self-adjoint on H² for every λ : ℝ.
* `hydrogen_isSelfAdjoint` — **the textbook hydrogen Hamiltonian −½Δ − Z/r is
  self-adjoint on H²(ℝ³)**, proved via the `−½Δ`-normalized re-threading
  (`coulomb_isSymmetricOn_half`, `coulomb_relative_bound_is_zero_half`) of the
  `−Δ` results above, at the fixed coupling `λ = 1`.

## References

* [Kato, *Perturbation Theory*][kato1995], §V.5, Example 5.2.
* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975],
  Example 2, p. 167.
-/
open MeasureTheory Complex Filter InnerProductSpace
open Spectra.Sobolev
open Spectra.OneParameterUnitaryGroup
open Spectra.Operator
open Spectra.Resolvent
open scoped Topology NNReal ENNReal

namespace Spectra.QuantumMechanics.Hydrogen

/-! ## The Coulomb multiplier function -/

/-- The nuclear charge (positive real parameter). -/
structure CoulombParams where
  /-- The nuclear charge `Z`. -/
  Z : ℝ
  hZ : 0 < Z

/-- The Coulomb multiplier function: x ↦ −Z/|x|.

    Defined as 0 at the origin (measure-zero, irrelevant for L²).
    This is a real-valued function, which is key for symmetry. -/
noncomputable def coulombMultiplier (p : CoulombParams) (x : R3) : ℝ :=
  if ‖x‖ = 0 then 0 else -p.Z / ‖x‖

/-- The Coulomb multiplier is measurable. -/
lemma coulombMultiplier_measurable (p : CoulombParams) :
    Measurable (coulombMultiplier p) := by
  unfold coulombMultiplier
  exact Measurable.ite (measurableSet_eq_fun measurable_norm measurable_const)
    measurable_const (measurable_const.div measurable_norm)

/-- The Coulomb multiplier is real-valued (trivially, since codomain is ℝ). -/
lemma coulombMultiplier_real (p : CoulombParams) (x : R3) :
    (coulombMultiplier p x : ℂ) = starRingEnd ℂ (coulombMultiplier p x : ℂ) := by
  rw [Complex.conj_ofReal]

/-- Pointwise bound: |coulombMultiplier(x)| = Z/|x| = Z · inverseR(x). -/
lemma coulombMultiplier_abs (p : CoulombParams) (x : R3) :
    |coulombMultiplier p x| = p.Z * inverseR x := by
  simp only [coulombMultiplier, inverseR]
  split_ifs with h
  · simp
  · rw [abs_div, abs_neg, abs_of_pos p.hZ]
    simp only [abs_norm, one_div]
    ring

/-- Pointwise squared bound: coulombMultiplier(x)² = Z² · inverseRSq(x). -/
lemma coulombMultiplier_sq (p : CoulombParams) (x : R3) :
    coulombMultiplier p x ^ 2 = p.Z ^ 2 * inverseRSq x := by
  simp only [coulombMultiplier, inverseRSq]
  split_ifs with h
  · simp
  · rw [neg_div, neg_sq, div_pow, mul_one_div]

/-! ## (1/r)ψ is in L² for ψ ∈ H¹ -/

/-- `(Z/r)ψ ∈ L²` for `ψ ∈ H¹`. Pointwise `‖(−Z/|x|)·ψ(x)‖² = Z²·inverseRSq(x)·‖ψ(x)‖²`,
which is integrable by Hardy's inequality (`inverseRSq_mul_sq_integrable`). -/
theorem coulomb_mul_memLp
    (p : CoulombParams) (ψ : l2R3) (hψ : MemSobolevH1 ψ) :
    MemLp (fun x => (coulombMultiplier p x : ℂ) * (ψ : R3 → ℂ) x)
      2 (volume : Measure R3) := by
  have h_meas : AEStronglyMeasurable
      (fun x => (coulombMultiplier p x : ℂ) * (ψ : R3 → ℂ) x) volume :=
    (Complex.measurable_ofReal.comp (coulombMultiplier_measurable p)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable ψ)
  rw [memLp_two_iff_integrable_sq_norm h_meas]
  refine ((inverseRSq_mul_sq_integrable ψ hψ).const_mul (p.Z ^ 2)).congr
    (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, coulombMultiplier_sq]
  ring

/-- The Coulomb potential applied to an H² function is in L². -/
theorem coulomb_mul_memLp_H2
    (p : CoulombParams) (ψ : l2R3) (hψ : MemSobolevH2 ψ) :
    MemLp (fun x => (coulombMultiplier p x : ℂ) * (ψ : R3 → ℂ) x)
      2 (volume : Measure R3) :=
  coulomb_mul_memLp p ψ (sobolevH2_le_sobolevH1 hψ)

/-! ## The Coulomb potential as a linear map on H²

Because `laplacianPMap.domain = SobolevH2` definitionally, this map needs
no further transport: it is already of the type
`laplacianPMap.domain →ₗ[ℂ] l2R3` that Kato–Rellich consumes.
-/

/-- The Coulomb potential `V = −Z/r` as a `ℂ`-linear map `H²(ℝ³) →ₗ[ℂ] L²(ℝ³)`,
`(Vψ)(x) = (−Z/|x|)·ψ(x)`, well-defined by `coulomb_mul_memLp_H2`. Since
`laplacianPMap.domain = SobolevH2` definitionally, this is already of the type
`laplacianPMap.domain →ₗ[ℂ] l2R3` consumed by Kato–Rellich. -/
noncomputable def coulombPotential (p : CoulombParams) : SobolevH2 (d := 3) →ₗ[ℂ] l2R3 where
  toFun := fun ⟨ψ, hψ⟩ =>
    (coulomb_mul_memLp_H2 p ψ hψ).toLp
      (fun x => (coulombMultiplier p x : ℂ) * (ψ : R3 → ℂ) x)
  map_add' := fun ⟨ψ₁, hψ₁⟩ ⟨ψ₂, hψ₂⟩ => by
    rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
    filter_upwards [Lp.coeFn_add ψ₁ ψ₂] with x hx
    simp only [Pi.add_apply, hx, mul_add]
  map_smul' := fun c ⟨ψ, hψ⟩ => by
    simp only [RingHom.id_apply]
    rw [← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
    filter_upwards [Lp.coeFn_smul c ψ] with x hx
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at hx ⊢
    rw [hx]; ring

/-! ## Symmetry -/

/-- The Coulomb potential is symmetric on `H²`: `⟪Vψ, φ⟫ = ⟪ψ, Vφ⟫`. As `V` is
multiplication by the real-valued `−Z/|x|`, both sides equal `∫ (−Z/|x|)·conj(ψ)·φ`. -/
theorem coulomb_symmetric (p : CoulombParams) :
    ∀ (ψ φ : SobolevH2 (d := 3)),
      ⟪coulombPotential p ψ, (φ : l2R3)⟫_ℂ =
      ⟪(ψ : l2R3), coulombPotential p φ⟫_ℂ := by
  rintro ⟨ψ, hψ⟩ ⟨φ, hφ⟩
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(coulomb_mul_memLp_H2 p ψ hψ).coeFn_toLp,
    (coulomb_mul_memLp_H2 p φ hφ).coeFn_toLp] with x hVψ hVφ
  simp only [coulombPotential, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hVψ, hVφ, RCLike.inner_apply, RCLike.inner_apply, map_mul, ← coulombMultiplier_real]
  ring

/-- Symmetry in the `IsSymmetricOn` shape consumed by Kato–Rellich.
    Pure repackaging: `laplacianPMap.domain` *is* `SobolevH2`. -/
theorem coulomb_isSymmetricOn (p : CoulombParams) :
    IsSymmetricOn laplacianPMap (coulombPotential p) :=
  coulomb_symmetric p

/-! ## Relative boundedness -/

/-- The `L²`-norm of `Vψ` in terms of the Hardy integral: `‖Vψ‖ = Z·√(hardyIntegral ψ)`,
from `‖Vψ‖² = Z²·∫ inverseRSq·‖ψ‖² = Z²·hardyIntegral ψ`. -/
theorem coulomb_norm_eq (p : CoulombParams)
    (ψ : l2R3) (hψ : MemSobolevH2 ψ) :
    ‖(coulombPotential p ⟨ψ, hψ⟩ : l2R3)‖ =
      p.Z * Real.sqrt (hardyIntegral ψ) := by
  have hsq : ‖(coulombPotential p ⟨ψ, hψ⟩ : l2R3)‖ ^ 2 = p.Z ^ 2 * hardyIntegral ψ := by
    rw [norm_sq_eq_integral_norm_sq, hardyIntegral, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [(coulomb_mul_memLp_H2 p ψ hψ).coeFn_toLp] with x hx
    simp only [coulombPotential, LinearMap.coe_mk, AddHom.coe_mk]
    rw [hx, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, coulombMultiplier_sq]
    ring
  rw [← Real.sqrt_sq (norm_nonneg (coulombPotential p ⟨ψ, hψ⟩ : l2R3)), hsq,
    Real.sqrt_mul (sq_nonneg p.Z), Real.sqrt_sq p.hZ.le]

/-- **The Coulomb potential is (−Δ)-bounded with any slope ε > 0.**

    Proved from `coulomb_norm_eq` + Hardy's `hardy_operator_bound`
    applied at ε/Z; only real arithmetic remains. -/
theorem coulomb_relatively_bounded_H2 (p : CoulombParams)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (ψ : l2R3) (hψ : MemSobolevH2 ψ),
      ‖(coulombPotential p ⟨ψ, hψ⟩ : l2R3)‖ ≤
        ε * ‖weakLaplacian ψ hψ‖ + C * ‖ψ‖ := by
  obtain ⟨C, hC₀, hC⟩ := hardy_operator_bound (ε / p.Z) (div_pos hε p.hZ)
  refine ⟨p.Z * C, mul_nonneg p.hZ.le hC₀, fun ψ hψ => ?_⟩
  rw [coulomb_norm_eq p ψ hψ]
  have h := mul_le_mul_of_nonneg_left (hC ψ hψ) p.hZ.le
  refine h.trans (le_of_eq ?_)
  rw [mul_add, ← mul_assoc, ← mul_assoc, ← mul_div_assoc,
    mul_div_cancel_left₀ ε (ne_of_gt p.hZ)]
  -- if the cancellation lemma name differs on your Mathlib:
  -- `field_simp` (with `ne_of_gt p.hZ`) followed by `ring` also closes this

/-- **The relative bound is 0**, in the exact shape `kato_rellich_bound_zero`
    consumes: for every slope a > 0 there is an admissible intercept b. -/
theorem coulomb_relative_bound_is_zero (p : CoulombParams) :
    ∀ a : ℝ, 0 < a →
    ∃ b : ℝ, 0 ≤ b ∧
    ∀ ψ : laplacianPMap.domain,
      ‖coulombPotential p ψ‖ ≤
        a * ‖laplacianPMap ψ‖ + b * ‖(ψ : l2R3)‖ := by
  intro a ha
  obtain ⟨C, hC₀, hC⟩ := coulomb_relatively_bounded_H2 p a ha
  exact ⟨C, hC₀, fun ψ => hC ψ.1 ψ.2⟩

/-- Packaged as `IsRelativelyBounded`, for use with `kato_rellich'`. -/
noncomputable def coulombIsRelativelyBounded (p : CoulombParams) (a : ℝ) (ha : 0 < a) :
    IsRelativelyBounded laplacianPMap (coulombPotential p) where
  a := a
  b := (coulomb_relative_bound_is_zero p a ha).choose
  ha := ha.le
  hb := (coulomb_relative_bound_is_zero p a ha).choose_spec.1
  bound := (coulomb_relative_bound_is_zero p a ha).choose_spec.2

/-! ## Kato–Rellich, applied

The old file ended by *bundling* the hypotheses
(`coulomb_kato_rellich_ready`).  With `KatoRellich.lean` complete, we can
state the conclusions instead.
-/

/-- **Self-adjointness of −Δ + λ·V for every real coupling λ.**

    Relative bound 0 (Hardy) feeds `kato_rellich_bound_zero`; any λ works. -/
theorem coulomb_kato_rellich (p : CoulombParams) (lam : ℝ) :
    IsSelfAdjoint
      (perturbedOp laplacianPMap ((lam : ℂ) • coulombPotential p)) :=
  kato_rellich_bound_zero laplacian_isSelfAdjoint (coulombPotential p)
    (coulomb_isSymmetricOn p) (coulomb_relative_bound_is_zero p) lam

/-! ## The textbook kinetic operator `−½Δ`

Re-threading symmetry, the (zero) relative bound, and Kato–Rellich
self-adjointness against `halfLaplacianPMap = (½ : ℂ) • laplacianPMap`. -/

/-- The Coulomb potential is symmetric on `Dom(−½Δ)` (= `Dom(−Δ)` definitionally). -/
theorem coulomb_isSymmetricOn_half (p : CoulombParams) :
    IsSymmetricOn halfLaplacianPMap (coulombPotential p) :=
  coulomb_isSymmetricOn p

/-- The Coulomb potential is `(−½Δ)`-bounded with relative bound `0`.

    Halving the kinetic operator at most doubles its norm slope; applying the
    `(−Δ)`-bound at `ε/2` and using `‖−½Δψ‖ = ½‖−Δψ‖` recovers slope `ε`. -/
theorem coulomb_relative_bound_is_zero_half (p : CoulombParams) :
    ∀ ε : ℝ, 0 < ε → ∃ b : ℝ, 0 ≤ b ∧
      ∀ ψ : halfLaplacianPMap.domain,
        ‖coulombPotential p ψ‖ ≤ ε * ‖halfLaplacianPMap ψ‖ + b * ‖(ψ : l2R3)‖ := by
  intro ε hε
  obtain ⟨b, hb0, hb⟩ := coulomb_relative_bound_is_zero p (ε / 2) (by positivity)
  refine ⟨b, hb0, fun ψ => ?_⟩
  have hdom : (ψ : l2R3) ∈ laplacianPMap.domain := ψ.2
  have hb' := hb ⟨(ψ : l2R3), hdom⟩
  have hnorm : ‖halfLaplacianPMap ψ‖ = (1 / 2 : ℝ) * ‖laplacianPMap ⟨(ψ : l2R3), hdom⟩‖ := by
    rw [halfLaplacianPMap_apply ψ, norm_smul]
    have hc : ‖((1 / 2 : ℝ) : ℂ)‖ = (1 / 2 : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs]; norm_num
    rw [hc]
    rfl
  rw [hnorm]
  have hVeq : ‖coulombPotential p ψ‖ = ‖coulombPotential p ⟨(ψ : l2R3), hdom⟩‖ := by congr 1
  rw [hVeq]
  calc ‖coulombPotential p ⟨(ψ : l2R3), hdom⟩‖
      ≤ (ε / 2) * ‖laplacianPMap ⟨(ψ : l2R3), hdom⟩‖ + b * ‖(ψ : l2R3)‖ := hb'
    _ = ε * (1 / 2 * ‖laplacianPMap ⟨(ψ : l2R3), hdom⟩‖) + b * ‖(ψ : l2R3)‖ := by ring

/-- **The hydrogen Hamiltonian `H = −½Δ − Z/r` is self-adjoint on `H²(ℝ³)`.**

    (The sign and charge are already inside `coulombMultiplier`; the kinetic term is the
    textbook `−½Δ`.) The `λ = 1` specialisation of `kato_rellich_bound_zero` at
    `halfLaplacianPMap`, re-threaded through `coulomb_isSymmetricOn_half` and
    `coulomb_relative_bound_is_zero_half`. -/
theorem hydrogen_isSelfAdjoint (p : CoulombParams) :
    IsSelfAdjoint (perturbedOp halfLaplacianPMap (coulombPotential p)) := by
  have h := kato_rellich_bound_zero halfLaplacian_isSelfAdjoint (coulombPotential p)
    (coulomb_isSymmetricOn_half p) (coulomb_relative_bound_is_zero_half p) 1
  rwa [Complex.ofReal_one, one_smul] at h

/-! ## Interface summary

### Exports for `HydrogenHamiltonian.lean`:
- `CoulombParams` — nuclear charge Z.
- `coulombPotential p` — V = −Z/r on H² (= on `laplacianPMap.domain`, by `rfl`).
- `hydrogen_isSelfAdjoint p` — H := `perturbedOp halfLaplacianPMap
  (coulombPotential p)` is self-adjoint; `H.domain = SobolevH2` by `rfl`
  (`perturbedOp_domain`).
- Dynamics: `kato_rellich_generates_unitary` (or `genToGroup
  (hydrogen_isSelfAdjoint p)`) gives the unique unitary evolution;
  `spectralPVM (hydrogen_isSelfAdjoint p)` its spectral measure — the
  starting point for the hydrogen spectrum.
-/

end Spectra.QuantumMechanics.Hydrogen
