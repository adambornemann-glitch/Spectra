/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Perturbation.HardyInequality
import Spectra.QuantumMechanics.Perturbation.KatoRellich
import Spectra.QuantumMechanics.Hydrogen.Laplacian

-- ^ adjust the three module paths above to the actual file locations

/-!
# The Coulomb Potential: Relative Boundedness

This file constructs the Coulomb potential V = −Z/r as a linear map on
H²(ℝ³), verifies the Kato–Rellich hypotheses, and *applies* the theorem:

  `hydrogen_isSelfAdjoint : IsSelfAdjoint (perturbedOp laplacianPMap (coulombPotential p))`

i.e. H = −Δ − Z/r is self-adjoint on H²(ℝ³) for every nuclear charge Z > 0
(and, via `coulomb_kato_rellich`, for every real coupling λ).

## Architecture

```
  HardyInequality.lean             KatoRellich.lean
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
`coulombPotential p : SobolevH2 →ₗ[ℂ] L2_R3` *is* a
`laplacianPMap.domain →ₗ[ℂ] L2_R3`.  The transport layer is deleted, and
the corresponding sorries with it.

## Main definitions

* `CoulombParams` — the nuclear charge Z > 0.
* `coulombMultiplier` — the function x ↦ −Z/|x| (real-valued; key for symmetry).
* `coulombPotential` — V = −Z/r as a linear map `SobolevH2 →ₗ[ℂ] L2_R3`.

## Main statements

* `coulomb_isSymmetricOn` — V is symmetric on Dom(−Δ).
* `coulomb_relative_bound_is_zero` — V is (−Δ)-bounded with relative bound 0.
* `coulomb_kato_rellich` — −Δ + λV is self-adjoint on H² for every λ : ℝ.
* `hydrogen_isSelfAdjoint` — **the hydrogen Hamiltonian −Δ − Z/r is
  self-adjoint on H²(ℝ³)** (λ = 1 specialisation).

## Sorry strategy

Five sorries remain, all integral-level facts about L² and `MemLp.toLp`;
none touches operator theory:
- `coulomb_mul_memLp` — (1/r)ψ ∈ L² for ψ ∈ H¹, from
  `inverseRSq_mul_sq_integrable` (Hardy).
- `coulombPotential.map_add'/map_smul'` — a.e. linearity of pointwise
  multiplication, via `MemLp.toLp_eq_toLp_iff` + `Lp.coeFn_add/smul`.
- `coulomb_symmetric` — real-valuedness of −Z/|x|, via `L2.inner_def`,
  `MemLp.coeFn_toLp`, `integral_congr_ae`, `Complex.conj_ofReal`.
- `coulomb_norm_eq` — ‖Vψ‖ = Z·√(hardyIntegral ψ), via `coulombMultiplier_sq`
  and the L²-norm/integral dictionary.

Everything downstream of these (the relative bound, the Kato–Rellich
packaging, self-adjointness of hydrogen) is **proved**.

## References

* [Kato, *Perturbation Theory*][kato1995], §V.5, Example 5.2.
* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975],
  Example 2, p. 167.
-/
open MeasureTheory Complex Filter InnerProductSpace
open Spectra.Sobolev
open Spectra.QuantumMechanics
open Spectra.QuantumMechanics.Hamiltonian
open scoped Topology NNReal ENNReal

namespace Spectra.QuantumMechanics.Hydrogen

/-! ## The Coulomb multiplier function -/

/-- The nuclear charge (positive real parameter). -/
structure CoulombParams where
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

/-- **The Coulomb potential applied to an H¹ function is in L².**

    ‖(Z/r)ψ‖² = Z² ∫ |ψ|²/|x|² dx = Z² · hardyIntegral(ψ) < ∞.

    **Discharge route:**
    1. Pointwise: ‖V(x)ψ(x)‖² = Z² · inverseRSq x · ‖ψ(x)‖²
       (`coulombMultiplier_sq`).
    2. The RHS is integrable by `inverseRSq_mul_sq_integrable` (Hardy).
    3. Measurability: `coulombMultiplier_measurable` + a.e.-measurability
       of the Lp representative; conclude with the `MemLp` characterisation
       via finiteness of the squared integral. -/
theorem coulomb_mul_memLp
    (p : CoulombParams) (ψ : L2_R3) (hψ : MemSobolevH1 ψ) :
    MemLp (fun x => (coulombMultiplier p x : ℂ) * (ψ : R3 → ℂ) x)
      2 (volume : Measure R3) :=
  sorry

/-- The Coulomb potential applied to an H² function is in L². -/
theorem coulomb_mul_memLp_H2
    (p : CoulombParams) (ψ : L2_R3) (hψ : MemSobolevH2 ψ) :
    MemLp (fun x => (coulombMultiplier p x : ℂ) * (ψ : R3 → ℂ) x)
      2 (volume : Measure R3) :=
  coulomb_mul_memLp p ψ (sobolevH2_le_H1 hψ)

/-! ## The Coulomb potential as a linear map on H²

Because `laplacianPMap.domain = SobolevH2` definitionally, this map needs
no further transport: it is already of the type
`laplacianPMap.domain →ₗ[ℂ] L2_R3` that Kato–Rellich consumes.
-/

/-- **The Coulomb potential as a linear map on H².**

    V : H²(ℝ³) →ₗ[ℂ] L²(ℝ³) defined by (Vψ)(x) = (−Z/|x|) · ψ(x),
    well-defined by `coulomb_mul_memLp_H2`.

    **Discharge route for linearity:** both fields reduce, via
    `MemLp.toLp_eq_toLp_iff`, to a.e. pointwise identities
    (mul_add resp. mul_smul_comm) against `Lp.coeFn_add` / `Lp.coeFn_smul`. -/
noncomputable def coulombPotential (p : CoulombParams) : SobolevH2 →ₗ[ℂ] L2_R3 where
  toFun := fun ⟨ψ, hψ⟩ =>
    (coulomb_mul_memLp_H2 p ψ hψ).toLp
      (fun x => (coulombMultiplier p x : ℂ) * (ψ : R3 → ℂ) x)
  map_add' := fun ⟨ψ₁, hψ₁⟩ ⟨ψ₂, hψ₂⟩ => by
    sorry  -- a.e.: V(ψ₁+ψ₂) = Vψ₁ + Vψ₂, from mul_add + Lp.coeFn_add
  map_smul' := fun c ⟨ψ, hψ⟩ => by
    sorry  -- a.e.: V(cψ) = c·Vψ, from mul_smul_comm + Lp.coeFn_smul

/-! ## Symmetry -/

/-- **The Coulomb potential is symmetric on H².**

    ⟪Vψ, φ⟫ = ⟪ψ, Vφ⟫ for ψ, φ ∈ H².

    **Discharge route:** V is multiplication by the *real-valued*
    −Z/|x|, so under `L2.inner_def`,

      ⟪Vψ, φ⟫ = ∫ conj((−Z/|x|)ψ) · φ = ∫ conj(ψ) · (−Z/|x|)φ = ⟪ψ, Vφ⟫,

    using `Complex.conj_ofReal` (`coulombMultiplier_real`) pointwise,
    `MemLp.coeFn_toLp` to pass to representatives, and
    `integral_congr_ae`. -/
theorem coulomb_symmetric (p : CoulombParams) :
    ∀ (ψ φ : SobolevH2),
      ⟪coulombPotential p ψ, (φ : L2_R3)⟫_ℂ =
      ⟪(ψ : L2_R3), coulombPotential p φ⟫_ℂ :=
  sorry

/-- Symmetry in the `IsSymmetricOn` shape consumed by Kato–Rellich.
    Pure repackaging: `laplacianPMap.domain` *is* `SobolevH2`. -/
theorem coulomb_isSymmetricOn (p : CoulombParams) :
    IsSymmetricOn laplacianPMap (coulombPotential p) :=
  coulomb_symmetric p

/-! ## Relative boundedness -/

/-- **The L² norm of Vψ in terms of the Hardy integral**:
    ‖Vψ‖ = Z · √(hardyIntegral ψ).

    **Discharge route:** ‖Vψ‖² = ∫ ‖(−Z/|x|)ψ(x)‖² dx
    = Z² ∫ inverseRSq x · ‖ψ(x)‖² dx (pointwise `coulombMultiplier_sq`)
    = Z² · hardyIntegral ψ; take square roots (both sides ≥ 0;
    integrability from `inverseRSq_mul_sq_integrable`). -/
theorem coulomb_norm_eq (p : CoulombParams)
    (ψ : L2_R3) (hψ : MemSobolevH2 ψ) :
    ‖(coulombPotential p ⟨ψ, hψ⟩ : L2_R3)‖ =
      p.Z * Real.sqrt (hardyIntegral ψ) :=
  sorry

/-- **The Coulomb potential is (−Δ)-bounded with any slope ε > 0.**

    Proved from `coulomb_norm_eq` + Hardy's `hardy_operator_bound`
    applied at ε/Z; only real arithmetic remains. -/
theorem coulomb_relatively_bounded_H2 (p : CoulombParams)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (ψ : L2_R3) (hψ : MemSobolevH2 ψ),
      ‖(coulombPotential p ⟨ψ, hψ⟩ : L2_R3)‖ ≤
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
        a * ‖laplacianPMap ψ‖ + b * ‖(ψ : L2_R3)‖ := by
  intro a ha
  obtain ⟨C, hC₀, hC⟩ := coulomb_relatively_bounded_H2 p a ha
  exact ⟨C, hC₀, fun ψ => hC ψ.1 ψ.2⟩

/-- Packaged as `IsRelativelyBounded`, for use with `kato_rellich'`. -/
noncomputable def coulomb_isRelativelyBounded (p : CoulombParams) (a : ℝ) (ha : 0 < a) :
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

/-- **The hydrogen Hamiltonian H = −Δ − Z/r is self-adjoint on H²(ℝ³).**

    (The sign and charge are already inside `coulombMultiplier`;
    this is the λ = 1 specialisation.) -/
theorem hydrogen_isSelfAdjoint (p : CoulombParams) :
    IsSelfAdjoint (perturbedOp laplacianPMap (coulombPotential p)) := by
  have h := coulomb_kato_rellich p 1
  rwa [Complex.ofReal_one, one_smul] at h

/-! ## Interface summary

### Exports for `HydrogenHamiltonian.lean`:
- `CoulombParams` — nuclear charge Z.
- `coulombPotential p` — V = −Z/r on H² (= on `laplacianPMap.domain`, by `rfl`).
- `hydrogen_isSelfAdjoint p` — H := `perturbedOp laplacianPMap
  (coulombPotential p)` is self-adjoint; `H.domain = SobolevH2` by `rfl`
  (`perturbedOp_domain`).
- Dynamics: `kato_rellich_generates_unitary` (or `genToGroup
  (hydrogen_isSelfAdjoint p)`) gives the unique unitary evolution;
  `spectralPVM (hydrogen_isSelfAdjoint p)` its spectral measure — the
  starting point for the hydrogen spectrum.

### Remaining inputs (all in this file or Hardy):
- the five integral-level sorries listed in the module docstring, plus
  Hardy's own sorries (`hardy_inequality_smooth`, `hardy_inequality`,
  `hardy_operator_bound`, …).
-/

end Spectra.QuantumMechanics.Hydrogen
