/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Fock.BoseFermi
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Exponential (coherent) vectors in the bosonic Fock space

The **exponential vector** (coherent vector) of `f : H` in the bosonic Fock space:

`expVec 𝕜 f := (expCoeff n • f^⊗n)ₙ`, with `expCoeff n = (√n!)⁻¹`,

whose defining property is the **exponential formula**

`⟪ε(f), ε(g)⟫ = exp ⟪f, g⟫`  (`inner_expVec_expVec`),

with `exp` the normed-algebra exponential of Mathlib. This is Fock Spaces milestone M3
step 2; exponential vectors are the raw material for the Weyl operators of milestone M5
(Route W) and for total-family/cyclicity arguments.

## Convention: the coefficient is `(√n!)⁻¹`, not `(n!)⁻¹`

The inner product on `symPower 𝕜 n H` is the **restricted** full-tensor-power inner
product (Parthasarathy convention, no `n!` rescaling; see
`Spectra/Spaces/Fock/BoseFermi.lean`), so `⟪f^⊗n, g^⊗n⟫ = ⟪f, g⟫ ^ n` with **no**
factorial weight. Consequently the coefficient that makes the exponential formula come
out right is `(√n!)⁻¹`: the `n`-th term of `⟪ε(f), ε(g)⟫` is then
`(√n!)⁻¹ · (√n!)⁻¹ · ⟪f, g⟫ ^ n = ⟪f, g⟫ ^ n / n!`, which sums to `exp ⟪f, g⟫`. With
`(n!)⁻¹` coefficients one would instead get `∑ ⟪f, g⟫ ^ n / (n!)²`, which is *not* the
exponential. (Earlier project notes said `1/n!`; that applies only to the *weighted*
inner-product convention, which this development does not use.)

## Main definitions

* `Spectra.expCoeff n` — the coefficient `(√n!)⁻¹`.
* `Spectra.expVecSector 𝕜 f n` — the `n`-particle component `(√n!)⁻¹ • f^⊗n ∈ symPower`.
* `Spectra.expVec 𝕜 f` — the exponential vector `ε(f) ∈ boseFock 𝕜 H`.

## Main results

* `inner_expVec_expVec` — ★ the exponential formula `⟪ε(f), ε(g)⟫ = exp ⟪f, g⟫`.
* `norm_expVec_sq` — `‖ε(f)‖² = Real.exp ‖f‖²`; hence `expVec_ne_zero`.
* `exp_ofReal` — bridge `exp ((r : ℝ) : 𝕜) = ((Real.exp r : ℝ) : 𝕜)` on `RCLike` fields.
* `expVec_zero_apply_succ` — `ε(0)` is the vacuum: all components of positive rank vanish.

Linear independence of `f ↦ ε(f)` (the Gram positive-definiteness argument) is deferred
to M5 preparation.
-/

noncomputable section

open scoped Nat ENNReal
open UniformSpace

namespace Spectra

open HilbertTensorPower

/-! ## The exponential coefficients -/

/-- The exponential-vector coefficient `(√n!)⁻¹`. Under the restricted (unweighted)
inner product on `symPower`, this is the normalization for which
`⟪ε(f), ε(g)⟫ = exp ⟪f, g⟫` — see the module docstring. -/
def expCoeff (n : ℕ) : ℝ := (Real.sqrt n !)⁻¹

/-- The exponential-vector coefficients are positive. -/
theorem expCoeff_pos (n : ℕ) : 0 < expCoeff n :=
  inv_pos.mpr <| Real.sqrt_pos.mpr <| Nat.cast_pos.mpr n.factorial_pos

/-- The square of the exponential-vector coefficient is `(n!)⁻¹`. -/
@[simp]
theorem expCoeff_sq (n : ℕ) : expCoeff n ^ 2 = ((n !) : ℝ)⁻¹ := by
  rw [expCoeff, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

/-- The zeroth exponential-vector coefficient is `1`. -/
@[simp]
theorem expCoeff_zero : expCoeff 0 = 1 := by
  rw [expCoeff, Nat.factorial_zero, Nat.cast_one, Real.sqrt_one, inv_one]

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-! ## The exponential bridge on `RCLike` fields -/

variable (𝕜) in
/-- On an `RCLike` field the normed-algebra exponential of a real cast is the cast of the
real exponential: `exp ((r : ℝ) : 𝕜) = ((Real.exp r : ℝ) : 𝕜)`. -/
theorem exp_ofReal (r : ℝ) :
    NormedSpace.exp ((r : ℝ) : 𝕜) = ((Real.exp r : ℝ) : 𝕜) := by
  have h := NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := 𝕜) r
  rw [RCLike.algebraMap_eq_ofReal] at h
  rw [Real.exp_eq_exp_ℝ]
  exact h.symm

/-! ## The sector components -/

variable (𝕜) in
/-- The `n`-particle component of the exponential vector of `f`: the bosonic pure tensor
`(√n!)⁻¹ • f ⊗ ⋯ ⊗ f` in the symmetric sector. Constant families are symmetric
(`tprod_const_mem_symPower`), so this lands in `symPower` with no symmetrization. -/
def expVecSector (f : H) (n : ℕ) : symPower 𝕜 n H :=
  ⟨(expCoeff n : 𝕜) • tprod 𝕜 fun _ : Fin n => f,
    Submodule.smul_mem _ _ (tprod_const_mem_symPower f)⟩

/-- The ambient realization of the exponential-vector sector component. -/
@[simp]
theorem coe_expVecSector (f : H) (n : ℕ) :
    (expVecSector 𝕜 f n : HilbertTensorPower 𝕜 n H)
      = (expCoeff n : 𝕜) • tprod 𝕜 fun _ : Fin n => f := rfl

/-- The norm of the sector component: `‖(√n!)⁻¹ • f^⊗n‖ = (√n!)⁻¹ ‖f‖ ^ n`. -/
theorem norm_expVecSector (f : H) (n : ℕ) :
    ‖expVecSector 𝕜 f n‖ = expCoeff n * ‖f‖ ^ n := by
  rw [Submodule.coe_norm, coe_expVecSector, norm_smul, RCLike.norm_ofReal,
    abs_of_pos (expCoeff_pos n), norm_tprod, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- The sector components pair to `⟪f, g⟫ ^ n / n!` — the `n`-th exponential series term.
This is where the `(√n!)⁻¹` convention pays off: the two coefficients multiply to
`(n!)⁻¹` against the *unweighted* sector inner product `⟪f^⊗n, g^⊗n⟫ = ⟪f, g⟫ ^ n`. -/
theorem inner_expVecSector (f g : H) (n : ℕ) :
    inner 𝕜 (expVecSector 𝕜 f n) (expVecSector 𝕜 g n)
      = inner 𝕜 f g ^ n / ((n !) : 𝕜) := by
  rw [Submodule.coe_inner, coe_expVecSector, coe_expVecSector, inner_smul_left,
    inner_smul_right, RCLike.conj_ofReal, inner_tprod_tprod, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← mul_assoc, ← RCLike.ofReal_mul, ← pow_two,
    expCoeff_sq, RCLike.ofReal_inv, RCLike.ofReal_natCast, inv_mul_eq_div]

variable (𝕜) in
/-- Square-summability of the sector components: `‖(√n!)⁻¹ • f^⊗n‖² = (‖f‖²)ⁿ / n!` is
dominated by the exponential series of `‖f‖²`. -/
theorem summable_norm_expVecSector_sq (f : H) :
    Summable fun n : ℕ => ‖expVecSector 𝕜 f n‖ ^ (2 : ℝ≥0∞).toReal := by
  have key : ∀ n : ℕ, ‖expVecSector 𝕜 f n‖ ^ (2 : ℝ≥0∞).toReal = (‖f‖ ^ 2) ^ n / n ! := by
    intro n
    rw [ENNReal.toReal_ofNat, show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
      Real.rpow_natCast, norm_expVecSector, mul_pow, expCoeff_sq, ← pow_mul,
      mul_comm n 2, pow_mul, inv_mul_eq_div]
  exact (Real.summable_pow_div_factorial (‖f‖ ^ 2)).congr fun n => (key n).symm

variable (𝕜) in
/-- The sector components of an exponential vector are `ℓ²`. -/
theorem memℓp_expVecSector (f : H) : Memℓp (fun n => expVecSector 𝕜 f n) 2 :=
  memℓp_gen (summable_norm_expVecSector_sq 𝕜 f)

/-! ## The exponential vectors -/

variable (𝕜) in
/-- ★ The **exponential (coherent) vector** `ε(f)` of `f : H` in the bosonic Fock space:
the ℓ²-sequence of sector components `(√n!)⁻¹ • f^⊗n`. Its defining property is the
exponential formula `⟪ε(f), ε(g)⟫ = exp ⟪f, g⟫` (`inner_expVec_expVec`). -/
def expVec (f : H) : boseFock 𝕜 H :=
  ⟨fun n => expVecSector 𝕜 f n, memℓp_expVecSector 𝕜 f⟩

/-- The `n`-th component of the exponential vector is the sector component. -/
@[simp]
theorem expVec_apply (f : H) (n : ℕ) : expVec 𝕜 f n = expVecSector 𝕜 f n := rfl

/-- ★★ **The exponential formula**: exponential vectors pair to the exponential of the
one-particle inner product, `⟪ε(f), ε(g)⟫ = exp ⟪f, g⟫`. This identity drives all of
coherent-state analysis: totality, Weyl-operator matrix elements, and the CCR. -/
theorem inner_expVec_expVec (f g : H) :
    inner 𝕜 (expVec 𝕜 f) (expVec 𝕜 g) = NormedSpace.exp (inner 𝕜 f g) := by
  have hexp : NormedSpace.exp (inner 𝕜 f g)
      = ∑' n : ℕ, inner 𝕜 f g ^ n / ((n !) : 𝕜) := by
    rw [NormedSpace.exp_eq_tsum_div]
  rw [hexp, lp.inner_eq_tsum]
  exact tsum_congr fun n => by rw [expVec_apply, expVec_apply, inner_expVecSector]

/-- ★ The squared norm of an exponential vector: `‖ε(f)‖² = exp ‖f‖²`. -/
theorem norm_expVec_sq (f : H) :
    ‖expVec 𝕜 f‖ ^ 2 = Real.exp (‖f‖ ^ 2) := by
  have h := inner_expVec_expVec (𝕜 := 𝕜) f f
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
    ← RCLike.ofReal_pow, exp_ofReal] at h
  exact_mod_cast h

/-- Exponential vectors are nonzero: `‖ε(f)‖² = exp ‖f‖² > 0`. -/
theorem expVec_ne_zero (f : H) : expVec 𝕜 f ≠ 0 := by
  intro h0
  have h := norm_expVec_sq (𝕜 := 𝕜) f
  rw [h0, norm_zero, zero_pow two_ne_zero] at h
  exact (Real.exp_pos _).ne' h.symm

/-! ## The vacuum: `ε(0)` -/

/-- The rank-`0` component of `ε(0)` is the (unit-coefficient) sector component. -/
theorem expVec_zero_apply_zero : expVec 𝕜 (0 : H) 0 = expVecSector 𝕜 0 0 := rfl

/-- `ε(0)` is the vacuum: every component of positive rank vanishes, since a pure tensor
with a zero slot is zero. -/
theorem expVec_zero_apply_succ (n : ℕ) : expVec 𝕜 (0 : H) (n + 1) = 0 := by
  have htp : tprod 𝕜 (fun _ : Fin (n + 1) => (0 : H)) = 0 := by
    rw [HilbertTensorPower.tprod_def,
      (PiTensorProduct.tprod 𝕜).map_coord_zero (m := fun _ : Fin (n + 1) => (0 : H))
        (0 : Fin (n + 1)) rfl,
      Completion.coe_zero]
  rw [expVec_apply]
  apply Subtype.ext
  simp only [coe_expVecSector, htp, smul_zero, ZeroMemClass.coe_zero]

end Spectra
