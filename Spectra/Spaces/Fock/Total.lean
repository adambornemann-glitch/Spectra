/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Fock.Exponential
import Spectra.Spaces.Fock.Sector
import Spectra.Spaces.Fock.Polarization

/-!
# Totality of exponential vectors in the bosonic Fock space

★★★ **The M3 keystone**: the exponential (coherent) vectors of
`Spectra/Spaces/Fock/Exponential.lean` are **total** in the bosonic Fock space —

`expVec_total : (span 𝕜 (range (expVec 𝕜))).topologicalClosure = ⊤`.

This single theorem carries the Weyl operators of milestone M5 (defined on exponential
vectors and extended by density) and the second quantization functors `Γ`/`dΓ` of M6.

## Proof strategy

Write `M := expVecSpan 𝕜 H` for the closed span of the exponential vectors.

1. **Scaling** (`expVecSector_smul`): `ε(c • f)ₙ = cⁿ • ε(f)ₙ` — multilinearity of the
   tensor power.
2. **Tail estimate** (`norm_expVec_smul_sub_boseHead_sq_le`): the `lp` tail-norm formula
   gives `‖ε(c•f) − head_N(ε(c•f))‖² ≤ ‖c‖^{2N} · exp ‖f‖²` for `‖c‖ ≤ 1`.
3. **Sector extraction** (`boseSector_expVecSector_mem`): by strong induction on `n`, the
   embedded sector component `ε(f)ₙ` lies in `M`: subtract the (inductively known) head
   from `ε(c•f)`, rescale by `c⁻ⁿ`, and let `c = 1/(m+1) → 0` (`expVecApprox`); the tail
   estimate shows the error is `O(c)`, and `M` is closed.
4. **Single powers** (`boseSector_tprod_const_mem`): divide by the coefficient `(√n!)⁻¹`.
5. **Whole sectors** (`boseSector_mem_expVecSpan`): the polarization identity
   (`topologicalClosure_span_tprod_const`) writes the bosonic sector as the closed span
   of single powers; transport along the continuous map `symProjSector = boseSector n ∘
   symProj` — its preimage of any closed submodule containing all powers is a closed
   submodule of the ambient power containing all powers
   (`boseSector_mem_of_forall_tprod_const`).
6. **Assembly** (`expVecSpan_eq_top`, `expVec_total`): every sector range lies in `M`,
   so the dense finite-particle core does; hence `M = ⊤`.

## Main results

* `Spectra.expVecSector_smul` — scaling covariance of the exponential sectors.
* `Spectra.boseHead` / `norm_sub_boseHead_sq` — sector heads and the exact tail norm.
* `Spectra.expVecSpan` — the closed span of the exponential vectors.
* `Spectra.boseSector_expVecSector_mem` — ★ sector components of exponential vectors lie
  in the closed span of the exponential vectors.
* `Spectra.boseSector_mem_of_forall_tprod_const` — ★ generic sector-transport lemma for
  closed submodules (reusable for the Weyl-operator development of M5).
* `Spectra.expVec_total` — ★★★ the closed span of the exponential vectors is everything.
* `Spectra.dense_span_expVec` — the span of the exponential vectors is dense.
-/

noncomputable section

open scoped ENNReal TensorProduct Topology
open Filter UniformSpace

namespace Spectra

open HilbertTensorPower

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Bridge between the `lp`-norm exponent `(2 : ℝ≥0∞).toReal` (a real power) and the
natural power `x ^ 2`. -/
private theorem rpow_toReal_two (x : ℝ) : x ^ (2 : ℝ≥0∞).toReal = x ^ 2 := by
  rw [ENNReal.toReal_ofNat, show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
    Real.rpow_natCast]

/-- From `0 ≤ x` and `x² ≤ y` conclude `x ≤ √y`. -/
private theorem le_sqrt_of_sq_le {x y : ℝ} (hx : 0 ≤ x) (h : x ^ 2 ≤ y) :
    x ≤ Real.sqrt y :=
  calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx).symm
    _ ≤ Real.sqrt y := Real.sqrt_le_sqrt h

/-! ## Scaling covariance -/

namespace HilbertTensorPower

/-- Scaling the vector scales the constant pure tensor by the `n`-th power of the scalar:
`(c•f) ⊗ ⋯ ⊗ (c•f) = cⁿ • (f ⊗ ⋯ ⊗ f)`, by multilinearity. -/
theorem tprod_const_smul (c : 𝕜) (f : H) (n : ℕ) :
    tprod 𝕜 (fun _ : Fin n => c • f) = c ^ n • tprod 𝕜 (fun _ : Fin n => f) := by
  have h : (PiTensorProduct.tprod 𝕜 fun _ : Fin n => c • f)
      = c ^ n • (PiTensorProduct.tprod 𝕜 fun _ : Fin n => f : ⨂[𝕜]^n H) := by
    have hm := (PiTensorProduct.tprod 𝕜 (s := fun _ : Fin n => H)).map_smul_univ
      (fun _ => c) fun _ => f
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hm
  rw [tprod_def, tprod_def, h, Completion.coe_smul]

end HilbertTensorPower

/-- ★ **Scaling covariance of the exponential sectors**: the `n`-particle component of
`ε(c • f)` is `cⁿ` times that of `ε(f)`. This is the engine of the totality proof: it
lets the scaling parameter separate the sectors. -/
theorem expVecSector_smul (c : 𝕜) (f : H) (n : ℕ) :
    expVecSector 𝕜 (c • f) n = c ^ n • expVecSector 𝕜 f n := by
  apply Subtype.ext
  rw [Submodule.coe_smul, coe_expVecSector, coe_expVecSector, tprod_const_smul, smul_comm]

/-! ## Sector heads and the tail norm -/

/-- The `N`-sector **head** of a bosonic Fock vector: the sum of its first `N` sector
components (`k < N`), re-embedded via `boseSector`. -/
def boseHead (N : ℕ) (g : boseFock 𝕜 H) : boseFock 𝕜 H :=
  ∑ k ∈ Finset.range N, boseSector 𝕜 H k (g k)

/-- The head is the partial sum of the `lp.single`s of the components. -/
theorem boseHead_eq_sum_single (N : ℕ) (g : boseFock 𝕜 H) :
    boseHead N g = ∑ k ∈ Finset.range N, lp.single 2 k (g k) := rfl

/-- **Exact tail norm**: the squared distance from a bosonic Fock vector to its
`N`-sector head is the tail sum of its squared component norms. -/
theorem norm_sub_boseHead_sq (g : boseFock 𝕜 H) (N : ℕ) :
    ‖g - boseHead N g‖ ^ 2 = ∑' k, ‖g (k + N)‖ ^ 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hsum : Summable fun k => ‖g k‖ ^ (2 : ℝ≥0∞).toReal := (lp.memℓp g).summable hp
  have hsplit := hsum.sum_add_tsum_nat_add N
  have hcompl := lp.norm_compl_sum_single
    (E := fun k => ↥(symPower 𝕜 k H)) hp g (Finset.range N)
  have hfull := lp.norm_rpow_eq_tsum (E := fun k => ↥(symPower 𝕜 k H)) hp g
  calc ‖g - boseHead N g‖ ^ 2
      = ‖g - ∑ k ∈ Finset.range N, lp.single 2 k (g k)‖ ^ (2 : ℝ≥0∞).toReal := by
        rw [rpow_toReal_two, boseHead_eq_sum_single]
    _ = ‖g‖ ^ (2 : ℝ≥0∞).toReal
          - ∑ k ∈ Finset.range N, ‖g k‖ ^ (2 : ℝ≥0∞).toReal := hcompl
    _ = ∑' k, ‖g (k + N)‖ ^ (2 : ℝ≥0∞).toReal := by rw [hfull]; linarith [hsplit]
    _ = ∑' k, ‖g (k + N)‖ ^ 2 := tsum_congr fun k => rpow_toReal_two _

variable (𝕜) in
/-- The tail norm of an exponential vector, in terms of its sector components. -/
theorem norm_expVec_sub_boseHead_sq (f : H) (N : ℕ) :
    ‖expVec 𝕜 f - boseHead N (expVec 𝕜 f)‖ ^ 2
      = ∑' k, ‖expVecSector 𝕜 f (k + N)‖ ^ 2 :=
  (norm_sub_boseHead_sq (expVec 𝕜 f) N).trans
    (tsum_congr fun k => by rw [expVec_apply])

variable (𝕜) in
/-- The sector components of an exponential vector are square-summable (natural-power
form of `summable_norm_expVecSector_sq`). -/
theorem summable_norm_sq_expVecSector (f : H) :
    Summable fun n => ‖expVecSector 𝕜 f n‖ ^ 2 :=
  (summable_norm_expVecSector_sq 𝕜 f).congr fun n =>
    rpow_toReal_two ‖expVecSector 𝕜 f n‖

variable (𝕜) in
/-- The full sum of the squared sector norms of an exponential vector is `exp ‖f‖²`. -/
theorem tsum_norm_expVecSector_sq (f : H) :
    ∑' n, ‖expVecSector 𝕜 f n‖ ^ 2 = Real.exp (‖f‖ ^ 2) := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have h := lp.norm_rpow_eq_tsum (E := fun k => ↥(symPower 𝕜 k H)) hp (expVec 𝕜 f)
  rw [rpow_toReal_two, norm_expVec_sq] at h
  rw [h]
  exact tsum_congr fun n => (rpow_toReal_two _).symm

/-- **Tail estimate for scaled exponential vectors**: for `‖c‖ ≤ 1`,

`‖ε(c•f) − head_N(ε(c•f))‖² ≤ ‖c‖^{2N} · exp ‖f‖²`,

since the `k`-th tail component carries `‖c‖^{2k} ≤ ‖c‖^{2N}`. -/
theorem norm_expVec_smul_sub_boseHead_sq_le (f : H) {c : 𝕜} (hc : ‖c‖ ≤ 1) (N : ℕ) :
    ‖expVec 𝕜 (c • f) - boseHead N (expVec 𝕜 (c • f))‖ ^ 2
      ≤ ‖c‖ ^ (2 * N) * Real.exp (‖f‖ ^ 2) := by
  have hcomp : ∀ m : ℕ, ‖expVecSector 𝕜 (c • f) m‖ ^ 2
      = ‖c‖ ^ (2 * m) * ‖expVecSector 𝕜 f m‖ ^ 2 := fun m => by
    rw [expVecSector_smul, norm_smul, mul_pow, norm_pow, ← pow_mul, mul_comm m 2]
  have hshift : Summable fun k => ‖expVecSector 𝕜 f (k + N)‖ ^ 2 :=
    (summable_nat_add_iff (f := fun m => ‖expVecSector 𝕜 f m‖ ^ 2) N).mpr
      (summable_norm_sq_expVecSector 𝕜 f)
  have hsum1 : Summable fun k => ‖c‖ ^ (2 * (k + N)) * ‖expVecSector 𝕜 f (k + N)‖ ^ 2 :=
    ((summable_nat_add_iff (f := fun m => ‖expVecSector 𝕜 (c • f) m‖ ^ 2) N).mpr
        (summable_norm_sq_expVecSector 𝕜 (c • f))).congr
      fun k => hcomp (k + N)
  have hbound : ∀ k : ℕ, ‖c‖ ^ (2 * (k + N)) * ‖expVecSector 𝕜 f (k + N)‖ ^ 2
      ≤ ‖c‖ ^ (2 * N) * ‖expVecSector 𝕜 f (k + N)‖ ^ 2 := fun k =>
    mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one (norm_nonneg c) hc (by omega)) (sq_nonneg _)
  have htail : ∑' k, ‖expVecSector 𝕜 f (k + N)‖ ^ 2 ≤ Real.exp (‖f‖ ^ 2) := by
    have hsplit := (summable_norm_sq_expVecSector 𝕜 f).sum_add_tsum_nat_add N
    rw [tsum_norm_expVecSector_sq] at hsplit
    have hhead : (0 : ℝ) ≤ ∑ k ∈ Finset.range N, ‖expVecSector 𝕜 f k‖ ^ 2 :=
      Finset.sum_nonneg fun k _ => sq_nonneg _
    linarith
  rw [norm_expVec_sub_boseHead_sq]
  have e1 : (∑' k, ‖expVecSector 𝕜 (c • f) (k + N)‖ ^ 2)
      = ∑' k, ‖c‖ ^ (2 * (k + N)) * ‖expVecSector 𝕜 f (k + N)‖ ^ 2 :=
    tsum_congr fun k => hcomp (k + N)
  have le2 : (∑' k, ‖c‖ ^ (2 * (k + N)) * ‖expVecSector 𝕜 f (k + N)‖ ^ 2)
      ≤ ∑' k, ‖c‖ ^ (2 * N) * ‖expVecSector 𝕜 f (k + N)‖ ^ 2 :=
    Summable.tsum_le_tsum hbound hsum1 (hshift.mul_left (‖c‖ ^ (2 * N)))
  have e3 : (∑' k, ‖c‖ ^ (2 * N) * ‖expVecSector 𝕜 f (k + N)‖ ^ 2)
      = ‖c‖ ^ (2 * N) * ∑' k, ‖expVecSector 𝕜 f (k + N)‖ ^ 2 := tsum_mul_left
  have le4 : ‖c‖ ^ (2 * N) * (∑' k, ‖expVecSector 𝕜 f (k + N)‖ ^ 2)
      ≤ ‖c‖ ^ (2 * N) * Real.exp (‖f‖ ^ 2) :=
    mul_le_mul_of_nonneg_left htail (pow_nonneg (norm_nonneg c) _)
  exact e1.trans_le (le2.trans (e3.trans_le le4))

/-! ## The rescaled difference and its distance to the sector component -/

/-- The head of a scaled exponential vector is the `c`-weighted sum of the embedded
sector components of the unscaled one. -/
theorem boseHead_expVec_smul (f : H) (c : 𝕜) (n : ℕ) :
    boseHead n (expVec 𝕜 (c • f))
      = ∑ k ∈ Finset.range n, c ^ k • boseSector 𝕜 H k (expVecSector 𝕜 f k) :=
  Finset.sum_congr rfl fun k _ => by rw [expVec_apply, expVecSector_smul, map_smul]

/-- Abstract rearrangement in a module: for reciprocal scalars `u * v = 1`,
`u • (E − (B + v • T)) = u • (E − B) − T`. Kept abstract so the rewrite in
`smul_expVec_sub_boseHead_sub_boseSector` matches cheaply. -/
private theorem rearrange_aux {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    {u v : 𝕜} (huv : u * v = 1) (E B T : V) :
    u • (E - (B + v • T)) = u • (E - B) - T := by
  rw [sub_add_eq_sub_sub, smul_sub u (E - B) (v • T), smul_smul, huv, one_smul]

/-- **Key rearrangement**: subtracting the target sector vector from the rescaled
truncated exponential vector leaves exactly the rescaled tail beyond `n`. -/
theorem smul_expVec_sub_boseHead_sub_boseSector (f : H) {c : 𝕜} (hc : c ≠ 0) (n : ℕ) :
    c⁻¹ ^ n • (expVec 𝕜 (c • f) - boseHead n (expVec 𝕜 (c • f)))
        - boseSector 𝕜 H n (expVecSector 𝕜 f n)
      = c⁻¹ ^ n • (expVec 𝕜 (c • f) - boseHead (n + 1) (expVec 𝕜 (c • f))) := by
  have hhead : boseHead (n + 1) (expVec 𝕜 (c • f))
      = boseHead n (expVec 𝕜 (c • f))
          + c ^ n • boseSector 𝕜 H n (expVecSector 𝕜 f n) := by
    have h1 : boseHead (n + 1) (expVec 𝕜 (c • f))
        = boseHead n (expVec 𝕜 (c • f))
            + boseSector 𝕜 H n (expVec 𝕜 (c • f) n) :=
      Finset.sum_range_succ _ n
    rw [h1, expVec_apply, expVecSector_smul, map_smul]
  have hcc : c⁻¹ ^ n * c ^ n = (1 : 𝕜) := by
    rw [← mul_pow, inv_mul_cancel₀ hc, one_pow]
  rw [hhead, rearrange_aux hcc]

/-- **Distance estimate**: for `c ≠ 0` with `‖c‖ ≤ 1`, the rescaled truncated exponential
vector is within `‖c‖ · √(exp ‖f‖²)` of the embedded sector component. -/
theorem norm_smul_expVec_sub_boseHead_sub_le (f : H) {c : 𝕜} (hc : c ≠ 0)
    (hc1 : ‖c‖ ≤ 1) (n : ℕ) :
    ‖c⁻¹ ^ n • (expVec 𝕜 (c • f) - boseHead n (expVec 𝕜 (c • f)))
        - boseSector 𝕜 H n (expVecSector 𝕜 f n)‖
      ≤ ‖c‖ * Real.sqrt (Real.exp (‖f‖ ^ 2)) := by
  have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hsq : ‖c⁻¹ ^ n • (expVec 𝕜 (c • f) - boseHead n (expVec 𝕜 (c • f)))
        - boseSector 𝕜 H n (expVecSector 𝕜 f n)‖ ^ 2
      ≤ ‖c‖ ^ 2 * Real.exp (‖f‖ ^ 2) := by
    rw [smul_expVec_sub_boseHead_sub_boseSector f hc n, norm_smul, mul_pow, norm_pow,
      norm_inv]
    have htail := norm_expVec_smul_sub_boseHead_sq_le f hc1 (n + 1)
    have hpow : (‖c‖⁻¹ ^ n) ^ 2 * (‖c‖ ^ (2 * (n + 1)) * Real.exp (‖f‖ ^ 2))
        = ‖c‖ ^ 2 * Real.exp (‖f‖ ^ 2) := by
      rw [← pow_mul, show 2 * (n + 1) = n * 2 + 2 from by ring, pow_add, ← mul_assoc,
        ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hcn, one_pow, one_mul]
    calc (‖c‖⁻¹ ^ n) ^ 2
          * ‖expVec 𝕜 (c • f) - boseHead (n + 1) (expVec 𝕜 (c • f))‖ ^ 2
        ≤ (‖c‖⁻¹ ^ n) ^ 2 * (‖c‖ ^ (2 * (n + 1)) * Real.exp (‖f‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left htail (by positivity)
      _ = ‖c‖ ^ 2 * Real.exp (‖f‖ ^ 2) := hpow
  have h1 := le_sqrt_of_sq_le (norm_nonneg _) hsq
  rwa [Real.sqrt_mul (sq_nonneg _) _, Real.sqrt_sq (norm_nonneg _)] at h1

/-! ## The approximating sequence -/

variable (𝕜) in
/-- The reciprocal scalar sequence `1/(m+1)`, cast into `𝕜`: the scaling parameters sent
to `0` in the sector-extraction argument. -/
def invNatSucc (m : ℕ) : 𝕜 := ((((m : ℝ) + 1)⁻¹ : ℝ) : 𝕜)

variable (𝕜) in
/-- The norm of the reciprocal scalar sequence. -/
theorem norm_invNatSucc (m : ℕ) : ‖invNatSucc 𝕜 m‖ = ((m : ℝ) + 1)⁻¹ := by
  unfold invNatSucc
  rw [RCLike.norm_ofReal, abs_of_pos (by positivity)]

variable (𝕜) in
/-- The reciprocal scalars are nonzero. -/
theorem invNatSucc_ne_zero (m : ℕ) : invNatSucc 𝕜 m ≠ 0 :=
  RCLike.ofReal_ne_zero.mpr (by positivity)

variable (𝕜) in
/-- The reciprocal scalars have norm at most `1`. -/
theorem norm_invNatSucc_le_one (m : ℕ) : ‖invNatSucc 𝕜 m‖ ≤ 1 := by
  rw [norm_invNatSucc]
  exact inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg m))

variable (𝕜) in
/-- The `m`-th **approximant** of the embedded `n`-th sector component of `ε(f)`: the
rescaled, head-truncated exponential vector at scaling parameter `1/(m+1)`. -/
def expVecApprox (f : H) (n m : ℕ) : boseFock 𝕜 H :=
  (invNatSucc 𝕜 m)⁻¹ ^ n
    • (expVec 𝕜 (invNatSucc 𝕜 m • f) - boseHead n (expVec 𝕜 (invNatSucc 𝕜 m • f)))

variable (𝕜) in
/-- The `m`-th approximant is within `(m+1)⁻¹ · √(exp ‖f‖²)` of the embedded sector
component. -/
theorem norm_expVecApprox_sub_le (f : H) (n m : ℕ) :
    ‖expVecApprox 𝕜 f n m - boseSector 𝕜 H n (expVecSector 𝕜 f n)‖
      ≤ ((m : ℝ) + 1)⁻¹ * Real.sqrt (Real.exp (‖f‖ ^ 2)) := by
  unfold expVecApprox
  have h := norm_smul_expVec_sub_boseHead_sub_le f (invNatSucc_ne_zero 𝕜 m)
    (norm_invNatSucc_le_one 𝕜 m) n
  rwa [norm_invNatSucc] at h

variable (𝕜) in
/-- ★ The approximants converge to the embedded sector component. -/
theorem tendsto_expVecApprox (f : H) (n : ℕ) :
    Tendsto (expVecApprox 𝕜 f n) atTop
      (𝓝 (boseSector 𝕜 H n (expVecSector 𝕜 f n))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hg : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹ * Real.sqrt (Real.exp (‖f‖ ^ 2)))
      atTop (𝓝 (0 : ℝ)) := by
    have h0 : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
      simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using h0.mul_const (Real.sqrt (Real.exp (‖f‖ ^ 2)))
  exact squeeze_zero (fun m => norm_nonneg _)
    (fun m => norm_expVecApprox_sub_le 𝕜 f n m) hg

/-! ## The closed span of the exponential vectors -/

variable (𝕜 H) in
/-- The **closed span** of the exponential vectors — the target of the totality theorem
(`expVec_total` proves it is `⊤`). -/
def expVecSpan : Submodule 𝕜 (boseFock 𝕜 H) :=
  (Submodule.span 𝕜 (Set.range (expVec 𝕜 : H → boseFock 𝕜 H))).topologicalClosure

variable (𝕜 H) in
/-- The closed span of the exponential vectors is closed. -/
theorem isClosed_expVecSpan :
    IsClosed ((expVecSpan 𝕜 H : Submodule 𝕜 (boseFock 𝕜 H)) : Set (boseFock 𝕜 H)) :=
  Submodule.isClosed_topologicalClosure _

variable (𝕜) in
/-- Exponential vectors lie in their closed span. -/
theorem expVec_mem_expVecSpan (f : H) : expVec 𝕜 f ∈ expVecSpan 𝕜 H :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, rfl⟩)

variable (𝕜) in
/-- The approximants lie in the closed span of the exponential vectors, **given** that
the lower sector components already do — the inductive step of sector extraction. -/
theorem expVecApprox_mem (f : H) (n m : ℕ)
    (hIH : ∀ k, k < n → boseSector 𝕜 H k (expVecSector 𝕜 f k) ∈ expVecSpan 𝕜 H) :
    expVecApprox 𝕜 f n m ∈ expVecSpan 𝕜 H := by
  unfold expVecApprox
  refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
  · exact expVec_mem_expVecSpan 𝕜 _
  · rw [boseHead_expVec_smul]
    exact Submodule.sum_mem _ fun k hk =>
      Submodule.smul_mem _ _ (hIH k (Finset.mem_range.mp hk))

/-! ## Sector extraction -/

/-- ★ **Sector extraction**: every embedded sector component `boseSector n (ε(f)ₙ)` of an
exponential vector lies in the closed span of the exponential vectors. Strong induction
on `n`: the approximants lie in the closed span by the induction hypothesis
(`expVecApprox_mem`), converge to the sector component (`tendsto_expVecApprox`), and the
span is closed. -/
theorem boseSector_expVecSector_mem (f : H) (n : ℕ) :
    boseSector 𝕜 H n (expVecSector 𝕜 f n) ∈ expVecSpan 𝕜 H := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    exact (isClosed_expVecSpan 𝕜 H).mem_of_tendsto (tendsto_expVecApprox 𝕜 f n)
      (Eventually.of_forall fun m => expVecApprox_mem 𝕜 f n m IH)

/-- ★ **Embedded powers lie in the closed span**: the bosonic pure power
`f ⊗ ⋯ ⊗ f`, embedded in the `n`-particle sector, lies in the closed span of the
exponential vectors — divide the sector component by the coefficient `(√n!)⁻¹ ≠ 0`. -/
theorem boseSector_tprod_const_mem (f : H) (n : ℕ) :
    boseSector 𝕜 H n ⟨tprod 𝕜 fun _ : Fin n => f, tprod_const_mem_symPower f⟩
      ∈ expVecSpan 𝕜 H := by
  have hne : ((expCoeff n : ℝ) : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (expCoeff_pos n).ne'
  have hrepr : (⟨tprod 𝕜 fun _ : Fin n => f, tprod_const_mem_symPower f⟩ :
        symPower 𝕜 n H)
      = ((expCoeff n : ℝ) : 𝕜)⁻¹ • expVecSector 𝕜 f n := by
    apply Subtype.ext
    rw [Submodule.coe_smul, coe_expVecSector, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [hrepr, map_smul]
  exact Submodule.smul_mem _ _ (boseSector_expVecSector_mem f n)

/-! ## Transport to whole sectors -/

variable (𝕜 H) in
/-- The continuous linear map `boseSector n ∘ symProj` from the ambient tensor power to
the bosonic Fock space: symmetrize, then embed as the `n`-particle sector. -/
def symProjSector (n : ℕ) : HilbertTensorPower 𝕜 n H →L[𝕜] boseFock 𝕜 H :=
  ((boseSector 𝕜 H n).toContinuousLinearMap).comp
    ((symProj 𝕜 n H).codRestrict (symPower 𝕜 n H) symProj_mem_symPower)

variable (𝕜 H) in
/-- Action of `symProjSector`: symmetrize, then embed. -/
theorem symProjSector_apply (n : ℕ) (x : HilbertTensorPower 𝕜 n H) :
    symProjSector 𝕜 H n x
      = boseSector 𝕜 H n ⟨symProj 𝕜 n H x, symProj_mem_symPower x⟩ := rfl

/-- ★ **Sector transport**: a closed submodule of the bosonic Fock space containing every
embedded power `g ⊗ ⋯ ⊗ g` contains every embedded bosonic sector vector. Transport the
polarization density (`topologicalClosure_span_tprod_const`) along `symProjSector`: the
preimage of `M` is a closed submodule of the ambient power containing all powers, hence
all of `symPower`; and `symProjSector` fixes `symPower`. -/
theorem boseSector_mem_of_forall_tprod_const {n : ℕ} {M : Submodule 𝕜 (boseFock 𝕜 H)}
    (hMc : IsClosed (M : Set (boseFock 𝕜 H)))
    (hpow : ∀ g : H,
      boseSector 𝕜 H n ⟨tprod 𝕜 fun _ : Fin n => g, tprod_const_mem_symPower g⟩ ∈ M)
    (y : symPower 𝕜 n H) : boseSector 𝕜 H n y ∈ M := by
  have hgen : Submodule.span 𝕜 (Set.range fun g : H => tprod 𝕜 fun _ : Fin n => g)
      ≤ Submodule.comap
          (symProjSector 𝕜 H n : HilbertTensorPower 𝕜 n H →ₗ[𝕜] boseFock 𝕜 H) M := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe]
    rw [symProjSector_apply]
    have hfix : (⟨symProj 𝕜 n H (tprod 𝕜 fun _ : Fin n => g), symProj_mem_symPower _⟩ :
          symPower 𝕜 n H)
        = ⟨tprod 𝕜 fun _ : Fin n => g, tprod_const_mem_symPower g⟩ :=
      Subtype.ext (mem_symPower_iff.mp (tprod_const_mem_symPower g))
    rw [hfix]
    exact hpow g
  have hclosed : IsClosed ((Submodule.comap
      (symProjSector 𝕜 H n : HilbertTensorPower 𝕜 n H →ₗ[𝕜] boseFock 𝕜 H) M :
        Submodule 𝕜 (HilbertTensorPower 𝕜 n H)) : Set (HilbertTensorPower 𝕜 n H)) :=
    hMc.preimage (symProjSector 𝕜 H n).continuous
  have hle : symPower 𝕜 n H ≤ Submodule.comap
      (symProjSector 𝕜 H n : HilbertTensorPower 𝕜 n H →ₗ[𝕜] boseFock 𝕜 H) M := by
    rw [← topologicalClosure_span_tprod_const 𝕜 n H]
    exact Submodule.topologicalClosure_minimal _ hgen hclosed
  have hy := hle y.2
  rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe, symProjSector_apply] at hy
  have hyfix : (⟨symProj 𝕜 n H (y : HilbertTensorPower 𝕜 n H), symProj_mem_symPower _⟩ :
        symPower 𝕜 n H) = y :=
    Subtype.ext (mem_symPower_iff.mp y.2)
  rwa [hyfix] at hy

/-- ★ **Whole sectors lie in the closed span**: every embedded bosonic sector vector
`boseSector n y` lies in the closed span of the exponential vectors. -/
theorem boseSector_mem_expVecSpan (n : ℕ) (y : symPower 𝕜 n H) :
    boseSector 𝕜 H n y ∈ expVecSpan 𝕜 H :=
  boseSector_mem_of_forall_tprod_const (isClosed_expVecSpan 𝕜 H)
    (fun g => boseSector_tprod_const_mem g n) y

/-! ## Totality -/

variable (𝕜 H) in
/-- ★★★ The closed span of the exponential vectors is the whole bosonic Fock space:
every sector range lies in it (`boseSector_mem_expVecSpan`), hence so does the dense
finite-particle core. -/
theorem expVecSpan_eq_top : expVecSpan 𝕜 H = ⊤ := by
  have hfin : boseFinParticle 𝕜 H ≤ expVecSpan 𝕜 H := by
    refine iSup_le fun n => ?_
    intro x hx
    rw [LinearMap.mem_range] at hx
    obtain ⟨y, rfl⟩ := hx
    exact boseSector_mem_expVecSpan n y
  have htop : (boseFinParticle 𝕜 H).topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp (dense_boseFinParticle 𝕜 H)
  have h := Submodule.topologicalClosure_minimal _ hfin (isClosed_expVecSpan 𝕜 H)
  rw [htop] at h
  exact top_le_iff.mp h

variable (𝕜 H) in
/-- ★★★ **Totality of the exponential vectors**: the closed span of the exponential
vectors is the whole bosonic Fock space. -/
theorem expVec_total :
    (Submodule.span 𝕜 (Set.range (expVec 𝕜 : H → boseFock 𝕜 H))).topologicalClosure
      = ⊤ :=
  expVecSpan_eq_top 𝕜 H

variable (𝕜 H) in
/-- ★★ The span of the exponential vectors is **dense** in the bosonic Fock space. -/
theorem dense_span_expVec :
    Dense ((Submodule.span 𝕜 (Set.range (expVec 𝕜 : H → boseFock 𝕜 H)) :
        Submodule 𝕜 (boseFock 𝕜 H)) : Set (boseFock 𝕜 H)) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr (expVec_total 𝕜 H)

end Spectra
