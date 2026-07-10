/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.LinearAlgebra.TensorPower.Basic
import Spectra.Spaces.Tensor.Map

/-!
# The inner product on tensor powers `⨂[𝕜]^n H`

Mathlib's `PiTensorProduct` carries Banach (injective/projective) seminorms but **no inner
product**. This file closes that gap for tensor powers: the algebraic `n`-fold tensor power
`⨂[𝕜]^n H = ⨂[𝕜] (_ : Fin n), H` of an inner product space is an inner product space with

`⟪⨂ₜ x i, ⨂ₜ y i⟫ = ∏ i, ⟪x i, y i⟫`.

This is the `Fin n`-ary generalization of `Analysis/InnerProductSpace/TensorProduct.lean`
(the binary case), chosen over iterating the binary construction so that the permutation
action `PiTensorProduct.reindex` — the input to bosonic/fermionic symmetrization — acts on
a canonical object rather than through associator bookkeeping.

## Construction

The sesquilinear form cannot be obtained from `PiTensorProduct.lift` directly (there is no
semilinear multilinear lift), so it is assembled in two stages:

* `prodInnerRight y : ⨂[𝕜]^n H →ₗ[𝕜] 𝕜`, the lift of `x ↦ ∏ i, ⟪y i, x i⟫` — genuinely
  multilinear in `x` for fixed `y`;
* the assignment `y ↦ starComp (prodInnerRight y)` (post-composition with conjugation)
  **is** multilinear in `y`, valued in the conjugate-linear functionals, so it lifts to
  `innerJ : ⨂[𝕜]^n H →ₗ[𝕜] (⨂[𝕜]^n H →ₛₗ[conj] 𝕜)`, and `⟪t, s⟫ := innerJ s t`.

Positive definiteness is proved by induction on `n` through the splitting
`splitEquiv : (⨂[𝕜]^n H) ⊗ H ≃ₗ ⨂[𝕜]^(n+1) H`: the generalized orthonormal fiber
representation (`Spectra.HilbertTensor.exists_sum_tmul_orthonormal`, whose first factor
needs only a module structure) diagonalizes `⟪t, t⟫` into `∑ j, ⟪u j, u j⟫` at level `n`.
No intermediate `InnerProductSpace` instances are needed — the induction is a bare
proposition about the raw inner function.

## Main results

* `Spectra.TensorPower.instInnerProductSpace` — `⨂[𝕜]^n H` is an inner product space
  (via `InnerProductSpace.Core`, following the binary file's pattern).
* `Spectra.TensorPower.inner_tprod_tprod` — the product formula for pure tensors.
* `Spectra.TensorPower.norm_tprod` — `‖⨂ₜ x i‖ = ∏ i, ‖x i‖`.
* `Spectra.TensorPower.inner_splitEquiv_tmul` — the splitting intertwines the inner
  products: `⟪e (u ⊗ y), e (v ⊗ z)⟫ = ⟪u, v⟫ * ⟪y, z⟫`.

The completion (the *Hilbert* tensor power) and the permutation unitaries live in
`Spectra/Spaces/Tensor/Power.lean`.
-/

noncomputable section

open scoped TensorProduct
open PiTensorProduct Function

namespace Spectra.TensorPower

variable {𝕜 H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  {n : ℕ}

/-! ## The sesquilinear form -/

/-- Post-composition of a linear functional with conjugation, as a conjugate-linear
functional. -/
private def starComp {M : Type*} [AddCommMonoid M] [Module 𝕜 M] (f : M →ₗ[𝕜] 𝕜) :
    M →ₛₗ[starRingEnd 𝕜] 𝕜 where
  toFun t := starRingEnd 𝕜 (f t)
  map_add' s t := by simp
  map_smul' c t := by simp [smul_eq_mul]

private lemma starComp_apply {M : Type*} [AddCommMonoid M] [Module 𝕜 M]
    (f : M →ₗ[𝕜] 𝕜) (t : M) : starComp f t = starRingEnd 𝕜 (f t) := rfl

private lemma starComp_add {M : Type*} [AddCommMonoid M] [Module 𝕜 M]
    (f g : M →ₗ[𝕜] 𝕜) : starComp (f + g) = starComp f + starComp g :=
  LinearMap.ext fun t => by simp [starComp_apply]

private lemma starComp_conj_smul {M : Type*} [AddCommMonoid M] [Module 𝕜 M]
    (c : 𝕜) (f : M →ₗ[𝕜] 𝕜) :
    starComp (starRingEnd 𝕜 c • f) = c • starComp f :=
  LinearMap.ext fun t => by simp [starComp_apply, smul_eq_mul]

/-- For a fixed family `y`, the linear functional `⨂ₜ x ↦ ∏ i, ⟪y i, x i⟫` on the tensor
power. -/
private def prodInnerRight (y : Fin n → H) : (⨂[𝕜]^n H) →ₗ[𝕜] 𝕜 :=
  PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra 𝕜 (Fin n) 𝕜).compLinearMap fun i => innerₛₗ 𝕜 (y i))

private lemma prodInnerRight_tprod (y x : Fin n → H) :
    prodInnerRight (𝕜 := 𝕜) y (tprod 𝕜 x) = ∏ i, inner 𝕜 (y i) (x i) := by
  simp [prodInnerRight]

/-- The product `∏ i, ⟪(update y j v) i, x i⟫` isolates the updated slot. -/
private lemma prod_inner_update [DecidableEq (Fin n)] (y x : Fin n → H) (j : Fin n) (v : H) :
    ∏ i, inner 𝕜 (update y j v i) (x i)
      = inner 𝕜 v (x j) * ∏ i ∈ Finset.univ \ {j}, inner 𝕜 (y i) (x i) := by
  calc ∏ i, inner 𝕜 (update y j v i) (x i)
      = ∏ i, update (fun k => inner 𝕜 (y k) (x k)) j (inner 𝕜 v (x j)) i :=
        Finset.prod_congr rfl fun i _ =>
          apply_update (fun k (h : H) => inner 𝕜 h (x k)) y j v i
    _ = inner 𝕜 v (x j) * ∏ i ∈ Finset.univ \ {j}, inner 𝕜 (y i) (x i) :=
        Finset.prod_update_of_mem (Finset.mem_univ j) _ _

private lemma prodInnerRight_update_add [DecidableEq (Fin n)]
    (y : Fin n → H) (j : Fin n) (a b : H) :
    prodInnerRight (𝕜 := 𝕜) (update y j (a + b))
      = prodInnerRight (update y j a) + prodInnerRight (update y j b) := by
  refine LinearMap.ext fun t => ?_
  refine t.induction_on ?_ ?_
  · intro r x
    simp only [map_smul, LinearMap.add_apply, prodInnerRight_tprod, prod_inner_update,
      inner_add_left, smul_eq_mul]
    ring
  · intro t₁ t₂ h₁ h₂
    simp only [map_add, LinearMap.add_apply] at h₁ h₂ ⊢
    rw [h₁, h₂]

private lemma prodInnerRight_update_smul [DecidableEq (Fin n)]
    (y : Fin n → H) (j : Fin n) (c : 𝕜) (a : H) :
    prodInnerRight (𝕜 := 𝕜) (update y j (c • a))
      = starRingEnd 𝕜 c • prodInnerRight (update y j a) := by
  refine LinearMap.ext fun t => ?_
  refine t.induction_on ?_ ?_
  · intro r x
    simp only [map_smul, LinearMap.smul_apply, prodInnerRight_tprod, prod_inner_update,
      inner_smul_left, smul_eq_mul]
    ring
  · intro t₁ t₂ h₁ h₂
    simp only [map_add, LinearMap.smul_apply] at h₁ h₂ ⊢
    rw [h₁, h₂]

/-- The conjugated pairing `y ↦ (t ↦ star (∏ i, ⟪y i, ·⟫))`, multilinear in `y` and valued
in conjugate-linear functionals. -/
private def innerCore :
    MultilinearMap 𝕜 (fun _ : Fin n => H) ((⨂[𝕜]^n H) →ₛₗ[starRingEnd 𝕜] 𝕜) where
  toFun y := starComp (prodInnerRight y)
  map_update_add' := by
    intro _ y j a b
    rw [prodInnerRight_update_add, starComp_add]
  map_update_smul' := by
    intro _ y j c a
    rw [prodInnerRight_update_smul, starComp_conj_smul]

/-- The bundled inner pairing: linear in the second (outer) argument, conjugate-linear in
the first (inner) argument. `⟪t, s⟫ = innerJ s t`. -/
private def innerJ : (⨂[𝕜]^n H) →ₗ[𝕜] ((⨂[𝕜]^n H) →ₛₗ[starRingEnd 𝕜] 𝕜) :=
  PiTensorProduct.lift innerCore

noncomputable instance instInner : Inner 𝕜 (⨂[𝕜]^n H) :=
  ⟨fun t s => innerJ s t⟩

private lemma inner_def (t s : ⨂[𝕜]^n H) : inner 𝕜 t s = innerJ s t := rfl

/-- The inner product of pure tensors is the product of the factor inner products. -/
theorem inner_tprod_tprod (x y : Fin n → H) :
    inner 𝕜 (tprod 𝕜 x) (tprod 𝕜 y) = ∏ i, inner 𝕜 (x i) (y i) := by
  rw [inner_def, innerJ, lift.tprod]
  change starComp (prodInnerRight y) (tprod 𝕜 x) = _
  rw [starComp_apply, prodInnerRight_tprod, map_prod]
  exact Finset.prod_congr rfl fun i _ => inner_conj_symm _ _

/-! ### Raw sesquilinearity (available before the instance bundle) -/

private lemma inner_add_left' (t t' s : ⨂[𝕜]^n H) :
    inner 𝕜 (t + t') s = inner 𝕜 t s + inner 𝕜 t' s :=
  (innerJ s).map_add t t'

private lemma inner_smul_left' (c : 𝕜) (t s : ⨂[𝕜]^n H) :
    inner 𝕜 (c • t) s = starRingEnd 𝕜 c * inner 𝕜 t s :=
  (innerJ s).map_smulₛₗ c t

private lemma inner_add_right' (t s s' : ⨂[𝕜]^n H) :
    inner 𝕜 t (s + s') = inner 𝕜 t s + inner 𝕜 t s' := by
  rw [inner_def, map_add]; rfl

private lemma inner_smul_right' (c : 𝕜) (t s : ⨂[𝕜]^n H) :
    inner 𝕜 t (c • s) = c * inner 𝕜 t s := by
  rw [inner_def, map_smul]; rfl

private lemma inner_sum_left' {m : ℕ} (u : Fin m → ⨂[𝕜]^n H) (s : ⨂[𝕜]^n H) :
    inner 𝕜 (∑ j, u j) s = ∑ j, inner 𝕜 (u j) s :=
  map_sum (innerJ s) u Finset.univ

private lemma inner_sum_right' {m : ℕ} (t : ⨂[𝕜]^n H) (u : Fin m → ⨂[𝕜]^n H) :
    inner 𝕜 t (∑ j, u j) = ∑ j, inner 𝕜 t (u j) := by
  rw [inner_def, map_sum, LinearMap.sum_apply]
  rfl

private lemma inner_conj_symm' (t s : ⨂[𝕜]^n H) :
    starRingEnd 𝕜 (inner 𝕜 s t) = inner 𝕜 t s := by
  refine t.induction_on ?_ ?_
  · intro r x
    refine s.induction_on ?_ ?_
    · intro r' y
      rw [inner_smul_left', inner_smul_right', inner_smul_left', inner_smul_right',
        inner_tprod_tprod, inner_tprod_tprod, map_mul, map_mul, map_prod, RCLike.conj_conj]
      simp only [inner_conj_symm]
      ring
    · intro a b ha hb
      rw [inner_add_left', map_add, ha, hb, inner_add_right']
  · intro a b ha hb
    rw [inner_add_right', map_add, ha, hb, inner_add_left']

/-- `⟪t, t⟫` is real (before any instance exists): its conjugate is itself. -/
private lemma inner_self_eq_zero_of_re_eq_zero {t : ⨂[𝕜]^n H}
    (h : RCLike.re (inner 𝕜 t t) = 0) : inner 𝕜 t t = 0 := by
  have him : RCLike.im (inner 𝕜 t t) = 0 :=
    RCLike.conj_eq_iff_im.mp (inner_conj_symm' t t)
  exact RCLike.ext (by simpa using h) (by simpa using him)

/-! ## The splitting `(⨂[𝕜]^n H) ⊗ H ≃ₗ ⨂[𝕜]^(n+1) H` -/

variable (𝕜 H n) in
/-- The splitting of the `(n+1)`-fold tensor power as (`n`-fold power) ⊗ (one factor):
reindex `Fin n ⊕ Fin 1 ≃ Fin (n+1)` composed with `PiTensorProduct.tmulEquiv` and the
one-factor identification. -/
private def splitEquiv : ((⨂[𝕜]^n H) ⊗[𝕜] H) ≃ₗ[𝕜] ⨂[𝕜]^(n + 1) H :=
  (TensorProduct.congr (LinearEquiv.refl 𝕜 (⨂[𝕜]^n H))
      (subsingletonEquiv (0 : Fin 1) : (⨂[𝕜] _ : Fin 1, H) ≃ₗ[𝕜] H).symm).trans
    ((tmulEquiv 𝕜 H).trans (reindex 𝕜 (fun _ => H) finSumFinEquiv))

private lemma splitEquiv_tprod_tmul (x : Fin n → H) (y : H) :
    splitEquiv 𝕜 H n (tprod 𝕜 x ⊗ₜ[𝕜] y)
      = tprod 𝕜 fun i => Sum.elim x (fun _ => y) (finSumFinEquiv.symm i) := by
  have hy : ((subsingletonEquiv (0 : Fin 1) :
      (⨂[𝕜] _ : Fin 1, H) ≃ₗ[𝕜] H)).symm y = tprod 𝕜 fun _ : Fin 1 => y := by
    apply (subsingletonEquiv (0 : Fin 1)).injective
    rw [LinearEquiv.apply_symm_apply, subsingletonEquiv_apply_tprod]
  rw [splitEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, hy, tmulEquiv_apply, reindex_tprod]

/-- The splitting intertwines the inner products:
`⟪e (u ⊗ y), e (v ⊗ z)⟫ = ⟪u, v⟫ * ⟪y, z⟫`. -/
private lemma inner_splitEquiv_tmul (u v : ⨂[𝕜]^n H) (y z : H) :
    inner 𝕜 (splitEquiv 𝕜 H n (u ⊗ₜ[𝕜] y)) (splitEquiv 𝕜 H n (v ⊗ₜ[𝕜] z))
      = inner 𝕜 u v * inner 𝕜 y z := by
  refine u.induction_on ?_ ?_
  · intro r x
    refine v.induction_on ?_ ?_
    · intro r' x'
      rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul', map_smul, map_smul,
        inner_smul_left', inner_smul_right', inner_smul_left', inner_smul_right',
        splitEquiv_tprod_tmul, splitEquiv_tprod_tmul, inner_tprod_tprod, inner_tprod_tprod]
      have hprod : (∏ i : Fin (n + 1),
            inner 𝕜 (Sum.elim x (fun _ => y) (finSumFinEquiv.symm i))
              (Sum.elim x' (fun _ => z) (finSumFinEquiv.symm i)))
          = (∏ i, inner 𝕜 (x i) (x' i)) * inner 𝕜 y z := by
        rw [← Equiv.prod_comp finSumFinEquiv fun i =>
          inner 𝕜 (Sum.elim x (fun _ => y) (finSumFinEquiv.symm i))
            (Sum.elim x' (fun _ => z) (finSumFinEquiv.symm i))]
        simp only [Equiv.symm_apply_apply]
        rw [Fintype.prod_sum_type]
        simp
      rw [hprod]
      ring
    · intro a b ha hb
      rw [TensorProduct.add_tmul, map_add, inner_add_right', ha, hb, inner_add_right',
        add_mul]
  · intro a b ha hb
    rw [TensorProduct.add_tmul, map_add, inner_add_left', ha, hb, inner_add_left', add_mul]

/-! ## Positivity and definiteness, by induction on `n` -/

private theorem inner_self_nonneg_definite :
    ∀ (n : ℕ) (t : ⨂[𝕜]^n H),
      0 ≤ RCLike.re (inner 𝕜 t t) ∧ (inner 𝕜 t t = 0 → t = 0)
  | 0, t => by
    have ht : t = isEmptyEquiv (Fin 0) t • tprod 𝕜 isEmptyElim := by
      conv_lhs => rw [← (isEmptyEquiv (Fin 0)).symm_apply_apply t]
      rfl
    constructor
    · rw [ht, inner_smul_left', inner_smul_right', inner_tprod_tprod]
      simp [RCLike.conj_mul]
    · intro h0
      rw [ht, inner_smul_left', inner_smul_right', inner_tprod_tprod] at h0
      simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, RCLike.conj_mul,
        ← RCLike.ofReal_pow, RCLike.ofReal_eq_zero, pow_eq_zero_iff, norm_eq_zero,
        OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true] at h0
      rw [ht, h0, zero_smul]
  | (m + 1), t => by
    obtain ⟨k, u, g, hg, hw⟩ :=
      Spectra.HilbertTensor.exists_sum_tmul_orthonormal (𝕜 := 𝕜)
        ((splitEquiv 𝕜 H m).symm t)
    have ht : t = ∑ j, splitEquiv 𝕜 H m (u j ⊗ₜ[𝕜] g j) := by
      conv_lhs => rw [← (splitEquiv 𝕜 H m).apply_symm_apply t, hw]
      rw [map_sum]
    have horth := orthonormal_iff_ite.mp hg
    have hexp : inner 𝕜 t t = ∑ j, inner 𝕜 (u j) (u j) := by
      rw [ht, inner_sum_left']
      have hrow : ∀ j, inner 𝕜 (splitEquiv 𝕜 H m (u j ⊗ₜ[𝕜] g j))
          (∑ l, splitEquiv 𝕜 H m (u l ⊗ₜ[𝕜] g l)) = inner 𝕜 (u j) (u j) := by
        intro j
        rw [inner_sum_right']
        rw [Finset.sum_eq_single j
          (fun l _ hl => by
            rw [inner_splitEquiv_tmul, horth j l, if_neg fun h => hl h.symm, mul_zero])
          (fun h => absurd (Finset.mem_univ j) h)]
        rw [inner_splitEquiv_tmul, horth j j, if_pos rfl, mul_one]
      exact Finset.sum_congr rfl fun j _ => hrow j
    constructor
    · rw [hexp, map_sum]
      exact Finset.sum_nonneg fun j _ => (inner_self_nonneg_definite m (u j)).1
    · intro h0
      have hre : ∀ j ∈ Finset.univ, RCLike.re (inner 𝕜 (u j) (u j)) = 0 := by
        have hsum : ∑ j, RCLike.re (inner 𝕜 (u j) (u j)) = 0 := by
          rw [← map_sum, ← hexp, h0, map_zero]
        exact fun j _ =>
          (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
            (inner_self_nonneg_definite m (u j)).1).mp hsum j (Finset.mem_univ j)
      have hu : ∀ j, u j = 0 := fun j =>
        (inner_self_nonneg_definite m (u j)).2
          (inner_self_eq_zero_of_re_eq_zero (hre j (Finset.mem_univ j)))
      rw [ht]
      exact Finset.sum_eq_zero fun j _ => by rw [hu j, TensorProduct.zero_tmul, map_zero]

/-! ## The instances -/

variable (𝕜 H n) in
@[reducible]
private def coreStruct : InnerProductSpace.Core 𝕜 (⨂[𝕜]^n H) where
  conj_inner_symm := inner_conj_symm'
  add_left := inner_add_left'
  smul_left t s c := inner_smul_left' c t s
  definite t := (inner_self_nonneg_definite n t).2
  re_inner_nonneg t := (inner_self_nonneg_definite n t).1

noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (⨂[𝕜]^n H) :=
  (coreStruct 𝕜 H n).toNormedAddCommGroup

instance instInnerProductSpace : InnerProductSpace 𝕜 (⨂[𝕜]^n H) :=
  .ofCore _

/-- The cross norm on pure tensors of the tensor power: `‖⨂ₜ x i‖ = ∏ i, ‖x i‖`. -/
@[simp]
theorem norm_tprod (x : Fin n → H) : ‖tprod 𝕜 x‖ = ∏ i, ‖x i‖ := by
  -- The raw-instance inner product of a pure tensor with itself, as a real cast.
  have key : @inner 𝕜 _ instInner (tprod 𝕜 x) (tprod 𝕜 x)
      = ((∏ i, ‖x i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [inner_tprod_tprod, RCLike.ofReal_prod]
    exact Finset.prod_congr rfl fun i _ => by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) (x i), RCLike.ofReal_pow]
  have h : (‖tprod 𝕜 x‖ : ℝ) ^ 2 = (∏ i, ‖x i‖) ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := 𝕜)]
    calc RCLike.re (inner 𝕜 (tprod 𝕜 x) (tprod 𝕜 x))
        = RCLike.re ((∏ i, ‖x i‖ ^ 2 : ℝ) : 𝕜) := congrArg _ key
      _ = ∏ i, ‖x i‖ ^ 2 := RCLike.ofReal_re _
      _ = (∏ i, ‖x i‖) ^ 2 := by rw [Finset.prod_pow]
  have h1 := Real.sqrt_le_sqrt h.le
  have h2 := Real.sqrt_le_sqrt h.ge
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (Finset.prod_nonneg fun i _ =>
    norm_nonneg _)] at h1 h2
  exact le_antisymm h1 h2

end Spectra.TensorPower
