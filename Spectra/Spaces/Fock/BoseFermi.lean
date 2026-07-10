/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Fock.Basic
import Spectra.Spaces.Fock.Symmetrizer
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Bosonic and fermionic Fock spaces

The symmetric (bosonic) and antisymmetric (fermionic) `n`-particle sectors of the Hilbert
tensor power, and the ℓ²-direct sums built from them:

`boseFock 𝕜 H := lp (fun n => symPower 𝕜 n H) 2`,
`fermiFock 𝕜 H := lp (fun n => altPower 𝕜 n H) 2`.

The sectors are the fixed-point spaces of the symmetrizer `symProj` and antisymmetrizer
`altProj` of `Spectra/Spaces/Fock/Symmetrizer.lean`. As kernels of continuous linear maps
they are closed, hence complete, and the Fock spaces are Hilbert spaces by the same
instance inheritance as `fullFock`. This is Fock Spaces milestone M2 step 2.

## Conventions

Following Parthasarathy, the inner product on `symPower`/`altPower` is the **restricted**
full-tensor-power inner product — no `n!` rescaling. The exponential vectors of milestone
M3 carry `1/√(n!)` coefficients, giving `⟪ε(f), ε(g)⟫ = exp ⟪f, g⟫`; the CCR commutation
constant of milestone M4 is the acceptance test for this normalization. The single-mode
sanity check `boseFock` ≅ `ℓ²(ℕ)` (for a one-dimensional one-particle space) remains open;
it needs the sector dimension bookkeeping (`symPower 𝕜 n 𝕜` is one-dimensional).

For `n ≤ 1` the two sectors coincide (both are everything); genuine disjointness starts
at `n = 2` (`symPower_inf_altPower`).

## Main definitions

* `Spectra.HilbertTensorPower.symPower 𝕜 n H` — the bosonic (symmetric) sector,
  the kernel of `1 - symProj 𝕜 n H`.
* `Spectra.HilbertTensorPower.altPower 𝕜 n H` — the fermionic (antisymmetric) sector.
* `Spectra.boseFock 𝕜 H` / `Spectra.fermiFock 𝕜 H` — the bosonic/fermionic Fock spaces.

## Main results

* `mem_symPower_iff_forall` — `x` is bosonic iff `U_σ x = x` for every permutation `σ`.
* `mem_altPower_iff_forall` — `x` is fermionic iff `U_σ x = sign σ • x` for every `σ`.
* `range_symProj` / `range_altProj` — the sectors are exactly the projections' ranges.
* `isClosed_symPower` / `isClosed_altPower` — the sectors are closed (hence complete).
* `symPower_zero` … `altPower_one` — for `n ≤ 1` both sectors are `⊤`.
* `symPower_inf_altPower` — for `2 ≤ n` the sectors intersect trivially.
* `altProj_tprod_eq_zero` — **Pauli exclusion** at the tensor level: antisymmetrizing a
  pure tensor with a repeated factor gives `0`.
* `tprod_const_mem_symPower` / `symPower_ne_bot` — constant pure tensors are bosonic, so
  the bosonic sector is nonzero whenever `H` is.
* `norm_sq_altProj_tprod` — **Slater normalization**: for orthonormal `x`,
  `‖altProj (⨂ₜ x)‖² = (n!)⁻¹`; hence the fermionic sector is nonzero whenever `H`
  contains `n` orthonormal vectors (`altPower_ne_bot`).
-/

noncomputable section

open scoped TensorProduct Nat
open PiTensorProduct UniformSpace

namespace Spectra

variable (𝕜 : Type*) (n : ℕ) (H : Type*) [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

namespace HilbertTensorPower

variable {𝕜 n H}

/-! ## The sectors -/

variable (𝕜 n H) in
/-- The **bosonic sector**: the symmetric subspace of the `n`-fold Hilbert tensor power,
realized as the fixed-point space (kernel of `1 - symProj`) of the symmetrizer. -/
def symPower : Submodule 𝕜 (HilbertTensorPower 𝕜 n H) :=
  (1 - symProj 𝕜 n H).ker

variable (𝕜 n H) in
/-- The **fermionic sector**: the antisymmetric subspace of the `n`-fold Hilbert tensor
power, realized as the fixed-point space of the antisymmetrizer. -/
def altPower : Submodule 𝕜 (HilbertTensorPower 𝕜 n H) :=
  (1 - altProj 𝕜 n H).ker

/-- Membership in the bosonic sector: fixed points of the symmetrizer. -/
theorem mem_symPower_iff {x : HilbertTensorPower 𝕜 n H} :
    x ∈ symPower 𝕜 n H ↔ symProj 𝕜 n H x = x := by
  simp only [symPower, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, sub_eq_zero]
  exact eq_comm

/-- Membership in the fermionic sector: fixed points of the antisymmetrizer. -/
theorem mem_altPower_iff {x : HilbertTensorPower 𝕜 n H} :
    x ∈ altPower 𝕜 n H ↔ altProj 𝕜 n H x = x := by
  simp only [altPower, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, sub_eq_zero]
  exact eq_comm

variable (𝕜 n H) in
/-- The bosonic sector is closed: it is the kernel of a continuous linear map. -/
theorem isClosed_symPower :
    IsClosed (symPower 𝕜 n H : Set (HilbertTensorPower 𝕜 n H)) :=
  (1 - symProj 𝕜 n H).isClosed_ker

variable (𝕜 n H) in
/-- The fermionic sector is closed: it is the kernel of a continuous linear map. -/
theorem isClosed_altPower :
    IsClosed (altPower 𝕜 n H : Set (HilbertTensorPower 𝕜 n H)) :=
  (1 - altProj 𝕜 n H).isClosed_ker

instance : CompleteSpace (symPower 𝕜 n H) :=
  (isClosed_symPower 𝕜 n H).completeSpace_coe

instance : CompleteSpace (altPower 𝕜 n H) :=
  (isClosed_altPower 𝕜 n H).completeSpace_coe

-- Sanity: the sectors are Hilbert spaces by instance resolution alone.
example : NormedAddCommGroup (symPower 𝕜 n H) := inferInstance
example : InnerProductSpace 𝕜 (symPower 𝕜 n H) := inferInstance
example : CompleteSpace (symPower 𝕜 n H) := inferInstance
example : NormedAddCommGroup (altPower 𝕜 n H) := inferInstance
example : InnerProductSpace 𝕜 (altPower 𝕜 n H) := inferInstance
example : CompleteSpace (altPower 𝕜 n H) := inferInstance

/-! ## Characterizations by the permutation action -/

/-- **Bosonic states are the permutation-invariant states**: `x ∈ symPower` iff
`U_σ x = x` for every permutation `σ`. -/
theorem mem_symPower_iff_forall {x : HilbertTensorPower 𝕜 n H} :
    x ∈ symPower 𝕜 n H ↔ ∀ σ : Equiv.Perm (Fin n), permUnitary 𝕜 H σ x = x := by
  rw [mem_symPower_iff]
  constructor
  · intro hx σ
    calc permUnitary 𝕜 H σ x = permUnitary 𝕜 H σ (symProj 𝕜 n H x) := by rw [hx]
      _ = symProj 𝕜 n H x := permUnitary_symProj σ x
      _ = x := hx
  · intro h
    rw [symProj_apply]
    simp only [h]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), one_smul]

/-- **Fermionic states are the sign-covariant states**: `x ∈ altPower` iff
`U_σ x = sign σ • x` for every permutation `σ`. -/
theorem mem_altPower_iff_forall {x : HilbertTensorPower 𝕜 n H} :
    x ∈ altPower 𝕜 n H ↔
      ∀ σ : Equiv.Perm (Fin n), permUnitary 𝕜 H σ x = permSign 𝕜 σ • x := by
  rw [mem_altPower_iff]
  constructor
  · intro hx σ
    calc permUnitary 𝕜 H σ x = permUnitary 𝕜 H σ (altProj 𝕜 n H x) := by rw [hx]
      _ = permSign 𝕜 σ • altProj 𝕜 n H x := permUnitary_altProj σ x
      _ = permSign 𝕜 σ • x := by rw [hx]
  · intro h
    rw [altProj_apply]
    simp only [h, smul_smul, permSign_mul_self, one_smul]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), one_smul]

/-- Symmetrized states are bosonic. -/
theorem symProj_mem_symPower (x : HilbertTensorPower 𝕜 n H) :
    symProj 𝕜 n H x ∈ symPower 𝕜 n H :=
  mem_symPower_iff.mpr (symProj_symProj x)

/-- Antisymmetrized states are fermionic. -/
theorem altProj_mem_altPower (x : HilbertTensorPower 𝕜 n H) :
    altProj 𝕜 n H x ∈ altPower 𝕜 n H :=
  mem_altPower_iff.mpr (altProj_altProj x)

variable (𝕜 n H) in
/-- The bosonic sector is the range of the symmetrizer (as a linear map). -/
theorem range_symProj : (symProj 𝕜 n H).range = symPower 𝕜 n H := by
  ext x
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  constructor
  · rintro ⟨y, rfl⟩
    exact symProj_mem_symPower y
  · intro hx
    exact ⟨x, mem_symPower_iff.mp hx⟩

variable (𝕜 n H) in
/-- The fermionic sector is the range of the antisymmetrizer (as a linear map). -/
theorem range_altProj : (altProj 𝕜 n H).range = altPower 𝕜 n H := by
  ext x
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  constructor
  · rintro ⟨y, rfl⟩
    exact altProj_mem_altPower y
  · intro hx
    exact ⟨x, mem_altPower_iff.mp hx⟩

/-! ## Degenerate ranks `n ≤ 1` -/

/-- The scalar sign of the identity permutation. -/
@[simp]
theorem permSign_one : permSign 𝕜 (1 : Equiv.Perm (Fin n)) = 1 := by
  rw [permSign]
  simp

variable (𝕜 H) in
/-- At rank `0` the bosonic sector is everything. -/
theorem symPower_zero : symPower 𝕜 0 H = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  rw [mem_symPower_iff_forall]
  intro σ
  rw [Subsingleton.elim σ 1, permUnitary_one_apply]

variable (𝕜 H) in
/-- At rank `1` the bosonic sector is everything. -/
theorem symPower_one : symPower 𝕜 1 H = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  rw [mem_symPower_iff_forall]
  intro σ
  rw [Subsingleton.elim σ 1, permUnitary_one_apply]

variable (𝕜 H) in
/-- At rank `0` the fermionic sector is everything. -/
theorem altPower_zero : altPower 𝕜 0 H = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  rw [mem_altPower_iff_forall]
  intro σ
  rw [Subsingleton.elim σ 1, permUnitary_one_apply, permSign_one, one_smul]

variable (𝕜 H) in
/-- At rank `1` the fermionic sector is everything. -/
theorem altPower_one : altPower 𝕜 1 H = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  rw [mem_altPower_iff_forall]
  intro σ
  rw [Subsingleton.elim σ 1, permUnitary_one_apply, permSign_one, one_smul]

/-! ## Sector disjointness (`2 ≤ n`) -/

/-- For `2 ≤ n` the bosonic and fermionic sectors intersect trivially. (For `n ≤ 1` they
coincide instead — see `symPower_zero` … `altPower_one`.) -/
theorem symPower_inf_altPower (hn : 2 ≤ n) :
    symPower 𝕜 n H ⊓ altPower 𝕜 n H = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨hs, ha⟩ := Submodule.mem_inf.mp hx
  have h0 : symProj 𝕜 n H (altProj 𝕜 n H x) = 0 := by
    simpa using DFunLike.congr_fun (symProj_comp_altProj hn) x
  calc x = symProj 𝕜 n H x := (mem_symPower_iff.mp hs).symm
    _ = symProj 𝕜 n H (altProj 𝕜 n H x) := by rw [mem_altPower_iff.mp ha]
    _ = 0 := h0

/-! ## Pauli exclusion -/

/-- **Pauli exclusion** at the tensor level: antisymmetrizing a pure tensor with a
repeated factor (`x i = x j` in distinct slots `i ≠ j`) gives `0`. -/
theorem altProj_tprod_eq_zero (x : Fin n → H) (i j : Fin n) (hne : i ≠ j)
    (heq : x i = x j) : altProj 𝕜 n H (tprod 𝕜 x) = 0 := by
  have hxs : ∀ k, x (Equiv.swap i j k) = x k := by
    intro k
    rcases eq_or_ne k i with rfl | hki
    · rw [Equiv.swap_apply_left]
      exact heq.symm
    rcases eq_or_ne k j with rfl | hkj
    · rw [Equiv.swap_apply_right]
      exact heq
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hsign : permSign 𝕜 (Equiv.swap i j) = -1 := by
    rw [permSign, Equiv.Perm.sign_swap hne]
    simp
  have key : (∑ σ : Equiv.Perm (Fin n), permSign 𝕜 σ • tprod 𝕜 fun k => x (σ k))
      = -∑ σ : Equiv.Perm (Fin n), permSign 𝕜 σ • tprod 𝕜 fun k => x (σ k) := by
    have hre : (∑ σ : Equiv.Perm (Fin n),
          permSign 𝕜 (Equiv.swap i j * σ) • tprod 𝕜 fun k => x ((Equiv.swap i j * σ) k))
        = ∑ σ : Equiv.Perm (Fin n), permSign 𝕜 σ • tprod 𝕜 fun k => x (σ k) :=
      Fintype.sum_bijective (Equiv.swap i j * ·)
        (Group.mulLeft_bijective (Equiv.swap i j)) _ _ fun σ => rfl
    conv_lhs => rw [← hre]
    simp only [permSign_mul, hsign, neg_one_mul, Equiv.Perm.mul_apply, hxs, neg_smul]
    exact Finset.sum_neg_distrib fun σ => permSign 𝕜 σ • tprod 𝕜 fun k => x (σ k)
  have hzero : (∑ σ : Equiv.Perm (Fin n), permSign 𝕜 σ • tprod 𝕜 fun k => x (σ k)) = 0 := by
    have h2 : (2 : 𝕜) • (∑ σ : Equiv.Perm (Fin n), permSign 𝕜 σ • tprod 𝕜 fun k => x (σ k))
        = 0 := by
      rw [two_smul]
      nth_rewrite 1 [key]
      rw [neg_add_cancel]
    rcases smul_eq_zero.mp h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  rw [altProj_tprod, hzero, smul_zero]

/-! ## Non-degeneracy of the sectors -/

/-- Constant families are bosonic: permuting the slots of `u ⊗ ⋯ ⊗ u` is a no-op. -/
theorem tprod_const_mem_symPower (u : H) :
    tprod 𝕜 (fun _ : Fin n => u) ∈ symPower 𝕜 n H := by
  rw [mem_symPower_iff_forall]
  intro σ
  rw [permUnitary_tprod]

variable (𝕜 n) in
/-- The bosonic sector is nonzero whenever `H` is: it contains the constant pure tensor
`u ⊗ ⋯ ⊗ u`, of norm `‖u‖ ^ n ≠ 0`. -/
theorem symPower_ne_bot {u : H} (hu : u ≠ 0) : symPower 𝕜 n H ≠ ⊥ := by
  intro hbot
  have hmem := tprod_const_mem_symPower (𝕜 := 𝕜) (n := n) u
  rw [hbot, Submodule.mem_bot] at hmem
  have h0 : ‖tprod 𝕜 (fun _ : Fin n => u)‖ = 0 := by rw [hmem, norm_zero]
  simp only [norm_tprod, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h0
  exact pow_ne_zero n (norm_ne_zero_iff.mpr hu) h0

/-- For an orthonormal family `x`, the pure tensor pairs against its permuted versions
diagonally: `⟪⨂ₜ x, ⨂ₜ (x ∘ σ)⟫` is `1` at `σ = 1` and `0` otherwise. -/
theorem inner_tprod_perm_of_orthonormal {x : Fin n → H} (hx : Orthonormal 𝕜 x)
    (σ : Equiv.Perm (Fin n)) :
    inner 𝕜 (tprod 𝕜 x) (tprod 𝕜 fun i => x (σ i)) = if σ = 1 then (1 : 𝕜) else 0 := by
  have hij := orthonormal_iff_ite.mp hx
  simp only [inner_tprod_tprod]
  rcases eq_or_ne σ 1 with rfl | hσ
  · rw [if_pos rfl]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [Equiv.Perm.one_apply, hij i i, if_pos rfl]
  · rw [if_neg hσ]
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := not_forall.mp fun hcon => hσ (Equiv.ext hcon)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [hij i (σ i), if_neg (Ne.symm hi)]

/-- **Slater self-pairing**: for an orthonormal family `x` the antisymmetrized pure tensor
pairs with itself to exactly `(n!)⁻¹` — only the identity permutation survives. -/
theorem inner_altProj_tprod_self {x : Fin n → H} (hx : Orthonormal 𝕜 x) :
    inner 𝕜 (altProj 𝕜 n H (tprod 𝕜 x)) (altProj 𝕜 n H (tprod 𝕜 x)) = ((n !) : 𝕜)⁻¹ := by
  rw [inner_altProj_left, altProj_altProj, altProj_tprod, inner_smul_right, inner_sum]
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      inner 𝕜 (tprod 𝕜 x) (permSign 𝕜 σ • tprod 𝕜 fun i => x (σ i))
        = if σ = 1 then (1 : 𝕜) else 0 := by
    intro σ
    rw [inner_smul_right, inner_tprod_perm_of_orthonormal hx σ]
    rcases eq_or_ne σ 1 with rfl | hσ
    · rw [if_pos rfl, mul_one, permSign_one]
    · rw [if_neg hσ, mul_zero]
  rw [Finset.sum_congr rfl fun σ _ => hterm σ,
    Finset.sum_eq_single_of_mem (1 : Equiv.Perm (Fin n)) (Finset.mem_univ _)
      (fun σ _ hσ => if_neg hσ), if_pos rfl, mul_one]

/-- ★ **Slater normalization**: for an orthonormal family `x` the antisymmetrized pure
tensor has squared norm exactly `(n!)⁻¹` — so the Slater determinant `√(n!) • altProj (⨂ₜ x)`
is a unit vector. This pins the Parthasarathy (no-`n!`-rescaling) normalization of the
fermionic sector. -/
theorem norm_sq_altProj_tprod (x : Fin n → H) (hx : Orthonormal 𝕜 x) :
    ‖altProj 𝕜 n H (tprod 𝕜 x)‖ ^ 2 = ((n !) : ℝ)⁻¹ := by
  have hre := congrArg RCLike.re (inner_altProj_tprod_self hx)
  rw [inner_self_eq_norm_sq] at hre
  rw [hre, ← RCLike.ofReal_natCast (K := 𝕜), ← RCLike.ofReal_inv, RCLike.ofReal_re]

/-- For an orthonormal family the antisymmetrized pure tensor is **nonzero**: its squared
norm is `(n!)⁻¹ > 0`. -/
theorem altProj_tprod_ne_zero_of_orthonormal (x : Fin n → H) (hx : Orthonormal 𝕜 x) :
    altProj 𝕜 n H (tprod 𝕜 x) ≠ 0 := by
  intro h0
  have h := norm_sq_altProj_tprod x hx
  rw [h0, norm_zero, zero_pow two_ne_zero] at h
  exact inv_ne_zero (Nat.cast_ne_zero.mpr n.factorial_ne_zero) h.symm

/-- The fermionic sector is nonzero whenever `H` contains `n` orthonormal vectors: it
contains the (Slater) antisymmetrized pure tensor, of squared norm `(n!)⁻¹`. -/
theorem altPower_ne_bot (x : Fin n → H) (hx : Orthonormal 𝕜 x) :
    altPower 𝕜 n H ≠ ⊥ := by
  intro hbot
  have hmem := altProj_mem_altPower (tprod 𝕜 x)
  rw [hbot, Submodule.mem_bot] at hmem
  exact altProj_tprod_ne_zero_of_orthonormal x hx hmem

end HilbertTensorPower

/-! ## The bosonic and fermionic Fock spaces -/

/-- The **bosonic Fock space** over the one-particle space `H`: the Hilbert sum of the
symmetric sectors `symPower 𝕜 n H`. Each sector carries the restricted tensor-power inner
product (Parthasarathy convention, no `n!` rescaling). -/
abbrev boseFock := lp (fun k : ℕ => ↥(HilbertTensorPower.symPower 𝕜 k H)) 2

/-- The **fermionic Fock space** over the one-particle space `H`: the Hilbert sum of the
antisymmetric sectors `altPower 𝕜 n H`, with the same convention as `boseFock`. -/
abbrev fermiFock := lp (fun k : ℕ => ↥(HilbertTensorPower.altPower 𝕜 k H)) 2

-- Sanity: the Hilbert-space structure is found by instance resolution alone.
example : NormedAddCommGroup (boseFock 𝕜 H) := inferInstance
example : InnerProductSpace 𝕜 (boseFock 𝕜 H) := inferInstance
example : CompleteSpace (boseFock 𝕜 H) := inferInstance
example : NormedAddCommGroup (fermiFock 𝕜 H) := inferInstance
example : InnerProductSpace 𝕜 (fermiFock 𝕜 H) := inferInstance
example : CompleteSpace (fermiFock 𝕜 H) := inferInstance

end Spectra
