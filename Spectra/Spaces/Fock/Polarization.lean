/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Fock.BoseFermi
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.Completion

/-!
# Polarization and density of tensor powers in the bosonic sector

The **polarization identity** for the bosonic symmetrizer: expanding the pure tensor with
the same vector `∑_{i ∈ S} x i` in every slot by multilinearity and running
inclusion–exclusion over `S ⊆ Fin n` leaves exactly the bijective slot-assignments, so

`∑_{S ⊆ univ} (-1)^(n - |S|) • ⨂ₜ (∑_{i ∈ S} x i) = ∑_σ ⨂ₜ x∘σ = n! • symProj (⨂ₜ x)`.

Consequently every symmetrized pure tensor lies in the span of the *n*-th tensor powers
`f ⊗ ⋯ ⊗ f` of single vectors, and — combining with density of pure tensors in the full
power and continuity of the symmetrizer — the closed span of those powers is exactly the
bosonic sector `symPower 𝕜 n H`. This is the algebraic core of the exponential-vector
totality theorem (Fock Spaces milestone M3).

## Main results

* `polarization_symProj_tprod` — the polarization identity
  `n! • symProj (⨂ₜ x) = ∑_{S} (-1)^(n-|S|) • ⨂ₜ (∑_{i∈S} x i)`.
* `symProj_tprod_mem_span_powers` — symmetrized pure tensors lie in the span of tensor
  powers of single vectors.
* `topologicalClosure_span_tprod_const` — ★ the closed span of the tensor powers
  `tprod 𝕜 (fun _ => f)` equals `symPower 𝕜 n H` (as submodules of the full power).

## Implementation notes

The combinatorial engine is split into small lemmas: the multilinear expansion
(`tprod_sum_expand`), the inclusion–exclusion kernel (`sum_powerset_neg_one_pow_sub_card`,
reduced by complementation to `Finset.sum_powerset_neg_one_pow_card`), and the collapse of
the sum over bijective slot-assignments to a sum over `Equiv.Perm (Fin n)`
(`filter_bijective_eq_image_perm`).
-/

noncomputable section

open scoped TensorProduct Nat
open PiTensorProduct UniformSpace

namespace Spectra

variable (𝕜 : Type*) (n : ℕ) (H : Type*) [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

namespace HilbertTensorPower

variable {𝕜 n H}

/-! ## The inclusion–exclusion kernel -/

variable (𝕜) in
/-- **Inclusion–exclusion kernel**: summing `(-1)^(n - |S|)` over the supersets `S` of a
fixed `R ⊆ Fin n` gives `1` if `R = univ` and `0` otherwise. Complementation reduces this
to the alternating powerset sum `Finset.sum_powerset_neg_one_pow_card`. -/
theorem sum_powerset_neg_one_pow_sub_card (R : Finset (Fin n)) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        if R ⊆ S then (-1 : 𝕜) ^ (n - S.card) else 0)
      = if R = Finset.univ then 1 else 0 := by
  rw [← Finset.sum_filter]
  have hbij : (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun S => R ⊆ S),
        (-1 : 𝕜) ^ (n - S.card))
      = ∑ U ∈ Rᶜ.powerset, (-1 : 𝕜) ^ U.card :=
    Finset.sum_nbij' (fun S => Sᶜ) (fun U => Uᶜ)
      (fun S hS => Finset.mem_powerset.mpr
        (Finset.compl_subset_compl.mpr (Finset.mem_filter.mp hS).2))
      (fun U hU => Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
          compl_compl R ▸ Finset.compl_subset_compl.mpr (Finset.mem_powerset.mp hU)⟩)
      (fun S _ => compl_compl S) (fun U _ => compl_compl U)
      (fun S _ => by rw [Finset.card_compl, Fintype.card_fin])
  rw [hbij]
  calc ∑ U ∈ Rᶜ.powerset, (-1 : 𝕜) ^ U.card
      = ((∑ U ∈ Rᶜ.powerset, (-1 : ℤ) ^ U.card : ℤ) : 𝕜) := by push_cast; rfl
    _ = ((if Rᶜ = ∅ then 1 else 0 : ℤ) : 𝕜) := by
        rw [Finset.sum_powerset_neg_one_pow_card]
    _ = if R = Finset.univ then 1 else 0 := by
        simp only [Finset.compl_eq_empty_iff, apply_ite (Int.cast : ℤ → 𝕜),
          Int.cast_one, Int.cast_zero]

/-! ## Collapse of bijective slot-assignments to permutations -/

/-- A self-map of `Fin n` has full image iff it is bijective. -/
theorem image_univ_eq_univ_iff_bijective (r : Fin n → Fin n) :
    Finset.image r Finset.univ = Finset.univ ↔ Function.Bijective r := by
  rw [← Finset.coe_inj, Finset.coe_image, Finset.coe_univ, Set.image_univ,
    Set.range_eq_univ]
  exact Finite.surjective_iff_bijective

/-- The bijective self-maps of `Fin n` are exactly the coercions of permutations. -/
theorem filter_bijective_eq_image_perm :
    (Finset.univ.filter fun r : Fin n → Fin n => Function.Bijective r)
      = Finset.image (fun σ : Equiv.Perm (Fin n) => (σ : Fin n → Fin n)) Finset.univ := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hr
    exact ⟨Equiv.ofBijective r hr, rfl⟩
  · rintro ⟨σ, -, rfl⟩
    exact σ.bijective

/-! ## The multilinear expansion -/

/-- Expanding the pure tensor with `∑ i ∈ S, x i` in every slot by multilinearity: it is
the sum of `⨂ₜ x∘r` over all slot-assignments `r` with values in `S`. -/
theorem tprod_sum_expand (S : Finset (Fin n)) (x : Fin n → H) :
    (PiTensorProduct.tprod 𝕜 fun _ : Fin n => ∑ i ∈ S, x i)
      = ∑ r ∈ Fintype.piFinset (fun _ : Fin n => S),
          PiTensorProduct.tprod 𝕜 fun i => x (r i) :=
  (PiTensorProduct.tprod 𝕜).map_sum_finset (fun _ j => x j) fun _ => S

/-- The slot-assignments with values in `S` are the self-maps whose image is inside `S`. -/
theorem piFinset_const_eq_filter (S : Finset (Fin n)) :
    (Fintype.piFinset fun _ : Fin n => S)
      = Finset.univ.filter fun r : Fin n → Fin n => Finset.image r Finset.univ ⊆ S := by
  ext r
  simp [Fintype.mem_piFinset, Finset.image_subset_iff]

/-! ## The algebraic polarization identity -/

/-- **Algebraic polarization**: on the algebraic tensor power, the alternating sum over
`S ⊆ Fin n` of the pure tensors with `∑ i ∈ S, x i` in every slot collapses, by
inclusion–exclusion, to the sum of `⨂ₜ x∘σ` over all permutations `σ`. -/
theorem polarization_sum_perm (x : Fin n → H) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        (-1 : 𝕜) ^ (n - S.card) • PiTensorProduct.tprod 𝕜 fun _ : Fin n => ∑ i ∈ S, x i)
      = ∑ σ : Equiv.Perm (Fin n), PiTensorProduct.tprod 𝕜 fun i => x (σ i) := by
  calc
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        (-1 : 𝕜) ^ (n - S.card) • PiTensorProduct.tprod 𝕜 fun _ : Fin n => ∑ i ∈ S, x i)
        = ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, ∑ r : Fin n → Fin n,
            if Finset.image r Finset.univ ⊆ S
              then (-1 : 𝕜) ^ (n - S.card) • PiTensorProduct.tprod 𝕜 fun i => x (r i)
              else 0 := by
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [tprod_sum_expand S x, Finset.smul_sum, piFinset_const_eq_filter,
            Finset.sum_filter]
    _ = ∑ r : Fin n → Fin n, ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
            if Finset.image r Finset.univ ⊆ S
              then (-1 : 𝕜) ^ (n - S.card) • PiTensorProduct.tprod 𝕜 fun i => x (r i)
              else 0 := Finset.sum_comm
    _ = ∑ r : Fin n → Fin n,
          (if Finset.image r Finset.univ = Finset.univ then (1 : 𝕜) else 0)
            • PiTensorProduct.tprod 𝕜 fun i => x (r i) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [← sum_powerset_neg_one_pow_sub_card 𝕜 (Finset.image r Finset.univ),
            Finset.sum_smul]
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [ite_smul, zero_smul]
    _ = ∑ r : Fin n → Fin n,
          if Function.Bijective r then PiTensorProduct.tprod 𝕜 fun i => x (r i) else 0 := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [ite_smul, one_smul, zero_smul]
          exact if_congr (image_univ_eq_univ_iff_bijective r) rfl rfl
    _ = ∑ r ∈ Finset.univ.filter fun r : Fin n → Fin n => Function.Bijective r,
          PiTensorProduct.tprod 𝕜 fun i => x (r i) := (Finset.sum_filter _ _).symm
    _ = ∑ σ : Equiv.Perm (Fin n), PiTensorProduct.tprod 𝕜 fun i => x (σ i) := by
          rw [filter_bijective_eq_image_perm,
            Finset.sum_image fun σ _ τ _ h => Equiv.coe_fn_injective h]

/-! ## Transfer to the Hilbert tensor power -/

/-- The coercion into the completion commutes with finite sums. -/
theorem coe_sum {ι : Type*} (s : Finset ι) (f : ι → ⨂[𝕜]^n H) :
    ((↑(∑ a ∈ s, f a) : HilbertTensorPower 𝕜 n H))
      = ∑ a ∈ s, (↑(f a) : HilbertTensorPower 𝕜 n H) := by
  have h := map_sum (Completion.toComplₗᵢ (𝕜 := 𝕜) (E := ⨂[𝕜]^n H)) f s
  simpa only [Completion.coe_toComplₗᵢ] using h

/-- ★ **Polarization identity for the symmetrizer**: on the Hilbert tensor power,

`n! • symProj (⨂ₜ x) = ∑_{S ⊆ Fin n} (-1)^(n - |S|) • ⨂ₜ (∑_{i ∈ S} x i)`.

Every slot of each summand on the right carries the *same* vector `∑ i ∈ S, x i`, so the
right-hand side is a combination of `n`-th tensor powers of single vectors. -/
theorem polarization_symProj_tprod (x : Fin n → H) :
    (n ! : 𝕜) • symProj 𝕜 n H (tprod 𝕜 x)
      = ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          (-1 : 𝕜) ^ (n - S.card) • tprod 𝕜 fun _ : Fin n => ∑ i ∈ S, x i := by
  rw [symProj_tprod, smul_smul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), one_smul]
  calc (∑ σ : Equiv.Perm (Fin n), tprod 𝕜 fun i => x (σ i))
      = (↑(∑ σ : Equiv.Perm (Fin n), PiTensorProduct.tprod 𝕜 fun i => x (σ i)) :
          HilbertTensorPower 𝕜 n H) := (coe_sum _ _).symm
    _ = (↑(∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
            (-1 : 𝕜) ^ (n - S.card) • PiTensorProduct.tprod 𝕜 fun _ : Fin n => ∑ i ∈ S, x i) :
          HilbertTensorPower 𝕜 n H) := by rw [polarization_sum_perm]
    _ = ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          (-1 : 𝕜) ^ (n - S.card) • tprod 𝕜 fun _ : Fin n => ∑ i ∈ S, x i := by
        rw [coe_sum]
        exact Finset.sum_congr rfl fun S _ => Completion.coe_smul _ _

/-! ## Density of tensor powers in the bosonic sector -/

/-- ★ Symmetrized pure tensors lie in the span of the `n`-th tensor powers of single
vectors: divide the polarization identity by `n!`. -/
theorem symProj_tprod_mem_span_powers (x : Fin n → H) :
    symProj 𝕜 n H (tprod 𝕜 x)
      ∈ Submodule.span 𝕜 (Set.range fun f : H => tprod 𝕜 fun _ : Fin n => f) := by
  have hn : (n ! : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have h : symProj 𝕜 n H (tprod 𝕜 x)
      = (n ! : 𝕜)⁻¹ • ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          (-1 : 𝕜) ^ (n - S.card) • tprod 𝕜 fun _ : Fin n => ∑ i ∈ S, x i := by
    rw [← polarization_symProj_tprod, smul_smul, inv_mul_cancel₀ hn, one_smul]
  rw [h]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun S _ => Submodule.smul_mem _ _ ?_)
  exact Submodule.subset_span ⟨∑ i ∈ S, x i, rfl⟩

variable (𝕜 n H) in
/-- ★★ **Density of tensor powers in the bosonic sector**: the topological closure of the
span of the `n`-th tensor powers `f ⊗ ⋯ ⊗ f` of single vectors is exactly `symPower 𝕜 n H`
(as submodules of the full Hilbert tensor power).

Forward: each power is bosonic and the sector is closed. Reverse: a bosonic `y` is
`symProj y`; pure tensors are dense in the full power, `symProj` is continuous, and by
`symProj_tprod_mem_span_powers` it maps their span into the span of powers. -/
theorem topologicalClosure_span_tprod_const :
    (Submodule.span 𝕜 (Set.range fun f : H => tprod 𝕜 fun _ : Fin n => f)).topologicalClosure
      = symPower 𝕜 n H := by
  have hmap : ∀ z ∈ Submodule.span 𝕜 (Set.range fun w : Fin n → H => tprod 𝕜 w),
      symProj 𝕜 n H z
        ∈ Submodule.span 𝕜 (Set.range fun f : H => tprod 𝕜 fun _ : Fin n => f) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨v, rfl⟩ := hw
        exact symProj_tprod_mem_span_powers v
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  refine le_antisymm
    (Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_)
      (isClosed_symPower 𝕜 n H)) ?_
  · rintro _ ⟨f, rfl⟩
    exact tprod_const_mem_symPower f
  · intro y hy
    have hy' : symProj 𝕜 n H y = y := mem_symPower_iff.mp hy
    have h1 : y ∈ closure (Submodule.span 𝕜 (Set.range fun w : Fin n → H => tprod 𝕜 w) :
        Set (HilbertTensorPower 𝕜 n H)) := dense_span_tprod y
    have h2 : symProj 𝕜 n H y ∈ closure (⇑(symProj 𝕜 n H) ''
        (Submodule.span 𝕜 (Set.range fun w : Fin n → H => tprod 𝕜 w) :
          Set (HilbertTensorPower 𝕜 n H))) :=
      image_closure_subset_closure_image (symProj 𝕜 n H).continuous ⟨y, h1, rfl⟩
    have h3 : (⇑(symProj 𝕜 n H) ''
        (Submodule.span 𝕜 (Set.range fun w : Fin n → H => tprod 𝕜 w) :
          Set (HilbertTensorPower 𝕜 n H)))
        ⊆ (Submodule.span 𝕜 (Set.range fun f : H => tprod 𝕜 fun _ : Fin n => f) :
            Set (HilbertTensorPower 𝕜 n H)) := by
      rintro _ ⟨z, hz, rfl⟩
      exact hmap z hz
    have h4 := closure_mono h3 h2
    rw [hy'] at h4
    rwa [← SetLike.mem_coe, Submodule.topologicalClosure_coe]

end HilbertTensorPower

end Spectra
