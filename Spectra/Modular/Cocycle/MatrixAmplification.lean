/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Spectra.Modular.TomitaTakesaki.Basic
/-!
# The `2 × 2` matrix amplification `M₂(M)` (M4)

The Connes Radon–Nikodym cocycle `(Dφ : Dψ)_t` is read off the modular flow of the **balanced
state** on the `2 × 2` amplification `M₂(M) = M ⊗ M₂(ℂ)`, acting on `H ⊕ H`.  This file builds the
carrier of that amplification: block operators on the `L²` direct sum `H2 H := WithLp 2 (H × H)`,
their arithmetic, the matrix units `eᵢⱼ`, and the `*`-subalgebra `M2subalg M` of block operators
whose four entries all lie in `M`.

## Representation choice: `WithLp 2 (H × H)`

`H2 H := WithLp 2 (H × H)` carries `NormedAddCommGroup`, `InnerProductSpace ℂ`, and `CompleteSpace`
**for free** (all by `inferInstance`), with the `L²` inner product
`⟪x, y⟫ = ⟪x.1, y.1⟫ + ⟪x.2, y.2⟫`
(`WithLp.prod_inner_apply`).  This beats `PiLp 2 (fun _ : Fin 2 => H)`: the `Fin 2` indexing forces
`Fintype`/`Finset.sum` plumbing at every turn, whereas `prod` gives honest `.fst`/`.snd` projectors
and a ready `WithLp` continuous-linear-map toolkit.

## Block operators

`blockOp a b c d` is the operator with matrix `[[a, b], [c, d]]`,
`(x₁, x₂) ↦ (a x₁ + b x₂, c x₁ + d x₂)`, assembled from the `WithLp` projectors/injectors so
it lands
in `H2 H →L[ℂ] H2 H` with no side conditions.  The load-bearing facts are the ring/`*` structure:

* `blockOp_comp` — composition is matrix multiplication (THE key lemma);
* `blockOp_add`, `blockOp_smul`, `blockOp_zero`, `blockOp_one` — linear/unital structure;
* `blockOp_star` — `star (blockOp a b c d) = blockOp a⋆ c⋆ b⋆ d⋆`, the conjugate transpose
  (`star = adjoint` on `H2 H →L[ℂ] H2 H`).

From these the matrix-unit relations `eᵢⱼ eₖₗ = δⱼₖ eᵢₗ`, `e₁₁ + e₂₂ = 1`, and the `*`-subalgebra
closure all fall out.  The remaining content — the bicommutant `M₂(M)'' = M₂(M)` making `M2subalg M`
a genuine `VonNeumannAlgebra (H2 H)` — is a separate (gate-independent) build.
-/

namespace Spectra.TomitaTakesaki

open scoped InnerProductSpace
open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## 1. The carrier and its instances -/

/-- The amplified Hilbert space `H ⊕ H`, as the `L²` product `WithLp 2 (H × H)`. -/
abbrev H2 (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  WithLp 2 (H × H)

-- All three instances resolve by `inferInstance`.
noncomputable example : NormedAddCommGroup (H2 H) := inferInstance
noncomputable example : InnerProductSpace ℂ (H2 H) := inferInstance
example : CompleteSpace (H2 H) := inferInstance

/-! ## 2. Block operators and the `WithLp` CLM toolkit -/

/-- Reassemble a pair into `H2 H` as a CLM (`= (prodContinuousLinearEquiv 2 ℂ H H).symm`). -/
noncomputable def toLp₂ : (H × H) →L[ℂ] H2 H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap

/-- First `L²` projector `H2 H → H`. -/
noncomputable def fst₂ : H2 H →L[ℂ] H := WithLp.fstL 2 ℂ H H
/-- Second `L²` projector `H2 H → H`. -/
noncomputable def snd₂ : H2 H →L[ℂ] H := WithLp.sndL 2 ℂ H H

/-- Inject into the first summand. -/
noncomputable def inl₂ : H →L[ℂ] H2 H := toLp₂ ∘L (.inl ℂ H H)
/-- Inject into the second summand. -/
noncomputable def inr₂ : H →L[ℂ] H2 H := toLp₂ ∘L (.inr ℂ H H)

/-- The block operator with matrix `[[a, b], [c, d]]`:
`(x₁, x₂) ↦ (a x₁ + b x₂, c x₁ + d x₂)`. -/
noncomputable def blockOp (a b c d : H →L[ℂ] H) : H2 H →L[ℂ] H2 H :=
  toLp₂ ∘L
    ((a ∘L fst₂ + b ∘L snd₂).prod (c ∘L fst₂ + d ∘L snd₂))

@[simp] lemma blockOp_apply (a b c d : H →L[ℂ] H) (x : H2 H) :
    blockOp a b c d x =
      WithLp.toLp 2 (a (WithLp.fst x) + b (WithLp.snd x),
                     c (WithLp.fst x) + d (WithLp.snd x)) :=
  rfl

/-! ### Algebra of block operators

These are the load-bearing relations: composition is matrix multiplication, and the linear/`*`
structure is entrywise.  Each is a short pointwise computation on the `L²` product. -/

/-- Composition is matrix multiplication. THE key algebraic lemma; everything else (matrix-unit
relations, `*`-subalgebra closure) follows from it. Phrased with `*` (`= ∘L` for endomorphisms). -/
lemma blockOp_comp (a b c d a' b' c' d' : H →L[ℂ] H) :
    blockOp a b c d * blockOp a' b' c' d' =
      blockOp (a * a' + b * c') (a * b' + b * d')
              (c * a' + d * c') (c * b' + d * d') := by
  ext x
  simp only [ContinuousLinearMap.mul_apply, blockOp_apply, WithLp.toLp_fst, WithLp.toLp_snd,
    ContinuousLinearMap.add_apply, map_add]
  refine congrArg (WithLp.toLp 2) ?_
  rw [Prod.mk.injEq]
  exact ⟨by abel, by abel⟩

/-- Addition is entrywise. -/
lemma blockOp_add (a b c d a' b' c' d' : H →L[ℂ] H) :
    blockOp a b c d + blockOp a' b' c' d' =
      blockOp (a + a') (b + b') (c + c') (d + d') := by
  ext x
  simp only [ContinuousLinearMap.add_apply, blockOp_apply, ← WithLp.toLp_add, Prod.mk_add_mk]
  refine congrArg (WithLp.toLp 2) ?_
  rw [Prod.mk.injEq]
  exact ⟨by abel, by abel⟩

/-- Scalar multiplication is entrywise. -/
lemma blockOp_smul (r : ℂ) (a b c d : H →L[ℂ] H) :
    r • blockOp a b c d = blockOp (r • a) (r • b) (r • c) (r • d) := by
  ext x
  simp only [ContinuousLinearMap.smul_apply, blockOp_apply, ← WithLp.toLp_smul, Prod.smul_mk,
    smul_add]

/-- The zero block operator is `0`. -/
@[simp] lemma blockOp_zero : blockOp (0 : H →L[ℂ] H) 0 0 0 = 0 := by
  ext x
  simp [blockOp_apply]

/-- The block operator `[[1, 0], [0, 1]]` is the identity. -/
@[simp] lemma blockOp_one : blockOp (1 : H →L[ℂ] H) 0 0 1 = 1 := by
  ext x
  simp only [blockOp_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.zero_apply,
    add_zero, zero_add, WithLp.fst, WithLp.snd, Prod.mk.eta, WithLp.toLp_ofLp]

/-- `star (blockOp a b c d) = blockOp a⋆ c⋆ b⋆ d⋆` — the conjugate transpose.  On `H2 H →L[ℂ] H2 H`,
`star = adjoint`, and the adjoint of the `L²` product respects the block structure; this is what
makes `M₂(M)` `*`-closed. -/
lemma blockOp_star (a b c d : H →L[ℂ] H) :
    star (blockOp a b c d) = blockOp (star a) (star c) (star b) (star d) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [blockOp_apply, WithLp.prod_inner_apply, WithLp.fst, WithLp.snd,
    inner_add_left, inner_add_right, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]
  ring

/-! ## 3. The matrix units `eᵢⱼ` -/

/-- The four matrix units `eᵢⱼ` (identity in the `(i, j)` block, zero elsewhere). -/
noncomputable def e₁₁ : H2 H →L[ℂ] H2 H := blockOp 1 0 0 0
noncomputable def e₁₂ : H2 H →L[ℂ] H2 H := blockOp 0 1 0 0
noncomputable def e₂₁ : H2 H →L[ℂ] H2 H := blockOp 0 0 1 0
noncomputable def e₂₂ : H2 H →L[ℂ] H2 H := blockOp 0 0 0 1

/-- Matrix-unit relation `e₁₁ e₁₁ = e₁₁`. -/
lemma e₁₁_mul_e₁₁ : (e₁₁ : H2 H →L[ℂ] H2 H) * e₁₁ = e₁₁ := by
  simp [e₁₁, blockOp_comp]
/-- Matrix-unit relation `e₁₂ e₂₁ = e₁₁`. -/
lemma e₁₂_mul_e₂₁ : (e₁₂ : H2 H →L[ℂ] H2 H) * e₂₁ = e₁₁ := by
  simp [e₁₂, e₂₁, e₁₁, blockOp_comp]
/-- Matrix-unit relation `e₂₁ e₁₂ = e₂₂`. -/
lemma e₂₁_mul_e₁₂ : (e₂₁ : H2 H →L[ℂ] H2 H) * e₁₂ = e₂₂ := by
  simp [e₂₁, e₁₂, e₂₂, blockOp_comp]
/-- Matrix-unit relation `e₂₂ e₂₂ = e₂₂`. -/
lemma e₂₂_mul_e₂₂ : (e₂₂ : H2 H →L[ℂ] H2 H) * e₂₂ = e₂₂ := by
  simp [e₂₂, blockOp_comp]

/-- A vanishing instance `e₁₁ e₂₁ = 0` (`δ₁₂ = 0`). -/
lemma e₁₁_mul_e₂₁ : (e₁₁ : H2 H →L[ℂ] H2 H) * e₂₁ = 0 := by
  simp only [e₁₁, e₂₁, blockOp_comp, mul_one, mul_zero, add_zero, blockOp_zero]

/-- Completeness of the unit: `e₁₁ + e₂₂ = 1`. -/
lemma e₁₁_add_e₂₂ : (e₁₁ : H2 H →L[ℂ] H2 H) + e₂₂ = 1 := by
  rw [e₁₁, e₂₂, blockOp_add]
  simp

/-- `star (e₁₂) = e₂₁`: the matrix units `e₁₂` and `e₂₁` are adjoint. -/
lemma star_e₁₂ : star (e₁₂ : H2 H →L[ℂ] H2 H) = e₂₁ := by
  simp [e₁₂, e₂₁, blockOp_star]
/-- `star (e₂₁) = e₁₂`. -/
lemma star_e₂₁ : star (e₂₁ : H2 H →L[ℂ] H2 H) = e₁₂ := by
  simp [e₁₂, e₂₁, blockOp_star]

/-! ## 4. `M₂(M)` as a `*`-subalgebra

`M2set M` is the set of block operators with all four entries in `M`.  It is visibly a
`*`-subalgebra (closure follows from `blockOp_comp`/`blockOp_add`/`blockOp_star` plus `M`'s own
closure).  The real remaining content is the bicommutant identity `M₂(M)'' = M₂(M)`, deferred to a
separate build. -/

/-- The set of block operators whose four entries all lie in `M`. -/
def M2set (M : VonNeumannAlgebra H) : Set (H2 H →L[ℂ] H2 H) :=
  {T | ∃ a ∈ M, ∃ b ∈ M, ∃ c ∈ M, ∃ d ∈ M, T = blockOp a b c d}

/-- `M2set M` is a `*`-subalgebra of `H2 H →L[ℂ] H2 H`.  Closure under `+`, `*`, `star`, and the
unit/scalars all reduce to the block lemmas above together with `M`'s membership closure. -/
noncomputable def M2subalg (M : VonNeumannAlgebra H) :
    StarSubalgebra ℂ (H2 H →L[ℂ] H2 H) where
  carrier := M2set M
  mul_mem' := by
    rintro x y ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ ⟨a', ha', b', hb', c', hc', d', hd', rfl⟩
    exact ⟨_, add_mem (mul_mem ha ha') (mul_mem hb hc'),
           _, add_mem (mul_mem ha hb') (mul_mem hb hd'),
           _, add_mem (mul_mem hc ha') (mul_mem hd hc'),
           _, add_mem (mul_mem hc hb') (mul_mem hd hd'), blockOp_comp ..⟩
  add_mem' := by
    rintro x y ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ ⟨a', ha', b', hb', c', hc', d', hd', rfl⟩
    exact ⟨_, add_mem ha ha', _, add_mem hb hb', _, add_mem hc hc', _, add_mem hd hd',
      blockOp_add ..⟩
  algebraMap_mem' := by
    intro r
    refine ⟨algebraMap ℂ (H →L[ℂ] H) r, algebraMap_mem M.toStarSubalgebra r,
      0, zero_mem _, 0, zero_mem _,
      algebraMap ℂ (H →L[ℂ] H) r, algebraMap_mem M.toStarSubalgebra r, ?_⟩
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [← blockOp_one, blockOp_smul, smul_zero]
  star_mem' := by
    rintro x ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩
    exact ⟨star a, star_mem ha, star c, star_mem hc, star b, star_mem hb, star d, star_mem hd,
      blockOp_star ..⟩

@[simp] lemma mem_M2subalg {M : VonNeumannAlgebra H} {T : H2 H →L[ℂ] H2 H} :
    T ∈ M2subalg M ↔ ∃ a ∈ M, ∃ b ∈ M, ∃ c ∈ M, ∃ d ∈ M, T = blockOp a b c d :=
  Iff.rfl

/-- The matrix units lie in `M₂(M)` (their entries are `0` and `1 ∈ M`). -/
lemma e₁₁_mem_M2subalg (M : VonNeumannAlgebra H) : (e₁₁ : H2 H →L[ℂ] H2 H) ∈ M2subalg M :=
  ⟨1, one_mem _, 0, zero_mem _, 0, zero_mem _, 0, zero_mem _, rfl⟩
lemma e₁₂_mem_M2subalg (M : VonNeumannAlgebra H) : (e₁₂ : H2 H →L[ℂ] H2 H) ∈ M2subalg M :=
  ⟨0, zero_mem _, 1, one_mem _, 0, zero_mem _, 0, zero_mem _, rfl⟩
lemma e₂₁_mem_M2subalg (M : VonNeumannAlgebra H) : (e₂₁ : H2 H →L[ℂ] H2 H) ∈ M2subalg M :=
  ⟨0, zero_mem _, 0, zero_mem _, 1, one_mem _, 0, zero_mem _, rfl⟩
lemma e₂₂_mem_M2subalg (M : VonNeumannAlgebra H) : (e₂₂ : H2 H →L[ℂ] H2 H) ∈ M2subalg M :=
  ⟨0, zero_mem _, 0, zero_mem _, 0, zero_mem _, 1, one_mem _, rfl⟩

/-! ## 5. The bicommutant `M₂(M)'' = M₂(M)`

The remaining content promised above: `M2subalg M` is a genuine `VonNeumannAlgebra (H2 H)`.

The mathematics is `M₂(M) = M ⊗ M₂(ℂ)` on `H ⊗ ℂ² = H ⊕ H`.  Because `M₂(ℂ)' = ℂ·1₂` inside
`B(ℂ²)`, the commutant of `M₂(M)` is **not** `M₂(M')` but the *scalar blocks* `M' ⊗ 1₂`, i.e.
operators `blockOp w 0 0 w` with `w ∈ M'`.  Taking the commutant once more returns `M₂(M'')= M₂(M)`.
We prove the two set-equalities

* `centralizer_M2set`         : `(M2set M)ᶜᵉⁿᵗ = scalarBlockSet M'`,
* `centralizer_scalarBlockSet`: `(scalarBlockSet N)ᶜᵉⁿᵗ = M2set N'`,

and chain them with `VonNeumannAlgebra.commutant_commutant`. -/

/-! ### Structural helper lemmas: reading entries off a block operator -/

@[simp] lemma fst₂_apply (x : H2 H) : (fst₂ : H2 H →L[ℂ] H) x = WithLp.fst x := rfl

@[simp] lemma snd₂_apply (x : H2 H) : (snd₂ : H2 H →L[ℂ] H) x = WithLp.snd x := rfl

@[simp] lemma inl₂_apply (u : H) : (inl₂ : H →L[ℂ] H2 H) u = WithLp.toLp 2 (u, 0) := rfl

@[simp] lemma inr₂_apply (u : H) : (inr₂ : H →L[ℂ] H2 H) u = WithLp.toLp 2 (0, u) := rfl

/-- `blockOp` acting on the first injector reads off the first column `(a, c)`. -/
@[simp] lemma blockOp_inl₂ (a b c d : H →L[ℂ] H) (u : H) :
    blockOp a b c d (inl₂ u) = WithLp.toLp 2 (a u, c u) := by
  simp [blockOp_apply, inl₂_apply, WithLp.toLp_fst, WithLp.toLp_snd]

/-- `blockOp` acting on the second injector reads off the second column `(b, d)`. -/
@[simp] lemma blockOp_inr₂ (a b c d : H →L[ℂ] H) (u : H) :
    blockOp a b c d (inr₂ u) = WithLp.toLp 2 (b u, d u) := by
  simp [blockOp_apply, inr₂_apply, WithLp.toLp_fst, WithLp.toLp_snd]

/-- Reassembling the components of `z : H2 H` recovers `z`. -/
lemma H2_eta (z : H2 H) : WithLp.toLp 2 (WithLp.fst z, WithLp.snd z) = z := by
  simp only [WithLp.fst, WithLp.snd, Prod.mk.eta, WithLp.toLp_ofLp]

/-- The `(1,1)` entry: `fst₂ ∘L blockOp a b c d ∘L inl₂ = a`. -/
lemma fst₂_blockOp_inl₂ (a b c d : H →L[ℂ] H) :
    fst₂ ∘L blockOp a b c d ∘L inl₂ = a := by
  ext u; simp [fst₂_apply, WithLp.toLp_fst]

/-- The `(1,2)` entry: `fst₂ ∘L blockOp a b c d ∘L inr₂ = b`. -/
lemma fst₂_blockOp_inr₂ (a b c d : H →L[ℂ] H) :
    fst₂ ∘L blockOp a b c d ∘L inr₂ = b := by
  ext u; simp [fst₂_apply, WithLp.toLp_fst]

/-- The `(2,1)` entry: `snd₂ ∘L blockOp a b c d ∘L inl₂ = c`. -/
lemma snd₂_blockOp_inl₂ (a b c d : H →L[ℂ] H) :
    snd₂ ∘L blockOp a b c d ∘L inl₂ = c := by
  ext u; simp [snd₂_apply, WithLp.toLp_snd]

/-- The `(2,2)` entry: `snd₂ ∘L blockOp a b c d ∘L inr₂ = d`. -/
lemma snd₂_blockOp_inr₂ (a b c d : H →L[ℂ] H) :
    snd₂ ∘L blockOp a b c d ∘L inr₂ = d := by
  ext u; simp [snd₂_apply, WithLp.toLp_snd]

/-- **Every** operator on `H2 H` is a block operator: reconstruct it from its four entries.
This is the structural crux that lets us reduce operator equations to entrywise equations. -/
lemma eq_blockOp (T : H2 H →L[ℂ] H2 H) :
    T = blockOp (fst₂ ∘L T ∘L inl₂) (fst₂ ∘L T ∘L inr₂)
                (snd₂ ∘L T ∘L inl₂) (snd₂ ∘L T ∘L inr₂) := by
  ext x
  have hx : inl₂ (WithLp.fst x) + inr₂ (WithLp.snd x) = x := by
    simp only [inl₂_apply, inr₂_apply, ← WithLp.toLp_add, Prod.mk_add_mk, add_zero, zero_add,
      WithLp.fst, WithLp.snd, Prod.mk.eta, WithLp.toLp_ofLp]
  rw [blockOp_apply]
  simp only [ContinuousLinearMap.comp_apply, fst₂_apply, snd₂_apply]
  nth_rewrite 1 [← hx]
  rw [map_add]
  rw [← Prod.mk_add_mk, WithLp.toLp_add, H2_eta, H2_eta]

/-- Injectivity of `blockOp`: equal block operators have equal entries. -/
lemma blockOp_inj {a b c d a' b' c' d' : H →L[ℂ] H}
    (h : blockOp a b c d = blockOp a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := congrArg (fun S => fst₂ ∘L S ∘L inl₂) h
    simpa only [fst₂_blockOp_inl₂] using this
  · have := congrArg (fun S => fst₂ ∘L S ∘L inr₂) h
    simpa only [fst₂_blockOp_inr₂] using this
  · have := congrArg (fun S => snd₂ ∘L S ∘L inl₂) h
    simpa only [snd₂_blockOp_inl₂] using this
  · have := congrArg (fun S => snd₂ ∘L S ∘L inr₂) h
    simpa only [snd₂_blockOp_inr₂] using this

/-! ### The scalar-block set and the two centralizer identities -/

/-- The set of scalar block operators `blockOp w 0 0 w` with `w ∈ N`; this is `N ⊗ 1₂`. -/
def scalarBlockSet (N : VonNeumannAlgebra H) : Set (H2 H →L[ℂ] H2 H) :=
  {T | ∃ w ∈ N, T = blockOp w 0 0 w}

/-- **L1.** The commutant of `M₂(M)` is the scalar blocks `M' ⊗ 1₂`. -/
lemma centralizer_M2set (M : VonNeumannAlgebra H) :
    Set.centralizer (M2set M) = scalarBlockSet M.commutant := by
  ext T
  rw [Set.mem_centralizer_iff]
  constructor
  · -- `T` commutes with all of `M₂(M)` ⟹ `T` is a scalar block with entry in `M'`.
    intro hT
    -- Name the four entries and record the block decomposition of `T`.
    set T₁₁ := fst₂ ∘L T ∘L inl₂ with _hT₁₁
    set T₁₂ := fst₂ ∘L T ∘L inr₂ with _hT₁₂
    set T₂₁ := snd₂ ∘L T ∘L inl₂ with _hT₂₁
    set T₂₂ := snd₂ ∘L T ∘L inr₂ with _hT₂₂
    have hEq : T = blockOp T₁₁ T₁₂ T₂₁ T₂₂ := eq_blockOp T
    -- Commute with `e₁₂ = blockOp 0 1 0 0`.
    have h12 := hT e₁₂ (e₁₂_mem_M2subalg M)
    rw [hEq, e₁₂, blockOp_comp, blockOp_comp] at h12
    simp only [mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add] at h12
    obtain ⟨hA, hB, _hC, _hD⟩ := blockOp_inj h12
    -- From `e₁₂ * T = T * e₁₂`: forces `T₂₁ = 0`, `T₂₂ = T₁₁`.
    -- Commute with `e₂₁ = blockOp 0 0 1 0`.
    have h21 := hT e₂₁ (e₂₁_mem_M2subalg M)
    rw [hEq, e₂₁, blockOp_comp, blockOp_comp] at h21
    simp only [mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add] at h21
    obtain ⟨_hA', _hB', _hC', hD'⟩ := blockOp_inj h21
    -- Collect: `T₁₂ = 0`, `T₂₁ = 0`, `T₁₁ = T₂₂`.
    refine ⟨T₁₁, ?_, ?_⟩
    · -- `T₁₁ ∈ M'`: it commutes with every `m ∈ M`.
      rw [VonNeumannAlgebra.mem_commutant_iff]
      intro m hm
      -- Commute with `blockOp m 0 0 m ∈ M₂(M)`.
      have hm2 : blockOp m 0 0 m ∈ M2set M :=
        ⟨m, hm, 0, zero_mem _, 0, zero_mem _, m, hm, rfl⟩
      have hmT := hT _ hm2
      rw [hEq, blockOp_comp, blockOp_comp] at hmT
      simp only [mul_zero, zero_mul, add_zero, zero_add] at hmT
      obtain ⟨h1, _, _, _⟩ := blockOp_inj hmT
      exact h1
    · -- `T = blockOp T₁₁ 0 0 T₁₁`.
      -- From h12: hA : T₂₁ = 0, hB : T₂₂ = T₁₁. From h21: hD' : T₁₂ = 0.
      rw [hEq, hD', hA, hB]
  · -- `T = blockOp w 0 0 w`, `w ∈ M'` ⟹ `T` commutes with all of `M₂(M)`.
    rintro ⟨w, hw, rfl⟩ S ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩
    rw [VonNeumannAlgebra.mem_commutant_iff] at hw
    rw [blockOp_comp, blockOp_comp]
    simp only [mul_zero, zero_mul, add_zero, zero_add]
    rw [hw a ha, hw b hb, hw c hc, hw d hd]

/-- **L2.** The commutant of the scalar blocks `N ⊗ 1₂` is `M₂(N')`. -/
lemma centralizer_scalarBlockSet (N : VonNeumannAlgebra H) :
    Set.centralizer (scalarBlockSet N) = M2set N.commutant := by
  ext T
  rw [Set.mem_centralizer_iff]
  constructor
  · -- `T` commutes with all scalar blocks ⟹ each entry of `T` lies in `N'`.
    intro hT
    set T₁₁ := fst₂ ∘L T ∘L inl₂ with _hT₁₁
    set T₁₂ := fst₂ ∘L T ∘L inr₂ with _hT₁₂
    set T₂₁ := snd₂ ∘L T ∘L inl₂ with _hT₂₁
    set T₂₂ := snd₂ ∘L T ∘L inr₂ with _hT₂₂
    have hEq : T = blockOp T₁₁ T₁₂ T₂₁ T₂₂ := eq_blockOp T
    refine ⟨T₁₁, ?_, T₁₂, ?_, T₂₁, ?_, T₂₂, ?_, hEq⟩ <;>
    · rw [VonNeumannAlgebra.mem_commutant_iff]
      intro w hw
      have hw2 : (blockOp w 0 0 w : H2 H →L[ℂ] H2 H) ∈ scalarBlockSet N := ⟨w, hw, rfl⟩
      have hwT := hT _ hw2
      rw [hEq, blockOp_comp, blockOp_comp] at hwT
      simp only [mul_zero, zero_mul, add_zero, zero_add] at hwT
      obtain ⟨h1, h2, h3, h4⟩ := blockOp_inj hwT
      first
        | exact h1 | exact h2 | exact h3 | exact h4
  · -- `T = blockOp a b c d` with all entries in `N'` ⟹ commutes with scalar blocks.
    rintro ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ S ⟨w, hw, rfl⟩
    rw [VonNeumannAlgebra.mem_commutant_iff] at ha hb hc hd
    rw [blockOp_comp, blockOp_comp]
    simp only [mul_zero, zero_mul, add_zero, zero_add]
    rw [ha w hw, hb w hw, hc w hw, hd w hw]

/-! ### The `VonNeumannAlgebra` instance -/

/-- The `2 × 2` matrix amplification `M₂(M) = M ⊗ M₂(ℂ)` as a genuine `VonNeumannAlgebra (H2 H)`.
Its carrier is `M2set M` (block operators with all four entries in `M`); the bicommutant identity
`M₂(M)'' = M₂(M)` is discharged via the two scalar-block centralizer computations and
`VonNeumannAlgebra.commutant_commutant`. -/
noncomputable def M2 (M : VonNeumannAlgebra H) : VonNeumannAlgebra (H2 H) where
  toStarSubalgebra := M2subalg M
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer (M2set M)) = M2set M
    rw [centralizer_M2set, centralizer_scalarBlockSet, VonNeumannAlgebra.commutant_commutant]

@[simp] lemma mem_M2 {M : VonNeumannAlgebra H} {T : H2 H →L[ℂ] H2 H} :
    T ∈ M2 M ↔ ∃ a ∈ M, ∃ b ∈ M, ∃ c ∈ M, ∃ d ∈ M, T = blockOp a b c d :=
  Iff.rfl

end Spectra.TomitaTakesaki
