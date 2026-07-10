/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Spectra.Modular.TomitaTakesaki.Basic
/-!
# RECON SPIKE — `M₂(M)` as a `VonNeumannAlgebra (H ⊕ H)`  (WIP, `sorry` intentional)

This is a **de-risking prototype** for the 2×2 matrix amplification
`M₂(M) = M ⊗ M₂(ℂ)` acting on `H ⊕ H`, the carrier of the Connes RN-cocycle.
The goal is to find the lowest-friction Hilbert-space-direct-sum representation,
prototype block operators / matrix units / the balanced vector, and STATE the
von Neumann algebra and cyclic/separating obligations so the whole thing
typechecks together. `sorry` is deliberate — this file is *evidence*, not product.

## Representation choice: `WithLp 2 (H × H)`

`H2 := WithLp 2 (H × H)` carries all three needed instances **for free** (no
construction required):

* `NormedAddCommGroup (WithLp 2 (H × H))`           — `WithLp.instProdNormedAddCommGroup`
* `InnerProductSpace ℂ (WithLp 2 (H × H))`          — `WithLp.instProdInnerProductSpace`
  (`Mathlib/Analysis/InnerProductSpace/ProdL2.lean`), with the L² inner product
  `⟪x, y⟫ = ⟪x₁, y₁⟫ + ⟪x₂, y₂⟫`.
* `CompleteSpace (WithLp 2 (H × H))`                — `WithLp.instProdCompleteSpace`

This is strictly better than `PiLp 2 (fun _ : Fin 2 => H)`: the `Fin 2` indexing
forces `Fintype`/`DecidableEq` plumbing and `Finset.sum` reasoning at every turn,
whereas `prod` gives honest `.fst`/`.snd` projectors and a ready CLM toolkit
(`WithLp.fstL`, `WithLp.sndL`, `WithLp.prodContinuousLinearEquiv`).

## Block operators ↔ CLM

A bounded operator on `H2` is assembled from four blocks `a b c d : H →L[ℂ] H` by
post/pre-composing with the WithLp projectors and injectors. We use:

* `WithLp.fstL 2 ℂ H H : H2 →L[ℂ] H`  /  `WithLp.sndL 2 ℂ H H : H2 →L[ℂ] H`
  (the L² projectors), and
* `toLp₂ : H × H →L[ℂ] H2`, the inverse of `WithLp.prodContinuousLinearEquiv`,
  to reassemble. `inl₂ x = toLp₂ (x, 0)`, `inr₂ x = toLp₂ (0, x)`.

`blockOp a b c d` then sends `x ↦ toLp₂ (a x₁ + b x₂, c x₁ + d x₂)`.
-/

namespace Spectra.SpikeM2

open scoped InnerProductSpace
open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## 1. The carrier and its instances -/

/-- The amplified Hilbert space `H ⊕ H`, as the L² product. -/
abbrev H2 (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  WithLp 2 (H × H)

-- All three instances resolve by `inferInstance` — confirmed below.
-- (`noncomputable` because the normed/inner instances on `WithLp` are noncomputable;
-- this only confirms *resolution*, the term is never run.)
noncomputable example : NormedAddCommGroup (H2 H) := inferInstance
noncomputable example : InnerProductSpace ℂ (H2 H) := inferInstance
example : CompleteSpace (H2 H) := inferInstance

/-! ## 2. Block operators and the WithLp CLM toolkit -/

/-- Reassemble a pair into `H2` as a CLM (`= (prodContinuousLinearEquiv 2 ℂ H H).symm`). -/
noncomputable def toLp₂ : (H × H) →L[ℂ] H2 H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap

/-- First L² projector `H2 → H`. -/
noncomputable def fst₂ : H2 H →L[ℂ] H := WithLp.fstL 2 ℂ H H
/-- Second L² projector `H2 → H`. -/
noncomputable def snd₂ : H2 H →L[ℂ] H := WithLp.sndL 2 ℂ H H

/-- Inject into the first summand. -/
noncomputable def inl₂ : H →L[ℂ] H2 H := toLp₂ ∘L (.inl ℂ H H)
/-- Inject into the second summand. -/
noncomputable def inr₂ : H →L[ℂ] H2 H := toLp₂ ∘L (.inr ℂ H H)

/-- The block operator with matrix `[[a, b], [c, d]]`:
`(x₁, x₂) ↦ (a x₁ + b x₂, c x₁ + d x₂)`. Built entirely from the WithLp toolkit
so it lands in `H2 H →L[ℂ] H2 H` with no `sorry`. -/
noncomputable def blockOp (a b c d : H →L[ℂ] H) : H2 H →L[ℂ] H2 H :=
  toLp₂ ∘L
    ((a ∘L fst₂ + b ∘L snd₂).prod (c ∘L fst₂ + d ∘L snd₂))

@[simp] lemma blockOp_apply (a b c d : H →L[ℂ] H) (x : H2 H) :
    blockOp a b c d x =
      WithLp.toLp 2 (a (WithLp.fst x) + b (WithLp.snd x),
                     c (WithLp.fst x) + d (WithLp.snd x)) := by
  rfl

/-- The four matrix units `eᵢⱼ` (identity in the `(i,j)` block, zero elsewhere). -/
noncomputable def e₁₁ : H2 H →L[ℂ] H2 H := blockOp 1 0 0 0
noncomputable def e₁₂ : H2 H →L[ℂ] H2 H := blockOp 0 1 0 0
noncomputable def e₂₁ : H2 H →L[ℂ] H2 H := blockOp 0 0 1 0
noncomputable def e₂₂ : H2 H →L[ℂ] H2 H := blockOp 0 0 0 1

/-! ### Algebra of block operators

These are the load-bearing relations. Each reduces to entrywise CLM identities
once `blockOp_comp` / `blockOp_add` / `blockOp_one` are available. I prove the
shape statements; arithmetic discharge is left as `sorry` (the spike's purpose is
to confirm the *statements* typecheck and to gauge the proof shape). -/

/-- Composition is matrix multiplication. THE key algebraic lemma; everything else
(matrix-unit relations, `*`-subalgebra closure) follows from it. Phrased with `*`
(= `∘L` for endomorphisms) so the unital/zero `simp` set fires on the entries. -/
lemma blockOp_comp (a b c d a' b' c' d' : H →L[ℂ] H) :
    blockOp a b c d * blockOp a' b' c' d' =
      blockOp (a * a' + b * c') (a * b' + b * d')
              (c * a' + d * c') (c * b' + d * d') := by
  -- Pointwise: expand both sides via `blockOp_apply`, then `ext`; the L² inner
  -- structure is irrelevant — this is pure linear bookkeeping on `.fst`/`.snd`.
  sorry

lemma blockOp_add (a b c d a' b' c' d' : H →L[ℂ] H) :
    blockOp a b c d + blockOp a' b' c' d' =
      blockOp (a + a') (b + b') (c + c') (d + d') := by
  sorry

lemma blockOp_one : blockOp (1 : H →L[ℂ] H) 0 0 1 = 1 := by
  sorry

/-- The zero block operator is `0`. -/
lemma blockOp_zero : blockOp (0 : H →L[ℂ] H) 0 0 0 = 0 := by
  sorry

/-- `star (blockOp a b c d) = blockOp a⋆ c⋆ b⋆ d⋆` — the conjugate-transpose.
On `H2 H →L H2 H`, `star = adjoint`, and the adjoint of the L² product respects
the block structure. This is what makes `M₂(M)` `*`-closed. -/
lemma blockOp_star (a b c d : H →L[ℂ] H) :
    star (blockOp a b c d) = blockOp (star a) (star c) (star b) (star d) := by
  sorry

/-- Matrix-unit relation `eᵢⱼ * eₖₗ = δⱼₖ eᵢₗ`, the four nonzero instances.
(`*` = `∘L` for endomorphisms.) -/
lemma e₁₁_mul_e₁₁ : (e₁₁ : H2 H →L[ℂ] H2 H) * e₁₁ = e₁₁ := by
  simp [e₁₁, blockOp_comp]
lemma e₁₂_mul_e₂₁ : (e₁₂ : H2 H →L[ℂ] H2 H) * e₂₁ = e₁₁ := by
  simp [e₁₂, e₂₁, e₁₁, blockOp_comp]
lemma e₂₁_mul_e₁₂ : (e₂₁ : H2 H →L[ℂ] H2 H) * e₁₂ = e₂₂ := by
  simp [e₂₁, e₁₂, e₂₂, blockOp_comp]
lemma e₂₂_mul_e₂₂ : (e₂₂ : H2 H →L[ℂ] H2 H) * e₂₂ = e₂₂ := by
  simp [e₂₂, blockOp_comp]

/-- A vanishing instance `e₁₁ * e₂₁ = 0` (`δ₁₂ = 0`). -/
lemma e₁₁_mul_e₂₁ : (e₁₁ : H2 H →L[ℂ] H2 H) * e₂₁ = 0 := by
  simp only [e₁₁, e₂₁, blockOp_comp, mul_one, mul_zero, add_zero]
  exact blockOp_zero

/-- Completeness of the unit: `e₁₁ + e₂₂ = 1`. -/
lemma e₁₁_add_e₂₂ : (e₁₁ : H2 H →L[ℂ] H2 H) + e₂₂ = 1 := by
  rw [e₁₁, e₂₂, blockOp_add]
  simpa using blockOp_one (H := H)

/-! ## 3. `M₂(M)` as a (candidate) von Neumann algebra

We take the **predicate-set** encoding: `M2set M` is the set of block operators
with all four entries in `M`. This is visibly a `*`-subalgebra (closure follows
from `blockOp_comp`/`blockOp_add`/`blockOp_star` plus `M`'s closure), and the
real content is the bicommutant identity `M₂(M)'' = M₂(M)`. -/

/-- The set of block operators whose four entries all lie in `M`. -/
def M2set (M : VonNeumannAlgebra H) : Set (H2 H →L[ℂ] H2 H) :=
  {T | ∃ a ∈ M, ∃ b ∈ M, ∃ c ∈ M, ∃ d ∈ M, T = blockOp a b c d}

/-- `M2set` is a `*`-subalgebra of `H2 H →L[ℂ] H2 H`.
Closure under `+`, `*`, `star`, and `1` all reduce to the block lemmas above
together with `M`'s own membership closure. `algebraMap_mem'` needs
`algebraMap ℂ _ r = blockOp (r•1) 0 0 (r•1)` and `r•1 ∈ M`. -/
noncomputable def M2subalg (M : VonNeumannAlgebra H) :
    StarSubalgebra ℂ (H2 H →L[ℂ] H2 H) where
  carrier := M2set M
  mul_mem' := by
    rintro x y ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ ⟨a', ha', b', hb', c', hc', d', hd', rfl⟩
    refine ⟨_, add_mem (mul_mem ha ha') (mul_mem hb hc'),
            _, add_mem (mul_mem ha hb') (mul_mem hb hd'),
            _, add_mem (mul_mem hc ha') (mul_mem hd hc'),
            _, add_mem (mul_mem hc hb') (mul_mem hd hd'), ?_⟩
    exact blockOp_comp ..
  add_mem' := by
    rintro x y ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ ⟨a', ha', b', hb', c', hc', d', hd', rfl⟩
    exact ⟨_, add_mem ha ha', _, add_mem hb hb', _, add_mem hc hc', _, add_mem hd hd',
      (blockOp_add ..)⟩
  algebraMap_mem' := by
    intro r
    refine ⟨algebraMap ℂ (H →L[ℂ] H) r, ?_, 0, zero_mem _, 0, zero_mem _,
      algebraMap ℂ (H →L[ℂ] H) r, ?_, ?_⟩
    · exact algebraMap_mem M.toStarSubalgebra r
    · exact algebraMap_mem M.toStarSubalgebra r
    · -- `algebraMap ℂ _ r = blockOp (algebraMap ℂ _ r) 0 0 (algebraMap ℂ _ r)`
      sorry
  star_mem' := by
    rintro x ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩
    exact ⟨star a, star_mem ha, star c, star_mem hc, star b, star_mem hb, star d, star_mem hd,
      blockOp_star ..⟩

/-- **The open obligation.** `M₂(M)` is a von Neumann algebra, i.e. its underlying
`*`-subalgebra equals its own double commutant.

The cleanest route is `M₂(M)' = M₂(M')`: the commutant of the amplification is the
amplification of the commutant (because `M₂(ℂ)` is its own commutant inside
`B(H ⊕ H) = B(H) ⊗ M₂(ℂ)`). Applying it twice and using `M'' = M` (which Spectra
*has*, `VonNeumannAlgebra.commutant_commutant`) closes the bicommutant.

Concretely the `centralizer_centralizer'` field below should be discharged by a
lemma `commutant_M2 : M2set M.commutant = Set.centralizer (M2set M)` proved by:
a commutant element `T = blockOp w x y z` must commute with `e₁₂, e₂₁` (forcing
`w = z` block-diagonal-wise and `x = y = 0` ... actually forcing the entries into
a single `M'` element per block), and with `blockOp m 0 0 m` for all `m ∈ M`
(forcing each entry into `M'`). This is the standard "commutant of matrix
amplification" computation and is the real work item. -/
noncomputable def M2 (M : VonNeumannAlgebra H) : VonNeumannAlgebra (H2 H) where
  toStarSubalgebra := M2subalg M
  centralizer_centralizer' := by
    -- Route: reduce to `Set.centralizer (M2set M) = M2set M.commutant`
    -- applied twice, with `M.commutant.commutant = M`.
    sorry

@[simp] lemma mem_M2 {M : VonNeumannAlgebra H} {T : H2 H →L[ℂ] H2 H} :
    T ∈ M2 M ↔ ∃ a ∈ M, ∃ b ∈ M, ∃ c ∈ M, ∃ d ∈ M, T = blockOp a b c d :=
  Iff.rfl

/-! ## 4. The balanced vector and the cyclic/separating statements -/

open Spectra.TomitaTakesaki

/-- The balanced vector `Ω_θ = (Ω_φ, Ω_ψ) ∈ H ⊕ H`. -/
noncomputable def Ωθ (Ωφ Ωψ : H) : H2 H := WithLp.toLp 2 (Ωφ, Ωψ)

/-- STATEMENT: the balanced vector is cyclic for `M₂(M)`. (Typechecks; this is the
property the Connes-cocycle construction needs, true when `Ωφ, Ωψ` are cyclic.) -/
example (M : VonNeumannAlgebra H) (Ωφ Ωψ : H) : Prop :=
  IsCyclic (M2 M) (Ωθ Ωφ Ωψ)

/-- STATEMENT: the balanced vector is separating for `M₂(M)`. -/
example (M : VonNeumannAlgebra H) (Ωφ Ωψ : H) : Prop :=
  IsSeparating (M2 M) (Ωθ Ωφ Ωψ)

/-- A fully-assembled target theorem statement (proof deferred): if `Ωφ` and `Ωψ`
are each cyclic+separating for `M`, the balanced vector is cyclic+separating for
`M₂(M)`. This is the headline lemma `Cocycle/MatrixAmplification.lean` should land. -/
example (M : VonNeumannAlgebra H) (Ωφ Ωψ : H)
    (hφc : IsCyclic M Ωφ) (hψc : IsCyclic M Ωψ)
    (hφs : IsSeparating M Ωφ) (hψs : IsSeparating M Ωψ) :
    IsCyclic (M2 M) (Ωθ Ωφ Ωψ) ∧ IsSeparating (M2 M) (Ωθ Ωφ Ωψ) := by
  sorry

/-- And: a `ModularData` for `(M, ·)` should lift to `(M₂(M), Ω_θ)`. Just the
*shape* — confirms the bundle from `TomitaTakesaki.Basic` composes with `M2`. -/
example (M : VonNeumannAlgebra H) (Ωφ Ωψ : H) :
    ModularData (M2 M) (Ωθ Ωφ Ωψ) → True :=
  fun _ => trivial

end Spectra.SpikeM2
