/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.CayleyTransform.Generator.Stone   -- stoneGroup, stoneExp, generator_stoneGroup
import Spectra.YosidaHille.Basic                 -- genToGroup, generator_genToGroup, stoneEquiv
/-!
# Stone's theorem: the Cayley–Borel and Hille–Yosida constructions of `e^{itA}` agree

## The theorem

There is **one** theorem here, **Stone's theorem** (Stone 1932): the map

  `U ↦ generator U`

is a bijection from strongly continuous one-parameter unitary groups on a Hilbert space `H` to
(densely defined, unbounded) self-adjoint operators on `H`, with inverse `A ↦ (t ↦ e^{itA})`.

The **forward** map — send a group to its infinitesimal generator — is canonical and is literally
the same function in every development of the theorem. All of the mathematical work, and all of
the freedom, lives in the **inverse** map: given a self-adjoint `A`, *construct* the group
`t ↦ e^{itA}`. This project carries two independent constructions:

* `stoneGroup` — the **Cayley–Borel** construction: reduce the unbounded self-adjoint `A` to a
  unitary via the Cayley transform, then exponentiate through the bounded Borel functional
  calculus (`CayleyTransform.BorelCalculus`).
* `genToGroup` — the **Hille–Yosida** construction: realize `e^{itA}` as the strong limit of
  `e^{itAλ}` over the bounded Yosida approximants `Aλ`, via the semigroup/group generation
  theorem (`YosidaHille.Basic`).

## What this file proves

That the two constructions produce the *same group*:

  `stoneGroup hA = genToGroup hA`   (`stoneGroup_eq_genToGroup`).

This is the entire substantive content. Everything else is packaging.

## Logical structure (read before trusting the equivalence-level statement)

The two constructions are packaged as two `Equiv`s of the same type: `stoneEquivSpectral` (built
here from `stoneGroup`) and `stoneEquiv` (built in `YosidaHille.Basic` from `genToGroup`). It is
tempting to regard the equality of these `Equiv`s as the theorem. It is not, and the reason is
worth stating precisely, because the easy proof hides it:

* Both `Equiv`s have the **same forward map**, `U ↦ ⟨generator U, _⟩`, definitionally. Hence
  `stoneEquivSpectral = stoneEquiv` follows from `Equiv.ext` by `rfl` alone — *without ever
  comparing the two inverse constructions*, since an `Equiv`'s inverse is forced by its forward
  map (two-sided inverses are unique). So `stoneEquivSpectral_eq_stoneEquiv` is true but carries
  **no information about the constructions**; it is a fact about uniqueness of inverses.

* The fact that the constructions genuinely coincide is `stoneGroup_eq_genToGroup`, and its honest
  proof is generator-uniqueness (`group_unique`): the two groups are equal *because* they have the
  same generator, each computed independently (`generator_stoneGroup`, `generator_genToGroup`).

The inverse-map agreement read off the `Equiv` equality (`stoneEquivSpectral_symm_coe_eq`)
therefore *re-derives* `stoneGroup_eq_genToGroup`; `§1` is the conceptually primary statement and
`§3` is its formal shadow. We keep both, clearly labeled, rather than let the shadow pose as the
substance.

## Main results

* `stoneGroup_eq_genToGroup` — **the bridge**: the Cayley–Borel and Hille–Yosida constructions of
  `e^{itA}` are the same group. Proof: equal generators ⟹ equal groups.
* `stoneExp_eq_genToGroup` — the pointwise form, `e^{itA}` agrees at every `t`.
* `stoneEquivSpectral` — Stone's theorem as a bijection, with the inverse furnished by `stoneGroup`.
* `stoneEquivSpectral_eq_stoneEquiv` — the spectral and Yosida *packagings* coincide as `Equiv`s
  (formal; see the logical-structure note above).

## References

* M. H. Stone, *On one-parameter unitary groups in Hilbert space*, Ann. of Math. **33** (1932),
  643–648. (The theorem.)
* J. von Neumann, *Mathematische Grundlagen der Quantenmechanik* (1932). (Spectral theorem / Borel
  functional calculus underlying the Cayley–Borel construction; also the Cayley transform and the
  theory of self-adjoint extensions.)
* E. Hille, *Functional Analysis and Semi-Groups* (1948); K. Yosida, *On the differentiability and
  the representation of one-parameter semi-groups of linear operators*, J. Math. Soc. Japan **1**
  (1948), 15–21. (The Hille–Yosida construction.)
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics*, Vol. I, §VIII.4 (Stone's theorem).

## Not to be confused with: the Stone–von Neumann theorem

The **Stone–von Neumann theorem** (Stone 1930, von Neumann 1931) is a *different* theorem: the
uniqueness, up to unitary equivalence, of the irreducible representations of the Weyl form of the
canonical commutation relations `e^{isP} e^{itQ} = e^{-ist} e^{itQ} e^{isP}`. It concerns a *pair*
of one-parameter groups satisfying a fixed commutation relation and concludes they are unitarily
equivalent to the Schrödinger representation. Nothing in this file involves a CCR pair, and none
of the statements below are instances of Stone–von Neumann. (That theorem will become relevant —
and citable — only once the Weyl relations are formalized, e.g. for the hydrogen `P`, `Q` pair.)
-/

open InnerProductSpace Complex Filter Topology
open Spectra Spectra.OneParameterUnitaryGroup Spectra.Resolvent Spectra.YosidaHille Spectra.Cayley

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H}

namespace Spectra.YosidaHille

/-! ## §1  The bridge: the two constructions of `e^{itA}` coincide

This is the substantive content of the file. Both `stoneGroup hA` and `genToGroup hA` are
strongly continuous one-parameter unitary groups, and each has been *independently* shown to have
generator `A` (`generator_stoneGroup`, `generator_genToGroup`). Since a one-parameter unitary
group is determined by its generator (`group_unique`, the uniqueness half of Stone's theorem), the
two groups are equal. No comparison of spectral data is required. -/

/-- **The bridge.** The Cayley–Borel construction `stoneGroup` and the Hille–Yosida construction
`genToGroup` yield the *same* one-parameter unitary group `t ↦ e^{itA}`.

Proof: both have generator `A`, so they are equal by generator-uniqueness. This — not the
`Equiv`-level equality of `§3` — is the mathematical statement that the two constructions agree. -/
theorem stoneGroup_eq_genToGroup [Nontrivial H] (hA : IsSelfAdjoint A) :
    stoneGroup hA = genToGroup hA :=
  group_unique _ _ (by rw [generator_stoneGroup hA, generator_genToGroup hA])

/-- The pointwise form of the bridge: the two constructions of `e^{itA}` agree at every time `t`. -/
theorem stoneExp_eq_genToGroup [Nontrivial H] (hA : IsSelfAdjoint A) (t : ℝ) :
    stoneExp hA t = (genToGroup hA).U t := by
  rw [show stoneExp hA t = (stoneGroup hA).U t from rfl, stoneGroup_eq_genToGroup hA]

/-! ## §2  Stone's theorem as a bijection (Cayley–Borel construction of the inverse)

This packages Stone's theorem as an `Equiv`, with the inverse map furnished by the Cayley–Borel
`stoneGroup`. It is the *same* theorem as the Hille–Yosida packaging `stoneEquiv` from
`YosidaHille.Basic`; only the construction of the inverse differs. The forward map (take the
generator) is shared verbatim, which is what `§3` exploits.

`Nontrivial H` is inherited from `generator_stoneGroup` (ultimately from the keystone resolvent
identity). -/

/-- **Stone's theorem (spectral form).** The bijective correspondence between strongly continuous
one-parameter unitary groups and self-adjoint operators, with the inverse map given by the
Cayley–Borel construction `stoneGroup`. Identical in shape to the Hille–Yosida packaging
`stoneEquiv`; the two are proved equal in `§3`. -/
noncomputable def stoneEquivSpectral [Nontrivial H] :
    OneParameterUnitaryGroup (H := H) ≃ {A : H →ₗ.[ℂ] H // IsSelfAdjoint A} where
  toFun  U := ⟨generator U, generator_isSelfAdjoint U⟩
  invFun A := stoneGroup A.2
  left_inv  U := group_unique _ _ (generator_stoneGroup (generator_isSelfAdjoint U))
  right_inv A := Subtype.ext (generator_stoneGroup A.2)

@[simp] lemma stoneEquivSpectral_apply [Nontrivial H] (U : OneParameterUnitaryGroup (H := H)) :
    (stoneEquivSpectral U : H →ₗ.[ℂ] H) = generator U := rfl

@[simp] lemma stoneEquivSpectral_symm_apply [Nontrivial H] (hA : IsSelfAdjoint A) :
    stoneEquivSpectral.symm ⟨A, hA⟩ = stoneGroup hA := rfl

@[simp] lemma stoneEquivSpectral_symm_U [Nontrivial H] (hA : IsSelfAdjoint A) (t : ℝ) (ψ : H) :
    (stoneEquivSpectral.symm ⟨A, hA⟩).U t ψ = stoneExp hA t ψ := rfl

/-! ## §3  The two packagings coincide

We record that the spectral and Yosida `Equiv`s are equal. Read the logical-structure note in the
module docstring first: this equality is **formally immediate** and does *not*, by itself, witness
that the two constructions agree — that is `§1`. -/

/-- The spectral and Hille–Yosida packagings of Stone's theorem are the same `Equiv`.

**This proof carries no mathematical content about the two constructions.** The forward maps of
`stoneEquivSpectral` and `stoneEquiv` are definitionally equal (both `U ↦ ⟨generator U, _⟩`), so
`Equiv.ext` closes the goal by `rfl`; the agreement of the inverse maps is then forced abstractly
by uniqueness of two-sided inverses, *not* derived from any property of `stoneGroup` or
`genToGroup`. The statement that the constructions genuinely coincide is `stoneGroup_eq_genToGroup`
(`§1`), whose proof uses generator-uniqueness. -/
theorem stoneEquivSpectral_eq_stoneEquiv [Nontrivial H] :
    (stoneEquivSpectral : OneParameterUnitaryGroup (H := H) ≃ _) = stoneEquiv :=
  Equiv.ext fun _ => rfl

/-- The inverse maps of the two packagings agree. Unfolding the two sides via the `symm` simp
lemmas turns this into `stoneGroup hA = genToGroup hA` — i.e. it recovers the `§1` bridge as a
formal corollary of `§3`. We prove `§1` directly (via uniqueness) and treat this as its shadow. -/
theorem stoneEquivSpectral_symm_coe_eq [Nontrivial H] :
    (stoneEquivSpectral.symm : {A : H →ₗ.[ℂ] H // IsSelfAdjoint A} → _) = stoneEquiv.symm := by
  rw [stoneEquivSpectral_eq_stoneEquiv]

end Spectra.YosidaHille
