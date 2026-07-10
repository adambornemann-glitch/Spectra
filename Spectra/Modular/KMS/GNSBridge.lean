/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.KMS.UnitaryGroup
import Spectra.Modular.KMS.Modular
import Spectra.Modular.TomitaTakesaki.Basic
/-!
# The GNS bridge: from a state to a von Neumann algebra with cyclic vector

This file connects the abstract C*-algebraic KMS side of the library to the concrete
Tomita–Takesaki side. From a state `ω` on a unital C*-algebra `A`, the GNS construction
(`PositiveLinearMap.GNS`, wrapped as `State.gnsSpace`) produces a Hilbert space `H_ω`, a
`*`-representation `π = ω.toPLM.gnsStarAlgHom : A →⋆ₐ[ℂ] B(H_ω)`, and a distinguished unit
vector `Ω = ω.cyclicVector`. Here we complete that picture to the pair `(π(A)'', Ω)` on which
modular theory runs:

* `doubleCommutant` : for any star-closed set `S ⊆ B(K)`, the double commutant `S''` is a genuine
  `VonNeumannAlgebra K` (the bicommutant identity `S'''' = S''` is
  `Set.centralizer_centralizer_centralizer`).
* `State.gnsVonNeumann` : the GNS von Neumann algebra `π(A)''` acting on `H_ω`.
* `State.isCyclic_gnsVonNeumann` : **`Ω` is cyclic for `π(A)''` — unconditionally.** Already the
  orbit `π(A)Ω` is the coe-image of the pre-GNS space, which is dense in the completion `H_ω`.
* `State.norm_sq_gnsStarAlgHom_cyclicVector` : `⟪π(a)Ω, π(a)Ω⟫ = ω(a*a)`, the GNS norm
  identity.
* `State.gnsStarAlgHom_cyclicVector_eq_zero_iff`, `State.gnsStarAlgHom_injective` : for a
  **faithful** `ω`, the vector `Ω` separates the *represented copies of algebra elements* —
  `π(a)Ω = 0 ↔ a = 0` — and consequently `π` is injective, so `A` embeds into `B(H_ω)`.
* `FaithfulNormalState.isCyclic_gnsVonNeumann`, `FaithfulNormalState.gnsStarAlgHom_injective` :
  the same statements packaged for `FaithfulNormalState` (the modular-theory entry point).

## Honesty about scope

We do **not** claim `IsSeparating ω.gnsVonNeumann ω.cyclicVector`. Separation of the full
bicommutant `π(A)''` by `Ω` requires normality of `ω` together with density machinery
(Kaplansky density / σ-weak continuity of the extension of `ω` to `π(A)''`), none of which is in
Mathlib yet. What faithfulness alone buys is separation at the level of `A`
(`π(a)Ω = 0 → a = 0`), proved here; the bicommutant-level statement is the known next gap,
documented in the project plan.
-/

open Complex InnerProductSpace PositiveLinearMap
open scoped ComplexOrder

namespace Spectra.KMS

/-! ## The double-commutant von Neumann algebra of a star-closed set

Mathlib's `VonNeumannAlgebra K` is a star subalgebra of `B(K)` equal to its double commutant
(centralizer of centralizer). For any star-closed `S ⊆ B(K)` the double commutant `S''` satisfies
all of these demands: `Subalgebra.centralizer` provides the algebra structure, star-closure passes
through centralizers of star-closed sets (`Set.star_mem_centralizer'`), and the bicommutant
identity `(S'')'' = S''` is the general `Set.centralizer_centralizer_centralizer`. -/

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The **double commutant** `S''` of a star-closed set of bounded operators, as a genuine
`VonNeumannAlgebra K`. The carrier is `Set.centralizer (Set.centralizer S)`; star-closure descends
through both centralizers, and `(S'')'' = S''` is `Set.centralizer_centralizer_centralizer`. -/
noncomputable def doubleCommutant (S : Set (K →L[ℂ] K)) (hS : ∀ x ∈ S, star x ∈ S) :
    VonNeumannAlgebra K where
  toStarSubalgebra :=
    { Subalgebra.centralizer ℂ (Set.centralizer S) with
      star_mem' := fun hx =>
        Set.star_mem_centralizer' (fun _ ha => Set.star_mem_centralizer' hS ha) hx }
  centralizer_centralizer' := Set.centralizer_centralizer_centralizer (Set.centralizer S)

/-- The carrier of `doubleCommutant S hS` is the set-level double centralizer. -/
@[simp] lemma coe_doubleCommutant (S : Set (K →L[ℂ] K)) (hS : ∀ x ∈ S, star x ∈ S) :
    (doubleCommutant S hS : Set (K →L[ℂ] K)) = Set.centralizer (Set.centralizer S) :=
  rfl

/-- Every element of `S` lies in its double commutant `S''` (it commutes with everything that
commutes with it). -/
theorem subset_doubleCommutant (S : Set (K →L[ℂ] K)) (hS : ∀ x ∈ S, star x ∈ S) :
    S ⊆ (doubleCommutant S hS : Set (K →L[ℂ] K)) :=
  Set.subset_centralizer_centralizer

variable {A : Type*} [CStarAlgebra A]

-- The C*-algebra order on `A` is not a global instance (Mathlib enables it locally to avoid
-- diamonds); enable the spectral order, matching `Spectra.Modular.KMS.UnitaryGroup`.
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

/-! ## The GNS von Neumann algebra `π(A)''` -/

/-- The **GNS von Neumann algebra** of a state: the double commutant `π(A)''` of the range of the
GNS representation `π = ω.toPLM.gnsStarAlgHom`, acting on the GNS Hilbert space `H_ω`. The range
is star-closed since `π` is a `*`-homomorphism. -/
noncomputable def State.gnsVonNeumann (ω : State A) : VonNeumannAlgebra ω.gnsSpace :=
  doubleCommutant (Set.range (ω.toPLM.gnsStarAlgHom : A → ω.gnsSpace →L[ℂ] ω.gnsSpace))
    (by rintro _ ⟨a, rfl⟩; exact ⟨star a, map_star ω.toPLM.gnsStarAlgHom a⟩)

/-- Every represented operator `π(a)` belongs to the GNS von Neumann algebra `π(A)''`. -/
theorem State.gnsStarAlgHom_mem_gnsVonNeumann (ω : State A) (a : A) :
    ω.toPLM.gnsStarAlgHom a ∈ ω.gnsVonNeumann :=
  subset_doubleCommutant _ _ (Set.mem_range_self a)

/-! ## Cyclicity of the GNS vacuum for `π(A)''` — unconditional

The orbit `π(A)Ω` is exactly the coe-image of the pre-GNS space
(`State.gnsStarAlgHom_cyclicVector` computes `π(a)Ω = ↑(toPreGNS a)`, and `toPreGNS` is a linear
equivalence), and the coe-image of a space is dense in its completion. No hypothesis on `ω`
beyond being a state is needed. -/

/-- **The GNS vacuum is cyclic for the GNS von Neumann algebra.** The span of `π(A)'' Ω` contains
the coe-image of the pre-GNS space, which is dense in the completion `H_ω`. Holds for *every*
state — no faithfulness or normality is needed. -/
theorem State.isCyclic_gnsVonNeumann (ω : State A) :
    Spectra.TomitaTakesaki.IsCyclic ω.gnsVonNeumann ω.cyclicVector := by
  have hsub : Set.range ((↑) : ω.toPLM.PreGNS → ω.gnsSpace) ⊆
      (Submodule.span ℂ
        (Spectra.TomitaTakesaki.cyclicSet ω.gnsVonNeumann ω.cyclicVector) : Set ω.gnsSpace) := by
    rintro _ ⟨x, rfl⟩
    refine Submodule.subset_span ⟨ω.toPLM.gnsStarAlgHom (ω.toPLM.ofPreGNS x),
      ω.gnsStarAlgHom_mem_gnsVonNeumann (ω.toPLM.ofPreGNS x), ?_⟩
    change ω.toPLM.gnsStarAlgHom (ω.toPLM.ofPreGNS x) ω.cyclicVector = (↑x : ω.gnsSpace)
    rw [ω.gnsStarAlgHom_cyclicVector, toPreGNS_ofPreGNS]
  exact Dense.mono hsub (UniformSpace.Completion.denseRange_coe (α := ω.toPLM.PreGNS))

/-! ## Separation from faithfulness — at the level of the algebra

The GNS norm identity `‖π(a)Ω‖² = ω(a*a)` turns faithfulness of `ω` directly into separation of
the represented algebra elements by the vacuum, and hence injectivity of `π`. -/

/-- **GNS norm identity**: `⟪π(a)Ω, π(a)Ω⟫ = ω(a*a)`. Both sides compute on the pre-GNS
representative `toPreGNS a` of `π(a)Ω`. -/
theorem State.norm_sq_gnsStarAlgHom_cyclicVector (ω : State A) (a : A) :
    ⟪ω.toPLM.gnsStarAlgHom a ω.cyclicVector, ω.toPLM.gnsStarAlgHom a ω.cyclicVector⟫_ℂ
      = ω (star a * a) := by
  rw [ω.gnsStarAlgHom_cyclicVector, UniformSpace.Completion.inner_coe, preGNS_inner_def,
    ofPreGNS_toPreGNS, State.toPLM_apply]

/-- **Faithfulness separates the represented algebra at the vacuum**: `π(a)Ω = 0 ↔ a = 0`.
This is the honest, provable consequence of faithfulness alone; separation for the full
bicommutant `π(A)''` additionally needs normality plus density machinery (see the module
docstring). -/
theorem State.gnsStarAlgHom_cyclicVector_eq_zero_iff (ω : State A) (hfaith : ω.IsFaithful)
    (a : A) : ω.toPLM.gnsStarAlgHom a ω.cyclicVector = 0 ↔ a = 0 := by
  constructor
  · intro h
    refine hfaith a ?_
    have hnorm := ω.norm_sq_gnsStarAlgHom_cyclicVector a
    rw [h, inner_zero_right] at hnorm
    exact hnorm.symm
  · rintro rfl
    simp

/-- **The GNS representation of a faithful state is injective**: `A` embeds into `B(H_ω)`.
Standard consequence of `π(a-b)Ω = 0 → a - b = 0`. -/
theorem State.gnsStarAlgHom_injective (ω : State A) (hfaith : ω.IsFaithful) :
    Function.Injective ω.toPLM.gnsStarAlgHom := by
  intro a b hab
  have hz : ω.toPLM.gnsStarAlgHom (a - b) ω.cyclicVector = 0 := by
    rw [map_sub, ContinuousLinearMap.sub_apply, hab, sub_self]
  exact sub_eq_zero.mp ((ω.gnsStarAlgHom_cyclicVector_eq_zero_iff hfaith (a - b)).mp hz)

/-! ## The `FaithfulNormalState` packaging

Thin wrappers restating the bridge for `FaithfulNormalState` — the hypothesis shape under which
modular theory (`ModularTheoryData`) is stated. Only `ω.faithful` is consumed; normality is
carried along for the (future) bicommutant-level separation statement. -/

section FaithfulNormal

variable [WStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The GNS vacuum of a faithful normal state is cyclic for `π(A)''` (specialization of the
unconditional `State.isCyclic_gnsVonNeumann`). -/
theorem FaithfulNormalState.isCyclic_gnsVonNeumann (ω : FaithfulNormalState A) :
    Spectra.TomitaTakesaki.IsCyclic ω.toState.gnsVonNeumann ω.toState.cyclicVector :=
  ω.toState.isCyclic_gnsVonNeumann

/-- The GNS representation of a faithful normal state is injective. (The GNS machinery lives over
the spectral order on `A`, so the representation's order instances are pinned explicitly; the
ambient `[PartialOrder A] [StarOrderedRing A]` of `ω` itself remains arbitrary.) -/
theorem FaithfulNormalState.gnsStarAlgHom_injective (ω : FaithfulNormalState A) :
    Function.Injective
      (@PositiveLinearMap.gnsStarAlgHom A _ (CStarAlgebra.spectralOrder A)
        (CStarAlgebra.spectralOrderedRing A) ω.toState.toPLM) :=
  ω.toState.gnsStarAlgHom_injective ω.faithful

end FaithfulNormal

end Spectra.KMS
