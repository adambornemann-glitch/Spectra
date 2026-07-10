/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.KMS.Condition
import Spectra.Modular.KMS.Modular
import Spectra.OneParameterUnitaryGroup.Basic
import Spectra.StoneBridge.Basic
import Spectra.Bochner.GNS.Representation.StronglyEx
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Topology.Algebra.LinearMapCompletion
/-!
# The canonical GNS one-parameter unitary group of an invariant state

From a state `ω` on a C*-algebra `A` that is invariant under a dynamics `α` (in particular, any
KMS state, via `IsKMSState.isInvariant`), we construct the **canonical unitary implementation** of
`α` on the GNS Hilbert space `H_ω`:

  `U_ω(t) : H_ω → H_ω`,   `U_ω(t) π(a)Ω = π(α_t a)Ω`.

Because `ω` is `α`-invariant, `a ↦ α_t a` is an isometry of the GNS pre-inner product, so it
extends to a unitary on the completion. The result is a genuine
`Spectra.OneParameterUnitaryGroup H_ω`, so the project's Stone machinery applies verbatim: its
infinitesimal `generator` (the **Liouvillian / thermal Hamiltonian**) is self-adjoint and is the
operator assigned to `U_ω` by `stoneEquivSpectral`.

This is the bridge from the C*-algebraic KMS world to the Hilbert-space Stone/Yosida world.
-/

open Complex InnerProductSpace PositiveLinearMap
open scoped ComplexOrder

namespace Spectra.KMS

variable {A : Type*} [CStarAlgebra A]

-- The C*-algebra order on `A` is not a global instance (Mathlib enables it locally to avoid
-- diamonds); enable the spectral order for this file's positivity/monotonicity arguments.
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

/-! ## The state as a positive linear map -/

/-- A bespoke `State` as a Mathlib positive linear functional `A →ₚ[ℂ] ℂ`, unlocking the GNS
construction (`PositiveLinearMap.GNS`). Positivity on all nonnegative elements follows from
`State.nonneg` by the standard `StarOrderedRing` cone-induction (cf. `stateSet.map_nonneg`). -/
noncomputable def State.toPLM (ω : State A) : A →ₚ[ℂ] ℂ where
  toLinearMap := ω.toFun
  monotone' := by
    have hpos : ∀ {x : A}, 0 ≤ x → (0 : ℂ) ≤ ω.toFun x := by
      intro x hx
      rw [StarOrderedRing.nonneg_iff] at hx
      induction hx using AddSubmonoid.closure_induction with
      | mem y hy => obtain ⟨s, rfl⟩ := hy; exact ω.nonneg s
      | zero => simp
      | add y z _ _ ihy ihz => rw [map_add]; exact add_nonneg ihy ihz
    intro x y hxy
    have h : (0 : ℂ) ≤ ω.toFun (y - x) := hpos (sub_nonneg.mpr hxy)
    rw [map_sub] at h
    exact sub_nonneg.mp h

/-- `ω.toPLM` agrees with `ω` pointwise: `ω.toPLM a = ω a`. -/
@[simp] lemma State.toPLM_apply (ω : State A) (a : A) : ω.toPLM a = ω a := rfl

/-- The GNS Hilbert space of a state. -/
noncomputable abbrev State.gnsSpace (ω : State A) : Type _ := ω.toPLM.GNS

/-! ## The implementing isometry of the dynamics on the pre-GNS space -/

variable (ω : State A) (α : Dynamics A)

/-- The action `a ↦ α_t a` on the pre-GNS space, as a linear map (`α_t` transported through the
type-synonym identifications `toPreGNS`/`ofPreGNS`). -/
noncomputable def evolveLin (t : ℝ) : ω.toPLM.PreGNS →ₗ[ℂ] ω.toPLM.PreGNS :=
  ω.toPLM.toPreGNS.toLinearMap ∘ₗ α.evolve t ∘ₗ ω.toPLM.ofPreGNS.toLinearMap

/-- Transporting `evolveLin ω α t a` back through `ofPreGNS` recovers `α_t` acting on
`ofPreGNS a`. -/
@[simp] lemma evolveLin_ofPreGNS (t : ℝ) (a : ω.toPLM.PreGNS) :
    ω.toPLM.ofPreGNS (evolveLin ω α t a) = α.evolve t (ω.toPLM.ofPreGNS a) := by
  simp [evolveLin]

/-- Invariance of `ω` makes `α_t` preserve the pre-GNS inner product. -/
lemma evolveLin_inner (hinv : IsInvariant ω α) (t : ℝ) (a b : ω.toPLM.PreGNS) :
    ⟪evolveLin ω α t a, evolveLin ω α t b⟫_ℂ = ⟪a, b⟫_ℂ := by
  rw [preGNS_inner_def, preGNS_inner_def, evolveLin_ofPreGNS, evolveLin_ofPreGNS,
    ← α.map_star, ← α.map_mul, State.toPLM_apply, State.toPLM_apply]
  exact hinv t _

/-- Hence `α_t` is norm-preserving on the pre-GNS space. -/
lemma evolveLin_norm (hinv : IsInvariant ω α) (t : ℝ) (a : ω.toPLM.PreGNS) :
    ‖evolveLin ω α t a‖ = ‖a‖ := by
  have h := evolveLin_inner ω α hinv t a a
  rw [@inner_self_eq_norm_sq_to_K ℂ, @inner_self_eq_norm_sq_to_K ℂ] at h
  have h_sq : ‖evolveLin ω α t a‖ ^ 2 = ‖a‖ ^ 2 := by exact_mod_cast h
  nlinarith [sq_nonneg (‖evolveLin ω α t a‖ - ‖a‖), sq_nonneg (‖evolveLin ω α t a‖ + ‖a‖),
    norm_nonneg (evolveLin ω α t a), norm_nonneg a]

/-- `α_t` as a continuous linear map on the pre-GNS space (norm `≤ 1`). -/
noncomputable def evolveCLM (hinv : IsInvariant ω α) (t : ℝ) :
    ω.toPLM.PreGNS →L[ℂ] ω.toPLM.PreGNS :=
  (evolveLin ω α t).mkContinuous 1
    (fun a => le_of_eq (by rw [evolveLin_norm ω α hinv t a, one_mul]))

/-- `evolveCLM ω α hinv t` agrees with the underlying linear map `evolveLin ω α t` pointwise. -/
@[simp] lemma evolveCLM_apply (hinv : IsInvariant ω α) (t : ℝ) (a : ω.toPLM.PreGNS) :
    evolveCLM ω α hinv t a = evolveLin ω α t a := rfl

/-- The implementing unitary `U_ω(t)` on the GNS Hilbert space: the completion of `α_t`. -/
noncomputable def evolveU (hinv : IsInvariant ω α) (t : ℝ) : ω.gnsSpace →L[ℂ] ω.gnsSpace :=
  (evolveCLM ω α hinv t).completion

/-- `U_ω(t)` on the image of a pre-GNS vector is the image of `α_t` applied to it:
`U_ω(t) ↑a = ↑(evolveLin ω α t a)`. -/
@[simp] lemma evolveU_coe (hinv : IsInvariant ω α) (t : ℝ) (a : ω.toPLM.PreGNS) :
    evolveU ω α hinv t (a : ω.gnsSpace) = (evolveLin ω α t a : ω.gnsSpace) := by
  rw [evolveU, ContinuousLinearMap.completion_apply_coe, evolveCLM_apply]

/-! ## The unitary-group axioms as standalone lemmas -/

/-- `U_ω(t)` preserves the inner product (it is the completion of an isometry). -/
lemma evolveU_inner (hinv : IsInvariant ω α) (t : ℝ) (ψ φ : ω.gnsSpace) :
    ⟪evolveU ω α hinv t ψ, evolveU ω α hinv t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ := by
  induction ψ, φ using UniformSpace.Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih a b =>
    rw [evolveU_coe, evolveU_coe, UniformSpace.Completion.inner_coe,
      UniformSpace.Completion.inner_coe]
    exact evolveLin_inner ω α hinv t a b

/-- `U_ω(t)` is norm-preserving. -/
lemma evolveU_norm (hinv : IsInvariant ω α) (t : ℝ) (ψ : ω.gnsSpace) :
    ‖evolveU ω α hinv t ψ‖ = ‖ψ‖ := by
  have h := evolveU_inner ω α hinv t ψ ψ
  rw [@inner_self_eq_norm_sq_to_K ℂ, @inner_self_eq_norm_sq_to_K ℂ] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (by exact_mod_cast h)

/-- Group law (pointwise): `U_ω(s+t) = U_ω(s) ∘ U_ω(t)`. -/
lemma evolveU_group (hinv : IsInvariant ω α) (s t : ℝ) (ψ : ω.gnsSpace) :
    evolveU ω α hinv (s + t) ψ = evolveU ω α hinv s (evolveU ω α hinv t ψ) := by
  induction ψ using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih a =>
    rw [evolveU_coe, evolveU_coe, evolveU_coe]
    congr 1
    apply ω.toPLM.ofPreGNS.injective
    rw [evolveLin_ofPreGNS, evolveLin_ofPreGNS, evolveLin_ofPreGNS, α.evolve_add]

/-- Identity (pointwise): `U_ω(0) = id`. -/
lemma evolveU_id (hinv : IsInvariant ω α) (ψ : ω.gnsSpace) :
    evolveU ω α hinv 0 ψ = ψ := by
  induction ψ using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih a =>
    rw [evolveU_coe]
    congr 1
    apply ω.toPLM.ofPreGNS.injective
    rw [evolveLin_ofPreGNS, α.evolve_zero]

/-- Strong continuity on the dense pre-GNS vectors. The inner product
`⟪U_ω(t) π(a)Ω, U_ω(t₀) π(a)Ω⟫` is re-expressed on the algebra as
`ω(α_t(a)⋆ · α_{t₀}(a))`, where `t ↦ α_t(a)` is continuous, and `‖U_ω(·) - U_ω(t₀)‖²`
is controlled by it. -/
lemma evolveU_continuous_coe (hinv : IsInvariant ω α) (a : ω.toPLM.PreGNS) :
    Continuous (fun t => evolveU ω α hinv t (↑a : ω.gnsSpace)) := by
  rw [continuous_iff_continuousAt]; intro t₀
  set F : ℝ → ω.gnsSpace := fun t => evolveU ω α hinv t (↑a : ω.gnsSpace) with hF
  rw [Metric.continuousAt_iff]; intro ε hε
  set cross : ℝ → ℝ := fun t => (⟪F t, F t₀⟫_ℂ).re with hcross
  have hcross_eq : ∀ t, ⟪F t, F t₀⟫_ℂ
      = ω (star (α.evolve t (ω.toPLM.ofPreGNS a)) * α.evolve t₀ (ω.toPLM.ofPreGNS a)) := by
    intro t
    simp only [hF]
    rw [evolveU_coe, evolveU_coe, UniformSpace.Completion.inner_coe, preGNS_inner_def,
      evolveLin_ofPreGNS, evolveLin_ofPreGNS, State.toPLM_apply]
  have hcross_cont : Continuous cross := by
    have hce : cross = fun t => (ω (star (α.evolve t (ω.toPLM.ofPreGNS a))
        * α.evolve t₀ (ω.toPLM.ofPreGNS a))).re := by
      funext t; simp only [hcross]; rw [hcross_eq t]
    rw [hce]
    exact Complex.continuous_re.comp
      (ω.continuous.comp ((continuous_star.comp (α.continuous_evolve _)).mul continuous_const))
  have hFnorm : ∀ t, ‖F t‖ = ‖(↑a : ω.gnsSpace)‖ := by
    intro t; simp only [hF]; exact evolveU_norm ω α hinv t _
  have hinner_re : ∀ t, RCLike.re (⟪F t, F t₀⟫_ℂ) = cross t := fun _ => rfl
  have hcross_t₀ : cross t₀ = ‖(↑a : ω.gnsSpace)‖ ^ 2 := by
    have h1 : RCLike.re (⟪F t₀, F t₀⟫_ℂ) = ‖F t₀‖ ^ 2 := inner_self_eq_norm_sq (F t₀)
    rw [hFnorm t₀] at h1
    exact h1
  have hnorm_sq : ∀ t, ‖F t - F t₀‖ ^ 2 = 2 * (cross t₀ - cross t) := by
    intro t
    rw [@norm_sub_sq ℂ, hFnorm t, hFnorm t₀, hinner_re t, hcross_t₀]; ring
  obtain ⟨δ, hδ, hδ_spec⟩ := Metric.continuousAt_iff.mp
    hcross_cont.continuousAt (ε ^ 2 / 2) (by positivity)
  refine ⟨δ, hδ, fun {t} ht => ?_⟩
  rw [dist_eq_norm]
  have hcross_near : |cross t - cross t₀| < ε ^ 2 / 2 := by rw [← Real.dist_eq]; exact hδ_spec ht
  have _hnn : 0 ≤ cross t₀ - cross t := by
    have := (sq_nonneg ‖F t - F t₀‖).trans_eq (hnorm_sq t); linarith
  have hnorm_bound : ‖F t - F t₀‖ ^ 2 < ε ^ 2 := by
    rw [hnorm_sq]
    have : cross t₀ - cross t ≤ |cross t - cross t₀| := by rw [abs_sub_comm]; exact le_abs_self _
    linarith
  nlinarith [sq_nonneg ‖F t - F t₀‖, sq_abs ε]

/-! ## The one-parameter unitary group -/

/-- **The canonical GNS unitary implementation of an invariant dynamics.**

For a state `ω` invariant under the dynamics `α`, `t ↦ U_ω(t)` is a strongly continuous
one-parameter unitary group on the GNS Hilbert space `H_ω`, implementing `α`:
`U_ω(t) π(a)Ω = π(α_t a)Ω`. -/
noncomputable def invariantUnitaryGroup (hinv : IsInvariant ω α) :
    OneParameterUnitaryGroup ω.gnsSpace where
  U := fun t => evolveU ω α hinv t
  unitary := fun t ψ φ => evolveU_inner ω α hinv t ψ φ
  group_law := fun s t => ContinuousLinearMap.ext (fun ψ => evolveU_group ω α hinv s t ψ)
  identity := ContinuousLinearMap.ext (fun ψ => evolveU_id ω α hinv ψ)
  strong_continuous := fun ψ =>
    Spectra.Bochner.GNS.strong_continuity_extends
      (fun t => (evolveU ω α hinv t : ω.gnsSpace →ₗ[ℂ] ω.gnsSpace))
      (fun t χ => evolveU_norm ω α hinv t χ)
      (Set.range ((↑) : ω.toPLM.PreGNS → ω.gnsSpace))
      (UniformSpace.Completion.denseRange_coe (α := ω.toPLM.PreGNS))
      (by rintro φ ⟨a, rfl⟩; exact evolveU_continuous_coe ω α hinv a) ψ

/-- The unitary at time `t` of `invariantUnitaryGroup` is `evolveU ω α hinv t`. -/
@[simp] lemma invariantUnitaryGroup_U (hinv : IsInvariant ω α) (t : ℝ) :
    (invariantUnitaryGroup ω α hinv).U t = evolveU ω α hinv t := rfl

/-! ## Nontriviality: the cyclic vector is a unit vector -/

/-- The GNS space of a state is nontrivial: the cyclic vector `Ω = π(1)Ω` has norm one
(`‖Ω‖² = ω(1) = 1`). -/
instance State.instNontrivialGnsSpace (ω : State A) : Nontrivial ω.gnsSpace := by
  have hsq : ‖ω.toPLM.toPreGNS (1 : A)‖ ^ 2 = (1 : ℝ) := by
    have h := ω.toPLM.preGNS_norm_sq (ω.toPLM.toPreGNS 1)
    rw [ofPreGNS_toPreGNS, star_one, one_mul, State.toPLM_apply, ω.normalized] at h
    exact_mod_cast h
  have hnorm : ‖(↑(ω.toPLM.toPreGNS 1) : ω.gnsSpace)‖ = 1 := by
    rw [UniformSpace.Completion.norm_coe]
    nlinarith [norm_nonneg (ω.toPLM.toPreGNS (1 : A)), hsq]
  refine nontrivial_of_ne (↑(ω.toPLM.toPreGNS 1) : ω.gnsSpace) 0 ?_
  intro h; rw [h, norm_zero] at hnorm; exact one_ne_zero hnorm.symm

/-! ## The cyclic vector and the equilibrium (Liouvillian) eigenvector

The GNS construction comes with a canonical unit vector `Ω = π(1)Ω`, the **cyclic (vacuum)
vector**. For an invariant dynamics it is fixed by `U_ω(t)`, so it lies in the domain of the
generator (Liouvillian) and is annihilated by it: `L Ω = 0`. This is the Hilbert-space avatar of
the equilibrium condition. -/

/-- The cyclic (vacuum) vector `Ω = π(1)Ω` of the GNS Hilbert space, i.e. the image of the unit
`1 ∈ A` under the GNS embedding. -/
noncomputable def State.cyclicVector (ω : State A) : ω.gnsSpace :=
  (↑(ω.toPLM.toPreGNS (1 : A)) : ω.gnsSpace)

/-- The cyclic vector is a unit vector: `‖Ω‖ = 1` (since `‖Ω‖² = ω(1) = 1`). -/
@[simp] lemma State.cyclicVector_norm (ω : State A) : ‖ω.cyclicVector‖ = 1 := by
  have hsq : ‖ω.toPLM.toPreGNS (1 : A)‖ ^ 2 = (1 : ℝ) := by
    have h := ω.toPLM.preGNS_norm_sq (ω.toPLM.toPreGNS 1)
    rw [ofPreGNS_toPreGNS, star_one, one_mul, State.toPLM_apply, ω.normalized] at h
    exact_mod_cast h
  rw [State.cyclicVector, UniformSpace.Completion.norm_coe]
  nlinarith [norm_nonneg (ω.toPLM.toPreGNS (1 : A)), hsq]

/-- The GNS representation `π = gnsStarAlgHom` evaluated at the cyclic vector: `π(a) Ω` is the image
of `a` under the GNS embedding, `π(a) Ω = ↑(toPreGNS a)`. -/
lemma State.gnsStarAlgHom_cyclicVector (ω : State A) (a : A) :
    ω.toPLM.gnsStarAlgHom a ω.cyclicVector = (↑(ω.toPLM.toPreGNS a) : ω.gnsSpace) := by
  rw [State.cyclicVector]
  simp [gnsNonUnitalStarAlgHom_apply_coe, leftMulMapPreGNS_apply]

/-- **GNS reconstruction.** The state is recovered as the vacuum expectation value in its own GNS
representation: `⟪Ω, π(a) Ω⟫ = ω(a)`. This is the defining property of the GNS construction — it
certifies that the cyclic vector `Ω` genuinely represents `ω`. -/
lemma State.inner_cyclicVector_gnsStarAlgHom (ω : State A) (a : A) :
    ⟪ω.cyclicVector, ω.toPLM.gnsStarAlgHom a ω.cyclicVector⟫_ℂ = ω a := by
  rw [State.gnsStarAlgHom_cyclicVector, State.cyclicVector, UniformSpace.Completion.inner_coe,
    preGNS_inner_def, ofPreGNS_toPreGNS, ofPreGNS_toPreGNS, star_one, one_mul, State.toPLM_apply]

/-- **The cyclic vector is fixed by the invariant unitary group: `U_ω(t) Ω = Ω`.**
Concretely `α_t 1 = 1` (`Dynamics.map_one`), so `U_ω(t)π(1)Ω = π(α_t 1)Ω = π(1)Ω = Ω`. This does
not actually use invariance (only `α.map_one`), but `evolveU` is parameterized by `hinv`. -/
@[simp] lemma evolveU_cyclicVector (hinv : IsInvariant ω α) (t : ℝ) :
    evolveU ω α hinv t ω.cyclicVector = ω.cyclicVector := by
  rw [State.cyclicVector, evolveU_coe]
  congr 1
  apply ω.toPLM.ofPreGNS.injective
  rw [evolveLin_ofPreGNS, ofPreGNS_toPreGNS, α.map_one]

/-- The difference quotient of `U_ω` at the (fixed) cyclic vector is the constant-zero function. -/
lemma genDiffQuot_cyclicVector (hinv : IsInvariant ω α) :
    Spectra.OneParameterUnitaryGroup.genDiffQuot (invariantUnitaryGroup ω α hinv)
      ω.cyclicVector = fun _ => (0 : ω.gnsSpace) := by
  funext t
  rw [Spectra.OneParameterUnitaryGroup.genDiffQuot_apply, invariantUnitaryGroup_U,
    evolveU_cyclicVector ω α hinv t, sub_self, smul_zero]

/-- The cyclic vector lies in the domain of the generator (Liouvillian) of `U_ω`. -/
lemma cyclicVector_mem_generatorDomain (hinv : IsInvariant ω α) :
    ω.cyclicVector ∈
      (Spectra.OneParameterUnitaryGroup.generator (invariantUnitaryGroup ω α hinv)).domain :=
  Spectra.OneParameterUnitaryGroup.mem_generatorDomain.mpr
    ⟨0, by rw [genDiffQuot_cyclicVector ω α hinv]; exact tendsto_const_nhds⟩

/-- **The Liouvillian annihilates the equilibrium vector: `L Ω = 0`.** The generator of `U_ω`,
evaluated at the (fixed) cyclic vector, is zero — the Hilbert-space form of the equilibrium
condition. -/
lemma generator_apply_cyclicVector (hinv : IsInvariant ω α) :
    Spectra.OneParameterUnitaryGroup.generator (invariantUnitaryGroup ω α hinv)
        ⟨ω.cyclicVector, cyclicVector_mem_generatorDomain ω α hinv⟩ = 0 :=
  tendsto_nhds_unique
    (Spectra.OneParameterUnitaryGroup.generator_tendsto (invariantUnitaryGroup ω α hinv)
      ⟨ω.cyclicVector, cyclicVector_mem_generatorDomain ω α hinv⟩)
    (by rw [genDiffQuot_cyclicVector ω α hinv]; exact tendsto_const_nhds)

/-! ## The Stone correspondence

The KMS/invariant unitary group `U_ω` is a genuine `OneParameterUnitaryGroup`, so the project's
Stone machinery applies verbatim. Its generator — the **Liouvillian / thermal Hamiltonian** — is
self-adjoint, and is the operator assigned to `U_ω` by Stone's theorem in its Cayley/spectral form
`stoneEquivSpectral`. -/

/-- The Liouvillian (the generator of `U_ω`) is self-adjoint. -/
lemma invariantUnitaryGroup_generator_isSelfAdjoint (hinv : IsInvariant ω α) :
    IsSelfAdjoint (Spectra.OneParameterUnitaryGroup.generator (invariantUnitaryGroup ω α hinv)) :=
  Spectra.Resolvent.generator_isSelfAdjoint _

/-- **The Stone correspondence.** The generator of the KMS/invariant unitary group `U_ω` (the
Liouvillian / thermal Hamiltonian) is exactly the self-adjoint operator that Stone's theorem — in
its Cayley/Stone–von Neumann spectral form `stoneEquivSpectral`, which agrees with the Yosida–Hilde
bijection `stoneEquiv` — assigns to `U_ω`. -/
lemma invariantUnitaryGroup_stoneEquivSpectral (hinv : IsInvariant ω α) :
    (Spectra.YosidaHille.stoneEquivSpectral (invariantUnitaryGroup ω α hinv) :
        ω.gnsSpace →ₗ.[ℂ] ω.gnsSpace)
      = Spectra.OneParameterUnitaryGroup.generator (invariantUnitaryGroup ω α hinv) :=
  Spectra.YosidaHille.stoneEquivSpectral_apply _

/-! ## The KMS specialization -/

/-- **The canonical GNS unitary group of a KMS state.** A KMS state is invariant
(`IsKMSState.isInvariant`), so it implements its dynamics as a strongly continuous one-parameter
unitary group on the GNS Hilbert space. -/
noncomputable def IsKMSState.unitaryGroup {ω : State A} {α : Dynamics A} {β : ℝ}
    (hβ : 0 < β) (h : IsKMSState ω α β) : OneParameterUnitaryGroup ω.gnsSpace :=
  invariantUnitaryGroup ω α (h.isInvariant hβ)

/-- The thermal Hamiltonian of a KMS state is self-adjoint (Stone applies to `U_ω`). -/
lemma IsKMSState.generator_isSelfAdjoint {ω : State A} {α : Dynamics A} {β : ℝ}
    (hβ : 0 < β) (h : IsKMSState ω α β) :
    IsSelfAdjoint (Spectra.OneParameterUnitaryGroup.generator (h.unitaryGroup hβ)) :=
  invariantUnitaryGroup_generator_isSelfAdjoint ω α (h.isInvariant hβ)

/-! ## The modular unitary group `Δ^{it}` (Tomita–Takesaki specialization)

For a faithful normal state `ω` equipped with its modular theory data
`hmod : ModularTheoryData A ω`,
the modular flow `σ^ω` is implemented on the GNS Hilbert space by the canonical invariant unitary
group — the **GNS implementation of the modular flow**, written `Δ^{it}`, with generator the
**modular Hamiltonian** `K`.

**Scope and honesty caveats** (these lemmas are interpretive specializations of the general
invariant-state results, not new Tomita–Takesaki content):

* The construction uses **only** `hmod.dynamics` and `hmod.invariant`. The `kms_at_one` field,
  `ω.faithful`, and `ω.normal` are **not** used by any lemma below. So each statement in fact holds
  for *any* invariant dynamics, and the `FaithfulNormalState` / `ModularTheoryData` framing is
  contextual. (`State.IsNormal` is now an honest order-continuity predicate, no longer a
  placeholder, but nothing below depends on it.)
* The abstract `Δ` and `J` (from the polar decomposition `S = JΔ^{1/2}`) are **not** constructed —
  they remain axiomatized in `ModularTheoryData`. We never form `log Δ` nor prove
  `generator = ±log Δ`. The labels `Δ^{it}` and `K = -log Δ` name the canonical implementation *by
  analogy*; they become genuine identities only once a concrete `Δ` is built and `hmod.dynamics` is
  identified with the modular flow. -/

section Modular

variable [WStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (ω : FaithfulNormalState A) (hmod : ModularTheoryData A ω)

/-- **The modular unitary group `Δ^{it}`.** The GNS implementation of the modular flow `σ^ω`: a
strongly continuous one-parameter unitary group on `H_ω`. Definitionally this is
`invariantUnitaryGroup` of `hmod.dynamics` (using only its invariance); the `Δ^{it}` label is by
analogy — no abstract `Δ` is constructed (see the section caveats above). -/
noncomputable def ModularTheoryData.modularUnitaryGroup :
    OneParameterUnitaryGroup ω.toState.gnsSpace :=
  invariantUnitaryGroup ω.toState hmod.dynamics hmod.invariant

/-- The modular unitary `Δ^{it}` at time `t` is `evolveU` of `hmod.dynamics`. -/
@[simp] lemma ModularTheoryData.modularUnitaryGroup_U (t : ℝ) :
    (hmod.modularUnitaryGroup).U t = evolveU ω.toState hmod.dynamics hmod.invariant t :=
  rfl

/-- **The modular flow fixes the cyclic vector: `Δ^{it} Ω = Ω`.** The GNS vacuum is the equilibrium
vector of the modular flow. (Not `@[simp]`: it follows from the `@[simp]` lemmas
`modularUnitaryGroup_U` and `evolveU_cyclicVector`.) -/
lemma ModularTheoryData.modularUnitaryGroup_apply_cyclicVector (t : ℝ) :
    (hmod.modularUnitaryGroup).U t ω.toState.cyclicVector = ω.toState.cyclicVector :=
  evolveU_cyclicVector ω.toState hmod.dynamics hmod.invariant t

/-- **The modular Hamiltonian is self-adjoint.** The generator of the modular unitary group `Δ^{it}`
— informally `K = -log Δ`, though that spectral identity is not proved here (see section caveats) —
is self-adjoint, by Stone's theorem. -/
lemma ModularTheoryData.modularHamiltonian_isSelfAdjoint :
    IsSelfAdjoint
      (Spectra.OneParameterUnitaryGroup.generator hmod.modularUnitaryGroup) :=
  invariantUnitaryGroup_generator_isSelfAdjoint ω.toState hmod.dynamics hmod.invariant

/-- **The modular Hamiltonian annihilates the cyclic vector: `K Ω = 0`.** The generator of `Δ^{it}`
sends the GNS vacuum to `0` (equivalently `Δ^{it} Ω = Ω`), so the equilibrium vector lies in its
kernel. (`K` is the modular Hamiltonian by analogy — see section caveats.) -/
lemma ModularTheoryData.modularHamiltonian_apply_cyclicVector :
    Spectra.OneParameterUnitaryGroup.generator hmod.modularUnitaryGroup
        ⟨ω.toState.cyclicVector,
          cyclicVector_mem_generatorDomain ω.toState hmod.dynamics hmod.invariant⟩ = 0 :=
  generator_apply_cyclicVector ω.toState hmod.dynamics hmod.invariant

/-- **The Stone correspondence at the modular level.** The generator of the modular unitary group
`Δ^{it}` (the modular Hamiltonian) is exactly the self-adjoint operator that Stone's theorem — in
its Cayley/spectral form `stoneEquivSpectral` — assigns to it. -/
lemma ModularTheoryData.modularUnitaryGroup_stoneEquivSpectral :
    (Spectra.YosidaHille.stoneEquivSpectral hmod.modularUnitaryGroup :
        ω.toState.gnsSpace →ₗ.[ℂ] ω.toState.gnsSpace)
      = Spectra.OneParameterUnitaryGroup.generator hmod.modularUnitaryGroup :=
  invariantUnitaryGroup_stoneEquivSpectral ω.toState hmod.dynamics hmod.invariant

end Modular

end Spectra.KMS
