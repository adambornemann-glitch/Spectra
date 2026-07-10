/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.ProjValMeasure.Basic               -- ProjValMeasure, ext_of_diag
import Spectra.Herglotz.CauchyInjective           -- measure_ext_of_cauchyTransform
import Spectra.YosidaHille.Basic                        -- genToGroup, generator_genToGroup
import Spectra.YosidaHille.Helpers                      -- isSelfAdjoint_to_surjective
import Spectra.Resolvent.Diagonal.IntegralZ.Basic -- inner_resolvent_diag_eq_integral
import Spectra.SpectralTheory.StoneFormula.Basic  -- stonesFormula (for the coda)
import Spectra.Resolvent.Range
import Spectra.Bochner.Borel.CDF
import Spectra.OneParameterUnitaryGroup.PVM   -- toPVM (groupPVM's alias target)
/-!
# The Keystone: the spectral theorem, resolvent form

For every self-adjoint operator `A` on a complex Hilbert space there exists a
**unique** projection-valued measure `P` such that, for all `z` off the real
axis and all `ξ`,

  `⟪ξ, (A − z)⁻¹ ξ⟫ = ∫ (s − z)⁻¹ d(P.diag ξ)(s)`.

## Architecture

* **Existence** is transport: the canonical PVM is `groupPVM (genToGroup hA)`,
  and its resolvent formula is `inner_resolvent_diag_eq_integral` for the group
  `e^{itA}`, carried across `generator_genToGroup : generator (genToGroup hA) = A`.
  Since every hypothesis of `resolvent` is a proposition, the transport
  (`resolvent_congr_operator`) is `subst` followed by proof irrelevance.

* **Uniqueness** never touches the rival's projections: the resolvent formula
  pins each diagonal measure's Cauchy transform, `measure_ext_of_cauchyTransform`
  pins the diagonal measures, and `ProjValMeasure.ext_of_diag` pins the PVM.
  Note the rival's `proj_univ` and `proj_inter` are never consumed — the
  characterization is as robust as the structure allows.

## The resolvent-diagonal input

`inner_resolvent_diag_eq_integral` is declared, with this exact signature, in
`Resolvent/SpectralRepresentation.lean`:

  `(U_grp) (z : ℂ) (hz : z.im ≠ 0) (ξ : H) :
    ⟪ξ, resolvent z hz (generator_isFormalAdjoint U_grp)
      (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) ξ⟫_ℂ
    = ∫ s, ((s : ℂ) - z)⁻¹ ∂(borelMeasure U_grp ξ)`.
-/

open InnerProductSpace Complex MeasureTheory Filter Topology
open scoped InnerProductSpace
open Spectra.OneParameterUnitaryGroup
open Spectra.Resolvent
open Spectra.Borel
open Spectra.YosidaHille
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.QuantumMechanics.SpectralTheory

/-! ## The resolvent of a self-adjoint operator, canonically packaged -/

/-- A self-adjoint operator is formally self-adjoint (the incantation from
`genToGroup`, factored out). -/
lemma isFormalAdjoint_of_isSelfAdjoint {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    A.IsFormalAdjoint A := by
  have h := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
  rwa [LinearPMap.isSelfAdjoint_def.mp hA] at h

/-- The resolvent `(A − z)⁻¹` of a self-adjoint operator, with the deficiency
witnesses supplied once and for all. -/
noncomputable def selfAdjointResolvent {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (z : ℂ) (hz : z.im ≠ 0) : H →L[ℂ] H :=
  Resolvent.resolvent z hz (isFormalAdjoint_of_isSelfAdjoint hA)
    (isSelfAdjoint_to_surjective hA).1 (isSelfAdjoint_to_surjective hA).2

/-- The resolvent depends only on the operator: all hypothesis arguments are
propositions, so transport along an equality of operators is `subst` plus proof
irrelevance.  (This is why `selfAdjointResolvent` is canonical: any other choice
of witnesses yields the same operator, definitionally.) -/
lemma resolvent_congr_operator {A B : H →ₗ.[ℂ] H} (hAB : A = B) (z : ℂ) (hz : z.im ≠ 0)
    (hsymA : A.IsFormalAdjoint A)
    (hplusA : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminusA : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (hsymB : B.IsFormalAdjoint B)
    (hplusB : ∀ φ : H, ∃ ψ : B.domain, B ψ + I • (ψ : H) = φ)
    (hminusB : ∀ φ : H, ∃ ψ : B.domain, B ψ - I • (ψ : H) = φ) :
    resolvent z hz hsymA hplusA hminusA = resolvent z hz hsymB hplusB hminusB := by
  subst hAB
  rfl

/-- The resolvent of `A` is the resolvent of the generator of `e^{itA}`. -/
lemma selfAdjointResolvent_eq_genToGroup {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (z : ℂ) (hz : z.im ≠ 0) :
    selfAdjointResolvent hA z hz
      = resolvent z hz (generator_isFormalAdjoint (genToGroup hA))
          (range_plus_i_eq_top (genToGroup hA)) (range_minus_i_eq_top (genToGroup hA)) := by
  unfold selfAdjointResolvent
  exact resolvent_congr_operator (generator_genToGroup hA).symm z hz
    (isFormalAdjoint_of_isSelfAdjoint hA)
    (isSelfAdjoint_to_surjective hA).1 (isSelfAdjoint_to_surjective hA).2
    (generator_isFormalAdjoint _) (range_plus_i_eq_top _) (range_minus_i_eq_top _)

/-! ## The canonical projection-valued measures -/

/-- The canonical PVM of a strongly continuous one-parameter unitary group. An alias, under the
name this file's resolvent-form development was built against, for
`OneParameterUnitaryGroup.toPVM` (`OneParameterUnitaryGroup/PVM.lean`) — the same
`spectralProjection`/`borelMeasure` pair, bundled once, not rebuilt here. -/
noncomputable def groupPVM (U_grp : OneParameterUnitaryGroup (H := H)) : ProjValMeasure H :=
  U_grp.toPVM

@[simp] lemma groupPVM_proj (U_grp : OneParameterUnitaryGroup (H := H)) :
    (groupPVM U_grp).proj = spectralProjection U_grp := rfl

@[simp] lemma groupPVM_diag (U_grp : OneParameterUnitaryGroup (H := H)) :
    (groupPVM U_grp).diag = borelMeasure U_grp := rfl

/-- **The spectral measure of a self-adjoint operator.** -/
noncomputable def spectralPVM {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    ProjValMeasure H :=
  groupPVM (genToGroup hA)

@[simp] lemma spectralPVM_proj {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    (spectralPVM hA).proj = spectralProjection (genToGroup hA) := rfl

@[simp] lemma spectralPVM_diag {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    (spectralPVM hA).diag = borelMeasure (genToGroup hA) := rfl

/-! ## Existence -/

/-- **Existence**: the spectral measure of `A` represents its resolvent. -/
theorem spectralPVM_resolvent_formula {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (z : ℂ) (hz : z.im ≠ 0) (ξ : H) :
    ⟪ξ, selfAdjointResolvent hA z hz ξ⟫_ℂ
      = ∫ s, ((s : ℂ) - z)⁻¹ ∂((spectralPVM hA).diag ξ) := by
  rw [selfAdjointResolvent_eq_genToGroup hA z hz, spectralPVM_diag]
  exact inner_resolvent_diag_eq_integral (genToGroup hA) z hz ξ

/-! ## Uniqueness -/

/-- **Uniqueness**: any PVM representing the resolvent of `A` on its diagonal is
the spectral measure.  Cauchy-transform injectivity pins the diagonals;
polarization (inside `ext_of_diag`) pins the projections.  The rival's
`proj_univ` and `proj_inter` are never used. -/
theorem spectralPVM_unique {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (P : ProjValMeasure H)
    (hP : ∀ (z : ℂ) (hz : z.im ≠ 0) (ξ : H),
      ⟪ξ, selfAdjointResolvent hA z hz ξ⟫_ℂ = ∫ s, ((s : ℂ) - z)⁻¹ ∂(P.diag ξ)) :
    P = spectralPVM hA := by
  refine ProjValMeasure.ext_of_diag fun ξ => ?_
  refine measure_ext_of_cauchyTransform _ _ fun z hz_pos => ?_
  calc (∫ x, ((x : ℂ) - z)⁻¹ ∂(P.diag ξ))
      = ⟪ξ, selfAdjointResolvent hA z hz_pos.ne' ξ⟫_ℂ := (hP z hz_pos.ne' ξ).symm
    _ = ∫ x, ((x : ℂ) - z)⁻¹ ∂((spectralPVM hA).diag ξ) :=
        spectralPVM_resolvent_formula hA z hz_pos.ne' ξ

/-! ## The Keystone -/

/-- **The spectral theorem, resolvent form.**  Every self-adjoint operator on a
complex Hilbert space admits a unique projection-valued measure whose diagonal
measures represent its resolvent:

  `⟪ξ, (A − z)⁻¹ ξ⟫ = ∫ (s − z)⁻¹ d⟪ξ, E(·) ξ⟫(s)` for all `Im z ≠ 0`, `ξ ∈ H`.

Existence is `spectralPVM hA`, built from `e^{itA}` via Bochner–Herglotz and
Stone's theorem; uniqueness is Stieltjes inversion through the Cauchy transform.
-/
theorem spectralTheorem {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    ∃! P : ProjValMeasure H,
      ∀ (z : ℂ) (hz : z.im ≠ 0) (ξ : H),
        ⟪ξ, selfAdjointResolvent hA z hz ξ⟫_ℂ
          = ∫ s, ((s : ℂ) - z)⁻¹ ∂(P.diag ξ) :=
  ⟨spectralPVM hA, spectralPVM_resolvent_formula hA,
    fun P hP => spectralPVM_unique hA P hP⟩

/-! ## Coda: Stone's formula, finally about *the* spectral measure

With uniqueness in hand, `stonesFormula` is no longer a statement about the
projections of *a* calculus — it recovers the unique spectral measure of `A`
from boundary values of its resolvent. -/

theorem stonesFormula_spectralPVM {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (a b : ℝ) (hab : a < b) (ξ : H) :
    Tendsto (fun ε : ℝ =>
        spectralCalculus (genToGroup hA) (stoneSymbol a b ε)
          (stoneSymbol_measurable a b ε) (stoneSymbol_bdd a b ε) ξ)
      (𝓝[>] 0)
      (𝓝 (((spectralPVM hA).proj (Set.Ioo a b) measurableSet_Ioo
            + ((1 / 2 : ℂ) • (spectralPVM hA).proj {a} (measurableSet_singleton a)
                + (1 / 2 : ℂ) • (spectralPVM hA).proj {b}
                    (measurableSet_singleton b))) ξ)) :=
  stonesFormula (genToGroup hA) a b hab ξ

/-- Operator form: `e^{itA}` is the spectral-calculus exponential of A's spectral measure. -/
theorem genToGroup_eq_spectralCalculus_char {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (t : ℝ) :
    (genToGroup hA).U t
      = spectralCalculus (genToGroup hA) (fun l => cexp (I * l * t))
          (char_measurable t) (char_bdd t) :=
  (spectralCalculus_char (genToGroup hA) t).symm

/-- Scalar form: `⟪ξ, e^{itA} ξ⟫ = ∫ e^{itλ} dE_A(λ)`, against the diagonal of A's spectral PVM. -/
theorem inner_genToGroup_eq_integral {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (t : ℝ) (ξ : H) :
    ⟪ξ, (genToGroup hA).U t ξ⟫_ℂ
      = ∫ l, cexp (I * l * t) ∂((spectralPVM hA).diag ξ) := by
  simp only [spectralPVM_diag]
  rw [← spectralForm_self (genToGroup hA) ξ (char_measurable t) (char_bdd t)]
  exact (spectralForm_char (genToGroup hA) ξ ξ t).symm


end Spectra.QuantumMechanics.SpectralTheory
