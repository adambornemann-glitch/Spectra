/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: SpectralTheory/BorelCalculus.lean
-/
import Spectra.CayleyTransform.Defs        -- cayleyTransform, *_isStarNormal, *_unitary
import Spectra.CayleyTransform.Mobius           -- inverseMobius, inverseMobius_real
import Spectra.CayleyTransform.RieszMarkov       -- Riesz.spectralMeasure + cfcHom bridge
import Spectra.OneParameterUnitaryGroup.Basic
import Spectra.Resolvent.Integral.Domain   -- genToGroup, generator_genToGroup, group_unique
/-!
# Bounded Borel functional calculus of a normal operator, and Stone's group in spectral order

This file builds `e^{itA}` for a self-adjoint `A` *from* the spectral theory of its
Cayley transform `V = (A - i)(A + i)⁻¹`, rather than from the Yosida exponential.
This is the construction in Stone's 1932 order: spectral resolution first, group as
its corollary.

## Why a *Borel* calculus is required

`e^{itA}` pulls back, through the inverse Cayley (Möbius) map, to the symbol
`w ↦ exp (i t · inverseMobius w)` on `spectrum ℂ V ⊆ circle`.  That symbol is
unimodular but **discontinuous at `w = 1`**, and `1 ∈ spectrum ℂ V` exactly when `A`
is unbounded.  Mathlib's continuous functional calculus (`cfcHom`) demands continuity
on the spectrum, so it cannot evaluate this symbol; the bounded Borel extension below
is what is needed.

## Construction

The Borel calculus is assembled from the pieces already in the library:

* the spectral measure of `V` is `Spectra.Riesz.spectralMeasure V hn ξ`
  (`Measure (spectrum ℂ V)`), finite, with mass `‖ξ‖ ^ 2`;
* `Spectra.Riesz.integral_spectralMeasure_complex` / `inner_cfcHom_polarized`
  pin its agreement with `cfcHom` on continuous symbols;
* `Spectra.Riesz.norm_inner_cfcHom_le` gives the contraction bound.

`borelForm` is the polarized sesquilinear form against this measure (the analogue of
`crossInner` for a `Measure (spectrum ℂ V)`); `borelCalculus` is the bounded operator
it represents.  The single lemma with analytic weight is `borelCalculus_mul`
(multiplicativity on bounded Borel functions); it is free on continuous symbols and
extends by simple-function approximation + bounded convergence (`tendsto_borelCalculus_apply`).

## References

* Stone, "Linear Transformations in Hilbert Space" (1932), Chapter V.
* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], §VII–VIII.
-/

open Complex MeasureTheory Filter Topology InnerProductSpace
open scoped InnerProductSpace ComplexConjugate
open Spectra Spectra.Cayley Spectra.Riesz
open Spectra.QuantumMechanics.Observable
open UnboundedObservable
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.BorelCFC

/-! ## §1  The bounded Borel functional calculus of a normal operator -/

variable (U : H →L[ℂ] H) (hn : IsStarNormal U)

/-- The polarized sesquilinear form of a bounded Borel symbol `g` against the spectral
measure of `U`.  Mirrors `Spectra.Riesz.inner_cfcHom_polarized`, with the continuous
symbol replaced by an arbitrary measurable one. -/
noncomputable def borelForm (g : spectrum ℂ U → ℂ) (ξ η : H) : ℂ :=
  ( (∫ z, g z ∂(spectralMeasure U hn (ξ + η)))
    - (∫ z, g z ∂(spectralMeasure U hn (ξ - η)))
    - I * (∫ z, g z ∂(spectralMeasure U hn (ξ + I • η)))
    + I * (∫ z, g z ∂(spectralMeasure U hn (ξ - I • η))) ) / 4

/-- On the diagonal the form collapses to the spectral integral (uses the quadratic
homogeneity `μ (c • ξ) = ‖c‖ ^ 2 • μ ξ` of the spectral measure). -/
theorem borelForm_self (g : spectrum ℂ U → ℂ) (ξ : H) :
    borelForm U hn g ξ ξ = ∫ z, g z ∂(spectralMeasure U hn ξ) := by
  sorry

/-- Contraction bound for the form (the `crossInner_norm_le` analogue over the
spectrum). -/
theorem norm_borelForm_le {g : spectrum ℂ U → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ z, ‖g z‖ ≤ C) (ξ η : H) :
    ‖borelForm U hn g ξ η‖ ≤ C * (‖ξ‖ ^ 2 + ‖η‖ ^ 2) := by
  sorry

/-- The form is sesquilinear: conjugate-linear in the left slot. -/
theorem borelForm_add_left (g : spectrum ℂ U → ℂ) (ξ₁ ξ₂ η : H) :
    borelForm U hn g (ξ₁ + ξ₂) η = borelForm U hn g ξ₁ η + borelForm U hn g ξ₂ η := by
  sorry

theorem borelForm_smul_left (g : spectrum ℂ U → ℂ) (c : ℂ) (ξ η : H) :
    borelForm U hn g (c • ξ) η = conj c * borelForm U hn g ξ η := by
  sorry

theorem borelForm_add_right (g : spectrum ℂ U → ℂ) (ξ η₁ η₂ : H) :
    borelForm U hn g ξ (η₁ + η₂) = borelForm U hn g ξ η₁ + borelForm U hn g ξ η₂ := by
  sorry

theorem borelForm_smul_right (g : spectrum ℂ U → ℂ) (c : ℂ) (ξ η : H) :
    borelForm U hn g ξ (c • η) = c * borelForm U hn g ξ η := by
  sorry

/-- The bounded sesquilinear form bundled, ready for Riesz representation
(the analogue of your `spectralFormBilin`). -/
noncomputable def borelCalculusBilin (g : spectrum ℂ U → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ z, ‖g z‖ ≤ C) :
    H →L⋆[ℂ] H →L[ℂ] ℂ :=
  sorry

/-- **The bounded Borel functional calculus of `U`.**
`Φ_U(g) : H →L[ℂ] H` is the operator represented by `borelForm U hn g`. -/
noncomputable def borelCalculus (g : spectrum ℂ U → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ z, ‖g z‖ ≤ C) : H →L[ℂ] H :=
  sorry

/-- The characterizing property: matrix elements of `Φ_U(g)` are the polarized form. -/
theorem inner_borelCalculus (g : spectrum ℂ U → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ z, ‖g z‖ ≤ C) (ξ η : H) :
    ⟪ξ, borelCalculus U g hg_meas hg_bdd η⟫_ℂ = borelForm U hn g ξ η := by
  sorry

/-- Diagonal form of the characterization. -/
theorem inner_borelCalculus_self (g : spectrum ℂ U → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ z, ‖g z‖ ≤ C) (ξ : H) :
    ⟪ξ, borelCalculus U g hg_meas hg_bdd ξ⟫_ℂ = ∫ z, g z ∂(spectralMeasure U hn ξ) := by
  rw [inner_borelCalculus, borelForm_self]

/-- Operator-norm bound. -/
theorem norm_borelCalculus_le (g : spectrum ℂ U → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ z, ‖g z‖ ≤ C) {C : ℝ}
    (hC : ∀ z, ‖g z‖ ≤ C) :
    ‖borelCalculus U g hg_meas hg_bdd‖ ≤ C := by
  sorry

/-- On continuous symbols the Borel calculus is the continuous calculus. -/
theorem borelCalculus_eq_cfcHom (f : C(spectrum ℂ U, ℂ)) :
    borelCalculus U (fun z => f z) f.continuous.measurable ⟨‖f‖, fun z => f.norm_coe_le_norm z⟩
      = cfcHom hn f := by
  sorry

/-- `Φ_U(1) = id`  (uses `Spectra.Riesz.spectralMeasure_real_univ`). -/
theorem borelCalculus_one :
    borelCalculus U (fun _ => (1 : ℂ)) measurable_const ⟨1, fun _ => by simp⟩
      = ContinuousLinearMap.id ℂ H := by
  sorry

theorem borelCalculus_add (g h : spectrum ℂ U → ℂ)
    (hgm : Measurable g) (hgb : ∃ C, ∀ z, ‖g z‖ ≤ C)
    (hhm : Measurable h) (hhb : ∃ C, ∀ z, ‖h z‖ ≤ C)
    (hm : Measurable fun z => g z + h z) (hb : ∃ C, ∀ z, ‖g z + h z‖ ≤ C) :
    borelCalculus U (fun z => g z + h z) hm hb
      = borelCalculus U g hgm hgb + borelCalculus U h hhm hhb := by
  sorry

theorem borelCalculus_smul (c : ℂ) (g : spectrum ℂ U → ℂ)
    (hgm : Measurable g) (hgb : ∃ C, ∀ z, ‖g z‖ ≤ C)
    (hcm : Measurable fun z => c * g z) (hcb : ∃ C, ∀ z, ‖c * g z‖ ≤ C) :
    borelCalculus U (fun z => c * g z) hcm hcb = c • borelCalculus U g hgm hgb := by
  sorry

/-- `Φ_U(ḡ) = Φ_U(g)*`. -/
theorem borelCalculus_adjoint (g : spectrum ℂ U → ℂ)
    (hgm : Measurable g) (hgb : ∃ C, ∀ z, ‖g z‖ ≤ C)
    (hcm : Measurable fun z => conj (g z)) (hcb : ∃ C, ∀ z, ‖conj (g z)‖ ≤ C) :
    ContinuousLinearMap.adjoint (borelCalculus U g hgm hgb)
      = borelCalculus U (fun z => conj (g z)) hcm hcb := by
  sorry

/-- **Multiplicativity** — the one lemma with analytic weight.
Free on continuous symbols (`cfcHom` is a `*`-homomorphism); extend to bounded Borel
symbols by simple-function approximation and `tendsto_borelCalculus_apply`. -/
theorem borelCalculus_mul (g h : spectrum ℂ U → ℂ)
    (hgm : Measurable g) (hgb : ∃ C, ∀ z, ‖g z‖ ≤ C)
    (hhm : Measurable h) (hhb : ∃ C, ∀ z, ‖h z‖ ≤ C)
    (hghm : Measurable fun z => g z * h z) (hghb : ∃ C, ∀ z, ‖g z * h z‖ ≤ C) :
    (borelCalculus U g hgm hgb).comp (borelCalculus U h hhm hhb)
      = borelCalculus U (fun z => g z * h z) hghm hghb := by
  sorry

/-- Dominated-convergence engine: a uniformly bounded, pointwise-convergent net of
symbols converges in the strong operator topology.  (The driver for both
`borelCalculus_mul` and strong continuity of the group below.) -/
theorem tendsto_borelCalculus_apply {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {G : ι → spectrum ℂ U → ℂ} {g : spectrum ℂ U → ℂ}
    (hGm : ∀ n, Measurable (G n)) (hGb : ∀ n, ∃ C, ∀ z, ‖G n z‖ ≤ C)
    (hgm : Measurable g) (hgb : ∃ C, ∀ z, ‖g z‖ ≤ C)
    {C : ℝ} (hunif : ∀ n z, ‖G n z‖ ≤ C) (hlim : ∀ z, Tendsto (fun n => G n z) l (𝓝 (g z)))
    (ξ : H) :
    Tendsto (fun n => borelCalculus U (G n) (hGm n) (hGb n) ξ) l
      (𝓝 (borelCalculus U g hgm hgb ξ)) := by
  sorry

/-! ## §2  The Stone exponential symbol on the Cayley spectrum -/

open Spectra.OneParameterUnitaryGroup
open Spectra.Stoneslemma

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- The Cayley transform of a self-adjoint operator, as a bounded operator.
NB: confirm the witness lemma name matches `CayleyTransform/Transform.lean`
(`isFormalAdjoint_self_of_isSelfAdjoint` there vs. `isFormalAdjoint_of_isSelfAdjoint`
in the resolvent files). -/
noncomputable def cayley (hA : IsSelfAdjoint A) : H →L[ℂ] H :=
  cayleyTransform (isFormalAdjoint_self_of_isSelfAdjoint hA)
    (isSelfAdjoint_to_surjective hA).1

theorem cayley_isStarNormal (hA : IsSelfAdjoint A) : IsStarNormal (cayley hA) := by
  -- `cayleyTransform_isStarNormal _ _ (isSelfAdjoint_to_surjective hA).2`
  sorry

/-- The Stone symbol on `spectrum ℂ V`:  `w ↦ exp (i t · λ)` where `λ = inverseMobius w`
is the spectral value of `A`.  Unimodular, measurable, and discontinuous at `w = 1`. -/
noncomputable def stoneExpSymbol (hA : IsSelfAdjoint A) (t : ℝ) :
    spectrum ℂ (cayley hA) → ℂ :=
  fun z => Complex.exp (I * t * inverseMobius (z : ℂ))

theorem stoneExpSymbol_measurable (hA : IsSelfAdjoint A) (t : ℝ) :
    Measurable (stoneExpSymbol hA t) := by
  sorry

theorem stoneExpSymbol_norm_le_one (hA : IsSelfAdjoint A) (t : ℝ)
    (z : spectrum ℂ (cayley hA)) : ‖stoneExpSymbol hA t z‖ ≤ 1 := by
  -- on `spectrum ⊆ sphere 1`, `inverseMobius z` is real (`inverseMobius_real`),
  -- so the exponent is `i · real`; at the junk point `w = 1` the value is `1`.
  sorry

theorem stoneExpSymbol_bdd (hA : IsSelfAdjoint A) (t : ℝ) :
    ∃ C, ∀ z, ‖stoneExpSymbol hA t z‖ ≤ C :=
  ⟨1, stoneExpSymbol_norm_le_one hA t⟩

/-- The defining identity of the symbol family: `exp` turns the group law of `ℝ` into
pointwise multiplication. -/
theorem stoneExpSymbol_mul (hA : IsSelfAdjoint A) (s t : ℝ) :
    (fun z => stoneExpSymbol hA s z * stoneExpSymbol hA t z) = stoneExpSymbol hA (s + t) := by
  sorry

@[simp] theorem stoneExpSymbol_zero (hA : IsSelfAdjoint A) :
    stoneExpSymbol hA 0 = fun _ => (1 : ℂ) := by
  sorry

/-! ## §3  The spectral one-parameter group -/

/-- `e^{itA}`, defined spectrally: the bounded Borel calculus of the Cayley transform
applied to the pulled-back exponential symbol. -/
noncomputable def stoneExp (hA : IsSelfAdjoint A) (t : ℝ) : H →L[ℂ] H :=
  borelCalculus (cayley hA) (cayley_isStarNormal hA) (stoneExpSymbol hA t)
  /-hA : IsSelfAdjoint A) (s t : ℝ) :
Spectra.ModularTheory.KMS
Spectra.KMS
Application type mismatch: The argument
  cayley_isStarNormal hA
has type
  IsStarNormal (cayley hA)
of sort `Prop` but is expected to have type
  ↑(spectrum ℂ (cayley hA)) → ℂ
of sort `Type` in the application
  borelCalculus (cayley hA)-/
    (stoneExpSymbol_measurable hA t) (stoneExpSymbol_bdd hA t)

theorem stoneExp_identity (hA : IsSelfAdjoint A) (ψ : H) : stoneExp hA 0 ψ = ψ := by
  -- `stoneExpSymbol hA 0 = 1`, then `borelCalculus_one`.
  sorry

theorem stoneExp_group_law (hA : IsSelfAdjoint A) (s t : ℝ) (ψ : H) :
    stoneExp hA (s + t) ψ = stoneExp hA s (stoneExp hA t ψ) := by
  -- `stoneExpSymbol_mul` + `borelCalculus_mul`.
  sorry

theorem stoneExp_inner (hA : IsSelfAdjoint A) (t : ℝ) (ψ φ : H) :
    ⟪stoneExp hA t ψ, stoneExp hA t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ := by
  -- `borelCalculus_adjoint` + `borelCalculus_mul` with `conj g * g = 1` (|symbol| = 1).
  sorry

theorem stoneExp_strong_continuous (hA : IsSelfAdjoint A) (ψ : H) :
    Continuous (fun t => stoneExp hA t ψ) := by
  -- `tendsto_borelCalculus_apply` with pointwise continuity of `t ↦ stoneExpSymbol hA t z`,
  -- uniform bound `1`.
  sorry

open Spectra.StonesTheorem

/-- **Stone's group, built in spectral order.** -/
noncomputable def stoneGroup (hA : IsSelfAdjoint A) : OneParameterUnitaryGroup (H := H) where
  U := stoneExp hA
  unitary := fun t ψ φ => stoneExp_inner hA t ψ φ
  group_law := fun s t => ContinuousLinearMap.ext fun ψ => by
    rw [ContinuousLinearMap.comp_apply]; exact stoneExp_group_law hA s t ψ
  identity := ContinuousLinearMap.ext fun ψ => by
    rw [ContinuousLinearMap.id_apply]; exact stoneExp_identity hA ψ
  strong_continuous := fun ψ => stoneExp_strong_continuous hA ψ

/-! ## §4  Generator and the consistency with the Yosida construction -/
open Resolvent in
/-- The generator of the spectral group is `A`.  Mirrors `generator_genToGroup`:
`A ≤ generator (stoneGroup hA)` by the difference quotient of `stoneExp` through
`inverseMobius` (the Borel-calculus analogue of `generator_spectralCalculus`),
then maximality of self-adjoint operators. -/
theorem generator_stoneGroup (hA : IsSelfAdjoint A) : generator (stoneGroup hA) = A := by
  have hAle : A ≤ generator (stoneGroup hA) := by sorry
  exact (IsSelfAdjoint.eq_of_le hA (generator_isSelfAdjoint _) hAle).symm

/-- The spectral group agrees with the Yosida group: equal generators, then
`group_unique`.  This is the consistency statement closing the two constructions. -/
theorem stoneGroup_eq_genToGroup (hA : IsSelfAdjoint A) : stoneGroup hA = genToGroup hA :=
  group_unique _ _ (by rw [generator_stoneGroup hA, generator_genToGroup hA])

theorem stoneExp_eq_genToGroup (hA : IsSelfAdjoint A) (t : ℝ) :
    stoneExp hA t = (genToGroup hA).U t := by
  rw [show stoneExp hA t = (stoneGroup hA).U t from rfl, stoneGroup_eq_genToGroup hA]

end Spectra.BorelCFC
