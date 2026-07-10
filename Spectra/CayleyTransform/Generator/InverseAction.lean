/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.CayleyTransform.BorelCalculus
import Spectra.CayleyTransform.Defs
import Spectra.CayleyTransform.Inverse        -- inverse-Cayley action: one_minus/one_plus_cayley_apply
import Spectra.OneParameterUnitaryGroup.Basic
import Spectra.YosidaHille.Basic
import Spectra.Resolvent.Integral.Domain   -- genToGroup, generator_genToGroup, group_unique

/-!
# Stone's theorem via the Cayley transform

For a self-adjoint operator `A`, this file builds the unitary one-parameter group
`stoneExp hA t = e^{itA}` spectrally, as the Borel functional calculus of the (bounded,
star-normal) Cayley transform `cayley hA` applied to the pulled-back exponential symbol
`w ↦ exp(i t · inverseMobius w)`. It proves the group law, unitarity, and strong continuity, and
bundles the result into `stoneGroup hA : OneParameterUnitaryGroup`.

Along the way it also assembles the resolvent symbol `w ↦ (inverseMobius w - z)⁻¹` (bounded by
`|Im z|⁻¹` on the Cayley spectrum) and the diagonal spectral-integral identity for
`⟪ξ, stoneExp hA t ξ⟫`, plus the concrete inverse Cayley action recovering `A` from its Cayley
transform (`cayley_one_sub_mem_domain`, `cayley_apply_one_sub`).

The sole remaining analytic gap — identifying `stoneGroup hA` with the Yosida group
`genToGroup hA`, i.e. `generator (stoneGroup hA) = A` — is closed sorry-free in
`CayleyTransform/GeneratorStone.lean`, via the resolvent-symbol route sketched in §4 below.

## Main definitions

* `cayley`, `stoneExpSymbol`, `stoneExp`, `stoneGroup`: the Cayley transform, its exponential
  Borel symbol, the spectrally-defined unitary group, and its `OneParameterUnitaryGroup` bundle.
* `resolventSymbol`: the Borel symbol of the resolvent `(A - z)⁻¹` in the Cayley calculus.

## Main results

* `stoneExp_group_law`, `stoneExp_inner`, `stoneExp_strong_continuous`: the group law, unitarity,
  and strong continuity of `stoneExp`.
* `inner_stoneExp_self_eq_integral`: the diagonal matrix element of `e^{itA}` as a spectral
  integral over the Cayley spectrum.
* `cayley_apply_one_sub`: the concrete inverse Cayley transform, `A = i(1+V)(1-V)⁻¹`.
-/

open Complex MeasureTheory Filter Topology InnerProductSpace
open scoped InnerProductSpace ComplexConjugate ENNReal NNReal
open Spectra.YosidaHille
open Spectra.OneParameterUnitaryGroup
open Spectra.Resolvent
open Spectra.Operator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Cayley
open BorelCFC

/-! ## §2  The Stone exponential symbol on the Cayley spectrum -/

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- The Cayley transform of a self-adjoint operator, as a bounded operator. -/
noncomputable def cayley (hA : IsSelfAdjoint A) : H →L[ℂ] H :=
  cayleyTransform (isFormalAdjoint_self_of_isSelfAdjoint hA)
    (isSelfAdjoint_to_surjective hA).1

/-- The Cayley transform `cayley hA` is star-normal, so it admits a Borel functional calculus. -/
theorem cayley_isStarNormal (hA : IsSelfAdjoint A) : IsStarNormal (cayley hA) := by
  exact cayleyTransform_isStarNormal _ _ (isSelfAdjoint_to_surjective hA).2

/-- The Stone symbol on `spectrum ℂ V`:  `w ↦ exp (i t · λ)` where `λ = inverseMobius w`
is the spectral value of `A`.  Unimodular, measurable, and discontinuous at `w = 1`. -/
noncomputable def stoneExpSymbol (hA : IsSelfAdjoint A) (t : ℝ) :
    spectrum ℂ (cayley hA) → ℂ :=
  fun z => Complex.exp (I * t * inverseMobius (z : ℂ))

/-- The Stone symbol `stoneExpSymbol hA t` is measurable on `spectrum ℂ (cayley hA)`. -/
theorem stoneExpSymbol_measurable (hA : IsSelfAdjoint A) (t : ℝ) :
    Measurable (stoneExpSymbol hA t) := by
  have hmob : Measurable (inverseMobius : ℂ → ℂ) := by
    unfold inverseMobius
    exact (measurable_const.mul (measurable_const.add measurable_id)).div
      (measurable_const.sub measurable_id)
  have hcoe : Measurable (fun z : spectrum ℂ (cayley hA) => (z : ℂ)) :=
    continuous_subtype_val.measurable
  exact Complex.continuous_exp.measurable.comp (measurable_const.mul (hmob.comp hcoe))

/-- On the Cayley spectrum the inverse Möbius value is real: for `z ≠ 1` by
`inverseMobius_real` (the spectrum sits on the unit circle), and at the junk point `z = 1`
the convention `_/0 = 0` makes `inverseMobius 1 = 0`. -/
lemma inverseMobius_im_eq_zero_of_mem_spectrum (hA : IsSelfAdjoint A)
    (z : spectrum ℂ (cayley hA)) : (inverseMobius (z : ℂ)).im = 0 := by
  by_cases hz1 : (z : ℂ) = 1
  · simp [inverseMobius, hz1]
  · have hsub := cayleyTransform_spectrum_subset_circle
      (isFormalAdjoint_self_of_isSelfAdjoint hA) (isSelfAdjoint_to_surjective hA).1
      (isSelfAdjoint_to_surjective hA).2
    have hmem : (z : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := hsub z.2
    have hnorm : ‖(z : ℂ)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hmem
    exact inverseMobius_real (z : ℂ) hnorm hz1

/-- The Stone symbol is unimodular: `‖stoneExpSymbol hA t z‖ ≤ 1` (in fact `= 1`) on the
spectrum. -/
theorem stoneExpSymbol_norm_le_one (hA : IsSelfAdjoint A) (t : ℝ)
    (z : spectrum ℂ (cayley hA)) : ‖stoneExpSymbol hA t z‖ ≤ 1 := by
  have him : (inverseMobius (z : ℂ)).im = 0 := inverseMobius_im_eq_zero_of_mem_spectrum hA z
  have hre : (I * (t : ℂ) * inverseMobius (z : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, him]
  rw [stoneExpSymbol, Complex.norm_exp, hre, Real.exp_zero]

/-- The Stone symbol is bounded on the spectrum, with bound `1`. -/
theorem stoneExpSymbol_bdd (hA : IsSelfAdjoint A) (t : ℝ) :
    ∃ C, ∀ z, ‖stoneExpSymbol hA t z‖ ≤ C :=
  ⟨1, stoneExpSymbol_norm_le_one hA t⟩

/-- The symbol is unimodular: `conj(σ_t) · σ_t = 1` (its exponent is purely imaginary). -/
theorem stoneExpSymbol_conj_mul (hA : IsSelfAdjoint A) (t : ℝ) (z : spectrum ℂ (cayley hA)) :
    starRingEnd ℂ (stoneExpSymbol hA t z) * stoneExpSymbol hA t z = 1 := by
  have hre : (I * (t : ℂ) * inverseMobius (z : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, inverseMobius_im_eq_zero_of_mem_spectrum hA z]
  have hnorm : ‖stoneExpSymbol hA t z‖ = 1 := by
    rw [stoneExpSymbol, Complex.norm_exp, hre, Real.exp_zero]
  rw [RCLike.conj_mul, hnorm]; norm_num

/-- The defining identity of the symbol family: `exp` turns the group law of `ℝ` into
pointwise multiplication. -/
theorem stoneExpSymbol_mul (hA : IsSelfAdjoint A) (s t : ℝ) :
    (fun z => stoneExpSymbol hA s z * stoneExpSymbol hA t z) = stoneExpSymbol hA (s + t) := by
  funext z
  rw [stoneExpSymbol, stoneExpSymbol, stoneExpSymbol, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- At `t = 0` the Stone symbol is the constant `1`. -/
@[simp] theorem stoneExpSymbol_zero (hA : IsSelfAdjoint A) :
    stoneExpSymbol hA 0 = fun _ => (1 : ℂ) := by
  funext z
  simp [stoneExpSymbol]

/-! ## §3  The spectral one-parameter group -/

/-- `e^{itA}`, defined spectrally: the bounded Borel calculus of the Cayley transform
applied to the pulled-back exponential symbol. -/
noncomputable def stoneExp (hA : IsSelfAdjoint A) (t : ℝ) : H →L[ℂ] H :=
  borelCalculus (cayley hA) (cayley_isStarNormal hA) (stoneExpSymbol hA t)
    (stoneExpSymbol_measurable hA t) (stoneExpSymbol_bdd hA t)

/-- The identity element: `e^{i·0·A} = 1`, i.e. `stoneExp hA 0 ψ = ψ`. -/
theorem stoneExp_identity (hA : IsSelfAdjoint A) (ψ : H) : stoneExp hA 0 ψ = ψ := by
  have h : stoneExp hA 0 = ContinuousLinearMap.id ℂ H := by
    refine (borelCalculus_congr (cayley hA) (cayley_isStarNormal hA) (stoneExpSymbol_zero hA)
      (stoneExpSymbol_measurable hA 0) (stoneExpSymbol_bdd hA 0)
      measurable_const ⟨1, fun _ => by simp⟩).trans ?_
    exact borelCalculus_one (cayley hA) (cayley_isStarNormal hA)
  rw [h, ContinuousLinearMap.id_apply]

/-- The group law: `e^{i(s+t)A} = e^{isA} e^{itA}`, i.e.
`stoneExp hA (s + t) = stoneExp hA s ∘ stoneExp hA t`. -/
theorem stoneExp_group_law (hA : IsSelfAdjoint A) (s t : ℝ) (ψ : H) :
    stoneExp hA (s + t) ψ = stoneExp hA s (stoneExp hA t ψ) := by
  have hprodm : Measurable fun z => stoneExpSymbol hA s z * stoneExpSymbol hA t z :=
    (stoneExpSymbol_measurable hA s).mul (stoneExpSymbol_measurable hA t)
  have hprodb : ∃ C, ∀ z, ‖stoneExpSymbol hA s z * stoneExpSymbol hA t z‖ ≤ C :=
    ⟨1, fun z => by
      rw [norm_mul]
      nlinarith [stoneExpSymbol_norm_le_one hA s z, stoneExpSymbol_norm_le_one hA t z,
        norm_nonneg (stoneExpSymbol hA s z), norm_nonneg (stoneExpSymbol hA t z)]⟩
  have hop : stoneExp hA (s + t) = (stoneExp hA s).comp (stoneExp hA t) := by
    have hmul := borelCalculus_mul (cayley hA) (cayley_isStarNormal hA)
      (stoneExpSymbol hA s) (stoneExpSymbol hA t)
      (stoneExpSymbol_measurable hA s) (stoneExpSymbol_bdd hA s)
      (stoneExpSymbol_measurable hA t) (stoneExpSymbol_bdd hA t)
      hprodm hprodb
    have hcongr := borelCalculus_congr (cayley hA) (cayley_isStarNormal hA)
      (stoneExpSymbol_mul hA s t) hprodm hprodb
      (stoneExpSymbol_measurable hA (s + t)) (stoneExpSymbol_bdd hA (s + t))
    change borelCalculus (cayley hA) (cayley_isStarNormal hA) (stoneExpSymbol hA (s + t))
          (stoneExpSymbol_measurable hA (s + t)) (stoneExpSymbol_bdd hA (s + t))
        = (borelCalculus (cayley hA) (cayley_isStarNormal hA) (stoneExpSymbol hA s)
            (stoneExpSymbol_measurable hA s) (stoneExpSymbol_bdd hA s)).comp
          (borelCalculus (cayley hA) (cayley_isStarNormal hA) (stoneExpSymbol hA t)
            (stoneExpSymbol_measurable hA t) (stoneExpSymbol_bdd hA t))
    rw [hmul, hcongr]
  rw [hop, ContinuousLinearMap.comp_apply]

/-- `stoneExp hA t` is unitary: it preserves the inner product, `⟪e^{itA}ψ, e^{itA}φ⟫ = ⟪ψ, φ⟫`. -/
theorem stoneExp_inner (hA : IsSelfAdjoint A) (t : ℝ) (ψ φ : H) :
    ⟪stoneExp hA t ψ, stoneExp hA t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ := by
  have hcm : Measurable fun z => conj (stoneExpSymbol hA t z) :=
    Complex.continuous_conj.measurable.comp (stoneExpSymbol_measurable hA t)
  have hcb : ∃ C, ∀ z, ‖conj (stoneExpSymbol hA t z)‖ ≤ C :=
    ⟨1, fun z => by rw [RCLike.norm_conj]; exact stoneExpSymbol_norm_le_one hA t z⟩
  have hprodm : Measurable fun z => conj (stoneExpSymbol hA t z) * stoneExpSymbol hA t z :=
    hcm.mul (stoneExpSymbol_measurable hA t)
  have hprodb : ∃ C, ∀ z, ‖conj (stoneExpSymbol hA t z) * stoneExpSymbol hA t z‖ ≤ C :=
    ⟨1, fun z => by rw [stoneExpSymbol_conj_mul]; simp⟩
  -- `(stoneExp t)* ∘ (stoneExp t) = Φ(conj σ · σ) = Φ(1) = id`
  have hadj := borelCalculus_adjoint (cayley hA) (cayley_isStarNormal hA) (stoneExpSymbol hA t)
    (stoneExpSymbol_measurable hA t) (stoneExpSymbol_bdd hA t) hcm hcb
  have hmul := borelCalculus_mul (cayley hA) (cayley_isStarNormal hA)
    (fun z => conj (stoneExpSymbol hA t z)) (stoneExpSymbol hA t)
    hcm hcb (stoneExpSymbol_measurable hA t) (stoneExpSymbol_bdd hA t)
    hprodm hprodb
  have hone : borelCalculus (cayley hA) (cayley_isStarNormal hA)
      (fun z => conj (stoneExpSymbol hA t z) * stoneExpSymbol hA t z) hprodm hprodb
        = ContinuousLinearMap.id ℂ H := by
    refine (borelCalculus_congr (cayley hA) (cayley_isStarNormal hA)
      (funext fun z => stoneExpSymbol_conj_mul hA t z) hprodm hprodb
      measurable_const ⟨1, fun _ => by simp⟩).trans ?_
    exact borelCalculus_one (cayley hA) (cayley_isStarNormal hA)
  have hid : (ContinuousLinearMap.adjoint (stoneExp hA t)).comp (stoneExp hA t)
      = ContinuousLinearMap.id ℂ H := by
    have e1 : ContinuousLinearMap.adjoint (stoneExp hA t)
        = borelCalculus (cayley hA) (cayley_isStarNormal hA)
          (fun z => conj (stoneExpSymbol hA t z)) hcm hcb := hadj
    rw [e1]
    exact hmul.trans hone
  calc ⟪stoneExp hA t ψ, stoneExp hA t φ⟫_ℂ
      = ⟪ψ, ContinuousLinearMap.adjoint (stoneExp hA t) (stoneExp hA t φ)⟫_ℂ :=
        (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
    _ = ⟪ψ, (ContinuousLinearMap.adjoint (stoneExp hA t)).comp (stoneExp hA t) φ⟫_ℂ := by
        rw [ContinuousLinearMap.comp_apply]
    _ = ⟪ψ, φ⟫_ℂ := by rw [hid, ContinuousLinearMap.id_apply]

/-- Strong continuity: `t ↦ stoneExp hA t ψ` is continuous for each `ψ`. -/
theorem stoneExp_strong_continuous (hA : IsSelfAdjoint A) (ψ : H) :
    Continuous (fun t => stoneExp hA t ψ) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have hlim : ∀ z, Tendsto (fun t => stoneExpSymbol hA t z) (𝓝 t₀)
      (𝓝 (stoneExpSymbol hA t₀ z)) := by
    intro z
    have hcont : Continuous (fun t : ℝ => stoneExpSymbol hA t z) := by
      simp only [stoneExpSymbol]
      exact Complex.continuous_exp.comp
        ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
    exact hcont.continuousAt
  exact tendsto_borelCalculus_apply (cayley hA) (cayley_isStarNormal hA)
    (G := fun t => stoneExpSymbol hA t) (g := stoneExpSymbol hA t₀)
    (fun t => stoneExpSymbol_measurable hA t) (fun t => stoneExpSymbol_bdd hA t)
    (stoneExpSymbol_measurable hA t₀) (stoneExpSymbol_bdd hA t₀)
    (C := 1) (fun t z => stoneExpSymbol_norm_le_one hA t z) hlim ψ

/-- **Stone's group, built in spectral order.** -/
noncomputable def stoneGroup (hA : IsSelfAdjoint A) : OneParameterUnitaryGroup (H := H) where
  U := stoneExp hA
  unitary := fun t ψ φ => stoneExp_inner hA t ψ φ
  group_law := fun s t => ContinuousLinearMap.ext fun ψ => by
    rw [ContinuousLinearMap.comp_apply]; exact stoneExp_group_law hA s t ψ
  identity := ContinuousLinearMap.ext fun ψ => by
    rw [ContinuousLinearMap.id_apply]; exact stoneExp_identity hA ψ
  strong_continuous := fun ψ => stoneExp_strong_continuous hA ψ

/-! ## §4  Generator and the consistency with the Yosida construction

`A ≤ generator (stoneGroup hA)` unfolds (Mathlib `LinearPMap.le`) to a domain inclusion plus
value agreement, and — exactly as in `generator_genToGroup` (`Stone/Basic.lean`) — both reduce
to a single difference-quotient limit, `stoneExp_genDiffQuot_tendsto`.  That limit is the **sole
analytic gap** left in this file; everything else here is structural.

### Toward the limit: the resolvent symbol (the recommended, non-circular route)

The honest way to obtain `stoneExp_genDiffQuot_tendsto` avoids differentiating the spectral
integral.  It identifies `stoneGroup hA` with the Yosida group `genToGroup hA` *directly*, by
matching the **resolvent** of `A` against the Borel calculus of the Cayley transform and then
invoking PVM uniqueness (`SpectralTheory.spectralPVM_unique`).  Crucially the resolvent is a
*bounded* Borel symbol: on `spectrum ℂ (cayley hA)` the value `inverseMobius w` is real
(`inverseMobius_im_eq_zero_of_mem_spectrum`), so `|inverseMobius w − z| ≥ |Im z|`.  The opening
lemmas of that route — the resolvent symbol with its bound, and the spectral-integral form of
`⟪ξ, stoneExp t ξ⟫` — are proved below and are reusable in their own right. -/

/-- The Borel symbol of the resolvent `(A − z)⁻¹` in the Cayley calculus:
`w ↦ (inverseMobius w − z)⁻¹`.  Bounded by `|Im z|⁻¹` on the spectrum (`resolventSymbol_bdd`). -/
noncomputable def resolventSymbol (hA : IsSelfAdjoint A) (z : ℂ) :
    spectrum ℂ (cayley hA) → ℂ :=
  fun w => (inverseMobius (w : ℂ) - z)⁻¹

/-- The resolvent symbol `resolventSymbol hA z` is measurable on `spectrum ℂ (cayley hA)`. -/
theorem resolventSymbol_measurable (hA : IsSelfAdjoint A) (z : ℂ) :
    Measurable (resolventSymbol hA z) := by
  have hmob : Measurable (inverseMobius : ℂ → ℂ) := by
    unfold inverseMobius
    exact (measurable_const.mul (measurable_const.add measurable_id)).div
      (measurable_const.sub measurable_id)
  have hcoe : Measurable (fun w : spectrum ℂ (cayley hA) => (w : ℂ)) :=
    continuous_subtype_val.measurable
  change Measurable fun w : spectrum ℂ (cayley hA) => (inverseMobius (w : ℂ) - z)⁻¹
  exact ((measurable_id.sub measurable_const).inv).comp (hmob.comp hcoe)

/-- On the Cayley spectrum the resolvent symbol is bounded by `|Im z|⁻¹`: there
`inverseMobius w` is real, so `inverseMobius w − z` has imaginary part `−Im z`. -/
theorem resolventSymbol_bdd (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) :
    ∃ C, ∀ w, ‖resolventSymbol hA z w‖ ≤ C := by
  refine ⟨|z.im|⁻¹, fun w => ?_⟩
  have him : (inverseMobius (w : ℂ)).im = 0 := inverseMobius_im_eq_zero_of_mem_spectrum hA w
  have hden : |z.im| ≤ ‖inverseMobius (w : ℂ) - z‖ := by
    calc |z.im| = |(inverseMobius (w : ℂ) - z).im| := by
          rw [Complex.sub_im, him, zero_sub, abs_neg]
      _ ≤ ‖inverseMobius (w : ℂ) - z‖ := Complex.abs_im_le_norm _
  change ‖(inverseMobius (w : ℂ) - z)⁻¹‖ ≤ |z.im|⁻¹
  rw [norm_inv, inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le (abs_pos.mpr hz) hden

/-- Diagonal matrix element of `e^{itA}` as a spectral integral over the Cayley spectrum:
`⟪ξ, stoneExp t ξ⟫ = ∫ exp(i t · inverseMobius w) dμ_ξ(w)`.  One application of
`inner_borelCalculus_self`; the bridge between the group and the Cayley spectral measure. -/
theorem inner_stoneExp_self_eq_integral (hA : IsSelfAdjoint A) (t : ℝ) (ξ : H) :
    ⟪ξ, stoneExp hA t ξ⟫_ℂ
      = ∫ z, stoneExpSymbol hA t z
          ∂(Spectra.Riesz.spectralMeasure (cayley hA) (cayley_isStarNormal hA) ξ) :=
  inner_borelCalculus_self (cayley hA) (cayley_isStarNormal hA) (stoneExpSymbol hA t)
    (stoneExpSymbol_measurable hA t) (stoneExpSymbol_bdd hA t) ξ

/-- **Inverse Cayley action (domain).**  `(1 − V)χ ∈ dom A` for every `χ`, since
`dom A = range(1 − V)` (`generator_domain_eq_range_one_minus_cayley`).  Concretely
`(1 − V)χ = 2i ψ` for the `ψ ∈ dom A` with `(A + i)ψ = χ`. -/
theorem cayley_one_sub_mem_domain (hA : IsSelfAdjoint A) (χ : H) :
    (ContinuousLinearMap.id ℂ H - cayley hA) χ ∈ A.domain := by
  obtain ⟨ψ, hψ⟩ := (isSelfAdjoint_to_surjective hA).1 χ
  have h1 : (ContinuousLinearMap.id ℂ H - cayley hA) χ = (2 * I) • (ψ : H) := by
    rw [← hψ]
    exact one_minus_cayley_apply (isFormalAdjoint_self_of_isSelfAdjoint hA)
      (isSelfAdjoint_to_surjective hA).1 ψ
  rw [h1]
  exact A.domain.smul_mem (2 * I) ψ.2

/-- **Inverse Cayley action (value).**  `A ((1 − V)χ) = i (1 + V)χ`.  With
`cayley_one_sub_mem_domain` this is the concrete inverse Cayley transform
`A = i (1 + V)(1 − V)⁻¹` — the bounded handle on the unbounded `A`.  It is the engine of the
resolvent identity `(A − z)⁻¹ = (i + z)⁻¹ (1 − V)(V − w₀)⁻¹`, `w₀ = (z − i)/(z + i)`: for
`χ := (V − w₀)⁻¹ φ` one computes `(A − z)((i+z)⁻¹(1 − V)χ) = φ` and `solution_unique` closes it
(no functional calculus, no measure theory). -/
theorem cayley_apply_one_sub (hA : IsSelfAdjoint A) (χ : H) :
    A ⟨(ContinuousLinearMap.id ℂ H - cayley hA) χ, cayley_one_sub_mem_domain hA χ⟩
      = I • (ContinuousLinearMap.id ℂ H + cayley hA) χ := by
  obtain ⟨ψ, hψ⟩ := (isSelfAdjoint_to_surjective hA).1 χ
  have h1 : (ContinuousLinearMap.id ℂ H - cayley hA) χ = (2 * I) • (ψ : H) := by
    rw [← hψ]
    exact one_minus_cayley_apply (isFormalAdjoint_self_of_isSelfAdjoint hA)
      (isSelfAdjoint_to_surjective hA).1 ψ
  have h2 : (ContinuousLinearMap.id ℂ H + cayley hA) χ = (2 : ℂ) • A ψ := by
    rw [← hψ]
    exact one_plus_cayley_apply (isFormalAdjoint_self_of_isSelfAdjoint hA)
      (isSelfAdjoint_to_surjective hA).1 ψ
  have hsub : (⟨(ContinuousLinearMap.id ℂ H - cayley hA) χ,
      cayley_one_sub_mem_domain hA χ⟩ : A.domain) = (2 * I) • ψ := Subtype.ext h1
  rw [hsub, A.map_smul, h2, smul_smul]
  congr 1
  ring

/-! ## §4  Generator and the consistency with the Yosida construction

`generator (stoneGroup hA) = A`, `stoneGroup hA = genToGroup hA`, and the difference-quotient
limit `stoneExp_genDiffQuot_tendsto` are proved **sorry-free** in
`CayleyTransform/GeneratorStone.lean`, via the keystone `selfAdjointResolvent_eq_borelCalculus`
(`GeneratorResolvent.lean`) + the characteristic-function pushforward feeding
`measure_ext_of_cauchyTransform` — never touching the generator until the final rewrite. -/

end Spectra.Cayley
