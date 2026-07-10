/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.CayleyTransform.Generator.InverseAction
import Spectra.CayleyTransform.MapsResolvent
import Spectra.SpectralTheory.ResolventForm
/-!
# The resolvent of a self-adjoint operator through its Cayley transform

For `Im z ≠ 0` and `z ≠ −i`, the resolvent `(A − z)⁻¹` is an explicit **bounded** rational
expression in the Cayley transform `V = cayley hA`:

  `(A − z)⁻¹ = (i + z)⁻¹ (1 − V)(V − w₀)⁻¹`,    `w₀ = (z − i)/(z + i)`.

This is `selfAdjointResolvent_eq_operator` — **step 2** of `selfAdjointResolvent_eq_borelCalculus`
(see `CayleyTransform/Generator.lean`).  It is generator-free: the unbounded `A` enters only
through the inverse Cayley action `A ((1 − V)χ) = i (1 + V)χ` (`cayley_apply_one_sub`), the
invertibility of `V − w₀` (`cayley_maps_resolvent`), and uniqueness of solutions of
`(A − z)·  = φ` (`solution_unique`).  At `z = −i` the factor `(i + z)⁻¹` degenerates; that case
is `resolvent_at_neg_i_eq_cfc`.
-/
open Complex MeasureTheory
open scoped InnerProductSpace
open Spectra.Resolvent
open Spectra.YosidaHille
open Spectra.Operator
open Spectra.QuantumMechanics.SpectralTheory
open Spectra.BorelCFC
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H}
namespace Spectra.Cayley

/-- **Operator-form resolvent identity** (step 2 toward `selfAdjointResolvent_eq_borelCalculus`).
For `Im z ≠ 0` and `i + z ≠ 0`, the resolvent of `A` is a bounded rational function of the Cayley
transform `V = cayley hA`:  `(A − z)⁻¹ = (i + z)⁻¹ (1 − V)(V − w₀)⁻¹` with `w₀ = (z − i)/(z + i)`.

Proof: with `χ := (V − w₀)⁻¹ φ`, the vector `J := (i + z)⁻¹ (1 − V)χ` lies in `dom A`
(`cayley_one_sub_mem_domain`), and `A ((1 − V)χ) = i (1 + V)χ` (`cayley_apply_one_sub`) together
with `(V − w₀)χ = φ` and `(i + z)w₀ = z − i` give `(A − z)J = φ`; `solution_unique` identifies `J`
with `(A − z)⁻¹ φ`. -/
theorem selfAdjointResolvent_eq_operator [Nontrivial H] (hA : IsSelfAdjoint A) (z : ℂ)
    (hz : z.im ≠ 0) (hzi : I + z ≠ 0) :
    selfAdjointResolvent hA z hz
      = (I + z)⁻¹ • ((ContinuousLinearMap.id ℂ H - cayley hA).comp
          (Ring.inverse (cayley hA
            - ((z - I) * (z + I)⁻¹) • ContinuousLinearMap.id ℂ H))) := by
  have hzI : z + I ≠ 0 := by rwa [add_comm] at hzi
  -- `V − w₀` is invertible (`cayley_maps_resolvent`).
  have hUnit : IsUnit (cayley hA
      - ((z - I) * (z + I)⁻¹) • ContinuousLinearMap.id ℂ H) :=
    cayley_maps_resolvent (isFormalAdjoint_self_of_isSelfAdjoint hA)
      (isSelfAdjoint_to_surjective hA).1 (isSelfAdjoint_to_surjective hA).2 z hz
  refine ContinuousLinearMap.ext fun φ => ?_
  set χ : H := Ring.inverse (cayley hA
      - ((z - I) * (z + I)⁻¹) • ContinuousLinearMap.id ℂ H) φ with hχ_def
  -- `(V − w₀) χ = φ` (right inverse).
  have hχ : cayley hA χ - ((z - I) * (z + I)⁻¹) • χ = φ := by
    have h := DFunLike.congr_fun (Ring.mul_inverse_cancel _ hUnit) φ
    rw [hχ_def]
    simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.one_apply] using h
  -- the candidate solution `J = (i + z)⁻¹ (1 − V) χ ∈ dom A`.
  set J : A.domain := (I + z)⁻¹ • (⟨(ContinuousLinearMap.id ℂ H - cayley hA) χ,
      cayley_one_sub_mem_domain hA χ⟩ : A.domain) with hJ_def
  have hJcoe : (J : H) = (I + z)⁻¹ • (ContinuousLinearMap.id ℂ H - cayley hA) χ := by
    rw [hJ_def]; rfl
  have hAJ : A J = (I + z)⁻¹ • (I • (ContinuousLinearMap.id ℂ H + cayley hA) χ) := by
    rw [hJ_def, A.map_smul, cayley_apply_one_sub hA χ]
  -- `J` solves `(A − z)·  = φ`.
  have hUχ : cayley hA χ = φ + ((z - I) * (z + I)⁻¹) • χ := sub_eq_iff_eq_add.mp hχ
  have hJeq : A J - z • (J : H) = φ := by
    rw [hAJ, hJcoe]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply]
    rw [hUχ]
    match_scalars <;> field_simp [hzi, hzI] <;> ring
  -- uniqueness identifies `J` with the resolvent value.
  set R_sub : A.domain := Classical.choose
    (self_adjoint_range_all_z (isFormalAdjoint_of_isSelfAdjoint hA)
      (isSelfAdjoint_to_surjective hA).1 (isSelfAdjoint_to_surjective hA).2 z hz φ).exists
    with _hRsub_def
  have hR_eq : A R_sub - z • (R_sub : H) = φ := Classical.choose_spec
    (self_adjoint_range_all_z (isFormalAdjoint_of_isSelfAdjoint hA)
      (isSelfAdjoint_to_surjective hA).1 (isSelfAdjoint_to_surjective hA).2 z hz φ).exists
  have hR_res : selfAdjointResolvent hA z hz φ = (R_sub : H) := rfl
  have huniq : J = R_sub :=
    solution_unique (isFormalAdjoint_of_isSelfAdjoint hA) z hz φ J R_sub hJeq hR_eq
  rw [hR_res, ← congrArg Subtype.val huniq, hJcoe, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ← hχ_def]

/-- **Resolvent as the continuous functional calculus of the Cayley transform** (step 3 toward
`selfAdjointResolvent_eq_borelCalculus`).  Feeding the operator identity
`selfAdjointResolvent_eq_operator` through the cfc algebra (`cfc_mul`, `cfc_inv`, `cfc_sub`,
`cfc_id'`, `cfc_const`) rewrites it as a single continuous functional calculus:

  `(A − z)⁻¹ = cfc (fun w ↦ (i + z)⁻¹ (1 − w)(w − w₀)⁻¹) V`,    `w₀ = (z − i)/(z + i)`.

The symbol is continuous on `σ(V)` because `w₀ ∉ σ(V)` (`cayley_maps_resolvent`).  The remaining
step 4 replaces this continuous symbol by `(inverseMobius w − z)⁻¹`, which agrees with it off the
junk point `w = 1` (a `spectralMeasure`-null point). -/
theorem selfAdjointResolvent_eq_cfc [Nontrivial H] (hA : IsSelfAdjoint A) (z : ℂ)
    (hz : z.im ≠ 0) (hzi : I + z ≠ 0) :
    selfAdjointResolvent hA z hz
      = cfc (fun w : ℂ => (I + z)⁻¹ * ((1 - w) * (w - (z - I) * (z + I)⁻¹)⁻¹)) (cayley hA) := by
  have hn : IsStarNormal (cayley hA) := cayley_isStarNormal hA
  -- `V − w₀` is a unit, so `w₀ ∉ σ(V)` and the resolvent symbol is continuous on `σ(V)`.
  have hUnit : IsUnit (cayley hA - ((z - I) * (z + I)⁻¹) • (1 : H →L[ℂ] H)) := by
    rw [ContinuousLinearMap.one_def]
    exact cayley_maps_resolvent (isFormalAdjoint_self_of_isSelfAdjoint hA)
      (isSelfAdjoint_to_surjective hA).1 (isSelfAdjoint_to_surjective hA).2 z hz
  have hUnit2 : IsUnit (algebraMap ℂ (H →L[ℂ] H) ((z - I) * (z + I)⁻¹) - cayley hA) := by
    rw [Algebra.algebraMap_eq_smul_one,
      show ((z - I) * (z + I)⁻¹) • (1 : H →L[ℂ] H) - cayley hA
          = -(cayley hA - ((z - I) * (z + I)⁻¹) • (1 : H →L[ℂ] H)) by abel]
    exact hUnit.neg
  have hw₀spec : (z - I) * (z + I)⁻¹ ∉ spectrum ℂ (cayley hA) :=
    fun hmem => spectrum.mem_iff.mp hmem hUnit2
  have hw₀ : ∀ x ∈ spectrum ℂ (cayley hA), x - (z - I) * (z + I)⁻¹ ≠ 0 := by
    intro x hx h
    exact hw₀spec ((sub_eq_zero.mp h) ▸ hx)
  have hcontSub : ContinuousOn (fun w : ℂ => w - (z - I) * (z + I)⁻¹) (spectrum ℂ (cayley hA)) :=
    (continuous_id.sub continuous_const).continuousOn
  have hcontInv : ContinuousOn (fun w : ℂ => (w - (z - I) * (z + I)⁻¹)⁻¹)
      (spectrum ℂ (cayley hA)) := hcontSub.inv₀ hw₀
  have hcontProd : ContinuousOn (fun w : ℂ => (1 - w) * (w - (z - I) * (z + I)⁻¹)⁻¹)
      (spectrum ℂ (cayley hA)) := ((continuous_const.sub continuous_id).continuousOn).mul hcontInv
  -- cfc building blocks.
  have e1 : cfc (fun w : ℂ => 1 - w) (cayley hA) = 1 - cayley hA := by
    rw [cfc_sub (fun _ : ℂ => (1 : ℂ)) (fun w : ℂ => w) (cayley hA),
      cfc_const (1 : ℂ) (cayley hA), cfc_id' (R := ℂ) (a := cayley hA), map_one]
  have e2 : cfc (fun w : ℂ => w - (z - I) * (z + I)⁻¹) (cayley hA)
      = cayley hA - ((z - I) * (z + I)⁻¹) • (1 : H →L[ℂ] H) := by
    rw [cfc_sub (fun w : ℂ => w) (fun _ : ℂ => (z - I) * (z + I)⁻¹) (cayley hA),
      cfc_id' (R := ℂ) (a := cayley hA), cfc_const ((z - I) * (z + I)⁻¹) (cayley hA),
      Algebra.algebraMap_eq_smul_one]
  have e3 : cfc (fun w : ℂ => (w - (z - I) * (z + I)⁻¹)⁻¹) (cayley hA)
      = Ring.inverse (cayley hA - ((z - I) * (z + I)⁻¹) • (1 : H →L[ℂ] H)) := by
    rw [cfc_inv (fun w : ℂ => w - (z - I) * (z + I)⁻¹) (cayley hA) hw₀ hcontSub, e2]
  have e4 : cfc (fun w : ℂ => (1 - w) * (w - (z - I) * (z + I)⁻¹)⁻¹) (cayley hA)
      = (1 - cayley hA) * Ring.inverse (cayley hA - ((z - I) * (z + I)⁻¹) • (1 : H →L[ℂ] H)) := by
    rw [cfc_mul (fun w : ℂ => 1 - w) (fun w : ℂ => (w - (z - I) * (z + I)⁻¹)⁻¹) (cayley hA)
      (hg := hcontInv), e1, e3]
  rw [selfAdjointResolvent_eq_operator hA z hz hzi,
    cfc_const_mul (I + z)⁻¹ (fun w : ℂ => (1 - w) * (w - (z - I) * (z + I)⁻¹)⁻¹) (cayley hA)
      (hf := hcontProd), e4]
  rfl

/-- **Bridge `cfc → borelCalculus`.**  For a symbol continuous on `σ(V)`, the continuous
functional calculus coincides with the bounded Borel calculus (`borelCalculus_eq_cfcHom` plus the
`cfc`/`cfcHom` unfolding `cfc_apply`).  This is the connector that puts
`selfAdjointResolvent_eq_cfc` into the `borelCalculus` form used by the keystone. -/
theorem cfc_eq_borelCalculus (hA : IsSelfAdjoint A) (g : ℂ → ℂ)
    (hg : ContinuousOn g (spectrum ℂ (cayley hA)))
    (hmeas : Measurable fun w : spectrum ℂ (cayley hA) => g (w : ℂ))
    (hbdd : ∃ C, ∀ w : spectrum ℂ (cayley hA), ‖g (w : ℂ)‖ ≤ C) :
    cfc g (cayley hA)
      = borelCalculus (cayley hA) (cayley_isStarNormal hA) (fun w => g (w : ℂ)) hmeas hbdd := by
  have hn : IsStarNormal (cayley hA) := cayley_isStarNormal hA
  rw [cfc_apply (f := g) (a := cayley hA) (ha := hn) (hf := hg),
    ← borelCalculus_eq_cfcHom (cayley hA) hn ⟨_, hg.restrict⟩]
  exact borelCalculus_congr (cayley hA) hn (by funext w; rfl) _ _ hmeas hbdd

/-! ## Step 4 — replacing the continuous symbol by `resolventSymbol`

`g_z` and `resolventSymbol hA z` agree on `σ(V)` except at the single point `w = 1`, where
`inverseMobius` blows up.  The Borel calculus does not see that point because the Cayley spectral
measure has no atom there (`ker(1 − V) = 0`).  The two ingredients are a measure-a.e. congruence
for `borelCalculus`, and the no-atom fact. -/

/-- **`borelCalculus` congruence up to a.e. equality.**  If two bounded symbols agree
`spectralMeasure U hn v`-a.e. for every vector `v`, their Borel calculi coincide.  Route: the
polarized form `borelForm` is a fixed `ℂ`-combination of integrals `∫ g ∂(spectralMeasure U hn ·)`,
so `integral_congr_ae` on each of the four polarization vectors collapses the difference. -/
theorem borelCalculus_congr_ae {U : H →L[ℂ] H} (hn : IsStarNormal U)
    (g₁ g₂ : spectrum ℂ U → ℂ) (hm₁ : Measurable g₁) (hb₁ : ∃ C, ∀ z, ‖g₁ z‖ ≤ C)
    (hm₂ : Measurable g₂) (hb₂ : ∃ C, ∀ z, ‖g₂ z‖ ≤ C)
    (hae : ∀ v : H, g₁ =ᵐ[Spectra.Riesz.spectralMeasure U hn v] g₂) :
    borelCalculus U hn g₁ hm₁ hb₁ = borelCalculus U hn g₂ hm₂ hb₂ := by
  refine ContinuousLinearMap.ext fun η => ext_inner_left ℂ fun ξ => ?_
  rw [inner_borelCalculus U hn g₁ hm₁ hb₁ ξ η, inner_borelCalculus U hn g₂ hm₂ hb₂ ξ η]
  simp only [borelForm]
  rw [integral_congr_ae (hae (ξ + η)), integral_congr_ae (hae (ξ - η)),
    integral_congr_ae (hae (ξ + I • η)), integral_congr_ae (hae (ξ - I • η))]

/-- **`1` is not an eigenvalue of the Cayley transform.**  `(1 − V)x = 0 ⇒ x = 0`: from `Vx = x`
and unitarity `V⋆x = x`, the vector `x` is orthogonal to `range(1 − V) = dom A`
(`generator_domain_eq_range_one_minus_cayley`), which is dense, so `x = 0`. -/
theorem ker_one_sub_cayley (hA : IsSelfAdjoint A) (x : H)
    (hx : (ContinuousLinearMap.id ℂ H - cayley hA) x = 0) : x = 0 := by
  have hVx : cayley hA x = x := by
    have h := hx
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero] at h
    exact h.symm
  have hU : (cayley hA).adjoint * cayley hA = 1 ∧ cayley hA * (cayley hA).adjoint = 1 :=
    cayleyTransform_unitary (isFormalAdjoint_self_of_isSelfAdjoint hA)
      (isSelfAdjoint_to_surjective hA).1 (isSelfAdjoint_to_surjective hA).2
  have hVstar : (cayley hA).adjoint x = x := by
    have h1 : (cayley hA).adjoint (cayley hA x) = x := by
      rw [← ContinuousLinearMap.mul_apply, hU.1, ContinuousLinearMap.one_apply]
    rwa [hVx] at h1
  have hperp : ∀ y : H, ⟪x, (ContinuousLinearMap.id ℂ H - cayley hA) y⟫_ℂ = 0 := by
    intro y
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, inner_sub_right,
      ← ContinuousLinearMap.adjoint_inner_left, hVstar, sub_self]
  have hxdom : ∀ y ∈ (A.domain : Set H), ⟪x, y⟫_ℂ = 0 := by
    intro y hy
    rw [generator_domain_eq_range_one_minus_cayley (isFormalAdjoint_self_of_isSelfAdjoint hA)
      (isSelfAdjoint_to_surjective hA).1, SetLike.mem_coe, LinearMap.mem_range] at hy
    obtain ⟨χ, hχ⟩ := hy
    rw [ContinuousLinearMap.coe_coe] at hχ
    rw [← hχ]
    exact hperp χ
  have hself : ⟪x, x⟫_ℂ = 0 := by
    have hzero : (fun y => ⟪x, y⟫_ℂ) = fun _ : H => (0 : ℂ) :=
      Continuous.ext_on hA.dense_domain (continuous_const.inner continuous_id) continuous_const
        hxdom
    exact congrFun hzero x
  exact inner_self_eq_zero.mp hself

/-- **No atom of the Cayley spectral measure at `w = 1`.**  The spectral projection at the set
`{w | (w:ℂ) = 1}` is `0` (its range lies in `ker(1 − V) = 0` by `ker_one_sub_cayley`, using
`V · 1_S = 1_S`), so the measure of that set vanishes for every vector. -/
theorem spectralMeasure_one_eq_zero (hA : IsSelfAdjoint A) (v : H) :
    Spectra.Riesz.spectralMeasure (cayley hA) (cayley_isStarNormal hA) v
        {w : spectrum ℂ (cayley hA) | (w : ℂ) = 1} = 0 := by
  have hn : IsStarNormal (cayley hA) := cayley_isStarNormal hA
  set S : Set (spectrum ℂ (cayley hA)) := {w | (w : ℂ) = 1} with _hSdef
  have hSmeas : MeasurableSet S :=
    (measurableSet_singleton (1 : ℂ)).preimage continuous_subtype_val.measurable
  set χS : spectrum ℂ (cayley hA) → ℂ := Set.indicator S (fun _ => 1) with hχSdef
  have hχm : Measurable χS := measurable_const.indicator hSmeas
  have hχb : ∃ C, ∀ z, ‖χS z‖ ≤ C :=
    ⟨1, fun z => by rw [hχSdef, Set.indicator_apply]; split_ifs <;> simp⟩
  have hmid : Measurable (fun w : spectrum ℂ (cayley hA) => (w : ℂ)) :=
    continuous_subtype_val.measurable
  have hbid : ∃ C, ∀ w : spectrum ℂ (cayley hA), ‖(w : ℂ)‖ ≤ C := by
    refine ⟨1, fun w => ?_⟩
    have hmem := cayleyTransform_spectrum_subset_circle (isFormalAdjoint_self_of_isSelfAdjoint hA)
      (isSelfAdjoint_to_surjective hA).1 (isSelfAdjoint_to_surjective hA).2 w.2
    rw [Metric.mem_sphere, dist_zero_right] at hmem
    exact le_of_eq hmem
  have hVid : borelCalculus (cayley hA) hn (fun w => (w : ℂ)) hmid hbid = cayley hA := by
    rw [← cfc_eq_borelCalculus hA (fun w : ℂ => w) continuousOn_id hmid hbid]
    exact cfc_id' (R := ℂ) (a := cayley hA)
  have hpm : Measurable (fun w : spectrum ℂ (cayley hA) => (w : ℂ) * χS w) := hmid.mul hχm
  have hpb : ∃ C, ∀ z : spectrum ℂ (cayley hA), ‖(z : ℂ) * χS z‖ ≤ C :=
    ⟨1, fun z => by
      rw [hχSdef, Set.indicator_apply]
      split_ifs with hz
      · have hz1 : (z : ℂ) = 1 := hz
        rw [mul_one, hz1]; exact le_of_eq norm_one
      · rw [mul_zero, norm_zero]; exact zero_le_one⟩
  have hprodeq : (fun w : spectrum ℂ (cayley hA) => (w : ℂ) * χS w) = χS := by
    funext w
    rw [hχSdef, Set.indicator_apply]
    split_ifs with hw
    · rw [mul_one]; exact hw
    · rw [mul_zero]
  have hcomp : (cayley hA).comp (borelCalculus (cayley hA) hn χS hχm hχb)
      = borelCalculus (cayley hA) hn χS hχm hχb := by
    have h1 : (cayley hA).comp (borelCalculus (cayley hA) hn χS hχm hχb)
        = (borelCalculus (cayley hA) hn (fun w => (w : ℂ)) hmid hbid).comp
            (borelCalculus (cayley hA) hn χS hχm hχb) := by rw [hVid]
    rw [h1, borelCalculus_mul (cayley hA) hn (fun w => (w : ℂ)) χS hmid hbid hχm hχb hpm hpb,
      borelCalculus_congr (cayley hA) hn hprodeq hpm hpb hχm hχb]
  have hEzero : borelCalculus (cayley hA) hn χS hχm hχb = 0 := by
    refine ContinuousLinearMap.ext fun v' => ?_
    have hker : (ContinuousLinearMap.id ℂ H - cayley hA)
        (borelCalculus (cayley hA) hn χS hχm hχb v') = 0 := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
        ← ContinuousLinearMap.comp_apply, hcomp, sub_self]
    rw [ContinuousLinearMap.zero_apply]
    exact ker_one_sub_cayley hA _ hker
  have hint : ∫ z, χS z ∂(Spectra.Riesz.spectralMeasure (cayley hA) hn v) = 0 := by
    rw [← inner_borelCalculus_self (cayley hA) hn χS hχm hχb v, hEzero,
      ContinuousLinearMap.zero_apply, inner_zero_right]
  rw [hχSdef, integral_indicator_const (1 : ℂ) hSmeas, Complex.real_smul, mul_one] at hint
  have hreal : (Spectra.Riesz.spectralMeasure (cayley hA) hn v S).toReal = 0 :=
    Complex.ofReal_eq_zero.mp hint
  rcases (ENNReal.toReal_eq_zero_iff _).mp hreal with h | h
  · exact h
  · exact absurd h (measure_ne_top _ _)

/-- **The two symbols agree off `w = 1`.**  For `w ∈ σ(V)` with `(w:ℂ) ≠ 1`, the morally-correct
resolvent symbol `(inverseMobius w − z)⁻¹` equals the continuous symbol
`(i+z)⁻¹(1−w)(w−w₀)⁻¹`, `w₀ = (z−i)/(z+i)`.  Pure scalar algebra: `inverseMobius w − z =
(z+i)(w−w₀)/(1−w)`, and `w − w₀ ≠ 0` because `w₀ ∉ σ(V)`. -/
theorem resolventSymbol_eq_cts [Nontrivial H] (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0)
    (hzi : I + z ≠ 0) (w : spectrum ℂ (cayley hA)) (hw1 : (w : ℂ) ≠ 1) :
    resolventSymbol hA z w
      = (I + z)⁻¹ * ((1 - (w : ℂ)) * ((w : ℂ) - (z - I) * (z + I)⁻¹)⁻¹) := by
  have hzI : z + I ≠ 0 := by rwa [add_comm] at hzi
  have hUnit : IsUnit (cayley hA - ((z - I) * (z + I)⁻¹) • (1 : H →L[ℂ] H)) := by
    rw [ContinuousLinearMap.one_def]
    exact cayley_maps_resolvent (isFormalAdjoint_self_of_isSelfAdjoint hA)
      (isSelfAdjoint_to_surjective hA).1 (isSelfAdjoint_to_surjective hA).2 z hz
  have hUnit2 : IsUnit (algebraMap ℂ (H →L[ℂ] H) ((z - I) * (z + I)⁻¹) - cayley hA) := by
    rw [Algebra.algebraMap_eq_smul_one,
      show ((z - I) * (z + I)⁻¹) • (1 : H →L[ℂ] H) - cayley hA
          = -(cayley hA - ((z - I) * (z + I)⁻¹) • (1 : H →L[ℂ] H)) by abel]
    exact hUnit.neg
  have hww₀ : (w : ℂ) - (z - I) * (z + I)⁻¹ ≠ 0 := by
    rw [sub_ne_zero]; intro h
    exact spectrum.mem_iff.mp (h ▸ w.2) hUnit2
  have h1w : (1 : ℂ) - (w : ℂ) ≠ 0 := sub_ne_zero.mpr (fun h => hw1 h.symm)
  have _hnum : I * (1 + (w : ℂ)) - z * (1 - (w : ℂ)) ≠ 0 := by
    have heq : I * (1 + (w : ℂ)) - z * (1 - (w : ℂ))
        = (z + I) * ((w : ℂ) - (z - I) * (z + I)⁻¹) := by
      field_simp
      ring
    rw [heq]; exact mul_ne_zero hzI hww₀
  simp only [resolventSymbol, inverseMobius]
  field_simp
  ring

/-- **The keystone (steps 1–4 assembled).**  For `Im z ≠ 0` and `i + z ≠ 0`, the resolvent of `A`
is the bounded Borel calculus of the Cayley transform applied to `resolventSymbol hA z`
(`w ↦ (inverseMobius w − z)⁻¹`):

  `(A − z)⁻¹ = borelCalculus (cayley hA) _ (resolventSymbol hA z) _ _`.

Step 3 gives `(A − z)⁻¹ = borelCalculus _ g_z` for the continuous symbol `g_z`; `g_z` and
`resolventSymbol hA z` agree off `w = 1` (`resolventSymbol_eq_cts`), a point of zero Cayley
spectral measure (`spectralMeasure_one_eq_zero`), so `borelCalculus_congr_ae` swaps one for the
other.  (At `z = −i` use `resolvent_at_neg_i_eq_cfc`.) -/
theorem selfAdjointResolvent_eq_borelCalculus [Nontrivial H] (hA : IsSelfAdjoint A) (z : ℂ)
    (hz : z.im ≠ 0) (hzi : I + z ≠ 0) :
    selfAdjointResolvent hA z hz
      = borelCalculus (cayley hA) (cayley_isStarNormal hA) (resolventSymbol hA z)
          (resolventSymbol_measurable hA z) (resolventSymbol_bdd hA z hz) := by
  have hn : IsStarNormal (cayley hA) := cayley_isStarNormal hA
  have _hzI : z + I ≠ 0 := by rwa [add_comm] at hzi
  -- continuity of the continuous symbol `g_z` on `σ(V)` (`w₀ ∉ σ(V)`).
  have hUnit : IsUnit (cayley hA - ((z - I) * (z + I)⁻¹) • (1 : H →L[ℂ] H)) := by
    rw [ContinuousLinearMap.one_def]
    exact cayley_maps_resolvent (isFormalAdjoint_self_of_isSelfAdjoint hA)
      (isSelfAdjoint_to_surjective hA).1 (isSelfAdjoint_to_surjective hA).2 z hz
  have hUnit2 : IsUnit (algebraMap ℂ (H →L[ℂ] H) ((z - I) * (z + I)⁻¹) - cayley hA) := by
    rw [Algebra.algebraMap_eq_smul_one,
      show ((z - I) * (z + I)⁻¹) • (1 : H →L[ℂ] H) - cayley hA
          = -(cayley hA - ((z - I) * (z + I)⁻¹) • (1 : H →L[ℂ] H)) by abel]
    exact hUnit.neg
  have hw₀ : ∀ x ∈ spectrum ℂ (cayley hA), x - (z - I) * (z + I)⁻¹ ≠ 0 := fun x hx h =>
    spectrum.mem_iff.mp ((sub_eq_zero.mp h) ▸ hx) hUnit2
  have hgcont : ContinuousOn (fun w : ℂ => (I + z)⁻¹ * ((1 - w) * (w - (z - I) * (z + I)⁻¹)⁻¹))
      (spectrum ℂ (cayley hA)) :=
    continuousOn_const.mul (((continuous_const.sub continuous_id).continuousOn).mul
      (((continuous_id.sub continuous_const).continuousOn).inv₀ hw₀))
  have hmeas_cts : Measurable (fun w : spectrum ℂ (cayley hA) =>
      (I + z)⁻¹ * ((1 - (w : ℂ)) * ((w : ℂ) - (z - I) * (z + I)⁻¹)⁻¹)) := hgcont.restrict.measurable
  have hbdd_cts : ∃ C, ∀ w : spectrum ℂ (cayley hA),
      ‖(I + z)⁻¹ * ((1 - (w : ℂ)) * ((w : ℂ) - (z - I) * (z + I)⁻¹)⁻¹)‖ ≤ C := by
    obtain ⟨C, hC⟩ := resolventSymbol_bdd hA z hz
    refine ⟨C, fun w => ?_⟩
    by_cases hw1 : (w : ℂ) = 1
    · have hgz0 : (I + z)⁻¹ * ((1 - (w : ℂ)) * ((w : ℂ) - (z - I) * (z + I)⁻¹)⁻¹) = 0 := by
        rw [hw1]; simp
      rw [hgz0, norm_zero]
      exact le_trans (norm_nonneg _) (hC w)
    · rw [← resolventSymbol_eq_cts hA z hz hzi w hw1]; exact hC w
  -- step 3 in `borelCalculus` form.
  have h3 : selfAdjointResolvent hA z hz
      = borelCalculus (cayley hA) hn
          (fun w => (I + z)⁻¹ * ((1 - (w : ℂ)) * ((w : ℂ) - (z - I) * (z + I)⁻¹)⁻¹))
          hmeas_cts hbdd_cts := by
    rw [selfAdjointResolvent_eq_cfc hA z hz hzi]
    exact cfc_eq_borelCalculus hA _ hgcont hmeas_cts hbdd_cts
  -- step 4: swap the continuous symbol for `resolventSymbol` (a.e. equal, no atom at `w = 1`).
  rw [h3]
  refine borelCalculus_congr_ae hn _ (resolventSymbol hA z) hmeas_cts hbdd_cts
    (resolventSymbol_measurable hA z) (resolventSymbol_bdd hA z hz) (fun v => ?_)
  refine MeasureTheory.ae_iff.mpr (measure_mono_null (fun w hw => ?_)
    (spectralMeasure_one_eq_zero hA v))
  by_contra hwS
  exact hw (resolventSymbol_eq_cts hA z hz hzi w hwS).symm

end Spectra.Cayley
