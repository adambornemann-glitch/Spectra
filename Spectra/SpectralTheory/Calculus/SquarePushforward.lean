/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SpectralTheory.Calculus.MixedProduct
/-!
# KILL-SPIKE — the `s ↦ s²` resolvent identity (Field-3 polar-uniqueness, DAG node 1.2)

This file is the **kill-spike** for the Field-3 polar-uniqueness plan
(`Spectra-Vault/Projects/Modular Theory/Field 3 - Polar Uniqueness Plan.md`). The plan's keystone is
`posSqrt_unique` (`P,Q ≥ 0` self-adjoint, `P² = Q² ⟹ P = Q`), built from an `s ↦ s²` spectral
pushforward `E^{A²} = (·²)_* E^A`. The single load-bearing prerequisite — and the cheapest binary
go/no-go for the whole route — is the **resolvent identity** connecting the resolvent of `A²` to the
bounded spectral-calculus symbol `1/(s² − z)`:

> `(A² − z)⁻¹ = Φ(1/(s² − z))`  and hence  `⟪ξ, (A²−z)⁻¹ ξ⟫ = ∫ (s²−z)⁻¹ dμ^E_ξ`.

**Result: GREEN.** Both are proved here, sorry-free, for an arbitrary one-parameter unitary group
`U_grp` (so in particular for the modular group `genToGroup Δ`), with
`A² := pmapOfPVM U_grp (s ↦ s²)`:

* `resolvent_sq_identity` — `A²(Φ(1/(s²−z)) ξ) = ξ + z • Φ(1/(s²−z)) ξ`, i.e. `Φ(1/(s²−z))` is the
  right-inverse of `A² − z` (the resolvent identity). Proved via the **mixed bounded/unbounded
  product law** `pmapOfPVM_spectralCalculus_of_mul_bounded` on the `s²` symbol composed with the
  bounded resolvent symbol `1/(s²−z)`, then the pointwise arithmetic `s²·1/(s²−z) = 1 + z·1/(s²−z)`.
* `resolvent_sq_symbols` — the measurability/boundedness/domain-membership witnesses are inhabited
  (the spike is non-vacuous); `resolvent_sq_identity'` packages the identity from just `(z, hz, ξ)`.
* `inner_resolvent_sq` — the pairing `⟪ξ, Φ(1/(s²−z)) ξ⟫ = ∫ (s²−z)⁻¹ dμ^E_ξ`
  (free, from `inner_spectralCalculus` + `spectralForm_self`).

Together these ARE DAG node 1.2 — the `s ↦ s²` machinery works on Spectra's calculus with no new
analytic infrastructure, using only the already-built mixed product law and change-of-density.

**Import hygiene (done).** The two generic lemmas reused here —
`mem_pmapDomain_spectralCalculus` and `pmapOfPVM_spectralCalculus_of_mul_bounded` — now live in the
`J`-free `Spectra/SpectralTheory/Calculus/MixedProduct.lean` (relocated there from the `J`-bearing
`ModularSqrtSelfAdjoint.lean`). This file therefore imports **no** modular/`J` file, so circularity
for the Field-3 build is structurally impossible (landmine #5): the whole `s ↦ s²` pushforward layer
is a statement purely about a PVM/`Δ`, never about `J`/`modularConjugation`/`S̃`.
-/

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal

namespace Spectra.QuantumMechanics.SpectralTheory

open Spectra Spectra.Borel Spectra.OneParameterUnitaryGroup SpectralMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-! ## Elementary facts about the symbol `s ↦ (s:ℂ)² − z` (`Im z ≠ 0`) -/

/-- `((s:ℂ)² − z).im = −z.im`: the real point `s²` contributes no imaginary part. -/
lemma sq_ofReal_sub_im (z : ℂ) (s : ℝ) : ((s : ℂ) ^ 2 - z).im = -z.im := by
  have h : (s : ℂ) ^ 2 = ((s ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.sub_im, Complex.ofReal_im, zero_sub]

/-- `(s:ℂ)² − z ≠ 0` when `z.im ≠ 0` (a real square cannot cancel a non-real number). -/
lemma sq_ofReal_sub_ne_zero {z : ℂ} (hz : z.im ≠ 0) (s : ℝ) : (s : ℂ) ^ 2 - z ≠ 0 := by
  intro h
  apply hz
  have him := sq_ofReal_sub_im z s
  rw [h, Complex.zero_im] at him
  linarith [him]

/-- The resolvent symbol is bounded: `‖1/((s:ℂ)² − z)‖ ≤ |z.im|⁻¹`. -/
lemma norm_inv_sq_sub_le {z : ℂ} (hz : z.im ≠ 0) (s : ℝ) :
    ‖((s : ℂ) ^ 2 - z)⁻¹‖ ≤ |z.im|⁻¹ := by
  rw [norm_inv]
  have hpos : 0 < |z.im| := abs_pos.mpr hz
  have hge : |z.im| ≤ ‖(s : ℂ) ^ 2 - z‖ := by
    have h1 : |((s : ℂ) ^ 2 - z).im| ≤ ‖(s : ℂ) ^ 2 - z‖ := Complex.abs_im_le_norm _
    rwa [sq_ofReal_sub_im, abs_neg] at h1
  simp only [← one_div]
  exact one_div_le_one_div_of_le hpos hge

/-- The pointwise partial-fraction identity `s²·1/(s²−z) = 1 + z·1/(s²−z)`. -/
lemma sq_mul_inv_eq {z : ℂ} (hz : z.im ≠ 0) (s : ℝ) :
    (s : ℂ) ^ 2 * ((s : ℂ) ^ 2 - z)⁻¹ = 1 + z * ((s : ℂ) ^ 2 - z)⁻¹ := by
  have hne := sq_ofReal_sub_ne_zero hz s
  field_simp
  ring

/-! ## The witnesses (spike is non-vacuous) -/

/-- Measurability of `s ↦ (s:ℂ)²`. -/
lemma measurable_sq_ofReal : Measurable (fun s : ℝ => (s : ℂ) ^ 2) := by fun_prop

/-- Measurability of `s ↦ 1/((s:ℂ)² − z)`. -/
lemma measurable_inv_sq_sub (z : ℂ) : Measurable (fun s : ℝ => ((s : ℂ) ^ 2 - z)⁻¹) := by fun_prop

/-- Boundedness of the resolvent symbol. -/
lemma bdd_inv_sq_sub {z : ℂ} (hz : z.im ≠ 0) : ∃ C, ∀ s : ℝ, ‖((s : ℂ) ^ 2 - z)⁻¹‖ ≤ C :=
  ⟨|z.im|⁻¹, norm_inv_sq_sub_le hz⟩

/-- Boundedness of the product symbol `s²·1/(s²−z)` (it equals `1 + z·1/(s²−z)`). -/
lemma bdd_sq_mul_inv {z : ℂ} (hz : z.im ≠ 0) :
    ∃ C, ∀ s : ℝ, ‖(s : ℂ) ^ 2 * ((s : ℂ) ^ 2 - z)⁻¹‖ ≤ C := by
  refine ⟨1 + ‖z‖ * |z.im|⁻¹, fun s => ?_⟩
  rw [sq_mul_inv_eq hz s]
  calc ‖(1 : ℂ) + z * ((s : ℂ) ^ 2 - z)⁻¹‖
      ≤ ‖(1 : ℂ)‖ + ‖z * ((s : ℂ) ^ 2 - z)⁻¹‖ := norm_add_le _ _
    _ = 1 + ‖z‖ * ‖((s : ℂ) ^ 2 - z)⁻¹‖ := by rw [norm_mul, NormOneClass.norm_one]
    _ ≤ 1 + ‖z‖ * |z.im|⁻¹ := by gcongr; exact norm_inv_sq_sub_le hz s

/-- Boundedness of `s ↦ z·1/(s²−z)`. -/
lemma bdd_const_mul_inv_sq_sub {z : ℂ} (hz : z.im ≠ 0) :
    ∃ C, ∀ s : ℝ, ‖z * ((s : ℂ) ^ 2 - z)⁻¹‖ ≤ C := by
  refine ⟨‖z‖ * |z.im|⁻¹, fun s => ?_⟩
  rw [norm_mul]; gcongr; exact norm_inv_sq_sub_le hz s

/-- Boundedness of `s ↦ 1 + z·1/(s²−z)`. -/
lemma bdd_one_add_const_mul_inv_sq_sub {z : ℂ} (hz : z.im ≠ 0) :
    ∃ C, ∀ s : ℝ, ‖(1 : ℂ) + z * ((s : ℂ) ^ 2 - z)⁻¹‖ ≤ C := by
  refine ⟨1 + ‖z‖ * |z.im|⁻¹, fun s => ?_⟩
  calc ‖(1 : ℂ) + z * ((s : ℂ) ^ 2 - z)⁻¹‖
      ≤ ‖(1 : ℂ)‖ + ‖z * ((s : ℂ) ^ 2 - z)⁻¹‖ := norm_add_le _ _
    _ = 1 + ‖z‖ * ‖((s : ℂ) ^ 2 - z)⁻¹‖ := by rw [norm_mul, NormOneClass.norm_one]
    _ ≤ 1 + ‖z‖ * |z.im|⁻¹ := by gcongr; exact norm_inv_sq_sub_le hz s

/-- **The domain membership** `Φ(1/(s²−z)) ξ ∈ D(A²)`, `A² := pmapOfPVM U_grp (s²)`. From
`mem_pmapDomain_spectralCalculus` (the product `s²·1/(s²−z)` is bounded). -/
theorem resolvent_sq_mem {z : ℂ} (hz : z.im ≠ 0) (ξ : H) :
    spectralCalculus U_grp (fun s => ((s : ℂ) ^ 2 - z)⁻¹) (measurable_inv_sq_sub z)
        (bdd_inv_sq_sub hz) ξ
      ∈ (pmapOfPVM U_grp (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal).domain :=
  mem_pmapDomain_spectralCalculus U_grp (fun s => (s : ℂ) ^ 2)
    (fun s => ((s : ℂ) ^ 2 - z)⁻¹) measurable_sq_ofReal (measurable_inv_sq_sub z)
    (bdd_inv_sq_sub hz) (bdd_sq_mul_inv hz) ξ

/-! ## The resolvent identity (DAG node 1.2 — the make-or-break) -/

/-- **The `s ↦ s²` resolvent identity.**  For `A² := pmapOfPVM U_grp (fun s => (s:ℂ)²)` and any
`z` with `Im z ≠ 0`, the bounded-calculus vector `Φ(1/(s²−z)) ξ` lies in `D(A²)` and

`A² (Φ(1/(s²−z)) ξ) = ξ + z • Φ(1/(s²−z)) ξ`,

i.e. `(A² − z) Φ(1/(s²−z)) = 1` — so `Φ(1/(s²−z))` is the resolvent `(A² − z)⁻¹`.  Proof: the mixed
bounded/unbounded product law collapses `A²(Φ(g) ξ)` to `Φ(s²·g) ξ`, and pointwise
`s²·g = 1 + z·g` (partial fractions), so `Φ(s²·g) = Φ(1) + z • Φ(g) = 1 + z • Φ(g)`. -/
theorem resolvent_sq_identity {z : ℂ} (hz : z.im ≠ 0) (ξ : H) :
    pmapOfPVM U_grp (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal
        ⟨spectralCalculus U_grp (fun s => ((s : ℂ) ^ 2 - z)⁻¹) (measurable_inv_sq_sub z)
            (bdd_inv_sq_sub hz) ξ, resolvent_sq_mem U_grp hz ξ⟩
      = ξ + z • spectralCalculus U_grp (fun s => ((s : ℂ) ^ 2 - z)⁻¹) (measurable_inv_sq_sub z)
          (bdd_inv_sq_sub hz) ξ := by
  -- Collapse `A²(Φ(g)ξ)` to `Φ(s²·g)ξ` via the mixed product law.
  rw [pmapOfPVM_spectralCalculus_of_mul_bounded U_grp (fun s => (s : ℂ) ^ 2)
      (fun s => ((s : ℂ) ^ 2 - z)⁻¹) measurable_sq_ofReal (measurable_inv_sq_sub z)
      (bdd_inv_sq_sub hz) (measurable_sq_ofReal.mul (measurable_inv_sq_sub z)) (bdd_sq_mul_inv hz)
      ξ (resolvent_sq_mem U_grp hz ξ)]
  -- Rewrite the symbol `s²·g` as `1 + z·g` (partial fractions), then split additively.
  have hpt : (fun s : ℝ => (s : ℂ) ^ 2 * ((s : ℂ) ^ 2 - z)⁻¹)
      = (fun s : ℝ => (1 : ℂ) + z * ((s : ℂ) ^ 2 - z)⁻¹) := funext (sq_mul_inv_eq hz)
  rw [spectralCalculus_congr U_grp hpt (measurable_sq_ofReal.mul (measurable_inv_sq_sub z))
      (bdd_sq_mul_inv hz) (measurable_const.add ((measurable_inv_sq_sub z).const_mul z))
      (bdd_one_add_const_mul_inv_sq_sub hz),
    spectralCalculus_add U_grp (fun _ => (1 : ℂ)) (fun s => z * ((s : ℂ) ^ 2 - z)⁻¹)
      measurable_const ⟨1, fun _ => le_of_eq NormOneClass.norm_one⟩
      ((measurable_inv_sq_sub z).const_mul z) (bdd_const_mul_inv_sq_sub hz)
      (measurable_const.add ((measurable_inv_sq_sub z).const_mul z))
      (bdd_one_add_const_mul_inv_sq_sub hz),
    spectralCalculus_one,
    spectralCalculus_smul U_grp z (fun s => ((s : ℂ) ^ 2 - z)⁻¹) (measurable_inv_sq_sub z)
      (bdd_inv_sq_sub hz) ((measurable_inv_sq_sub z).const_mul z) (bdd_const_mul_inv_sq_sub hz)]
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]

/-! ## The pairing (the node 1.2 diagonal identity — free) -/

/-- **The resolvent diagonal identity** `⟪ξ, Φ(1/(s²−z)) ξ⟫ = ∫ (s²−z)⁻¹ dμ^E_ξ`.  With
`resolvent_sq_identity` (`Φ(1/(s²−z)) = (A²−z)⁻¹`) this is exactly the DAG-node-1.2 statement
`⟪ξ, (A²−z)⁻¹ ξ⟫ = ∫ (s²−z)⁻¹ dμ^E_ξ` that feeds `spectralPVM_unique`.  Free from
`inner_spectralCalculus` + `spectralForm_self`. -/
theorem inner_resolvent_sq {z : ℂ} (hz : z.im ≠ 0) (ξ : H) :
    ⟪ξ, spectralCalculus U_grp (fun s => ((s : ℂ) ^ 2 - z)⁻¹) (measurable_inv_sq_sub z)
        (bdd_inv_sq_sub hz) ξ⟫_ℂ
      = ∫ s, ((s : ℂ) ^ 2 - z)⁻¹ ∂(borelMeasure U_grp ξ) := by
  rw [inner_spectralCalculus U_grp _ (measurable_inv_sq_sub z) (bdd_inv_sq_sub hz) ξ ξ,
    spectralForm_self U_grp ξ (measurable_inv_sq_sub z) (bdd_inv_sq_sub hz)]

end Spectra.QuantumMechanics.SpectralTheory
