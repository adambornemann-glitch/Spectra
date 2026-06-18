/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: UnitaryEvolution/Resolvent/IntegralZ.lean
-/
import Spectra.Resolvent.Identities
import Spectra.YosidaHille.Basic

open Complex MeasureTheory
open Spectra.OneParameterUnitaryGroup
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Resolvent
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- Resolvent integral at general `z` in the lower half-plane:
    `R(z)φ = (-i) ∫₀^∞ e^{-izt} U(t)φ dt`.  At `z = -i` this is `resolventIntegralPlus`. -/
noncomputable def resolventIntegralZ (z : ℂ) (φ : H) : H :=
  (-I) • ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ

/-- Integrability needs `Im z < 0`; bound `‖e^{-izt} • U(t)φ‖ = e^{(Im z)t} ‖φ‖ ≤ ‖φ‖`. -/
lemma integrable_expZ_unitary {z : ℂ} (hz : z.im < 0) (φ : H) :
    IntegrableOn (fun t : ℝ => cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) (Set.Ici 0) := by
  -- ── two facts from the `OneParameterUnitaryGroup` API (supply the names) ──────
  have h_orbit_cont : Continuous (fun t : ℝ => U_grp.U t φ) := U_grp.strong_continuous φ
  have h_normU : ∀ t : ℝ, ‖U_grp.U t φ‖ ≤ ‖φ‖ := fun t => (norm_preserving U_grp t φ).le
  -- ── dominating function  ‖φ‖ · e^{(Im z)·t},  integrable since  Im z < 0 ──────
  have h_exp_int : IntegrableOn (fun t : ℝ => Real.exp (z.im * t)) (Set.Ici 0) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_exp_mul_Ioi hz 0)
  have h_g_int : IntegrableOn (fun t : ℝ => ‖φ‖ * Real.exp (z.im * t)) (Set.Ici 0) volume :=
    h_exp_int.const_mul ‖φ‖
  -- ── measurability of the integrand ──────────────────────────────────────────
  have h_scalar_cont : Continuous (fun t : ℝ => cexp (-(I * z * (t : ℂ)))) := by
    apply Complex.continuous_exp.comp
    exact (Complex.continuous_ofReal.const_mul (I * z)).neg
  have h_meas : AEStronglyMeasurable
      (fun t : ℝ => cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) (volume.restrict (Set.Ici 0)) := by
    apply AEStronglyMeasurable.smul
    · exact h_scalar_cont.aestronglyMeasurable.restrict
    · exact h_orbit_cont.aestronglyMeasurable.restrict
  -- ── pointwise domination:  ‖integrand t‖ = e^{(Im z)·t} · ‖U(t)φ‖ ≤ g t ──────
  have h_bound : ∀ᵐ (t : ℝ) ∂(volume.restrict (Set.Ici (0 : ℝ))),
      ‖cexp (-(I * z * (t : ℂ))) • U_grp.U t φ‖ ≤ ‖φ‖ * Real.exp (z.im * t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t _ht
    rw [norm_smul, Complex.norm_exp]
    have h_re : (-(I * z * (t : ℂ))).re = z.im * t := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
                 Complex.ofReal_re, Complex.ofReal_im]; ring
    rw [h_re]
    calc Real.exp (z.im * t) * ‖U_grp.U t φ‖
        ≤ Real.exp (z.im * t) * ‖φ‖ :=
          mul_le_mul_of_nonneg_left (h_normU t) (Real.exp_pos _).le
      _ = ‖φ‖ * Real.exp (z.im * t) := mul_comm _ _
  exact Integrable.mono' h_g_int h_meas h_bound

/-- The shift lemma, generalizing `unitary_apply_Ici_orbit_integral_plus`:
    the prefactor `e^h` becomes `e^{izh}`. -/
lemma unitary_apply_expZ_integral {z : ℂ} (hz : z.im < 0) (φ : H) (h : ℝ) :
    U_grp.U h (∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) =
      cexp (I * z * (h : ℂ)) • ∫ s in Set.Ici h, cexp (-(I * z * (s : ℂ))) • U_grp.U s φ := by
  have h_int := integrable_expZ_unitary U_grp hz φ
  -- (1) push U(h) through the Bochner integral
  have h_comm : U_grp.U h (∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) =
                ∫ t in Set.Ici (0 : ℝ), U_grp.U h (cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) :=
    ((U_grp.U h).integral_comp_comm h_int).symm
  -- (2) group law:  U(h)(e^{-izt} • U(t)φ) = e^{-izt} • U(t+h)φ
  have h_shift : ∀ t : ℝ, U_grp.U h (cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) =
                      cexp (-(I * z * (t : ℂ))) • U_grp.U (t + h) φ := by
    intro t
    have hlaw := U_grp.group_law h t
    rw [add_comm] at hlaw
    rw [hlaw, ContinuousLinearMap.comp_apply]
    exact map_smul (U_grp.U h) _ _
  -- (3) split the prefactor:  e^{-izt} = e^{izh} · e^{-iz(t+h)}
  have h_exp : ∀ t : ℝ, cexp (-(I * z * (t : ℂ))) • U_grp.U (t + h) φ =
                    cexp (I * z * (h : ℂ)) •
                      (cexp (-(I * z * ((t + h : ℝ) : ℂ))) • U_grp.U (t + h) φ) := by
    intro t
    rw [← smul_assoc]
    congr 1
    rw [smul_eq_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h_comm]
  simp_rw [h_shift]
  simp_rw [h_exp]
  rw [integral_smul]
  -- (4) translation  s = t + h :  ∫_{[0,∞)} f(t+h) dt = ∫_{[h,∞)} f(s) ds
  have h_subst :
      ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * ((t + h : ℝ) : ℂ))) • U_grp.U (t + h) φ =
      ∫ s in Set.Ici h, cexp (-(I * z * (s : ℂ))) • U_grp.U s φ := by
    have hmp : MeasurePreserving (· + h) (volume : Measure ℝ) volume :=
      measurePreserving_add_right volume h
    have hme : MeasurableEmbedding (· + h : ℝ → ℝ) :=
      (Homeomorph.addRight h).isClosedEmbedding.measurableEmbedding
    have hpre : (· + h) ⁻¹' (Set.Ici h) = Set.Ici (0 : ℝ) := by
      ext t; simp only [Set.mem_preimage, Set.mem_Ici]
      constructor <;> intro ht <;> linarith
    have key := hmp.setIntegral_preimage_emb hme
      (fun s => cexp (-(I * z * (s : ℂ))) • U_grp.U s φ) (Set.Ici h)
    rw [hpre] at key
    exact key
  rw [h_subst]

end Spectra.Resolvent
