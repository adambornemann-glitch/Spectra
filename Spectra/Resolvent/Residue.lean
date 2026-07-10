/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Meromorphic
import Spectra.Resolvent.SpectralRepresentation
import Spectra.SpectralTheory.ResolventForm
import Spectra.SpectralTheory.Measure.Convergence
import Spectra.SpectralTheory.Measure.PVM

/-!
# The residue of the resolvent at a spectral point (Tier A)

For a self-adjoint operator `A`, the resolvent `R(z) = (A − z)⁻¹` has the strong limit

  `s-lim_{ε→0⁺} (i ε) · R(λ + iε) = − E({λ})`,

i.e. at an *isolated* eigenvalue `λ` the resolvent has a simple pole with residue `−E({λ})`, the
spectral projection.  This is the analytic companion to the projection theorems
`hydrogen_spectral_projection_discrete` / `hydrogen_eigenfunction_complete`, and the residue
half of the (future) operator-valued meromorphy of the resolvent.

## Proof

Via the spectral representation `R(z) = Φ((·−z)⁻¹)` (`resolvent_eq_spectralCalculus`),
`(iε)·R(λ+iε) = Φ(g_ε)` with symbol `g_ε(s) = iε·(s − λ − iε)⁻¹`.  Uniformly `‖g_ε‖ ≤ 1`, and
pointwise `g_ε(s) → −1_{s=λ}` as `ε → 0⁺`, so the dominated-convergence theorem for the spectral
calculus (`tendsto_spectralCalculus_apply`) gives `Φ(g_ε)ξ → Φ(−1_{λ})ξ = −E({λ})ξ`.

## Implementation notes

The headline theorem is stated through `Spectra.Resolvent.resolventOf`
(`Resolvent/Meromorphic.lean`), the *totalized* resolvent (junk `0` off the resolvent set), rather
than the partial `selfAdjointResolvent` (which takes an explicit `hz : z.im ≠ 0` proof). This
avoids a `dite` on `0 < ε` inside the theorem's own statement: `resolventOf A (lam + iε)` is
already the right operator for every real `ε`, positive or not, by
`mem_resolventSet_of_im_ne_zero` supplying membership in the resolvent set whenever `ε ≠ 0`.
`selfAdjointResolvent_eq_resolventOf` is the one-line bridge lemma identifying the two on
`Im z ≠ 0`. This theorem is deliberately weaker than the isolated-point result
`tendsto_sub_smul_resolventOf` (`SpectralTheory/SimplePole.lean`): that one needs a spectral-gap
hypothesis around `lam` and gets the stronger complex-variable limit `z → lam` through
`𝓝[≠] (lam : ℂ)` in operator norm; this one holds *unconditionally* for any real `lam` (isolated
or not), at the cost of only a real-variable vertical-line limit `ε → 0⁺` in the strong (weak-on-ξ)
topology. The two are complementary, not duplicates.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Theorem VIII.1
* [Kato, *Perturbation Theory for Linear Operators*][kato1995], Section V.3

## Tags

resolvent, residue, spectral projection, simple pole
-/

open InnerProductSpace Complex MeasureTheory Filter Topology
open scoped InnerProductSpace Topology
open Spectra.OneParameterUnitaryGroup Spectra.Resolvent Spectra.Borel Spectra.YosidaHille

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.QuantumMechanics.SpectralTheory

/-- The resolvent residue symbol `g_ε(s) = (iε)·(s − λ − iε)⁻¹`. -/
@[reducible] private noncomputable def residueSymbol (lam : ℝ) (ε : ℝ) (s : ℝ) : ℂ :=
  (Complex.I * (ε : ℂ)) * ((s : ℂ) - (lam + Complex.I * (ε : ℂ)))⁻¹

private lemma residueSymbol_measurable (lam ε : ℝ) : Measurable (residueSymbol lam ε) :=
  measurable_const.mul ((Complex.measurable_ofReal.sub measurable_const).inv)

private lemma residueSymbol_norm_le_one (lam ε s : ℝ) : ‖residueSymbol lam ε s‖ ≤ 1 := by
  unfold residueSymbol
  rw [norm_mul, norm_inv]
  have hIe : ‖Complex.I * (ε : ℂ)‖ = |ε| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hIe]
  set w := (s : ℂ) - (lam + Complex.I * (ε : ℂ)) with hw
  have hwim : w.im = -ε := by
    rw [hw]
    simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_im, Complex.ofReal_re]
  have hge : |ε| ≤ ‖w‖ := by
    have h := Complex.abs_im_le_norm w
    rwa [hwim, abs_neg] at h
  exact mul_inv_le_one_of_le₀ hge (norm_nonneg w)

private lemma residueSymbol_bdd (lam ε : ℝ) : ∃ C, ∀ s, ‖residueSymbol lam ε s‖ ≤ C :=
  ⟨1, fun s => residueSymbol_norm_le_one lam ε s⟩

/-- The pointwise limit `g_ε(s) → −1_{s=λ}` as `ε → 0⁺`. -/
private lemma residueSymbol_tendsto (lam s : ℝ) :
    Tendsto (fun ε => residueSymbol lam ε s) (𝓝[>] (0 : ℝ))
      (𝓝 ((-1 : ℂ) * Set.indicator ({lam} : Set ℝ) (fun _ => (1 : ℂ)) s)) := by
  unfold residueSymbol
  by_cases hs : s = lam
  · subst hs
    have hval : (-1 : ℂ) * Set.indicator ({s} : Set ℝ) (fun _ => (1 : ℂ)) s = -1 := by simp
    rw [hval]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [Set.mem_Ioi] at hε
    have hεne : Complex.I * (ε : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hε))
    have hsimp : ((s : ℂ) - ((s : ℝ) + Complex.I * (ε : ℂ))) = -(Complex.I * (ε : ℂ)) := by
      ring
    rw [hsimp, inv_neg, mul_neg, mul_inv_cancel₀ hεne]
  · have hval : (-1 : ℂ) * Set.indicator ({lam} : Set ℝ) (fun _ => (1 : ℂ)) s = 0 := by
      simp [hs]
    rw [hval]
    have hne : ((s : ℂ) - (lam + Complex.I * ((0 : ℝ) : ℂ))) ≠ 0 := by
      simp only [Complex.ofReal_zero, mul_zero, add_zero]
      rw [sub_ne_zero]
      exact fun h => hs (by exact_mod_cast h)
    have hcont : ContinuousAt
        (fun ε : ℝ => (Complex.I * (ε : ℂ)) * ((s : ℂ) - (lam + Complex.I * (ε : ℂ)))⁻¹) 0 :=
      ContinuousAt.mul (by fun_prop) (ContinuousAt.inv₀ (by fun_prop) hne)
    have h0 :
        (Complex.I * ((0 : ℝ) : ℂ)) * ((s : ℂ) - (lam + Complex.I * ((0 : ℝ) : ℂ)))⁻¹ = 0 := by
      simp
    have hlim := hcont.tendsto
    rw [h0] at hlim
    exact hlim.mono_left nhdsWithin_le_nhds

/-- **The totalized resolvent agrees with `selfAdjointResolvent`** off the real axis: both are the
two-sided inverse of `A − z`, and two-sided inverses are unique (`IsResolvent.unique`). -/
lemma selfAdjointResolvent_eq_resolventOf {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (z : ℂ) (hz : z.im ≠ 0) :
    selfAdjointResolvent hA z hz = Spectra.Resolvent.resolventOf A z := by
  unfold selfAdjointResolvent
  exact (Spectra.Resolvent.resolventOf_eq_resolvent (isFormalAdjoint_of_isSelfAdjoint hA)
    (isSelfAdjoint_to_surjective hA).1 (isSelfAdjoint_to_surjective hA).2 hz).symm

/-- **Tier A — the resolvent residue is the spectral projection.**  For a self-adjoint operator
`A`, real `λ`, and `ξ`, the strong limit `(iε)·R(λ+iε) ξ → −E({λ}) ξ` as `ε → 0⁺`, with the
resolvent taken as `resolventOf A` (total in `z`, so no `dite`/partial-function bookkeeping
appears in the statement). This holds for every real `λ`, isolated eigenvalue or not; see the
module's `## Implementation notes` for the (stronger, but gap-hypothesis-dependent) complex-limit
form `tendsto_sub_smul_resolventOf`. -/
theorem selfAdjointResolvent_residue_proj_singleton {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (lam : ℝ) (ξ : H) :
    Tendsto (fun ε : ℝ =>
        (Complex.I * (ε : ℂ)) • Spectra.Resolvent.resolventOf A (lam + Complex.I * (ε : ℂ)) ξ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (-(((PVM.spectralPVM hA).proj {lam} (measurableSet_singleton lam)) ξ))) := by
  have hg_meas : Measurable
      (fun s => (-1 : ℂ) * Set.indicator ({lam} : Set ℝ) (fun _ => (1 : ℂ)) s) :=
    measurable_const.mul (measurable_const.indicator (measurableSet_singleton lam))
  have hg_bdd : ∃ C, ∀ s, ‖(-1 : ℂ) * Set.indicator ({lam} : Set ℝ) (fun _ => (1 : ℂ)) s‖ ≤ C := by
    refine ⟨1, fun s => ?_⟩
    rcases eq_or_ne s lam with h | h
    · subst h; simp
    · simp [Set.mem_singleton_iff, h]
  -- the dominated-convergence limit at the calculus level
  have hcalc := tendsto_spectralCalculus_apply (genToGroup hA)
    (G := fun ε => residueSymbol lam ε)
    (g := fun s => (-1 : ℂ) * Set.indicator ({lam} : Set ℝ) (fun _ => (1 : ℂ)) s)
    (fun ε => residueSymbol_measurable lam ε) (fun ε => residueSymbol_bdd lam ε)
    hg_meas hg_bdd (C := 1) (fun ε s => residueSymbol_norm_le_one lam ε s)
    (residueSymbol_tendsto lam) ξ
  -- identify the limit value `Φ(g) ξ = −E({λ}) ξ`
  have hΦg : spectralCalculus (genToGroup hA)
      (fun s => (-1 : ℂ) * Set.indicator ({lam} : Set ℝ) (fun _ => (1 : ℂ)) s) hg_meas hg_bdd ξ
      = -(((PVM.spectralPVM hA).proj {lam} (measurableSet_singleton lam)) ξ) := by
    rw [spectralCalculus_smul (genToGroup hA) (-1 : ℂ)
        (Set.indicator ({lam} : Set ℝ) (fun _ => (1 : ℂ)))
        (measurable_const.indicator (measurableSet_singleton lam)) (indicator_one_bdd _)
        hg_meas hg_bdd,
      ContinuousLinearMap.smul_apply, neg_one_smul]
    rfl
  rw [hΦg] at hcalc
  -- bridge: on `ε > 0`, `(iε) • resolventOf A (lam+iε) ξ` equals `Φ(g_ε) ξ`
  refine hcalc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [Set.mem_Ioi] at hε
  have hz : (lam + Complex.I * (ε : ℂ)).im ≠ 0 := by
    have him : (lam + Complex.I * (ε : ℂ)).im = ε := by
      simp [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_im,
        Complex.ofReal_re]
    rw [him]; exact ne_of_gt hε
  have e := spectralCalculus_smul (genToGroup hA) (Complex.I * (ε : ℂ))
    (fun s => ((s : ℂ) - (lam + Complex.I * (ε : ℂ)))⁻¹)
    (kernel_measurable (lam + Complex.I * (ε : ℂ)) hz)
    (kernel_bdd (lam + Complex.I * (ε : ℂ)) hz)
    (residueSymbol_measurable lam ε) (residueSymbol_bdd lam ε)
  have hop : (Complex.I * (ε : ℂ)) • selfAdjointResolvent hA (lam + Complex.I * (ε : ℂ)) hz
      = spectralCalculus (genToGroup hA) (residueSymbol lam ε) (residueSymbol_measurable lam ε)
          (residueSymbol_bdd lam ε) := by
    rw [selfAdjointResolvent_eq_genToGroup hA, resolvent_eq_spectralCalculus, ← e]
  rw [← selfAdjointResolvent_eq_resolventOf hA (lam + Complex.I * (ε : ℂ)) hz]
  exact (ContinuousLinearMap.ext_iff.mp hop ξ).symm

end Spectra.QuantumMechanics.SpectralTheory
