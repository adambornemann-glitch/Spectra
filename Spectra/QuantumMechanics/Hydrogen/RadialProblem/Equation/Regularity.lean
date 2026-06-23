/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Weak-derivative regularity, step 1: du Bois-Reymond

The first analytic brick of the radial elliptic-regularity step (Step 4) of the forward
direction of `hydrogen_discrete_spectrum`.

* `exists_contDiff_hasCompactSupport_deriv_eq` — a smooth compactly supported function with
  zero integral is the derivative of a smooth compactly supported function (the primitive).
* `ae_eq_const_of_integral_deriv_mul_eq_zero` — **du Bois-Reymond's lemma**: a locally
  integrable `f` whose distributional derivative vanishes (tested against all smooth compactly
  supported `g` via `∫ g' · f = 0`) is almost everywhere constant.

These are general one-dimensional facts; the radial bootstrap (weak ODE ⟹ classical `C²`)
is assembled on top of them.
-/

open MeasureTheory Set
open scoped ContDiff

namespace Spectra.RadialRegularity

/-- A smooth compactly supported function with zero total integral has a smooth compactly
supported primitive. -/
lemma exists_contDiff_hasCompactSupport_deriv_eq {k : ℝ → ℝ}
    (hk : ContDiff ℝ ∞ k) (hk0 : HasCompactSupport k) (hint : ∫ x, k x = 0) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ deriv g = k := by
  have hkc : Continuous k := hk.continuous
  have hki : Integrable k volume := hkc.integrable_of_hasCompactSupport hk0
  -- bound the support inside `Icc (-R) R`
  obtain ⟨R, hR0, hRsub⟩ : ∃ R : ℝ, 0 ≤ R ∧ Function.support k ⊆ Icc (-R) R := by
    obtain ⟨R, hRsub⟩ := hk0.isBounded.subset_closedBall (0 : ℝ)
    refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
    have hx' := hRsub (subset_tsupport k hx)
    rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hx'
    exact ⟨le_trans (neg_le_neg (le_max_left _ _)) hx'.1, le_trans hx'.2 (le_max_left _ _)⟩
  set a₀ : ℝ := -R - 1 with ha₀
  set g : ℝ → ℝ := fun x => ∫ t in a₀..x, k t with hg_def
  have hHDA : ∀ x, HasDerivAt g (k x) x := fun x =>
    (intervalIntegral.integral_hasStrictDerivAt_right (hkc.intervalIntegrable _ _)
      (hkc.stronglyMeasurableAtFilter _ _) hkc.continuousAt).hasDerivAt
  have hg_deriv : deriv g = k := funext fun x => (hHDA x).deriv
  refine ⟨g, ?_, ?_, hg_deriv⟩
  · rw [contDiff_infty_iff_deriv]
    exact ⟨fun x => (hHDA x).differentiableAt, by rw [hg_deriv]; exact hk⟩
  · apply HasCompactSupport.intro (isCompact_Icc (a := a₀) (b := R))
    intro x hx
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    show (∫ t in a₀..x, k t) = 0
    rcases hx with hlt | hgt
    · -- x < a₀ : integrate over a region left of the support
      rw [intervalIntegral.integral_of_ge hlt.le, neg_eq_zero]
      refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
      refine Function.notMem_support.mp fun hts => ?_
      have hmem := hRsub hts
      rw [mem_Icc] at hmem
      have ha : a₀ < t := lt_of_lt_of_le (by rw [ha₀]; linarith) hmem.1
      exact absurd (mem_Ioc.mp ht).2 (not_le.mpr ha)
    · -- x > R : the full integral, which vanishes
      rw [intervalIntegral.integral_of_le (by rw [ha₀]; linarith : a₀ ≤ x),
        setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_, hint]
      refine Function.notMem_support.mp fun hts => ht ?_
      have hmem := hRsub hts
      rw [mem_Icc] at hmem
      exact mem_Ioc.mpr ⟨by rw [ha₀]; linarith [hmem.1], by linarith [hmem.2]⟩

/-- **du Bois-Reymond's lemma (1-D).** A locally integrable function whose distributional
derivative vanishes — i.e. `∫ (deriv g) · f = 0` for every smooth compactly supported `g` —
is almost everywhere equal to a constant. -/
theorem ae_eq_const_of_integral_deriv_mul_eq_zero (f : ℝ → ℝ)
    (hf : LocallyIntegrable f volume)
    (h : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, deriv g x * f x = 0) :
    ∃ c : ℝ, ∀ᵐ x, f x = c := by
  -- a fixed smooth bump with unit integral
  set e : ℝ → ℝ := (default : ContDiffBump (0 : ℝ)).normed volume with he_def
  have he_diff : ContDiff ℝ ∞ e := (default : ContDiffBump (0 : ℝ)).contDiff_normed
  have he_supp : HasCompactSupport e := (default : ContDiffBump (0 : ℝ)).hasCompactSupport_normed
  have he_int : ∫ x, e x = 1 := (default : ContDiffBump (0 : ℝ)).integral_normed
  -- products of a continuous compactly supported function with `f` are integrable
  have hmul : ∀ φ : ℝ → ℝ, Continuous φ → HasCompactSupport φ →
      Integrable (fun x => φ x * f x) volume := fun φ hφc hφ0 => by
    simpa only [smul_eq_mul] using hf.integrable_smul_left_of_hasCompactSupport hφc hφ0
  set c : ℝ := ∫ x, e x * f x with hc_def
  refine ⟨c, ?_⟩
  have key : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ x, ψ x • f x = ∫ x, ψ x • (fun _ => c) x := by
    intro ψ hψ hψ0
    have hψc : Continuous ψ := hψ.continuous
    set Iψ : ℝ := ∫ x, ψ x with hIψ
    set k : ℝ → ℝ := fun x => ψ x - Iψ * e x with hk_def
    have hk_diff : ContDiff ℝ ∞ k := hψ.sub (contDiff_const.mul he_diff)
    have hk_supp : HasCompactSupport k := hψ0.sub (he_supp.mul_left)
    have hk_int : ∫ x, k x = 0 := by
      rw [hk_def, integral_sub (hψ.continuous.integrable_of_hasCompactSupport hψ0)
        ((he_diff.continuous.integrable_of_hasCompactSupport he_supp).const_mul Iψ),
        integral_const_mul, he_int, ← hIψ, mul_one, sub_self]
    obtain ⟨g, hg_diff, hg_supp, hg_deriv⟩ :=
      exists_contDiff_hasCompactSupport_deriv_eq hk_diff hk_supp hk_int
    have hzero := h g hg_diff hg_supp
    rw [hg_deriv] at hzero
    -- hzero : ∫ k x * f x = 0
    have hexpand : ∫ x, k x * f x = (∫ x, ψ x * f x) - Iψ * c := by
      have : (fun x => k x * f x) = fun x => ψ x * f x - Iψ * (e x * f x) := by
        funext x; rw [hk_def]; ring
      rw [this, integral_sub (hmul ψ hψc hψ0)
        ((hmul e he_diff.continuous he_supp).const_mul Iψ), integral_const_mul, ← hc_def]
    rw [hexpand, sub_eq_zero] at hzero
    -- hzero : ∫ ψ f = Iψ * c
    simp only [smul_eq_mul]
    rw [hzero, integral_mul_const, ← hIψ]
  exact ae_eq_of_integral_contDiff_smul_eq hf (locallyIntegrable_const c) key

/-- The full-line integral of the derivative of a `C¹` compactly supported function is zero. -/
private lemma integral_deriv_eq_zero_hcs {F : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (hF0 : HasCompactSupport F) : ∫ x, deriv F x = 0 := by
  have hint : Integrable (deriv F) volume :=
    (hF.continuous_deriv le_rfl).integrable_of_hasCompactSupport hF0.deriv
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ)) hint.integrableOn hint.integrableOn,
    HasCompactSupport.integral_Iic_deriv_eq hF hF0 0,
    HasCompactSupport.integral_Ioi_deriv_eq hF hF0 0, add_neg_cancel]

/-- **du Bois-Reymond's lemma, second order.** A locally integrable function whose
distributional *second* derivative vanishes — `∫ (deriv (deriv g)) · f = 0` for every smooth
compactly supported `g` — is almost everywhere an affine function `x ↦ a x + b`. Reduces to
the first-order version applied to `f - a · id`. -/
theorem ae_eq_affine_of_integral_deriv2_mul_eq_zero (f : ℝ → ℝ)
    (hf : LocallyIntegrable f volume)
    (hyp : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, deriv (deriv g) x * f x = 0) :
    ∃ a b : ℝ, ∀ᵐ x, f x = a * x + b := by
  set e : ℝ → ℝ := (default : ContDiffBump (0 : ℝ)).normed volume with he_def
  have he_diff : ContDiff ℝ ∞ e := (default : ContDiffBump (0 : ℝ)).contDiff_normed
  have he_supp : HasCompactSupport e := (default : ContDiffBump (0 : ℝ)).hasCompactSupport_normed
  have he_int : ∫ x, e x = 1 := (default : ContDiffBump (0 : ℝ)).integral_normed
  -- `deriv ψ * f` is integrable for test `ψ`
  have hmulf : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Integrable (fun x => deriv ψ x * f x) volume := fun ψ hψ hψ0 => by
    have hd : Continuous (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2.continuous
    simpa only [smul_eq_mul] using hf.integrable_smul_left_of_hasCompactSupport hd hψ0.deriv
  -- (key0) test functions with zero integral are derivatives of test functions
  have key0 : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∫ x, ψ x = 0 →
      ∫ x, deriv ψ x * f x = 0 := by
    intro ψ hψ hψ0 hψint
    obtain ⟨φ, hφ, hφ0, hφd⟩ := exists_contDiff_hasCompactSupport_deriv_eq hψ hψ0 hψint
    have hdd : deriv ψ = deriv (deriv φ) := by rw [hφd]
    rw [hdd]; exact hyp φ hφ hφ0
  -- the slope
  set a : ℝ := -(∫ x, deriv e x * f x) with ha_def
  -- (keyA) weak derivative pairing has the affine form
  have keyA : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ x, deriv ψ x * f x = -a * ∫ x, ψ x := by
    intro ψ hψ hψ0
    set Iψ : ℝ := ∫ x, ψ x with hIψ
    have hcomb0 : ∫ x, (ψ x - Iψ * e x) = 0 := by
      rw [integral_sub (hψ.continuous.integrable_of_hasCompactSupport hψ0)
        ((he_diff.continuous.integrable_of_hasCompactSupport he_supp).const_mul Iψ),
        integral_const_mul, he_int, ← hIψ, mul_one, sub_self]
    have hde : ∀ x, deriv (fun y => ψ y - Iψ * e y) x = deriv ψ x - Iψ * deriv e x := fun x =>
      (((hψ.differentiable (by norm_num)).differentiableAt.hasDerivAt).sub
        (((he_diff.differentiable (by norm_num)).differentiableAt.hasDerivAt).const_mul Iψ)).deriv
    have hd0 := key0 (fun x => ψ x - Iψ * e x) (hψ.sub (contDiff_const.mul he_diff))
      (hψ0.sub he_supp.mul_left) hcomb0
    have hexp : ∫ x, deriv (fun y => ψ y - Iψ * e y) x * f x
        = (∫ x, deriv ψ x * f x) - Iψ * ∫ x, deriv e x * f x := by
      rw [show (fun x => deriv (fun y => ψ y - Iψ * e y) x * f x)
          = (fun x => deriv ψ x * f x - Iψ * (deriv e x * f x)) from
          funext fun x => by rw [hde x]; ring,
        integral_sub (hmulf ψ hψ hψ0) ((hmulf e he_diff he_supp).const_mul Iψ),
        integral_const_mul]
    rw [hexp] at hd0
    rw [ha_def]
    linear_combination hd0
  -- (keyB) integration by parts against the identity
  have keyB : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, deriv g x * x = -∫ x, g x := by
    intro g hg hg0
    have hgid_diff : ContDiff ℝ 1 (fun y => g y * y) := (hg.mul contDiff_id).of_le (by norm_num)
    have hgid_supp : HasCompactSupport (fun y => g y * y) := hg0.mul_right
    have hz := integral_deriv_eq_zero_hcs hgid_diff hgid_supp
    have hde : ∀ x, deriv (fun y => g y * y) x = deriv g x * x + g x := fun x => by
      have h := (((hg.differentiable (by norm_num)).differentiableAt.hasDerivAt).mul
        (hasDerivAt_id x)).deriv
      simp only [id_eq, mul_one] at h
      exact h
    have hint1 : Integrable (fun x => deriv g x * x) volume :=
      ((contDiff_infty_iff_deriv.mp hg).2.continuous.mul continuous_id').integrable_of_hasCompactSupport
        (hg0.deriv.mul_right)
    rw [show (fun x => deriv (fun y => g y * y) x) = (fun x => deriv g x * x + g x) from
        funext hde, integral_add hint1 (hg.continuous.integrable_of_hasCompactSupport hg0)] at hz
    linarith [hz]
  -- assemble: `f - a · id` has vanishing weak derivative
  obtain ⟨b, hb⟩ := ae_eq_const_of_integral_deriv_mul_eq_zero (fun x => f x - a * x)
    (hf.sub ((continuous_const.mul continuous_id').locallyIntegrable)) (fun g hg hg0 => by
      have hdgx : Integrable (fun x => deriv g x * x) volume :=
        ((contDiff_infty_iff_deriv.mp hg).2.continuous.mul continuous_id').integrable_of_hasCompactSupport
          (hg0.deriv.mul_right)
      have e1 : ∫ x, deriv g x * (f x - a * x)
          = (∫ x, deriv g x * f x) - a * ∫ x, deriv g x * x := by
        rw [show (fun x => deriv g x * (f x - a * x))
            = (fun x => deriv g x * f x - a * (deriv g x * x)) from funext fun x => by ring,
          integral_sub (hmulf g hg hg0) (hdgx.const_mul a), integral_const_mul]
      rw [e1, keyA g hg hg0, keyB g hg hg0]; ring)
  exact ⟨a, b, by filter_upwards [hb] with x hx; linarith [hx]⟩

/-! ## Bootstrap workhorse — integration by parts against a primitive

The mechanical core of the weak-ODE bootstrap: a primitive `x ↦ ∫_{x₀}^x h` of an
integrable function integrates by parts against a smooth compactly supported test
function, with no boundary term. -/

/-- **Integration by parts against a primitive.** For locally integrable `h` and a smooth
compactly supported `ψ`, the primitive `x ↦ ∫_{x₀}^x h` satisfies `∫ (∫_{x₀}^· h) · ψ' = -∫ h · ψ`.
(Local integrability suffices — the test function confines everything to a compact interval —
which is what the radial application, where `h` is not globally `L¹`, requires.) -/
theorem integral_primitive_mul_deriv {h : ℝ → ℝ} (hh : LocallyIntegrable h volume) (x₀ : ℝ)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ0 : HasCompactSupport ψ) :
    ∫ x, (∫ t in x₀..x, h t) * deriv ψ x = -∫ x, h x * ψ x := by
  set F : ℝ → ℝ := fun x => ∫ t in x₀..x, h t with hF_def
  -- a finite interval `[-M, M]` containing the support of `ψ` (in its interior) and `x₀`
  obtain ⟨R, hRsub⟩ := hψ0.isBounded.subset_closedBall (0 : ℝ)
  set M : ℝ := max R |x₀| + 1 with hM
  have hMpos : (0 : ℝ) ≤ max R |x₀| := le_trans (abs_nonneg _) (le_max_right _ _)
  have hab : -M ≤ M := by rw [hM]; linarith
  have hψ_supp : tsupport ψ ⊆ Set.Ioo (-M) M := by
    intro x hx
    have hxR : |x| ≤ R := by simpa [Real.dist_eq, Metric.mem_closedBall] using hRsub hx
    have hxM : |x| ≤ M - 1 := le_trans hxR (by rw [hM]; simp)
    rw [Set.mem_Ioo]; rw [abs_le] at hxM; constructor <;> linarith [hxM.1, hxM.2]
  have hψ0' : ∀ x, x ∉ Set.Ioo (-M) M → ψ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hts => hx (hψ_supp hts))
  have hderivψ0 : ∀ x, x ∉ Set.Ioo (-M) M → deriv ψ x = 0 := fun x hx =>
    deriv_of_notMem_tsupport (fun hts => hx (hψ_supp hts))
  have hx₀mem : x₀ ∈ Set.uIcc (-M) M := by
    rw [Set.uIcc_of_le hab, Set.mem_Icc]
    have hx0M : |x₀| ≤ M - 1 := by rw [hM]; simp
    rw [abs_le] at hx0M; constructor <;> linarith [hx0M.1, hx0M.2]
  -- absolute continuity of the primitive and the test function
  have hii : IntervalIntegrable h volume (-M) M :=
    intervalIntegrable_iff.mpr ((hh.integrableOn_isCompact isCompact_uIcc).mono_set Set.uIoc_subset_uIcc)
  have hFac : AbsolutelyContinuousOnInterval F (-M) M :=
    hii.absolutelyContinuousOnInterval_intervalIntegral hx₀mem
  have hψac : AbsolutelyContinuousOnInterval ψ (-M) M :=
    (hψ.of_le (by norm_num)).contDiffOn.absolutelyContinuousOnInterval
  -- integration by parts (boundary term vanishes since `ψ (±M) = 0`)
  have hibp := hFac.integral_mul_deriv_eq_deriv_mul hψac
  simp only [hψ0' (-M) (fun hh => lt_irrefl _ hh.1), hψ0' M (fun hh => lt_irrefl _ hh.2),
    mul_zero, sub_zero, zero_sub] at hibp
  -- replace `deriv F` by `h` (a.e.)
  have hderivF : ∀ᵐ x, deriv F x = h x := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hh] with x hx
    exact (hx x₀).deriv
  have hcongr : ∫ x in (-M)..M, deriv F x * ψ x = ∫ x in (-M)..M, h x * ψ x := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hderivF] with x hx
    intro _; rw [hx]
  rw [hcongr] at hibp
  -- confine the two full-line integrals to `[-M, M]`
  have hLHS : ∫ x, F x * deriv ψ x = ∫ x in (-M)..M, F x * deriv ψ x := by
    rw [intervalIntegral.integral_of_le hab]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)).symm
    rw [hderivψ0 x (fun hmem => hx (Set.Ioo_subset_Ioc_self hmem)), mul_zero]
  have hRHS : ∫ x, h x * ψ x = ∫ x in (-M)..M, h x * ψ x := by
    rw [intervalIntegral.integral_of_le hab]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)).symm
    rw [hψ0' x (fun hmem => hx (Set.Ioo_subset_Ioc_self hmem)), mul_zero]
  rw [hLHS, hibp, hRHS]

end Spectra.RadialRegularity
