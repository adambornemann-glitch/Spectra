/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Weak-derivative regularity for the radial ODE

The one-dimensional elliptic-regularity bootstrap of the forward direction of
`hydrogen_discrete_spectrum`: it upgrades a weak (distributional) solution of the log-coordinate
radial ODE `c'' + c' − b c = 0` to a genuine pointwise `C²` solution. The headline result
`classical_of_weak_ode` is imported and invoked directly by the `Hydrogen/Spectrum/` files
(`SectorProjection`, `Forward`, `Discrete`, `SeparatedEigenfunction/Span`).

## Main statements

* `exists_contDiff_hasCompactSupport_deriv_eq` — a smooth compactly supported function with
  zero integral is the derivative of a smooth compactly supported function (its primitive).
* `ae_eq_const_of_integral_deriv_mul_eq_zero` — **du Bois-Reymond's lemma**: a locally
  integrable `f` whose distributional derivative vanishes (tested against all smooth compactly
  supported `g` via `∫ g' · f = 0`) is almost everywhere constant.
* `ae_eq_affine_of_integral_deriv2_mul_eq_zero` — **second-order du Bois-Reymond**: a locally
  integrable `f` whose distributional second derivative vanishes is almost everywhere affine.
* `integral_primitive_mul_deriv` — integration by parts against a primitive `x ↦ ∫_{x₀}^x h`:
  `∫ (∫_{x₀}^· h) · ψ' = -∫ h · ψ` for smooth compactly supported `ψ`, with no boundary term.
* `classical_of_weak_ode` — **weak ODE ⟹ classical `C²`**: a locally integrable weak solution of
  `c'' + c' − b c = 0` agrees almost everywhere with a twice-differentiable function solving the
  ODE pointwise. This is the file's headline elliptic-regularity result.
* `ae_eq_continuous_of_weak_ode` — the continuity-only corollary of `classical_of_weak_ode`.

The du Bois-Reymond lemmas are general one-dimensional facts; the radial bootstrap
(`classical_of_weak_ode`) is assembled on top of them via `integral_primitive_mul_deriv`.
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
  have _hki : Integrable k volume := hkc.integrable_of_hasCompactSupport hk0
  -- bound the support inside `Icc (-R) R`
  obtain ⟨R, hR0, hRsub⟩ : ∃ R : ℝ, 0 ≤ R ∧ Function.support k ⊆ Icc (-R) R := by
    obtain ⟨R, hRsub⟩ := hk0.isBounded.subset_closedBall (0 : ℝ)
    refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
    have hx' := hRsub (subset_tsupport k hx)
    rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hx'
    exact ⟨le_trans (neg_le_neg (le_max_left _ _)) hx'.1, le_trans hx'.2 (le_max_left _ _)⟩
  set a₀ : ℝ := -R - 1 with ha₀
  set g : ℝ → ℝ := fun x => ∫ t in a₀..x, k t with _hg_def
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
    change (∫ t in a₀..x, k t) = 0
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
  set e : ℝ → ℝ := (default : ContDiffBump (0 : ℝ)).normed volume with _he_def
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
  set e : ℝ → ℝ := (default : ContDiffBump (0 : ℝ)).normed volume with _he_def
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
      ((contDiff_infty_iff_deriv.mp hg).2.continuous.mul
        continuous_id').integrable_of_hasCompactSupport
        (hg0.deriv.mul_right)
    rw [show (fun x => deriv (fun y => g y * y) x) = (fun x => deriv g x * x + g x) from
        funext hde, integral_add hint1 (hg.continuous.integrable_of_hasCompactSupport hg0)] at hz
    linarith [hz]
  -- assemble: `f - a · id` has vanishing weak derivative
  obtain ⟨b, hb⟩ := ae_eq_const_of_integral_deriv_mul_eq_zero (fun x => f x - a * x)
    (hf.sub ((continuous_const.mul continuous_id').locallyIntegrable)) (fun g hg hg0 => by
      have hdgx : Integrable (fun x => deriv g x * x) volume :=
        ((contDiff_infty_iff_deriv.mp hg).2.continuous.mul
          continuous_id').integrable_of_hasCompactSupport
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
  set F : ℝ → ℝ := fun x => ∫ t in x₀..x, h t with _hF_def
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
    intervalIntegrable_iff.mpr ((hh.integrableOn_isCompact isCompact_uIcc).mono_set
      Set.uIoc_subset_uIcc)
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

/-! ## Route B — weak ODE on `ℝ` has a classical `C²` solution

The elliptic-regularity bootstrap. A locally integrable weak solution of the (log-coordinate)
radial ODE `c'' + c' − b c = 0` — i.e. `∫ c·(χ'' − χ' − b χ) = 0` for all test `χ` — is, after
three integrations by parts against primitives, of the form `∫ (c + G₁ − G₂)·χ'' = 0`, so the
affine du Bois-Reymond lemma forces `c` to equal `c₀ = α·id + β − G₁ + G₂` almost everywhere.
That representative is then *climbed* to `C²`: `G₁ = ∫c₀` and `g = ∫b c₀` are `C¹` (FTC, `c₀`
continuous), `G₂ = ∫g` is `C²`, hence `c₀ = α·id + β − G₁ + G₂` is `C²`, and differentiating the
relation twice (`G₁' = c₀`, `g' = b c₀`, `G₂' = g`) recovers the pointwise ODE
`c₀'' + c₀' − b c₀ = 0`. -/

/-- **Weak ODE ⟹ classical `C²` solution.** If `c` is locally integrable, `b` is continuous,
and `c` weakly solves the second-order ODE `c'' + c' − b c = 0` (tested against smooth compactly
supported `χ` via `∫ c·(χ'' − χ' − bχ) = 0`), then `c` agrees almost everywhere with a function
`c₀` that is twice differentiable everywhere and solves the ODE pointwise:
`c₀'' + c₀' − b c₀ = 0`.

This is the elliptic-regularity bootstrap for the (log-coordinate) radial equation: it upgrades a
weak/distributional solution to an honest pointwise `C²` solution, the form consumed by
`RadialEq.radial_quantization` (after the `r ↔ s = log r` change of variables). -/
theorem classical_of_weak_ode {c : ℝ → ℝ} (hc : LocallyIntegrable c volume)
    {b : ℝ → ℝ} (hb : Continuous b)
    (hweak : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∫ s, c s * (deriv (deriv χ) s - deriv χ s - b s * χ s) = 0) :
    ∃ c₀ : ℝ → ℝ, c =ᵐ[volume] c₀ ∧
      (∀ x, HasDerivAt c₀ (deriv c₀ x) x) ∧
      (∀ x, HasDerivAt (deriv c₀) (deriv^[2] c₀ x) x) ∧
      (∀ x, deriv^[2] c₀ x + deriv c₀ x - b x * c₀ x = 0) := by
  -- interval integrability of `c` and `b·c`
  have hcII : ∀ p q : ℝ, IntervalIntegrable c volume p q := fun p q =>
    intervalIntegrable_iff.mpr ((hc.integrableOn_isCompact isCompact_uIcc).mono_set
      Set.uIoc_subset_uIcc)
  have hbc : LocallyIntegrable (fun x => b x * c x) volume :=
    locallyIntegrableOn_univ.mp
      ((locallyIntegrableOn_univ.mpr hc).continuousOn_mul hb.continuousOn
        isOpen_univ.isLocallyClosed)
  have hbcII : ∀ p q : ℝ, IntervalIntegrable (fun x => b x * c x) volume p q := fun p q =>
    intervalIntegrable_iff.mpr ((hbc.integrableOn_isCompact isCompact_uIcc).mono_set
      Set.uIoc_subset_uIcc)
  -- primitives `G₁ = ∫c`, `g = ∫bc`, `G₂ = ∫g`
  set G₁ : ℝ → ℝ := fun x => ∫ t in (0:ℝ)..x, c t with hG₁
  set g : ℝ → ℝ := fun x => ∫ t in (0:ℝ)..x, b t * c t with hg
  set G₂ : ℝ → ℝ := fun x => ∫ t in (0:ℝ)..x, g t with hG₂
  have hG₁cont : Continuous G₁ := intervalIntegral.continuous_primitive hcII 0
  have hgcont : Continuous g := intervalIntegral.continuous_primitive hbcII 0
  have hG₂cont : Continuous G₂ :=
    intervalIntegral.continuous_primitive (fun p q => hgcont.intervalIntegrable p q) 0
  -- the target function `f = c + G₁ − G₂`, locally integrable
  set f : ℝ → ℝ := fun x => c x + G₁ x - G₂ x with hf
  have hfloc : LocallyIntegrable f volume :=
    (hc.add hG₁cont.locallyIntegrable).sub hG₂cont.locallyIntegrable
  -- the fold gives `∫ deriv²χ · f = 0`
  have hfold : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∫ x, deriv (deriv χ) x * f x = 0 := by
    intro χ hχ hχ0
    have hχ' : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
    have hχ'0 : HasCompactSupport (deriv χ) := hχ0.deriv
    have hd2cont : Continuous (deriv (deriv χ)) := (contDiff_infty_iff_deriv.mp hχ').2.continuous
    have hd2supp : HasCompactSupport (deriv (deriv χ)) := hχ'0.deriv
    -- workhorse applications
    have hA1 : ∫ x, G₁ x * deriv (deriv χ) x = -∫ x, c x * deriv χ x :=
      integral_primitive_mul_deriv hc 0 hχ' hχ'0
    have hA2b : ∫ x, G₂ x * deriv (deriv χ) x = -∫ x, g x * deriv χ x :=
      integral_primitive_mul_deriv hgcont.locallyIntegrable 0 hχ' hχ'0
    have hA2a : ∫ x, g x * deriv χ x = -∫ x, b x * c x * χ x :=
      integral_primitive_mul_deriv hbc 0 hχ hχ0
    -- commute the workhorse results to `deriv²χ · _`
    have hA1' : ∫ x, deriv (deriv χ) x * G₁ x = -∫ x, c x * deriv χ x := by
      rw [← hA1]; exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
    have hA2' : ∫ x, deriv (deriv χ) x * G₂ x = ∫ x, b x * c x * χ x := by
      rw [show ∫ x, deriv (deriv χ) x * G₂ x = ∫ x, G₂ x * deriv (deriv χ) x from
        integral_congr_ae (ae_of_all _ fun x => mul_comm _ _), hA2b, hA2a, neg_neg]
    -- integrability of the pieces
    have iA : Integrable (fun x => deriv (deriv χ) x * c x) volume := by
      simpa only [smul_eq_mul] using hc.integrable_smul_left_of_hasCompactSupport hd2cont hd2supp
    have iG₁ : Integrable (fun x => deriv (deriv χ) x * G₁ x) volume :=
      (hd2cont.mul hG₁cont).integrable_of_hasCompactSupport hd2supp.mul_right
    have iG₂ : Integrable (fun x => deriv (deriv χ) x * G₂ x) volume :=
      (hd2cont.mul hG₂cont).integrable_of_hasCompactSupport hd2supp.mul_right
    have iB : Integrable (fun x => c x * deriv χ x) volume := by
      simpa [mul_comm] using hc.integrable_smul_left_of_hasCompactSupport hχ'.continuous hχ'0
    have iC : Integrable (fun x => b x * c x * χ x) volume := by
      simpa [mul_comm] using hbc.integrable_smul_left_of_hasCompactSupport hχ.continuous hχ0
    -- split, substitute the workhorse identities, and match the weak form
    have hsplit : ∫ x, deriv (deriv χ) x * f x
        = (∫ x, deriv (deriv χ) x * c x) + (∫ x, deriv (deriv χ) x * G₁ x)
          - ∫ x, deriv (deriv χ) x * G₂ x :=
      calc ∫ x, deriv (deriv χ) x * f x
          = ∫ x, (deriv (deriv χ) x * c x + deriv (deriv χ) x * G₁ x
              - deriv (deriv χ) x * G₂ x) :=
            integral_congr_ae (ae_of_all _ fun x => by simp only [hf]; ring)
        _ = (∫ x, (deriv (deriv χ) x * c x + deriv (deriv χ) x * G₁ x))
              - ∫ x, deriv (deriv χ) x * G₂ x := integral_sub (iA.add iG₁) iG₂
        _ = (∫ x, deriv (deriv χ) x * c x) + (∫ x, deriv (deriv χ) x * G₁ x)
              - ∫ x, deriv (deriv χ) x * G₂ x := by rw [integral_add iA iG₁]
    rw [hsplit, hA1', hA2']
    have hrw : ∫ s, c s * (deriv (deriv χ) s - deriv χ s - b s * χ s)
        = (∫ s, deriv (deriv χ) s * c s) - (∫ s, c s * deriv χ s) - ∫ s, b s * c s * χ s :=
      calc ∫ s, c s * (deriv (deriv χ) s - deriv χ s - b s * χ s)
          = ∫ s, (deriv (deriv χ) s * c s - c s * deriv χ s - b s * c s * χ s) :=
            integral_congr_ae (ae_of_all _ fun s => by ring)
        _ = (∫ s, (deriv (deriv χ) s * c s - c s * deriv χ s)) - ∫ s, b s * c s * χ s :=
            integral_sub (iA.sub iB) iC
        _ = (∫ s, deriv (deriv χ) s * c s) - (∫ s, c s * deriv χ s) - ∫ s, b s * c s * χ s := by
            rw [integral_sub iA iB]
    rw [show (∫ x, deriv (deriv χ) x * c x) + (-∫ x, c x * deriv χ x) - ∫ x, b x * c x * χ x
        = ∫ s, c s * (deriv (deriv χ) s - deriv χ s - b s * χ s) from by rw [hrw]; ring]
    exact hweak χ hχ hχ0
  obtain ⟨α, β, hαβ⟩ := ae_eq_affine_of_integral_deriv2_mul_eq_zero f hfloc hfold
  -- the continuous representative `c₀ = α·id + β − G₁ + G₂`
  set c₀ : ℝ → ℝ := fun x => α * x + β - G₁ x + G₂ x with hc₀def
  have hc₀cont : Continuous c₀ := by
    rw [hc₀def]
    exact (((continuous_const.mul continuous_id).add continuous_const).sub hG₁cont).add hG₂cont
  have hae : c =ᵐ[volume] c₀ := by
    filter_upwards [hαβ] with x hx
    simp only [hf] at hx
    change c x = α * x + β - G₁ x + G₂ x
    linarith [hx]
  -- FTC for the three primitives, re-expressed through the continuous representative
  have hbc₀cont : Continuous (fun x => b x * c₀ x) := hb.mul hc₀cont
  have hG₁eq : G₁ = fun u => ∫ t in (0:ℝ)..u, c₀ t := by
    funext u; simp only [hG₁]
    exact intervalIntegral.integral_congr_ae (by filter_upwards [hae] with t ht; exact fun _ => ht)
  have hgeq : g = fun u => ∫ t in (0:ℝ)..u, b t * c₀ t := by
    funext u; simp only [hg]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with t ht; exact fun _ => by rw [ht]
  have hG₁d : ∀ x, HasDerivAt G₁ (c₀ x) x := fun x => by
    rw [hG₁eq]
    exact (intervalIntegral.integral_hasStrictDerivAt_right (hc₀cont.intervalIntegrable _ _)
      (hc₀cont.stronglyMeasurableAtFilter _ _) hc₀cont.continuousAt).hasDerivAt
  have hgd : ∀ x, HasDerivAt g (b x * c₀ x) x := fun x => by
    rw [hgeq]
    exact (intervalIntegral.integral_hasStrictDerivAt_right (hbc₀cont.intervalIntegrable _ _)
      (hbc₀cont.stronglyMeasurableAtFilter _ _) hbc₀cont.continuousAt).hasDerivAt
  have hG₂d : ∀ x, HasDerivAt G₂ (g x) x := fun x => by
    rw [hG₂]
    exact (intervalIntegral.integral_hasStrictDerivAt_right (hgcont.intervalIntegrable _ _)
      (hgcont.stronglyMeasurableAtFilter _ _) hgcont.continuousAt).hasDerivAt
  -- first derivative of `c₀`
  have hlin : ∀ x, HasDerivAt (fun y => α * y + β) α x := fun x => by
    simpa using ((hasDerivAt_id x).const_mul α).add_const β
  have hc₀d1 : ∀ x, HasDerivAt c₀ (α - c₀ x + g x) x := fun x =>
    ((hlin x).sub (hG₁d x)).add (hG₂d x)
  have hderiv1 : ∀ x, deriv c₀ x = α - c₀ x + g x := fun x => (hc₀d1 x).deriv
  have hderiv1_eq : deriv c₀ = fun x => α - c₀ x + g x := funext hderiv1
  -- second derivative of `c₀`, recovering the pointwise ODE
  have hc₀d2 : ∀ x, HasDerivAt (deriv c₀) (-(α - c₀ x + g x) + b x * c₀ x) x := fun x => by
    rw [hderiv1_eq]
    exact ((hc₀d1 x).const_sub α).add (hgd x)
  have hderiv2 : ∀ x, deriv^[2] c₀ x = -(α - c₀ x + g x) + b x * c₀ x := fun x => by
    change deriv (deriv c₀) x = -(α - c₀ x + g x) + b x * c₀ x
    exact (hc₀d2 x).deriv
  refine ⟨c₀, hae, ?_, ?_, ?_⟩
  · intro x; rw [hderiv1 x]; exact hc₀d1 x
  · intro x; rw [hderiv2 x]; exact hc₀d2 x
  · intro x; rw [hderiv2 x, hderiv1 x]; ring

/-- **Weak ODE ⟹ continuous representative.** A locally integrable weak solution of
`c'' + c' − b c = 0` agrees almost everywhere with a continuous function. The continuity-only
corollary of `classical_of_weak_ode` (the `C²` solution is in particular continuous). -/
theorem ae_eq_continuous_of_weak_ode {c : ℝ → ℝ} (hc : LocallyIntegrable c volume)
    {b : ℝ → ℝ} (hb : Continuous b)
    (hweak : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∫ s, c s * (deriv (deriv χ) s - deriv χ s - b s * χ s) = 0) :
    ∃ c₀ : ℝ → ℝ, Continuous c₀ ∧ c =ᵐ[volume] c₀ := by
  obtain ⟨c₀, hae, hd1, _, _⟩ := classical_of_weak_ode hc hb hweak
  have hdiff : Differentiable ℝ c₀ := fun x => (hd1 x).differentiableAt
  exact ⟨c₀, hdiff.continuous, hae⟩

end Spectra.RadialRegularity
