/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SpectralTheory.Calculus.PMapOfPVM
import Spectra.SpectralTheory.Weak
/-!
# The square root of a non-negative generator (R2)

For a one-parameter unitary group `U_grp` whose self-adjoint generator `A = generator U_grp` is
**non-negative** (`0 ≤ Re⟪x, A x⟫` on the domain), the unbounded calculus `pmapOfPVM U_grp √`
is the operator square root `A^{½}`, and it satisfies the **form identity**

  `‖A^{½} x‖² = Re⟪x, A x⟫`   (`norm_sq_pmapOfPVM_sqrt`),

the `L²` shadow of `(A^{½})² = A`.  In the Tomita–Takesaki setting (`A = Δ = S⋆S`, which is
`≥ 0`) the right-hand side is `‖S x‖²`, giving `‖Δ^{½} x‖ = ‖S x‖` — the isometry that drives the
polar decomposition `S = J Δ^{½}` (R3, the input to `LinearEquiv.extendOfIsometry`).

## Ingredients

* `borelMeasure_spectralProjection_restrict` — the diagonal measure of a projected vector is the
  restriction: `μ_{E(B)ξ} = μ_ξ|_B` (from `E(C)E(B) = E(C∩B)` and `‖E(·)ξ‖² = μ_ξ(·)`).
* `borelMeasure_Iio_zero_eq_zero` — for `A ≥ 0`, the spectral measure `μ_x` charges no negative
  reals: `μ_x((-∞,0)) = 0`.  Proof: `y = E((-∞,-c))x ∈ D(A)`, so `0 ≤ Re⟪y,Ay⟫ = ∫_{(-∞,-c)} s dμ_x
  ≤ -c · μ_x((-∞,-c))`, forcing `μ_x((-∞,-c)) = 0`; take `c ↓ 0`.
* `norm_sq_pmapOfPVM_sqrt` — combines the `L²` isometry `norm_sq_pmapOfPVM_apply` (`‖A^{½}x‖² =
  ∫‖√s‖²dμ_x`) with `‖√s‖² = (√s)² = s` a.e. (since `μ_x` lives on `[0,∞)`) and the first moment
  `∫ s dμ_x = Re⟪x, A x⟫` (`weak_first_moment`).
-/

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal
open Spectra.Borel
open SpectralMeasure
open Spectra.OneParameterUnitaryGroup
open Spectra.YosidaHille

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.QuantumMechanics.SpectralTheory

variable (U_grp : OneParameterUnitaryGroup (H := H))

/-! ## The diagonal measure of a projected vector is a restriction -/

/-- **Restriction.**  The spectral measure of the projected vector `E(B) ξ` is the restriction of
`μ_ξ` to `B`: `μ_{E(B)ξ} = μ_ξ|_B`.  On a measurable test set `C` both sides have mass
`μ_ξ(C ∩ B)`, since `E(C) (E(B) ξ) = E(C ∩ B) ξ` (multiplicativity) and `‖E(·)ξ‖² = μ_ξ(·)`. -/
theorem borelMeasure_spectralProjection_restrict (B : Set ℝ) (hB : MeasurableSet B) (ξ : H) :
    borelMeasure U_grp (spectralProjection U_grp B hB ξ) = (borelMeasure U_grp ξ).restrict B := by
  haveI : IsFiniteMeasure (borelMeasure U_grp (spectralProjection U_grp B hB ξ)) :=
    borelMeasure_isFiniteMeasure U_grp _
  haveI : IsFiniteMeasure (borelMeasure U_grp ξ) := borelMeasure_isFiniteMeasure U_grp ξ
  refine Measure.ext fun C hC => ?_
  rw [Measure.restrict_apply hC]
  refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp ?_
  rw [← norm_sq_spectralProjection U_grp C hC (spectralProjection U_grp B hB ξ),
    ← norm_sq_spectralProjection U_grp (C ∩ B) (hC.inter hB) ξ]
  have hvec : spectralProjection U_grp C hC (spectralProjection U_grp B hB ξ)
      = spectralProjection U_grp (C ∩ B) (hC.inter hB) ξ := by
    rw [← ContinuousLinearMap.mul_apply, spectralProjection_inter U_grp C B hC hB]
  rw [hvec]

/-! ## A non-negative generator charges no negative reals -/

/-- For a non-negative generator, the spectral measure gives zero mass to each ray `(-∞, -c)`,
`c > 0`.  The projected vector `y = E((-∞,-c)) x` lies in `D(A)`, so non-negativity gives
`0 ≤ Re⟪y, A y⟫ = ∫_{(-∞,-c)} s dμ_x ≤ -c · μ_x((-∞,-c))`, hence `μ_x((-∞,-c)) = 0`. -/
private theorem borelMeasure_Iio_neg_eq_zero
    (hpos : ∀ z : (generator U_grp).domain, 0 ≤ (⟪(z : H), generator U_grp z⟫_ℂ).re)
    (x : (generator U_grp).domain) {c : ℝ} (hc : 0 < c) :
    borelMeasure U_grp (x : H) (Set.Iio (-c)) = 0 := by
  haveI : IsFiniteMeasure (borelMeasure U_grp (x : H)) := borelMeasure_isFiniteMeasure U_grp _
  have hBmeas : MeasurableSet (Set.Iio (-c)) := measurableSet_Iio
  have hmem : spectralProjection U_grp (Set.Iio (-c)) hBmeas (x : H) ∈ generatorDomain U_grp :=
    spectralProjection_mem_generatorDomain_of_mem U_grp hBmeas x
  set y : (generator U_grp).domain :=
    ⟨spectralProjection U_grp (Set.Iio (-c)) hBmeas (x : H), hmem⟩ with _hy
  have hrestr : borelMeasure U_grp (y : H)
      = (borelMeasure U_grp (x : H)).restrict (Set.Iio (-c)) :=
    borelMeasure_spectralProjection_restrict U_grp (Set.Iio (-c)) hBmeas (x : H)
  obtain ⟨hint, hmom⟩ := weak_first_moment U_grp y
  rw [hrestr] at hint hmom
  have hpos_y : 0 ≤ ∫ s, s ∂((borelMeasure U_grp (x : H)).restrict (Set.Iio (-c))) := by
    rw [hmom]; exact hpos y
  have hle : (fun s : ℝ => s)
      ≤ᵐ[(borelMeasure U_grp (x : H)).restrict (Set.Iio (-c))] (fun _ => -c) := by
    filter_upwards [ae_restrict_mem hBmeas] with s hs
    exact le_of_lt (Set.mem_Iio.mp hs)
  have hub : ∫ s, s ∂((borelMeasure U_grp (x : H)).restrict (Set.Iio (-c)))
      ≤ ∫ _s, (-c) ∂((borelMeasure U_grp (x : H)).restrict (Set.Iio (-c))) :=
    integral_mono_ae hint (integrable_const _) hle
  simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ] at hub
  have hkey : (0 : ℝ) ≤ (borelMeasure U_grp (x : H)).real (Set.Iio (-c)) * (-c) :=
    le_trans hpos_y hub
  have hle0 : (borelMeasure U_grp (x : H)).real (Set.Iio (-c)) ≤ 0 := by
    nlinarith [hkey, hc, measureReal_nonneg (μ := borelMeasure U_grp (x : H)) (s := Set.Iio (-c))]
  have hreal0 : (borelMeasure U_grp (x : H)).real (Set.Iio (-c)) = 0 :=
    le_antisymm hle0 measureReal_nonneg
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hreal0

/-- **A non-negative generator charges no negative reals**: `μ_x((-∞,0)) = 0`.  Assembled from the
ray version `borelMeasure_Iio_neg_eq_zero` over the cover `(-∞,0) = ⋃ₖ (-∞, -1/(k+1))`. -/
theorem borelMeasure_Iio_zero_eq_zero
    (hpos : ∀ z : (generator U_grp).domain, 0 ≤ (⟪(z : H), generator U_grp z⟫_ℂ).re)
    (x : (generator U_grp).domain) :
    borelMeasure U_grp (x : H) (Set.Iio (0 : ℝ)) = 0 := by
  have hcover : Set.Iio (0 : ℝ) = ⋃ k : ℕ, Set.Iio (-(1 / (k + 1 : ℝ))) := by
    ext s
    simp only [Set.mem_Iio, Set.mem_iUnion]
    constructor
    · intro hs
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (neg_pos.mpr hs)
      exact ⟨k, by linarith⟩
    · rintro ⟨k, hk⟩
      have : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
      linarith
  rw [hcover]
  exact measure_iUnion_null fun k =>
    borelMeasure_Iio_neg_eq_zero U_grp hpos x (by positivity)

/-- **∀-vector upgrade** of `borelMeasure_Iio_zero_eq_zero`: for a *densely-defined* non-negative
generator, the spectral measure of **every** `y : H` charges no negative reals.  The projection
`E((-∞,0))` vanishes on the dense domain `D(generator U)` (there `‖E((-∞,0))z‖² = μ_z((-∞,0)) = 0`),
hence everywhere by continuity, and `μ_y((-∞,0)) = ‖E((-∞,0))y‖² = 0`. -/
theorem borelMeasure_Iio_zero_eq_zero_of_dense
    (hdense : Dense ((generator U_grp).domain : Set H))
    (hpos : ∀ z : (generator U_grp).domain, 0 ≤ (⟪(z : H), generator U_grp z⟫_ℂ).re) (y : H) :
    borelMeasure U_grp y (Set.Iio (0 : ℝ)) = 0 := by
  have hdense' : Dense (Submodule.span ℂ ((generator U_grp).domain : Set H) : Set H) := by
    rwa [Submodule.span_eq]
  have hzero : Set.EqOn (spectralProjection U_grp (Set.Iio 0) measurableSet_Iio) 0
      ((generator U_grp).domain : Set H) := by
    intro z hz
    have hμ : borelMeasure U_grp z (Set.Iio 0) = 0 :=
      borelMeasure_Iio_zero_eq_zero U_grp hpos ⟨z, hz⟩
    change spectralProjection U_grp (Set.Iio 0) measurableSet_Iio z = 0
    rw [← norm_eq_zero, ← sq_eq_zero_iff,
      norm_sq_spectralProjection U_grp (Set.Iio 0) measurableSet_Iio z, hμ]
    simp
  have hE0 : spectralProjection U_grp (Set.Iio 0) measurableSet_Iio = 0 :=
    ContinuousLinearMap.ext_on hdense' hzero
  haveI : IsFiniteMeasure (borelMeasure U_grp y) := borelMeasure_isFiniteMeasure U_grp y
  have hnorm : ((borelMeasure U_grp y (Set.Iio 0)).toReal) = 0 := by
    rw [← norm_sq_spectralProjection U_grp (Set.Iio 0) measurableSet_Iio y, hE0]
    simp
  exact ((ENNReal.toReal_eq_zero_iff _).mp hnorm).resolve_right (measure_ne_top _ _)

/-! ## The square-root form identity -/

/-- The real square-root symbol `s ↦ (√s : ℂ)` is measurable. -/
lemma measurable_sqrtC : Measurable (fun s : ℝ => (Real.sqrt s : ℂ)) :=
  (Complex.continuous_ofReal.comp Real.continuous_sqrt).measurable

/-- `‖(√s : ℂ)‖² = (√s)²`. -/
lemma norm_sqrtC_sq (s : ℝ) : ‖(Real.sqrt s : ℂ)‖ ^ 2 = Real.sqrt s ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg s)]

/-- `(√s)² ≤ |s|` (equality for `s ≥ 0`; the left side vanishes for `s < 0`). -/
lemma sq_sqrt_le_abs (s : ℝ) : Real.sqrt s ^ 2 ≤ |s| := by
  by_cases hs : 0 ≤ s
  · rw [Real.sq_sqrt hs]; exact le_abs_self s
  · rw [Real.sqrt_eq_zero_of_nonpos (not_le.mp hs).le];
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, abs_nonneg];

/-- A generator-domain vector lies in the `L²` domain of the `√` calculus: `∫ ‖√·‖² dμ_x < ∞`,
since `‖(√s:ℂ)‖² = (√s)² ≤ |s|` and `s ∈ L¹(μ_x)` (`weak_first_moment`). -/
theorem sqrt_integrable_of_mem_generator (x : (generator U_grp).domain) :
    Integrable (fun s => ‖(Real.sqrt s : ℂ)‖ ^ 2) (borelMeasure U_grp (x : H)) := by
  refine Integrable.mono' (weak_first_moment U_grp x).1.norm
    (measurable_sqrtC.norm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_sqrtC_sq, Real.norm_eq_abs]
  exact sq_sqrt_le_abs s

/-- **The square-root form identity**: for a non-negative generator `A = generator U_grp`,
`‖A^{½} x‖² = Re⟪x, A x⟫` on `D(A)`.  Combines the `L²` isometry `norm_sq_pmapOfPVM_apply`
(`‖A^{½}x‖² = ∫ ‖√s‖² dμ_x`) with `‖√s‖² = (√s)² = s` a.e. (`μ_x` is supported on `[0,∞)`,
`borelMeasure_Iio_zero_eq_zero`) and the first moment `∫ s dμ_x = Re⟪x, A x⟫`. -/
theorem norm_sq_pmapOfPVM_sqrt
    (hpos : ∀ z : (generator U_grp).domain, 0 ≤ (⟪(z : H), generator U_grp z⟫_ℂ).re)
    (x : (generator U_grp).domain) :
    ‖pmapOfPVM U_grp (fun s => (Real.sqrt s : ℂ)) measurable_sqrtC
        ⟨(x : H), (ProjValMeasure.mem_pmapDomain U_grp.toPVM).mpr
          (sqrt_integrable_of_mem_generator U_grp x)⟩‖ ^ 2
      = (⟪(x : H), generator U_grp x⟫_ℂ).re := by
  rw [norm_sq_pmapOfPVM_apply U_grp _ measurable_sqrtC (sqrt_integrable_of_mem_generator U_grp x)]
  have hμ0 : borelMeasure U_grp (x : H) (Set.Iio 0) = 0 :=
    borelMeasure_Iio_zero_eq_zero U_grp hpos x
  have hae : (fun s => ‖(Real.sqrt s : ℂ)‖ ^ 2)
      =ᵐ[borelMeasure U_grp (x : H)] (fun s => s) := by
    have hnn : ∀ᵐ s ∂(borelMeasure U_grp (x : H)), (0 : ℝ) ≤ s := by
      rw [ae_iff]
      have hset : {s : ℝ | ¬ (0 : ℝ) ≤ s} = Set.Iio 0 := by ext s; simp [not_le]
      rw [hset]; exact hμ0
    filter_upwards [hnn] with s hs
    rw [norm_sqrtC_sq, Real.sq_sqrt hs]
  rw [integral_congr_ae hae]
  exact (weak_first_moment U_grp x).2

end Spectra.QuantumMechanics.SpectralTheory
