/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
-/
import Spectra.KMS.Condition
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
/-!
# Analytic Elements of a One-Parameter Automorphism Group

For a `Dynamics α` on a C*-algebra `A`, an element `a : A` is an **analytic (entire) element**
if the orbit map `t ↦ α_t(a)` extends to an entire `A`-valued function `ℂ → A`. On such elements
the **complexified flow** `σ_z` is defined as the (unique) analytic continuation.

This is the Bratteli–Robinson notion of analytic element of a one-parameter automorphism group; it
is the substrate for the imaginary-time KMS condition (A2) and the Tomita–Takesaki modular flow.

## The isometry of the dynamics, for free

A `*`-automorphism of a C*-algebra is automatically **isometric**. We never assume this — we *prove*
it. `Dynamics.evolve t` bundles as a unital `*`-homomorphism `Dynamics.evolveStarAlgHom`, and Mathlib's
`NonUnitalStarAlgHom.norm_apply_le` / `NonUnitalStarAlgHom.norm_map` (the latter via injectivity from
the two-sided inverse `α_{-t}`) give `‖α_t a‖ ≤ ‖a‖` and then `‖α_t a‖ = ‖a‖`. Keeping the isometry a
*lemma*, not a `Dynamics` field, keeps the structure minimal — the same discipline that the
conjugate-linear-`evolve` soundness bug taught.

## Main definitions

* `Dynamics.evolveStarAlgHom`, `Dynamics.evolveL` — `α_t` as a `*`-algebra hom / continuous linear map.
* `Dynamics.IsAnalyticElement` — `a` whose orbit extends to an entire `ℂ → A` map.
* `Dynamics.analyticExtend`, `Dynamics.sigma` — the (proof-carrying) entire extension and the flow `σ_z`.
* `Dynamics.analyticElements` — the set of analytic elements.

## Main results

* `Dynamics.norm_evolve` — `α_t` is isometric.
* `analyticExtend_unique` — the entire extension is unique (1-D identity theorem at `ℂ → A`).
* `Dynamics.analyticElements_{zero,add,smul,mul,star}` — analytic elements form a `*`-subalgebra.
* `Dynamics.ext_add_real` — the real-shift cocycle `σ_{s+z} = α_s ∘ σ_z` (`s ∈ ℝ`).

## References

* O. Bratteli, D.W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 1*, §2.5.3.
-/

open Complex Set Filter Topology MeasureTheory
open ComplexConjugate

namespace Spectra.KMS

variable {A : Type*} [CStarAlgebra A]

/-! ## Bundling the dynamics as a `*`-homomorphism / continuous linear map -/

/-- The time-`t` automorphism `α_t` bundled as a unital `*`-algebra homomorphism `A →⋆ₐ[ℂ] A`.
This is a pure repackaging of the `Dynamics` fields — no new hypothesis. -/
noncomputable def Dynamics.evolveStarAlgHom (α : Dynamics A) (t : ℝ) : A →⋆ₐ[ℂ] A :=
  { AlgHom.ofLinearMap (α.evolve t) (α.map_one t) (α.map_mul t) with
    map_star' := α.map_star t }

@[simp] lemma Dynamics.evolveStarAlgHom_apply (α : Dynamics A) (t : ℝ) (a : A) :
    α.evolveStarAlgHom t a = α.evolve t a := rfl

/-- Each `α_t` is norm-contractive: a unital `*`-homomorphism of C*-algebras is contractive. -/
lemma Dynamics.norm_evolve_le (α : Dynamics A) (t : ℝ) (a : A) : ‖α.evolve t a‖ ≤ ‖a‖ := by
  simpa using NonUnitalStarAlgHom.norm_apply_le (α.evolveStarAlgHom t) a

/-- Each `α_t` is injective, with two-sided inverse `α_{-t}`. -/
lemma Dynamics.evolve_injective (α : Dynamics A) (t : ℝ) : Function.Injective (α.evolve t) := by
  intro x y h
  have hx : α.evolve (-t) (α.evolve t x) = α.evolve (-t) (α.evolve t y) := by rw [h]
  rwa [← α.evolve_add, ← α.evolve_add, neg_add_cancel, α.evolve_zero, α.evolve_zero] at hx

/-- Each `α_t` is **isometric**: a `*`-automorphism of a C*-algebra preserves the norm. -/
lemma Dynamics.norm_evolve (α : Dynamics A) (t : ℝ) (a : A) : ‖α.evolve t a‖ = ‖a‖ := by
  have hinj : Function.Injective (α.evolveStarAlgHom t) := fun x y h => α.evolve_injective t h
  simpa using NonUnitalStarAlgHom.norm_map (α.evolveStarAlgHom t) hinj a

/-- The time-`t` automorphism `α_t` as a continuous linear map `A →L[ℂ] A`. -/
noncomputable def Dynamics.evolveL (α : Dynamics A) (t : ℝ) : A →L[ℂ] A :=
  (α.evolve t).mkContinuous 1 (fun a => by simpa using α.norm_evolve_le t a)

@[simp] lemma Dynamics.evolveL_apply (α : Dynamics A) (t : ℝ) (a : A) :
    α.evolveL t a = α.evolve t a := rfl

/-! ## Analytic elements and the complexified flow -/

/-- An element `a : A` is an **analytic (entire) element** of the dynamics `α` if the orbit map
`t ↦ α_t(a)` extends to an entire `A`-valued function `ℂ → A`. -/
def Dynamics.IsAnalyticElement (α : Dynamics A) (a : A) : Prop :=
  ∃ F : ℂ → A, Differentiable ℂ F ∧ ∀ t : ℝ, F (t : ℂ) = α.evolve t a

/-- **Non-vacuity.** Under the trivial dynamics every element is analytic (`σ_z = const`). -/
lemma isAnalyticElement_trivial (a : A) : (Dynamics.trivial A).IsAnalyticElement a :=
  ⟨fun _ => a, differentiable_const a, fun _ => rfl⟩

omit [CStarAlgebra A] in
/-- Two `A`-valued maps that are entire and agree on the real axis agree frequently near `0`. The
real line accumulates at `0`, so this feeds the identity theorem. -/
lemma frequently_ofReal_eq {F G : ℂ → A} (h : ∀ t : ℝ, F (t : ℂ) = G (t : ℂ)) :
    ∃ᶠ z in 𝓝[≠] (0 : ℂ), F z = G z := by
  have htend : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (0 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hR : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 (0 : ℝ)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hR
    · filter_upwards with n
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
      positivity
  exact htend.frequently (Frequently.of_forall (fun n => h (1 / ((n : ℝ) + 1))))

/-- **Uniqueness of the entire extension** (the 1-D identity theorem for `ℂ → A`). Two entire maps
agreeing on the real axis are equal. This pins the analytic continuation canonically. -/
lemma analyticExtend_unique (F G : ℂ → A) (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (h : ∀ t : ℝ, F (t : ℂ) = G (t : ℂ)) : F = G := by
  have hFa : AnalyticOnNhd ℂ F univ := analyticOnNhd_univ_iff_differentiable.mpr hF
  have hGa : AnalyticOnNhd ℂ G univ := analyticOnNhd_univ_iff_differentiable.mpr hG
  funext z
  exact hFa.eqOn_of_preconnected_of_frequently_eq hGa isPreconnected_univ (mem_univ 0)
    (frequently_ofReal_eq h) (mem_univ z)

/-- The canonical entire extension of the orbit of an analytic element. Carries the analyticity
proof as an explicit argument (never a total junk function on non-analytic elements). -/
noncomputable def Dynamics.analyticExtend (α : Dynamics A) {a : A} (ha : α.IsAnalyticElement a) :
    ℂ → A := ha.choose

lemma Dynamics.analyticExtend_differentiable (α : Dynamics A) {a : A}
    (ha : α.IsAnalyticElement a) : Differentiable ℂ (α.analyticExtend ha) := ha.choose_spec.1

@[simp] lemma Dynamics.analyticExtend_real (α : Dynamics A) {a : A} (ha : α.IsAnalyticElement a)
    (t : ℝ) : α.analyticExtend ha (t : ℂ) = α.evolve t a := ha.choose_spec.2 t

/-- The **complexified flow** `σ_z` on an analytic element, i.e. the analytic continuation of the
orbit evaluated at the complex time `z`. -/
noncomputable def Dynamics.sigma (α : Dynamics A) {a : A} (ha : α.IsAnalyticElement a) (z : ℂ) : A :=
  α.analyticExtend ha z

@[simp] lemma Dynamics.sigma_ofReal (α : Dynamics A) {a : A} (ha : α.IsAnalyticElement a) (t : ℝ) :
    α.sigma ha (t : ℂ) = α.evolve t a := α.analyticExtend_real ha t

@[simp] lemma Dynamics.sigma_zero (α : Dynamics A) {a : A} (ha : α.IsAnalyticElement a) :
    α.sigma ha 0 = a := by
  have h := α.sigma_ofReal ha 0
  simpa [α.evolve_zero] using h

/-! ## Analytic elements form a `*`-subalgebra -/

/-- The set of analytic elements of `α`. -/
def Dynamics.analyticElements (α : Dynamics A) : Set A := {a | α.IsAnalyticElement a}

@[simp] lemma Dynamics.mem_analyticElements (α : Dynamics A) {a : A} :
    a ∈ α.analyticElements ↔ α.IsAnalyticElement a := Iff.rfl

lemma Dynamics.analyticElements_zero (α : Dynamics A) : α.IsAnalyticElement (0 : A) :=
  ⟨fun _ => 0, differentiable_const 0, fun t => by simp⟩

lemma Dynamics.analyticElements_add (α : Dynamics A) {a b : A}
    (ha : α.IsAnalyticElement a) (hb : α.IsAnalyticElement b) : α.IsAnalyticElement (a + b) := by
  obtain ⟨F, hF, hFr⟩ := ha
  obtain ⟨G, hG, hGr⟩ := hb
  exact ⟨fun z => F z + G z, hF.add hG, fun t => by simp [hFr t, hGr t, map_add]⟩

lemma Dynamics.analyticElements_smul (α : Dynamics A) (c : ℂ) {a : A}
    (ha : α.IsAnalyticElement a) : α.IsAnalyticElement (c • a) := by
  obtain ⟨F, hF, hFr⟩ := ha
  exact ⟨fun z => c • F z, hF.const_smul c, fun t => by simp [hFr t, map_smul]⟩

lemma Dynamics.analyticElements_mul (α : Dynamics A) {a b : A}
    (ha : α.IsAnalyticElement a) (hb : α.IsAnalyticElement b) : α.IsAnalyticElement (a * b) := by
  obtain ⟨F, hF, hFr⟩ := ha
  obtain ⟨G, hG, hGr⟩ := hb
  exact ⟨fun z => F z * G z, hF.mul hG, fun t => by simp [hFr t, hGr t, α.map_mul]⟩

lemma Dynamics.analyticElements_star (α : Dynamics A) {a : A}
    (ha : α.IsAnalyticElement a) : α.IsAnalyticElement (star a) := by
  obtain ⟨F, hF, hFr⟩ := ha
  refine ⟨fun z => star (F (conj z)), ?_, ?_⟩
  · intro z
    have hd := differentiableAt_star_conj_iff.mpr (hF (conj z))
    simpa [Function.comp_def] using hd
  · intro t
    simp only [Complex.conj_ofReal, hFr t]
    rw [← α.map_star]

/-! ## The real-shift cocycle -/

/-- **Real-shift cocycle:** `σ_{s+z} = α_s(σ_z)` for real `s`. The `t ∈ ℝ` boundary specialization
of the σ group law, proved by lifting the boundary identity `α_{s+t} = α_s ∘ α_t` through the
uniqueness of the entire extension. -/
lemma Dynamics.ext_add_real (α : Dynamics A) {a : A} (ha : α.IsAnalyticElement a) (s : ℝ) (z : ℂ) :
    α.analyticExtend ha ((s : ℂ) + z) = α.evolve s (α.analyticExtend ha z) := by
  have key : (fun z => α.analyticExtend ha ((s : ℂ) + z))
      = (fun z => α.evolveL s (α.analyticExtend ha z)) := by
    refine analyticExtend_unique _ _
      ((α.analyticExtend_differentiable ha).comp (differentiable_id.const_add (s : ℂ)))
      ((α.evolveL s).differentiable.comp (α.analyticExtend_differentiable ha)) (fun t => ?_)
    have hcast : (s : ℂ) + (t : ℂ) = ((s + t : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, α.analyticExtend_real ha (s + t), evolveL_apply, α.analyticExtend_real ha t,
      α.evolve_add]
  simpa using congrFun key z

/-! ## Gaussian smoothing (toward density)

The Gaussian-smoothed elements `a_n := √(n/π) ∫ e^{-n t²} α_t(a) dt` are the Bratteli–Robinson
approximation: each `a_n` is an analytic element and `a_n → a`, so the analytic elements are dense.
This section lands the **integrability gateway** on which both hard limbs rest; the entirety of `a_n`
(differentiation under the integral) and the limit `a_n → a` (Gaussian approximate identity) are the
remaining work. -/

/-- The orbit smoothed against a Gaussian is **integrable**: `‖α_t a‖ = ‖a‖` is bounded, so the
Gaussian weight dominates `t ↦ e^{-b t²} • α_t(a)`. The gateway for the density argument. -/
lemma Dynamics.integrable_gaussian_smul (α : Dynamics A) (a : A) {b : ℝ} (hb : 0 < b) :
    Integrable (fun t : ℝ => Real.exp (-b * t ^ 2) • α.evolve t a) := by
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-b * t ^ 2) • α.evolve t a) volume :=
    ((Real.continuous_exp.comp (by fun_prop)).smul (α.continuous_evolve a)).aestronglyMeasurable
  refine Integrable.mono' ((integrable_exp_neg_mul_sq hb).mul_const ‖a‖) hmeas ?_
  filter_upwards with t
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  exact mul_le_mul_of_nonneg_left (α.norm_evolve_le t a) (Real.exp_nonneg _)

/-- The **Gaussian-smoothed element** `a_n := √(n/π) ∫ e^{-n t²} α_t(a) dt`. -/
noncomputable def Dynamics.gaussianSmooth (α : Dynamics A) (a : A) (n : ℕ) : A :=
  Real.sqrt ((n : ℝ) / Real.pi) • ∫ t : ℝ, Real.exp (-(n : ℝ) * t ^ 2) • α.evolve t a

end Spectra.KMS
