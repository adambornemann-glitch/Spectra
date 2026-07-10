/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.KMS.Condition
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
it. `Dynamics.evolve t` bundles as a unital `*`-homomorphism `Dynamics.evolveStarAlgHom`, and
Mathlib's `NonUnitalStarAlgHom.norm_apply_le` / `NonUnitalStarAlgHom.norm_map` (the latter via
injectivity from the two-sided inverse `α_{-t}`) give `‖α_t a‖ ≤ ‖a‖` and then `‖α_t a‖ = ‖a‖`.
Keeping the isometry a *lemma*, not a `Dynamics` field, keeps the structure minimal — the same
discipline that the conjugate-linear-`evolve` soundness bug taught.

## Main definitions

* `Dynamics.evolveStarAlgHom`, `Dynamics.evolveL` — `α_t` as a `*`-algebra hom / continuous linear
  map.
* `Dynamics.IsAnalyticElement` — `a` whose orbit extends to an entire `ℂ → A` map.
* `Dynamics.analyticExtend`, `Dynamics.sigma` — the (proof-carrying) entire extension and the flow
  `σ_z`.
* `Dynamics.analyticElements` — the set of analytic elements.

## Main statements

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

/-- The bundled `*`-homomorphism `α.evolveStarAlgHom t` applied to `a` is just `α.evolve t a`. -/
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

/-- The continuous linear map `α.evolveL t` applied to `a` is just `α.evolve t a`. -/
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

/-- The entire extension `α.analyticExtend ha` is differentiable on all of `ℂ`. -/
lemma Dynamics.analyticExtend_differentiable (α : Dynamics A) {a : A}
    (ha : α.IsAnalyticElement a) : Differentiable ℂ (α.analyticExtend ha) := ha.choose_spec.1

/-- On the real axis the entire extension recovers the orbit:
`α.analyticExtend ha t = α.evolve t a`. -/
@[simp] lemma Dynamics.analyticExtend_real (α : Dynamics A) {a : A} (ha : α.IsAnalyticElement a)
    (t : ℝ) : α.analyticExtend ha (t : ℂ) = α.evolve t a := ha.choose_spec.2 t

/-- The **complexified flow** `σ_z` on an analytic element, i.e. the analytic continuation of the
orbit evaluated at the complex time `z`. -/
noncomputable def Dynamics.sigma (α : Dynamics A) {a : A} (ha : α.IsAnalyticElement a) (z : ℂ) :
    A :=
  α.analyticExtend ha z

/-- At real time `t` the complexified flow agrees with the real flow: `σ_t(a) = α_t(a)`. -/
@[simp] lemma Dynamics.sigma_ofReal (α : Dynamics A) {a : A} (ha : α.IsAnalyticElement a) (t : ℝ) :
    α.sigma ha (t : ℂ) = α.evolve t a := α.analyticExtend_real ha t

/-- The complexified flow at time `0` is the identity: `σ_0(a) = a`. -/
@[simp] lemma Dynamics.sigma_zero (α : Dynamics A) {a : A} (ha : α.IsAnalyticElement a) :
    α.sigma ha 0 = a := by
  have h := α.sigma_ofReal ha 0
  simpa [α.evolve_zero] using h

/-! ## Analytic elements form a `*`-subalgebra -/

/-- The set of analytic elements of `α`. -/
def Dynamics.analyticElements (α : Dynamics A) : Set A := {a | α.IsAnalyticElement a}

/-- Membership in `α.analyticElements` unfolds to `α.IsAnalyticElement`. -/
@[simp] lemma Dynamics.mem_analyticElements (α : Dynamics A) {a : A} :
    a ∈ α.analyticElements ↔ α.IsAnalyticElement a := Iff.rfl

/-- `0` is an analytic element: its orbit is constant, `α_t(0) = 0`. -/
lemma Dynamics.analyticElements_zero (α : Dynamics A) : α.IsAnalyticElement (0 : A) :=
  ⟨fun _ => 0, differentiable_const 0, fun t => by simp⟩

/-- The **unit** is an analytic element: its orbit is constant, `α_t(1) = 1`. -/
lemma Dynamics.analyticElements_one (α : Dynamics A) : α.IsAnalyticElement (1 : A) :=
  ⟨fun _ => 1, differentiable_const 1, fun t => by simp [α.map_one]⟩

/-- Analytic elements are closed under addition: if `a` and `b` are analytic so is `a + b`. -/
lemma Dynamics.analyticElements_add (α : Dynamics A) {a b : A}
    (ha : α.IsAnalyticElement a) (hb : α.IsAnalyticElement b) : α.IsAnalyticElement (a + b) := by
  obtain ⟨F, hF, hFr⟩ := ha
  obtain ⟨G, hG, hGr⟩ := hb
  exact ⟨fun z => F z + G z, hF.add hG, fun t => by simp [hFr t, hGr t, map_add]⟩

/-- Analytic elements are closed under scalar multiplication: if `a` is analytic so is `c • a`. -/
lemma Dynamics.analyticElements_smul (α : Dynamics A) (c : ℂ) {a : A}
    (ha : α.IsAnalyticElement a) : α.IsAnalyticElement (c • a) := by
  obtain ⟨F, hF, hFr⟩ := ha
  exact ⟨fun z => c • F z, hF.const_smul c, fun t => by simp [hFr t, map_smul]⟩

/-- Analytic elements are closed under multiplication: if `a` and `b` are analytic so is `a * b`. -/
lemma Dynamics.analyticElements_mul (α : Dynamics A) {a b : A}
    (ha : α.IsAnalyticElement a) (hb : α.IsAnalyticElement b) : α.IsAnalyticElement (a * b) := by
  obtain ⟨F, hF, hFr⟩ := ha
  obtain ⟨G, hG, hGr⟩ := hb
  exact ⟨fun z => F z * G z, hF.mul hG, fun t => by simp [hFr t, hGr t, α.map_mul]⟩

/-- Analytic elements are closed under the `*`-operation: if `a` is analytic so is `star a`. -/
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

/-! ## Closure under the complexified flow and the group law

The analytic elements are closed under `σ_w` for **complex** `w`, and the complexified flow
satisfies the group law `σ_z ∘ σ_w = σ_{z+w}`. The witness for `σ_w(b)` being analytic is
`z ↦ σ_{z+w}(b)`, whose real boundary is `α_t(σ_w b)` by the real-shift cocycle `ext_add_real`; the
group law then follows from the identity theorem `analyticExtend_unique`. -/

/-- **Closure under the complexified flow.** If `a` is an analytic element then so is `σ_w(a)` for
every complex time `w` — its entire orbit extension is `z ↦ σ_{z+w}(a)`. -/
lemma Dynamics.isAnalyticElement_sigma (α : Dynamics A) {a : A}
    (ha : α.IsAnalyticElement a) (w : ℂ) : α.IsAnalyticElement (α.sigma ha w) := by
  refine ⟨fun z => α.analyticExtend ha (z + w), ?_, fun t => ?_⟩
  · exact (α.analyticExtend_differentiable ha).comp (differentiable_id.add_const w)
  · change α.analyticExtend ha ((t : ℂ) + w) = α.evolve t (α.analyticExtend ha w)
    rw [α.ext_add_real ha t w]

/-- **The complexified flow is a group action: `σ_z ∘ σ_w = σ_{z+w}`.** For an analytic element `a`,
`σ_z(σ_w(a)) = σ_{z+w}(a)`. Proved by the identity theorem: both sides are entire in `z` and
agree on the real axis (where they equal `α_t(σ_w a)` via the real-shift cocycle). -/
lemma Dynamics.sigma_sigma (α : Dynamics A) {a : A} (ha : α.IsAnalyticElement a) (z w : ℂ) :
    α.sigma (α.isAnalyticElement_sigma ha w) z = α.sigma ha (z + w) := by
  have key : α.analyticExtend (α.isAnalyticElement_sigma ha w)
      = fun z => α.analyticExtend ha (z + w) := by
    refine analyticExtend_unique _ _
      (α.analyticExtend_differentiable (α.isAnalyticElement_sigma ha w))
      ((α.analyticExtend_differentiable ha).comp (differentiable_id.add_const w)) (fun t => ?_)
    rw [α.analyticExtend_real (α.isAnalyticElement_sigma ha w) t, α.ext_add_real ha t w]
    simp only [Dynamics.sigma]
  change α.analyticExtend (α.isAnalyticElement_sigma ha w) z = α.analyticExtend ha (z + w)
  rw [key]

/-! ## Gaussian smoothing (toward density)

The Gaussian-smoothed elements `a_n := √(n/π) ∫ e^{-n t²} α_t(a) dt` are the Bratteli–Robinson
approximation: each `a_n` is an analytic element and `a_n → a`, so the analytic elements are dense.
This section lands the **integrability gateway** on which both hard limbs rest; the entirety of
`a_n` (differentiation under the integral) and the limit `a_n → a` (Gaussian approximate identity)
are the remaining work. -/

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

/-! ## Density: each `aₙ` is analytic, and `aₙ → a`

The two hard limbs of the Bratteli–Robinson density argument. `gaussianSmooth_isAnalyticElement`
shows `aₙ` extends to an entire `ℂ → A` map (differentiation under the integral, with a bespoke
Gaussian×linear dominating bound). `gaussianSmooth_tendsto` shows `aₙ → a` (rescale `s = √n·t`, then
dominated convergence with strong continuity). Together: the analytic elements are dense. -/

/-- The complexified Gaussian kernel `e^{-n(u - z)²} • α_u(a)` integrated over `u` to extend
`aₙ`. -/
private noncomputable def gsKern (α : Dynamics A) (a : A) (n : ℕ) (z : ℂ) (u : ℝ) : A :=
  Complex.exp (-(n : ℂ) * (((u : ℂ)) - z) ^ 2) • α.evolve u a

/-- The `z`-derivative of `gsKern`, i.e. `2n(u - z) e^{-n(u - z)²} • α_u(a)`. -/
private noncomputable def gsKernDer (α : Dynamics A) (a : A) (n : ℕ) (z : ℂ) (u : ℝ) : A :=
  ((2 * (n : ℂ) * (((u : ℂ)) - z)) * Complex.exp (-(n : ℂ) * (((u : ℂ)) - z) ^ 2)) • α.evolve u a

/-- The kernel `gsKern` is `ℂ`-differentiable in `z` with derivative `gsKernDer`. -/
private theorem hasDerivAt_gsKern (α : Dynamics A) (a : A) (n : ℕ) (z : ℂ) (u : ℝ) :
    HasDerivAt (fun z => gsKern α a n z u) (gsKernDer α a n z u) z := by
  unfold gsKern gsKernDer
  have hinner : HasDerivAt (fun z : ℂ => -(n : ℂ) * (((u : ℂ)) - z) ^ 2)
      (2 * (n : ℂ) * (((u : ℂ)) - z)) z := by
    have h1 : HasDerivAt (fun z : ℂ => ((u : ℂ)) - z) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub (u : ℂ)
    have h2 : HasDerivAt (fun z : ℂ => (((u : ℂ)) - z) ^ 2)
        (2 * (((u : ℂ)) - z) ^ 1 * (-1)) z := h1.pow 2
    have h3 := h2.const_mul (-(n : ℂ))
    convert h3 using 1
    ring
  have hexp := hinner.cexp
  have := hexp.smul_const (α.evolve u a)
  convert this using 2
  ring

/-- For fixed `z`, the kernel `gsKern` is continuous in the integration variable `u`. -/
private theorem continuous_gsKern (α : Dynamics A) (a : A) (n : ℕ) (z : ℂ) :
    Continuous (fun u : ℝ => gsKern α a n z u) := by
  unfold gsKern
  exact (Complex.continuous_exp.comp (by fun_prop)).smul (α.continuous_evolve a)

/-- Real part of the kernel exponent: `Re(-n(u - z)²) = -n((u - Re z)² - (Im z)²)`. -/
private theorem gsKern_re (n : ℕ) (z : ℂ) (u : ℝ) :
    (-(n : ℂ) * (((u : ℂ)) - z) ^ 2).re = -(n : ℝ) * ((u - z.re)^2 - z.im^2) := by
  simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im, Complex.sub_re, Complex.ofReal_re,
    Complex.sub_im, Complex.ofReal_im, pow_two]
  ring

/-- For fixed `z`, the kernel `gsKern` is integrable in `u`, dominated by a Gaussian. -/
private theorem integrable_gsKern (α : Dynamics A) (a : A) (n : ℕ) (hn : 0 < (n : ℝ)) (z : ℂ) :
    Integrable (fun u : ℝ => gsKern α a n z u) := by
  unfold gsKern
  have hb : 0 < (n / 2 : ℝ) := by positivity
  refine Integrable.mono'
    ((integrable_exp_neg_mul_sq hb).const_mul
      (Real.exp (2 * (n:ℝ) * (|z.re|^2 + |z.im|^2)) * ‖a‖))
    (continuous_gsKern α a n z).aestronglyMeasurable ?_
  filter_upwards with u
  rw [norm_smul, norm_exp, gsKern_re, α.norm_evolve]
  have hkey : (u - z.re)^2 ≥ u^2/2 - z.re^2 := by nlinarith [sq_nonneg (u - 2*z.re)]
  have hbound : -(n:ℝ) * ((u - z.re)^2 - z.im^2)
      ≤ 2 * (n:ℝ) * (|z.re|^2 + |z.im|^2) + (-(n/2:ℝ) * u^2) := by
    have h1 : z.re^2 = |z.re|^2 := (sq_abs z.re).symm
    have h2 : z.im^2 ≤ |z.im|^2 := by rw [sq_abs]
    nlinarith [hn.le, sq_nonneg z.re, sq_nonneg z.im]
  calc Real.exp (-(n:ℝ) * ((u - z.re)^2 - z.im^2)) * ‖a‖
      ≤ Real.exp (2 * (n:ℝ) * (|z.re|^2 + |z.im|^2) + (-(n/2:ℝ) * u^2)) * ‖a‖ := by gcongr
    _ = Real.exp (2 * (n:ℝ) * (|z.re|^2 + |z.im|^2)) * ‖a‖ * Real.exp (-(n/2:ℝ) * u^2) := by
        rw [Real.exp_add]; ring

/-- The Gaussian×linear majorant `C(|u| + R) e^{-(n/2)u²}` is integrable, the dominating bound. -/
private theorem integrable_gsKern_bound (n : ℕ) (hn : 0 < (n : ℝ)) (C R : ℝ) :
    Integrable (fun u : ℝ => C * (|u| + R) * Real.exp (-(n / 2 : ℝ) * u ^ 2)) := by
  have hb : 0 < (n / 2 : ℝ) := by positivity
  have h1 : Integrable (fun u : ℝ => |u| * Real.exp (-(n / 2 : ℝ) * u ^ 2)) := by
    have hmul := (integrable_mul_exp_neg_mul_sq hb)
    rw [← integrable_norm_iff hmul.aestronglyMeasurable] at hmul
    refine hmul.congr ?_
    filter_upwards with u
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs (Real.exp _),
      abs_of_nonneg (Real.exp_nonneg _)]
  have h2 : Integrable (fun u : ℝ => R * Real.exp (-(n / 2 : ℝ) * u ^ 2)) :=
    (integrable_exp_neg_mul_sq hb).const_mul R
  have h4 : Integrable (fun u : ℝ => C * (|u| * Real.exp (-(n / 2 : ℝ) * u ^ 2)
      + R * Real.exp (-(n / 2 : ℝ) * u ^ 2))) := (h1.add h2).const_mul C
  refine h4.congr ?_
  filter_upwards with u
  ring

/-- Uniform majorant for `‖gsKernDer‖` on the unit ball around `z0`, by a Gaussian×linear bound. -/
private theorem norm_gsKernDer_le (α : Dynamics A) (a : A) (n : ℕ) (hn : 0 < (n : ℝ)) (z0 : ℂ)
    (z : ℂ) (hz : z ∈ Metric.ball z0 1) (u : ℝ) :
    ‖gsKernDer α a n z u‖
      ≤ (2 * (n:ℝ) * Real.exp (2 * (n:ℝ) * (‖z0‖ + 1)^2) * ‖a‖)
          * (|u| + (‖z0‖ + 1)) * Real.exp (-(n / 2 : ℝ) * u ^ 2) := by
  unfold gsKernDer
  set R := ‖z0‖ + 1 with hR
  have hRpos : 0 ≤ R := by positivity
  have hzn : ‖z‖ ≤ R := by
    have hsum : ‖z‖ ≤ ‖z0‖ + ‖z - z0‖ := by
      have := norm_add_le z0 (z - z0); simpa using this
    have hd : ‖z - z0‖ < 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hz; exact hz
    rw [hR]; linarith
  have hzre : |z.re| ≤ R := (Complex.abs_re_le_norm z).trans hzn
  have hzim : |z.im| ≤ R := (Complex.abs_im_le_norm z).trans hzn
  rw [norm_smul, norm_mul, α.norm_evolve, norm_exp, gsKern_re]
  have hf1 : ‖2 * (n : ℂ) * (((u : ℂ)) - z)‖ ≤ 2 * (n:ℝ) * (|u| + R) := by
    rw [norm_mul, norm_mul]
    have hcoeff : ‖(2 : ℂ)‖ * ‖(n : ℂ)‖ = 2 * (n:ℝ) := by
      rw [Complex.norm_natCast]; norm_num
    rw [hcoeff]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ‖(((u : ℂ)) - z)‖ ≤ ‖(u : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ = |u| + ‖z‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |u| + R := by gcongr
  have hf2 : Real.exp (-(n:ℝ) * ((u - z.re)^2 - z.im^2))
      ≤ Real.exp (2 * (n:ℝ) * R^2) * Real.exp (-(n / 2 : ℝ) * u ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hkey : (u - z.re)^2 ≥ u^2/2 - z.re^2 := by nlinarith [sq_nonneg (u - 2*z.re)]
    have hre2 : z.re^2 ≤ R^2 := by
      have := abs_le.mp hzre; nlinarith [abs_nonneg z.re, hRpos]
    have him2 : z.im^2 ≤ R^2 := by
      have := abs_le.mp hzim; nlinarith [abs_nonneg z.im, hRpos]
    nlinarith [hn.le]
  calc ‖2 * (n : ℂ) * (((u : ℂ)) - z)‖ * Real.exp (-(n:ℝ) * ((u - z.re)^2 - z.im^2)) * ‖a‖
      ≤ (2 * (n:ℝ) * (|u| + R))
          * (Real.exp (2 * (n:ℝ) * R^2) * Real.exp (-(n / 2 : ℝ) * u ^ 2)) * ‖a‖ := by gcongr
    _ = (2 * (n:ℝ) * Real.exp (2 * (n:ℝ) * R^2) * ‖a‖) * (|u| + R)
          * Real.exp (-(n / 2 : ℝ) * u ^ 2) := by ring

/-- Differentiation under the integral: `z ↦ ∫ gsKern` is differentiable, derivative
`∫ gsKernDer`. -/
private theorem hasDerivAt_integral_gsKern (α : Dynamics A) (a : A) (n : ℕ) (hn : 0 < (n : ℝ))
    (z0 : ℂ) :
    HasDerivAt (fun z => ∫ u : ℝ, gsKern α a n z u)
      (∫ u : ℝ, gsKernDer α a n z0 u) z0 := by
  set R := ‖z0‖ + 1 with hRdef
  set C := 2 * (n:ℝ) * Real.exp (2 * (n:ℝ) * R^2) * ‖a‖ with hCdef
  have hball : Metric.ball z0 1 ∈ 𝓝 z0 := Metric.ball_mem_nhds z0 one_pos
  have hmeas : ∀ᶠ z in 𝓝 z0, AEStronglyMeasurable (fun u : ℝ => gsKern α a n z u) volume := by
    filter_upwards with z
    exact (continuous_gsKern α a n z).aestronglyMeasurable
  have hint : Integrable (fun u : ℝ => gsKern α a n z0 u) volume := integrable_gsKern α a n hn z0
  have hder_meas : AEStronglyMeasurable (fun u : ℝ => gsKernDer α a n z0 u) volume := by
    unfold gsKernDer
    refine Continuous.aestronglyMeasurable ?_
    exact (((continuous_const.mul (Complex.continuous_ofReal.sub continuous_const)).mul
      (Complex.continuous_exp.comp (by fun_prop))).smul (α.continuous_evolve a))
  have hbound : ∀ᵐ u ∂(volume : Measure ℝ), ∀ z ∈ Metric.ball z0 1,
      ‖gsKernDer α a n z u‖ ≤ C * (|u| + R) * Real.exp (-(n / 2 : ℝ) * u ^ 2) := by
    filter_upwards with u z hz
    have := norm_gsKernDer_le α a n hn z0 z hz u
    rw [hCdef, hRdef]
    convert this using 2
  have hbound_int : Integrable
      (fun u : ℝ => C * (|u| + R) * Real.exp (-(n / 2 : ℝ) * u ^ 2)) volume :=
    integrable_gsKern_bound n hn C R
  have hdiff : ∀ᵐ u ∂(volume : Measure ℝ), ∀ z ∈ Metric.ball z0 1,
      HasDerivAt (fun z => gsKern α a n z u) (gsKernDer α a n z u) z := by
    filter_upwards with u z _
    exact hasDerivAt_gsKern α a n z u
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hball hmeas hint hder_meas
    hbound hbound_int hdiff).2

/-- Each Gaussian-smoothed element `aₙ` is analytic: its orbit extends to the entire `ℂ → A` map
`z ↦ √(n/π) ∫ e^{-n(u - z)²} α_u(a) du`. -/
theorem Dynamics.gaussianSmooth_isAnalyticElement (α : Dynamics A) (a : A) (n : ℕ)
    (hn : 0 < (n : ℝ)) : α.IsAnalyticElement (α.gaussianSmooth a n) := by
  refine ⟨fun z => Real.sqrt ((n : ℝ) / Real.pi) • ∫ u : ℝ, gsKern α a n z u, ?_, ?_⟩
  · intro z0
    apply DifferentiableAt.const_smul
    exact (hasDerivAt_integral_gsKern α a n hn z0).differentiableAt
  · intro s
    change Real.sqrt ((n : ℝ) / Real.pi) • ∫ u : ℝ, gsKern α a n (s : ℂ) u
      = α.evolve s (α.gaussianSmooth a n)
    unfold Dynamics.gaussianSmooth
    have hker : ∀ u : ℝ, gsKern α a n (s : ℂ) u
        = Real.exp (-(n : ℝ) * (u - s) ^ 2) • α.evolve u a := by
      intro u
      unfold gsKern
      have hcast : Complex.exp (-(n : ℂ) * (((u : ℂ)) - (s : ℂ)) ^ 2)
          = ((Real.exp (-(n : ℝ) * (u - s) ^ 2) : ℝ) : ℂ) := by
        rw [Complex.ofReal_exp]
        congr 1
        push_cast
        ring
      rw [hcast, Complex.coe_smul]
    simp only [hker]
    rw [show (∫ u : ℝ, Real.exp (-(n : ℝ) * (u - s) ^ 2) • α.evolve u a)
        = ∫ u : ℝ, Real.exp (-(n : ℝ) * ((u + s) - s) ^ 2) • α.evolve (u + s) a from
      (integral_add_right_eq_self
        (fun u : ℝ => Real.exp (-(n : ℝ) * (u - s) ^ 2) • α.evolve u a) s).symm]
    simp only [add_sub_cancel_right]
    have hev : (fun u : ℝ => Real.exp (-(n : ℝ) * u ^ 2) • α.evolve (u + s) a)
        = fun u : ℝ => α.evolveL s (Real.exp (-(n : ℝ) * u ^ 2) • α.evolve u a) := by
      funext u
      rw [← Complex.coe_smul, ← Complex.coe_smul, map_smul, evolveL_apply]
      congr 1
      rw [add_comm, α.evolve_add]
    rw [hev]
    rw [ContinuousLinearMap.integral_comp_comm _ (α.integrable_gaussian_smul a hn)]
    set Z := ∫ u : ℝ, Real.exp (-(n : ℝ) * u ^ 2) • α.evolve u a with _hZ
    have hpull : α.evolve s (Real.sqrt ((n : ℝ) / Real.pi) • Z)
        = Real.sqrt ((n : ℝ) / Real.pi) • α.evolve s Z := by
      rw [← Complex.coe_smul, ← evolveL_apply, map_smul, evolveL_apply, Complex.coe_smul]
    rw [hpull, evolveL_apply]

/-- **Gaussian approximate identity.** The Gaussian-smoothed elements converge to `a`:
`a_n = √(n/π) ∫ e^{-n t²} α_t(a) dt → a`. This is the Bratteli–Robinson approximation showing
that, together with analyticity of each `a_n`, the analytic elements are dense. -/
theorem Dynamics.gaussianSmooth_tendsto (α : Dynamics A) (a : A) :
    Filter.Tendsto (fun n : ℕ => α.gaussianSmooth a n) Filter.atTop (nhds a) := by
  -- Reduce to the norm of the difference tending to 0.
  rw [← tendsto_sub_nhds_zero_iff]
  -- The rescaled scalar integral, whose limit drives everything.
  have hresc : Filter.Tendsto
      (fun n : ℕ => ∫ s : ℝ, Real.exp (-s ^ 2) * ‖α.evolve (s / Real.sqrt (n : ℝ)) a - a‖)
      Filter.atTop (nhds 0) := by
    -- pointwise limit
    have hptw : ∀ s : ℝ, Filter.Tendsto
        (fun n : ℕ => Real.exp (-s ^ 2) * ‖α.evolve (s / Real.sqrt (n : ℝ)) a - a‖)
        Filter.atTop (nhds 0) := by
      intro s
      have htz : Filter.Tendsto (fun n : ℕ => s / Real.sqrt (n : ℝ)) Filter.atTop (nhds 0) := by
        have h1 : Filter.Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) Filter.atTop (nhds 0) :=
          tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
        have h2 := h1.const_mul s
        simp only [mul_zero] at h2
        simpa only [div_eq_mul_inv] using h2
      have hcont : Filter.Tendsto (fun n : ℕ => α.evolve (s / Real.sqrt (n : ℝ)) a)
          Filter.atTop (nhds a) := by
        have h0 := ((α.continuous_evolve a).tendsto 0).comp htz
        simpa [Function.comp_def, α.evolve_zero] using h0
      have hnorm : Filter.Tendsto (fun n : ℕ => ‖α.evolve (s / Real.sqrt (n : ℝ)) a - a‖)
          Filter.atTop (nhds 0) := by simpa using (hcont.sub_const a).norm
      simpa using hnorm.const_mul (Real.exp (-s ^ 2))
    -- bound
    set bnd : ℝ → ℝ := fun s => Real.exp (-1 * s ^ 2) * (2 * ‖a‖) with hbnd
    have hbnd_int : Integrable bnd :=
      (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)).mul_const _
    have hlim : (∫ _s : ℝ, (0 : ℝ)) = 0 := by simp
    rw [← hlim]
    apply tendsto_integral_filter_of_dominated_convergence bnd
    · filter_upwards with n
      apply Continuous.aestronglyMeasurable
      apply Continuous.mul (by fun_prop)
      apply Continuous.norm
      exact (α.continuous_evolve a).comp (by fun_prop) |>.sub continuous_const
    · filter_upwards with n
      filter_upwards with s
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simp only [hbnd]
      have hexp : Real.exp (-1 * s ^ 2) = Real.exp (-s ^ 2) := by norm_num
      rw [hexp]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      calc ‖α.evolve (s / Real.sqrt (n : ℝ)) a - a‖
          ≤ ‖α.evolve (s / Real.sqrt (n : ℝ)) a‖ + ‖a‖ := norm_sub_le _ _
        _ = 2 * ‖a‖ := by rw [α.norm_evolve]; ring
    · exact hbnd_int
    · filter_upwards with s
      exact hptw s
  -- Squeeze `‖a_n - a‖` by `(1/√π) * (rescaled integral)`, eventually for `n ≥ 1`.
  have hsq : Filter.Tendsto
      (fun n : ℕ => (1 / Real.sqrt Real.pi)
        * ∫ s : ℝ, Real.exp (-s ^ 2) * ‖α.evolve (s / Real.sqrt (n : ℝ)) a - a‖)
      Filter.atTop (nhds 0) := by
    have := hresc.const_mul (1 / Real.sqrt Real.pi)
    simpa using this
  refine squeeze_zero_norm'
    (a := fun n : ℕ => (1 / Real.sqrt Real.pi)
      * ∫ s : ℝ, Real.exp (-s ^ 2) * ‖α.evolve (s / Real.sqrt (n : ℝ)) a - a‖) ?_ ?_
  · -- ‖a_n - a‖ ≤ (1/√π) * rescaled,  eventually for n ≥ 1
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    -- normalization representation of `a`
    have hrep : a = Real.sqrt ((n : ℝ) / Real.pi)
        • ∫ t : ℝ, Real.exp (-(n : ℝ) * t ^ 2) • a := by
      rw [integral_smul_const, integral_gaussian, smul_smul, ← Real.sqrt_mul (by positivity),
        div_mul_div_comm, mul_comm (n : ℝ) Real.pi, div_self (by positivity), Real.sqrt_one,
        one_smul]
    -- difference formula
    have hdiff : α.gaussianSmooth a n - a
        = Real.sqrt ((n : ℝ) / Real.pi)
            • ∫ t : ℝ, Real.exp (-(n : ℝ) * t ^ 2) • (α.evolve t a - a) := by
      unfold Dynamics.gaussianSmooth
      have hsub : (fun t : ℝ => Real.exp (-(n : ℝ) * t ^ 2) • (α.evolve t a - a))
          = (fun t : ℝ => Real.exp (-(n : ℝ) * t ^ 2) • α.evolve t a
              - Real.exp (-(n : ℝ) * t ^ 2) • a) := by
        ext t; rw [smul_sub]
      rw [hsub, integral_sub (α.integrable_gaussian_smul a hnpos)
        ((integrable_exp_neg_mul_sq hnpos).smul_const a), smul_sub, ← hrep]
    -- norm bound (scalar integral)
    have hnb : ‖α.gaussianSmooth a n - a‖
        ≤ Real.sqrt ((n : ℝ) / Real.pi)
            * ∫ t : ℝ, Real.exp (-(n : ℝ) * t ^ 2) * ‖α.evolve t a - a‖ := by
      rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
      congr 1; ext t
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    -- rescaling
    have hres : Real.sqrt ((n : ℝ) / Real.pi)
          * ∫ t : ℝ, Real.exp (-(n : ℝ) * t ^ 2) * ‖α.evolve t a - a‖
        = (1 / Real.sqrt Real.pi)
            * ∫ s : ℝ, Real.exp (-s ^ 2) * ‖α.evolve (s / Real.sqrt (n : ℝ)) a - a‖ := by
      set g : ℝ → ℝ := fun s => Real.exp (-s ^ 2) * ‖α.evolve (s / Real.sqrt (n : ℝ)) a - a‖
        with hg
      have hcomp : (fun t : ℝ => Real.exp (-(n : ℝ) * t ^ 2) * ‖α.evolve t a - a‖)
          = (fun t : ℝ => g (Real.sqrt (n : ℝ) * t)) := by
        ext t
        simp only [hg]
        have hsqn : Real.sqrt (n : ℝ) * t / Real.sqrt (n : ℝ) = t := by
          rw [mul_comm, mul_div_assoc, div_self (by positivity : Real.sqrt (n : ℝ) ≠ 0), mul_one]
        rw [hsqn]
        congr 2
        rw [mul_pow, Real.sq_sqrt hnpos.le]; ring
      rw [hcomp, MeasureTheory.Measure.integral_comp_mul_left g (Real.sqrt (n : ℝ)), smul_eq_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt (n : ℝ))⁻¹), ← mul_assoc,
        Real.sqrt_div hnpos.le Real.pi, div_mul_eq_mul_div,
        mul_inv_cancel₀ (by positivity : Real.sqrt (n : ℝ) ≠ 0)]
    rw [← hres]
    exact hnb
  · exact hsq

/-- **Density of the analytic elements** (Bratteli–Robinson). Every `a : A` is the limit of the
analytic sequence `a_n := α.gaussianSmooth a n` — each analytic by
`gaussianSmooth_isAnalyticElement`, converging to `a` by `gaussianSmooth_tendsto` — so the
analytic elements are norm-dense in `A`. -/
theorem Dynamics.analyticElements_dense (α : Dynamics A) : Dense (α.analyticElements) := by
  intro a
  refine mem_closure_of_tendsto (α.gaussianSmooth_tendsto a) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  exact (α.mem_analyticElements).mpr (α.gaussianSmooth_isAnalyticElement a n hnpos)

end Spectra.KMS
