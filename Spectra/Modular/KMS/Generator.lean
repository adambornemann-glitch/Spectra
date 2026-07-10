/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.KMS.AnalyticElements
import Mathlib.Analysis.Calculus.Deriv.Mul
/-!
# The Infinitesimal Generator of the Dynamics

On the analytic elements (A1) the one-parameter group `α` has a genuine **infinitesimal generator**
— the `*`-derivation `δ(a) = (d/dz) σ_z(a)|_{z=0}`, defined as the (complex) derivative at `0` of
the entire orbit extension `σ_z(a)`. We prove it is a `ℂ`-linear `*`-derivation. This is the
C*-algebraic generator of `Dynamics`; the Hilbert-space GNS Liouvillian is a separate
(modular-theory) development.

Each derivation law is obtained by pinning the entire extension of the combined element via the
identity theorem `analyticExtend_unique` (so `σ_z(a+b) = σ_z a + σ_z b`, etc.) and then applying the
corresponding `HasDerivAt` law (`add`, `const_smul`, `mul`, `star_conj`) at `z = 0`. Working with
the **complex** derivative keeps everything over `ℂ`, avoiding the `ℝ`-vs-`ℂ` module diamonds that a
real-parameter formulation would hit.

## Main definitions / results

* `Dynamics.generator` — the generator `δ(a)` of an analytic element.
* `Dynamics.hasDerivAt_analyticExtend` — `σ_z(a)` has complex derivative `δ(a)` at `0`.
* `Dynamics.generator_{add,smul,mul,star}` — `δ` is a `ℂ`-linear `*`-derivation (Leibniz rule).
* `IsInvariant.generator_apply` — an invariant state is annihilated by the generator: `ω(δ a) = 0`.

## The ground-state spectrum condition

The ground-state spectrum condition (Bratteli–Robinson 5.3.19) is `-i · ω(a⋆ · δ a) ≥ 0` for all
analytic `a` — the statement that the generator is positive. Its nonnegativity is the
operator-theoretic content of being a ground state; it is gated on the GNS Hamiltonian (`H ≥ 0`) of
the modular-theory development, or on spectral-measure theory, and is not proved here. The vacuum
property `ω(δ a) = 0` (below) is the part that holds for *any* invariant state.
-/

open Complex

namespace Spectra.KMS

variable {A : Type*} [CStarAlgebra A]

/-- The **infinitesimal generator** `δ(a) = (d/dz) σ_z(a)|_{z=0}` of the dynamics, defined on an
analytic element `a` as the complex derivative at `0` of its entire orbit extension `σ_z(a)`. -/
noncomputable def Dynamics.generator (α : Dynamics A) {a : A} (ha : α.IsAnalyticElement a) : A :=
  deriv (α.analyticExtend ha) 0

/-- The orbit extension `σ_z(a)` has complex derivative `δ(a)` at `0`. -/
lemma Dynamics.hasDerivAt_analyticExtend (α : Dynamics A) {a : A} (ha : α.IsAnalyticElement a) :
    HasDerivAt (α.analyticExtend ha) (α.generator ha) 0 :=
  (α.analyticExtend_differentiable ha).differentiableAt.hasDerivAt

/-- The orbit extension at `0` is the element itself: `σ_0(a) = a`. -/
lemma Dynamics.analyticExtend_zero (α : Dynamics A) {a : A} (ha : α.IsAnalyticElement a) :
    α.analyticExtend ha 0 = a := α.sigma_zero ha

/-- The generator is **additive**: `δ(a + b) = δ a + δ b`. -/
lemma Dynamics.generator_add (α : Dynamics A) {a b : A}
    (ha : α.IsAnalyticElement a) (hb : α.IsAnalyticElement b) :
    α.generator (α.analyticElements_add ha hb) = α.generator ha + α.generator hb := by
  have heq : α.analyticExtend (α.analyticElements_add ha hb)
      = fun z => α.analyticExtend ha z + α.analyticExtend hb z := by
    refine analyticExtend_unique _ _ (α.analyticExtend_differentiable _)
      ((α.analyticExtend_differentiable ha).add (α.analyticExtend_differentiable hb)) (fun t => ?_)
    simp only [α.analyticExtend_real, map_add]
  have h2 : HasDerivAt (α.analyticExtend (α.analyticElements_add ha hb))
      (α.generator ha + α.generator hb) 0 := by
    rw [heq]; exact (α.hasDerivAt_analyticExtend ha).add (α.hasDerivAt_analyticExtend hb)
  exact (α.hasDerivAt_analyticExtend (α.analyticElements_add ha hb)).unique h2

/-- The generator is **`ℂ`-homogeneous**: `δ(c • a) = c • δ a`. -/
lemma Dynamics.generator_smul (α : Dynamics A) (c : ℂ) {a : A} (ha : α.IsAnalyticElement a) :
    α.generator (α.analyticElements_smul c ha) = c • α.generator ha := by
  have heq : α.analyticExtend (α.analyticElements_smul c ha)
      = fun z => c • α.analyticExtend ha z := by
    refine analyticExtend_unique _ _ (α.analyticExtend_differentiable _)
      ((α.analyticExtend_differentiable ha).const_smul c) (fun t => ?_)
    simp only [α.analyticExtend_real, map_smul]
  have h2 : HasDerivAt (α.analyticExtend (α.analyticElements_smul c ha))
      (c • α.generator ha) 0 := by
    rw [heq]; exact (α.hasDerivAt_analyticExtend ha).const_smul c
  exact (α.hasDerivAt_analyticExtend (α.analyticElements_smul c ha)).unique h2

/-- The generator satisfies the **Leibniz rule**: `δ(a * b) = δ a * b + a * δ b`. -/
lemma Dynamics.generator_mul (α : Dynamics A) {a b : A}
    (ha : α.IsAnalyticElement a) (hb : α.IsAnalyticElement b) :
    α.generator (α.analyticElements_mul ha hb) = α.generator ha * b + a * α.generator hb := by
  have heq : α.analyticExtend (α.analyticElements_mul ha hb)
      = fun z => α.analyticExtend ha z * α.analyticExtend hb z := by
    refine analyticExtend_unique _ _ (α.analyticExtend_differentiable _)
      ((α.analyticExtend_differentiable ha).mul (α.analyticExtend_differentiable hb)) (fun t => ?_)
    simp only [α.analyticExtend_real, α.map_mul]
  have hmul := (α.hasDerivAt_analyticExtend ha).mul (α.hasDerivAt_analyticExtend hb)
  rw [α.analyticExtend_zero ha, α.analyticExtend_zero hb] at hmul
  have h2 : HasDerivAt (α.analyticExtend (α.analyticElements_mul ha hb))
      (α.generator ha * b + a * α.generator hb) 0 := by rw [heq]; exact hmul
  exact (α.hasDerivAt_analyticExtend (α.analyticElements_mul ha hb)).unique h2

/-- The generator is a **`*`-derivation**: `δ(star a) = star (δ a)`. -/
lemma Dynamics.generator_star (α : Dynamics A) {a : A} (ha : α.IsAnalyticElement a) :
    α.generator (α.analyticElements_star ha) = star (α.generator ha) := by
  have hdiff : Differentiable ℂ (fun z => star (α.analyticExtend ha (starRingEnd ℂ z))) := by
    intro z
    have hd := differentiableAt_star_conj_iff.mpr
      (α.analyticExtend_differentiable ha (starRingEnd ℂ z))
    simpa [Function.comp_def] using hd
  have heq : α.analyticExtend (α.analyticElements_star ha)
      = fun z => star (α.analyticExtend ha (starRingEnd ℂ z)) := by
    refine analyticExtend_unique _ _ (α.analyticExtend_differentiable _) hdiff (fun t => ?_)
    simp only [Complex.conj_ofReal, α.analyticExtend_real, α.map_star]
  have h2 : HasDerivAt (α.analyticExtend (α.analyticElements_star ha))
      (star (α.generator ha)) 0 := by
    rw [heq]
    simpa [Function.comp_def] using (α.hasDerivAt_analyticExtend ha).star_conj
  exact (α.hasDerivAt_analyticExtend (α.analyticElements_star ha)).unique h2

/-- The generator **annihilates the unit**: `δ(1) = 0`. The orbit of `1` is constant
(`α_t 1 = 1`), so its entire extension is the constant `1`, whose derivative vanishes. -/
lemma Dynamics.generator_one (α : Dynamics A) :
    α.generator α.analyticElements_one = 0 := by
  have heq : α.analyticExtend α.analyticElements_one = fun _ : ℂ => (1 : A) :=
    analyticExtend_unique _ _ (α.analyticExtend_differentiable _) (differentiable_const 1)
      (fun t => by rw [α.analyticExtend_real]; exact α.map_one t)
  have h1 : HasDerivAt (α.analyticExtend α.analyticElements_one)
      (α.generator α.analyticElements_one) 0 := α.hasDerivAt_analyticExtend _
  rw [heq] at h1
  exact h1.unique (hasDerivAt_const 0 (1 : A))

/-! ## Generator action on invariant states -/

/-- **An invariant state is annihilated by the generator:** `ω(δ a) = 0`. The orbit average
`z ↦ ω(σ_z a)` is entire and constant on `ℝ` (invariance), hence constant; its derivative vanishes.
-/
lemma IsInvariant.generator_apply {ω : State A} {α : Dynamics A} (hinv : IsInvariant ω α)
    {a : A} (ha : α.IsAnalyticElement a) : ω (α.generator ha) = 0 := by
  set ωL : A →L[ℂ] ℂ := ⟨ω.toFun, ω.continuous⟩ with _hωL
  have hωL_apply : ∀ x, ωL x = ω x := fun _ => rfl
  -- `z ↦ ω(σ_z a)` is constant (identity theorem: entire, constant on `ℝ`).
  have hconst : (fun z : ℂ => ω (α.analyticExtend ha z)) = fun _ : ℂ => ω a := by
    have hFa := analyticOnNhd_univ_iff_differentiable.mpr
      (ωL.differentiable.comp (α.analyticExtend_differentiable ha))
    have hGa := analyticOnNhd_univ_iff_differentiable.mpr (differentiable_const (ω a))
    funext z
    refine hFa.eqOn_of_preconnected_of_frequently_eq hGa isPreconnected_univ (Set.mem_univ 0)
      (frequently_ofReal_eq fun t => ?_) (Set.mem_univ z)
    change ω (α.analyticExtend ha (t : ℂ)) = ω a
    rw [α.analyticExtend_real]; exact hinv t a
  -- Differentiating: `ω(δ a)` is the derivative at `0`, which is `0`.
  have h1 : HasDerivAt (fun z : ℂ => ω (α.analyticExtend ha z)) (ω (α.generator ha)) 0 := by
    have h := ωL.hasFDerivAt.comp_hasDerivAt (0 : ℂ) (α.hasDerivAt_analyticExtend ha)
    simpa [Function.comp_def, hωL_apply] using h
  have h2 : HasDerivAt (fun z : ℂ => ω (α.analyticExtend ha z)) 0 0 := by
    rw [hconst]; exact hasDerivAt_const 0 (ω a)
  exact h1.unique h2

/-! ## Integration by parts and the reality of the ground-state spectral form

For an **invariant** state the generator integrates by parts — the vacuum property
`IsInvariant.generator_apply` applied to a product `a * b`, combined with the Leibniz rule,
gives `ω(δ a · b) + ω(a · δ b) = 0`. Taking `b = a` and using hermiticity forces `ω(a⋆ · δ a)`
to be **purely imaginary**; equivalently `-i · ω(a⋆ · δ a)` is **real**.

This is the *reality half* of the ground-state spectrum condition `-i·ω(a⋆·δ a) ≥ 0`
(Bratteli–Robinson, *Operator Algebras and Quantum Statistical Mechanics II*, 5.3.19). The
nonnegative *sign* is the operator-theoretic content of being a ground state (positivity of the
GNS Hamiltonian `H ≥ 0`) and is **not** proved here. Note that everything in this section holds
for *any* invariant state — in particular for any ground state via `IsGroundState.isInvariant`. -/

/-- **Integration by parts for the generator on an invariant state.** The orbit average is
annihilated by `δ` (`IsInvariant.generator_apply`) and `δ` obeys the Leibniz rule, so the two
boundary contributions cancel: `ω(δ a · b) + ω(a · δ b) = 0`. -/
lemma IsInvariant.generator_leibniz_apply {ω : State A} {α : Dynamics A}
    (hinv : IsInvariant ω α) {a b : A}
    (ha : α.IsAnalyticElement a) (hb : α.IsAnalyticElement b) :
    ω (α.generator ha * b) + ω (a * α.generator hb) = 0 := by
  have h0 := hinv.generator_apply (α.analyticElements_mul ha hb)
  rw [α.generator_mul ha hb, map_add] at h0
  exact h0

/-- **The ground-state spectral form is purely imaginary (reality half).** For an invariant
state `ω` and an analytic element `a`, the value `ω(a⋆ · δ a)` has vanishing real part. The
proof: integration by parts at `(a⋆, a)` gives `ω(δ(a⋆)·a) + ω(a⋆·δ a) = 0`, while hermiticity
(`State.star_apply`) together with `δ(a⋆) = (δ a)⋆` identifies `ω(δ(a⋆)·a) = conj (ω(a⋆·δ a))`;
hence `w + conj w = 0`, i.e. `Re w = 0`. -/
lemma IsInvariant.re_star_mul_generator_eq_zero {ω : State A} {α : Dynamics A}
    (hinv : IsInvariant ω α) {a : A} (ha : α.IsAnalyticElement a) :
    (ω (star a * α.generator ha)).re = 0 := by
  have hibp := hinv.generator_leibniz_apply (α.analyticElements_star ha) ha
  rw [α.generator_star ha] at hibp
  have hconj : ω (star (α.generator ha) * a) = star (ω (star a * α.generator ha)) := by
    have h := ω.star_apply (star a * α.generator ha)
    rwa [star_mul, star_star] at h
  rw [hconj] at hibp
  have hre := congrArg Complex.re hibp
  rw [Complex.add_re, Complex.zero_re] at hre
  have hsr : (star (ω (star a * α.generator ha))).re = (ω (star a * α.generator ha)).re := by
    rw [← starRingEnd_apply]; exact Complex.conj_re _
  rw [hsr] at hre
  linarith

/-- **Reality of the ground-state spectral form.** `-i · ω(a⋆ · δ a)` is a real number — its
imaginary part vanishes. This is the *reality half* of the ground-state spectrum condition
`-i·ω(a⋆·δ a) ≥ 0` (Bratteli–Robinson 5.3.19); the nonnegative *sign* is the GNS-Hamiltonian
content and is not proved here. -/
lemma IsInvariant.im_neg_I_mul_star_mul_generator_eq_zero {ω : State A} {α : Dynamics A}
    (hinv : IsInvariant ω α) {a : A} (ha : α.IsAnalyticElement a) :
    (-Complex.I * ω (star a * α.generator ha)).im = 0 := by
  have hre := hinv.re_star_mul_generator_eq_zero ha
  have hcalc : (-Complex.I * ω (star a * α.generator ha)).im
      = -(ω (star a * α.generator ha)).re := by
    simp [Complex.mul_im]
  rw [hcalc, hre, neg_zero]

end Spectra.KMS
