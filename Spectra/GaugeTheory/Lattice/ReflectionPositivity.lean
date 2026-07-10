/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.GaugeTheory.Lattice.GibbsMeasure
import Spectra.QuantumFieldTheory.OsterwalderSchrader.ReflectedForm

/-!
# Reflection positivity of the lattice gauge Gibbs measure — the free (β = 0) case

This file instantiates the abstract Osterwalder–Seiler positivity engine
(`OsterwalderSchrader.ReflectedForm`, Lane R2-core) on the **actual finite-lattice a-priori
measure** `aprioriMeasure = ∏ₑ dHaar` (Lane L3), discharging reflection positivity
at zero coupling — with a genuine, explicit configuration reflection `Θ`.

## Setup

A **time reflection** of the lattice splits the links into a positive-time set and a negative-time
set and pairs them up.  We model that split abstractly by a decidable predicate
`p : Link → Prop` ("positive-time links") together with a bijection
`e : {ℓ // p ℓ} ≃ {ℓ // ¬ p ℓ}` pairing
positive with negative links.  Nothing here depends on `(p, e)` being *exactly* the physical
time reflection: reflection positivity of the free measure holds for **any** such split — so the
specific geometric predicate and pairing (which, for a genuine time reflection, are
orientation-careful) are a *plug-in*, carrying **no soundness risk to the statements below**.

From `(p, e)` we build:

* `posMeasure`/`negMeasure` — the product-Haar measures on the positive/negative link variables;
* `configReflection` — the configuration reflection `Θ : Config → Config` that swaps the two halves
  through `e` (`Function.Involutive`, `configReflection_involutive`).

## Main results

* `measurePreserving_split` — `aprioriMeasure` factors as `posMeasure ⊗ negMeasure` under the link
  partition (`MeasurableEquiv.piEquivPiSubtypeProd`).  This is what ties the engine to the real L3
  lattice measure.
* `reflectionPositive_free` — the engine's reflected pairing of a positive-time observable on
  `posMeasure` collapses to `‖𝔼[f]‖²`.
* `reflectionPositive_configReflection` — **the free-case headline:** for the explicit
  configuration reflection `Θ` and a positive-time observable `F U = f (U|₊)`,
  the reflected pairing `∫ conj(F(Θ U))·F(U) d(aprioriMeasure)` equals `‖𝔼[f]‖²`,
  hence is a **nonnegative real** (`reflectionPositive_configReflection_re_nonneg`).  This is
  Osterwalder–Seiler reflection positivity for the free (`β = 0`) lattice gauge theory,
  over the genuine a-priori measure.
* `reflectionPositive_weighted_tsum` / `reflectionPositive_gibbsMeasure` — **the interacting
  (`β > 0`) case, modulo G5:** if the Wilson Boltzmann weight is a *convergent reflected
  Gram series* (the character/heat-kernel expansion Lane G5 supplies — countably infinite for
  `β > 0`), the reflected pairing over the genuine `gibbsMeasure` is `≥ 0`, by
  reducing per Gram-mode to the free-case theorem. (`reflectionPositive_weighted` is the
  finite-mode/truncated special case.)  See §6.

## What remains (documented honestly)

For the free (`β = 0`) case, only the specific *physical* choice of `(p, e)`
remains (the orientation-careful time reflection — a geometry plug-in, **not** a soundness
question; RP holds for any `(p, e)`).  For the interacting (`β > 0`) case, the sole
remaining input is the **Gram decomposition of the Wilson weight** `exp(−S)` with nonnegative
coefficients — i.e. **Lane G5's character/heat-kernel expansion** (`IsReflectionPositiveKernel`),
which needs compact-group representation theory absent from Mathlib.  Everything downstream of
that decomposition is discharged here.

## Tags

reflection positivity, Osterwalder-Seiler, lattice gauge theory, Gibbs measure, Haar measure
-/

open MeasureTheory Matrix ComplexConjugate
open Spectra.QuantumFieldTheory.OsterwalderSchrader
open scoped ENNReal

namespace Spectra.GaugeTheory.Lattice

variable {d L : ℕ} [NeZero L] {n : Type*} [Fintype n] [DecidableEq n]

/-! ## §1  The positive- and negative-time product-Haar measures -/

/-- The a-priori (product-Haar) measure on the **positive-time** link variables `{ℓ // p ℓ}`. -/
noncomputable def posMeasure (p : Link d L → Prop) [DecidablePred p] :
    Measure ({ℓ : Link d L // p ℓ} → Matrix.unitaryGroup n ℂ) :=
  Measure.pi fun _ => haarUnitary

instance (p : Link d L → Prop) [DecidablePred p] :
    IsProbabilityMeasure (posMeasure (d := d) (L := L) (n := n) p) := by
  unfold posMeasure; infer_instance

/-- The a-priori (product-Haar) measure on the **negative-time** link variables `{ℓ // ¬ p ℓ}`. -/
noncomputable def negMeasure (p : Link d L → Prop) [DecidablePred p] :
    Measure ({ℓ : Link d L // ¬ p ℓ} → Matrix.unitaryGroup n ℂ) :=
  Measure.pi fun _ => haarUnitary

instance (p : Link d L → Prop) [DecidablePred p] :
    IsProbabilityMeasure (negMeasure (d := d) (L := L) (n := n) p) := by
  unfold negMeasure; infer_instance

/-! ## §2  `aprioriMeasure` factors across the reflection plane -/

/-- **The a-priori measure factors as `posMeasure ⊗ negMeasure`** under the link partition `p`, via
`MeasurableEquiv.piEquivPiSubtypeProd`.  This is the bridge from the abstract engine to the concrete
L3 lattice measure. -/
theorem measurePreserving_split (p : Link d L → Prop) [DecidablePred p] :
    MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Link d L => Matrix.unitaryGroup n ℂ) p)
      (aprioriMeasure (d := d) (L := L) (n := n))
      ((posMeasure (d := d) (L := L) (n := n) p).prod
        (negMeasure (d := d) (L := L) (n := n) p)) := by
  unfold aprioriMeasure posMeasure negMeasure
  exact measurePreserving_piEquivPiSubtypeProd _ p

/-- **`e` reindexes `posMeasure` to `negMeasure`** — the reflection identifies the two product-Haar
half-measures (all factors are the same Haar measure). -/
theorem measurePreserving_congr (p : Link d L → Prop) [DecidablePred p]
    (e : {ℓ : Link d L // p ℓ} ≃ {ℓ : Link d L // ¬ p ℓ}) :
    MeasurePreserving
      (MeasurableEquiv.piCongrLeft
        (fun _ : {ℓ : Link d L // ¬ p ℓ} => Matrix.unitaryGroup n ℂ) e)
      (posMeasure (d := d) (L := L) (n := n) p) (negMeasure (d := d) (L := L) (n := n) p) := by
  unfold posMeasure negMeasure
  exact measurePreserving_piCongrLeft (fun _ => haarUnitary) e

/-! ## §3  Reflection positivity on the positive-time measure (engine bridge) -/

/-- **Free (β = 0) lattice reflection positivity, on the positive-time measure.**  The engine's
reflected pairing of a positive-time observable `f` collapses to `‖𝔼[f]‖²`. -/
theorem reflectionPositive_free (p : Link d L → Prop) [DecidablePred p]
    {f : ({ℓ : Link d L // p ℓ} → Matrix.unitaryGroup n ℂ) → ℂ}
    (hf : Integrable f (posMeasure (d := d) (L := L) (n := n) p)) :
    reflectedForm (posMeasure (d := d) (L := L) (n := n) p) (fun _ _ => 1) f
      = (Complex.normSq (∫ x, f x ∂(posMeasure (d := d) (L := L) (n := n) p)) : ℂ) :=
  reflectedForm_const_one _ _ hf

/-! ## §4  The configuration reflection `Θ` -/

/-- The **configuration reflection** `Θ` induced by a link partition `p` and a positive↔negative
link pairing `e`: it swaps the positive- and negative-time link variables through `e`. -/
noncomputable def configReflection (p : Link d L → Prop) [DecidablePred p]
    (e : {ℓ : Link d L // p ℓ} ≃ {ℓ : Link d L // ¬ p ℓ})
    (U : Config d L (Matrix.unitaryGroup n ℂ)) : Config d L (Matrix.unitaryGroup n ℂ) :=
  let Φ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Link d L => Matrix.unitaryGroup n ℂ) p
  let E := MeasurableEquiv.piCongrLeft
    (fun _ : {ℓ : Link d L // ¬ p ℓ} => Matrix.unitaryGroup n ℂ) e
  Φ.symm (E.symm (Φ U).2, E (Φ U).1)

variable (p : Link d L → Prop) [DecidablePred p]
    (e : {ℓ : Link d L // p ℓ} ≃ {ℓ : Link d L // ¬ p ℓ})

omit [NeZero L] in
/-- The positive-time part of the reflected configuration `Θ U` reads the negative-time links of `U`
through `e`. -/
theorem posPart_configReflection (U : Config d L (Matrix.unitaryGroup n ℂ)) :
    (fun ℓ : {ℓ : Link d L // p ℓ} => configReflection p e U ℓ.val)
      = (MeasurableEquiv.piCongrLeft
          (fun _ : {ℓ : Link d L // ¬ p ℓ} => Matrix.unitaryGroup n ℂ) e).symm
          (fun ℓ : {ℓ : Link d L // ¬ p ℓ} => U ℓ.val) := by
  funext ℓ
  simp only [configReflection, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply,
    MeasurableEquiv.piEquivPiSubtypeProd_apply]
  rw [dif_pos ℓ.2]

omit [NeZero L] in
/-- **The configuration reflection is an involution** — `Θ` is a genuine reflection. -/
theorem configReflection_involutive :
    Function.Involutive (configReflection (n := n) p e) := by
  intro U
  simp only [configReflection, MeasurableEquiv.apply_symm_apply, MeasurableEquiv.symm_apply_apply,
    Prod.mk.eta]

/-! ## §5  Reflection positivity of the free lattice theory, over `aprioriMeasure` -/

/-- **Reflection positivity of the free (β = 0) lattice gauge theory, fully explicit.**  For the
configuration reflection `Θ = configReflection p e` and a positive-time
observable `F U = f (U|₊)`, the reflected pairing
`∫ conj(F(Θ U))·F(U) d(aprioriMeasure)` equals `‖𝔼[f]‖²` — hence a **nonnegative
real** (`reflectionPositive_configReflection_re_nonneg`).  This is Osterwalder–Seiler reflection
positivity for the free lattice gauge theory, over the genuine a-priori measure. -/
theorem reflectionPositive_configReflection
    (f : ({ℓ : Link d L // p ℓ} → Matrix.unitaryGroup n ℂ) → ℂ) :
    ∫ U, conj (f (fun ℓ => configReflection p e U ℓ.val)) * f (fun ℓ => U ℓ.val)
        ∂(aprioriMeasure (d := d) (L := L) (n := n))
      = (Complex.normSq (∫ x, f x ∂(posMeasure (d := d) (L := L) (n := n) p)) : ℂ) := by
  set Φ := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : Link d L => Matrix.unitaryGroup n ℂ) p with _hΦ
  set E := MeasurableEquiv.piCongrLeft
    (fun _ : {ℓ : Link d L // ¬ p ℓ} => Matrix.unitaryGroup n ℂ) e with hE
  have hsplit : MeasurePreserving (⇑Φ) (aprioriMeasure (d := d) (L := L) (n := n))
      ((posMeasure (d := d) (L := L) (n := n) p).prod (negMeasure p)) :=
    measurePreserving_split (d := d) (L := L) (n := n) p
  have hEmp : MeasurePreserving (⇑E.symm) (negMeasure (d := d) (L := L) (n := n) p)
      (posMeasure (d := d) (L := L) (n := n) p) := (measurePreserving_congr p e).symm
  have hint : ∀ U, conj (f (fun ℓ => configReflection p e U ℓ.val)) * f (fun ℓ => U ℓ.val)
      = conj (f (E.symm (fun ℓ => U ℓ.val))) * f (fun ℓ => U ℓ.val) := by
    intro U; rw [posPart_configReflection p e U, ← hE]
  calc ∫ U, conj (f (fun ℓ => configReflection p e U ℓ.val)) * f (fun ℓ => U ℓ.val)
          ∂(aprioriMeasure (d := d) (L := L) (n := n))
      = ∫ U, conj (f (E.symm (fun ℓ => U ℓ.val))) * f (fun ℓ => U ℓ.val)
          ∂(aprioriMeasure (d := d) (L := L) (n := n)) :=
        integral_congr_ae (Filter.Eventually.of_forall hint)
    _ = ∫ z, conj (f (E.symm z.2)) * f z.1
          ∂((posMeasure (d := d) (L := L) (n := n) p).prod (negMeasure p)) :=
        hsplit.integral_comp' (g := fun z => conj (f (E.symm z.2)) * f z.1)
    _ = ∫ z, f z.1 * (fun b => conj (f (E.symm b))) z.2
          ∂((posMeasure (d := d) (L := L) (n := n) p).prod (negMeasure p)) := by
        simp_rw [mul_comm]
    _ = (∫ a, f a ∂(posMeasure (d := d) (L := L) (n := n) p))
          * (∫ b, conj (f (E.symm b)) ∂(negMeasure p)) :=
        integral_prod_mul f (fun b => conj (f (E.symm b)))
    _ = (∫ a, f a ∂(posMeasure (d := d) (L := L) (n := n) p))
          * (∫ a, conj (f a) ∂(posMeasure (d := d) (L := L) (n := n) p)) := by
        rw [hEmp.integral_comp' (g := fun a => conj (f a))]
    _ = (∫ a, f a ∂(posMeasure (d := d) (L := L) (n := n) p))
          * conj (∫ a, f a ∂(posMeasure (d := d) (L := L) (n := n) p)) := by
        rw [integral_conj]
    _ = (Complex.normSq (∫ x, f x ∂(posMeasure (d := d) (L := L) (n := n) p)) : ℂ) :=
        Complex.mul_conj _

/-- **Reflection positivity (the nonnegativity):** the free-theory reflected pairing is `≥ 0`. -/
theorem reflectionPositive_configReflection_re_nonneg
    (f : ({ℓ : Link d L // p ℓ} → Matrix.unitaryGroup n ℂ) → ℂ) :
    0 ≤ (∫ U, conj (f (fun ℓ => configReflection p e U ℓ.val)) * f (fun ℓ => U ℓ.val)
        ∂(aprioriMeasure (d := d) (L := L) (n := n))).re := by
  rw [reflectionPositive_configReflection p e f, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

/-! ## §6  The interacting (β > 0) case, reduced to the character expansion (Lane G5)

For `β > 0` the Boltzmann weight `exp(−S)` is nontrivial.  The Osterwalder–Seiler
mechanism is that, after the compact-group **character/heat-kernel expansion** of the plaquette
weight (Lane G5), the weight becomes a *reflected Gram sum* `∑ₖ conj(gₖ((ΘU)|₊))·gₖ(U|₊)` —
the exact structure the engine's `IsReflectionPositiveKernel` predicate names.  This section
proves the reflection positivity that follows from that structure, reducing the whole
`β > 0` case **per Gram-mode** to the free-case theorem
`reflectionPositive_configReflection` (applied to the observable `f·gₖ`).

**Finite vs. countable — an honesty point.**  For a *finite* Gram family the reduction is
`reflectionPositive_weighted` (a truncated / finite-mode statement, genuinely satisfiable — take
`w` *defined* as the finite sum).  But the actual Wilson weight `exp(−S)` is **not** a finite
reflected Gram sum for any `β > 0`: its reflected kernel has infinite rank (e.g. for
`U(1)`, `exp(β cos θ) = ∑ₘ Iₘ(β) e^{imθ}` has infinitely many
nonzero modes).  So the genuine interacting case needs the **countable** (`tsum`) series —
`reflectionPositive_weighted_tsum` and `reflectionPositive_gibbsMeasure` — whose hypothesis
`w U = ∑'ₖ …` *is* satisfiable at `β > 0` (that is exactly what the
convergent character expansion delivers).  The `β = 0` case is the one-mode instance
`gₖ ≡ 1` (recovering `reflectionPositive_configReflection`).

**What is proved vs. assumed.**  The reductions below are unconditional; the sole hypothesis is
the Gram series `hw` (plus routine summability/integrability).  Supplying that decomposition for
the actual Wilson weight — with nonnegative coefficients, from the character/heat-kernel expansion
— is **Lane G5**, which needs compact-group representation theory absent from Mathlib and is not
done here. -/

/-- **Reflection positivity — finite-mode (truncated) Gram-weighted form.**  If the Boltzmann
weight `w` is a *finite* reflected Gram sum
`w U = ∑ₖ conj(gₖ((ΘU)|₊))·gₖ(U|₊)`, the `w`-weighted reflected pairing
collapses to `∑ₖ ‖𝔼[f·gₖ]‖²` — a nonnegative real.  Proof: reduce per Gram-mode to
`reflectionPositive_configReflection` for the observable `f·gₖ`.  Genuinely satisfiable (take
`w` to be the finite sum), but note the *actual* Wilson weight is a finite such sum only at
`β = 0` — the interacting case needs the countable `reflectionPositive_weighted_tsum`. -/
theorem reflectionPositive_weighted
    (f : ({ℓ : Link d L // p ℓ} → Matrix.unitaryGroup n ℂ) → ℂ)
    (w : Config d L (Matrix.unitaryGroup n ℂ) → ℂ)
    {ι : Type} (s : Finset ι) (g : ι → ({ℓ : Link d L // p ℓ} → Matrix.unitaryGroup n ℂ) → ℂ)
    (hw : ∀ U, w U = ∑ k ∈ s, conj (g k (fun ℓ => configReflection p e U ℓ.val))
        * g k (fun ℓ => U ℓ.val))
    (hint : ∀ k ∈ s, Integrable (fun U =>
      conj ((fun x => f x * g k x) (fun ℓ => configReflection p e U ℓ.val))
        * (fun x => f x * g k x) (fun ℓ => U ℓ.val))
      (aprioriMeasure (d := d) (L := L) (n := n))) :
    ∫ U, w U * (conj (f (fun ℓ => configReflection p e U ℓ.val)) * f (fun ℓ => U ℓ.val))
        ∂(aprioriMeasure (d := d) (L := L) (n := n))
      = ((∑ k ∈ s, Complex.normSq
          (∫ x, f x * g k x ∂(posMeasure (d := d) (L := L) (n := n) p))) : ℂ) := by
  -- Rewrite the integrand as a finite sum of free-case integrands (for observables `f·gₖ`).
  have hpt : ∀ U, w U * (conj (f (fun ℓ => configReflection p e U ℓ.val)) * f (fun ℓ => U ℓ.val))
      = ∑ k ∈ s, conj ((fun x => f x * g k x) (fun ℓ => configReflection p e U ℓ.val))
          * (fun x => f x * g k x) (fun ℓ => U ℓ.val) := by
    intro U
    rw [hw U, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul]; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact reflectionPositive_configReflection p e (fun x => f x * g k x)

/-- **Reflection positivity (nonnegativity) of the interacting (β > 0) Gram-weighted theory.** -/
theorem reflectionPositive_weighted_re_nonneg
    (f : ({ℓ : Link d L // p ℓ} → Matrix.unitaryGroup n ℂ) → ℂ)
    (w : Config d L (Matrix.unitaryGroup n ℂ) → ℂ)
    {ι : Type} (s : Finset ι) (g : ι → ({ℓ : Link d L // p ℓ} → Matrix.unitaryGroup n ℂ) → ℂ)
    (hw : ∀ U, w U = ∑ k ∈ s, conj (g k (fun ℓ => configReflection p e U ℓ.val))
        * g k (fun ℓ => U ℓ.val))
    (hint : ∀ k ∈ s, Integrable (fun U =>
      conj ((fun x => f x * g k x) (fun ℓ => configReflection p e U ℓ.val))
        * (fun x => f x * g k x) (fun ℓ => U ℓ.val))
      (aprioriMeasure (d := d) (L := L) (n := n))) :
    0 ≤ (∫ U, w U * (conj (f (fun ℓ => configReflection p e U ℓ.val)) * f (fun ℓ => U ℓ.val))
        ∂(aprioriMeasure (d := d) (L := L) (n := n))).re := by
  rw [reflectionPositive_weighted p e f w s g hw hint]
  simp only [Complex.re_sum, Complex.ofReal_re]
  exact Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _

/-- **Countable (character-expansion) Gram-weighted form.**  If the weight `w` is a *convergent*
reflected Gram series `w U = ∑'ₖ conj(gₖ((ΘU)|₊))·gₖ(U|₊)` — the genuine character/heat-kernel
expansion, which for `β > 0` is countably infinite — the `w`-weighted reflected pairing equals
`∑'ₖ ‖𝔼[f·gₖ]‖²`.  Proof: reduce per Gram-mode to `reflectionPositive_configReflection` (via
`integral_tsum`). -/
theorem reflectionPositive_weighted_tsum
    (f : ({ℓ : Link d L // p ℓ} → Matrix.unitaryGroup n ℂ) → ℂ)
    (w : Config d L (Matrix.unitaryGroup n ℂ) → ℂ)
    {ι : Type} [Countable ι] (g : ι → ({ℓ : Link d L // p ℓ} → Matrix.unitaryGroup n ℂ) → ℂ)
    (hw : ∀ U, w U = ∑' k, conj (g k (fun ℓ => configReflection p e U ℓ.val))
        * g k (fun ℓ => U ℓ.val))
    (hsum : ∀ U, Summable fun k => conj (g k (fun ℓ => configReflection p e U ℓ.val))
        * g k (fun ℓ => U ℓ.val))
    (hmeas : ∀ k, AEStronglyMeasurable (fun U =>
      conj ((fun x => f x * g k x) (fun ℓ => configReflection p e U ℓ.val))
        * (fun x => f x * g k x) (fun ℓ => U ℓ.val))
      (aprioriMeasure (d := d) (L := L) (n := n)))
    (hfin : ∑' k, ∫⁻ U, ‖conj ((fun x => f x * g k x) (fun ℓ => configReflection p e U ℓ.val))
        * (fun x => f x * g k x) (fun ℓ => U ℓ.val)‖ₑ
        ∂(aprioriMeasure (d := d) (L := L) (n := n)) ≠ ∞) :
    ∫ U, w U * (conj (f (fun ℓ => configReflection p e U ℓ.val)) * f (fun ℓ => U ℓ.val))
        ∂(aprioriMeasure (d := d) (L := L) (n := n))
      = ∑' k, (Complex.normSq
          (∫ x, f x * g k x ∂(posMeasure (d := d) (L := L) (n := n) p)) : ℂ) := by
  have hpt : ∀ U, w U * (conj (f (fun ℓ => configReflection p e U ℓ.val)) * f (fun ℓ => U ℓ.val))
      = ∑' k, conj ((fun x => f x * g k x) (fun ℓ => configReflection p e U ℓ.val))
          * (fun x => f x * g k x) (fun ℓ => U ℓ.val) := by
    intro U
    rw [hw U, ← Summable.tsum_mul_right _ (hsum U)]
    refine tsum_congr fun k => ?_
    simp only [map_mul]; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_tsum hmeas hfin]
  refine tsum_congr fun k => ?_
  exact reflectionPositive_configReflection p e (fun x => f x * g k x)

/-- **Reflection positivity of the finite-volume lattice gauge Gibbs measure (β > 0), modulo G5.**
If the Wilson Boltzmann weight `exp(−S)` is a *convergent reflected Gram series* (the
character/heat-kernel expansion, Lane G5 — genuinely countably infinite for `β > 0`,
e.g. `∑ₘ Iₘ(β) e^{imθ}` for `U(1)`), then the reflected pairing of a positive-time
observable over the **genuine `gibbsMeasure`** is a nonnegative real.  The sole remaining input is
that Gram series (Lane G5); everything downstream is discharged here, by reduction per Gram-mode
to the free case. -/
theorem reflectionPositive_gibbsMeasure (β : ℝ)
    (f : ({ℓ : Link d L // p ℓ} → Matrix.unitaryGroup n ℂ) → ℂ)
    {ι : Type} [Countable ι] (g : ι → ({ℓ : Link d L // p ℓ} → Matrix.unitaryGroup n ℂ) → ℂ)
    (hw : ∀ U, (Real.exp (-wilsonAction β U) : ℂ)
        = ∑' k, conj (g k (fun ℓ => configReflection p e U ℓ.val)) * g k (fun ℓ => U ℓ.val))
    (hsum : ∀ U, Summable fun k => conj (g k (fun ℓ => configReflection p e U ℓ.val))
        * g k (fun ℓ => U ℓ.val))
    (hmeas : ∀ k, AEStronglyMeasurable (fun U =>
      conj ((fun x => f x * g k x) (fun ℓ => configReflection p e U ℓ.val))
        * (fun x => f x * g k x) (fun ℓ => U ℓ.val))
      (aprioriMeasure (d := d) (L := L) (n := n)))
    (hfin : ∑' k, ∫⁻ U, ‖conj ((fun x => f x * g k x) (fun ℓ => configReflection p e U ℓ.val))
        * (fun x => f x * g k x) (fun ℓ => U ℓ.val)‖ₑ
        ∂(aprioriMeasure (d := d) (L := L) (n := n)) ≠ ∞) :
    0 ≤ (∫ U, conj (f (fun ℓ => configReflection p e U ℓ.val)) * f (fun ℓ => U ℓ.val)
        ∂(gibbsMeasure (d := d) (L := L) (n := n) β)).re := by
  have hmeasd := measurable_gibbsDensity (d := d) (L := L) (n := n) β
  have hlt : ∀ᵐ U ∂(aprioriMeasure (d := d) (L := L) (n := n)), gibbsDensity β U < ⊤ :=
    Filter.Eventually.of_forall fun U => by rw [gibbsDensity]; exact ENNReal.ofReal_lt_top
  rw [gibbsMeasure, integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hmeasd hlt]
  have hdens : ∀ U, (gibbsDensity β U).toReal
        • (conj (f (fun ℓ => configReflection p e U ℓ.val)) * f (fun ℓ => U ℓ.val))
      = (Real.exp (-wilsonAction β U) : ℂ)
        * (conj (f (fun ℓ => configReflection p e U ℓ.val)) * f (fun ℓ => U ℓ.val)) := by
    intro U
    rw [gibbsDensity, ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul]
  simp_rw [hdens]
  rw [reflectionPositive_weighted_tsum p e f (fun U => (Real.exp (-wilsonAction β U) : ℂ)) g
      hw hsum hmeas hfin, ← Complex.ofReal_tsum, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.ofReal_re]
  exact mul_nonneg ENNReal.toReal_nonneg (tsum_nonneg fun k => Complex.normSq_nonneg _)

end Spectra.GaugeTheory.Lattice
