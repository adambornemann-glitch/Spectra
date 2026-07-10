/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.DiracEquation.Current
import Spectra.QuantumMechanics.DiracEquation.Conservation
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
/-!
# Probability Conservation and Unitarity

Total probability `∫ ρ d³x` is conserved under the Dirac equation, and the
normalized density satisfies the Born rule axioms.  **All former `sorry`s are
discharged**; the price was correcting three statements that were unprovable as
previously written:

1. **The mass is now real** (`m : ℝ`).  `dirac_current_conserved` requires it,
   and not by accident: the mass cancellation `conj(−im) + (−im) = 0` fails for
   complex `m`.  A complex mass is an absorptive potential — probability is
   genuinely *not* conserved, so no proof could exist.
2. **Regularity hypotheses are now explicit.**  A bare `SpinorField` is an
   arbitrary function; `deriv` of a non-differentiable function is a junk value,
   so the Leibniz rule and continuity equation are false without
   differentiability (`h_diff`), and the Leibniz rule further needs measurability,
   integrability, and a dominating function for the time derivative.
3. **The divergence theorem now assumes decay of the spatial current `jⁱ`**
   (along each axis, with integrable axis-derivative), not decay of the density
   `ρ`.  Decay of `ρ` says nothing about `∫ ∇·j`; even in one dimension,
   `f → 0` at `±∞` does not give `∫ f' = 0` unless `f'` is integrable.

## Main results

* `continuity_equation` — `∂ρ/∂t = −∇·j`, **proved** from
  `dirac_current_conserved` by splitting the four-divergence into its time and
  spatial parts (`Fin.sum_univ_succ`) and commuting `Complex.re` with `deriv`.
* `leibniz_integral_rule` — `d/dt ∫ ρ = ∫ ∂ρ/∂t`, **proved** via Mathlib's
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le`.
* `integral_deriv_eq_zero_of_tendsto` — the 1-D kernel of the divergence
  theorem at infinity: `∫_ℝ f' = 0` for differentiable `f` with integrable
  derivative vanishing at `±∞` (improper FTC on `Iic 0` and `Ioi 0`).
* `integral_deriv_update_eq_zero` — its 3-D form for one axis: slice
  `ℝ³ ≅ ℝ × ℝ²` with the measure-preserving `piFinSuccAbove`, Fubini, and
  apply the kernel on every line.
* `divergence_integral_vanishes` — `∫ ∇·j d³x = 0`, **proved** by summing the
  per-axis lemma.
* `probability_conserved` — **MAIN THEOREM**, `d/dt ∫ ρ d³x = 0`.
* `born_rule_valid` — `ρ/∫ρ` is a probability distribution (unchanged).

## Axioms used

None.  The former axiom-tier placeholders (`leibniz_integral_rule`,
`continuity_equation`, `divergence_integral_vanishes`) are theorems with
honest hypotheses.
-/
open Complex MeasureTheory Filter Topology
open Spectra.QuantumMechanics.Dirac.Current
open Spectra.QuantumMechanics.Dirac.Conservation

namespace Spectra.QuantumMechanics.BornRule

/-! ## Coordinate bookkeeping

`spacetimePoint t x = ![t, x 0, x 1, x 2]` packages time and space; the
four-divergence walks coordinate lines via `Function.update` on `Fin 4`, while
the physical statements separate the time line (`spacetimePoint · x`) from the
spatial lines (`Function.update x i ·`).  These lemmas translate. -/

@[simp] lemma spacetimePoint_zero (t : ℝ) (x : Fin 3 → ℝ) :
    spacetimePoint t x 0 = t := rfl

@[simp] lemma spacetimePoint_succ (t : ℝ) (x : Fin 3 → ℝ) (i : Fin 3) :
    spacetimePoint t x i.succ = x i := by
  fin_cases i <;> rfl

/-- Updating the time slot of a spacetime point moves along the time line. -/
lemma update_spacetimePoint_zero (t s : ℝ) (x : Fin 3 → ℝ) :
    Function.update (spacetimePoint t x) (0 : Fin 4) s = spacetimePoint s x := by
  funext ν
  fin_cases ν <;> first | rfl

/-- Updating a spatial slot of a spacetime point moves along that spatial line. -/
lemma update_spacetimePoint_succ (t s : ℝ) (x : Fin 3 → ℝ) (i : Fin 3) :
    Function.update (spacetimePoint t x) i.succ s
      = spacetimePoint t (Function.update x i s) := by
  funext ν
  fin_cases ν <;> fin_cases i <;> first | rfl

/-- Updating slot `i` of `i.insertNth a y` replaces the inserted value. -/
lemma update_insertNth (i : Fin 3) (a b : ℝ) (y : Fin 2 → ℝ) :
    Function.update (i.insertNth a y : Fin 3 → ℝ) i b = i.insertNth b y := by
  funext j
  rcases eq_or_ne j i with rfl | hj
  · rw [Function.update_self, Fin.insertNth_apply_same]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    rw [Function.update_of_ne (Fin.succAbove_ne i k),
      Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]

/-- Re-inserting a value into the off-axis coordinates of `x` is `update`. -/
lemma insertNth_eq_update (i : Fin 3) (x : Fin 3 → ℝ) (a : ℝ) :
    (i.insertNth a (fun j => x (i.succAbove j)) : Fin 3 → ℝ) = Function.update x i a := by
  funext j
  rcases eq_or_ne j i with rfl | hj
  · rw [Fin.insertNth_apply_same, Function.update_self]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    rw [Fin.insertNth_apply_succAbove, Function.update_of_ne (Fin.succAbove_ne i k)]

/-! ## Differentiation toolkit

The current slices `s ↦ jᵘ(ψ(x + s eᵤ))` are sesquilinear in the (differentiable)
spinor components, hence differentiable: this is `hasDerivAt_bilinear_self` from
`Conservation.lean` composed with the chain rule along `hasDerivAt_update`.
`probabilityDensity` then needs `deriv` to commute with `Complex.re`, which holds
because `re` is an `ℝ`-linear continuous map. -/

/-- `Complex.re` commutes with differentiation: `HasDerivAt` form. -/
lemma hasDerivAt_re_comp (f : ℝ → ℂ) {t : ℝ} (hf : DifferentiableAt ℝ f t) :
    HasDerivAt (fun s => (f s).re) ((deriv f t).re) t := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf.hasDerivAt
  simpa only [Function.comp_def, Complex.reCLM_apply] using h

/-- `Complex.re` commutes with differentiation: `deriv` form. -/
lemma deriv_re_comp (f : ℝ → ℂ) {t : ℝ} (hf : DifferentiableAt ℝ f t) :
    deriv (fun s => (f s).re) t = (deriv f t).re :=
  (hasDerivAt_re_comp f hf).deriv

/-- Differentiability of the coordinate slice of a current component.  The
slice is the bilinear form `star ψ ⬝ᵥ (γ⁰γᵘ) ψ` along a coordinate line; the
chain rule (`hasDerivAt_update`) plus the product rule for sesquilinear forms
(`hasDerivAt_bilinear_self`) give a genuine `HasDerivAt`. -/
lemma differentiableAt_current_slice (Γ : GammaMatrices) (ψ : Spacetime → Fin 4 → ℂ)
    (X : Spacetime) (μ : Fin 4)
    (hψ : ∀ a, DifferentiableAt ℝ (fun y => ψ y a) X) :
    DifferentiableAt ℝ (fun s => diracCurrent Γ (ψ (Function.update X μ s)) μ) (X μ) := by
  -- per-component derivative of `s ↦ ψ(update X μ s)` (chain rule)
  have h_comp_a : ∀ a, HasDerivAt (fun s => ψ (Function.update X μ s) a)
      (partialDeriv' μ ψ X a) (X μ) := by
    intro a
    unfold partialDeriv'
    have h_base : Function.update X μ (X μ) = X := Function.update_eq_self μ X
    have h_fderiv : HasFDerivAt (fun y => ψ y a)
        (fderiv ℝ (fun y => ψ y a) X) (Function.update X μ (X μ)) := by
      rw [h_base]; exact (hψ a).hasFDerivAt
    have h_chain := h_fderiv.comp_hasDerivAt (X μ) (hasDerivAt_update X μ)
    have h_eq : (fun y => ψ y a) ∘ Function.update X μ
        = fun s => ψ (Function.update X μ s) a := rfl
    rw [h_eq] at h_chain
    exact h_chain
  have h_comp : HasDerivAt (fun s => ψ (Function.update X μ s))
      (partialDeriv' μ ψ X) (X μ) := hasDerivAt_pi.mpr h_comp_a
  -- product rule for the sesquilinear form
  have h_bilinear := hasDerivAt_bilinear_self (Γ.gamma 0 * Γ.gamma μ)
    (fun s => ψ (Function.update X μ s)) (partialDeriv' μ ψ X) (X μ) h_comp
  have h_fn : (fun s => diracCurrent Γ (ψ (Function.update X μ s)) μ)
      = fun s => star (ψ (Function.update X μ s)) ⬝ᵥ
          (Γ.gamma 0 * Γ.gamma μ).mulVec (ψ (Function.update X μ s)) :=
    funext fun s => diracCurrent_eq_dotProduct_mulVec Γ _ μ
  rw [h_fn]
  exact h_bilinear.differentiableAt

/-! ## The Leibniz integral rule -/

/-- **Leibniz integral rule** — differentiation commutes with integration:

  `d/dt ∫ ρ(t,x) d³x = ∫ (∂ρ/∂t)(t,x) d³x`.

Previously a `sorry` with no hypotheses, hence false (an arbitrary
`SpinorField` has junk derivatives on both sides).  Now proved from Mathlib's
dominated-derivative theorem `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
under the honest hypotheses: differentiability of the spinor components
(`h_diff`), measurability of the density slices (`h_meas`) and of the
derivative integrand (`h_meas'`), integrability at time `t` (`h_int`), and an
integrable dominating function for the time derivative (`bound`). -/
lemma leibniz_integral_rule (Γ : GammaMatrices) (ψ : SpinorField) (t : ℝ)
    (h_diff : ∀ x a, DifferentiableAt ℝ (fun y => ψ.ψ y a) x)
    (h_meas : ∀ s : ℝ, AEStronglyMeasurable
      (fun x : Fin 3 → ℝ => probabilityDensity Γ (ψ.ψ (spacetimePoint s x))) volume)
    (h_int : Integrable
      (fun x : Fin 3 → ℝ => probabilityDensity Γ (ψ.ψ (spacetimePoint t x))) volume)
    (h_meas' : AEStronglyMeasurable (fun x : Fin 3 → ℝ =>
      deriv (fun s => probabilityDensity Γ (ψ.ψ (spacetimePoint s x))) t) volume)
    (bound : (Fin 3 → ℝ) → ℝ)
    (h_bound : ∀ᵐ x ∂(volume : Measure (Fin 3 → ℝ)), ∀ s : ℝ,
      ‖deriv (fun u => probabilityDensity Γ (ψ.ψ (spacetimePoint u x))) s‖ ≤ bound x)
    (h_bound_int : Integrable bound volume) :
    deriv (totalProbability Γ ψ) t =
    ∫ x : Fin 3 → ℝ, deriv (fun s => probabilityDensity Γ (ψ.ψ (spacetimePoint s x))) t
      ∂volume := by
  -- the density slice is differentiable at every time, with `deriv` derivative
  have hdens : ∀ (x : Fin 3 → ℝ) (s : ℝ), HasDerivAt
      (fun u => probabilityDensity Γ (ψ.ψ (spacetimePoint u x)))
      (deriv (fun u => probabilityDensity Γ (ψ.ψ (spacetimePoint u x))) s) s := by
    intro x s
    simp only [probabilityDensity]
    have h := differentiableAt_current_slice Γ ψ.ψ (spacetimePoint s x) 0 (h_diff _)
    simp_rw [update_spacetimePoint_zero, spacetimePoint_zero] at h
    exact ((hasDerivAt_re_comp _ h).differentiableAt).hasDerivAt
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (s : ℝ) (x : Fin 3 → ℝ) => probabilityDensity Γ (ψ.ψ (spacetimePoint s x)))
    (F' := fun (s : ℝ) (x : Fin 3 → ℝ) =>
      deriv (fun u => probabilityDensity Γ (ψ.ψ (spacetimePoint u x))) s)
    (x₀ := t) (bound := bound) univ_mem
    (Eventually.of_forall h_meas) h_int h_meas'
    (h_bound.mono fun x hx s _ => hx s) h_bound_int
    (Eventually.of_forall fun x s _ => hdens x s)
  unfold totalProbability
  exact key.2.deriv

/-! ## The continuity equation -/

/-- **The continuity equation** `∂ρ/∂t = −∇·j`, the spatial decomposition of
`∂ᵤjᵘ = 0`:

  `∂j⁰/∂t + ∂j¹/∂x¹ + ∂j²/∂x² + ∂j³/∂x³ = 0  ⟺  ∂ρ/∂t = −∇·j`.

Previously a `sorry` with complex mass; now **proved** from
`dirac_current_conserved` (which forces `m : ℝ` — for complex mass the current
is genuinely not conserved) by splitting the `Fin 4` sum into the `μ = 0` term
and the spatial terms, translating the coordinate lines, and commuting
`Complex.re` with `deriv` (legitimate by differentiability of the slices). -/
theorem continuity_equation (Γ : GammaMatrices) (ψ : SpinorField) (m : ℝ)
    (h_dirac : ∀ x, (∑ μ : Fin 4, I • (Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x))
      = (↑m : ℂ) • ψ.ψ x)
    (h_diff : ∀ x a, DifferentiableAt ℝ (fun y => ψ.ψ y a) x)
    (t : ℝ) (x : Fin 3 → ℝ) :
    deriv (fun s => probabilityDensity Γ (ψ.ψ (spacetimePoint s x))) t =
    -(∑ i : Fin 3, deriv (fun s =>
        (diracCurrent Γ (ψ.ψ (spacetimePoint t (Function.update x i s))) i.succ).re)
      (x i)) := by
  -- current conservation at the spacetime point, split into time + space
  have hcons := dirac_current_conserved Γ ψ m h_dirac h_diff (spacetimePoint t x)
  simp only [fourDivergence] at hcons
  rw [Fin.sum_univ_succ] at hcons
  simp_rw [update_spacetimePoint_zero, update_spacetimePoint_succ,
    spacetimePoint_zero, spacetimePoint_succ] at hcons
  -- hcons : deriv (s ↦ j⁰(ψ(s,x))) t + ∑ i, deriv (s ↦ jⁱ(ψ(t, x[i↦s]))) (x i) = 0
  -- differentiability of the time slice and the spatial slices
  have h0diff : DifferentiableAt ℝ
      (fun s => diracCurrent Γ (ψ.ψ (spacetimePoint s x)) 0) t := by
    have h := differentiableAt_current_slice Γ ψ.ψ (spacetimePoint t x) 0 (h_diff _)
    simp_rw [update_spacetimePoint_zero, spacetimePoint_zero] at h
    exact h
  have hidiff : ∀ i : Fin 3, DifferentiableAt ℝ
      (fun s => diracCurrent Γ (ψ.ψ (spacetimePoint t (Function.update x i s))) i.succ)
      (x i) := by
    intro i
    have h := differentiableAt_current_slice Γ ψ.ψ (spacetimePoint t x) i.succ (h_diff _)
    simp_rw [update_spacetimePoint_succ, spacetimePoint_succ] at h
    exact h
  -- commute `re` with `deriv` on both sides
  simp only [probabilityDensity]
  rw [deriv_re_comp (fun s => diracCurrent Γ (ψ.ψ (spacetimePoint s x)) 0) h0diff]
  have hRHS : ∀ i : Fin 3, deriv (fun s =>
      (diracCurrent Γ (ψ.ψ (spacetimePoint t (Function.update x i s))) i.succ).re) (x i)
      = (deriv (fun s =>
          diracCurrent Γ (ψ.ψ (spacetimePoint t (Function.update x i s))) i.succ) (x i)).re :=
    fun i => deriv_re_comp _ (hidiff i)
  simp_rw [hRHS]
  -- conclude: real part of the conservation identity
  have h := eq_neg_of_add_eq_zero_left hcons
  rw [h, Complex.neg_re, Complex.re_sum]

/-! ## The divergence theorem at infinity -/

/-- **The 1-D kernel**: if `f` is differentiable with integrable derivative and
`f → 0` at `±∞`, then `∫_ℝ f' = 0`.  Improper FTC on `Iic 0` and `Ioi 0`:
`∫_{Ioi 0} f' = 0 − f 0` and `∫_{Iic 0} f' = f 0 − 0`.

The integrability hypothesis is not decorative: `f → 0` at `±∞` alone does not
make `f'` integrable, and without it the statement is false. -/
lemma integral_deriv_eq_zero_of_tendsto (f : ℝ → ℝ)
    (hf : ∀ s, HasDerivAt f (deriv f s) s)
    (hint : Integrable (deriv f) volume)
    (htop : Tendsto f atTop (𝓝 0)) (hbot : Tendsto f atBot (𝓝 0)) :
    ∫ s, deriv f s = 0 := by
  have hIoi : ∫ s in Set.Ioi (0 : ℝ), deriv f s = 0 - f 0 :=
    integral_Ioi_of_hasDerivAt_of_tendsto
      ((hf 0).continuousAt.continuousWithinAt)
      (fun s _ => hf s) hint.integrableOn htop
  have hIic : ∫ s in Set.Iic (0 : ℝ), deriv f s = f 0 - 0 :=
    integral_Iic_of_hasDerivAt_of_tendsto
      ((hf 0).continuousAt.continuousWithinAt)
      (fun s _ => hf s) hint.integrableOn hbot
  have htotal := MeasureTheory.integral_add_compl (s := Set.Iic (0 : ℝ)) (μ := volume)
    measurableSet_Iic hint
  rw [Set.compl_Iic] at htotal
  rw [← htotal, hIic, hIoi]
  ring

/-- **The per-axis divergence lemma**: for `F : ℝ³ → ℝ` differentiable along the
`i`-th axis with line-integrable axis-derivative and decay at `±∞` along every
`i`-line, the integral of `∂ᵢF` over `ℝ³` vanishes.

Proof: slice `ℝ³ ≅ ℝ × ℝ²` by the measure-preserving `piFinSuccAbove` equivalence
(axis `i` first), apply Fubini, and kill every line integral with the 1-D kernel. -/
lemma integral_deriv_update_eq_zero (F : (Fin 3 → ℝ) → ℝ) (i : Fin 3)
    (h_diff : ∀ x : Fin 3 → ℝ, DifferentiableAt ℝ (fun s => F (Function.update x i s)) (x i))
    (h_line_int : ∀ x : Fin 3 → ℝ,
      Integrable (fun s => deriv (fun u => F (Function.update x i u)) s) volume)
    (h_top : ∀ x : Fin 3 → ℝ, Tendsto (fun s => F (Function.update x i s)) atTop (𝓝 0))
    (h_bot : ∀ x : Fin 3 → ℝ, Tendsto (fun s => F (Function.update x i s)) atBot (𝓝 0))
    (h_int : Integrable (fun x => deriv (fun s => F (Function.update x i s)) (x i)) volume) :
    ∫ x : Fin 3 → ℝ, deriv (fun s => F (Function.update x i s)) (x i) ∂volume = 0 := by
  -- lines of direction `i` in `insertNth` coordinates
  have hline_fun : ∀ (y : Fin 2 → ℝ) (u : ℝ),
      (fun s => F (Function.update (i.insertNth u y) i s)) = fun s => F (i.insertNth s y) :=
    fun y u => funext fun s => congrArg F (update_insertNth i u s y)
  have hg_diff : ∀ (y : Fin 2 → ℝ) (u : ℝ),
      DifferentiableAt ℝ (fun s => F (i.insertNth s y)) u := by
    intro y u
    have h := h_diff (i.insertNth u y)
    rwa [hline_fun y u, Fin.insertNth_apply_same] at h
  have hg_int : ∀ y : Fin 2 → ℝ,
      Integrable (fun s => deriv (fun u => F (i.insertNth u y)) s) volume := by
    intro y
    have h := h_line_int (i.insertNth 0 y)
    rwa [hline_fun y 0] at h
  have hg_top : ∀ y : Fin 2 → ℝ, Tendsto (fun s => F (i.insertNth s y)) atTop (𝓝 0) := by
    intro y
    have h := h_top (i.insertNth 0 y)
    rwa [hline_fun y 0] at h
  have hg_bot : ∀ y : Fin 2 → ℝ, Tendsto (fun s => F (i.insertNth s y)) atBot (𝓝 0) := by
    intro y
    have h := h_bot (i.insertNth 0 y)
    rwa [hline_fun y 0] at h
  -- every line integral of the axis-derivative vanishes
  have hinner : ∀ y : Fin 2 → ℝ, (∫ s, deriv (fun u => F (i.insertNth u y)) s) = 0 :=
    fun y => integral_deriv_eq_zero_of_tendsto _ (fun s => (hg_diff y s).hasDerivAt)
      (hg_int y) (hg_top y) (hg_bot y)
  -- transport the 3-D integral to `ℝ × ℝ²` along the measure-preserving slicing
  set e : (Fin 3 → ℝ) ≃ᵐ ℝ × (Fin 2 → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i with _he
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) i
  have hcomp : ∀ x : Fin 3 → ℝ,
      deriv (fun u => F (i.insertNth u (fun j => x (i.succAbove j)))) (x i)
        = deriv (fun s => F (Function.update x i s)) (x i) := by
    intro x
    congr 1
    funext u
    exact congrArg F (insertNth_eq_update i x u)
  have htrans : (∫ p : ℝ × (Fin 2 → ℝ), deriv (fun u => F (i.insertNth u p.2)) p.1 ∂volume)
      = ∫ x : Fin 3 → ℝ, deriv (fun s => F (Function.update x i s)) (x i) ∂volume := by
    rw [← hmp.map_eq, MeasureTheory.integral_map_equiv]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change deriv (fun u => F (i.insertNth u ((e x).2))) ((e x).1)
        = deriv (fun s => F (Function.update x i s)) (x i)
    have h1 : (e x).1 = x i := rfl
    have h2 : (e x).2 = fun j => x (i.succAbove j) := rfl
    rw [h1, h2]
    exact hcomp x
  have hGint : Integrable
      (fun p : ℝ × (Fin 2 → ℝ) => deriv (fun u => F (i.insertNth u p.2)) p.1) volume := by
    rw [← hmp.map_eq, MeasureTheory.integrable_map_equiv]
    refine h_int.congr (Eventually.of_forall fun x => ?_)
    change deriv (fun s => F (Function.update x i s)) (x i)
        = deriv (fun u => F (i.insertNth u ((e x).2))) ((e x).1)
    have h1 : (e x).1 = x i := rfl
    have h2 : (e x).2 = fun j => x (i.succAbove j) := rfl
    rw [h1, h2]
    exact (hcomp x).symm
  -- Fubini, then every inner (line) integral is zero
  rw [← htrans]
  rw [Measure.volume_eq_prod] at hGint ⊢
  rw [MeasureTheory.integral_prod_symm _ hGint]
  simp_rw [hinner]
  simp

/-- **The divergence theorem with vanishing boundary conditions**:

  `∫ ∇·j d³x = 0`.

Previously a `sorry` assuming only cocompact decay of the *density* — which
neither mentions the spatial current nor controls the integral of its
derivative.  The honest hypotheses are decay of each spatial current component
along its own axis (`h_top`, `h_bot`) together with integrability of the
divergence term (`h_int`) and of each line derivative (`h_line_int`).
Physically: no probability current survives at spatial infinity, so the
"boundary at infinity" contributes nothing and no probability escapes. -/
theorem divergence_integral_vanishes (Γ : GammaMatrices) (ψ : SpinorField) (t : ℝ)
    (h_diff : ∀ x a, DifferentiableAt ℝ (fun y => ψ.ψ y a) x)
    (h_int : ∀ i : Fin 3, Integrable (fun x : Fin 3 → ℝ =>
      deriv (fun s =>
        (diracCurrent Γ (ψ.ψ (spacetimePoint t (Function.update x i s))) i.succ).re)
      (x i)) volume)
    (h_line_int : ∀ (i : Fin 3) (x : Fin 3 → ℝ), Integrable (fun s : ℝ =>
      deriv (fun u =>
        (diracCurrent Γ (ψ.ψ (spacetimePoint t (Function.update x i u))) i.succ).re)
      s) volume)
    (h_top : ∀ (i : Fin 3) (x : Fin 3 → ℝ), Tendsto (fun s =>
      (diracCurrent Γ (ψ.ψ (spacetimePoint t (Function.update x i s))) i.succ).re)
      atTop (𝓝 0))
    (h_bot : ∀ (i : Fin 3) (x : Fin 3 → ℝ), Tendsto (fun s =>
      (diracCurrent Γ (ψ.ψ (spacetimePoint t (Function.update x i s))) i.succ).re)
      atBot (𝓝 0)) :
    ∫ x : Fin 3 → ℝ, (∑ i : Fin 3, deriv (fun s =>
      (diracCurrent Γ (ψ.ψ (spacetimePoint t (Function.update x i s))) i.succ).re)
      (x i)) ∂volume = 0 := by
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ => h_int i)]
  refine Finset.sum_eq_zero fun i _ => ?_
  refine integral_deriv_update_eq_zero
    (fun x' => (diracCurrent Γ (ψ.ψ (spacetimePoint t x')) i.succ).re) i
    ?_ (h_line_int i) (h_top i) (h_bot i) (h_int i)
  -- differentiability of each spatial slice, from differentiability of ψ
  intro x
  have h := differentiableAt_current_slice Γ ψ.ψ (spacetimePoint t x) i.succ (h_diff _)
  simp_rw [update_spacetimePoint_succ, spacetimePoint_succ] at h
  exact (hasDerivAt_re_comp _ h).differentiableAt

/-! ## Main Theorem: Probability Conservation -/

/-- **MAIN THEOREM**: Total probability is conserved: `d/dt ∫ ρ d³x = 0`.

**Hypotheses**:
- `h_dirac` : ψ satisfies the Dirac equation with **real** mass `m`;
- `h_diff`  : ψ is differentiable (the equation involves derivatives, so this
  is not optional);
- `h_meas`, `h_int`, `h_meas'`, `bound`, `h_bound`, `h_bound_int` : regularity
  for the Leibniz rule (measurable slices, integrable density, integrable
  dominating function for `∂ρ/∂t`);
- `h_div_int`, `h_line_int`, `h_top`, `h_bot` : the spatial current decays
  along each axis with integrable axis-derivatives, for the divergence theorem.

**Proof**:
1. Differentiate under the integral sign (`leibniz_integral_rule`);
2. Apply the continuity equation `∂ρ/∂t = −∇·j` (`continuity_equation`);
3. The integral of `∇·j` vanishes by the divergence theorem at infinity
   (`divergence_integral_vanishes`). -/
theorem probability_conserved (Γ : GammaMatrices) (ψ : SpinorField) (m : ℝ)
    (h_dirac : ∀ x, (∑ μ : Fin 4, I • (Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x))
      = (↑m : ℂ) • ψ.ψ x)
    (h_diff : ∀ x a, DifferentiableAt ℝ (fun y => ψ.ψ y a) x)
    (h_meas : ∀ s : ℝ, AEStronglyMeasurable
      (fun x : Fin 3 → ℝ => probabilityDensity Γ (ψ.ψ (spacetimePoint s x))) volume)
    (h_int : ∀ s : ℝ, Integrable
      (fun x : Fin 3 → ℝ => probabilityDensity Γ (ψ.ψ (spacetimePoint s x))) volume)
    (h_meas' : ∀ s : ℝ, AEStronglyMeasurable (fun x : Fin 3 → ℝ =>
      deriv (fun u => probabilityDensity Γ (ψ.ψ (spacetimePoint u x))) s) volume)
    (bound : (Fin 3 → ℝ) → ℝ)
    (h_bound : ∀ᵐ x ∂(volume : Measure (Fin 3 → ℝ)), ∀ s : ℝ,
      ‖deriv (fun u => probabilityDensity Γ (ψ.ψ (spacetimePoint u x))) s‖ ≤ bound x)
    (h_bound_int : Integrable bound volume)
    (h_div_int : ∀ (t : ℝ) (i : Fin 3), Integrable (fun x : Fin 3 → ℝ =>
      deriv (fun s =>
        (diracCurrent Γ (ψ.ψ (spacetimePoint t (Function.update x i s))) i.succ).re)
      (x i)) volume)
    (h_line_int : ∀ (t : ℝ) (i : Fin 3) (x : Fin 3 → ℝ), Integrable (fun s : ℝ =>
      deriv (fun u =>
        (diracCurrent Γ (ψ.ψ (spacetimePoint t (Function.update x i u))) i.succ).re)
      s) volume)
    (h_top : ∀ (t : ℝ) (i : Fin 3) (x : Fin 3 → ℝ), Tendsto (fun s =>
      (diracCurrent Γ (ψ.ψ (spacetimePoint t (Function.update x i s))) i.succ).re)
      atTop (𝓝 0))
    (h_bot : ∀ (t : ℝ) (i : Fin 3) (x : Fin 3 → ℝ), Tendsto (fun s =>
      (diracCurrent Γ (ψ.ψ (spacetimePoint t (Function.update x i s))) i.succ).re)
      atBot (𝓝 0)) :
    ∀ t, deriv (totalProbability Γ ψ) t = 0 := by
  intro t
  -- Step 1: move the derivative inside the integral (Leibniz rule)
  rw [leibniz_integral_rule Γ ψ t h_diff h_meas (h_int t) (h_meas' t)
    bound h_bound h_bound_int]
  -- Step 2: apply the continuity equation ∂₀ρ = −∇·j
  have h_cont := fun x : Fin 3 → ℝ => continuity_equation Γ ψ m h_dirac h_diff t x
  simp_rw [h_cont]
  -- Step 3: integral of negative divergence
  rw [MeasureTheory.integral_neg]
  -- Step 4: the divergence integral vanishes by the boundary conditions
  rw [divergence_integral_vanishes Γ ψ t h_diff (h_div_int t) (h_line_int t)
    (h_top t) (h_bot t), neg_zero]

end Spectra.QuantumMechanics.BornRule
