/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Equation.Eigenfunctions

/-!
# Reduced Radial Quantization

The transform `χ = r · ψ`, the Kummer/Frobenius negative-energy core, and the
classical radial quantization theorem.

## Main definitions

* `kummerRadial` — the regular Kummer-model reduced radial solution.

## Main statements

* `reduced_ode` — the radial equation transformed to the reduced Schrödinger form.
* `kummerRadial_solves` — the regular Kummer solution `φ` solves the reduced radial equation.
* `reduced_radial_L2_quantized` — negative-energy reduced `L²` solutions are quantized.
* `reduced_eigenfunction_solves` — the known eigenfunction `r·R_{mℓ}` satisfies the reduced
  equation (consistency witness for the analytic core).
* `radial_quantization` — classical radial bound states occur exactly at `E_n`.

## References

* [Schrödinger, *Quantisierung als Eigenwertproblem I*][schrodinger1926]
* [Griffiths, *Introduction to Quantum Mechanics*][griffiths2018], §4.2.
-/

open MeasureTheory Complex Filter Real
open scoped Topology NNReal ENNReal Nat
open Spectra.QuantumMechanics.Hydrogen.Radial
open Spectra.Kummer

namespace QuantumMechanics.Hydrogen.RadialEq

/-! ## Reduced-equation transform and the analytic quantization core

The quantization argument is cleanest for the *reduced* wavefunction `χ = r·ψ`,
which obeys a Schrödinger-form equation with no first-derivative term:
`χ''(r) = (ℓ(ℓ+1)/r² − 2/r − 2E)·χ(r)`.
The lemmas below carry out the (fully mechanical) transform `ψ ↦ χ`, the
`κ = √(−2E)` algebra, and the `κ ↔ Eₙ` dictionary. The analytic core — that
square-integrability quantizes the decay rate — is `reduced_radial_L2_quantized`
(and its `E ≥ 0` companion `reduced_radial_continuum`), both **proved sorry-free and
axiom-clean** via the confluent-hypergeometric (`₁F₁`/Kummer) machinery of
`Spectra.Kummer`: the regular-at-`0` Kummer solution grows like `r^{ℓ+1}` at infinity
unless its parameter terminates (`kummerRadial_growth`), and a Wronskian /
reduction-of-order estimate plus Grönwall uniqueness pin every regular `L²` solution to
it (see their docstrings). There is no remaining analytic gap in the radial problem. -/

/-- First derivative of `χ = r·ψ`, valid at every `r`. -/
lemma hasDerivAt_reducedMul (ψ : ℝ → ℝ) {r : ℝ}
    (hψ : HasDerivAt ψ (deriv ψ r) r) :
    HasDerivAt (fun s => s * ψ s) (ψ r + r * deriv ψ r) r := by
  have h : HasDerivAt (fun s => s * ψ s) (1 * ψ r + r * deriv ψ r) r :=
    (hasDerivAt_id' (x := r)).mul hψ
  rwa [one_mul] at h

/-- Closed form of `deriv (r·ψ)` where `ψ` is differentiable at `r`. -/
lemma deriv_reducedMul (ψ : ℝ → ℝ) {r : ℝ}
    (hψ : HasDerivAt ψ (deriv ψ r) r) :
    deriv (fun s => s * ψ s) r = ψ r + r * deriv ψ r :=
  (hasDerivAt_reducedMul ψ hψ).deriv

/-- On `(0,∞)` the derivative of `χ = r·ψ` agrees with the explicit closed form. -/
private lemma deriv_reducedMul_eventuallyEq (ψ : ℝ → ℝ)
    (hψ1 : ∀ r, 0 < r → HasDerivAt ψ (deriv ψ r) r) {r : ℝ} (hr : 0 < r) :
    deriv (fun s => s * ψ s) =ᶠ[nhds r] (fun s => ψ s + s * deriv ψ s) := by
  have hmem : Set.Ioi (0 : ℝ) ∈ nhds r := isOpen_Ioi.mem_nhds hr
  filter_upwards [hmem] with x hx
  exact deriv_reducedMul ψ (hψ1 x hx)

/-- Second derivative of `χ = r·ψ` exists at `r>0`. -/
lemma hasDerivAt_deriv_reducedMul (ψ : ℝ → ℝ)
    (hψ1 : ∀ r, 0 < r → HasDerivAt ψ (deriv ψ r) r)
    (hψ2 : ∀ r, 0 < r → HasDerivAt (deriv ψ) (deriv^[2] ψ r) r)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (deriv (fun s => s * ψ s))
      (2 * deriv ψ r + r * deriv^[2] ψ r) r := by
  have hbase : HasDerivAt (fun s => ψ s + s * deriv ψ s)
      (deriv ψ r + (deriv ψ r + r * deriv^[2] ψ r)) r := by
    have h1 : HasDerivAt ψ (deriv ψ r) r := hψ1 r hr
    have h2 : HasDerivAt (fun s => s * deriv ψ s) (deriv ψ r + r * deriv^[2] ψ r) r := by
      have h2' : HasDerivAt (fun s => s * deriv ψ s) (1 * deriv ψ r + r * deriv^[2] ψ r) r :=
        (hasDerivAt_id' (x := r)).mul (hψ2 r hr)
      rwa [one_mul] at h2'
    exact h1.add h2
  have hee := deriv_reducedMul_eventuallyEq ψ hψ1 hr
  have : HasDerivAt (deriv (fun s => s * ψ s))
      (deriv ψ r + (deriv ψ r + r * deriv^[2] ψ r)) r :=
    hbase.congr_of_eventuallyEq hee
  convert this using 1
  ring

/-- Closed form of `deriv^[2] (r·ψ)` at `r>0`. -/
lemma deriv2_reducedMul (ψ : ℝ → ℝ)
    (hψ1 : ∀ r, 0 < r → HasDerivAt ψ (deriv ψ r) r)
    (hψ2 : ∀ r, 0 < r → HasDerivAt (deriv ψ) (deriv^[2] ψ r) r)
    {r : ℝ} (hr : 0 < r) :
    deriv^[2] (fun s => s * ψ s) r = 2 * deriv ψ r + r * deriv^[2] ψ r := by
  change deriv (deriv (fun s => s * ψ s)) r = _
  exact (hasDerivAt_deriv_reducedMul ψ hψ1 hψ2 hr).deriv

/-- **The reduced radial equation.** If `ψ` is a `C²` classical solution of
    `H_ℓ ψ = E ψ` on `(0,∞)`, then `χ = r·ψ` solves the first-derivative-free form
    `χ''(r) = (ℓ(ℓ+1)/r² − 2/r − 2E)·χ(r)`. -/
lemma reduced_ode (ℓ : ℕ) (E : ℝ) (ψ : ℝ → ℝ)
    (hψ1 : ∀ r, 0 < r → HasDerivAt ψ (deriv ψ r) r)
    (hψ2 : ∀ r, 0 < r → HasDerivAt (deriv ψ) (deriv^[2] ψ r) r)
    (heq : ∀ r, 0 < r → radialHamiltonian ℓ ψ r = E * ψ r)
    {r : ℝ} (hr : 0 < r) :
    deriv^[2] (fun s => s * ψ s) r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r - 2 * E) * (r * ψ r) := by
  have hrne : r ≠ 0 := ne_of_gt hr
  rw [deriv2_reducedMul ψ hψ1 hψ2 hr]
  have he := heq r hr
  simp only [radialHamiltonian] at he
  have hX : deriv^[2] ψ r =
      -2 * (E * ψ r + (1 / r) * deriv ψ r
        - ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / (2 * r ^ 2)) * ψ r + (1 / r) * ψ r) := by
    linear_combination -2 * he
  rw [hX]
  field_simp
  ring

/-- `RadialL2 ψ` says exactly that the reduced wavefunction `χ = r·ψ` is in
    `L²((0,∞), dr)`. -/
lemma reduced_integrableOn_sq (ψ : ℝ → ℝ) (h : RadialL2 ψ) :
    IntegrableOn (fun r => (r * ψ r) ^ 2) (Set.Ioi 0) := by
  unfold RadialL2 at h
  exact h.congr_fun (fun x _ => by ring) measurableSet_Ioi

/-- Nondegeneracy transfers: a point `r>0` with `ψ ≠ 0` gives one with `χ = r·ψ ≠ 0`. -/
private lemma reduced_nonzero (ψ : ℝ → ℝ) (h : ∃ r, 0 < r ∧ ψ r ≠ 0) :
    ∃ r, 0 < r ∧ r * ψ r ≠ 0 := by
  obtain ⟨r, hr, hψ⟩ := h
  exact ⟨r, hr, mul_ne_zero (ne_of_gt hr) hψ⟩

/-- For `E < 0`, the decay rate `κ = √(−2E)` is positive with `κ² = −2E`. -/
private lemma kappa_pos_sq (E : ℝ) (hE : E < 0) :
    0 < Real.sqrt (-2 * E) ∧ Real.sqrt (-2 * E) ^ 2 = -2 * E := by
  have hpos : 0 < -2 * E := by linarith
  exact ⟨Real.sqrt_pos.mpr hpos, Real.sq_sqrt (le_of_lt hpos)⟩

/-- The `κ ↔ Eₙ` dictionary: `κ = 1/m` together with `κ² = −2E` forces `E = Eₘ`. -/
private lemma energy_eq_of_kappa (E κ : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hκ2 : κ ^ 2 = -2 * E) (hκm : κ = 1 / (m : ℝ)) :
    E = hydrogenEigenvalue m hm := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hkey : (1 : ℝ) / (m : ℝ) ^ 2 = -2 * E := by
    rw [← hκ2, hκm, div_pow, one_pow]
  unfold hydrogenEigenvalue
  field_simp at hkey ⊢
  linarith

/-! ### The Frobenius/Kummer ansatz `χ = r^{ℓ+1} e^{-κr} w`

The reduced equation is solved by separating the boundary behaviour: a regular
solution has the form `χ = r^{ℓ+1} e^{-κr} w` with `w` analytic. The lemmas below
prove (purely mechanically) that this ansatz solves the reduced radial equation
*iff* `w` solves the confluent (Laguerre/Kummer) ODE. This is the substitution at
the heart of the quantization argument; the remaining ingredient — the *asymptotics*
of the Kummer solution `w` (termination ⇔ `L²`) — is supplied downstream and
assembled into the (sorry-free) `reduced_radial_L2_quantized`. -/

/-- First derivative of the ansatz `χ = r^{ℓ+1} e^{-κr} w`. -/
private lemma deriv_ansatz (ℓ : ℕ) (κ : ℝ) (w : ℝ → ℝ) {r : ℝ}
    (hw : HasDerivAt w (deriv w r) r) :
    deriv (fun s => s ^ (ℓ + 1) * Real.exp (-κ * s) * w s) r
      = ((ℓ : ℝ) + 1) * r ^ ℓ * Real.exp (-κ * r) * w r
        - κ * r ^ (ℓ + 1) * Real.exp (-κ * r) * w r
        + r ^ (ℓ + 1) * Real.exp (-κ * r) * deriv w r := by
  have hpow : HasDerivAt (fun s : ℝ => s ^ (ℓ + 1)) (((ℓ : ℝ) + 1) * r ^ ℓ) r := by
    simpa using hasDerivAt_pow (ℓ + 1) r
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-κ * s)) (Real.exp (-κ * r) * (-κ)) r := by
    have hin : HasDerivAt (fun s : ℝ => -κ * s) (-κ) r := by
      simpa using (hasDerivAt_id r).const_mul (-κ)
    simpa using hin.exp
  have key : HasDerivAt (fun s => s ^ (ℓ + 1) * Real.exp (-κ * s) * w s) _ r :=
    (hpow.mul hexp).mul hw
  rw [key.deriv]
  simp only [Pi.mul_apply]
  ring

/-- Second derivative of the ansatz `χ = r^{ℓ+1} e^{-κr} w` (raw expanded form). -/
private lemma deriv2_ansatz (ℓ : ℕ) (κ : ℝ) (w : ℝ → ℝ)
    (hw1 : ∀ s, 0 < s → HasDerivAt w (deriv w s) s)
    (hw2 : ∀ s, 0 < s → HasDerivAt (deriv w) (deriv^[2] w s) s)
    {r : ℝ} (hr : 0 < r) :
    deriv^[2] (fun s => s ^ (ℓ + 1) * Real.exp (-κ * s) * w s) r
      = Real.exp (-κ * r) * (
          (ℓ : ℝ) * ((ℓ : ℝ) + 1) * r ^ (ℓ - 1) * w r
          - 2 * κ * ((ℓ : ℝ) + 1) * r ^ ℓ * w r
          + 2 * ((ℓ : ℝ) + 1) * r ^ ℓ * deriv w r
          + κ ^ 2 * r ^ (ℓ + 1) * w r
          - 2 * κ * r ^ (ℓ + 1) * deriv w r
          + r ^ (ℓ + 1) * deriv^[2] w r) := by
  have hD1eq : deriv (fun s => s ^ (ℓ + 1) * Real.exp (-κ * s) * w s) =ᶠ[nhds r]
      (fun x => ((ℓ : ℝ) + 1) * x ^ ℓ * Real.exp (-κ * x) * w x
        - κ * x ^ (ℓ + 1) * Real.exp (-κ * x) * w x
        + x ^ (ℓ + 1) * Real.exp (-κ * x) * deriv w x) := by
    have hmem : Set.Ioi (0 : ℝ) ∈ nhds r := isOpen_Ioi.mem_nhds hr
    filter_upwards [hmem] with x hx
    exact deriv_ansatz ℓ κ w (hw1 x hx)
  have hpowℓ : HasDerivAt (fun s : ℝ => s ^ ℓ) ((ℓ : ℝ) * r ^ (ℓ - 1)) r := by
    simpa using hasDerivAt_pow ℓ r
  have hpowℓ1 : HasDerivAt (fun s : ℝ => s ^ (ℓ + 1)) (((ℓ : ℝ) + 1) * r ^ ℓ) r := by
    simpa using hasDerivAt_pow (ℓ + 1) r
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-κ * s)) (Real.exp (-κ * r) * (-κ)) r := by
    have hin : HasDerivAt (fun s : ℝ => -κ * s) (-κ) r := by
      simpa using (hasDerivAt_id r).const_mul (-κ)
    simpa using hin.exp
  have hw := hw1 r hr
  have hw2' := hw2 r hr
  have hD1 : HasDerivAt
      (fun x => ((ℓ : ℝ) + 1) * x ^ ℓ * Real.exp (-κ * x) * w x
        - κ * x ^ (ℓ + 1) * Real.exp (-κ * x) * w x
        + x ^ (ℓ + 1) * Real.exp (-κ * x) * deriv w x) _ r :=
    ((((hpowℓ.const_mul ((ℓ : ℝ) + 1)).mul hexp).mul hw).sub
      (((hpowℓ1.const_mul κ).mul hexp).mul hw)).add
      ((hpowℓ1.mul hexp).mul hw2')
  change deriv (deriv (fun s => s ^ (ℓ + 1) * Real.exp (-κ * s) * w s)) r = _
  rw [hD1eq.deriv_eq, hD1.deriv]
  simp only [Pi.mul_apply]
  ring

/-- **The Laguerre/Kummer residual identity.** For the ansatz `χ = r^{ℓ+1} e^{-κr} w`,
    the reduced-equation residual factors through the Laguerre/Kummer operator on `w`:
    `χ''(r) − (ℓ(ℓ+1)/r² − 2/r + κ²)·χ(r)`
      `= e^{-κr} r^ℓ · (r·w'' + (2ℓ+2 − 2κr)·w' + (2 − 2(ℓ+1)κ)·w)`.
    Since `e^{-κr} r^ℓ ≠ 0` for `r > 0`, the ansatz solves the reduced radial
    equation iff `w` solves the confluent (Laguerre) ODE
    `ρ v'' + (2ℓ+2 − ρ) v' + (1/κ − ℓ − 1) v = 0` (in the variable `ρ = 2κr`). -/
lemma laguerre_ansatz_residual (ℓ : ℕ) (κ : ℝ) (w : ℝ → ℝ)
    (hw1 : ∀ s, 0 < s → HasDerivAt w (deriv w s) s)
    (hw2 : ∀ s, 0 < s → HasDerivAt (deriv w) (deriv^[2] w s) s)
    {r : ℝ} (hr : 0 < r) :
    deriv^[2] (fun s => s ^ (ℓ + 1) * Real.exp (-κ * s) * w s) r
      - ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + κ ^ 2)
        * (r ^ (ℓ + 1) * Real.exp (-κ * r) * w r)
      = Real.exp (-κ * r) * r ^ ℓ
        * (r * deriv^[2] w r + (2 * (ℓ : ℝ) + 2 - 2 * κ * r) * deriv w r
           + (2 - 2 * ((ℓ : ℝ) + 1) * κ) * w r) := by
  have hrne : r ≠ 0 := ne_of_gt hr
  rw [deriv2_ansatz ℓ κ w hw1 hw2 hr]
  rcases lt_or_ge ℓ 2 with hℓ | hℓ
  · interval_cases ℓ <;> · field_simp; ring
  · obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 2 := ⟨ℓ - 2, by omega⟩
    rw [show k + 2 - 1 = k + 1 from rfl]
    field_simp
    push_cast
    ring

/-- **The Kummer bridge.** The ansatz `χ = r^{ℓ+1} e^{-κr} w` solves the reduced
    radial equation `χ'' = (ℓ(ℓ+1)/r² − 2/r + κ²)·χ` at `r > 0` *iff* `w` solves
    the confluent (Laguerre) ODE there, written in the variable `r`:
    `r·w'' + (2ℓ+2 − 2κr)·w' + (2 − 2(ℓ+1)κ)·w = 0`. This is the exact substitution
    underlying `reduced_radial_L2_quantized`; the *asymptotics* of `w` are then handled
    downstream (both are proved sorry-free). -/
lemma laguerre_ansatz_reduced_iff (ℓ : ℕ) (κ : ℝ) (w : ℝ → ℝ)
    (hw1 : ∀ s, 0 < s → HasDerivAt w (deriv w s) s)
    (hw2 : ∀ s, 0 < s → HasDerivAt (deriv w) (deriv^[2] w s) s)
    {r : ℝ} (hr : 0 < r) :
    deriv^[2] (fun s => s ^ (ℓ + 1) * Real.exp (-κ * s) * w s) r
        = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + κ ^ 2)
          * (r ^ (ℓ + 1) * Real.exp (-κ * r) * w r)
      ↔ r * deriv^[2] w r + (2 * (ℓ : ℝ) + 2 - 2 * κ * r) * deriv w r
          + (2 - 2 * ((ℓ : ℝ) + 1) * κ) * w r = 0 := by
  have hfac : Real.exp (-κ * r) * r ^ ℓ ≠ 0 := by positivity
  rw [← sub_eq_zero (a := deriv^[2] (fun s => s ^ (ℓ + 1) * Real.exp (-κ * s) * w s) r),
    laguerre_ansatz_residual ℓ κ w hw1 hw2 hr, mul_eq_zero]
  exact or_iff_right hfac

/-- **Non-`L²` from a positive lower bound at infinity.** If `|χ(r)| ≥ A > 0` for all large `r`,
    then `χ` is not square-integrable on `(0,∞)`: `χ(r)² ≥ A² > 0` on the infinite-measure set
    `(max R 1, ∞)`. This is the mechanism by which exponential growth of the Kummer factor
    (`Spectra.Kummer.kummerM_abs_exp_lower`) breaks normalisability of a
    non-terminating solution. -/
lemma not_radialL2_of_eventually_ge (χ : ℝ → ℝ) {A R : ℝ} (hA : 0 < A)
    (hlb : ∀ r, R ≤ r → A ≤ |χ r|) :
    ¬ IntegrableOn (fun r => χ r ^ 2) (Set.Ioi 0) := by
  intro hint
  have hc0 : (0 : ℝ) < max R 1 := lt_of_lt_of_le one_pos (le_max_right R 1)
  have hint2 : IntegrableOn (fun r => χ r ^ 2) (Set.Ioi (max R 1)) :=
    hint.mono_set (Set.Ioi_subset_Ioi (le_of_lt hc0))
  have hbound : ∀ r ∈ Set.Ioi (max R 1), A ^ 2 ≤ χ r ^ 2 := by
    intro r hr
    rw [Set.mem_Ioi] at hr
    have hrR : R ≤ r := le_of_lt (lt_of_le_of_lt (le_max_left R 1) hr)
    nlinarith [hlb r hrR, hA, abs_nonneg (χ r), sq_abs (χ r)]
  have hconst : IntegrableOn (fun _ : ℝ => A ^ 2) (Set.Ioi (max R 1)) :=
    hint2.mono' aestronglyMeasurable_const
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hbound r hr))
  rw [integrableOn_const_iff] at hconst
  rcases hconst with h | h
  · rw [enorm_eq_zero] at h; nlinarith [hA, h]
  · rw [Real.volume_Ioi] at h; exact absurd h (lt_irrefl _)

/-! ### The explicit regular solution `φ = r^{ℓ+1} e^{−κr} M(a, 2ℓ+2, 2κr)`

The analytic core of `reduced_radial_L2_quantized`: the confluent-hypergeometric
(Kummer) machinery of `Spectra.Kummer` is assembled into the regular solution `φ`
of the reduced radial equation, whose growth at `∞` (unless the series terminates)
breaks square-integrability. -/

/-- The regular-at-`0` solution `φ(r) = r^{ℓ+1} e^{−κr} M(ℓ+1−1/κ, 2ℓ+2, 2κr)` of the reduced
radial equation. -/
noncomputable def kummerRadial (ℓ : ℕ) (κ : ℝ) : ℝ → ℝ :=
  fun r => r ^ (ℓ + 1) * Real.exp (-κ * r) *
    kummerM ((ℓ : ℝ) + 1 - 1 / κ) (2 * (ℓ : ℝ) + 2) (2 * κ * r)

/-! ### Chain-rule derivatives of `w(s) = M(a,b,2κs)` -/

/-- Chain rule for `w(s) = M(a,b,2κs)`: `w' r = 2κ · M'(a,b,2κr)`. -/
private lemma kummerComp_hasDerivAt (a b κ : ℝ) (hb : 0 < b) (r : ℝ) :
    HasDerivAt (fun s => kummerM a b (2 * κ * s)) (2 * κ * deriv (kummerM a b) (2 * κ * r)) r := by
  have h1 : HasDerivAt (kummerM a b) (deriv (kummerM a b) (2 * κ * r)) (2 * κ * r) :=
    (kummerM_hasDerivAt a b hb (2 * κ * r)).differentiableAt.hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => 2 * κ * s) (2 * κ) r := by
    simpa using (hasDerivAt_id r).const_mul (2 * κ)
  have hc : HasDerivAt (fun s => kummerM a b (2 * κ * s))
      (deriv (kummerM a b) (2 * κ * r) * (2 * κ)) r := h1.comp r h2
  convert hc using 1
  ring

/-- Closed form of `deriv (w)` for `w(s) = M(a,b,2κs)`. -/
private lemma kummerComp_deriv (a b κ : ℝ) (hb : 0 < b) (r : ℝ) :
    deriv (fun s => kummerM a b (2 * κ * s)) r = 2 * κ * deriv (kummerM a b) (2 * κ * r) :=
  (kummerComp_hasDerivAt a b κ hb r).deriv

/-- Second-derivative chain rule for `w(s) = M(a,b,2κs)`:
`(w)'' r = 4κ² · M''(a,b,2κr)`. -/
private lemma kummerComp_hasDerivAt2 (a b κ : ℝ) (hb : 0 < b) (r : ℝ) :
    HasDerivAt (deriv (fun s => kummerM a b (2 * κ * s)))
      (4 * κ ^ 2 * deriv (deriv (kummerM a b)) (2 * κ * r)) r := by
  have hfun : deriv (fun s => kummerM a b (2 * κ * s))
      = fun s => 2 * κ * deriv (kummerM a b) (2 * κ * s) :=
    funext (fun s => kummerComp_deriv a b κ hb s)
  rw [hfun]
  have h1 : HasDerivAt (deriv (kummerM a b))
      (deriv (deriv (kummerM a b)) (2 * κ * r)) (2 * κ * r) :=
    (kummerM_hasDerivAt2 a b hb (2 * κ * r)).differentiableAt.hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => 2 * κ * s) (2 * κ) r := by
    simpa using (hasDerivAt_id r).const_mul (2 * κ)
  have hc : HasDerivAt (fun s => 2 * κ * deriv (kummerM a b) (2 * κ * s))
      (2 * κ * (deriv (deriv (kummerM a b)) (2 * κ * r) * (2 * κ))) r :=
    (h1.comp r h2).const_mul (2 * κ)
  convert hc using 1
  ring

/-- Closed form of `deriv^[2] (w)` for `w(s) = M(a,b,2κs)`. -/
private lemma kummerComp_deriv2 (a b κ : ℝ) (hb : 0 < b) (r : ℝ) :
    deriv^[2] (fun s => kummerM a b (2 * κ * s)) r
      = 4 * κ ^ 2 * deriv (deriv (kummerM a b)) (2 * κ * r) := by
  change deriv (deriv (fun s => kummerM a b (2 * κ * s))) r = _
  exact (kummerComp_hasDerivAt2 a b κ hb r).deriv

/-! ### Part A: `φ` solves the reduced radial ODE -/

/-- **The regular Kummer solution solves the reduced radial equation.** For `κ > 0` and `r > 0`,
    `φ = kummerRadial ℓ κ` satisfies `φ''(r) = (ℓ(ℓ+1)/r² − 2/r + κ²)·φ(r)`. Proved by feeding the
    Kummer ODE (`Spectra.Kummer.kummerM_ode`) through the ansatz bridge
    `laguerre_ansatz_reduced_iff`. -/
theorem kummerRadial_solves (ℓ : ℕ) (κ : ℝ) (hκ : 0 < κ) {r : ℝ} (hr : 0 < r) :
    deriv^[2] (kummerRadial ℓ κ) r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + κ ^ 2) * kummerRadial ℓ κ r := by
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  set a := (ℓ : ℝ) + 1 - 1 / κ with ha_def
  set b := 2 * (ℓ : ℝ) + 2 with hb_def
  have hb : 0 < b := by rw [hb_def]; positivity
  set w := fun s => kummerM a b (2 * κ * s) with hw_def
  have hw1 : ∀ s, 0 < s → HasDerivAt w (deriv w s) s := by
    intro s _
    rw [hw_def, kummerComp_deriv a b κ hb s]
    exact kummerComp_hasDerivAt a b κ hb s
  have hw2 : ∀ s, 0 < s → HasDerivAt (deriv w) (deriv^[2] w s) s := by
    intro s _
    rw [hw_def, kummerComp_deriv2 a b κ hb s]
    exact kummerComp_hasDerivAt2 a b κ hb s
  have hφ : kummerRadial ℓ κ = fun s => s ^ (ℓ + 1) * Real.exp (-κ * s) * w s := by
    funext s; rw [kummerRadial, hw_def]
  rw [hφ]
  rw [laguerre_ansatz_reduced_iff ℓ κ w hw1 hw2 hr]
  rw [hw_def, kummerComp_deriv2 a b κ hb r, kummerComp_deriv a b κ hb r]
  have hdict : (2 : ℝ) - 2 * ((ℓ : ℝ) + 1) * κ = -2 * κ * a := by
    rw [ha_def]; field_simp; ring
  rw [hdict]
  linear_combination (2 * κ) * kummerM_ode a b hb (2 * κ * r)

/-! ### Differentiability / continuity of `M` and `φ` -/

/-- `M(a,b,·)` is differentiable (for `b > 0`). -/
private lemma kummerM_differentiable (a b : ℝ) (hb : 0 < b) : Differentiable ℝ (kummerM a b) :=
  fun z => (kummerM_hasDerivAt a b hb z).differentiableAt

/-- `M'(a,b,·)` is differentiable (for `b > 0`). -/
private lemma kummerM_deriv_differentiable (a b : ℝ) (hb : 0 < b) :
    Differentiable ℝ (deriv (kummerM a b)) :=
  fun z => (kummerM_hasDerivAt2 a b hb z).differentiableAt

/-- `M(a,b,·)` is continuous (for `b > 0`). -/
private lemma kummerM_continuous (a b : ℝ) (hb : 0 < b) : Continuous (kummerM a b) :=
  (kummerM_differentiable a b hb).continuous

/-- Definitional unfolding of `kummerRadial ℓ κ`. -/
private lemma kummerRadial_eq (ℓ : ℕ) (κ : ℝ) :
    kummerRadial ℓ κ = fun r => r ^ (ℓ + 1) * Real.exp (-κ * r) *
      kummerM ((ℓ : ℝ) + 1 - 1 / κ) (2 * (ℓ : ℝ) + 2) (2 * κ * r) := rfl

/-- `φ(r)` written as `r^{ℓ+1}` times the `e^{−κr} · M(…)` factor. -/
private lemma kummerRadial_factor (ℓ : ℕ) (κ : ℝ) (r : ℝ) :
    kummerRadial ℓ κ r = r ^ (ℓ + 1) *
      (Real.exp (-κ * r) * kummerM ((ℓ : ℝ) + 1 - 1 / κ) (2 * (ℓ : ℝ) + 2) (2 * κ * r)) := by
  rw [kummerRadial]; ring

/-- `φ = kummerRadial ℓ κ` is differentiable on `ℝ`. -/
private lemma kummerRadial_differentiable (ℓ : ℕ) (κ : ℝ) :
    Differentiable ℝ (kummerRadial ℓ κ) := by
  set a := (ℓ : ℝ) + 1 - 1 / κ
  set b := 2 * (ℓ : ℝ) + 2 with hb_def
  have hb : 0 < b := by rw [hb_def]; positivity
  rw [kummerRadial_eq]
  have hM : Differentiable ℝ (fun r : ℝ => kummerM a b (2 * κ * r)) :=
    (kummerM_differentiable a b hb).comp (by fun_prop)
  exact (((differentiable_id.pow (ℓ + 1)).mul (Real.differentiable_exp.comp (by fun_prop))).mul hM)

/-- `φ = kummerRadial ℓ κ` is continuous on `ℝ`. -/
private lemma kummerRadial_continuous (ℓ : ℕ) (κ : ℝ) : Continuous (kummerRadial ℓ κ) :=
  (kummerRadial_differentiable ℓ κ).continuous

/-- Closed form of `deriv φ`. -/
private lemma kummerRadial_deriv_eq (ℓ : ℕ) (κ : ℝ) :
    deriv (kummerRadial ℓ κ) = fun r =>
      ((ℓ : ℝ) + 1) * r ^ ℓ * Real.exp (-κ * r) *
          kummerM ((ℓ : ℝ) + 1 - 1 / κ) (2 * (ℓ : ℝ) + 2) (2 * κ * r)
      + r ^ (ℓ + 1) * (Real.exp (-κ * r) * (-κ)) *
          kummerM ((ℓ : ℝ) + 1 - 1 / κ) (2 * (ℓ : ℝ) + 2) (2 * κ * r)
      + r ^ (ℓ + 1) * Real.exp (-κ * r) *
          (2 * κ * deriv (kummerM ((ℓ : ℝ) + 1 - 1 / κ) (2 * (ℓ : ℝ) + 2)) (2 * κ * r)) := by
  have hb : (0 : ℝ) < 2 * (ℓ : ℝ) + 2 := by positivity
  funext r
  have hp : HasDerivAt (fun s : ℝ => s ^ (ℓ + 1)) (((ℓ : ℝ) + 1) * r ^ ℓ) r := by
    simpa using hasDerivAt_pow (ℓ + 1) r
  have he : HasDerivAt (fun s : ℝ => Real.exp (-κ * s)) (Real.exp (-κ * r) * (-κ)) r := by
    have hin : HasDerivAt (fun s : ℝ => -κ * s) (-κ) r := by
      simpa using (hasDerivAt_id r).const_mul (-κ)
    simpa using hin.exp
  have hwc : HasDerivAt
      (fun s => kummerM ((ℓ : ℝ) + 1 - 1 / κ) (2 * (ℓ : ℝ) + 2) (2 * κ * s))
      (2 * κ * deriv (kummerM ((ℓ : ℝ) + 1 - 1 / κ) (2 * (ℓ : ℝ) + 2)) (2 * κ * r)) r :=
    kummerComp_hasDerivAt ((ℓ : ℝ) + 1 - 1 / κ) (2 * (ℓ : ℝ) + 2) κ hb r
  have hF : HasDerivAt (fun s => s ^ (ℓ + 1) * Real.exp (-κ * s) *
      kummerM ((ℓ : ℝ) + 1 - 1 / κ) (2 * (ℓ : ℝ) + 2) (2 * κ * s)) _ r :=
    (hp.mul he).mul hwc
  rw [kummerRadial_eq, hF.deriv]
  simp only [Pi.mul_apply]
  ring

/-- `deriv φ` is itself differentiable on `ℝ` (so `φ` is `C²`). -/
private lemma kummerRadial_deriv_differentiable (ℓ : ℕ) (κ : ℝ) :
    Differentiable ℝ (deriv (kummerRadial ℓ κ)) := by
  set a := (ℓ : ℝ) + 1 - 1 / κ
  set b := 2 * (ℓ : ℝ) + 2 with hb_def
  have hb : 0 < b := by rw [hb_def]; positivity
  rw [kummerRadial_deriv_eq]
  have hM : Differentiable ℝ (fun r : ℝ => kummerM a b (2 * κ * r)) :=
    (kummerM_differentiable a b hb).comp (by fun_prop)
  have hM' : Differentiable ℝ (fun r : ℝ => deriv (kummerM a b) (2 * κ * r)) :=
    (kummerM_deriv_differentiable a b hb).comp (by fun_prop)
  fun_prop

/-! ### Part B: behaviour of `φ` near `0` and at `∞` -/

/-- `φ(0) = 0` (the regular solution vanishes at the origin). -/
private lemma kummerRadial_zero (ℓ : ℕ) (κ : ℝ) : kummerRadial ℓ κ 0 = 0 := by
  rw [kummerRadial]; simp

/-- `φ(r) → 0` as `r → 0⁺` (regularity of `φ` at the origin). -/
private lemma kummerRadial_tendsto_zero (ℓ : ℕ) (κ : ℝ) :
    Filter.Tendsto (kummerRadial ℓ κ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h := ((kummerRadial_continuous ℓ κ).tendsto 0)
  rw [kummerRadial_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- `1/2 r^{ℓ+1} ≤ φ(r) ≤ 2 r^{ℓ+1}` and `φ(r) > 0` for small `r > 0`. -/
private lemma kummerRadial_near_zero (ℓ : ℕ) (κ : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r, 0 < r → r < δ →
      (1 / 2) * r ^ (ℓ + 1) ≤ kummerRadial ℓ κ r ∧
      kummerRadial ℓ κ r ≤ 2 * r ^ (ℓ + 1) ∧ 0 < kummerRadial ℓ κ r := by
  set a := (ℓ : ℝ) + 1 - 1 / κ
  set b := 2 * (ℓ : ℝ) + 2 with hb_def
  have hb : 0 < b := by rw [hb_def]; positivity
  have ht : Filter.Tendsto (fun r => Real.exp (-κ * r) * kummerM a b (2 * κ * r)) (nhds 0)
      (nhds 1) := by
    have hc : Continuous (fun r => Real.exp (-κ * r) * kummerM a b (2 * κ * r)) :=
      (Real.continuous_exp.comp (by fun_prop)).mul ((kummerM_continuous a b hb).comp (by fun_prop))
    have := hc.tendsto 0
    simpa using this
  have key : ∀ᶠ r in nhds (0 : ℝ),
      1 / 2 < Real.exp (-κ * r) * kummerM a b (2 * κ * r) ∧
      Real.exp (-κ * r) * kummerM a b (2 * κ * r) < 2 := by
    filter_upwards [ht.eventually (Ioo_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1)
      (by norm_num : (1 : ℝ) < 2))] with r hr using ⟨hr.1, hr.2⟩
  rw [Metric.eventually_nhds_iff] at key
  obtain ⟨δ, hδ, hball⟩ := key
  refine ⟨δ, hδ, fun r hr hrδ => ?_⟩
  have hmem : dist r 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos hr]; exact hrδ
  obtain ⟨hlo, hhi⟩ := hball hmem
  have hpow : 0 < r ^ (ℓ + 1) := by positivity
  have hfac := kummerRadial_factor ℓ κ r
  rw [show ((ℓ : ℝ) + 1 - 1 / κ) = a from rfl, show (2 * (ℓ : ℝ) + 2) = b from rfl] at hfac
  refine ⟨?_, ?_, ?_⟩
  · rw [hfac]; nlinarith [hlo, hpow]
  · rw [hfac]; nlinarith [hhi, hpow]
  · rw [hfac]; nlinarith [hlo, hpow]

/-- `|φ(r)| ≥ C > 0` for all large `r`, when the Kummer series does not terminate. -/
private lemma kummerRadial_growth (ℓ : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (ha : ∀ p : ℕ, (ℓ : ℝ) + 1 - 1 / κ ≠ -(p : ℝ)) :
    ∃ C R : ℝ, 0 < C ∧ ∀ r, R ≤ r → C ≤ |kummerRadial ℓ κ r| := by
  set a := (ℓ : ℝ) + 1 - 1 / κ with _ha_def
  set b := 2 * (ℓ : ℝ) + 2 with hb_def
  have hb : 0 < b := by rw [hb_def]; positivity
  obtain ⟨C, R₀, hC, hlb⟩ := kummerM_abs_exp_lower a b hb ha
  refine ⟨C, max 1 (R₀ / (2 * κ)), hC, fun r hr => ?_⟩
  have hr1 : 1 ≤ r := le_trans (le_max_left _ _) hr
  have _hrpos : 0 < r := lt_of_lt_of_le one_pos hr1
  have hrR : R₀ / (2 * κ) ≤ r := le_trans (le_max_right _ _) hr
  have h2κ : 0 < 2 * κ := by positivity
  have hρ : R₀ ≤ 2 * κ * r := by
    rw [div_le_iff₀ h2κ] at hrR; linarith [hrR]
  have hMlb : C * Real.exp (2 * κ * r / 2) ≤ |kummerM a b (2 * κ * r)| := hlb _ hρ
  have hexp : Real.exp (2 * κ * r / 2) = Real.exp (κ * r) := by congr 1; ring
  rw [hexp] at hMlb
  have hfac := kummerRadial_factor ℓ κ r
  rw [show ((ℓ : ℝ) + 1 - 1 / κ) = a from rfl, show (2 * (ℓ : ℝ) + 2) = b from rfl] at hfac
  rw [hfac]
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < r ^ (ℓ + 1)),
    abs_of_pos (Real.exp_pos _)]
  have hpow1 : 1 ≤ r ^ (ℓ + 1) := one_le_pow₀ hr1
  have hexpn : 0 ≤ Real.exp (-κ * r) := (Real.exp_pos _).le
  have hkey : Real.exp (-κ * r) * (C * Real.exp (κ * r)) = C := by
    rw [show Real.exp (-κ * r) * (C * Real.exp (κ * r))
        = C * (Real.exp (-κ * r) * Real.exp (κ * r)) from by ring,
      ← Real.exp_add, show -κ * r + κ * r = 0 from by ring, Real.exp_zero, mul_one]
  have step1 : Real.exp (-κ * r) * (C * Real.exp (κ * r))
      ≤ Real.exp (-κ * r) * |kummerM a b (2 * κ * r)| :=
    mul_le_mul_of_nonneg_left hMlb hexpn
  have hMnn : 0 ≤ Real.exp (-κ * r) * |kummerM a b (2 * κ * r)| :=
    mul_nonneg hexpn (abs_nonneg _)
  calc C = Real.exp (-κ * r) * (C * Real.exp (κ * r)) := hkey.symm
    _ ≤ Real.exp (-κ * r) * |kummerM a b (2 * κ * r)| := step1
    _ ≤ r ^ (ℓ + 1) * (Real.exp (-κ * r) * |kummerM a b (2 * κ * r)|) := by
          nlinarith [hpow1, hMnn]

/-! ### Part C: the Wronskian `W = χ φ' − χ' φ` vanishes -/

/-- The Wronskian of `χ` (a solution of the reduced equation) and `φ = kummerRadial` has
zero derivative on `(0,∞)`. -/
private lemma wronskian_hasDerivAt_zero (ℓ : ℕ) (κ : ℝ) (hκ : 0 < κ) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    (hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + κ ^ 2) * χ r)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => χ s * deriv (kummerRadial ℓ κ) s - deriv χ s * kummerRadial ℓ κ s)
      0 r := by
  have hχd : HasDerivAt χ (deriv χ r) r := hχ1 r hr
  have hχd2 : HasDerivAt (deriv χ) (deriv^[2] χ r) r := hχ2 r hr
  have hφd : HasDerivAt (kummerRadial ℓ κ) (deriv (kummerRadial ℓ κ) r) r :=
    (kummerRadial_differentiable ℓ κ r).hasDerivAt
  have hφd2 : HasDerivAt (deriv (kummerRadial ℓ κ)) (deriv^[2] (kummerRadial ℓ κ) r) r :=
    (kummerRadial_deriv_differentiable ℓ κ r).hasDerivAt
  have h1 : HasDerivAt (fun s => χ s * deriv (kummerRadial ℓ κ) s)
      (deriv χ r * deriv (kummerRadial ℓ κ) r + χ r * deriv^[2] (kummerRadial ℓ κ) r) r :=
    hχd.mul hφd2
  have h2 : HasDerivAt (fun s => deriv χ s * kummerRadial ℓ κ s)
      (deriv^[2] χ r * kummerRadial ℓ κ r + deriv χ r * deriv (kummerRadial ℓ κ) r) r :=
    hχd2.mul hφd
  convert h1.sub h2 using 1
  rw [hode r hr, kummerRadial_solves ℓ κ hκ hr]
  ring

/-- The Wronskian is constant on `(0,∞)`. -/
private lemma wronskian_const (ℓ : ℕ) (κ : ℝ) (hκ : 0 < κ) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    (hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + κ ^ 2) * χ r)
    {r₀ s : ℝ} (hr₀ : 0 < r₀) (hs : 0 < s) :
    χ s * deriv (kummerRadial ℓ κ) s - deriv χ s * kummerRadial ℓ κ s
      = χ r₀ * deriv (kummerRadial ℓ κ) r₀ - deriv χ r₀ * kummerRadial ℓ κ r₀ := by
  set W : ℝ → ℝ := fun s => χ s * deriv (kummerRadial ℓ κ) s - deriv χ s * kummerRadial ℓ κ s
    with hWdef
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := W) (f' := fun _ => (0 : ℝ)) (s := Set.Ioi 0) (C := 0)
    (fun x hx => (wronskian_hasDerivAt_zero ℓ κ hκ χ hχ1 hχ2 hode hx).hasDerivWithinAt)
    (fun x _ => by simp) (convex_Ioi 0) hr₀ (Set.mem_Ioi.2 hs)
  simpa [hWdef, sub_eq_zero] using hb

/-- **Reduction-of-order lower bound.** `φ(r)·∫_r^d ds/φ(s)² ≥ 1/(8·2^{2ℓ+2})` for small `r`,
using only that `(1/2)r^{ℓ+1} ≤ φ ≤ 2 r^{ℓ+1}` near `0`. The integral is bounded below by its
restriction to `[r,2r]` (length × minimum), avoiding any explicit power integral. -/
private lemma reduction_order_lower (ℓ : ℕ) (κ : ℝ) {d : ℝ}
    (hbpos : ∀ s, 0 < s → s ≤ d → 0 < kummerRadial ℓ κ s)
    (hbub : ∀ s, 0 < s → s ≤ d → kummerRadial ℓ κ s ≤ 2 * s ^ (ℓ + 1))
    {r : ℝ} (hr : 0 < r) (h2r : 2 * r ≤ d) (hr1 : r ≤ 1)
    (hblb : (1 / 2) * r ^ (ℓ + 1) ≤ kummerRadial ℓ κ r) :
    1 / (8 * 2 ^ (2 * ℓ + 2)) ≤
      kummerRadial ℓ κ r * ∫ s in r..d, 1 / (kummerRadial ℓ κ s) ^ 2 := by
  have hrd : r ≤ d := le_trans (by linarith) h2r
  have hr2r : r ≤ 2 * r := by linarith
  set f := fun s => 1 / (kummerRadial ℓ κ s) ^ 2 with hf
  have hfnn : ∀ s, 0 ≤ f s := fun s => by rw [hf]; positivity
  have hcont : ContinuousOn f (Set.uIcc r d) := by
    rw [hf]
    apply ContinuousOn.div continuousOn_const ((kummerRadial_continuous ℓ κ).pow 2).continuousOn
    intro s hs
    rw [Set.uIcc_of_le hrd] at hs
    exact pow_ne_zero 2 (ne_of_gt (hbpos s (lt_of_lt_of_le hr hs.1) hs.2))
  have hsub1 : Set.uIcc r (2 * r) ⊆ Set.uIcc r d :=
    Set.uIcc_subset_uIcc Set.left_mem_uIcc (by rw [Set.uIcc_of_le hrd]; exact ⟨hr2r, h2r⟩)
  have hsub2 : Set.uIcc (2 * r) d ⊆ Set.uIcc r d :=
    Set.uIcc_subset_uIcc (by rw [Set.uIcc_of_le hrd]; exact ⟨hr2r, h2r⟩) Set.right_mem_uIcc
  have hii_1 : IntervalIntegrable f volume r (2 * r) := (hcont.mono hsub1).intervalIntegrable
  have hii_2 : IntervalIntegrable f volume (2 * r) d := (hcont.mono hsub2).intervalIntegrable
  have hsplit : (∫ s in r..(2 * r), f s) + ∫ s in (2 * r)..d, f s = ∫ s in r..d, f s :=
    intervalIntegral.integral_add_adjacent_intervals hii_1 hii_2
  have htail : 0 ≤ ∫ s in (2 * r)..d, f s :=
    intervalIntegral.integral_nonneg h2r (fun s _ => hfnn s)
  have hΦ1 : (∫ s in r..(2 * r), f s) ≤ ∫ s in r..d, f s := by rw [← hsplit]; linarith
  set c₁ := 1 / (4 * (2 * r) ^ (2 * ℓ + 2)) with hc₁
  have hc₁pos : 0 < c₁ := by rw [hc₁]; positivity
  have hptwise : ∀ s ∈ Set.Icc r (2 * r), c₁ ≤ f s := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hr hs.1
    have hsd : s ≤ d := le_trans hs.2 h2r
    have hφs : kummerRadial ℓ κ s ≤ 2 * (2 * r) ^ (ℓ + 1) := by
      refine le_trans (hbub s hs0 hsd) ?_
      have hp : s ^ (ℓ + 1) ≤ (2 * r) ^ (ℓ + 1) := pow_le_pow_left₀ (le_of_lt hs0) hs.2 _
      linarith
    have hφspos : 0 < kummerRadial ℓ κ s := hbpos s hs0 hsd
    have hsq : (kummerRadial ℓ κ s) ^ 2 ≤ 4 * (2 * r) ^ (2 * ℓ + 2) := by
      have h1 : (kummerRadial ℓ κ s) ^ 2 ≤ (2 * (2 * r) ^ (ℓ + 1)) ^ 2 :=
        pow_le_pow_left₀ (le_of_lt hφspos) hφs 2
      rwa [show (2 * (2 * r) ^ (ℓ + 1)) ^ 2 = 4 * (2 * r) ^ (2 * ℓ + 2) from by
        rw [mul_pow, ← pow_mul]; ring_nf] at h1
    rw [hf, hc₁]
    exact one_div_le_one_div_of_le (by positivity) hsq
  have hintc : (2 * r - r) * c₁ ≤ ∫ s in r..(2 * r), f s := by
    have hmono := intervalIntegral.integral_mono_on hr2r intervalIntegrable_const hii_1 hptwise
    rwa [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hΦlb : (2 * r - r) * c₁ ≤ ∫ s in r..d, f s := le_trans hintc hΦ1
  have hφrpos : 0 < kummerRadial ℓ κ r := hbpos r hr hrd
  have hpow_le : r ^ (2 * ℓ + 2) ≤ r ^ (ℓ + 2) := by
    have hsplit : r ^ (2 * ℓ + 2) = r ^ (ℓ + 2) * r ^ ℓ := by rw [← pow_add]; congr 1; omega
    rw [hsplit]
    have hrℓ : r ^ ℓ ≤ 1 := pow_le_one₀ (le_of_lt hr) hr1
    nlinarith [pow_nonneg (le_of_lt hr) (ℓ + 2), hrℓ]
  calc 1 / (8 * 2 ^ (2 * ℓ + 2))
      ≤ (1 / 2 * r ^ (ℓ + 1)) * ((2 * r - r) * c₁) := by
        have hX : (1 / 2 * r ^ (ℓ + 1)) * ((2 * r - r) * c₁)
            = r ^ (ℓ + 2) / (8 * 2 ^ (2 * ℓ + 2) * r ^ (2 * ℓ + 2)) := by
          rw [hc₁, show (2 * r) ^ (2 * ℓ + 2) = 2 ^ (2 * ℓ + 2) * r ^ (2 * ℓ + 2) from by
            rw [mul_pow]]
          have _hrne : r ≠ 0 := ne_of_gt hr
          field_simp
          ring
        rw [hX, le_div_iff₀ (by positivity)]
        rw [show (1 : ℝ) / (8 * 2 ^ (2 * ℓ + 2)) * (8 * 2 ^ (2 * ℓ + 2) * r ^ (2 * ℓ + 2))
          = r ^ (2 * ℓ + 2) from by field_simp]
        exact hpow_le
    _ ≤ kummerRadial ℓ κ r * ∫ s in r..d, f s :=
        mul_le_mul hblb hΦlb (le_of_lt (mul_pos (by linarith) hc₁pos)) (le_of_lt hφrpos)

/-- **Reduction-of-order FTC identity.** With `W₀` the (constant) Wronskian
`χ φ' − χ' φ`, integrating `(χ/φ)' = -W₀/φ²` gives
`χ(r) − φ(r)·(χ(d)/φ(d)) = W₀·(φ(r)·∫_r^d ds/φ²)`. -/
private lemma reduction_order_ftc (ℓ : ℕ) (κ : ℝ) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    {d : ℝ} (W₀ : ℝ)
    (hW₀ : ∀ s, 0 < s →
      χ s * deriv (kummerRadial ℓ κ) s - deriv χ s * kummerRadial ℓ κ s = W₀)
    (hbpos : ∀ s, 0 < s → s ≤ d → 0 < kummerRadial ℓ κ s)
    {r : ℝ} (hr : 0 < r) (hrd : r < d) :
    χ r - kummerRadial ℓ κ r * (χ d / kummerRadial ℓ κ d)
      = W₀ * (kummerRadial ℓ κ r * ∫ s in r..d, 1 / (kummerRadial ℓ κ s) ^ 2) := by
  have hrd' : r ≤ d := le_of_lt hrd
  have hxpos : ∀ x ∈ Set.uIcc r d, 0 < x := by
    intro x hx; rw [Set.uIcc_of_le hrd'] at hx; exact lt_of_lt_of_le hr hx.1
  have hφpos : ∀ x ∈ Set.uIcc r d, 0 < kummerRadial ℓ κ x := by
    intro x hx
    have hx' := hx; rw [Set.uIcc_of_le hrd'] at hx'
    exact hbpos x (hxpos x hx) hx'.2
  have hφrne : kummerRadial ℓ κ r ≠ 0 := ne_of_gt (hbpos r hr hrd')
  have hφdne : kummerRadial ℓ κ d ≠ 0 := ne_of_gt (hbpos d (lt_trans hr hrd) le_rfl)
  set rawf := fun x => (deriv χ x * kummerRadial ℓ κ x - χ x * deriv (kummerRadial ℓ κ) x) /
    (kummerRadial ℓ κ x) ^ 2 with hrawf
  have hderiv : ∀ x ∈ Set.uIcc r d, HasDerivAt (fun s => χ s / kummerRadial ℓ κ s) (rawf x) x := by
    intro x hx
    exact (hχ1 x (hxpos x hx)).div ((kummerRadial_differentiable ℓ κ x).hasDerivAt)
      (ne_of_gt (hφpos x hx))
  have hint : IntervalIntegrable rawf volume r d := by
    rw [hrawf]
    have hχc : ContinuousOn χ (Set.uIcc r d) :=
      fun x hx => (hχ1 x (hxpos x hx)).continuousAt.continuousWithinAt
    have hdχc : ContinuousOn (deriv χ) (Set.uIcc r d) :=
      fun x hx => (hχ2 x (hxpos x hx)).continuousAt.continuousWithinAt
    have hφc : ContinuousOn (kummerRadial ℓ κ) (Set.uIcc r d) :=
      (kummerRadial_continuous ℓ κ).continuousOn
    have hdφc : ContinuousOn (deriv (kummerRadial ℓ κ)) (Set.uIcc r d) :=
      (kummerRadial_deriv_differentiable ℓ κ).continuous.continuousOn
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div ((hdχc.mul hφc).sub (hχc.mul hdφc))
      ((hφc.pow 2))
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (hφpos x hx))
  have hFTC : ∫ s in r..d, rawf s = χ d / kummerRadial ℓ κ d - χ r / kummerRadial ℓ κ r :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hcongr : Set.EqOn rawf (fun s => -W₀ * (1 / (kummerRadial ℓ κ s) ^ 2)) (Set.uIcc r d) := by
    intro s hs
    have hnum : deriv χ s * kummerRadial ℓ κ s - χ s * deriv (kummerRadial ℓ κ) s = -W₀ := by
      have := hW₀ s (hxpos s hs); linarith
    rw [hrawf]
    simp only
    rw [hnum]; ring
  have hΦ : ∫ s in r..d, rawf s = -W₀ * ∫ s in r..d, 1 / (kummerRadial ℓ κ s) ^ 2 := by
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul]
  rw [hΦ] at hFTC
  -- rearrange
  have key : χ r - kummerRadial ℓ κ r * (χ d / kummerRadial ℓ κ d)
      = kummerRadial ℓ κ r *
        (χ r / kummerRadial ℓ κ r - χ d / kummerRadial ℓ κ d) := by
    field_simp
  rw [key, show χ r / kummerRadial ℓ κ r - χ d / kummerRadial ℓ κ d
    = W₀ * ∫ s in r..d, 1 / (kummerRadial ℓ κ s) ^ 2 from by linarith [hFTC]]
  ring

/-- **The Wronskian vanishes.** A square-integrable-near-`0` solution `χ` with `χ → 0` at `0⁺`
has zero Wronskian with the regular solution `φ`: `χ φ' − χ' φ ≡ 0`. -/
private lemma wronskian_zero (ℓ : ℕ) (κ : ℝ) (hκ : 0 < κ) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    (hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + κ ^ 2) * χ r)
    (hχ0 : Filter.Tendsto χ (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∀ s, 0 < s → χ s * deriv (kummerRadial ℓ κ) s - deriv χ s * kummerRadial ℓ κ s = 0 := by
  obtain ⟨δ, hδ, hbounds⟩ := kummerRadial_near_zero ℓ κ
  set δ' := δ / 2 with hδ'def
  have hδ'pos : 0 < δ' := by rw [hδ'def]; linarith
  have hδ'lt : δ' < δ := by rw [hδ'def]; linarith
  have hbpos : ∀ s, 0 < s → s ≤ δ' → 0 < kummerRadial ℓ κ s :=
    fun s hs0 hsd => (hbounds s hs0 (lt_of_le_of_lt hsd hδ'lt)).2.2
  have hbub : ∀ s, 0 < s → s ≤ δ' → kummerRadial ℓ κ s ≤ 2 * s ^ (ℓ + 1) :=
    fun s hs0 hsd => (hbounds s hs0 (lt_of_le_of_lt hsd hδ'lt)).2.1
  set W₀ := χ δ' * deriv (kummerRadial ℓ κ) δ' - deriv χ δ' * kummerRadial ℓ κ δ' with _hW₀def
  have hWconst : ∀ s, 0 < s →
      χ s * deriv (kummerRadial ℓ κ) s - deriv χ s * kummerRadial ℓ κ s = W₀ :=
    fun s hs => wronskian_const ℓ κ hκ χ hχ1 hχ2 hode hδ'pos hs
  suffices hW₀ : W₀ = 0 by
    intro s hs; rw [hWconst s hs]; exact hW₀
  by_contra hW₀ne
  set ρ := min (δ / 4) 1 with _hρdef
  have hρpos : 0 < ρ := lt_min (by linarith) one_pos
  have hAtend : Filter.Tendsto
      (fun r => χ r - kummerRadial ℓ κ r * (χ δ' / kummerRadial ℓ κ δ'))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h2 := (kummerRadial_tendsto_zero ℓ κ).mul_const (χ δ' / kummerRadial ℓ κ δ')
    simpa using hχ0.sub h2
  have hc0pos : (0 : ℝ) < 1 / (8 * 2 ^ (2 * ℓ + 2)) := by positivity
  have hWc0pos : 0 < |W₀| * (1 / (8 * 2 ^ (2 * ℓ + 2))) := mul_pos (abs_pos.2 hW₀ne) hc0pos
  have hev1 : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      |W₀| * (1 / (8 * 2 ^ (2 * ℓ + 2)))
        ≤ |χ r - kummerRadial ℓ κ r * (χ δ' / kummerRadial ℓ κ δ')| := by
    have hmem : Set.Iio ρ ∈ nhds (0 : ℝ) := Iio_mem_nhds hρpos
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hmem] with r hr0 hrρ
    rw [Set.mem_Ioi] at hr0
    rw [Set.mem_Iio] at hrρ
    have hrδ4 : r < δ / 4 := lt_of_lt_of_le hrρ (min_le_left _ _)
    have hr_lt_δ' : r < δ' := by rw [hδ'def]; linarith
    have h2r : 2 * r ≤ δ' := by rw [hδ'def]; linarith
    have hr1 : r ≤ 1 := le_of_lt (lt_of_lt_of_le hrρ (min_le_right _ _))
    have hblb : (1 / 2) * r ^ (ℓ + 1) ≤ kummerRadial ℓ κ r :=
      (hbounds r hr0 (lt_trans hr_lt_δ' hδ'lt)).1
    have hA := reduction_order_ftc ℓ κ χ hχ1 hχ2 W₀ hWconst hbpos hr0 hr_lt_δ'
    have hlb := reduction_order_lower ℓ κ hbpos hbub hr0 h2r hr1 hblb
    have hPos : 0 ≤ kummerRadial ℓ κ r * ∫ s in r..δ', 1 / (kummerRadial ℓ κ s) ^ 2 :=
      le_trans (le_of_lt hc0pos) hlb
    rw [hA, abs_mul, abs_of_nonneg hPos]
    exact mul_le_mul_of_nonneg_left hlb (abs_nonneg W₀)
  have hev2 : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      |χ r - kummerRadial ℓ κ r * (χ δ' / kummerRadial ℓ κ δ')|
        < |W₀| * (1 / (8 * 2 ^ (2 * ℓ + 2))) := by
    filter_upwards [hAtend.eventually_mem (Metric.ball_mem_nhds 0 hWc0pos)] with r hr
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hr
    exact hr
  obtain ⟨r, hr1, hr2⟩ := (hev1.and hev2).exists
  linarith

/-! ### Part D: global identification `χ = c₀ φ` and the final contradiction -/

/-- **Forward identification.** If `χ − c₀ φ` and its derivative both vanish at `r₁ > 0`
(and `χ` solves the reduced equation), then `χ = c₀ φ` on `[r₁, ∞)`. This is linear ODE
uniqueness, via Grönwall on the first-order system `(u, u')`. -/
private lemma forward_identification (ℓ : ℕ) (κ : ℝ) (hκ : 0 < κ) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    (hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + κ ^ 2) * χ r)
    (c₀ : ℝ) {r₁ : ℝ} (hr₁ : 0 < r₁)
    (h0 : χ r₁ - c₀ * kummerRadial ℓ κ r₁ = 0)
    (h0' : deriv χ r₁ - c₀ * deriv (kummerRadial ℓ κ) r₁ = 0) :
    ∀ r, r₁ ≤ r → χ r = c₀ * kummerRadial ℓ κ r := by
  intro r hr
  set V : ℝ → ℝ := fun x => (ℓ : ℝ) * ((ℓ : ℝ) + 1) / x ^ 2 - 2 / x + κ ^ 2 with hVdef
  set u : ℝ → ℝ := fun s => χ s - c₀ * kummerRadial ℓ κ s with hudef
  set du : ℝ → ℝ := fun s => deriv χ s - c₀ * deriv (kummerRadial ℓ κ) s with hdudef
  set F : ℝ → ℝ × ℝ := fun t => (u t, du t) with hFdef
  set M : ℝ := (ℓ : ℝ) * ((ℓ : ℝ) + 1) / r₁ ^ 2 + 2 / r₁ + κ ^ 2 with hMdef
  have hMnn : 0 ≤ M := by rw [hMdef]; positivity
  set K : ℝ := M + 1 with hKdef
  have hxpos : ∀ x ∈ Set.Icc r₁ r, 0 < x := fun x hx => lt_of_lt_of_le hr₁ hx.1
  -- continuity of F on [r₁, r]
  have hχcont : ContinuousOn χ (Set.Icc r₁ r) :=
    fun x hx => (hχ1 x (hxpos x hx)).continuousAt.continuousWithinAt
  have hdχcont : ContinuousOn (deriv χ) (Set.Icc r₁ r) :=
    fun x hx => (hχ2 x (hxpos x hx)).continuousAt.continuousWithinAt
  have hφcont : ContinuousOn (kummerRadial ℓ κ) (Set.Icc r₁ r) :=
    (kummerRadial_continuous ℓ κ).continuousOn
  have hdφcont : ContinuousOn (deriv (kummerRadial ℓ κ)) (Set.Icc r₁ r) :=
    (kummerRadial_deriv_differentiable ℓ κ).continuous.continuousOn
  have hcont : ContinuousOn F (Set.Icc r₁ r) :=
    (hχcont.sub (continuousOn_const.mul hφcont)).prodMk
      (hdχcont.sub (continuousOn_const.mul hdφcont))
  -- derivative of F
  have hderiv : ∀ x ∈ Set.Ico r₁ r, HasDerivWithinAt F (du x, V x * u x) (Set.Ici x) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hr₁ hx.1
    have hud : HasDerivAt u (du x) x :=
      (hχ1 x hx0).sub ((kummerRadial_differentiable ℓ κ x).hasDerivAt.const_mul c₀)
    have hdud : HasDerivAt du (V x * u x) x := by
      have hb := (hχ2 x hx0).sub
        ((kummerRadial_deriv_differentiable ℓ κ x).hasDerivAt.const_mul c₀)
      convert hb using 1
      rw [show deriv (deriv (kummerRadial ℓ κ)) x = deriv^[2] (kummerRadial ℓ κ) x from rfl,
        hode x hx0, kummerRadial_solves ℓ κ hκ hx0]
      simp only [hVdef, hudef]
      ring
    exact (hud.prodMk hdud).hasDerivWithinAt
  -- initial condition
  have hinit : F r₁ = 0 := by
    simp only [hFdef, hudef, hdudef, Prod.mk_eq_zero]
    exact ⟨h0, h0'⟩
  -- the norm bound
  have hbound : ∀ x ∈ Set.Ico r₁ r, ‖(du x, V x * u x)‖ ≤ K * ‖F x‖ := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hr₁ hx.1
    have hxr₁ : r₁ ≤ x := hx.1
    have hVbound : |V x| ≤ M := by
      have hb1 : 1 / x ^ 2 ≤ 1 / r₁ ^ 2 :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith [hxr₁, hr₁])
      have hb2 : 1 / x ≤ 1 / r₁ := one_div_le_one_div_of_le hr₁ hxr₁
      have hℓ : (0 : ℝ) ≤ (ℓ : ℝ) * ((ℓ : ℝ) + 1) := by positivity
      have h1 : (ℓ : ℝ) * ((ℓ : ℝ) + 1) / x ^ 2 ≤ (ℓ : ℝ) * ((ℓ : ℝ) + 1) / r₁ ^ 2 := by
        rw [div_eq_mul_one_div, div_eq_mul_one_div ((ℓ : ℝ) * ((ℓ : ℝ) + 1)) (r₁ ^ 2)]
        exact mul_le_mul_of_nonneg_left hb1 hℓ
      have h2 : (2 : ℝ) / x ≤ 2 / r₁ := by
        rw [div_eq_mul_one_div, div_eq_mul_one_div (2 : ℝ) r₁]
        exact mul_le_mul_of_nonneg_left hb2 (by norm_num)
      have hx2nn : 0 ≤ (ℓ : ℝ) * ((ℓ : ℝ) + 1) / x ^ 2 := by positivity
      have hr1nn : 0 ≤ (ℓ : ℝ) * ((ℓ : ℝ) + 1) / r₁ ^ 2 := by positivity
      have h2xpos : 0 < (2 : ℝ) / x := by positivity
      have h2r1pos : 0 < (2 : ℝ) / r₁ := by positivity
      simp only [hVdef, hMdef]
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · linarith [h1, h2, hx2nn, hr1nn, h2xpos, h2r1pos, sq_nonneg κ]
      · linarith [h1, h2, hx2nn, hr1nn, h2xpos, h2r1pos, sq_nonneg κ]
    have hFnorm : ‖F x‖ = max |u x| |du x| := by
      rw [hFdef]; simp only [Prod.norm_def, Real.norm_eq_abs]
    have hF'norm : ‖(du x, V x * u x)‖ = max |du x| |V x * u x| := by
      simp only [Prod.norm_def, Real.norm_eq_abs]
    have hmax_nn : 0 ≤ max |u x| |du x| := le_trans (abs_nonneg _) (le_max_left _ _)
    rw [hF'norm, hFnorm]
    apply max_le
    · calc |du x| ≤ max |u x| |du x| := le_max_right _ _
        _ ≤ K * max |u x| |du x| := by rw [hKdef]; nlinarith [mul_nonneg hMnn hmax_nn]
    · rw [abs_mul]
      calc |V x| * |u x| ≤ M * |u x| := mul_le_mul_of_nonneg_right hVbound (abs_nonneg _)
        _ ≤ M * max |u x| |du x| := mul_le_mul_of_nonneg_left (le_max_left _ _) hMnn
        _ ≤ K * max |u x| |du x| := by rw [hKdef]; nlinarith [hmax_nn]
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hcont hderiv hinit hbound
  have hFr : F r = 0 := hzero r (Set.right_mem_Icc.2 hr)
  have hur : u r = 0 := by
    have := congrArg Prod.fst hFr
    simpa [hFdef] using this
  rw [hudef] at hur
  linarith

/-- **Square-integrable bound states of the reduced radial operator are quantized.**

    If `χ` is a `C²` function on `(0,∞)`, square-integrable there, nonzero at some
    point, regular at the origin (`χ(r) → 0` as `r → 0⁺`, hypothesis `hχ0`), and
    solving the reduced radial equation
    `χ''(r) = (ℓ(ℓ+1)/r² − 2/r + κ²)·χ(r)` with decay rate `κ > 0`,
    then `1/κ` is an integer `m ≥ ℓ+1`, i.e. `κ = 1/m`.

    **Why `hχ0` (the Dirichlet boundary condition) is essential.** Without it the
    statement is *false for `ℓ = 0`*: there the operator `−d²/dr² − 2/r` is in the
    Weyl limit-circle case at `0` (inverse-square coefficient `ℓ(ℓ+1) = 0 < 3/4`),
    so the recessive-at-∞ ("irregular") Coulomb solution `W_{1/κ,1/2}(2κr)` is
    bounded (`→ const ≠ 0`) at the origin and `~ e^{−κr}` at infinity — hence
    globally `L²` for *every* `κ > 0`, including non-quantized `κ`. The condition
    `χ → 0` at `0⁺` excludes it (for `ℓ = 0` the regular solution `~ r → 0`, the
    irregular one `→ const ≠ 0`; for `ℓ ≥ 1` the irregular one `~ r^{−ℓ} → ∞`),
    and is satisfied by every genuine reduced eigenfunction
    `χ_{nℓ} = r·R_{nℓ} ~ r^{ℓ+1} → 0` (`radial_boundary_r_zero`).

    **Proof.** Argue by contradiction: if `κ ≠ 1/m` for every `m ≥ ℓ+1`, then the
    Kummer parameter `a = ℓ+1 − 1/κ` is never a non-positive integer, so the
    regular-at-`0` solution `φ = kummerRadial ℓ κ = r^{ℓ+1} e^{−κr} M(a, 2ℓ+2, 2κr)`
    (which solves the reduced equation, `kummerRadial_solves`, via
    `laguerre_ansatz_reduced_iff` and `Spectra.Kummer.kummerM_ode`) grows like
    `|φ(r)| ≳ r^{ℓ+1}` at infinity (`Spectra.Kummer.kummerM_abs_exp_lower`, packaged
    as `kummerRadial_growth`). The Wronskian `χ φ' − χ' φ` is constant on `(0,∞)`;
    the regularity `χ → 0` at `0⁺` forces it to vanish (`wronskian_zero`, a
    reduction-of-order estimate that bounds `∫ dr/φ²` below by integrating over
    `[r, 2r]`). Linear second-order ODE uniqueness — Grönwall on the first-order
    system `(u, u')` with `u = χ − c₀ φ`, `forward_identification` — then propagates
    `χ = c₀ φ` to all of `(0,∞)`, with `c₀ ≠ 0` since `χ` is nonzero somewhere. Thus
    `|χ(r)| = |c₀|·|φ(r)|` is bounded below by a positive constant at infinity, so
    `χ ∉ L²` (`not_radialL2_of_eventually_ge`), contradicting `hL2`. Hence `a` is a
    non-positive integer, i.e. `κ = 1/m` with `m ≥ ℓ+1`. -/
theorem reduced_radial_L2_quantized (ℓ : ℕ) (κ : ℝ) (hκ : 0 < κ) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    (hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + κ ^ 2) * χ r)
    (hχ0 : Filter.Tendsto χ (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hL2 : IntegrableOn (fun r => χ r ^ 2) (Set.Ioi 0))
    (hnz : ∃ r, 0 < r ∧ χ r ≠ 0) :
    ∃ m : ℕ, ℓ + 1 ≤ m ∧ κ = 1 / (m : ℝ) := by
  by_contra hcon
  have _hκ0 : κ ≠ 0 := ne_of_gt hκ
  -- the Kummer parameter `a = ℓ+1−1/κ` does not terminate
  have ha : ∀ p : ℕ, (ℓ : ℝ) + 1 - 1 / κ ≠ -(p : ℝ) := by
    intro p hp
    refine hcon ⟨ℓ + 1 + p, by omega, ?_⟩
    have h1κ : 1 / κ = (ℓ : ℝ) + 1 + (p : ℝ) := by linarith
    have hcast : (((ℓ + 1 + p : ℕ)) : ℝ) = (ℓ : ℝ) + 1 + (p : ℝ) := by push_cast; ring
    rw [hcast, ← h1κ, one_div_one_div]
  -- the Wronskian vanishes
  have hW := wronskian_zero ℓ κ hκ χ hχ1 hχ2 hode hχ0
  -- choose a base point `r₁` (small, below the nonzero point of `χ`)
  obtain ⟨δ, hδ, hbounds⟩ := kummerRadial_near_zero ℓ κ
  obtain ⟨rs, hrs_pos, hrs_ne⟩ := hnz
  set r₁ := min (δ / 2) rs with _hr₁def
  have hr₁pos : 0 < r₁ := lt_min (by linarith) hrs_pos
  have hr₁δ : r₁ < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hr₁rs : r₁ ≤ rs := min_le_right _ _
  have hφr₁pos : 0 < kummerRadial ℓ κ r₁ := (hbounds r₁ hr₁pos hr₁δ).2.2
  have hφr₁ne : kummerRadial ℓ κ r₁ ≠ 0 := ne_of_gt hφr₁pos
  set c₀ := χ r₁ / kummerRadial ℓ κ r₁ with hc₀def
  -- the two initial conditions for `u = χ − c₀ φ`
  have h0 : χ r₁ - c₀ * kummerRadial ℓ κ r₁ = 0 := by
    rw [hc₀def, div_mul_cancel₀ _ hφr₁ne, sub_self]
  have h0' : deriv χ r₁ - c₀ * deriv (kummerRadial ℓ κ) r₁ = 0 := by
    have hWr := hW r₁ hr₁pos
    rw [hc₀def]; field_simp; linarith [hWr]
  -- global identification `χ = c₀ φ` on `[r₁, ∞)`
  have hident := forward_identification ℓ κ hκ χ hχ1 hχ2 hode c₀ hr₁pos h0 h0'
  -- `c₀ ≠ 0` (else `χ` would vanish at the nonzero point)
  have hc₀ne : c₀ ≠ 0 := by
    intro h
    apply hrs_ne
    rw [hident rs hr₁rs, h, zero_mul]
  -- exponential growth of `φ`, transported to `χ`, breaks square-integrability
  obtain ⟨C, R, hC, hgrow⟩ := kummerRadial_growth ℓ κ hκ ha
  have hlb : ∀ r, max r₁ R ≤ r → |c₀| * C ≤ |χ r| := by
    intro r hr
    have hr_r₁ : r₁ ≤ r := le_trans (le_max_left _ _) hr
    have hr_R : R ≤ r := le_trans (le_max_right _ _) hr
    rw [hident r hr_r₁, abs_mul]
    exact mul_le_mul_of_nonneg_left (hgrow r hr_R) (abs_nonneg c₀)
  exact not_radialL2_of_eventually_ge χ (mul_pos (abs_pos.2 hc₀ne) hC) hlb hL2

/-- **Consistency of the analytic core on the known eigenfunctions.**

    The reduced hydrogen eigenfunction `χ_{mℓ} = r·R_{mℓ}` (for `m ≥ ℓ+1`) solves
    the reduced radial equation `χ'' = (ℓ(ℓ+1)/r² − 2/r + κ²)·χ` with decay rate
    `κ = 1/m`. Combined with `radial_wavefunction_L2` (square-integrability) and
    `radial_wavefunction_norm` (nonvanishing), this exhibits `χ_{mℓ}` as a witness
    satisfying *every* hypothesis of `reduced_radial_L2_quantized`, with the
    expected conclusion `κ = 1/m`. It confirms that the reduced equation
    (`reduced_ode`) and `reduced_radial_L2_quantized`'s hypotheses are correctly stated
    and non-vacuous (a mis-stated reduced ODE would fail to compile here). -/
theorem reduced_eigenfunction_solves (m ℓ : ℕ) (hm : ℓ + 1 ≤ m) {r : ℝ} (hr : 0 < r) :
    deriv^[2] (fun s => s * hydrogenRadialWavefunction m ℓ hm s) r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + (1 / (m : ℝ)) ^ 2)
        * (r * hydrogenRadialWavefunction m ℓ hm r) := by
  have hψ1 : ∀ s, 0 < s →
      HasDerivAt (hydrogenRadialWavefunction m ℓ hm)
        (deriv (hydrogenRadialWavefunction m ℓ hm) s) s :=
    fun s _ => (differentiable_hydrogenRadial m ℓ hm s).hasDerivAt
  have hψ2 : ∀ s, 0 < s →
      HasDerivAt (deriv (hydrogenRadialWavefunction m ℓ hm))
        (deriv^[2] (hydrogenRadialWavefunction m ℓ hm) s) s :=
    fun s _ => (differentiable_deriv_hydrogenRadial m ℓ hm s).hasDerivAt
  have heq : ∀ s, 0 < s → radialHamiltonian ℓ (hydrogenRadialWavefunction m ℓ hm) s
      = hydrogenEigenvalue m (by omega) * hydrogenRadialWavefunction m ℓ hm s :=
    fun s hs => radial_eigenvalue_eq m ℓ hm s hs
  have h := reduced_ode ℓ (hydrogenEigenvalue m (by omega))
    (hydrogenRadialWavefunction m ℓ hm) hψ1 hψ2 heq hr
  have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hE : -2 * hydrogenEigenvalue m (by omega) = (1 / (m : ℝ)) ^ 2 := by
    rw [hydrogenEigenvalue]; field_simp
  rw [h, ← hE]; ring

/-! ## Quantization -/

/-- **The quantization theorem.**

    A *classical* (`C²` on `(0,∞)`) square-integrable solution of the radial
    equation `H_ℓ ψ = E ψ` with `E < 0` that is nonzero somewhere on `(0,∞)` and
    regular at the origin (`r·ψ(r) → 0` as `r → 0⁺`) exists if and only if
    `E = −1/(2n²)` for some integer `n ≥ ℓ + 1`.

    **On the hypotheses.** The `C²` hypotheses (`HasDerivAt`), the nondegeneracy
    `∃ r₀ > 0, ψ r₀ ≠ 0`, and the regularity `r·ψ(r) → 0` at `0⁺` are all
    essential. `radialHamiltonian` is built from Mathlib's junk-extended `deriv`,
    so *without* differentiability a `ψ` supported on a single point (or supported
    off `(0,∞)`) satisfies the equation vacuously for an arbitrary `E < 0`. And
    *without* the regularity condition the statement is false for `ℓ = 0`: the
    irregular Coulomb solution `ψ = W_{1/κ,1/2}(2κr)/r` is `C²` on `(0,∞)`,
    `L²(r²dr)`, nonzero, and solves the equation for *every* `E < 0` (limit-circle
    case at `0`; see `reduced_radial_L2_quantized`). The
    `C²`/nondegeneracy/regularity form here is the genuine classical-solution
    theorem, and matches the hypotheses of `radial_eigenfunction_unique`.

    **`←` (E = Eₙ ⟹ a solution exists): proved.** Take `ψ = R_{nℓ}`; it is `C²`
    (`differentiable_hydrogenRadial`), L² (`radial_wavefunction_L2`), nonzero
    (from `radial_wavefunction_norm`), solves the equation (`radial_eigenvalue_eq`),
    and is regular at `0` — `r·R_{nℓ}(r)` is continuous with value `0` at `r = 0`.

    **`→` (a solution exists ⟹ E = Eₙ): proved.**
    Set `κ = √(−2E) > 0` and pass to the reduced wavefunction `χ = r·ψ`, which by
    `reduced_ode` solves `χ'' = (ℓ(ℓ+1)/r² − 2/r + κ²)χ`. That an L² such `χ` forces
    `κ = 1/m` with `m ∈ ℕ`, `m ≥ ℓ+1` is `reduced_radial_L2_quantized` (proved via the
    confluent-hypergeometric machinery of `Spectra.Kummer`; see its docstring). Then
    `E = Eₘ` by `energy_eq_of_kappa`. -/
theorem radial_quantization (ℓ : ℕ) (E : ℝ) (hE : E < 0) :
    (∃ (ψ : ℝ → ℝ),
        (∃ r₀, 0 < r₀ ∧ ψ r₀ ≠ 0) ∧ RadialL2 ψ ∧
        (∀ r, 0 < r → HasDerivAt ψ (deriv ψ r) r) ∧
        (∀ r, 0 < r → HasDerivAt (deriv ψ) (deriv^[2] ψ r) r) ∧
        (∀ r, 0 < r → radialHamiltonian ℓ ψ r = E * ψ r) ∧
        Filter.Tendsto (fun r => r * ψ r) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ↔
    ∃ (n : ℕ) (hn : ℓ + 1 ≤ n), E = hydrogenEigenvalue n (by omega) := by
  constructor
  · -- (→) a classical L² bound state forces quantization (via the reduced equation).
    rintro ⟨ψ, hnz, hL2, hψ1, hψ2, heq, hψ0⟩
    obtain ⟨hκpos, hκ2⟩ := kappa_pos_sq E hE
    set κ := Real.sqrt (-2 * E) with _hκdef
    set χ : ℝ → ℝ := fun s => s * ψ s with hχdef
    have hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r := by
      intro r hr
      rw [hχdef, deriv_reducedMul ψ (hψ1 r hr)]
      exact hasDerivAt_reducedMul ψ (hψ1 r hr)
    have hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r := by
      intro r hr
      rw [hχdef, deriv2_reducedMul ψ hψ1 hψ2 hr]
      exact hasDerivAt_deriv_reducedMul ψ hψ1 hψ2 hr
    have hode : ∀ r, 0 < r → deriv^[2] χ r
        = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + κ ^ 2) * χ r := by
      intro r hr
      have hχr : χ r = r * ψ r := rfl
      rw [show deriv^[2] χ r = deriv^[2] (fun s => s * ψ s) r from rfl,
        reduced_ode ℓ E ψ hψ1 hψ2 heq hr, hχr, hκ2]
      ring
    have hχL2 : IntegrableOn (fun r => χ r ^ 2) (Set.Ioi 0) := reduced_integrableOn_sq ψ hL2
    have hχnz : ∃ r, 0 < r ∧ χ r ≠ 0 := reduced_nonzero ψ hnz
    have hχ0 : Filter.Tendsto χ (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := hψ0
    obtain ⟨m, hm_le, hκm⟩ :=
      reduced_radial_L2_quantized ℓ κ hκpos χ hχ1 hχ2 hode hχ0 hχL2 hχnz
    exact ⟨m, hm_le, energy_eq_of_kappa E κ m (by omega) hκ2 hκm⟩
  · -- (←) construct the eigenfunction R_{nℓ}.
    rintro ⟨n, hn, rfl⟩
    refine ⟨hydrogenRadialWavefunction n ℓ hn, ?_, radial_wavefunction_L2 n ℓ hn,
      fun r _ => (differentiable_hydrogenRadial n ℓ hn r).hasDerivAt,
      fun r _ => (differentiable_deriv_hydrogenRadial n ℓ hn r).hasDerivAt,
      fun r hr => radial_eigenvalue_eq n ℓ hn r hr,
      ((continuous_id'.mul (continuous_hydrogenRadialWavefunction n ℓ hn)).tendsto'
        0 0 (by simp)).mono_left nhdsWithin_le_nhds⟩
    -- nondegeneracy: if R_{nℓ} vanished on all of (0,∞) its unit norm would be 0.
    by_contra hcon
    have hz : ∀ r, 0 < r → hydrogenRadialWavefunction n ℓ hn r = 0 :=
      fun r hr => not_not.1 (fun h => hcon ⟨r, hr, h⟩)
    have hnorm := radial_wavefunction_norm n ℓ hn
    rw [setIntegral_congr_fun measurableSet_Ioi
      (g := fun _ => (0 : ℝ)) (fun r hr => by rw [hz r hr]; ring)] at hnorm
    simp at hnorm

end QuantumMechanics.Hydrogen.RadialEq
