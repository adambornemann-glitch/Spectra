/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumFieldTheory.OsterwalderSchrader.ReflectionPositivity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The Osterwalder–Seiler reflection-positivity engine (integral form)

This file supplies the **positivity mechanism** at the heart of Osterwalder–Schrader /
Osterwalder–Seiler reflection positivity, at the level of integrals over a measure space — the
concrete realization of the abstract predicate in `ReflectionPositivity.lean` (Lane R1), and the
reusable engine that lattice gauge theory's reflection positivity (Lane R2) plugs into.

## The mathematics

Split a Euclidean configuration space as `Ω = X × X`, the negative-time block times the
positive-time block, with the (geometric) time reflection `θ` identifying the two factors.
The reflection-symmetric reference measure carries the same marginal `ν` on each factor —
modeled here as the iterated integral against `ν` in each slot — weighted by a Boltzmann
density `ρ(a, b)` (`a` the reflected negative-time variable, `b` the positive-time variable);
an observable `A` supported in positive time is a function `A(a, b) = f(b)` of the
positive-time block alone; its **reflected pairing** is
$$ \langle A, A\rangle_{\mathrm{OS}} \;=\; \int (\theta A)\,A \; = \;
   \int_X\!\!\int_X \overline{f(a)}\, f(b)\, \rho(a, b)\, \mathrm d\nu(a)\,\mathrm d\nu(b), $$
here packaged as `reflectedForm ν ρ f`.

Reflection positivity is the statement `0 ≤ ⟨A, A⟩_{OS}`.  The Osterwalder–Seiler observation is
that it holds **whenever the Boltzmann density is a positive-definite kernel of the reflected
form**,
$$ \rho(a, b) \;=\; \sum_{i} \overline{g_i(a)}\, g_i(b) \qquad(\text{a finite Gram sum}), $$
because then the double integral collapses to a manifest sum of squared moduli:
$$ \langle A, A\rangle_{\mathrm{OS}} \;=\;
   \sum_i \Bigl|\!\int_X f\, g_i \,\mathrm d\nu\Bigr|^2 \;\ge\; 0. $$
The whole content of the Osterwalder–Seiler theorem for the Wilson action then reduces to
exhibiting the plaquette Boltzmann weight `exp(β·Re tr(⋯))` in this Gram form — which is exactly
the **character/heat-kernel expansion** on the compact gauge group (Lane G5).  This file proves
the engine and the collapse unconditionally; it does **not** perform that expansion.

## Main definitions and results

* `reflectedForm ν ρ f` — the reflected pairing, an iterated integral.
* `reflectedForm_gram` — the collapse: for a Gram kernel `ρ = ∑ᵢ conj(gᵢ) ⊗ gᵢ`, the reflected form
  equals `∑ᵢ ‖∫ f·gᵢ‖²` (as a nonnegative real cast into `ℂ`), under integrability of each `f·gᵢ`.
* `reflectedForm_gram_re_nonneg` / `reflectedForm_gram_im` — reflection positivity: the reflected
  form is a nonnegative real (`0 ≤ .re`, `.im = 0`).
* `IsReflectionPositiveKernel` — the (measure-free) predicate "`ρ` is a finite Gram kernel", the
  exact input Lane G5's character expansion must supply for the Wilson weight.
* `reflectedForm_re_nonneg_of_kernel` — reflection positivity from a Gram kernel plus integrability.
* `reflectedForm_const_one` — the **free (`β = 0`) case**: the constant kernel `ρ ≡ 1` (a single
  Gram mode `g ≡ 1`) is reflection positive, with `⟨A, A⟩_{OS} = ‖∫ f‖²`.  This is an
  *unconditional* reflection-positivity estimate in the integral framework — the `X × X`-swap
  analogue of `ReflectionData.trivial`, but with a genuine (non-identity) reflection rather than
  `id`.  (It yields a nonnegative *value*, not yet a bundled `ReflectionData`; that completion is
  Lane R3.)

## Relation to Lanes R1/R3

`ReflectionPositivity.lean` (R1) states the abstract predicate on an inner-product space; this
file is its concrete integral realization on `L²`-style data.  The GNS/Hilbert-space completion
of this positive-semidefinite reflected form — turning `reflectedForm` into a genuine
`ReflectionData` — is Lane R3, deliberately not done here (this is only the positivity estimate,
R2's mathematical core).

## References

* K. Osterwalder, E. Seiler, *Gauge field theories on a lattice*, Ann. Physics 110 (1978) 440–471.
* J. Glimm, A. Jaffe, *Quantum Physics: A Functional Integral Point of View*, §6.2, §7.10.

## Tags

reflection positivity, Osterwalder-Schrader, Osterwalder-Seiler, Gram kernel, lattice gauge theory
-/

open MeasureTheory ComplexConjugate

namespace Spectra.QuantumFieldTheory.OsterwalderSchrader

variable {X : Type*} [MeasurableSpace X]

/-- The **reflected pairing** of a positive-time observable `f` against a Boltzmann kernel `ρ`:
`∫∫ conj(f a) · f b · ρ(a, b) dν(a) dν(b)`, the Osterwalder–Schrader reflected form
`⟨A, A⟩_OS` with `A(a, b) = f(b)` positive-time and the reflection identifying the two
`X`-factors. -/
noncomputable def reflectedForm (ν : Measure X) (ρ : X → X → ℂ) (f : X → ℂ) : ℂ :=
  ∫ a, ∫ b, conj (f a) * f b * ρ a b ∂ν ∂ν

/-- **The Osterwalder–Seiler collapse.**  For a Boltzmann kernel of Gram form
`ρ(a, b) = ∑ᵢ conj(gᵢ a) · gᵢ b`, the reflected pairing equals `∑ᵢ ‖∫ f·gᵢ‖²`, a nonnegative real —
the mechanism behind reflection positivity.  The only hypothesis is integrability of each mode
product `f · gᵢ` (automatic on a compact group with continuous data, the lattice-gauge use
case). -/
theorem reflectedForm_gram (ν : Measure X) {ι : Type*} (s : Finset ι) (g : ι → X → ℂ) (f : X → ℂ)
    (hint : ∀ i ∈ s, Integrable (fun x => f x * g i x) ν) :
    reflectedForm ν (fun a b => ∑ i ∈ s, conj (g i a) * g i b) f
      = ((∑ i ∈ s, Complex.normSq (∫ x, f x * g i x ∂ν) : ℝ) : ℂ) := by
  -- Abbreviation for the moments `Iᵢ = ∫ f·gᵢ`.
  set I : ι → ℂ := fun i => ∫ x, f x * g i x ∂ν with _hI
  -- Inner integral (fixing `a`) collapses to a finite sum with `Iᵢ`.
  have hInner : ∀ a, (∫ b, conj (f a) * f b * (∑ i ∈ s, conj (g i a) * g i b) ∂ν)
      = ∑ i ∈ s, conj (f a * g i a) * I i := by
    intro a
    have hrw : (∫ b, conj (f a) * f b * (∑ i ∈ s, conj (g i a) * g i b) ∂ν)
        = ∫ b, ∑ i ∈ s, conj (f a * g i a) * (f b * g i b) ∂ν := by
      congr 1; funext b
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [map_mul]; ring
    rw [hrw, integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul]
    · exact fun i hi => (hint i hi).const_mul _
  -- Outer integral: move conjugation out via `integral_conj`, then collapse the remaining sum.
  unfold reflectedForm
  simp_rw [hInner]
  have hconj : (fun a => ∑ i ∈ s, conj (f a * g i a) * I i)
      = fun a => conj (∑ i ∈ s, (f a * g i a) * conj (I i)) := by
    funext a
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul, Complex.conj_conj]
  rw [hconj, integral_conj, integral_finsetSum]
  · -- `∑ᵢ (∫ f·gᵢ)·conj(Iᵢ) = ∑ᵢ Iᵢ·conj(Iᵢ) = ∑ᵢ ‖Iᵢ‖²`, then conj of a real is itself.
    have hterm : ∀ i ∈ s, (∫ a, (f a * g i a) * conj (I i) ∂ν) = (Complex.normSq (I i) : ℂ) := by
      intro i _
      rw [integral_mul_const]
      change I i * conj (I i) = (Complex.normSq (I i) : ℂ)
      rw [Complex.mul_conj]
    rw [Finset.sum_congr rfl hterm, ← Complex.ofReal_sum, Complex.conj_ofReal]
  · exact fun i hi => (hint i hi).mul_const _

/-- **Reflection positivity, Gram form (real part).**  The reflected pairing of a Gram-kernel
Boltzmann weight is a nonnegative real. -/
theorem reflectedForm_gram_re_nonneg (ν : Measure X) {ι : Type*} (s : Finset ι) (g : ι → X → ℂ)
    (f : X → ℂ) (hint : ∀ i ∈ s, Integrable (fun x => f x * g i x) ν) :
    0 ≤ (reflectedForm ν (fun a b => ∑ i ∈ s, conj (g i a) * g i b) f).re := by
  rw [reflectedForm_gram ν s g f hint, Complex.ofReal_re]
  exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _

/-- **Reflection positivity, Gram form (imaginary part vanishes).**  The reflected pairing is
genuinely real. -/
theorem reflectedForm_gram_im (ν : Measure X) {ι : Type*} (s : Finset ι) (g : ι → X → ℂ)
    (f : X → ℂ) (hint : ∀ i ∈ s, Integrable (fun x => f x * g i x) ν) :
    (reflectedForm ν (fun a b => ∑ i ∈ s, conj (g i a) * g i b) f).im = 0 := by
  rw [reflectedForm_gram ν s g f hint, Complex.ofReal_im]

/-- **`ρ` is a reflection-positive (Gram) kernel:** a finite-rank Gram kernel of the reflected form,
`ρ(a, b) = ∑ᵢ conj(gᵢ a) · gᵢ b` (hence positive semidefinite).  This measure-free predicate is
*exactly* the input Lane G5's character/heat-kernel expansion must supply for the Wilson plaquette
weight; the reflection positivity of the lattice Gibbs measure (Lane R2) then follows from
`reflectedForm_re_nonneg_of_kernel`. -/
def IsReflectionPositiveKernel (ρ : X → X → ℂ) : Prop :=
  ∃ (ι : Type) (s : Finset ι) (g : ι → X → ℂ),
    ρ = fun a b => ∑ i ∈ s, conj (g i a) * g i b

omit [MeasurableSpace X] in
/-- The constant kernel `ρ ≡ 1` is a reflection-positive kernel — the single Gram mode `g ≡ 1`.
(This is the `β = 0` Boltzmann weight of the lattice gauge theory: no interaction.) -/
theorem isReflectionPositiveKernel_const_one :
    IsReflectionPositiveKernel (fun _ _ : X => (1 : ℂ)) := by
  refine ⟨Unit, {()}, fun _ _ => 1, ?_⟩
  funext a b; simp

/-- **Reflection positivity from a Gram kernel.**  If the Boltzmann density is a reflection-positive
kernel and the observable's products with the kernel modes are integrable, the reflected pairing is
a nonnegative real.  This is the engine Lane R2 invokes: feed it G5's Gram decomposition of the
Wilson weight. -/
theorem reflectedForm_re_nonneg_of_kernel (ν : Measure X) {ρ : X → X → ℂ} {f : X → ℂ}
    (h : ∃ (ι : Type) (s : Finset ι) (g : ι → X → ℂ),
      ρ = (fun a b => ∑ i ∈ s, conj (g i a) * g i b) ∧
        ∀ i ∈ s, Integrable (fun x => f x * g i x) ν) :
    0 ≤ (reflectedForm ν ρ f).re := by
  obtain ⟨ι, s, g, rfl, hint⟩ := h
  exact reflectedForm_gram_re_nonneg ν s g f hint

/-! ## The free (`β = 0`) case: reflection positivity of the product measure

At zero coupling the Boltzmann weight is constant (`ρ ≡ 1`) and reflection positivity holds
unconditionally: the reflected pairing of any integrable observable is `‖∫ f‖²`.  This is a
concrete, *unconditional* reflection-positivity estimate — the honest lattice-gauge analogue of
`ReflectionData.trivial`, but with a genuine (non-identity) reflection built into the `X × X`
splitting. -/

/-- **The free case.**  For the constant kernel `ρ ≡ 1`, the reflected pairing collapses to
`‖∫ f‖²`. -/
theorem reflectedForm_const_one (ν : Measure X) (f : X → ℂ) (hf : Integrable f ν) :
    reflectedForm ν (fun _ _ => (1 : ℂ)) f = (Complex.normSq (∫ x, f x ∂ν) : ℂ) := by
  have h := reflectedForm_gram ν ({()} : Finset Unit) (fun _ _ => (1 : ℂ)) f
    (fun _ _ => by simpa using hf)
  simpa using h

/-- **Reflection positivity of the free (`β = 0`) theory:** the reflected pairing of the constant
kernel is a nonnegative real. -/
theorem reflectedForm_const_one_re_nonneg (ν : Measure X) (f : X → ℂ) (hf : Integrable f ν) :
    0 ≤ (reflectedForm ν (fun _ _ => (1 : ℂ)) f).re := by
  rw [reflectedForm_const_one ν f hf, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

end Spectra.QuantumFieldTheory.OsterwalderSchrader
