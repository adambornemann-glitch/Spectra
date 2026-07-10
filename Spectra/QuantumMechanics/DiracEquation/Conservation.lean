/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.DiracEquation.Current
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
/-!
# Local Conservation of the Dirac Current

This file proves the **local** continuity equation `∂ᵤjᵘ = 0`: when a spinor field
satisfies the Dirac equation, its 4-current is divergence-free. This is the local form of
probability conservation.

The **global** result `d/dt ∫ρ d³x = 0` (`probability_conserved`) is *not* in this file. It is
developed in `QuantumMechanics/Unitarity/Basic.lean`, whose `continuity_equation` and
`probability_conserved` consume the local conservation theorem proved here.

## Main definitions

* `stdBasis`: standard basis vectors in ℝ⁴
* `fourDivergence`: the 4-divergence `∂ᵤjᵘ`
* `partialDeriv'`: partial derivative of a spinor field

## Main results

* `dirac_current_conserved`: if `ψ` solves the Dirac equation (`h_dirac`) and is differentiable,
  then `∂ᵤjᵘ = 0`. Assembled from the bilinear product rule (`hasDerivAt_bilinear_self`), the
  per-`μ` adjoint transfer (`current_adjoint_transfer`), and the mass-term cancellation
  (`dirac_divergence_bilinear_vanishes`).

The conclusion is conditional on `ψ` *being* a solution; the link to the operator dynamics
`e^{-itH_D}ψ` of `FreeHamiltonian.lean` is not yet made.

## Physical interpretation

### Current Conservation
The continuity equation ∂ᵤjᵘ = ∂ρ/∂t + ∇·j = 0 is the local form of
probability conservation. It says that probability density changes only
due to probability current flowing in or out — there are no sources or sinks.

### Global Conservation
Integrating over all space: d/dt ∫ρ d³x = -∫∇·j d³x = 0 (by divergence theorem
with vanishing boundary conditions). The total probability is constant.

### The Born Rule
Max Born's interpretation (1926): |ψ(x)|² gives the probability density for
finding the particle at position x. The local conservation proved here is what makes
`ρ/∫ρ` a *consistent* probability distribution over time — normalized once, it stays
normalized:
1. Non-negativity: P(x) ≥ 0
2. Normalization: ∫P(x)d³x = 1

This connects the mathematical formalism to physical measurement. (The normalization
axioms themselves are not established in this file.)

## References

* [Born, *Zur Quantenmechanik der Stoßvorgänge*][born1926]
* [Dirac, *The Principles of Quantum Mechanics*][dirac1930], Chapter XI
* [Thaller, *The Dirac Equation*][thaller1992], §1.4 (conserved current)
* [Peskin, Schroeder, *An Introduction to Quantum Field Theory*][peskin1995], §3.4

## Tags

probability conservation, continuity equation, Born rule, divergence theorem,
current conservation
-/
open Complex
open Spectra.QuantumMechanics.Dirac.Current
namespace Spectra.QuantumMechanics.Dirac.Conservation

/-! ## Calculus Setup -/

/-- Standard basis vector eᵤ in ℝ⁴.

  e₀ = (1,0,0,0), e₁ = (0,1,0,0), e₂ = (0,0,1,0), e₃ = (0,0,0,1)

Used to define partial derivatives via directional derivatives. -/
def stdBasis (μ : Fin 4) : Spacetime := fun ν => if μ = ν then 1 else 0

/-- The four-divergence ∂ᵤjᵘ = ∂₀j⁰ + ∂₁j¹ + ∂₂j² + ∂₃j³.

In components: ∂ᵤjᵘ = ∂ρ/∂t + ∂jˣ/∂x + ∂jʸ/∂y + ∂jᶻ/∂z.

The continuity equation states ∂ᵤjᵘ = 0 for solutions of the Dirac equation. -/
noncomputable def fourDivergence (j : (Fin 4 → ℝ) → (Fin 4 → ℂ)) :
    (Fin 4 → ℝ) → ℂ :=
  fun x => ∑ μ, deriv (fun t => j (Function.update x μ t) μ) (x μ)

/-- Partial derivative of a spinor field: ∂ᵤψ.

This is the directional derivative along the μ-th coordinate axis:
  (∂ᵤψ)(x) = lim_{ε→0} (ψ(x + εeᵤ) - ψ(x)) / ε

Each spinor component is differentiated separately.

The trailing prime distinguishes this spinor-field partial derivative from the scalar-field
`partialDeriv`-family lemmas in `Spaces/Sobolev/` (`memLp_partialDeriv`, `contDiff_partialDeriv`,
…); here the value is a full spinor `Fin 4 → ℂ` rather than a single component. -/
noncomputable def partialDeriv' (μ : Fin 4) (ψ : Spacetime → (Fin 4 → ℂ))
    (x : Spacetime) : Fin 4 → ℂ :=
  fun a => fderiv ℝ (fun y => ψ y a) x (stdBasis μ)

/-- **Adjoint transfer**: u†(A†w) = (Au)†w for the spinor bilinear form.

    In components:
    ∑ᵢ conj(uᵢ) · ∑ⱼ conj(Aⱼᵢ) · wⱼ = ∑ⱼ conj(∑ᵢ Aⱼᵢuᵢ) · wⱼ.
    This is the finite-dimensional version of ⟨u, A†w⟩ = ⟨Au, w⟩. -/
lemma star_dotProduct_conjTranspose_mulVec
    (A : Matrix (Fin 4) (Fin 4) ℂ) (u w : Fin 4 → ℂ) :
    star u ⬝ᵥ A.conjTranspose.mulVec w = star (A.mulVec u) ⬝ᵥ w := by
  simp only [dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply,
             Pi.star_apply, RCLike.star_def, map_sum, map_mul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1; ext j; congr 1; ext i; ring

/-- **Per-μ adjoint transfer for the current**: ψ†(γ⁰γ^μ)φ = (γ^μ ψ)†(γ⁰ φ).

    This is the identity that lets the adjoint Dirac equation "eat" the
    current: instead of γ⁰γ^μ acting on the right spinor, γ^μ acts on
    the left spinor under the dagger, leaving only γ⁰. -/
lemma current_adjoint_transfer (Γ : GammaMatrices) (μ : Fin 4) (u v : Fin 4 → ℂ) :
    star u ⬝ᵥ (Γ.gamma 0 * Γ.gamma μ).mulVec v =
    star ((Γ.gamma μ).mulVec u) ⬝ᵥ (Γ.gamma 0).mulVec v := by
  conv_lhs =>
    rw [show Γ.gamma 0 * Γ.gamma μ = (Γ.gamma μ).conjTranspose * Γ.gamma 0
        from (gamma_conjTranspose_mul_gamma0 Γ μ).symm,
        ← Matrix.mulVec_mulVec]
  exact star_dotProduct_conjTranspose_mulVec (Γ.gamma μ) u ((Γ.gamma 0).mulVec v)

/-- **Sesquilinear cancellation**: (c·u)†v + u†(c·v) = (c̄+c)·(u†v).

    When a scalar multiplies from opposite sides of a bilinear pairing,
    the result collects the scalar plus its conjugate. For purely imaginary c,
    c̄ + c = 0 and the whole expression vanishes. -/
lemma star_smul_dotProduct_add (c : ℂ) (u v : Fin 4 → ℂ) :
    star (c • u) ⬝ᵥ v + star u ⬝ᵥ (c • v) =
    (starRingEnd ℂ c + c) * (star u ⬝ᵥ v) := by
  rw [star_smul, smul_dotProduct]
  rw [dotProduct_comm (star u) (c • v), smul_dotProduct, dotProduct_comm]
  ring_nf; simp only [RCLike.star_def]
  exact AddCommMagma.add_comm (v ⬝ᵥ star u * (starRingEnd ℂ) c) (v ⬝ᵥ star u * c)

/-- **Mass cancellation**: conj(-im) + (-im) = 0 for real m.
    conj(-im) = -conj(i)·conj(m) = -(-i)·m = im, so im + (-im) = 0. -/
lemma neg_I_mul_ofReal_add_conj (m : ℝ) :
    starRingEnd ℂ (-(I * ↑m)) + (-(I * ↑m)) = 0 := by
  rw [map_neg, map_mul, conj_I, conj_ofReal]; ring

/-- **Divergence cancellation** (algebraic core):

    Given w = ∑ γ^μ(∂_μψ) satisfying the Dirac equation I·w = m·ψ (m real),
    the divergence bilinear form vanishes:
      w† · γ⁰(ψ)  +  ψ† · γ⁰(w)  =  0. -/
lemma dirac_divergence_bilinear_vanishes (Γ : GammaMatrices) (m : ℝ)
    (ψ w : Fin 4 → ℂ)
    (h : I • w = (↑m : ℂ) • ψ) :
    star w ⬝ᵥ (Γ.gamma 0).mulVec ψ +
    star ψ ⬝ᵥ (Γ.gamma 0).mulVec w = 0 := by
  -- Step 1: Extract w = (-(I * m)) • ψ from Dirac equation
  have hw : w = (-(I * ↑m)) • ψ := by
    have h1 := congr_arg ((-I) • ·) h
    simp only [smul_smul] at h1
    rwa [show (-I : ℂ) * I = 1 from by rw [neg_mul, ← sq, I_sq, neg_neg],
         one_smul, neg_mul] at h1
  -- Step 2: Substitute and linearize γ⁰
  rw [hw, show (Γ.gamma 0).mulVec ((-(I * ↑m)) • ψ) = (-(I * ↑m)) • (Γ.gamma 0).mulVec ψ
       from (Γ.gamma 0).mulVecLin.map_smul _ _]
  -- Step 3: Sesquilinear identity + mass cancellation
  rw [star_smul_dotProduct_add, neg_I_mul_ofReal_add_conj, zero_mul]

/-! ### Helper A1: diracCurrent as dot product -/

lemma diracCurrent_eq_dotProduct_mulVec (Γ : GammaMatrices) (v : Fin 4 → ℂ) (μ : Fin 4) :
    diracCurrent Γ v μ = star v ⬝ᵥ (Γ.gamma 0 * Γ.gamma μ).mulVec v := by
  simp only [diracCurrent, dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def]
  congr 1; ext a; rw [Finset.mul_sum]; congr 1; ext b; ring

/-! ### Helper B1: HasDerivAt for coordinate update -/

lemma hasDerivAt_update (x : Spacetime) (μ : Fin 4) :
    HasDerivAt (fun t => Function.update x μ t) (stdBasis μ) (x μ) := by
  rw [hasDerivAt_pi]
  intro ν
  simp only [stdBasis]
  by_cases h : μ = ν
  · subst h
    simp only [Function.update_self, ↓reduceIte]
    exact hasDerivAt_id (x μ)
  · simp only [h, ↓reduceIte]
    have hν : ∀ t, Function.update x μ t ν = x ν :=
      fun t => Function.update_of_ne
        (fun a => h (id (Eq.symm a))) t x
    simp_rw [hν]
    exact hasDerivAt_const _ _

/-! ### Helper C1: Bilinear product rule -/

/-- Product rule for the sesquilinear form t ↦ star(f t) ⬝ᵥ M.mulVec(f t) -/
lemma hasDerivAt_bilinear_self
    (M : Matrix (Fin 4) (Fin 4) ℂ) (f : ℝ → Fin 4 → ℂ) (f' : Fin 4 → ℂ) (t₀ : ℝ)
    (hf : HasDerivAt f f' t₀) :
    HasDerivAt (fun t => star (f t) ⬝ᵥ M.mulVec (f t))
      (star f' ⬝ᵥ M.mulVec (f t₀) + star (f t₀) ⬝ᵥ M.mulVec f') t₀ := by
  -- Component-wise derivatives
  have hf_a : ∀ a, HasDerivAt (fun t => f t a) (f' a) t₀ :=
    hasDerivAt_pi.mp hf
  -- Conjugation is ℝ-differentiable: d/dt conj(f_a(t)) = conj(f'_a)
  have hf_star : ∀ a, HasDerivAt (fun t => starRingEnd ℂ (f t a))
      (starRingEnd ℂ (f' a)) t₀ := by
    intro a
    have h := (RCLike.conjCLE (K := ℂ)).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
      t₀ (hf_a a)
    convert h using 1
  -- Constant × component: d/dt (M_{ab} · f_b(t)) = M_{ab} · f'_b
  have h_Mf : ∀ a b, HasDerivAt (fun t => M a b * f t b) (M a b * f' b) t₀ := by
    intro a b
    have h := (hasDerivAt_const t₀ (M a b)).mul (hf_a b)
    simp only [zero_mul, zero_add] at h; exact h
  -- Per-summand product rule: d/dt [conj(f_a) · (M_{ab} · f_b)]
  have h_term : ∀ a b, HasDerivAt
      (fun t => starRingEnd ℂ (f t a) * (M a b * f t b))
      (starRingEnd ℂ (f' a) * (M a b * f t₀ b) +
       starRingEnd ℂ (f t₀ a) * (M a b * f' b)) t₀ :=
    fun a b => (hf_star a).mul (h_Mf a b)
  -- Double sum: HasDerivAt distributes over finite sums
  have h_sum : HasDerivAt
      (fun t => ∑ a, ∑ b, starRingEnd ℂ (f t a) * (M a b * f t b))
      (∑ a, ∑ b, (starRingEnd ℂ (f' a) * (M a b * f t₀ b) +
                   starRingEnd ℂ (f t₀ a) * (M a b * f' b))) t₀ := by
    have := HasDerivAt.sum fun a (_ : a ∈ Finset.univ) =>
      HasDerivAt.sum fun b (_ : b ∈ Finset.univ) => h_term a b
    simp only [← Finset.sum_fn] at this
    exact this
  -- Rewrite function body: double sum = star(f t) ⬝ᵥ M.mulVec(f t)
  have h_fn : ∀ t, (∑ a, ∑ b, starRingEnd ℂ (f t a) * (M a b * f t b)) =
      star (f t) ⬝ᵥ M.mulVec (f t) := by
    intro t
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum]
  -- Rewrite derivative: split ∑(A+B) = ∑A + ∑B, then each is a ⬝ᵥ
  have h_deriv :
      (∑ a, ∑ b, (starRingEnd ℂ (f' a) * (M a b * f t₀ b) +
                   starRingEnd ℂ (f t₀ a) * (M a b * f' b))) =
      star f' ⬝ᵥ M.mulVec (f t₀) + star (f t₀) ⬝ᵥ M.mulVec f' := by
    simp_rw [Finset.sum_add_distrib]
    congr 1 <;> {
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum]
    }
  -- Assemble: rewrite both parts of h_sum
  simp_rw [h_fn] at h_sum
  rwa [h_deriv] at h_sum

/-- Product rule for the current bilinear form.
    ∂_μ(ψ†γ⁰γ^μψ) = (∂_μψ)†γ⁰γ^μψ + ψ†γ⁰γ^μ(∂_μψ) -/
lemma current_divergence_product_rule (Γ : GammaMatrices)
    (ψ : Spacetime → Fin 4 → ℂ) (x : Spacetime)
    (hψ : ∀ a, DifferentiableAt ℝ (fun y => ψ y a) x) :
    fourDivergence (fun y => diracCurrent Γ (ψ y)) x =
    ∑ μ : Fin 4,
      (star (partialDeriv' μ ψ x) ⬝ᵥ (Γ.gamma 0 * Γ.gamma μ).mulVec (ψ x) +
       star (ψ x) ⬝ᵥ (Γ.gamma 0 * Γ.gamma μ).mulVec (partialDeriv' μ ψ x)) := by
  unfold fourDivergence
  congr 1; ext μ
  -- Step 1: Rewrite diracCurrent as bilinear form
  simp_rw [diracCurrent_eq_dotProduct_mulVec]
  -- Step 2: Per-component HasDerivAt for ψ ∘ update
  have h_comp_a : ∀ a, HasDerivAt (fun t => ψ (Function.update x μ t) a)
      (partialDeriv' μ ψ x a) (x μ) := by
    intro a
    unfold partialDeriv'
    have h_base : Function.update x μ (x μ) = x := Function.update_eq_self μ x
    have h_fderiv : HasFDerivAt (fun y => ψ y a)
        (fderiv ℝ (fun y => ψ y a) x) (Function.update x μ (x μ)) := by
      rw [h_base]; exact (hψ a).hasFDerivAt
    have h_chain := h_fderiv.comp_hasDerivAt (x μ) (hasDerivAt_update x μ)
    have h_eq : (fun y => ψ y a) ∘ Function.update x μ =
        fun t => ψ (Function.update x μ t) a := rfl
    rw [h_eq] at h_chain
    exact h_chain
  -- Step 3: Package into Fin 4 → ℂ valued HasDerivAt
  have h_comp : HasDerivAt (fun t => ψ (Function.update x μ t))
      (partialDeriv' μ ψ x) (x μ) :=
    hasDerivAt_pi.mpr h_comp_a
  -- Step 4: Bilinear product rule
  have h_bilinear := hasDerivAt_bilinear_self (Γ.gamma 0 * Γ.gamma μ)
    (fun t => ψ (Function.update x μ t)) (partialDeriv' μ ψ x) (x μ) h_comp
  -- Step 5: Simplify update x μ (x μ) = x in the derivative value
  simp only [Fin.isValue, Function.update_eq_self] at h_bilinear
  -- Step 6: Extract deriv from HasDerivAt
  exact h_bilinear.deriv

/-- Sum in first argument of dotProduct: (∑ uᵢ) ⬝ᵥ v = ∑ (uᵢ ⬝ᵥ v). -/
lemma finset_sum_dotProduct {ι : Type*} {s : Finset ι}
    (f : ι → Fin 4 → ℂ) (v : Fin 4 → ℂ) :
    (∑ i ∈ s, f i) ⬝ᵥ v = ∑ i ∈ s, f i ⬝ᵥ v := by
  simp_rw [dotProduct, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

/-- Sum in second argument of dotProduct: u ⬝ᵥ (∑ vᵢ) = ∑ (u ⬝ᵥ vᵢ). -/
lemma dotProduct_finset_sum {ι : Type*} {s : Finset ι}
    (u : Fin 4 → ℂ) (f : ι → Fin 4 → ℂ) :
    u ⬝ᵥ (∑ i ∈ s, f i) = ∑ i ∈ s, u ⬝ᵥ f i := by
  simp_rw [dotProduct, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

/-- mulVec distributes over finite sums: M(∑ vᵢ) = ∑ M(vᵢ). -/
lemma mulVec_finset_sum {ι : Type*} {s : Finset ι}
    (M : Matrix (Fin 4) (Fin 4) ℂ) (f : ι → Fin 4 → ℂ) :
    M.mulVec (∑ i ∈ s, f i) = ∑ i ∈ s, M.mulVec (f i) := by
  simpa only [Matrix.mulVecLin_apply] using map_sum M.mulVecLin f s

/-- **Current conservation** (real mass): ∂_μj^μ = 0. -/
theorem dirac_current_conserved (Γ : GammaMatrices) (ψ : SpinorField) (m : ℝ)
    (h_dirac : ∀ x, ∑ μ : Fin 4,
      I • (Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x) = (↑m : ℂ) • ψ.ψ x)
    (h_diff : ∀ x a, DifferentiableAt ℝ (fun y => ψ.ψ y a) x) :
    ∀ x, fourDivergence (fun y => diracCurrent Γ (ψ.ψ y)) x = 0 := by
  intro x
  -- Step 1: Product rule decomposition
  rw [current_divergence_product_rule Γ ψ.ψ x (h_diff x)]
  -- Step 2: Name w = ∑_μ γ^μ(∂_μψ)
  set w := ∑ μ : Fin 4, (Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x) with hw
  -- Step 3: Split ∑(a+b) = ∑a + ∑b
  rw [Finset.sum_add_distrib]
  -- Step 4: Left sum → star(w) ⬝ᵥ γ⁰(ψ)
  --   per-μ adjoint transfer, then collect sum through star and ⬝ᵥ
  have h_left : ∑ μ : Fin 4, star (partialDeriv' μ ψ.ψ x) ⬝ᵥ
      (Γ.gamma 0 * Γ.gamma μ).mulVec (ψ.ψ x) =
      star w ⬝ᵥ (Γ.gamma 0).mulVec (ψ.ψ x) := by
    simp_rw [current_adjoint_transfer]
    rw [← finset_sum_dotProduct, ← star_sum]
  -- Step 5: Right sum → star(ψ) ⬝ᵥ γ⁰(w)
  --   factor γ⁰γ^μ via mulVec_mulVec, then collect through ⬝ᵥ and mulVec
  have h_right : ∑ μ : Fin 4, star (ψ.ψ x) ⬝ᵥ
      (Γ.gamma 0 * Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x) =
      star (ψ.ψ x) ⬝ᵥ (Γ.gamma 0).mulVec w := by
    simp_rw [← Matrix.mulVec_mulVec]
    rw [← dotProduct_finset_sum, ← mulVec_finset_sum]
  -- Step 6: Dirac equation gives I • w = m • ψ(x)
  have h_eq : I • w = (↑m : ℂ) • ψ.ψ x := by
    rw [hw, Finset.smul_sum]; exact h_dirac x
  -- Step 7: Mass cancellation
  rw [h_left, h_right]
  exact dirac_divergence_bilinear_vanishes Γ m (ψ.ψ x) w h_eq

end Spectra.QuantumMechanics.Dirac.Conservation
