/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Uncertainty.SchrodingerRobertson
import Spectra.InformationGeometry.CramerRao.Quantum
import Spectra.Operator.SelfAdjoint
/-!
# Composite Symmetric Operators and the Quantum–Geometric Bridge

The **composite** `O_v = ∑ᵢ vᵢ Oᵢ` contracts a real tangent vector
`v ∈ ℝⁿ` against a family of symmetric operators.  It is the quantum
object corresponding to a *directional score* in information geometry:
just as `⟨v, s(θ,ω)⟩ = ∑ vᵢ sᵢ` probes the statistical manifold in
direction `v`, the composite `O_v` probes the quantum state in
direction `v` through the operator algebra.

The central results are three bilinearity lemmas:

1. `covariance_composite` — `Cov(O_v, O_w) = ∑ᵢⱼ vᵢ wⱼ Cov(Oᵢ, Oⱼ)`
2. `commutator_im_composite` — `Im⟨ψ,[O_v,O_w]ψ⟩ = ∑ᵢⱼ vᵢ wⱼ Im⟨ψ,[Oᵢ,Oⱼ]ψ⟩`
3. `variance_composite` — `Var(O_v) = ∑ᵢⱼ vᵢ vⱼ Cov(Oᵢ, Oⱼ)`

These establish that the covariance matrix is a genuine bilinear form
on tangent vectors (the **Riemannian metric** / SLD Fisher information)
and the commutator expectation matrix a genuine 2-form (the
**symplectic form**).

## Why `SymmetricOperator`, not `SelfAdjointOperator`

The composite of genuinely self-adjoint operators is *symmetric* but in
general **not** self-adjoint: a real linear combination `∑ vᵢ Oᵢ` of
unbounded self-adjoint operators on a common dense domain can fail even
essential self-adjointness (Nelson's example; Reed–Simon VIII.6).
Bundling it as a `SelfAdjointOperator` under the refactored definition
(`A† = A` including the domain equality) would therefore be an
unjustified claim.

Fortunately the claim is never needed: the Schrödinger inequality and
both bilinearity reductions hold at `SymmetricOperator` generality —
exactly the level at which `Uncertainty/Schrodinger.lean` states them.
So the composite is constructed here as a `SymmetricOperator`, the
*minimal hypothesis* for everything downstream, and `QuantumRLDData`
stores symmetric operators.  Physics-facing users with genuine
observables enter through `QuantumRLDData.ofObservables`, which applies
the (definitional) coercion `toSymmetricOperator` componentwise.

The key data structure `QuantumRLDData` bundles a family of `n`
operators with a common invariant domain — the quantum analogue of a
regular statistical model.  The invariant domain condition
`∀ i j, Oⱼψ ∈ dom(Oᵢ)` ensures that all pairwise products, commutators,
and composites are well-defined on the state `ψ`: the minimal
regularity making the Fisher metric finite and the Schrödinger bound
meaningful.

## Design notes

The bilinearity proofs reduce composite-level identities (Schrödinger
applied to `O_v, O_w`) to sums over pairwise identities (Schrödinger
applied to `Oᵢ, Oⱼ`).  The reduction passes through
`inner_shifted_composite`, which decomposes `⟨Õ_v ψ, Õ_w ψ⟩` as a
double sum, then takes real and imaginary parts separately.

This mirrors the classical proof that the Fisher matrix is the Hessian
of the KL divergence.  The quantum novelty is that the form is
*complex-valued*, and its imaginary part — invisible classically —
carries the symplectic structure responsible for uncertainty.

## References

* S. Amari, *Information Geometry and Its Applications*, §2.2, 2016.
* A. S. Holevo, *Probabilistic and Statistical Aspects of Quantum
  Theory*, North-Holland, 1982.
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I*,
  §VIII.6 — sums of unbounded self-adjoint operators.
-/
open Spectra.Operator
open Spectra.QuantumMechanics.Schrodinger
open Spectra.InformationGeometry
open SymmetricOperator
open InnerProductSpace
open scoped ComplexConjugate

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.QuantumMechanics.Composite

/-- Membership in `⨅ᵢ dom(Oᵢ)` gives membership in each `dom(Oᵢ)`. -/
private lemma mem_of_mem_iInf {O : Fin n → SymmetricOperator H} {x : H}
    (hx : x ∈ ⨅ i, (O i).domain) (i : Fin n) : x ∈ (O i).domain :=
  iInf_le (fun i => (O i).domain) i hx

/-- Membership in every `dom(Oᵢ)` gives membership in `⨅ᵢ dom(Oᵢ)`. -/
private lemma mem_iInf_of_forall {O : Fin n → SymmetricOperator H} {x : H}
    (hx : ∀ i, x ∈ (O i).domain) : x ∈ ⨅ i, (O i).domain := by
  rw [← SetLike.mem_coe, Submodule.coe_iInf]
  exact Set.mem_iInter.mpr hx

/-- The **composite symmetric operator** `O_v = ∑ᵢ vᵢ · Oᵢ`, defined on
`⋂ᵢ dom(Oᵢ)`.

This is the quantum analogue of contracting a tangent vector `v ∈ T_θΘ`
against a family of operators.  The coefficients are *real* to preserve
symmetry: `⟨O_v ψ, φ⟩ = ∑ vᵢ ⟨Oᵢψ, φ⟩ = ∑ vᵢ ⟨ψ, Oᵢφ⟩ = ⟨ψ, O_v φ⟩`.

Note: even for self-adjoint `Oᵢ` the composite is only symmetric in
general, which is all the uncertainty machinery requires. -/
noncomputable def compositeSymmetric
    (O : Fin n → SymmetricOperator H) (v : Fin n → ℝ)
    (h_dense : Dense ((⨅ i, (O i).domain : Submodule ℂ H) : Set H)) :
    SymmetricOperator H where
  toLinearPMap :=
    { domain := ⨅ i, (O i).domain
      toFun := ∑ i : Fin n, ((v i : ℝ) : ℂ) •
        ((O i).toLinearPMap.toFun.comp
          (Submodule.inclusion (iInf_le (fun i => (O i).domain) i))) }
  dense := h_dense
  symmetric := fun ⟨ψ, hψ⟩ ⟨φ, hφ⟩ => by
    simp only [LinearPMap.mk_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.comp_apply]
    rw [sum_inner, inner_sum]
    congr 1; ext i
    simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    congr 1
    exact (O i).symmetric
      ⟨ψ, iInf_le (fun i => (O i).domain) i hψ⟩
      ⟨φ, iInf_le (fun i => (O i).domain) i hφ⟩

/-- The composite applied to `φ` decomposes as a sum. -/
lemma compositeSymmetric_apply
    (O : Fin n → SymmetricOperator H) (v : Fin n → ℝ)
    (h_dense : Dense ((⨅ i, (O i).domain : Submodule ℂ H) : Set H))
    (φ : H) (hφ : φ ∈ ⨅ i, (O i).domain) :
    (compositeSymmetric O v h_dense).apply φ hφ =
    ∑ i : Fin n, ((v i : ℝ) : ℂ) • (O i).apply φ (mem_of_mem_iInf hφ i) := by
  simp only [compositeSymmetric, apply, LinearPMap.mk_apply]
  exact LinearMap.sum_apply Finset.univ _
    (⟨φ, hφ⟩ : (⨅ i, (O i).domain : Submodule ℂ H))

/-- Bundled quantum data for constructing the RLD Fisher model.

This packages a family of `n` symmetric operators, a normalized state
`ψ`, and the mutual domain conditions ensuring that all pairwise
commutators and composites are well-defined on `ψ`.

The key condition `hOψ_all` says that `ψ` sits in a *common invariant
domain* for all operators — the quantum analogue of regularity.

For genuinely self-adjoint observables, use `ofObservables`. -/
structure QuantumRLDData (n : ℕ) (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  O : Fin n → SymmetricOperator H
  ψ : H
  h_norm : ‖ψ‖ = 1
  hψ_all : ∀ i, ψ ∈ (O i).domain
  /-- `Oⱼψ ∈ dom(Oᵢ)` for all `i, j`: the invariant domain condition. -/
  hOψ_all : ∀ i j, (O j).apply ψ (hψ_all j) ∈ (O i).domain
  h_dense : Dense ((⨅ i, (O i).domain : Submodule ℂ H) : Set H)

namespace QuantumRLDData

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The physics-facing constructor: build `QuantumRLDData` from a family
of genuinely self-adjoint observables.  Since `toSymmetricOperator`
preserves the underlying `LinearPMap` definitionally, all domain
conditions transport unchanged. -/
def ofObservables (O : Fin n → SelfAdjointOperator H) (ψ : H)
    (h_norm : ‖ψ‖ = 1)
    (hψ_all : ∀ i, ψ ∈ (O i).domain)
    (hOψ_all : ∀ i j,
      (O j).toSymmetricOperator.apply ψ (hψ_all j) ∈ (O i).domain)
    (h_dense : Dense ((⨅ i, (O i).domain : Submodule ℂ H) : Set H)) :
    QuantumRLDData n H where
  O := fun i => (O i).toSymmetricOperator
  ψ := ψ
  h_norm := h_norm
  hψ_all := hψ_all
  hOψ_all := hOψ_all
  h_dense := h_dense

variable (D : QuantumRLDData n H)

/-- Abbreviation for the common domain `⋂ᵢ dom(Oᵢ)`. -/
def commonDomain : Submodule ℂ H := ⨅ i, (D.O i).domain

/-- `ψ ∈ ⋂ᵢ dom(Oᵢ)`. -/
lemma ψ_mem_commonDomain : D.ψ ∈ D.commonDomain :=
  mem_iInf_of_forall D.hψ_all

/-- `O_w ψ = ∑ⱼ wⱼ Oⱼψ` lies in the common domain. -/
lemma compositeApply_mem_commonDomain (w : Fin n → ℝ) :
    (compositeSymmetric D.O w D.h_dense).apply D.ψ
      D.ψ_mem_commonDomain ∈ D.commonDomain := by
  rw [compositeSymmetric_apply]
  apply mem_iInf_of_forall; intro i
  apply Submodule.sum_mem; intro j _
  exact Submodule.smul_mem _ _ (D.hOψ_all i j)

/-- `DomainConditions` for `[O_v, O_w]ψ`, derived from `QuantumRLDData`. (Currently unused.) -/
theorem composites_domainConditions (v w : Fin n → ℝ) :
    DomainConditions (compositeSymmetric D.O v D.h_dense)
                     (compositeSymmetric D.O w D.h_dense) D.ψ where
  hψ_A := D.ψ_mem_commonDomain
  hψ_B := D.ψ_mem_commonDomain
  hBψ_A := D.compositeApply_mem_commonDomain w
  hAψ_B := D.compositeApply_mem_commonDomain v

/-- `ShiftedDomainConditions` for `O_v, O_w` — ready to feed
into `schrodinger_uncertainty`. -/
theorem composites_shiftedDC (v w : Fin n → ℝ) :
    ShiftedDomainConditions
      (compositeSymmetric D.O v D.h_dense)
      (compositeSymmetric D.O w D.h_dense) D.ψ where
  hψ_A := D.ψ_mem_commonDomain
  hψ_B := D.ψ_mem_commonDomain
  hBψ_A := D.compositeApply_mem_commonDomain w
  hAψ_B := D.compositeApply_mem_commonDomain v
  h_norm := D.h_norm

/-- Pairwise `DomainConditions` for `[Oᵢ, Oⱼ]ψ`. (Currently unused.) -/
theorem pairwise_domainConditions (i j : Fin n) :
    DomainConditions (D.O i) (D.O j) D.ψ where
  hψ_A := D.hψ_all i
  hψ_B := D.hψ_all j
  hBψ_A := D.hOψ_all i j
  hAψ_B := D.hOψ_all j i

end QuantumRLDData

/-- Expectation of the composite decomposes linearly:
  `⟨O_v⟩_ψ = ∑ᵢ vᵢ ⟨Oᵢ⟩_ψ`. -/
lemma expectation_composite (D : QuantumRLDData n H) (v : Fin n → ℝ) :
    (compositeSymmetric D.O v D.h_dense).expectation D.ψ D.h_norm
      D.ψ_mem_commonDomain =
    ∑ i : Fin n, v i * (D.O i).expectation D.ψ D.h_norm (D.hψ_all i) := by
  unfold expectation
  rw [compositeSymmetric_apply]
  rw [inner_sum]
  rw [Complex.re_sum]
  congr 1; ext i
  rw [inner_smul_right]
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im]
  rw [(D.O i).inner_self_eq_re (D.hψ_all i)]
  simp

/-- The shifted composite decomposes as a sum of shifted components:
  `(O_v - ⟨O_v⟩)ψ = ∑ᵢ vᵢ (Oᵢ - ⟨Oᵢ⟩)ψ`. -/
lemma shiftedApply_composite (D : QuantumRLDData n H) (v : Fin n → ℝ) :
    (compositeSymmetric D.O v D.h_dense).shiftedApply
      D.ψ D.ψ D.h_norm D.ψ_mem_commonDomain D.ψ_mem_commonDomain =
    ∑ i : Fin n, ((v i : ℝ) : ℂ) •
      (D.O i).shiftedApply D.ψ D.ψ D.h_norm (D.hψ_all i) (D.hψ_all i) := by
  unfold shiftedApply
  rw [compositeSymmetric_apply]
  rw [expectation_composite]
  simp only [smul_sub, Finset.sum_sub_distrib]
  congr 1
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.coe_smul]
  rw [Finset.sum_smul]
  congr 1; ext i
  simp only [smul_smul]
  rw [← Complex.ofReal_mul]
  exact Complex.coe_smul (v i * (D.O i).expectation D.ψ D.h_norm (D.hψ_all i)) D.ψ

/-- The inner product of shifted composites decomposes as a double sum:
  `⟨Õ_v ψ, Õ_w ψ⟩ = ∑ᵢⱼ vᵢwⱼ ⟨Õᵢψ, Õⱼψ⟩`. -/
lemma inner_shifted_composite (D : QuantumRLDData n H) (v w : Fin n → ℝ) :
    ⟪(compositeSymmetric D.O v D.h_dense).shiftedApply
        D.ψ D.ψ D.h_norm D.ψ_mem_commonDomain D.ψ_mem_commonDomain,
      (compositeSymmetric D.O w D.h_dense).shiftedApply
        D.ψ D.ψ D.h_norm D.ψ_mem_commonDomain D.ψ_mem_commonDomain⟫_ℂ =
    ∑ i : Fin n, ∑ j : Fin n,
      ((v i : ℝ) : ℂ) * ((w j : ℝ) : ℂ) *
      ⟪(D.O i).shiftedApply D.ψ D.ψ D.h_norm (D.hψ_all i) (D.hψ_all i),
        (D.O j).shiftedApply D.ψ D.ψ D.h_norm (D.hψ_all j) (D.hψ_all j)⟫_ℂ := by
  rw [shiftedApply_composite, shiftedApply_composite]
  rw [sum_inner]
  congr 1; ext i
  rw [inner_smul_left, inner_sum]
  rw [Finset.mul_sum]
  congr 1; ext j
  rw [inner_smul_right, Complex.conj_ofReal]
  ring

/-- Pairwise `ShiftedDomainConditions` for `Oᵢ, Oⱼ` — ready to feed
into the Schrödinger inequality. -/
theorem pairwise_shiftedDC (D : QuantumRLDData n H) (i j : Fin n) :
    ShiftedDomainConditions (D.O i) (D.O j) D.ψ where
  hψ_A := D.hψ_all i
  hψ_B := D.hψ_all j
  hBψ_A := D.hOψ_all i j
  hAψ_B := D.hOψ_all j i
  h_norm := D.h_norm

/-- Covariance of composites is bilinear:
  `Cov(O_v, O_w)_ψ = ∑ᵢⱼ vᵢwⱼ Cov(Oᵢ, Oⱼ)_ψ`. -/
lemma covariance_composite (D : QuantumRLDData n H) (v w : Fin n → ℝ) :
    covariance (compositeSymmetric D.O v D.h_dense)
               (compositeSymmetric D.O w D.h_dense)
               D.ψ (D.composites_shiftedDC v w) =
    ∑ i : Fin n, ∑ j : Fin n,
      v i * w j * covariance (D.O i) (D.O j) D.ψ
        (pairwise_shiftedDC D i j) := by
  rw [← re_inner_shifted_eq_covariance]
  simp only [ShiftedDomainConditions.A'ψ, ShiftedDomainConditions.B'ψ]
  rw [inner_shifted_composite]
  rw [Complex.re_sum]
  congr 1; ext i
  rw [Complex.re_sum]
  congr 1; ext j
  rw [← re_inner_shifted_eq_covariance]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
             mul_zero, sub_zero]
  ring_nf
  simp_all only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
    add_zero, sub_zero, mul_eq_mul_left_iff, mul_eq_zero]
  apply Or.inl
  rfl

/-- The imaginary part of the commutator expectation of composites is bilinear:
  `Im⟨ψ,[O_v,O_w]ψ⟩ = ∑ᵢⱼ vᵢwⱼ Im⟨ψ,[Oᵢ,Oⱼ]ψ⟩`. -/
lemma commutator_im_composite (D : QuantumRLDData n H) (v w : Fin n → ℝ) :
    (⟪D.ψ, commutatorAt
      (compositeSymmetric D.O v D.h_dense)
      (compositeSymmetric D.O w D.h_dense)
      D.ψ (D.composites_shiftedDC v w).toDomainConditions⟫_ℂ).im =
    ∑ i : Fin n, ∑ j : Fin n,
      v i * w j *
      (⟪D.ψ, commutatorAt (D.O i) (D.O j) D.ψ
        (pairwise_shiftedDC D i j).toDomainConditions⟫_ℂ).im := by
  have h_lhs := im_inner_shifted_eq_half_commutator
    (compositeSymmetric D.O v D.h_dense)
    (compositeSymmetric D.O w D.h_dense)
    D.ψ (D.composites_shiftedDC v w)
  have h_decomp : (⟪(compositeSymmetric D.O v D.h_dense).shiftedApply
      D.ψ D.ψ D.h_norm D.ψ_mem_commonDomain D.ψ_mem_commonDomain,
    (compositeSymmetric D.O w D.h_dense).shiftedApply
      D.ψ D.ψ D.h_norm D.ψ_mem_commonDomain D.ψ_mem_commonDomain⟫_ℂ).im =
    ∑ i : Fin n, ∑ j : Fin n,
      v i * w j *
      (⟪(D.O i).shiftedApply D.ψ D.ψ D.h_norm (D.hψ_all i) (D.hψ_all i),
        (D.O j).shiftedApply D.ψ D.ψ D.h_norm (D.hψ_all j) (D.hψ_all j)⟫_ℂ).im := by
    rw [inner_shifted_composite]
    rw [Complex.im_sum]
    congr 1; ext i
    rw [Complex.im_sum]
    congr 1; ext j
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
        add_zero, Complex.mul_re, sub_zero]
  simp only [ShiftedDomainConditions.A'ψ, ShiftedDomainConditions.B'ψ] at h_lhs
  have h_ij (i j : Fin n) :=
    im_inner_shifted_eq_half_commutator (D.O i) (D.O j) D.ψ (pairwise_shiftedDC D i j)
  have h_decomp' : (⟪(compositeSymmetric D.O v D.h_dense).shiftedApply
      D.ψ D.ψ D.h_norm D.ψ_mem_commonDomain D.ψ_mem_commonDomain,
    (compositeSymmetric D.O w D.h_dense).shiftedApply
      D.ψ D.ψ D.h_norm D.ψ_mem_commonDomain D.ψ_mem_commonDomain⟫_ℂ).im =
    ∑ i : Fin n, ∑ j : Fin n,
      v i * w j * (1/2 *
        (⟪D.ψ, commutatorAt (D.O i) (D.O j) D.ψ
          (pairwise_shiftedDC D i j).toDomainConditions⟫_ℂ).im) := by
    rw [h_decomp]
    congr 1; ext i; congr 1; ext j
    exact Real.ext_cauchy (congrArg Real.cauchy
      (congrArg (HMul.hMul (v i * w j)) (h_ij i j)))
  have h_half_ne : (1/2 : ℝ) ≠ 0 := by norm_num
  have h_combined : 1/2 * (⟪D.ψ, commutatorAt
      (compositeSymmetric D.O v D.h_dense)
      (compositeSymmetric D.O w D.h_dense)
      D.ψ (D.composites_shiftedDC v w).toDomainConditions⟫_ℂ).im =
    1/2 * ∑ i : Fin n, ∑ j : Fin n,
      v i * w j * (⟪D.ψ, commutatorAt (D.O i) (D.O j) D.ψ
        (pairwise_shiftedDC D i j).toDomainConditions⟫_ℂ).im := by
    rw [← h_lhs, h_decomp']
    ring_nf
    rw [Finset.sum_mul]
    congr 1; ext i
    rw [← Finset.sum_mul]
  linarith [mul_left_cancel₀ h_half_ne h_combined]

/-- Variance equals self-covariance: `Var(A) = Cov(A,A)`. (Currently unused.) -/
lemma variance_eq_covariance_self (D : QuantumRLDData n H) (i : Fin n) :
    (D.O i).variance D.ψ D.h_norm (D.hψ_all i) =
    covariance (D.O i) (D.O i) D.ψ (pairwise_shiftedDC D i i) := by
  unfold variance
  rw [← re_inner_shifted_eq_covariance]
  simp only [ShiftedDomainConditions.A'ψ, ShiftedDomainConditions.B'ψ]
  rw [inner_self_eq_norm_sq_to_K]
  simp only [Complex.coe_algebraMap]
  norm_cast

/-- Variance of the composite is bilinear:
  `Var(O_v) = ∑ᵢⱼ vᵢvⱼ Cov(Oᵢ,Oⱼ)`. -/
lemma variance_composite (D : QuantumRLDData n H) (v : Fin n → ℝ) :
    (compositeSymmetric D.O v D.h_dense).variance D.ψ D.h_norm
      D.ψ_mem_commonDomain =
    ∑ i : Fin n, ∑ j : Fin n,
      v i * v j * covariance (D.O i) (D.O j) D.ψ
        (pairwise_shiftedDC D i j) := by
  have h_var_cov : (compositeSymmetric D.O v D.h_dense).variance D.ψ D.h_norm
      D.ψ_mem_commonDomain =
    covariance (compositeSymmetric D.O v D.h_dense)
               (compositeSymmetric D.O v D.h_dense)
               D.ψ (D.composites_shiftedDC v v) := by
    unfold variance
    rw [← re_inner_shifted_eq_covariance]
    simp only [ShiftedDomainConditions.A'ψ, ShiftedDomainConditions.B'ψ]
    rw [inner_self_eq_norm_sq_to_K]
    simp only [Complex.coe_algebraMap]
    norm_cast
  rw [h_var_cov, covariance_composite]

end Spectra.QuantumMechanics.Composite
