/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.OneParameterUnitaryGroup.Basic
import Spectra.YosidaHille.Basic
import Spectra.Operator.SelfAdjoint
import Spectra.Resolvent.Defs
import Spectra.Resolvent.NormExpansion
import Spectra.Resolvent.Range
import Spectra.SpectralTheory.StoneFormula.Identities

/-!
# The Kato–Rellich Theorem

If `A` is self-adjoint and `V` is symmetric on `Dom A` with relative bound
`a < 1`, i.e.

  `‖V ψ‖ ≤ a * ‖A ψ‖ + b * ‖ψ‖`   for all `ψ ∈ Dom A`,

then `A + V` is self-adjoint on `Dom A` (no domain shrinkage).  This is the
mathematical engine of perturbation theory in quantum mechanics: "small"
perturbations of a Hamiltonian preserve self-adjointness, hence unitary time
evolution and conservation of probability.

The paradigmatic application is hydrogen:
- `A = −Δ` (self-adjoint on `H²(ℝ³)`),
- `V = −Z/r` (Coulomb; infinitesimally small relative to `−Δ` by Hardy),
- `A + V` = hydrogen Hamiltonian, self-adjoint on `H²(ℝ³)`.

## Design

A perturbation of `A : H →ₗ.[ℂ] H` is a *bounded-domain* linear map
`V : A.domain →ₗ[ℂ] H` (not necessarily continuous).  The sum is

  `perturbedOp A V : H →ₗ.[ℂ] H`,   with the **same** `domain` field as `A`,

so `(perturbedOp A V).domain = A.domain` holds by `rfl` — the "no domain
shrinkage" clause of Kato–Rellich is definitional in this encoding, and all
self-adjointness statements use Mathlib's star-based `IsSelfAdjoint` on
`LinearPMap`, matching the refactored Stone library.

## Proof architecture

We verify von Neumann's criterion at height `η` rather than at `±i`:

1. `isSelfAdjoint_of_surjective_addSub_smul`: a densely defined symmetric `B`
   with `ran (B + iμ) = ran (B − iμ) = H` (`μ : ℝ`) is self-adjoint.  This is
   the library's criterion `isSelfAdjoint_of_surjective_addSub` with `i`
   replaced by `iμ`; the proof is the same computation.
2. For purely imaginary `z = ±iη` the resolvent `R = (A − z)⁻¹` of the
   *unperturbed* operator satisfies the Pythagoras identity
   `‖χ‖² = ‖A(Rχ)‖² + η²‖Rχ‖²`  (`norm_sq_sub_smul_of_symmetric` +
   `resolvent_solves`), whence

     `‖A (R χ)‖ ≤ ‖χ‖`   and   `‖R χ‖ ≤ ‖χ‖ / η`.

3. Therefore `W := V ∘ R` is bounded with `‖W‖ ≤ a + b/η`, which is `< 1`
   for `η := (b + 1)/(1 − a)`.  The Neumann series inverts `1 + W`, and

     `(A + V − z) (R χ) = χ + W χ`

   shows `A + V − z` is surjective for `z = ±iη`.  Apply step 1.

## Main definitions

* `perturbedOp A V` — the operator sum `A + V` on `Dom A`.
* `IsRelativelyBounded A V` — bundled witnesses `a`, `b` for the relative
  bound; `relativeBound A V hV` is the infimum of admissible `a`.
* `IsSymmetricOn A V` — symmetry of `V` against the inner product on `Dom A`.

## Main statements

* `kato_rellich` — the theorem, with explicit constants `a < 1`, `b`.
* `kato_rellich'` — packaged via `IsRelativelyBounded`.
* `kato_rellich_bounded` — bounded self-adjoint perturbations (`a = 0`).
* `kato_rellich_bound_zero` — relative bound `0` allows any real coupling
  `lam`; this is the form consumed by the hydrogen Hamiltonian, where the
  Coulomb potential has `−Δ`-bound `0` by Hardy's inequality.
* `kato_rellich_generates_unitary` — `A + V` generates a unique strongly
  continuous one-parameter unitary group (via Stone).
* `isSelfAdjoint_of_surjective_addSub_smul` — von Neumann's criterion at
  height `μ`, of independent use.

This file is deliberately abstract: it does not import Sobolev spaces.  The
concrete inputs (`IsSelfAdjoint` for `−Δ` on `H²`, the Hardy/Coulomb
estimate) are produced downstream and plugged into `kato_rellich_bound_zero`.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975],
  Theorem X.12 (Kato–Rellich).
* [Kato, *Perturbation Theory for Linear Operators*][kato1966], Thm V.4.3.
* [Hall, *Quantum Theory for Mathematicians*][hall2013], Theorem 9.37.
* [Teschl, *Mathematical Methods in Quantum Mechanics*][teschl2014], §6.5.
-/
open Complex Filter InnerProductSpace
open Spectra.OneParameterUnitaryGroup
open Spectra.YosidaHille
open Spectra.Resolvent
open Spectra.QuantumMechanics.SpectralTheory

namespace Spectra.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The perturbed operator

A perturbation of an unbounded operator `A` is a linear map defined on
`Dom A`.  Its sum with `A` is again a partial linear map with the *same*
domain — so the Kato–Rellich conclusion "self-adjoint **on Dom A**" is
carried by the definition itself. -/

omit [CompleteSpace H] in
/-- The operator sum `A + V` on `Dom A`, as a partial linear map. -/
def perturbedOp (A : H →ₗ.[ℂ] H) (V : A.domain →ₗ[ℂ] H) : H →ₗ.[ℂ] H where
  domain := A.domain
  toFun := A.toFun + V

omit [CompleteSpace H] in
/-- No domain shrinkage: `Dom (A + V) = Dom A`, definitionally. -/
@[simp] lemma perturbedOp_domain (A : H →ₗ.[ℂ] H) (V : A.domain →ₗ[ℂ] H) :
    (perturbedOp A V).domain = A.domain := rfl

omit [CompleteSpace H] in
@[simp] lemma perturbedOp_apply (A : H →ₗ.[ℂ] H) (V : A.domain →ₗ[ℂ] H)
    (ψ : A.domain) :
    perturbedOp A V ψ = A ψ + V ψ := rfl

/-! ## Relative boundedness -/

/-- `V` is relatively bounded with respect to `A` ("`A`-bounded"):
there are constants `a, b ≥ 0` with `‖V ψ‖ ≤ a‖A ψ‖ + b‖ψ‖` on `Dom A`.

`V` is given as a linear map *on* `Dom A` (not on its own domain), which
encodes the Kato condition `Dom A ⊆ Dom V` by construction. -/
structure IsRelativelyBounded (A : H →ₗ.[ℂ] H) (V : A.domain →ₗ[ℂ] H) where
  /-- The relative bound constant `a`. -/
  a : ℝ
  /-- The subordinate constant `b`. -/
  b : ℝ
  /-- `a` is non-negative. -/
  ha : 0 ≤ a
  /-- `b` is non-negative. -/
  hb : 0 ≤ b
  /-- The defining estimate: `‖Vψ‖ ≤ a‖Aψ‖ + b‖ψ‖`. -/
  bound : ∀ ψ : A.domain, ‖V ψ‖ ≤ a * ‖A ψ‖ + b * ‖(ψ : H)‖

omit [CompleteSpace H] in
/-- The relative bound (`A`-bound) of `V`: the infimum of all admissible
slopes `a`.  Kato–Rellich requires this to be `< 1`. -/
noncomputable def relativeBound (A : H →ₗ.[ℂ] H) (V : A.domain →ₗ[ℂ] H)
    (_hV : IsRelativelyBounded A V) : ℝ :=
  sInf { a : ℝ | 0 ≤ a ∧ ∃ b : ℝ, 0 ≤ b ∧
    ∀ ψ : A.domain, ‖V ψ‖ ≤ a * ‖A ψ‖ + b * ‖(ψ : H)‖ }

omit [CompleteSpace H] in
lemma relativeBound_nonneg (A : H →ₗ.[ℂ] H) (V : A.domain →ₗ[ℂ] H)
    (hV : IsRelativelyBounded A V) :
    0 ≤ relativeBound A V hV :=
  le_csInf ⟨hV.a, hV.ha, hV.b, hV.hb, hV.bound⟩ fun _ hx => hx.1

omit [CompleteSpace H] in
lemma relativeBound_le (A : H →ₗ.[ℂ] H) (V : A.domain →ₗ[ℂ] H)
    (hV : IsRelativelyBounded A V) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ ψ : A.domain, ‖V ψ‖ ≤ a * ‖A ψ‖ + b * ‖(ψ : H)‖) :
    relativeBound A V hV ≤ a :=
  csInf_le ⟨0, fun _ hx => hx.1⟩ ⟨ha, b, hb, h⟩

/-! ## Symmetry of perturbations -/

omit [CompleteSpace H] in
/-- `V` is symmetric on `Dom A`: `⟪V ψ, φ⟫ = ⟪ψ, V φ⟫` for `ψ, φ ∈ Dom A`. -/
def IsSymmetricOn (A : H →ₗ.[ℂ] H) (V : A.domain →ₗ[ℂ] H) : Prop :=
  ∀ ψ φ : A.domain, ⟪V ψ, (φ : H)⟫_ℂ = ⟪(ψ : H), V φ⟫_ℂ

omit [CompleteSpace H] in
lemma IsSymmetricOn.add {A : H →ₗ.[ℂ] H} {V W : A.domain →ₗ[ℂ] H}
    (hV : IsSymmetricOn A V) (hW : IsSymmetricOn A W) :
    IsSymmetricOn A (V + W) := by
  intro ψ φ
  rw [LinearMap.add_apply, LinearMap.add_apply, inner_add_left, inner_add_right,
    hV ψ φ, hW ψ φ]

omit [CompleteSpace H] in
/-- Symmetry is preserved by *real* scalar multiples.  (Complex scalars
break symmetry: `⟪c•Vψ, φ⟫ = conj c ⟪Vψ, φ⟫` but `⟪ψ, c•Vφ⟫ = c ⟪ψ, Vφ⟫`.) -/
lemma IsSymmetricOn.real_smul {A : H →ₗ.[ℂ] H} {V : A.domain →ₗ[ℂ] H}
    (hV : IsSymmetricOn A V) (lam : ℝ) :
    IsSymmetricOn A ((lam : ℂ) • V) := by
  intro ψ φ
  rw [LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal, hV ψ φ]

/-- A bounded self-adjoint operator, restricted to `Dom A`, is a symmetric
perturbation. -/
lemma isSymmetricOn_of_selfAdjoint (A : H →ₗ.[ℂ] H) {T : H →L[ℂ] H}
    (hT : IsSelfAdjoint T) :
    IsSymmetricOn A (T.comp (Submodule.subtypeL A.domain)).toLinearMap := by
  intro ψ φ
  change ⟪T (ψ : H), (φ : H)⟫_ℂ = ⟪(ψ : H), T (φ : H)⟫_ℂ
  have h := ContinuousLinearMap.adjoint_inner_right T (ψ : H) (φ : H)
  -- h : ⟪↑ψ, adjoint T ↑φ⟫ = ⟪T ↑ψ, ↑φ⟫
  rw [← ContinuousLinearMap.star_eq_adjoint, hT.star_eq] at h
  exact h.symm

omit [CompleteSpace H] in
/-- A symmetric perturbation of a symmetric operator is symmetric. -/
lemma perturbedOp_isFormalAdjoint {A : H →ₗ.[ℂ] H}
    (hsymA : A.IsFormalAdjoint A) {V : A.domain →ₗ[ℂ] H}
    (hV : IsSymmetricOn A V) :
    (perturbedOp A V).IsFormalAdjoint (perturbedOp A V) := by
  intro ψ φ
  change ⟪A ψ + V ψ, (φ : H)⟫_ℂ = ⟪(ψ : H), A φ + V φ⟫_ℂ
  rw [inner_add_left, inner_add_right, hsymA ψ φ, hV ψ φ]

/-! ## von Neumann's criterion at height `μ`

The library proves the criterion at `±i`
(`OneParameterUnitaryGroup.isSelfAdjoint_of_surjective_addSub`).  The
Kato–Rellich argument needs it at `±iμ` for a *free* parameter `μ`, since
smallness of `V ∘ (A − iμ)⁻¹` is only available for `μ` large.  The proof
below is the library proof with `I` replaced by `I * μ` throughout; the
only new ingredient is `conj (iμ) = −iμ` for real `μ`. -/

/-- **von Neumann's criterion at height `μ`.**  A densely defined symmetric
operator `B` with `ran (B + iμ) = ran (B − iμ) = H` is self-adjoint. -/
lemma isSelfAdjoint_of_surjective_addSub_smul
    (B : H →ₗ.[ℂ] H) (hsym : B.IsFormalAdjoint B)
    (hdense : Dense (B.domain : Set H)) (μ : ℝ)
    (hplus : ∀ φ : H, ∃ ψ : B.domain, B ψ + (I * (μ : ℂ)) • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : B.domain, B ψ - (I * (μ : ℂ)) • (ψ : H) = φ) :
    IsSelfAdjoint B := by
  have hconj : (starRingEnd ℂ) (I * (μ : ℂ)) = -(I * (μ : ℂ)) := by
    simp [map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [LinearPMap.isSelfAdjoint_def]
  refine le_antisymm ?_ (hsym.le_adjoint hdense)
  -- ⊢ B† ≤ B.  First: ker(B† − iμ) = 0, using surjectivity of B + iμ.
  have hker : ∀ w : (B.adjoint).domain,
      B.adjoint w = (I * (μ : ℂ)) • (w : H) → (w : H) = 0 := by
    intro w hw
    obtain ⟨v, hv⟩ := hplus (w : H)        -- hv : B v + iμ•(v:H) = (w:H)
    have hadj : ⟪B.adjoint w, (v : H)⟫_ℂ = ⟪(w : H), B v⟫_ℂ :=
      LinearPMap.adjoint_isFormalAdjoint hdense w v
    rw [hw, inner_smul_left, hconj] at hadj
    -- hadj : -(iμ) * ⟪w,v⟫ = ⟪w, B v⟫
    have key : ⟪(w : H), B v⟫_ℂ + (I * (μ : ℂ)) * ⟪(w : H), (v : H)⟫_ℂ
        = ⟪(w : H), (w : H)⟫_ℂ := by
      rw [← inner_smul_right, ← inner_add_right, hv]
    have hww : ⟪(w : H), (w : H)⟫_ℂ = 0 := by rw [← key, ← hadj]; ring
    exact inner_self_eq_zero.mp hww
  -- Now B† ≤ B via eqLocus.
  apply LinearPMap.le_of_eqLocus_ge
  intro w hw                                -- hw : w ∈ (B.adjoint).domain
  set W : (B.adjoint).domain := ⟨w, hw⟩ with hWdef
  obtain ⟨x, hx⟩ := hminus (B.adjoint W - (I * (μ : ℂ)) • (W : H))
  -- hx : B x - iμ•(x:H) = B† W - iμ•(W:H)
  have hxin : (x : H) ∈ (B.adjoint).domain := (hsym.le_adjoint hdense).1 x.2
  have hxeq : B.adjoint (⟨(x : H), hxin⟩ : (B.adjoint).domain) = B x :=
    ((hsym.le_adjoint hdense).2 (x := x) (y := ⟨(x : H), hxin⟩) rfl).symm
  set W' : (B.adjoint).domain := W - ⟨(x : H), hxin⟩ with hW'def
  have hW'val : (W' : H) = (W : H) - (x : H) := rfl
  have hrearr : B.adjoint W - B x
      = (I * (μ : ℂ)) • (W : H) - (I * (μ : ℂ)) • (x : H) := by
    have h2 : B.adjoint W
        = B x - (I * (μ : ℂ)) • (x : H) + (I * (μ : ℂ)) • (W : H) := by
      rw [hx]; abel
    rw [h2]; abel
  have hAW' : B.adjoint W' = (I * (μ : ℂ)) • (W' : H) := by
    have e1 : B.adjoint W' = B.adjoint W - B x := by
      rw [hW'def, LinearPMap.map_sub, hxeq]
    rw [e1, hrearr, hW'val, smul_sub]
  have hWx : (W : H) = (x : H) := sub_eq_zero.mp (hW'val ▸ hker W' hAW')
  have hwx : w = (x : H) := by
    have hWcoe : (W : H) = w := by rw [hWdef]
    rw [← hWcoe]; exact hWx
  subst hwx
  exact ⟨hw, x.2, hxeq⟩

/-! ## Resolvent estimates

For purely imaginary `z` and `ψ = (A − z)⁻¹ χ`, the symmetric cross terms
cancel and `‖χ‖² = ‖A ψ‖² + ‖z‖²‖ψ‖²`.  Both estimates that power the
Neumann series fall out:  `‖A ψ‖ ≤ ‖χ‖`  and  `‖ψ‖ ≤ ‖χ‖ / |Im z|`. -/

private lemma norm_resolvent_apply_le {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (z : ℂ) (him : z.im ≠ 0) (χ : H) :
    ‖resolvent z him hsym hplus hminus χ‖ ≤ (1 / |z.im|) * ‖χ‖ :=
  ((resolvent z him hsym hplus hminus).le_opNorm χ).trans
    (mul_le_mul_of_nonneg_right (resolvent_bound z him hsym hplus hminus)
      (norm_nonneg χ))

private lemma norm_op_resolvent_le {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (z : ℂ) (hre : z.re = 0) (him : z.im ≠ 0) (χ : H) :
    ‖A ⟨resolvent z him hsym hplus hminus χ,
        resolvent_mem_domain hsym hplus hminus z him χ⟩‖ ≤ ‖χ‖ := by
  -- Pythagoras along the resolvent:  ‖χ‖² = ‖A(Rχ)‖² + ‖z‖²‖Rχ‖².
  have hid2 : ‖χ‖ ^ 2
      = ‖A ⟨resolvent z him hsym hplus hminus χ,
            resolvent_mem_domain hsym hplus hminus z him χ⟩‖ ^ 2
        + ‖z‖ ^ 2 * ‖resolvent z him hsym hplus hminus χ‖ ^ 2 := by
    conv_lhs => rw [← resolvent_solves hsym hplus hminus z him χ]
    exact norm_sq_sub_smul_of_symmetric hsym
      ⟨resolvent z him hsym hplus hminus χ,
       resolvent_mem_domain hsym hplus hminus z him χ⟩ z hre
  have hsq : ‖A ⟨resolvent z him hsym hplus hminus χ,
        resolvent_mem_domain hsym hplus hminus z him χ⟩‖ ^ 2 ≤ ‖χ‖ ^ 2 := by
    have hnn : 0 ≤ ‖z‖ ^ 2 * ‖resolvent z him hsym hplus hminus χ‖ ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith
  calc ‖A ⟨resolvent z him hsym hplus hminus χ,
          resolvent_mem_domain hsym hplus hminus z him χ⟩‖
      = Real.sqrt (‖A ⟨resolvent z him hsym hplus hminus χ,
          resolvent_mem_domain hsym hplus hminus z him χ⟩‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖χ‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖χ‖ := Real.sqrt_sq (norm_nonneg _)

/-- `V ∘ (A − z)⁻¹` as a linear map `H →ₗ H`; the Neumann series will invert
`1 + V ∘ (A − z)⁻¹`. -/
private noncomputable def resolventPerturb {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (V : A.domain →ₗ[ℂ] H) (z : ℂ) (him : z.im ≠ 0) : H →ₗ[ℂ] H :=
  V ∘ₗ LinearMap.codRestrict A.domain
    (resolvent z him hsym hplus hminus).toLinearMap
    (fun χ => resolvent_mem_domain hsym hplus hminus z him χ)

private lemma resolventPerturb_apply {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (V : A.domain →ₗ[ℂ] H) (z : ℂ) (him : z.im ≠ 0) (χ : H) :
    resolventPerturb hsym hplus hminus V z him χ
      = V ⟨resolvent z him hsym hplus hminus χ,
           resolvent_mem_domain hsym hplus hminus z him χ⟩ := rfl

/-- The crucial smallness estimate:
`‖V ∘ (A − z)⁻¹‖ ≤ a + b / |Im z|` for purely imaginary `z`. -/
private lemma resolventPerturb_norm_le {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (V : A.domain →ₗ[ℂ] H) {a b : ℝ} (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b)
    (hbound : ∀ ψ : A.domain, ‖V ψ‖ ≤ a * ‖A ψ‖ + b * ‖(ψ : H)‖)
    (z : ℂ) (hre : z.re = 0) (him : z.im ≠ 0) (χ : H) :
    ‖resolventPerturb hsym hplus hminus V z him χ‖ ≤ (a + b / |z.im|) * ‖χ‖ := by
  rw [resolventPerturb_apply]
  calc ‖V ⟨resolvent z him hsym hplus hminus χ,
           resolvent_mem_domain hsym hplus hminus z him χ⟩‖
      ≤ a * ‖A ⟨resolvent z him hsym hplus hminus χ,
                resolvent_mem_domain hsym hplus hminus z him χ⟩‖
        + b * ‖resolvent z him hsym hplus hminus χ‖ :=
        hbound ⟨resolvent z him hsym hplus hminus χ,
                resolvent_mem_domain hsym hplus hminus z him χ⟩
    _ ≤ a * ‖χ‖ + b * ((1 / |z.im|) * ‖χ‖) :=
        add_le_add
          (mul_le_mul_of_nonneg_left
            (norm_op_resolvent_le hsym hplus hminus z hre him χ) ha₀)
          (mul_le_mul_of_nonneg_left
            (norm_resolvent_apply_le hsym hplus hminus z him χ) hb₀)
    _ = (a + b / |z.im|) * ‖χ‖ := by ring

/-- Solvability of `χ + T χ = φ` for `‖T‖ < 1`, via the library's Neumann
series for `1 − (−T)`. -/
private lemma exists_neumann_solution (T : H →L[ℂ] H) (hT : ‖T‖ < 1)
    (φ : H) : ∃ χ : H, χ + T χ = φ := by
  have hT' : ‖-T‖ < 1 := by rwa [norm_neg]
  refine ⟨neumannSeries (-T) hT' φ, ?_⟩
  have h := congrArg (fun S : H →L[ℂ] H => S φ) (neumannSeries_mul_left (-T) hT')
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply] at h
  -- h : neumannSeries (-T) hT' φ - -(T (neumannSeries (-T) hT' φ)) = φ
  rwa [sub_neg_eq_add] at h

/-! ## Surjectivity of `A + V − z` -/

/-- **The Kato–Rellich workhorse.**  If `‖Vψ‖ ≤ a‖Aψ‖ + b‖ψ‖` and
`z` is purely imaginary with `a + b/|Im z| < 1`, then `A + V − z` maps
`Dom A` *onto* `H`.

Given `φ`, solve `(1 + V R) χ = φ` by Neumann (`R := (A − z)⁻¹`, and
`‖V R‖ ≤ a + b/|Im z| < 1` by the resolvent estimates); then `ψ := R χ`
satisfies `(A + V − z) ψ = (A − z)(Rχ) + V(Rχ) = χ + (V R) χ = φ`. -/
lemma perturbedOp_sub_smul_surjective {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) (V : A.domain →ₗ[ℂ] H)
    {a b : ℝ} (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b)
    (hbound : ∀ ψ : A.domain, ‖V ψ‖ ≤ a * ‖A ψ‖ + b * ‖(ψ : H)‖)
    (z : ℂ) (hre : z.re = 0) (him : z.im ≠ 0)
    (hsmall : a + b / |z.im| < 1) (φ : H) :
    ∃ ψ : A.domain, perturbedOp A V ψ - z • (ψ : H) = φ := by
  have hsym : A.IsFormalAdjoint A := isFormalAdjoint_self_of_isSelfAdjoint hA
  obtain ⟨hplus, hminus⟩ := isSelfAdjoint_to_surjective hA
  have hC₀ : 0 ≤ a + b / |z.im| := add_nonneg ha₀ (div_nonneg hb₀ (abs_nonneg _))
  -- Invert 1 + V∘R by the Neumann series.
  have hWnorm : ‖(resolventPerturb hsym hplus hminus V z him).mkContinuous
      (a + b / |z.im|)
      (resolventPerturb_norm_le hsym hplus hminus V ha₀ hb₀ hbound z hre him)‖
      < 1 :=
    lt_of_le_of_lt (LinearMap.mkContinuous_norm_le _ hC₀ _) hsmall
  obtain ⟨χ, hχ⟩ := exists_neumann_solution _ hWnorm φ
  -- ψ := R χ does it.
  refine ⟨⟨resolvent z him hsym hplus hminus χ,
           resolvent_mem_domain hsym hplus hminus z him χ⟩, ?_⟩
  change A ⟨resolvent z him hsym hplus hminus χ,
          resolvent_mem_domain hsym hplus hminus z him χ⟩
      + V ⟨resolvent z him hsym hplus hminus χ,
           resolvent_mem_domain hsym hplus hminus z him χ⟩
      - z • resolvent z him hsym hplus hminus χ = φ
  calc A ⟨resolvent z him hsym hplus hminus χ,
          resolvent_mem_domain hsym hplus hminus z him χ⟩
      + V ⟨resolvent z him hsym hplus hminus χ,
           resolvent_mem_domain hsym hplus hminus z him χ⟩
      - z • resolvent z him hsym hplus hminus χ
      = (A ⟨resolvent z him hsym hplus hminus χ,
            resolvent_mem_domain hsym hplus hminus z him χ⟩
          - z • resolvent z him hsym hplus hminus χ)
        + V ⟨resolvent z him hsym hplus hminus χ,
             resolvent_mem_domain hsym hplus hminus z him χ⟩ := by abel
    _ = χ + V ⟨resolvent z him hsym hplus hminus χ,
               resolvent_mem_domain hsym hplus hminus z him χ⟩ := by
        rw [resolvent_solves hsym hplus hminus z him χ]
    _ = φ := hχ
  -- (the last step is definitional: `V ⟨Rχ, _⟩ = (V∘R) χ = mkContinuous … χ`)

/-! ## The Kato–Rellich theorem -/

/-- **Kato–Rellich.**  Let `A` be self-adjoint and `V` symmetric on `Dom A`
with

  `‖V ψ‖ ≤ a‖A ψ‖ + b‖ψ‖`,   `0 ≤ a < 1`,  `0 ≤ b`.

Then `A + V` is self-adjoint on `Dom A`.

The height `η := (b + 1)/(1 − a)` makes `a + b/η < 1`, so `A + V ∓ iη` is
surjective by the workhorse, and von Neumann's criterion applies. -/
theorem kato_rellich {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (V : A.domain →ₗ[ℂ] H) (hV_sym : IsSymmetricOn A V)
    {a b : ℝ} (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b) (ha₁ : a < 1)
    (hbound : ∀ ψ : A.domain, ‖V ψ‖ ≤ a * ‖A ψ‖ + b * ‖(ψ : H)‖) :
    IsSelfAdjoint (perturbedOp A V) := by
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hb1 : (0 : ℝ) < b + 1 := by linarith
  -- A height at which the perturbation series converges.
  obtain ⟨η, hη, hsmall⟩ : ∃ η : ℝ, 0 < η ∧ a + b / η < 1 := by
    refine ⟨(b + 1) / (1 - a), div_pos hb1 h1a, ?_⟩
    have hbη : b / ((b + 1) / (1 - a)) = b * (1 - a) / (b + 1) :=
      div_div_eq_mul_div b (b + 1) (1 - a)
    rw [hbη]
    have hlt : b * (1 - a) / (b + 1) < 1 - a := by
      rw [div_lt_iff₀ hb1]   -- on older Mathlib: `div_lt_iff hb1`
      nlinarith
    linarith
  have hIη_re : (I * (η : ℂ)).re = 0 := by simp [Complex.mul_re]
  have hIη_im : (I * (η : ℂ)).im = η := by simp [Complex.mul_im]
  refine isSelfAdjoint_of_surjective_addSub_smul (perturbedOp A V)
    (perturbedOp_isFormalAdjoint (isFormalAdjoint_self_of_isSelfAdjoint hA)
      hV_sym)
    (show Dense ((perturbedOp A V).domain : Set H) from hA.dense_domain)
    η ?_ ?_
  · -- ran (A + V + iη) = H :  take z = −iη in the workhorse.
    intro φ
    have h₂re : (-(I * (η : ℂ))).re = 0 := by simp [Complex.mul_re]
    have h₂im : (-(I * (η : ℂ))).im ≠ 0 := by
      simp only [Complex.neg_im, hIη_im]
      exact neg_ne_zero.mpr (ne_of_gt hη)
    have h₂abs : a + b / |(-(I * (η : ℂ))).im| < 1 := by
      rwa [Complex.neg_im, hIη_im, abs_neg, abs_of_pos hη]
    obtain ⟨ψ, hψ⟩ := perturbedOp_sub_smul_surjective hA V ha₀ hb₀ hbound
      (-(I * (η : ℂ))) h₂re h₂im h₂abs φ
    rw [neg_smul, sub_neg_eq_add] at hψ
    exact ⟨ψ, hψ⟩
  · -- ran (A + V − iη) = H :  take z = +iη.
    intro φ
    have h₂im : (I * (η : ℂ)).im ≠ 0 := by rw [hIη_im]; exact ne_of_gt hη
    have h₂abs : a + b / |(I * (η : ℂ)).im| < 1 := by
      rwa [hIη_im, abs_of_pos hη]
    exact perturbedOp_sub_smul_surjective hA V ha₀ hb₀ hbound
      (I * (η : ℂ)) hIη_re h₂im h₂abs φ

/-- Kato–Rellich, packaged: any `IsRelativelyBounded` witness with slope
`< 1` yields self-adjointness of the sum. -/
lemma kato_rellich' {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (V : A.domain →ₗ[ℂ] H) (hV_sym : IsSymmetricOn A V)
    (hV : IsRelativelyBounded A V) (ha : hV.a < 1) :
    IsSelfAdjoint (perturbedOp A V) :=
  kato_rellich hA V hV_sym hV.ha hV.hb ha hV.bound

/-! ## Consequences -/

/-- A bounded self-adjoint perturbation of a self-adjoint operator is
self-adjoint on the same domain (relative bound `a = 0`, `b = ‖T‖`). -/
lemma kato_rellich_bounded {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) :
    IsSelfAdjoint
      (perturbedOp A (T.comp (Submodule.subtypeL A.domain)).toLinearMap) :=
  kato_rellich hA _ (isSymmetricOn_of_selfAdjoint A hT)
    le_rfl (norm_nonneg T) zero_lt_one
    (fun ψ => by rw [zero_mul, zero_add]; exact T.le_opNorm (ψ : H))

/-- **Relative bound zero allows any coupling.**  If for every `ε > 0` there
is `b ≥ 0` with `‖V ψ‖ ≤ ε‖A ψ‖ + b‖ψ‖`, then `A + lam • V` is self-adjoint
for *every real* coupling constant `lam`.

This is the entry point for the hydrogen atom: the Coulomb potential has
`(−Δ)`-bound `0` by Hardy's inequality, so `−Δ − Z/r` is self-adjoint on
`H²(ℝ³)` for every nuclear charge `Z`.

(The coupling must be *real*: complex multiples of a symmetric operator are
not symmetric — this corrects the over-general `lam : ℂ` statement in the
previous version of this file, which was unprovable.) -/
lemma kato_rellich_bound_zero {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (V : A.domain →ₗ[ℂ] H) (hV_sym : IsSymmetricOn A V)
    (hV₀ : ∀ ε : ℝ, 0 < ε →
      ∃ b : ℝ, 0 ≤ b ∧ ∀ ψ : A.domain, ‖V ψ‖ ≤ ε * ‖A ψ‖ + b * ‖(ψ : H)‖)
    (lam : ℝ) :
    IsSelfAdjoint (perturbedOp A ((lam : ℂ) • V)) := by
  -- Choose ε so small that |lam| * ε < 1.
  have hpos : (0 : ℝ) < 1 / (2 * (|lam| + 1)) := by positivity
  obtain ⟨b, hb₀, hbound⟩ := hV₀ (1 / (2 * (|lam| + 1))) hpos
  refine kato_rellich hA ((lam : ℂ) • V) (hV_sym.real_smul lam)
    (a := |lam| * (1 / (2 * (|lam| + 1)))) (b := |lam| * b)
    (by positivity) (mul_nonneg (abs_nonneg lam) hb₀) ?_ ?_
  · -- |lam| / (2(|lam| + 1)) < 1
    rw [mul_one_div, div_lt_iff₀ (by positivity)]
    -- on older Mathlib: `div_lt_iff (by positivity)`
    nlinarith [abs_nonneg lam]
  · intro ψ
    have h1 : ‖((lam : ℂ) • V) ψ‖ = |lam| * ‖V ψ‖ := by
      rw [LinearMap.smul_apply, norm_smul]
      simp
    rw [h1]
    calc |lam| * ‖V ψ‖
        ≤ |lam| * (1 / (2 * (|lam| + 1)) * ‖A ψ‖ + b * ‖(ψ : H)‖) :=
          mul_le_mul_of_nonneg_left (hbound ψ) (abs_nonneg lam)
      _ = |lam| * (1 / (2 * (|lam| + 1))) * ‖A ψ‖
          + |lam| * b * ‖(ψ : H)‖ := by ring

/-- **Kato–Rellich + Stone.**  The perturbed operator generates a unique
strongly continuous one-parameter unitary group: perturbed quantum dynamics
exist and conserve probability. -/
lemma kato_rellich_generates_unitary {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) (V : A.domain →ₗ[ℂ] H)
    (hV_sym : IsSymmetricOn A V)
    {a b : ℝ} (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b) (ha₁ : a < 1)
    (hbound : ∀ ψ : A.domain, ‖V ψ‖ ≤ a * ‖A ψ‖ + b * ‖(ψ : H)‖) :
    ∃! U' : OneParameterUnitaryGroup (H := H),
      generator U' = perturbedOp A V := by
  have hsa := kato_rellich hA V hV_sym ha₀ hb₀ ha₁ hbound
  exact ⟨genToGroup hsa, generator_genToGroup hsa,
    fun W hW =>
      group_unique W (genToGroup hsa) (by rw [hW, generator_genToGroup hsa])⟩

/-- The perturbed dynamics of a self-adjoint generator: starting from a
unitary group `U`, a Kato-small symmetric perturbation of its generator
again generates a unique unitary group. -/
lemma kato_rellich_generator (U_grp : OneParameterUnitaryGroup (H := H))
    (V : (generator U_grp).domain →ₗ[ℂ] H)
    (hV_sym : IsSymmetricOn (generator U_grp) V)
    {a b : ℝ} (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b) (ha₁ : a < 1)
    (hbound : ∀ ψ : (generator U_grp).domain,
      ‖V ψ‖ ≤ a * ‖generator U_grp ψ‖ + b * ‖(ψ : H)‖) :
    ∃! U' : OneParameterUnitaryGroup (H := H),
      generator U' = perturbedOp (generator U_grp) V :=
  kato_rellich_generates_unitary (generator_isSelfAdjoint U_grp) V hV_sym
    ha₀ hb₀ ha₁ hbound

/-! ## Algebra of relatively bounded perturbations -/

omit [CompleteSpace H] in
/-- Sums of relatively bounded perturbations are relatively bounded. -/
def relatively_bounded_add {A : H →ₗ.[ℂ] H} {V W : A.domain →ₗ[ℂ] H}
    (hV : IsRelativelyBounded A V) (hW : IsRelativelyBounded A W) :
    IsRelativelyBounded A (V + W) where
  a := hV.a + hW.a
  b := hV.b + hW.b
  ha := add_nonneg hV.ha hW.ha
  hb := add_nonneg hV.hb hW.hb
  bound := fun ψ => by
    have h1 : ‖(V + W) ψ‖ ≤ ‖V ψ‖ + ‖W ψ‖ := by
      rw [LinearMap.add_apply]; exact norm_add_le _ _
    calc ‖(V + W) ψ‖ ≤ ‖V ψ‖ + ‖W ψ‖ := h1
      _ ≤ (hV.a * ‖A ψ‖ + hV.b * ‖(ψ : H)‖)
          + (hW.a * ‖A ψ‖ + hW.b * ‖(ψ : H)‖) :=
        add_le_add (hV.bound ψ) (hW.bound ψ)
      _ = (hV.a + hW.a) * ‖A ψ‖ + (hV.b + hW.b) * ‖(ψ : H)‖ := by ring

omit [CompleteSpace H] in
/-- Scalar multiples of relatively bounded perturbations are relatively
bounded. -/
noncomputable def relatively_bounded_smul {A : H →ₗ.[ℂ] H} {V : A.domain →ₗ[ℂ] H}
    (c : ℂ) (hV : IsRelativelyBounded A V) :
    IsRelativelyBounded A (c • V) where
  a := ‖c‖ * hV.a
  b := ‖c‖ * hV.b
  ha := mul_nonneg (norm_nonneg c) hV.ha
  hb := mul_nonneg (norm_nonneg c) hV.hb
  bound := fun ψ => by
    have h1 : ‖(c • V) ψ‖ = ‖c‖ * ‖V ψ‖ := by
      rw [LinearMap.smul_apply, norm_smul]
    calc ‖(c • V) ψ‖ = ‖c‖ * ‖V ψ‖ := h1
      _ ≤ ‖c‖ * (hV.a * ‖A ψ‖ + hV.b * ‖(ψ : H)‖) :=
        mul_le_mul_of_nonneg_left (hV.bound ψ) (norm_nonneg c)
      _ = ‖c‖ * hV.a * ‖A ψ‖ + ‖c‖ * hV.b * ‖(ψ : H)‖ := by ring

omit [CompleteSpace H] in
/-- Every bounded operator is a relatively bounded perturbation, with
relative bound `a = 0`. -/
noncomputable def bounded_is_relatively_bounded (A : H →ₗ.[ℂ] H) (T : H →L[ℂ] H) :
    IsRelativelyBounded A (T.comp (Submodule.subtypeL A.domain)).toLinearMap
    where
  a := 0
  b := ‖T‖
  ha := le_rfl
  hb := norm_nonneg T
  bound := fun ψ => by
    rw [zero_mul, zero_add]
    exact T.le_opNorm (ψ : H)

omit [CompleteSpace H] in
/-- Bounded perturbations have relative bound exactly `0`. -/
lemma bounded_relative_bound_zero (A : H →ₗ.[ℂ] H) (T : H →L[ℂ] H)
    (hT : IsRelativelyBounded A
      (T.comp (Submodule.subtypeL A.domain)).toLinearMap) :
    relativeBound A (T.comp (Submodule.subtypeL A.domain)).toLinearMap hT
      = 0 :=
  le_antisymm
    (relativeBound_le A _ hT le_rfl ‖T‖ (norm_nonneg T)
      (bounded_is_relatively_bounded A T).bound)
    (relativeBound_nonneg A _ hT)

end Spectra.Operator
