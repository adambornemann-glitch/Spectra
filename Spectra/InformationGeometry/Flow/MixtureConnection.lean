/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Flow.MixtureSymmetry
import Spectra.InformationGeometry.Flow.ThirdDerivative
import Spectra.InformationGeometry.Flow.PullbackIdentities
import Spectra.InformationGeometry.StatisticalManifold
import Spectra.InformationGeometry.CramerRao.Quantum
import Spectra.InformationGeometry.Divergence
import Spectra.InformationGeometry.Connection.AmariChentsov
import Spectra.InformationGeometry.Connection.Basic
import Spectra.InformationGeometry.Flow.Family
import Spectra.InformationGeometry.Flow.FaaDiBruno
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Algebra.BigOperators.WithTop
-- For Stone Uniqueness --
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Topology.Order.Compact

/-!
# The m-connection transformation law and cubic-tensor preservation

This file proves that a divergence-preserving family transforms the
m-connection coefficients tensorially-with-correction, and — as the key
intermediate step — that it preserves the Amari–Chentsov cubic tensor.

This is the capstone of a four-file cluster (split 2026-07-03 from a single 1,212-line file
of the same name, purely by section boundary — no statement changed):

1. `MixtureSymmetry.lean` — symmetry/relabeling lemmas for `scorePartial`, `Γᵐ`, the trilinear
   forms, and the cubic tensor; the expected-Hessian identity.
2. `ThirdDerivative.lean` — the integrated Bartlett identities and the diagonal third KL
   derivative (componentwise and trilinear).
3. `PullbackIdentities.lean` — identity (I), from differentiating `preserves_fisher` across
   base points.
4. This file — identity (M1), cubic-tensor preservation, and the main transformation law.

## The mathematical shape of the argument

Write `α := φ_t θ`, `uₓ := dφ_t(θ)·eₓ`, `w_{xy} := d²φ_t(θ)(eₓ, e_y)`,
`g := fisherBilin`, `Γ := mConnectionCoeff`, `C := cubicTensor`, and let
`T := D'''(α‖·)(α)[u_a, u_b, u_c]` denote the third KL derivative at the
diagonal, evaluated on the pushed-forward basis.  Two independent
families of identities are available:

1. **Transfer at one base point** (`third_deriv_transfer` +
   `kl_faa_di_bruno` + the diagonal third-derivative formula):

     `T + g(w_ab,u_c) + g(w_ac,u_b) + g(u_a,w_bc)
        = C(θ)_{abc} + Γ(θ)_{ac,b} + Γ(θ)_{bc,a} + Γ(θ)_{ab,c}`.   (M1)

2. **Differentiating `preserves_fisher` across base points** (three
   instances, one per choice of differentiated pair, `PullbackIdentities.lean`):

     `Γᵗʳⁱ(α)(u_c,u_a,u_b) + Γᵗʳⁱ(α)(u_c,u_b,u_a) + C(α)[u³]
        + g(w_ca,u_b) + g(u_a,w_cb)
        = Γ(θ)_{ca,b} + Γ(θ)_{cb,a} + C(θ)_{cab}`,                   (I)

   and its `(a,c,b)`, `(b,c,a)` permutations.

The diagonal formula also gives the trilinear decomposition

     `T = C(α)[u³] + Γᵗʳⁱ(α)(u_a,u_c,u_b) + Γᵗʳⁱ(α)(u_b,u_c,u_a)
                   + Γᵗʳⁱ(α)(u_a,u_b,u_c)`.                          (M3)

Summing the three instances of (I), substituting (M3), and comparing
with (M1) yields **cubic preservation** `C(α)[u³] = C(θ)_{abc}`
(`preserves_cubic_basis`), and then (M1) minus cubic preservation is
exactly the m-connection transformation law (`mConnection_correction`).

Note the law is *equivalent* to cubic preservation given (M1): it
cannot be obtained from the transfer identities at the single base
point `θ` alone, because the order-3 transfer only constrains the
totally symmetric combination `C + ΓΣ`.  The cross-base-point
information of (I) is what separates `C` from `Γ`.

## Analytic inputs

(I) requires differentiating `θ' ↦ g_{ij}(θ')` — a Leibniz interchange
with *live* density.  This is supplied by the new
`ThriceDifferentiableModel.fisherMatrix_hasFDerivAt` field (see the
design note in `Regularity.lean`).  Everything else is assembled from
`cross_score_hasFDerivAt'`, `klDiv_third_partial`,
`klDiv_third_deriv_decomposition`, `bartlett2_hasFDerivAt`,
`kl_faa_di_bruno`, and `third_deriv_transfer`.

## Main statements

* `third_deriv_pullback` — identity (M1)
* `preserves_cubic_basis` — `C(α)` pulled back through `dφ_t` is `C(θ)`
* `mConnection_correction` — the m-connection transformation law

(`bartlett_second`/`third`, `klDiv_third_deriv_eval`/`trilin` are in `ThirdDerivative.lean`;
`fisher_derivative_identity` is in `PullbackIdentities.lean` — see those files' docstrings.)
-/

open MeasureTheory Finset Filter Topology TopologicalSpace
namespace Spectra.InformationGeometry

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

namespace ThriceDifferentiableModel

namespace DivergencePreservingFamily

variable {M : ThriceDifferentiableModel n Ω}
variable (F : M.toTwiceDifferentiableModel.DivergencePreservingFamily)
open TwiceDifferentiableModel ThriceDifferentiableModel
open TwiceDifferentiableModel.DivergencePreservingFamily

-- ════════════════════════════════════════════════════════════════════
-- §7. The transfer identity (M1), cubic preservation, and the main law
-- ════════════════════════════════════════════════════════════════════

/-- **Identity (M1): pullback of the diagonal third derivative.**
Combining `kl_faa_di_bruno`, `third_deriv_transfer`, and the diagonal
formula `klDiv_third_deriv_eval`:

  `T + g_α(d²φ_{ab},u_c) + g_α(d²φ_{ac},uᵦ) + g_α(uₐ,d²φ_{bc})
     = C(θ)_{abc} + Γᵐ(θ)_{ac,b} + Γᵐ(θ)_{bc,a} + Γᵐ(θ)_{ab,c}`. -/
lemma third_deriv_pullback
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (t : ℝ) (a b c : Fin n) :
    fderiv ℝ (fun θ₁ =>
      fderiv ℝ (fun θ₂ =>
        fderiv ℝ (M.klDiv (F.φ t θ)) θ₂
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))) θ₁
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))) (F.φ t θ)
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
    + M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
        (F.secondDerivPhi t θ a b)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
    + M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
        (F.secondDerivPhi t θ a c)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
    + M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
        (F.secondDerivPhi t θ b c)
    = M.cubicTensor θ a b c + M.mConnectionCoeff θ a c b +
      M.mConnectionCoeff θ b c a + M.mConnectionCoeff θ a b c := by
  have hFdB :
      fderiv ℝ (fun θ₁ =>
        fderiv ℝ (fun θ₂ =>
          fderiv ℝ (fun θ₃ => M.klDiv (F.φ t θ) (F.φ t θ₃)) θ₂
            (EuclideanSpace.single c 1)) θ₁
          (EuclideanSpace.single b 1)) θ
        (EuclideanSpace.single a 1) =
      fderiv ℝ (fun θ₁ =>
        fderiv ℝ (fun θ₂ =>
          fderiv ℝ (M.klDiv (F.φ t θ)) θ₂
            (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))) θ₁
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))) (F.φ t θ)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
      + M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
          (F.secondDerivPhi t θ a b)
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
      + M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
          (F.secondDerivPhi t θ a c)
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
      + M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
          (F.secondDerivPhi t θ b c) :=
    kl_faa_di_bruno F hθ t a b c
  have hTrans := F.third_deriv_transfer hθ t a b c
  have hEval := M.klDiv_third_deriv_eval hθ a b c
  linarith [hFdB, hTrans, hEval]

/-- **Cubic-tensor preservation on the moving frame.**  The pullback of
`C(α)` through `dφ_t(θ)` on basis vectors recovers `C(θ)`:

  `∑ᵢⱼₖ (uₐ)ᵢ(uᵦ)ⱼ(u_c)ₖ C(φ_tθ)ᵢⱼₖ = C(θ)_{abc}`. -/
lemma preserves_cubic_basis
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (t : ℝ) (a b c : Fin n) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) i *
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) j *
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) k *
      M.cubicTensor (F.φ t θ) i j k) = M.cubicTensor θ a b c := by
  have hα : F.φ t θ ∈ M.paramDomain := F.maps_domain t θ hθ
  -- the three differentiated-isometry identities
  have hI₁ := fisher_derivative_identity F hθ t a b c
  have hI₂ := fisher_derivative_identity F hθ t a c b
  have hI₃ := fisher_derivative_identity F hθ t b c a
  -- the transfer identity
  have hD1 := third_deriv_pullback F hθ t a b c
  -- the trilinear decomposition of the tensorial term
  have hM3 :
      fderiv ℝ (fun θ₁ =>
        fderiv ℝ (fun θ₂ =>
          fderiv ℝ (M.klDiv (F.φ t θ)) θ₂
            (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))) θ₁
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))) (F.φ t θ)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) i *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) j *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) k *
        M.cubicTensor (F.φ t θ) i j k) +
      M.mConnectionTrilin (F.φ t θ)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) +
      M.mConnectionTrilin (F.φ t θ)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) +
      M.mConnectionTrilin (F.φ t θ)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) := by
    rw [M.klDiv_third_deriv_trilin hα
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [M.trilin_relabel_ikj (F.φ t θ)
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)),
        M.trilin_relabel_jki (F.φ t θ)
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)),
        ← M.mConnectionTrilin_eq_sum (F.φ t θ)
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))]
  -- ── normalize hI₁: sort the trilinear slots, the d²φ indices,
  --    and the θ-side tensor indices ──
  rw [M.mConnectionTrilin_symm₁₂ hα
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)),
      M.mConnectionTrilin_symm₁₂ hα
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)),
      F.secondDerivPhi_symm t θ c a, F.secondDerivPhi_symm t θ c b,
      M.mConnectionCoeff_symm₁₂ hθ c a b,
      M.mConnectionCoeff_symm₁₂ hθ c b a,
      M.cubicTensor_symm₁₂ hθ c a b,
      M.cubicTensor_symm₂₃ hθ a c b] at hI₁
  -- ── normalize hI₂ ──
  have hQ₂ : (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) i *
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) j *
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) k *
      M.cubicTensor (F.φ t θ) i j k) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) i *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) j *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) k *
        M.cubicTensor (F.φ t θ) i j k :=
    (M.cubic_sum_swap₂₃ hα
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))).symm
  rw [M.mConnectionTrilin_symm₁₂ hα
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)),
      hQ₂,
      F.secondDerivPhi_symm t θ b a,
      M.mConnectionCoeff_symm₁₂ hθ b a c,
      M.cubicTensor_symm₁₂ hθ b a c] at hI₂
  -- ── normalize hI₃ ──
  have hQ₃ : (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) i *
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) j *
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) k *
      M.cubicTensor (F.φ t θ) i j k) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) i *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) j *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) k *
        M.cubicTensor (F.φ t θ) i j k := by
    rw [M.cubic_sum_swap₂₃ hα
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)),
        M.cubic_sum_swap₁₂ hα
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))]
  rw [hQ₃,
      M.toRegularStatisticalModel.fisherBilin_symm (F.φ t θ)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
        (F.secondDerivPhi t θ a c)] at hI₃
  -- ── solve the linear system ──
  linarith [hI₁, hI₂, hI₃, hD1, hM3]

/-- **m-Connection transformation law.**  Differentiating the isometry
identity `g(φ_tθ')(dφ·eₐ, dφ·eᵦ) = g(θ')_{ab}` from `preserves_fisher`
in direction `e_c`, combined with the Faà di Bruno expansion of the
transferred third derivative, gives

  `[D'''(α‖·)(α)(uₐ,uᵦ,u_c) − C(α)(uₐ,uᵦ,u_c)]
     + g_α(d²φ_{ab}, u_c) + g_α(d²φ_{ac}, uᵦ) + g_α(uₐ, d²φ_{bc})
   = Γᵐ(θ)_{ac,b} + Γᵐ(θ)_{bc,a} + Γᵐ(θ)_{ab,c}`,

i.e. the m-connection of the image point, pulled back through `dφ_t`
and corrected by the metric-paired second derivatives of the flow, is
the m-connection at the source.  Equivalently (given
`third_deriv_pullback`): the cubic tensor is preserved. -/
theorem mConnection_correction
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (t : ℝ) (a b c : Fin n) :
    (fderiv ℝ (fun θ₁ =>
      fderiv ℝ (fun θ₂ =>
        fderiv ℝ (M.klDiv (F.φ t θ)) θ₂
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))) θ₁
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))) (F.φ t θ)
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
    - ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) i *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) j *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) k *
        M.cubicTensor (F.φ t θ) i j k)
    + M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
        (F.secondDerivPhi t θ a b)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
    + M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
        (F.secondDerivPhi t θ a c)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
    + M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
        (F.secondDerivPhi t θ b c)
    = M.mConnectionCoeff θ a c b + M.mConnectionCoeff θ b c a +
      M.mConnectionCoeff θ a b c := by
  have hD1 := third_deriv_pullback F hθ t a b c
  have hQ := preserves_cubic_basis F hθ t a b c
  linarith [hD1, hQ]

end DivergencePreservingFamily

end ThriceDifferentiableModel

end Spectra.InformationGeometry
