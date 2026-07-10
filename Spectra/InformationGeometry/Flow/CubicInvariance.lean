/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Connection.Bartlett
import Spectra.InformationGeometry.Flow.FaaDiBruno
import Spectra.InformationGeometry.Flow.MixtureConnection

/-!
# Divergence Preservation Implies Cubic-Tensor Preservation

A *divergence-preserving family* `φ_t` is one along which the KL divergence between
nearby points is invariant. This file shows that such a family preserves not only the
Fisher metric but the full Amari–Chentsov cubic tensor: the pullback of `cubicTrilin`
along `dφ_t` equals `cubicTrilin`. The basis-triple case is `preserves_cubic_basis`
(`MixtureConnection.lean`); here it is extended to arbitrary tangent vectors by trilinearity.

## Main statements

* `preserves_cubic` — for arbitrary tangent vectors `u v w`,
  `cubicTrilin (φ_t θ) (dφ·u) (dφ·v) (dφ·w) = cubicTrilin θ u v w`.

## References

* S. Amari, H. Nagaoka, *Methods of Information Geometry*, AMS, 2000.
-/
open MeasureTheory Finset Filter Topology TopologicalSpace
namespace Spectra.InformationGeometry
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

namespace ThriceDifferentiableModel.DivergencePreservingFamily
variable (M : TwiceDifferentiableModel n Ω)
open TwiceDifferentiableModel


/-- Divergence preservation implies cubic tensor preservation.

The basis-triple case is `preserves_cubic_basis` (MixtureConnection.lean); this
lemma extends it to arbitrary tangent vectors `u v w` by trilinearity:
expand each pushed-forward vector `dφ_t(θ)·x` over the coordinate basis,
distribute, reorder the resulting six-fold sum, and contract with the
basis identity.

This is the key result showing that divergence preservation captures
the *full* information-geometric structure, not just the metric. -/
lemma preserves_cubic
    (M₃ : ThriceDifferentiableModel n Ω)
    (hM₃ : M₃.toTwiceDifferentiableModel = M)
    (F : M.DivergencePreservingFamily)
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (t : ℝ) (u v w : ParamSpace n) :
    M.cubicTrilin (F.φ t θ)
      (fderiv ℝ (F.φ t) θ u) (fderiv ℝ (F.φ t) θ v) (fderiv ℝ (F.φ t) θ w) =
    M.cubicTrilin θ u v w := by
  subst hM₃
  -- ═══ Step 1: componentwise identity on basis triples ═══
  -- This is exactly `preserves_cubic_basis` from MixtureConnection.lean.
  have h_comp : ∀ a b c : Fin n,
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)).ofLp i *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)).ofLp j *
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)).ofLp k *
        M₃.cubicTensor (F.φ t θ) i j k =
      M₃.cubicTensor θ a b c :=
    fun a b c => preserves_cubic_basis (M := M₃) F hθ t a b c
  -- ═══ Step 2: Trilinearity reduction ═══
  -- Helper: 6-fold sum reordering (bubble sort, 9 adjacent transpositions)
  have sum6_comm : ∀ (f : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℝ),
      ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c, f i j k a b c =
      ∑ a, ∑ b, ∑ c, ∑ i, ∑ j, ∑ k, f i j k a b c := by
    intro f
    -- Move a past k, j, i
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    -- Move b past k, j, i (now at positions 2,3,4 under a)
    conv_lhs => arg 2; ext a; arg 2; ext i; arg 2; ext j; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext a; arg 2; ext i; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    -- Move c past k, j, i (now at positions 3,4,5 under a,b)
    conv_lhs => arg 2; ext a; arg 2; ext b; arg 2; ext i; arg 2; ext j; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext a; arg 2; ext b; arg 2; ext i; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext a; arg 2; ext b; rw [Finset.sum_comm]
  -- Generic linearity of CL map evaluation in EuclideanSpace
  have hlin : ∀ (L : ParamSpace n →L[ℝ] ParamSpace n) (x : ParamSpace n) (i : Fin n),
      (L x).ofLp i = ∑ a : Fin n, x.ofLp a *
        (L (EuclideanSpace.single a 1)).ofLp i := by
    intro L x i
    have hbasis : x = ∑ a : Fin n, x.ofLp a • EuclideanSpace.single a 1 := by
      ext p; simp only [WithLp.ofLp_sum, WithLp.ofLp_smul,
        PiLp.ofLp_single, sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_apply, mul_ite, mul_one, mul_zero, sum_ite_eq,
        mem_univ, ↓reduceIte]
    conv_lhs => rw [hbasis, map_sum]
    simp only [map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul,
      Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  have hdist : ∀ (f g h : Fin n → ℝ) (d : ℝ),
      (∑ a : Fin n, f a) * (∑ b : Fin n, g b) * (∑ c : Fin n, h c) * d =
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, f a * g b * h c * d := by
    intro f g h d
    rw [Finset.sum_mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
  -- Main reduction
  unfold cubicTrilin
  calc (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (fderiv ℝ (F.φ t) θ u).ofLp i *
        (fderiv ℝ (F.φ t) θ v).ofLp j *
        (fderiv ℝ (F.φ t) θ w).ofLp k *
        M₃.cubicTensor (F.φ t θ) i j k)
      -- expand each pushforward over the basis and distribute
      = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
          (u.ofLp a *
            (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)).ofLp i) *
          (v.ofLp b *
            (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)).ofLp j) *
          (w.ofLp c *
            (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)).ofLp k) *
          M₃.cubicTensor (F.φ t θ) i j k := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => ?_
        rw [hlin _ u i, hlin _ v j, hlin _ w k]
        exact hdist _ _ _ _
      -- reorder (i,j,k,a,b,c) → (a,b,c,i,j,k)
    _ = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
          ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          (u.ofLp a *
            (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)).ofLp i) *
          (v.ofLp b *
            (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)).ofLp j) *
          (w.ofLp c *
            (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)).ofLp k) *
          M₃.cubicTensor (F.φ t θ) i j k :=
        sum6_comm fun i j k a b c =>
          (u.ofLp a *
            (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)).ofLp i) *
          (v.ofLp b *
            (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)).ofLp j) *
          (w.ofLp c *
            (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)).ofLp k) *
          M₃.cubicTensor (F.φ t θ) i j k
      -- contract the inner triple sum with the basis identity
    _ = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
          u.ofLp a * v.ofLp b * w.ofLp c * M₃.cubicTensor θ a b c := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun c _ => ?_
        rw [← h_comp a b c]
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => by ring

end DivergencePreservingFamily
end ThriceDifferentiableModel
end Spectra.InformationGeometry
