/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: UnitaryEvolution/Ehrenfest.lean
-/
import Spectra.UnitaryEvolution.Schrodinger

namespace QuantumMechanics.UnitaryEvo

open InnerProductSpace Complex Filter Topology

open Generators StonesTheorem Schrödinger


/-- The ℂ-inner product is bounded ℝ-bilinear.
Conjugate-linearity over ℂ restricts to genuine ℝ-linearity since
`conj(r) = r` for real scalars. Cauchy-Schwarz gives the bound. -/
private lemma inner_isBoundedBilinearMap_real {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [IsScalarTower ℝ ℂ H] :
    IsBoundedBilinearMap ℝ (fun p : H × H => ⟪p.1, p.2⟫_ℂ) where
  add_left x₁ x₂ y := inner_add_left x₁ x₂ y
  smul_left c x y := by
    rw [← algebraMap_smul ℂ c x, inner_smul_left,
        RCLike.conj_ofReal, ← Algebra.smul_def]
  add_right x y₁ y₂ := inner_add_right x y₁ y₂
  smul_right c x y := by
    rw [← algebraMap_smul ℂ c y, inner_smul_right,
        ← Algebra.smul_def]
  bound := ⟨1, one_pos, fun x y => by rw [one_mul]; exact norm_inner_le_norm x y⟩


/-- **Product rule for the ℂ-inner product under ℝ-differentiation.**
`d/dt ⟨f(t), g(t)⟩_ℂ = ⟨f'(t), g(t)⟩_ℂ + ⟨f(t), g'(t)⟩_ℂ`.

The ℂ-inner product is bounded ℝ-bilinear (Cauchy-Schwarz gives the bound,
conjugate-linearity restricts to ℝ-linearity). The standard product rule
for bounded bilinear maps applies. The sorry is an API gap in composing
`IsBoundedBilinearMap.hasFDerivAt` with a product of `HasDerivAt` maps;
the mathematics is completely standard. -/
private lemma hasDerivAt_inner_cplx  {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [IsScalarTower ℝ ℂ H]
    {f g : ℝ → H} {f' g' : H} {x : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun t => ⟪f t, g t⟫_ℂ)
               (⟪f', g x⟫_ℂ + ⟪f x, g'⟫_ℂ) x := by
  have hb := @inner_isBoundedBilinearMap_real H _ _ _
  have h := (hb.hasFDerivAt (f x, g x)).comp_hasDerivAt x (hf.prodMk hg)
  exact h.congr_deriv
    (by simp [IsBoundedBilinearMap.deriv]
        rw [AddCommMagma.add_comm ⟪f x, g'⟫_ℂ ⟪f', g x⟫_ℂ])



variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- ℂ-linear maps are ℝ-compatible: any ℂ-linear map preserves ℝ-scalar multiplication.
This follows from `IsScalarTower ℝ ℂ H`: real scalar action factors through ℂ. -/
instance : LinearMap.CompatibleSMul H H ℝ ℂ := ⟨fun f c x => by
  have := f.map_smul (algebraMap ℝ ℂ c) x
  simp_all only [coe_algebraMap, coe_smul]⟩

/-- **Ehrenfest's theorem**: the rate of change of the expectation value
of a bounded observable `B` is determined by the commutator with the generator.

  `d/dt ⟨ψ(t), Bψ(t)⟩ = ⟨iAψ(t), Bψ(t)⟩ + ⟨ψ(t), B(iAψ(t))⟩`

The RHS equals `i⟨ψ(t), [A,B]ψ(t)⟩` when `B` maps `dom(A)` into `dom(A)`.
This connects quantum dynamics to classical equations of motion. -/
theorem ehrenfest_theorem {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [IsScalarTower ℝ ℂ H]
    (U_grp : OneParameterUnitaryGroup (H := H))
    (gen : Generator U_grp)
    (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (B : H →L[ℂ] H)
    (ψ₀ : H) (hψ₀ : ψ₀ ∈ gen.domain)
    (t₀ : ℝ) :
    let ψ_t := U_grp.U t₀ ψ₀
    let Aψ_t := gen.op ⟨ψ_t, gen.domain_invariant t₀ ψ₀ hψ₀⟩
    HasDerivAt (fun t => ⟪U_grp.U t ψ₀, B (U_grp.U t ψ₀)⟫_ℂ)
               (⟪I • Aψ_t, B ψ_t⟫_ℂ + ⟪ψ_t, B (I • Aψ_t)⟫_ℂ)
               t₀ := by
  intro ψ_t Aψ_t
  -- (1) Schrödinger: d/dt U(t)ψ₀ = I • A(U(t)ψ₀) at t₀
  have hf := schrödinger_equation₂ U_grp gen hsa h_dense ψ₀ hψ₀ t₀
  -- (2) Chain rule through B: d/dt B(U(t)ψ₀) = B(I • Aψ_t) at t₀
  have hg : HasDerivAt (fun t => B (U_grp.U t ψ₀)) (B (I • Aψ_t)) t₀ :=
    (B.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t₀ hf
  -- (3) Product rule for the ℂ-inner product
  exact hasDerivAt_inner_cplx hf hg

end QuantumMechanics.UnitaryEvo
