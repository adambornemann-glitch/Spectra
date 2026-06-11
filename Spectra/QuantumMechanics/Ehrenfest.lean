/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: UnitaryEvolution/Ehrenfest.lean
-/
import Spectra.QuantumMechanics.SchrodingerEquation
import Mathlib.Analysis.InnerProductSpace.Continuous

open InnerProductSpace Complex Filter Topology
open Spectra.QuantumMechanics.StonesTheorem
open Spectra.QuantumMechanics.Schrodinger
open Spectra.QuantumMechanics.OneParameterUnitaryGroup
namespace Spectra.QuantumMechanics.Ehrenfest

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

/-- **Ehrenfest's theorem.** For a bounded observable `B` and `ψ₀ ∈ dom(A)` (with
`A := generator U_grp`), the expectation value `⟪ψ(t), B ψ(t)⟫` evolves by

  `d/dt ⟪ψ(t), B ψ(t)⟫ = ⟪i A ψ(t), B ψ(t)⟫ + ⟪ψ(t), B (i A ψ(t))⟫`,

which equals `i⟪ψ(t), [A,B]ψ(t)⟫` when `B` preserves `dom(A)`. The dynamics enters only
through `schrödinger_equation₂`; the product rule is `HasDerivAt.inner`. -/
theorem ehrenfest_theorem (U_grp : OneParameterUnitaryGroup (H := H))
    (B : H →L[ℂ] H) (ψ₀ : H) (hψ₀ : ψ₀ ∈ (generator U_grp).domain) (t₀ : ℝ) :
    let ψ_t  := U_grp.U t₀ ψ₀
    let Aψ_t := generator U_grp ⟨ψ_t, generator_domain_invariant U_grp t₀ ⟨ψ₀, hψ₀⟩⟩
    HasDerivAt (fun t => ⟪U_grp.U t ψ₀, B (U_grp.U t ψ₀)⟫_ℂ)
               (⟪I • Aψ_t, B ψ_t⟫_ℂ + ⟪ψ_t, B (I • Aψ_t)⟫_ℂ) t₀ := by
  intro ψ_t Aψ_t
  -- Schrödinger gives ψ'(t₀) = i A ψ(t₀)
  have hf := schrödinger_equation₂ U_grp ψ₀ hψ₀ t₀
  -- push through the bounded operator B
  have hg : HasDerivAt (fun t => B (U_grp.U t ψ₀)) (B (I • Aψ_t)) t₀ := by
    have h := (B.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t₀ hf
    simp only [map_smul]
    simp only [ContinuousLinearMap.coe_restrictScalars', generator_domain, map_smul] at h
    exact HasDerivAt.congr_deriv h rfl
  -- product rule for the ℂ-inner product
  exact hasDerivAt_inner_cplx hf hg

end Spectra.QuantumMechanics.Ehrenfest
