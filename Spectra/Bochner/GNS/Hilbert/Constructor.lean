/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.Completion
import Spectra.Bochner.GNS.Hilbert.Bundler

/-!
# GNS Hilbert Space Construction

This file builds the actual constructive payload of GNS: `gnsConstruction` takes a
positive-definite, Hermitian-symmetric `f : ℝ → ℂ` and produces the `GNSData f` bundle — a
Hilbert space `H`, a dense-range embedding `(ℝ →₀ ℂ) →ₗ[ℂ] H`, and the compatibility
identity `⟪embed α, embed β⟫ = pdInner f α β`.

## Main definitions

* `gnsConstruction`: the GNS Hilbert space, embedding, and their compatibility identities,
  packaged as a `GNSData f`

## Implementation notes

The `NormedAddCommGroup`/`InnerProductSpace` instances on the quotient `GNSQuotient hPD hH`
cannot be found by ordinary instance synthesis: they depend on the specific witnesses `hPD`/`hH`,
and registering them as global instances would create a diamond against any other
`NormedAddCommGroup`/`InnerProductSpace` structure the same underlying type might already carry
elsewhere. `gnsQuotientNACG`/`gnsQuotientIPS` package them as `@[reducible]` local `def`s instead,
brought into scope via `letI` at each of the two use sites (`gnsQuotient_uniformContinuousConstSMul`
and `gnsConstruction` itself); `@[reducible]` is load-bearing here, not cosmetic — without it the
two `letI`-introduced instances are opaque enough that later defeq checks (e.g. unfolding `dist`
back to `norm`, or matching `emb` against its `mkQ`-composed definition) fail to close.

## References

* Reed–Simon, *Methods of Modern Mathematical Physics I*, §VIII.5 (Gelfand–Naimark–Segal
  construction)
-/
open Spectra.PositiveDefinite
namespace Spectra.Bochner.GNS

/-- The `NormedAddCommGroup` instance on the GNS quotient, built from the pre-Hilbert core.
Kept as a `def` rather than a global `instance` — it is specific to a given `hPD`/`hH` witness
pair, and registering it globally would create instance-search ambiguity (the diamond this whole
file works around). Not `private`: every downstream file that needs the quotient's completion
(`Representation/Lemmas.lean`, `Representation/StronglyCont.lean`) brings it into scope locally
via `letI` rather than re-deriving it from `quotientCore` at each use site. -/
@[reducible] noncomputable def gnsQuotientNACG {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) :
    NormedAddCommGroup (GNSQuotient hPD hH) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)

/-- The `InnerProductSpace` instance on the GNS quotient, built over `gnsQuotientNACG`. Same
local-`letI` discipline as `gnsQuotientNACG` — see its docstring. -/
@[reducible] noncomputable def gnsQuotientIPS {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) :
    letI := gnsQuotientNACG hPD hH
    InnerProductSpace ℂ (GNSQuotient hPD hH) :=
  letI := gnsQuotientNACG hPD hH
  InnerProductSpace.ofCore (quotientCore hPD hH).toCore

/-- Scalar multiplication on the GNS quotient is uniformly continuous.
    (Instance synthesis can't derive this due to the NormedAddCommGroup/Module diamond,
    so we build it from the Lipschitz bound directly.) -/
lemma gnsQuotient_uniformContinuousConstSMul {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) :
    letI := gnsQuotientNACG hPD hH
    letI := gnsQuotientIPS hPD hH
    UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) := by
  letI nacgV := gnsQuotientNACG hPD hH
  letI ipsV := gnsQuotientIPS hPD hH
  constructor; intro c
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  have hc : (0 : ℝ) < ‖c‖ + 1 := by linarith [norm_nonneg c]
  refine ⟨ε / (‖c‖ + 1), by positivity, fun {x y} hxy => ?_⟩
  calc dist (c • x) (c • y)
      = ‖c • (x - y)‖ := by rw [dist_eq_norm, smul_sub]
    _ ≤ ‖c‖ * ‖x - y‖ := NormedSpace.norm_smul_le c (x - y)
    _ ≤ (‖c‖ + 1) * ‖x - y‖ := by nlinarith [norm_nonneg (x - y)]
    _ = (‖c‖ + 1) * dist x y := by rw [dist_eq_norm]
    _ < (‖c‖ + 1) * (ε / (‖c‖ + 1)) := by exact mul_lt_mul_of_pos_left hxy hc
    _ = ε := by field_simp

/-- **Existence of the GNS Hilbert space.**

Construction outline:
1. `pdInner` is a positive semi-definite Hermitian form on `ℝ →₀ ℂ`.
2. The null space `N = {α : pdInner f α α = 0}` is a ℂ-submodule.
3. The quotient `V = (ℝ →₀ ℂ) / N` inherits a genuine inner product:
   `⟨[α], [β]⟩_V = pdInner f α β` (well-defined by null orthogonality).
4. This makes `V` a pre-Hilbert space.
5. The Cauchy completion `H = V̂` is a Hilbert space.
6. The embedding `ι : (ℝ →₀ ℂ) → H` is `α ↦ [α]` composed with
   the completion embedding. It is ℂ-linear and has dense range.

Mathlib tools:
- `Submodule.Quotient` for V = (ℝ →₀ ℂ) / N
- `InnerProductSpace.Core` to build the inner product on V
- `UniformSpace.Completion` for H = V̂
- `UniformSpace.Completion.denseRange_coe` for density -/
noncomputable def gnsConstruction {f : ℝ → ℂ}
    (hPD : IsPositiveDefinite f) (hH : IsHermitian f) :
    GNSData f := by
  let _core := quotientCore hPD hH
  let V := GNSQuotient hPD hH
  letI nacgV := gnsQuotientNACG hPD hH
  letI ipsV := gnsQuotientIPS hPD hH
  haveI : UniformContinuousConstSMul ℂ V :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  let H := UniformSpace.Completion V
  let mkQ := (pdNullSubmodule hPD hH).mkQ
  let ι : V →ₗᵢ[ℂ] H := UniformSpace.Completion.toComplₗᵢ
  let emb : (ℝ →₀ ℂ) →ₗ[ℂ] H := ι.toLinearMap.comp mkQ
  exact {
    H := H
    instNACG := inferInstance
    instIPS := inferInstance
    instComplete := inferInstance
    embed := emb
    embed_inner := fun α β => by
      -- `emb α` unfolds to `ι.toLinearMap (mkQ α)`, i.e. the completion coercion `↑(mkQ α)`
      change @inner ℂ H _ (↑(mkQ α) : H) (↑(mkQ β) : H) = pdInner f α β
      rw [@UniformSpace.Completion.inner_coe]
      rfl
    embed_dense := by
      have h1 : DenseRange (mkQ : (ℝ →₀ ℂ) → V) :=
        (Submodule.mkQ_surjective _).denseRange
      have h2 : DenseRange (UniformSpace.Completion.coe' : V → H) :=
        UniformSpace.Completion.denseRange_coe
      exact h2.comp h1 (UniformSpace.Completion.continuous_coe V)
    embed_ker := fun α => by
      constructor
      · intro h
        -- unfold `emb α = 0` to the completion coercion `↑(mkQ α) = 0`, then use that the
        -- coercion is a uniform embedding (hence injective) to descend to `mkQ α = 0` in `V`
        change (↑(mkQ α) : H) = 0 at h
        rw [← UniformSpace.Completion.coe_zero] at h
        have hinj : mkQ α = 0 := by
          have := UniformSpace.Completion.isUniformEmbedding_coe (α := V)
          exact this.injective h
        rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hinj
      · intro h
        -- same unfolding as above, in reverse: `mkQ α = 0` in `V` pushes forward to
        -- `↑(mkQ α) = 0` in `H` via the coercion, which is `emb α`
        change (↑(mkQ α) : H) = 0
        have : mkQ α = 0 := (Submodule.Quotient.mk_eq_zero _).mpr h
        rw [this, UniformSpace.Completion.coe_zero]
  }

end Spectra.Bochner.GNS
