/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.Cocycle.ModularPolarUniqueness
import Spectra.Modular.Cocycle.ModularSqrtInverse
import Spectra.SpectralTheory.Calculus.SquareBridge
import Spectra.Operator.BoundedFactorAdjoint
/-!
# `J² = 1` and `J Δ^{±1,±½} J⁻¹ = Δ^{∓1,∓½}` — Field 3 closed (Route B Stages 4–5)

The last structural field of `ModularData` — `J_involutive : ∀ x, J (J x) = x` — together with the
Tomita conjugation relations for the modular calculus.  The proof is the **second polar
decomposition** argument, made possible by three previously-banked layers:

1. the Stage-3 *full-domain* polar identity `S̃ y = J (Δ^{½} y)` on `D(S) = D(Δ^{½})`
   (`ModularPolarExtension.lean`);
2. the inverse-calculus twins `Δ^{-½}(Δ^{½}y) = y`, `Δ^{½}(Δ^{-½}z) = z` and the range
   characterization `ran Δ^{½} = D(Δ^{-½})` (`ModularSqrtInverse.lean`);
3. the KS3 bounded-factor adjoint law `(b∘A)⋆ = A⋆∘b⁻¹` (`Operator/BoundedFactorAdjoint.lean`),
   the KS2 conjugation transfers (`conjPMap`, `ModularPolarUniqueness.lean`), the `s ↦ s²`
   spectral-square bridge (`SpectralTheory/Calculus/SquareBridge.lean`), and the keystone
   `posSqrt_unique` (`SquareSpectralMap.lean`).

## The argument

Let `P₂ := J Δ^{-½} J⁻¹` (`conjModularSqrtInv`) — self-adjoint with spectral measure carried by
`[0,∞)`, by the generic KS2 transfers (conjugation is spectrum-preserving, so this smuggles **no**
inversion).  The Tomita involution `S̃(S̃y) = y` combined with the full-domain polar identity gives
the key pointwise fact

  `J⁻¹ y = Δ^{½}(S̃ y)`   for all `y ∈ D(S)`,                                       (♦)

an *explicit* element of `ran Δ^{½}`.  With the inverse-calculus twins, (♦) upgrades to the
**second polar decomposition** `S = W″ ∘ P₂` where `W″ := toConj ∘ J⁻¹` is a *bounded unitary*
`H ≃ₗᵢ[ℂ] Conj H` (`modularWInv`).  Taking adjoints by the *bounded-factor* law KS3 — never the
dead both-unbounded `(AB)⋆ = B⋆A⋆` — and using `Δ = S⋆S`:

  `Δ x = P₂ (P₂ x)`  pointwise on `D(Δ)`  (memberships come *out of* the adjoint domain).

The square bridge turns this (and the banked `(Δ^{½})² = Δ` pointwise identity) into the two
spectral-square equalities `posSqrt_unique` consumes, yielding **`P₂ = Δ^{½}`**.  Reading this
back through (♦) and the polar identity gives `J (J (Δ^{½} y)) = Δ^{½} y` on the dense
`ran Δ^{½}`, hence **`J² = 1`** by continuity.  The conjugation relations
`J Δ^{½} J⁻¹ = Δ^{-½}` and `J Δ J⁻¹ = Δ⁻¹` follow.

## Main statements

* `conjModularSqrtInv_eq_modularSqrt` — **`J Δ^{-½} J⁻¹ = Δ^{½}`** (the polar-uniqueness output).
* `modularConjugation_involutive` — **`J (J x) = x`** — the `ModularData.J_involutive` field.
* `modularConjugation_symm_eq` — `J⁻¹ = J`.
* `conjModularSqrt_eq_modularSqrtInv` — **`J Δ^{½} J⁻¹ = Δ^{-½}`** (the Stage-5 target 5.1).
* `conjModularOp_eq_modularOpInv` — **`J Δ J⁻¹ = Δ⁻¹`** (the Field-3 gate, Stage-3.5 target).

The old hostile estimates for this node priced in building the antilinear `SS⋆` layer and the
`s ↦ s²` pushforward from scratch; with Stages 0–3 and KS1–KS3 banked, what remains is exactly
this assembly.
-/

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace
open Spectra.QuantumMechanics.SpectralTheory
open Spectra.YosidaHille
open Spectra.OneParameterUnitaryGroup
open Spectra.Borel
open Spectra.Conj
open Spectra.Operator

namespace Spectra.TomitaTakesaki

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}
variable (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)

/-! ### The conjugated inverse square root `P₂ = J Δ^{-½} J⁻¹` and its `posSqrt_unique` inputs -/

/-- **The conjugated inverse modular square root** `P₂ := J Δ^{-½} J⁻¹` — the second polar
factor.  Conjugation is spectrum-preserving, so this definition smuggles no inversion; the
inversion enters only through the involution `S̃² = 1`, via the second polar decomposition. -/
noncomputable def conjModularSqrtInv : H →ₗ.[ℂ] H :=
  conjPMap (modularConjugation hcyc hsep) (modularSqrtInv hcyc hsep)

/-- `J Δ^{-½} J⁻¹` is self-adjoint (generic KS2 transfer). -/
theorem conjModularSqrtInv_isSelfAdjoint : IsSelfAdjoint (conjModularSqrtInv hcyc hsep) :=
  conjPMap_isSelfAdjoint (inner_modularConjugation hcyc hsep)
    (modularSqrtInv_isSelfAdjoint hcyc hsep)

/-- The quadratic form of `Δ^{-½}` is non-negative (the symbol `1/√s` is non-negative). -/
private theorem modularSqrtInv_re_inner_nonneg :
    ∀ x : (modularSqrtInv hcyc hsep).domain,
      0 ≤ (⟪(x : H), modularSqrtInv hcyc hsep x⟫_ℂ).re :=
  fun x =>
    re_inner_self_pmapOfPVM_nonneg (genToGroup (modularOp_isSelfAdjoint hcyc hsep))
      (fun s => ((Real.sqrt s : ℂ))⁻¹) measurable_invSqrtC
      (fun s => by rw [← Complex.ofReal_inv, Complex.ofReal_re]; positivity)
      ((ProjValMeasure.mem_pmapDomain _).mp x.2)

/-- The quadratic form of `Δ^{½}` is non-negative (the symbol `√s` is non-negative). -/
private theorem modularSqrt_re_inner_nonneg' :
    ∀ x : (modularSqrt hcyc hsep).domain,
      0 ≤ (⟪(x : H), modularSqrt hcyc hsep x⟫_ℂ).re :=
  fun x =>
    re_inner_self_pmapOfPVM_nonneg (genToGroup (modularOp_isSelfAdjoint hcyc hsep))
      (fun s => (Real.sqrt s : ℂ)) measurable_sqrtC
      (fun s => by rw [Complex.ofReal_re]; exact Real.sqrt_nonneg s)
      ((ProjValMeasure.mem_pmapDomain _).mp x.2)

/-- **The spectral measure of `J Δ^{-½} J⁻¹` charges no negative reals** — the `posSqrt_unique`
positivity input for the `P` slot. -/
theorem conjModularSqrtInv_borelMeasure_Iio_zero (ξ : H) :
    borelMeasure (genToGroup (conjModularSqrtInv_isSelfAdjoint hcyc hsep)) ξ
      (Set.Iio (0 : ℝ)) = 0 := by
  have hgen : generator (genToGroup (conjModularSqrtInv_isSelfAdjoint hcyc hsep))
      = conjModularSqrtInv hcyc hsep := generator_genToGroup _
  refine borelMeasure_Iio_zero_eq_zero_of_dense _ ?_ ?_ ξ
  · rw [hgen]
    exact (conjModularSqrtInv_isSelfAdjoint hcyc hsep).dense_domain
  · rintro ⟨ψ, hψ'⟩
    have hψ : ψ ∈ (conjModularSqrtInv hcyc hsep).domain := by rw [← hgen]; exact hψ'
    have hval : generator (genToGroup (conjModularSqrtInv_isSelfAdjoint hcyc hsep)) ⟨ψ, hψ'⟩
        = conjModularSqrtInv hcyc hsep ⟨ψ, hψ⟩ := (le_of_eq hgen).2 rfl
    rw [hval]
    exact conjPMap_re_inner_nonneg (inner_modularConjugation hcyc hsep)
      (modularSqrtInv_re_inner_nonneg hcyc hsep) ⟨ψ, hψ⟩

/-- **The spectral measure of `Δ^{½}` charges no negative reals** — the `posSqrt_unique`
positivity input for the `Q` slot. -/
theorem modularSqrt_borelMeasure_Iio_zero (ξ : H) :
    borelMeasure (genToGroup (modularSqrt_isSelfAdjoint hcyc hsep)) ξ (Set.Iio (0 : ℝ)) = 0 := by
  have hgen : generator (genToGroup (modularSqrt_isSelfAdjoint hcyc hsep))
      = modularSqrt hcyc hsep := generator_genToGroup _
  refine borelMeasure_Iio_zero_eq_zero_of_dense _ ?_ ?_ ξ
  · rw [hgen]
    exact (modularSqrt_isSelfAdjoint hcyc hsep).dense_domain
  · rintro ⟨ψ, hψ'⟩
    have hψ : ψ ∈ (modularSqrt hcyc hsep).domain := by rw [← hgen]; exact hψ'
    have hval : generator (genToGroup (modularSqrt_isSelfAdjoint hcyc hsep)) ⟨ψ, hψ'⟩
        = modularSqrt hcyc hsep ⟨ψ, hψ⟩ := (le_of_eq hgen).2 rfl
    rw [hval]
    exact modularSqrt_re_inner_nonneg' hcyc hsep ⟨ψ, hψ⟩

/-! ### The key pointwise identity (♦): `J⁻¹ y = Δ^{½}(S̃ y)` on `D(S)` -/

/-- `S̃ y ∈ D(Δ^{½})` for `y ∈ D(S)` (involution-invariance of the domain + `D(S) = D(Δ^{½})`). -/
theorem sTilde_mem_modularSqrt_domain (y : (tomitaClosure M Ω).domain) :
    ofConj (tomitaClosure M Ω y) ∈ (modularSqrt hcyc hsep).domain :=
  (tomitaClosure_domain_eq_modularSqrt_domain hcyc hsep) ▸
    (sTilde_closure_mem_domain hcyc hsep y)

/-- **(♦) The involution reads the polar decomposition backwards**: for `y ∈ D(S)`,
`J⁻¹ y = Δ^{½}(S̃ y)` — an explicit element of `ran Δ^{½}`.  From `y = S̃(S̃ y) = J(Δ^{½}(S̃ y))`
(involution + the full-domain Stage-3 polar identity applied at `S̃ y`). -/
theorem modularConjugation_symm_apply_eq (y : (tomitaClosure M Ω).domain) :
    (modularConjugation hcyc hsep).symm (y : H)
      = modularSqrt hcyc hsep
          ⟨ofConj (tomitaClosure M Ω y), sTilde_mem_modularSqrt_domain hcyc hsep y⟩ := by
  have hzQ : ofConj (tomitaClosure M Ω y) ∈ (modularSqrt hcyc hsep).domain :=
    sTilde_mem_modularSqrt_domain hcyc hsep y
  -- the full-domain polar identity at `S̃ y`, pushed through `ofConj`
  have hpolar := congrArg ofConj
    (tomita_eq_modularConjugation_modularSqrt_full hcyc hsep ⟨ofConj (tomitaClosure M Ω y), hzQ⟩)
  rw [Conj.coe_toConjₗᵢ (E := H), Conj.ofConj_toConj] at hpolar
  -- the involution at `y` (the two `S`-membership proofs are definitionally interchangeable)
  have hinv := sTilde_closure_involutive hcyc hsep y
  -- `J (Δ^{½} (S̃ y)) = S̃ (S̃ y) = y`
  have hJ : modularConjugation hcyc hsep
      (modularSqrt hcyc hsep ⟨ofConj (tomitaClosure M Ω y), hzQ⟩) = (y : H) :=
    hpolar.trans hinv
  exact ((modularConjugation hcyc hsep).symm_apply_eq).mpr hJ.symm

/-! ### The second polar decomposition `S = W″ ∘ P₂` -/

/-- **The second polar unitary** `W″ := toConj ∘ J⁻¹ : H ≃ₗᵢ[ℂ] Conj H` (a genuinely `ℂ`-linear
unitary: antilinear ∘ antilinear). -/
noncomputable def modularWInv : H ≃ₗᵢ[ℂ] Conj H :=
  ((modularConjugation hcyc hsep).symm).trans (toConjₗᵢ H)

/-- `W″ y = toConj (J⁻¹ y)`. -/
theorem modularWInv_apply (y : H) :
    modularWInv hcyc hsep y = toConj ((modularConjugation hcyc hsep).symm y) := by
  rw [modularWInv, LinearIsometryEquiv.trans_apply, Conj.coe_toConjₗᵢ (E := H)]

/-- `(W″)⁻¹ z = J (ofConj z)`. -/
theorem modularWInv_symm_apply (z : Conj H) :
    (modularWInv hcyc hsep).symm z = modularConjugation hcyc hsep (ofConj z) := by
  apply (modularWInv hcyc hsep).injective
  rw [LinearIsometryEquiv.apply_symm_apply, modularWInv_apply,
    LinearIsometryEquiv.symm_apply_apply, Conj.toConj_ofConj]

/-- **Domain of the second polar factor**: `D(P₂) = D(S)`.  (→): `J⁻¹ z ∈ D(Δ^{-½}) = ran Δ^{½}`
exhibits `z = J(Δ^{½}u) = S̃ u ∈ D(S)`.  (←): (♦) puts `J⁻¹ z` in `ran Δ^{½} ⊆ D(Δ^{-½})`. -/
theorem mem_conjModularSqrtInv_domain_iff {z : H} :
    z ∈ (conjModularSqrtInv hcyc hsep).domain ↔ z ∈ (tomitaClosure M Ω).domain := by
  constructor
  · intro hzP
    have hzInv : (modularConjugation hcyc hsep).symm z ∈ (modularSqrtInv hcyc hsep).domain :=
      (mem_conjPMap_domain_iff _ _).mp hzP
    obtain ⟨u, hu⟩ := (mem_modularSqrtInv_domain_iff hcyc hsep _).mp hzInv
    -- `z = J (Δ^{½} u) = S̃ u ∈ D(S)`
    have hzu : z = modularConjugation hcyc hsep (modularSqrt hcyc hsep u) := by
      have h := congrArg (modularConjugation hcyc hsep) hu
      rw [LinearIsometryEquiv.apply_symm_apply] at h
      exact h.symm
    have hpolar := tomita_eq_modularConjugation_modularSqrt_full hcyc hsep u
    have hJu : modularConjugation hcyc hsep (modularSqrt hcyc hsep u)
        = ofConj (tomitaClosure M Ω
            ⟨(u : H), modularSqrt_domain_le_tomitaClosure_domain hcyc hsep u.2⟩) := by
      have h1 := congrArg ofConj hpolar
      rwa [Conj.coe_toConjₗᵢ (E := H), Conj.ofConj_toConj] at h1
    rw [hzu, hJu]
    exact sTilde_closure_mem_domain hcyc hsep _
  · intro hzS
    have h := modularConjugation_symm_apply_eq hcyc hsep ⟨z, hzS⟩
    have hmem : (modularConjugation hcyc hsep).symm z ∈ (modularSqrtInv hcyc hsep).domain := by
      rw [h]
      exact modularSqrt_mem_modularSqrtInv_domain hcyc hsep _
    exact (mem_conjPMap_domain_iff _ _).mpr hmem

/-- **Value of the second polar factor on `D(S)`**: `P₂ z = J (S̃ z)`. -/
theorem conjModularSqrtInv_apply_eq {z : H} (hzS : z ∈ (tomitaClosure M Ω).domain)
    (hzP : z ∈ (conjModularSqrtInv hcyc hsep).domain) :
    conjModularSqrtInv hcyc hsep ⟨z, hzP⟩
      = modularConjugation hcyc hsep (ofConj (tomitaClosure M Ω ⟨z, hzS⟩)) := by
  have h0 : conjModularSqrtInv hcyc hsep ⟨z, hzP⟩
      = modularConjugation hcyc hsep (modularSqrtInv hcyc hsep
          ⟨(modularConjugation hcyc hsep).symm z, hzP⟩) := rfl
  rw [h0]
  congr 1
  -- `Δ^{-½} (J⁻¹ z) = Δ^{-½} (Δ^{½} (S̃ z)) = S̃ z`
  have hsub : (⟨(modularConjugation hcyc hsep).symm z, hzP⟩ :
      (modularSqrtInv hcyc hsep).domain)
      = ⟨modularSqrt hcyc hsep
            ⟨ofConj (tomitaClosure M Ω ⟨z, hzS⟩),
              sTilde_mem_modularSqrt_domain hcyc hsep ⟨z, hzS⟩⟩,
          modularSqrt_mem_modularSqrtInv_domain hcyc hsep _⟩ :=
    Subtype.ext (modularConjugation_symm_apply_eq hcyc hsep ⟨z, hzS⟩)
  rw [hsub, modularSqrtInv_modularSqrt_apply]

/-- **The second polar decomposition**: `S = W″ ∘ P₂` as an operator identity
(`LinearMap.compPMap`, domain `D(P₂) = D(S)`). -/
theorem tomitaClosure_eq_modularWInv_comp :
    tomitaClosure M Ω
      = (modularWInv hcyc hsep).toLinearEquiv.toLinearMap.compPMap
          (conjModularSqrtInv hcyc hsep) := by
  refine LinearPMap.ext_iff.mpr ⟨?_, ?_⟩
  · -- domains agree: `D(compPMap) = D(P₂) = D(S)`
    ext z
    exact (mem_conjModularSqrtInv_domain_iff hcyc hsep).symm
  · intro z hf hg
    have hzS : z ∈ (tomitaClosure M Ω).domain := hf
    have hval : (modularWInv hcyc hsep).toLinearEquiv.toLinearMap.compPMap
        (conjModularSqrtInv hcyc hsep) ⟨z, hg⟩
        = modularWInv hcyc hsep (conjModularSqrtInv hcyc hsep ⟨z, hg⟩) := rfl
    rw [hval, conjModularSqrtInv_apply_eq hcyc hsep hzS hg, modularWInv_apply,
      LinearIsometryEquiv.symm_apply_apply, Conj.toConj_ofConj]

/-! ### `Δ = P₂²` pointwise on `D(Δ)`, via the KS3 adjoint law -/

/-- **`Δ x = P₂ (P₂ x)` pointwise on `D(Δ)`**, with the memberships extracted from the adjoint
domain via KS3 — this is where the involution's content reaches the square. -/
theorem exists_conjModularSqrtInv_sq (x : (modularOp M Ω).domain) :
    ∃ (h1 : (x : H) ∈ (conjModularSqrtInv hcyc hsep).domain)
      (h2 : (conjModularSqrtInv hcyc hsep ⟨(x : H), h1⟩ : H)
        ∈ (conjModularSqrtInv hcyc hsep).domain),
      conjModularSqrtInv hcyc hsep
          ⟨conjModularSqrtInv hcyc hsep ⟨(x : H), h1⟩, h2⟩ = modularOp M Ω x := by
  classical
  obtain ⟨⟨hxS, hSx⟩, -⟩ := x.2
  set S : H →ₗ.[ℂ] Conj H := tomitaClosure M Ω with _hSdef
  set P : H →ₗ.[ℂ] H := conjModularSqrtInv hcyc hsep with _hPdef
  set b : H ≃ₗᵢ[ℂ] Conj H := modularWInv hcyc hsep with _hbdef
  have hSC : S = b.toLinearEquiv.toLinearMap.compPMap P :=
    tomitaClosure_eq_modularWInv_comp hcyc hsep
  have hPsa : P.adjoint = P :=
    LinearPMap.isSelfAdjoint_def.mp (conjModularSqrtInv_isSelfAdjoint hcyc hsep)
  have h1 : (x : H) ∈ P.domain := (mem_conjModularSqrtInv_domain_iff hcyc hsep).mpr hxS
  -- `D(b ∘ P) = D(P)` definitionally
  have hxC : (x : H) ∈ (b.toLinearEquiv.toLinearMap.compPMap P).domain := h1
  have hvec : S ⟨(x : H), hxS⟩ = b.toLinearEquiv.toLinearMap.compPMap P ⟨(x : H), hxC⟩ :=
    (le_of_eq hSC).2 rfl
  have hadj : S.adjoint = (b.toLinearEquiv.toLinearMap.compPMap P).adjoint := by rw [hSC]
  have hSxC : b.toLinearEquiv.toLinearMap.compPMap P ⟨(x : H), hxC⟩
      ∈ (b.toLinearEquiv.toLinearMap.compPMap P).adjoint.domain := by
    rw [← hvec, ← hadj]; exact hSx
  -- the composite value is `b (P x)`; unwind `b⁻¹` of it
  have hCval : b.toLinearEquiv.toLinearMap.compPMap P ⟨(x : H), hxC⟩ = b (P ⟨(x : H), h1⟩) := rfl
  have hbsymm : (b.symm (b.toLinearEquiv.toLinearMap.compPMap P ⟨(x : H), hxC⟩) : H)
      = P ⟨(x : H), h1⟩ := by
    rw [hCval, LinearIsometryEquiv.symm_apply_apply]
  -- KS3 membership: `P x ∈ D(P⋆) = D(P)`
  have hmem' := (mem_compPMap_adjoint_domain_iff b P).mp hSxC
  rw [hbsymm] at hmem'
  have hdomPa : P.adjoint.domain = P.domain := by rw [hPsa]
  have h2 : (P ⟨(x : H), h1⟩ : H) ∈ P.domain := (le_of_eq hdomPa) hmem'
  refine ⟨h1, h2, ?_⟩
  -- KS3 value: `Δ x = S⋆(Sx) = P⋆(b⁻¹(Sx)) = P (P x)`
  have hΔ := modularOp_apply (M := M) (Ω := Ω) x hxS hSx
  have hSadj : S.adjoint ⟨S ⟨(x : H), hxS⟩, hSx⟩
      = (b.toLinearEquiv.toLinearMap.compPMap P).adjoint
          ⟨b.toLinearEquiv.toLinearMap.compPMap P ⟨(x : H), hxC⟩, hSxC⟩ := by
    have hSx' : S ⟨(x : H), hxS⟩
        ∈ (b.toLinearEquiv.toLinearMap.compPMap P).adjoint.domain := by
      rw [← hadj]; exact hSx
    have hsub : (⟨S ⟨(x : H), hxS⟩, hSx'⟩ :
        ((b.toLinearEquiv.toLinearMap.compPMap P).adjoint).domain)
        = ⟨b.toLinearEquiv.toLinearMap.compPMap P ⟨(x : H), hxC⟩, hSxC⟩ :=
      Subtype.ext hvec
    calc S.adjoint ⟨S ⟨(x : H), hxS⟩, hSx⟩
        = (b.toLinearEquiv.toLinearMap.compPMap P).adjoint ⟨S ⟨(x : H), hxS⟩, hSx'⟩ :=
          (le_of_eq hadj).2 rfl
      _ = (b.toLinearEquiv.toLinearMap.compPMap P).adjoint
            ⟨b.toLinearEquiv.toLinearMap.compPMap P ⟨(x : H), hxC⟩, hSxC⟩ := by rw [hsub]
  have hKS3 := compPMap_adjoint_apply b P
    (conjModularSqrtInv_isSelfAdjoint hcyc hsep).dense_domain
    (b.toLinearEquiv.toLinearMap.compPMap P ⟨(x : H), hxC⟩) hSxC
  -- `P⋆ (b⁻¹ (Sx)) = P (P x)`
  have hPapp : P.adjoint ⟨(b.symm (b.toLinearEquiv.toLinearMap.compPMap P ⟨(x : H), hxC⟩) : H),
      (mem_compPMap_adjoint_domain_iff b P).mp hSxC⟩
      = P ⟨(P ⟨(x : H), h1⟩ : H), h2⟩ := by
    have hmemPa : (P ⟨(x : H), h1⟩ : H) ∈ P.adjoint.domain := (le_of_eq hdomPa.symm) h2
    have hsub2 : (⟨(b.symm (b.toLinearEquiv.toLinearMap.compPMap P ⟨(x : H), hxC⟩) : H),
        (mem_compPMap_adjoint_domain_iff b P).mp hSxC⟩ : P.adjoint.domain)
        = ⟨(P ⟨(x : H), h1⟩ : H), hmemPa⟩ := Subtype.ext hbsymm
    calc P.adjoint ⟨(b.symm (b.toLinearEquiv.toLinearMap.compPMap P ⟨(x : H), hxC⟩) : H),
          (mem_compPMap_adjoint_domain_iff b P).mp hSxC⟩
        = P.adjoint ⟨(P ⟨(x : H), h1⟩ : H), hmemPa⟩ := by rw [hsub2]
      _ = P ⟨(P ⟨(x : H), h1⟩ : H), h2⟩ := (le_of_eq hPsa).2 rfl
  rw [hΔ, hSadj, hKS3, hPapp]

/-! ### The two spectral squares and `posSqrt_unique` -/

/-- **The spectral square of `P₂` is `Δ`** (via the square bridge and the KS3 computation). -/
theorem sq_conjModularSqrtInv_eq_modularOp :
    pmapOfPVM (genToGroup (conjModularSqrtInv_isSelfAdjoint hcyc hsep))
        (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal = modularOp M Ω :=
  pmapOfPVM_sq_genToGroup_eq (conjModularSqrtInv_isSelfAdjoint hcyc hsep)
    (modularOp_isSelfAdjoint hcyc hsep)
    (fun x => exists_conjModularSqrtInv_sq hcyc hsep x)

/-- **The spectral square of `Δ^{½}` is `Δ`** — node 2.2 of the Field-3 plan, the graph-equality
upgrade of the pointwise `(Δ^{½})² = Δ`. -/
theorem sq_modularSqrt_eq_modularOp :
    pmapOfPVM (genToGroup (modularSqrt_isSelfAdjoint hcyc hsep))
        (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal = modularOp M Ω :=
  pmapOfPVM_sq_genToGroup_eq (modularSqrt_isSelfAdjoint hcyc hsep)
    (modularOp_isSelfAdjoint hcyc hsep)
    (fun x => ⟨modularOp_domain_le_modularSqrt_domain hcyc hsep x.2,
      modularSqrt_mem_domain_of_mem_modularOp hcyc hsep x,
      modularSqrt_sq_apply hcyc hsep x⟩)

/-- ★ **`J Δ^{-½} J⁻¹ = Δ^{½}`** — positive-square-root uniqueness applied to the second polar
factor: both are self-adjoint, `≥ 0`, and square to `Δ`. -/
theorem conjModularSqrtInv_eq_modularSqrt :
    conjModularSqrtInv hcyc hsep = modularSqrt hcyc hsep :=
  posSqrt_unique (conjModularSqrtInv_isSelfAdjoint hcyc hsep)
    (modularSqrt_isSelfAdjoint hcyc hsep)
    (conjModularSqrtInv_borelMeasure_Iio_zero hcyc hsep)
    (modularSqrt_borelMeasure_Iio_zero hcyc hsep)
    ((sq_conjModularSqrtInv_eq_modularOp hcyc hsep).trans
      (sq_modularSqrt_eq_modularOp hcyc hsep).symm)

/-! ### ★★ `J² = 1` — the `ModularData.J_involutive` field -/

/-- **`J (J (Δ^{½} y)) = Δ^{½} y`** for `y ∈ D(Δ^{½})`: reading `P₂ = Δ^{½}` back through the
second polar value `P₂ y = J(S̃ y)` and the polar identity `S̃ y = J(Δ^{½} y)`. -/
theorem modularConjugation_involutive_on_range (y : (modularSqrt hcyc hsep).domain) :
    modularConjugation hcyc hsep
        (modularConjugation hcyc hsep (modularSqrt hcyc hsep y)) = modularSqrt hcyc hsep y := by
  have hyS : (y : H) ∈ (tomitaClosure M Ω).domain :=
    modularSqrt_domain_le_tomitaClosure_domain hcyc hsep y.2
  have hyP : (y : H) ∈ (conjModularSqrtInv hcyc hsep).domain :=
    (mem_conjModularSqrtInv_domain_iff hcyc hsep).mpr hyS
  -- `P₂ y = J (S̃ y)`
  have h1 := conjModularSqrtInv_apply_eq hcyc hsep hyS hyP
  -- `P₂ y = Δ^{½} y`  (posSqrt uniqueness)
  have h2 : conjModularSqrtInv hcyc hsep ⟨(y : H), hyP⟩ = modularSqrt hcyc hsep y := by
    have hle := le_of_eq (conjModularSqrtInv_eq_modularSqrt hcyc hsep)
    exact hle.2 rfl
  -- `S̃ y = J (Δ^{½} y)`  (polar identity)
  have hpolar := tomita_eq_modularConjugation_modularSqrt_full hcyc hsep y
  have h3 : ofConj (tomitaClosure M Ω
      ⟨(y : H), modularSqrt_domain_le_tomitaClosure_domain hcyc hsep y.2⟩)
      = modularConjugation hcyc hsep (modularSqrt hcyc hsep y) := by
    have h := congrArg ofConj hpolar
    rw [Conj.coe_toConjₗᵢ (E := H), Conj.ofConj_toConj] at h
    exact h.symm
  -- align the `S`-subtype in `h1` with the one in `h3`
  have h4 : conjModularSqrtInv hcyc hsep ⟨(y : H), hyP⟩
      = modularConjugation hcyc hsep
          (modularConjugation hcyc hsep (modularSqrt hcyc hsep y)) := by
    rw [h1]
    exact congrArg _ (by rw [← h3])
  rw [← h4, h2]

/-- ★★ **`J² = 1`** — the modular conjugation is an involution (`ModularData.J_involutive`).
The identity holds on the dense set `Δ^{½}(D(Δ))` and extends by continuity. -/
theorem modularConjugation_involutive (x : H) :
    modularConjugation hcyc hsep (modularConjugation hcyc hsep x) = x := by
  have hdense : Dense (Set.range (modularSqrtOnModularDomain hcyc hsep)) :=
    denseRange_modularSqrtOnModularDomain hcyc hsep
  have hcont : Continuous fun v : H =>
      modularConjugation hcyc hsep (modularConjugation hcyc hsep v) :=
    (modularConjugation hcyc hsep).continuous.comp (modularConjugation hcyc hsep).continuous
  have heq : Set.EqOn
      (fun v : H => modularConjugation hcyc hsep (modularConjugation hcyc hsep v)) id
      (Set.range (modularSqrtOnModularDomain hcyc hsep)) := by
    rintro _ ⟨w, rfl⟩
    rw [modularSqrtOnModularDomain_apply]
    exact modularConjugation_involutive_on_range hcyc hsep _
  exact congrFun (Continuous.ext_on hdense hcont continuous_id heq) x

/-- `J⁻¹ = J`. -/
theorem modularConjugation_symm_eq :
    (modularConjugation hcyc hsep).symm = modularConjugation hcyc hsep := by
  ext x
  apply (modularConjugation hcyc hsep).injective
  rw [LinearIsometryEquiv.apply_symm_apply, modularConjugation_involutive hcyc hsep]

/-! ### The conjugation relations `J Δ^{½} J⁻¹ = Δ^{-½}` and `J Δ J⁻¹ = Δ⁻¹` -/

omit [CompleteSpace H] in
/-- Conjugating twice by an involutive antiunitary is the identity. -/
theorem conjPMap_conjPMap_of_involutive {e : H ≃ₗᵢ⋆[ℂ] H} (he : ∀ x, e (e x) = x)
    (A : H →ₗ.[ℂ] H) : conjPMap e (conjPMap e A) = A := by
  have hsymm : ∀ x, e.symm x = e x := fun x =>
    e.injective (by rw [LinearIsometryEquiv.apply_symm_apply, he])
  have hz : ∀ z : H, e.symm (e.symm z) = z := fun z => by rw [hsymm, hsymm, he]
  refine LinearPMap.ext_iff.mpr ⟨?_, ?_⟩
  · ext z
    rw [mem_conjPMap_domain_iff, mem_conjPMap_domain_iff, hz]
  · intro z hf hg
    have hf' : e.symm z ∈ (conjPMap e A).domain := hf
    have hf'' : e.symm (e.symm z) ∈ A.domain := hf'
    have h1 : conjPMap e (conjPMap e A) ⟨z, hf⟩
        = e (e (A ⟨e.symm (e.symm z), hf''⟩)) := rfl
    have hsub : (⟨e.symm (e.symm z), hf''⟩ : A.domain) = ⟨z, hg⟩ := Subtype.ext (hz z)
    rw [h1, he, hsub]

/-- ★ **`J Δ^{½} J⁻¹ = Δ^{-½}`** — the Stage-5 target (plan node 5.1), by conjugating
`J Δ^{-½} J⁻¹ = Δ^{½}` once more with the now-involutive `J`. -/
theorem conjModularSqrt_eq_modularSqrtInv :
    conjModularSqrt hcyc hsep = modularSqrtInv hcyc hsep := by
  -- restate the uniqueness output at the unfolded `conjPMap` form (definitional)
  have h0 : conjPMap (modularConjugation hcyc hsep) (modularSqrtInv hcyc hsep)
      = modularSqrt hcyc hsep := conjModularSqrtInv_eq_modularSqrt hcyc hsep
  have h := congrArg (conjPMap (modularConjugation hcyc hsep)) h0
  rw [conjPMap_conjPMap_of_involutive (modularConjugation_involutive hcyc hsep)] at h
  exact h.symm

/-- **The spectral square of `Δ^{-½}` is `Δ⁻¹`** (Stage-0 pointwise data through the bridge). -/
theorem sq_modularSqrtInv_eq_modularOpInv :
    pmapOfPVM (genToGroup (modularSqrtInv_isSelfAdjoint hcyc hsep))
        (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal = modularOpInv hcyc hsep :=
  pmapOfPVM_sq_genToGroup_eq (modularSqrtInv_isSelfAdjoint hcyc hsep)
    (modularOpInv_isSelfAdjoint hcyc hsep)
    (fun x => ⟨modularOpInv_domain_le_modularSqrtInv_domain hcyc hsep x.2,
      modularSqrtInv_mem_domain_of_mem_modularOpInv hcyc hsep x,
      modularSqrtInv_sq_apply hcyc hsep x⟩)

/-- **`J Δ^{½} J⁻¹ = Δ^{-½}` read pointwise**: for `v ∈ D(Δ^{½})`, `J v ∈ D(Δ^{-½})` and
`Δ^{-½}(J v) = J (Δ^{½} v)`. -/
theorem modularSqrtInv_apply_conj (v : (modularSqrt hcyc hsep).domain) :
    ∃ hmem : modularConjugation hcyc hsep (v : H) ∈ (modularSqrtInv hcyc hsep).domain,
      modularSqrtInv hcyc hsep ⟨modularConjugation hcyc hsep (v : H), hmem⟩
        = modularConjugation hcyc hsep (modularSqrt hcyc hsep v) := by
  have hhalf : conjModularSqrt hcyc hsep = modularSqrtInv hcyc hsep :=
    conjModularSqrt_eq_modularSqrtInv hcyc hsep
  have hmemC : modularConjugation hcyc hsep (v : H) ∈ (conjModularSqrt hcyc hsep).domain := by
    change (modularConjugation hcyc hsep).symm (modularConjugation hcyc hsep (v : H))
        ∈ (modularSqrt hcyc hsep).domain
    rw [LinearIsometryEquiv.symm_apply_apply]
    exact v.2
  have hmem : modularConjugation hcyc hsep (v : H) ∈ (modularSqrtInv hcyc hsep).domain :=
    hhalf ▸ hmemC
  refine ⟨hmem, ?_⟩
  have hval : conjModularSqrt hcyc hsep ⟨modularConjugation hcyc hsep (v : H), hmemC⟩
      = modularSqrtInv hcyc hsep ⟨modularConjugation hcyc hsep (v : H), hmem⟩ :=
    (le_of_eq hhalf).2 rfl
  rw [← hval]
  have h1 : conjModularSqrt hcyc hsep ⟨modularConjugation hcyc hsep (v : H), hmemC⟩
      = modularConjugation hcyc hsep (modularSqrt hcyc hsep
          ⟨(modularConjugation hcyc hsep).symm (modularConjugation hcyc hsep (v : H)),
            hmemC⟩) := rfl
  rw [h1]
  exact congrArg (fun w => modularConjugation hcyc hsep (modularSqrt hcyc hsep w))
    (Subtype.ext (LinearIsometryEquiv.symm_apply_apply _ _))

/-- ★ **`J Δ J⁻¹ = Δ⁻¹`** — the Field-3 gate (plan node 3.5).  Pointwise on `D(JΔJ⁻¹)`,
`(JΔJ⁻¹) z = J(Δ^{½}(Δ^{½}(J⁻¹z))) = Δ^{-½}(Δ^{-½} z)` by the conjugation relation applied twice,
so `JΔJ⁻¹` is the spectral square of `Δ^{-½}` (the bridge), which is `Δ⁻¹`. -/
theorem conjModularOp_eq_modularOpInv :
    conjPMap (modularConjugation hcyc hsep) (modularOp M Ω) = modularOpInv hcyc hsep := by
  have hL : IsSelfAdjoint (conjPMap (modularConjugation hcyc hsep) (modularOp M Ω)) :=
    conjPMap_isSelfAdjoint (inner_modularConjugation hcyc hsep)
      (modularOp_isSelfAdjoint hcyc hsep)
  have key : pmapOfPVM (genToGroup (modularSqrtInv_isSelfAdjoint hcyc hsep))
      (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal
      = conjPMap (modularConjugation hcyc hsep) (modularOp M Ω) := by
    refine pmapOfPVM_sq_genToGroup_eq (modularSqrtInv_isSelfAdjoint hcyc hsep) hL (fun x => ?_)
    -- `u := J⁻¹ x ∈ D(Δ)`
    have hu : (modularConjugation hcyc hsep).symm (x : H) ∈ (modularOp M Ω).domain := x.2
    have huQ : (modularConjugation hcyc hsep).symm (x : H) ∈ (modularSqrt hcyc hsep).domain :=
      modularOp_domain_le_modularSqrt_domain hcyc hsep hu
    -- first application of `J Δ^{½} J⁻¹ = Δ^{-½}`: at `v := u`, so at the point `J u = x`
    obtain ⟨hm1, hv1⟩ := modularSqrtInv_apply_conj hcyc hsep
      ⟨(modularConjugation hcyc hsep).symm (x : H), huQ⟩
    have hx1 : (x : H) ∈ (modularSqrtInv hcyc hsep).domain := by
      rw [← LinearIsometryEquiv.apply_symm_apply (modularConjugation hcyc hsep) (x : H)]
      exact hm1
    have hxeq : (⟨modularConjugation hcyc hsep
          ((modularConjugation hcyc hsep).symm (x : H)), hm1⟩ :
        (modularSqrtInv hcyc hsep).domain) = ⟨(x : H), hx1⟩ :=
      Subtype.ext (LinearIsometryEquiv.apply_symm_apply _ _)
    rw [hxeq] at hv1
    -- hv1 : `Δ^{-½} ⟨x, hx1⟩ = J (Δ^{½} u)`
    -- second application: at `v := Δ^{½} u`
    have hsq_mem : (modularSqrt hcyc hsep
        ⟨(modularConjugation hcyc hsep).symm (x : H), huQ⟩ : H)
        ∈ (modularSqrt hcyc hsep).domain :=
      modularSqrt_mem_domain_of_mem_modularOp hcyc hsep
        ⟨(modularConjugation hcyc hsep).symm (x : H), hu⟩
    obtain ⟨hm2, hv2⟩ := modularSqrtInv_apply_conj hcyc hsep
      ⟨modularSqrt hcyc hsep ⟨(modularConjugation hcyc hsep).symm (x : H), huQ⟩, hsq_mem⟩
    -- assemble the composite membership
    have hx2 : (modularSqrtInv hcyc hsep ⟨(x : H), hx1⟩ : H)
        ∈ (modularSqrtInv hcyc hsep).domain := by
      rw [hv1]; exact hm2
    refine ⟨hx1, hx2, ?_⟩
    -- rewrite the outer subtype through `hv1`, then apply `hv2`
    have hsub2 : (⟨(modularSqrtInv hcyc hsep ⟨(x : H), hx1⟩ : H), hx2⟩ :
        (modularSqrtInv hcyc hsep).domain)
        = ⟨modularConjugation hcyc hsep (modularSqrt hcyc hsep
            ⟨(modularConjugation hcyc hsep).symm (x : H), huQ⟩), hm2⟩ :=
      Subtype.ext hv1
    rw [hsub2, hv2]
    -- `J (Δ^{½}(Δ^{½}u)) = J (Δ u) = (JΔJ⁻¹) x`
    have hΔ : modularSqrt hcyc hsep
        ⟨(modularSqrt hcyc hsep ⟨(modularConjugation hcyc hsep).symm (x : H), huQ⟩ : H),
          hsq_mem⟩
        = modularOp M Ω ⟨(modularConjugation hcyc hsep).symm (x : H), hu⟩ :=
      modularSqrt_sq_apply hcyc hsep ⟨(modularConjugation hcyc hsep).symm (x : H), hu⟩
    rw [conjPMap_apply]
    exact congrArg _ hΔ
  exact key.symm.trans (sq_modularSqrtInv_eq_modularOpInv hcyc hsep)

end Spectra.TomitaTakesaki
