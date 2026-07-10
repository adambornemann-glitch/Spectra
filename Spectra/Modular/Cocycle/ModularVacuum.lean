/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.Cocycle.PolarIsometry
/-!
# The vacuum-fixing facts of modular theory (R4a)

For a cyclic–separating vector `Ω` of a von Neumann algebra `M`, the cyclic vector `Ω` is fixed by
all of the modular data:

* `modularOp_vacuum` — **`Δ Ω = Ω`** (`Ω` is a `Δ`-eigenvector at `1`);
* `modularSqrt_vacuum` — **`Δ^{½} Ω = Ω`**;
* `modularConjugation_fixes_vacuum` — **`J Ω = Ω`** (Tomita's `J Ω = Ω`).

(The fourth vacuum-fixing fact `Δ^{it} Ω = Ω` is deferred; see the note at the end of this comment.)

These are the "vacuum-fixing" identities of Tomita–Takesaki theory.  `Δ Ω = Ω` comes from the direct
computation `S Ω = toConj Ω` and `S⋆ (toConj Ω) = Ω` (both `Ω = 1·Ω`, `1 ∈ M ∩ M'`), so
`Δ Ω = S⋆ S Ω = Ω`.  Feeding this eigenvector into the spectral atom `E({1})Ω = Ω` and the `√`
calculus gives `Δ^{½} Ω = Ω`, and the polar relation `S = J Δ^{½}` then forces `J Ω = Ω`.

The remaining vacuum-fixing fact `Δ^{it} Ω = Ω` (the modular flow fixes `Ω`) is **not** proved here:
`modularFlow = borelModularGroup (cayleyTransform Δ) …` acts through the *Borel* calculus of the
Cayley transform `V` (symbol `modularSymbol V t = λ^{it}`), whose generator is `log Δ` (not `Δ`),
and the codebase currently lacks the "`borelCalculus V g` on a `V`-eigenvector `ψ` (with
`V ψ = z • ψ`) equals `g z • ψ`" lemma — equivalently, that the spectral measure of an eigenvector
is a Dirac mass. That lemma (or, alternatively, `generator (modularFlow) = log Δ` via a
Stone/Yosida/Borel bridge) is the missing infrastructure; with either, `Ω` being a `Δ`-eigenvector
at `1` (`modularOp_vacuum`) gives `modularSymbol V t (cayley 1) = exp(i t · log 1) = 1`, hence
`Δ^{it} Ω = Ω`.
-/

open scoped InnerProductSpace
open Spectra.Conj
open Complex MeasureTheory Filter Topology
open Spectra.QuantumMechanics.SpectralTheory
open Spectra.OneParameterUnitaryGroup
open Spectra.Borel
open Spectra.YosidaHille

namespace Spectra.TomitaTakesaki

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

/-! ## Lemma A — `Δ Ω = Ω`

Throughout we use `(1 : H →L[ℂ] H) Ω = Ω` (which holds by `rfl`) so that `Ω = 1 · Ω` with `1 ∈ M`
and `1 ∈ M'`; the membership proofs for `Ω` and `1 Ω` are therefore definitionally interchangeable.
-/

/-- `Ω ∈ D(S)`: the vacuum lies in the domain of the Tomita operator (it is `1 · Ω` with `1 ∈ M`).
-/
theorem vacuum_mem_tomitaClosure_domain :
    Ω ∈ (tomitaClosure M Ω).domain := by
  have hΩop : Ω ∈ (tomitaOp M Ω).domain := by
    rw [tomitaOp_domain_eq_span]
    exact Submodule.subset_span ⟨(1 : H →L[ℂ] H), one_mem M, rfl⟩
  exact (LinearPMap.le_closure (tomitaOp M Ω)).1 hΩop

/-- `S Ω = toConj Ω`: the Tomita operator sends the vacuum to its conjugate (both `= 1 · Ω`,
`star 1 = 1`). -/
theorem tomitaClosure_vacuum (hsep : IsSeparating M Ω) :
    tomitaClosure M Ω ⟨Ω, vacuum_mem_tomitaClosure_domain⟩ = toConj Ω := by
  have hΩop : Ω ∈ (tomitaOp M Ω).domain := by
    rw [tomitaOp_domain_eq_span]
    exact Submodule.subset_span ⟨(1 : H →L[ℂ] H), one_mem M, rfl⟩
  have hagree : tomitaOp M Ω ⟨Ω, hΩop⟩
      = tomitaClosure M Ω ⟨Ω, vacuum_mem_tomitaClosure_domain⟩ :=
    (LinearPMap.le_closure (tomitaOp M Ω)).2 rfl
  -- `S₀ Ω = S₀ (1 · Ω) = toConj (star 1 · Ω) = toConj Ω` (using `1 Ω = Ω` definitionally).
  have hop : tomitaOp M Ω ⟨Ω, hΩop⟩ = toConj ((star (1 : H →L[ℂ] H)) Ω) :=
    tomitaOp_apply M Ω hsep (one_mem M) hΩop
  rw [← hagree, hop, star_one]
  rfl

/-- `toConj Ω ∈ D(S⋆)` with `S⋆ (toConj Ω) = Ω`: the second half of `Δ Ω = Ω`, proved directly from
the formal-adjoint relation for `S ≤ S₀⋆⋆` and `S₀⋆ (toConj Ω) = Ω` (both `1 · Ω`, `star 1 = 1`). -/
theorem tomitaClosure_adjoint_vacuum (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    ∃ htcΩ : toConj Ω ∈ (tomitaClosure M Ω).adjoint.domain,
      (tomitaClosure M Ω).adjoint ⟨toConj Ω, htcΩ⟩ = Ω := by
  have hAdense : Dense ((tomitaOp M Ω).adjoint.domain : Set (Conj H)) :=
    tomitaOp_adjoint_domain_dense hsep
  have hxle : tomitaClosure M Ω ≤ (tomitaOp M Ω).adjoint.adjoint :=
    tomitaClosure_le_adjoint_adjoint hcyc hsep
  have hFA' := LinearPMap.adjoint_isFormalAdjoint (T := (tomitaOp M Ω).adjoint) hAdense
  -- `toConj Ω ∈ D(S₀⋆)` with value `Ω` (note `1 Ω = Ω` by `rfl`, `star 1 = 1`).
  have hη' : toConj Ω ∈ (tomitaOp M Ω).adjoint.domain :=
    toConj_mem_adjoint_domain hsep (one_mem M.commutant)
  have hval : (tomitaOp M Ω).adjoint ⟨toConj Ω, hη'⟩ = Ω := by
    have h := tomitaAdjoint_apply_commutant hcyc hsep (one_mem M.commutant)
    rw [star_one] at h
    exact h
  -- For each `x ∈ D(S)`, `⟪S x, toConj Ω⟫ = ⟪x, Ω⟫` (formal adjoint of `S ≤ S₀⋆⋆`).
  have hpair : ∀ x : (tomitaClosure M Ω).domain,
      ⟪tomitaClosure M Ω x, toConj Ω⟫_ℂ = ⟪(x : H), Ω⟫_ℂ := by
    intro x
    have hxmem : (x : H) ∈ ((tomitaOp M Ω).adjoint).adjoint.domain := hxle.1 x.2
    have hxval : ((tomitaOp M Ω).adjoint).adjoint ⟨(x : H), hxmem⟩ = tomitaClosure M Ω x :=
      (hxle.2 rfl).symm
    have key := hFA' ⟨(x : H), hxmem⟩ ⟨toConj Ω, hη'⟩
    rw [hxval, hval] at key
    exact key
  -- `toConj Ω ∈ D(S⋆)` via `mem_adjoint_domain_of_exists`.
  have htcΩ : toConj Ω ∈ (tomitaClosure M Ω).adjoint.domain := by
    refine LinearPMap.mem_adjoint_domain_of_exists (toConj Ω) ⟨Ω, fun x => ?_⟩
    rw [← inner_conj_symm (𝕜 := ℂ) (toConj Ω) (tomitaClosure M Ω x), hpair x, inner_conj_symm]
  refine ⟨htcΩ, ?_⟩
  -- Value `S⋆ (toConj Ω) = Ω` via the formal-adjoint relation + density (avoids the slow
  -- `adjoint_apply_eq` `whnf` on the closure): `⟪S⋆(toConjΩ), x⟫ = ⟪Ω, x⟫` for all `x`, then
  -- `S⋆(toConjΩ) - Ω ⊥ D(S)` dense forces `S⋆(toConjΩ) = Ω`.
  have hdense : Dense ((tomitaClosure M Ω).domain : Set H) := tomitaClosure_domain_dense hcyc
  have hFA := LinearPMap.adjoint_isFormalAdjoint (T := tomitaClosure M Ω) hdense
  set w := (tomitaClosure M Ω).adjoint ⟨toConj Ω, htcΩ⟩ with hw
  have hkey : ∀ x : (tomitaClosure M Ω).domain, ⟪w, (x : H)⟫_ℂ = ⟪Ω, (x : H)⟫_ℂ := by
    intro x
    have h := hFA ⟨toConj Ω, htcΩ⟩ x
    rw [hw, h]
    change ⟪toConj Ω, tomitaClosure M Ω x⟫_ℂ = ⟪Ω, (x : H)⟫_ℂ
    rw [← inner_conj_symm (𝕜 := ℂ) (toConj Ω) (tomitaClosure M Ω x), hpair x, inner_conj_symm]
  have hsub0 : w - Ω = 0 := by
    have hd : ∀ z ∈ (tomitaClosure M Ω).domain, ⟪w - Ω, z⟫_ℂ = 0 := by
      intro z hz; rw [inner_sub_left, hkey ⟨z, hz⟩, sub_self]
    have hperp : (w - Ω) ∈ ((tomitaClosure M Ω).domain)ᗮ := (Submodule.mem_orthogonal' _ _).mpr hd
    have hbot : ((tomitaClosure M Ω).domain)ᗮ = ⊥ :=
      Submodule.topologicalClosure_eq_top_iff.mp
        (Submodule.dense_iff_topologicalClosure_eq_top.mp hdense)
    rw [hbot, Submodule.mem_bot] at hperp
    exact hperp
  exact sub_eq_zero.mp hsub0

/-- `Ω ∈ D(Δ)`: the vacuum lies in the modular domain. -/
theorem vacuum_mem_modularOp_domain (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    Ω ∈ (modularOp M Ω).domain := by
  obtain ⟨htcΩ, _⟩ := tomitaClosure_adjoint_vacuum hcyc hsep
  have hΩS : Ω ∈ (tomitaClosure M Ω).domain := vacuum_mem_tomitaClosure_domain
  have hSΩmem : tomitaClosure M Ω ⟨Ω, hΩS⟩ ∈ (tomitaClosure M Ω).adjoint.domain := by
    rw [tomitaClosure_vacuum hsep]; exact htcΩ
  exact ⟨⟨hΩS, hSΩmem⟩, hΩS⟩

/-- **Lemma A — `Δ Ω = Ω`.**  The vacuum is a `Δ`-eigenvector at eigenvalue `1`:
`Δ Ω = S⋆ (S Ω) = S⋆ (toConj Ω) = Ω`. -/
theorem modularOp_vacuum (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)
    (hΩ : Ω ∈ (modularOp M Ω).domain) : modularOp M Ω ⟨Ω, hΩ⟩ = Ω := by
  obtain ⟨htcΩ, hvalue⟩ := tomitaClosure_adjoint_vacuum hcyc hsep
  obtain ⟨⟨hxS, hSx⟩, _hΩS⟩ := id hΩ
  rw [modularOp_apply ⟨Ω, hΩ⟩ hxS hSx]
  -- `S Ω = toConj Ω`, and `S⋆ (toConj Ω) = Ω`.
  have hSΩ : tomitaClosure M Ω ⟨Ω, hxS⟩ = toConj Ω := tomitaClosure_vacuum hsep
  have hcast2 : (⟨tomitaClosure M Ω ⟨Ω, hxS⟩, hSx⟩ : (tomitaClosure M Ω).adjoint.domain)
      = ⟨toConj Ω, htcΩ⟩ := Subtype.ext hSΩ
  rw [hcast2, hvalue]

/-! ## Lemma B — `Ω` in the spectral atom `{1}` of `Δ`

The unitary group of `Δ = modularOp M Ω` (mirroring `PolarIsometry.lean`).  Its spectral projection
`spectralProjection U` is definitionally the projection of
`PVM.spectralPVM (modularOp_isSelfAdjoint …)`, so the eigenspace bridge
`spectralPVM_proj_singleton_eq_self_iff` transfers directly. -/

/-- The unitary group of the modular operator `Δ = modularOp M Ω`. -/
private noncomputable abbrev modularGroup (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    OneParameterUnitaryGroup (H := H) :=
  genToGroup (modularOp_isSelfAdjoint hcyc hsep)

/-- **Lemma B — `E_Δ({1}) Ω = Ω`.**  The vacuum lies in the spectral atom of `Δ` at eigenvalue `1`
(it is a `Δ`-eigenvector at `1` by Lemma A), phrased through the group spectral projection
`spectralProjection (modularGroup …)` (definitionally `E_Δ({1})`). -/
theorem spectralProjection_singleton_one_vacuum (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    spectralProjection (modularGroup hcyc hsep) ({(1 : ℝ)} : Set ℝ) (measurableSet_singleton 1) Ω
      = Ω := by
  have heig : modularOp M Ω ⟨Ω, vacuum_mem_modularOp_domain hcyc hsep⟩ = ((1 : ℝ) : ℂ) • Ω := by
    rw [modularOp_vacuum hcyc hsep (vacuum_mem_modularOp_domain hcyc hsep), Complex.ofReal_one,
      one_smul]
  have hE := (spectralPVM_proj_singleton_eq_self_iff (modularOp_isSelfAdjoint hcyc hsep)
    (lam := 1) Ω).mpr ⟨vacuum_mem_modularOp_domain hcyc hsep, heig⟩
  -- `(PVM.spectralPVM hA).proj {1} _ = spectralProjection (genToGroup hA) {1} _` definitionally.
  exact hE

/-! ## Lemma C — `Δ^{½} Ω = Ω` -/

/-- **Lemma C (operator identity on the atom).**  `Δ^{½}(E({1})Ω) = E({1})Ω`.  Truncating the `√`
calculus, `pmapTrunc U √ m (E({1})Ω) = Φ(truncSym √ m · 1_{{1}}) Ω`, which for `m ≥ 1` equals
`Φ(1_{{1}}) Ω = E({1})Ω` (on `{1}`, `truncSym √ m 1 = √1 = 1`); an eventually-constant sequence
converges to that constant, while `pmapOfPVM_apply_tendsto` says it converges to `Δ^{½}(E({1})Ω)`.
Uniqueness of limits finishes. -/
theorem modularSqrt_atom_apply (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)
    (hmem : spectralProjection (modularGroup hcyc hsep) ({(1 : ℝ)} : Set ℝ)
        (measurableSet_singleton 1) Ω ∈ (modularOp M Ω).domain) :
    modularSqrt hcyc hsep
        ⟨spectralProjection (modularGroup hcyc hsep) ({(1 : ℝ)} : Set ℝ)
          (measurableSet_singleton 1) Ω,
          modularOp_domain_le_modularSqrt_domain hcyc hsep hmem⟩
      = spectralProjection (modularGroup hcyc hsep) ({(1 : ℝ)} : Set ℝ)
          (measurableSet_singleton 1) Ω := by
  set U := modularGroup hcyc hsep with _hU
  set xn := spectralProjection U ({(1 : ℝ)} : Set ℝ) (measurableSet_singleton 1) Ω with hxn
  have hxnL2 : Integrable (fun s => ‖(Real.sqrt s : ℂ)‖ ^ 2) (borelMeasure U xn) :=
    (ProjValMeasure.mem_pmapDomain _).mp (modularOp_domain_le_modularSqrt_domain hcyc hsep hmem)
  -- for `m ≥ 1`, the truncated calculus on `xn` collapses to `Φ(1_{{1}}) Ω = xn`.
  have hev : ∀ᶠ m : ℕ in atTop,
      pmapTrunc U (fun s => (Real.sqrt s : ℂ)) measurable_sqrtC m xn = xn := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    rw [pmapTrunc_apply]
    have hE : xn = spectralCalculus U (Set.indicator ({(1 : ℝ)} : Set ℝ) fun _ => (1 : ℂ))
        (measurable_const.indicator (measurableSet_singleton 1)) (indicator_one_bdd _) Ω := by
      rw [hxn]; rfl
    rw [hE, ← ContinuousLinearMap.mul_apply,
      spectralCalculus_mul U (Set.indicator ({(1 : ℝ)} : Set ℝ) fun _ => (1 : ℂ))
        (truncSym (fun t => (Real.sqrt t : ℂ)) m)
        (measurable_const.indicator (measurableSet_singleton 1)) (indicator_one_bdd _)
        (measurable_truncSym measurable_sqrtC m) (truncSym_bdd _ m)
        ((measurable_truncSym measurable_sqrtC m).mul
          (measurable_const.indicator (measurableSet_singleton 1)))
        (bounded_mul (truncSym_bdd _ m) (indicator_one_bdd _))]
    refine congrArg (fun T : H →L[ℂ] H => T Ω) ?_
    refine spectralCalculus_congr U ?_ _ _ _ _
    funext s
    by_cases hs : s ∈ ({(1 : ℝ)} : Set ℝ)
    · rw [Set.mem_singleton_iff] at hs; subst hs
      rw [Set.indicator_of_mem (Set.mem_singleton _), mul_one, truncSym_apply, if_pos]
      · rw [Real.sqrt_one, Complex.ofReal_one]
      · rw [Complex.norm_real, Real.norm_eq_abs, Real.sqrt_one, abs_one]
        calc (1 : ℝ) = ((1 : ℕ) : ℝ) := by norm_num
          _ ≤ (m : ℝ) := by exact_mod_cast hm
    · rw [Set.indicator_of_notMem hs, mul_zero]
  have htends1 := pmapOfPVM_apply_tendsto U (fun s => (Real.sqrt s : ℂ)) measurable_sqrtC hxnL2
  have htends2 : Tendsto (fun m => pmapTrunc U (fun s => (Real.sqrt s : ℂ)) measurable_sqrtC m xn)
      atTop (𝓝 xn) :=
    Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev) tendsto_const_nhds
  exact tendsto_nhds_unique htends1 htends2

/-- **Lemma C — `Δ^{½} Ω = Ω`.**  The vacuum is fixed by the modular square root.  Since
`E({1})Ω = Ω` (Lemma B), the operator identity `Δ^{½}(E({1})Ω) = E({1})Ω` on the atom gives the
result. -/
theorem modularSqrt_vacuum (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)
    (hΩ : Ω ∈ (modularSqrt hcyc hsep).domain) : modularSqrt hcyc hsep ⟨Ω, hΩ⟩ = Ω := by
  have hEfix : spectralProjection (modularGroup hcyc hsep) ({(1 : ℝ)} : Set ℝ)
      (measurableSet_singleton 1) Ω = Ω := spectralProjection_singleton_one_vacuum hcyc hsep
  have hmem : spectralProjection (modularGroup hcyc hsep) ({(1 : ℝ)} : Set ℝ)
      (measurableSet_singleton 1) Ω ∈ (modularOp M Ω).domain := by
    rw [hEfix]; exact vacuum_mem_modularOp_domain hcyc hsep
  have hatom := modularSqrt_atom_apply hcyc hsep hmem
  -- `hatom : Δ^{½}⟨E({1})Ω, _⟩ = E({1})Ω`.  Convert the subtype element `⟨Ω, hΩ⟩ = ⟨E({1})Ω, _⟩`
  -- (via `E({1})Ω = Ω` and proof-irrelevance), then rewrite `E({1})Ω = Ω` on the value.
  have hcast : (⟨Ω, hΩ⟩ : (modularSqrt hcyc hsep).domain)
      = ⟨spectralProjection (modularGroup hcyc hsep) ({(1 : ℝ)} : Set ℝ)
          (measurableSet_singleton 1) Ω, modularOp_domain_le_modularSqrt_domain hcyc hsep hmem⟩ :=
    Subtype.ext hEfix.symm
  rw [hcast, hatom, hEfix]

/-! ## Lemma D — `J Ω = Ω` -/

/-- **Lemma D — `J Ω = Ω`** (Tomita's `J Ω = Ω`).  The modular conjugation fixes the vacuum.  From
the polar relation `S = J Δ^{½}` (`tomita_eq_modularConjugation_modularSqrt`): at `Ω ∈ D(Δ)`,
`toConj (J (Δ^{½} Ω)) = S Ω`, i.e. `toConj (J Ω) = toConj Ω` (Lemma C `Δ^{½} Ω = Ω`, Lemma A
`S Ω = toConj Ω`); antiunitary injectivity of `toConj` gives `J Ω = Ω`. -/
theorem modularConjugation_fixes_vacuum (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    modularConjugation hcyc hsep Ω = Ω := by
  have hΩΔ : Ω ∈ (modularOp M Ω).domain := vacuum_mem_modularOp_domain hcyc hsep
  have hpolar := tomita_eq_modularConjugation_modularSqrt hcyc hsep ⟨Ω, hΩΔ⟩
  -- inner argument `Δ^{½} Ω = Ω` (Lemma C).
  have hsqrt : modularSqrtOnModularDomain hcyc hsep ⟨Ω, hΩΔ⟩ = Ω := by
    rw [modularSqrtOnModularDomain_apply]
    exact modularSqrt_vacuum hcyc hsep _
  -- right side `S Ω = toConj Ω` (Lemma A).
  have htomita : tomitaOnModularDomain M Ω ⟨Ω, hΩΔ⟩ = toConj Ω := by
    rw [tomitaOnModularDomain_apply]
    exact tomitaClosure_vacuum hsep
  rw [hsqrt, htomita] at hpolar
  -- `hpolar : toConj (J Ω) = toConj Ω`; apply `toConj`-injectivity.
  exact Conj.ofConj_injective hpolar

end Spectra.TomitaTakesaki
