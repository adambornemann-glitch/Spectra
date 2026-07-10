/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.Cocycle.ModularVacuum
import Spectra.Modular.TomitaTakesaki.ModularFlow
import Spectra.StoneBridge.CalculusBridge
import Spectra.StoneBridge.Basic
/-!
# The modular flow fixes the vacuum: `Δ^{it} Ω = Ω` (R4a, field 5)

This file discharges the remaining structural vacuum-fixing field of `ModularData`,
`modularFlow_fixes_vacuum : ∀ t, (modularFlow …).U t Ω = Ω`, completing the trio started in
`ModularVacuum.lean` (`Δ Ω = Ω`, `Δ^{½} Ω = Ω`, `J Ω = Ω`).

## The route (Stone/genToGroup bridge, not the Cayley eigenvector)

`modularFlow = borelModularGroup (cayleyTransform Δ)` acts through the **Borel calculus of the
Cayley transform** `V = cayley Δ` (symbol `modularSymbol V t = λ^{it}`, generator `log Δ`), not
through `Δ`'s own spectral projections. Rather than build a fresh "spectral measure of a
`V`-eigenvector is a Dirac mass" lemma, we route through the already-proven, **unconditional**
bridge `spectralCalculus_stoneGroup_eq_borelCalculus`: it rewrites the `borelCalculus (cayley Δ)`
object as a `spectralCalculus (stoneGroup Δ)` of the *base* symbol
`logExpSym t s = exp(i t · log s)`, whose Möbius-pullback `s ↦ (inverseMobius ·).re` reproduces
`modularSymbol` on the nose. Composed with `stoneGroup_eq_genToGroup` (Stone's theorem: the
Cayley–Borel and Hille–Yosida constructions of `e^{itA}` coincide), the modular flow becomes
`spectralCalculus (genToGroup Δ) (logExpSym t)` — an object built on `Δ`'s own group, on which the
atom fact `E_Δ({1}) Ω = Ω` (`spectralProjection_singleton_one_vacuum`, from `Δ Ω = Ω`) collapses
everything: since `logExpSym t 1 = 1`,
`spectralCalculus (genToGroup Δ) (logExpSym t) (E({1})Ω) = E({1})Ω`, a limit-free clone of
`modularSqrt_atom_apply`.

`Δ^{it} Ω = Ω` is stated **unconditionally** (no `[Nontrivial H]`): the degenerate `Subsingleton H`
case is dispatched by `Subsingleton.elim`, and the `Nontrivial H` branch supplies the instance the
`stoneGroup = genToGroup` swap needs.
-/

open scoped InnerProductSpace
open Complex MeasureTheory Filter Topology
open Spectra.QuantumMechanics.SpectralTheory
open Spectra.OneParameterUnitaryGroup
open Spectra.YosidaHille
open Spectra.Cayley Spectra.BorelCFC

namespace Spectra.TomitaTakesaki

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

/-! ## The base symbol `logExpSym t s = exp(i t · log s)`

This is the `ℝ → ℂ` symbol whose Möbius pullback `s ↦ (inverseMobius ·).re` is `modularSymbol`. It
is the `log`-free counterpart of the Cayley `modularSymbol`; `logExpSym t (inverseMobiusReal Δ z)`
is *definitionally* `modularSymbol (cayley Δ) t z`. -/

/-- The base modular symbol on `ℝ`: `s ↦ exp(i t · log s)`. -/
noncomputable def logExpSym (t : ℝ) : ℝ → ℂ :=
  fun s => Complex.exp (Complex.I * (t : ℂ) * ((Real.log s : ℝ) : ℂ))

/-- `logExpSym t` is measurable. -/
lemma measurable_logExpSym (t : ℝ) : Measurable (logExpSym t) := by
  unfold logExpSym
  exact measurable_exp.comp <| measurable_const.mul <| measurable_ofReal.comp Real.measurable_log

/-- `logExpSym t` is unimodular, hence bounded by `1`. -/
lemma logExpSym_bdd (t : ℝ) : ∃ C, ∀ s, ‖logExpSym t s‖ ≤ C := by
  refine ⟨1, fun s => le_of_eq ?_⟩
  rw [logExpSym, norm_exp]
  have hre : (Complex.I * (t : ℂ) * ((Real.log s : ℝ) : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

/-- `logExpSym t 1 = 1`: the base symbol takes the value `1` at the eigenvalue `1` of `Δ`. -/
lemma logExpSym_one (t : ℝ) : logExpSym t 1 = 1 := by
  unfold logExpSym
  rw [Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

/-! ## The bridge step

`(modularFlow …).U t = spectralCalculus (genToGroup Δ) (logExpSym t)`, in the `Nontrivial H`
case. -/

/-- The modular operator `Δ = modularOp M Ω`, self-adjoint (`modularOp_isSelfAdjoint`). -/
private theorem modΔ (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    IsSelfAdjoint (modularOp M Ω) :=
  modularOp_isSelfAdjoint hcyc hsep

/-- **The bridge.** The modular flow, on a nondegenerate space, is `spectralCalculus (genToGroup Δ)`
of the base symbol `logExpSym t`. Via `borelModularGroup_U` (the flow is `borelCalculus (cayley Δ)`
of `modularSymbol`), `borelCalculus_congr` (the symbol is the Möbius pullback of `logExpSym t`), the
unconditional bridge `spectralCalculus_stoneGroup_eq_borelCalculus` (backwards), and
`stoneGroup_eq_genToGroup` (Stone's theorem). -/
theorem modularFlow_U_eq_spectralCalculus [Nontrivial H]
    (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) (t : ℝ) :
    (modularFlow hcyc hsep).U t
      = spectralCalculus (genToGroup (modΔ hcyc hsep)) (logExpSym t)
          (measurable_logExpSym t) (logExpSym_bdd t) := by
  set hA := modΔ hcyc hsep with _hAdef
  -- The flow `borelCalculus (cayley Δ) (modularSymbol …)` rewritten with
  -- the Möbius-pullback symbol.
  have hLHS : (modularFlow hcyc hsep).U t
      = borelCalculus (cayley hA) (cayley_isStarNormal hA)
          (fun z => logExpSym t (inverseMobiusReal hA z))
          ((measurable_logExpSym t).comp (inverseMobiusReal_measurable hA))
          ((logExpSym_bdd t).imp fun _ hC z => hC (inverseMobiusReal hA z)) := by
    rw [show (modularFlow hcyc hsep).U t
        = borelCalculus (cayley hA) (cayley_isStarNormal hA) (modularSymbol (cayley hA) t)
            (measurable_modularSymbol (cayley hA) t)
            ⟨1, fun z => le_of_eq (norm_modularSymbol (cayley hA) t z)⟩ from rfl]
    exact borelCalculus_congr (cayley hA) (cayley_isStarNormal hA) rfl _ _ _ _
  rw [hLHS, ← spectralCalculus_stoneGroup_eq_borelCalculus hA (logExpSym t)
    (measurable_logExpSym t) (logExpSym_bdd t), stoneGroup_eq_genToGroup hA]

/-! ## The atom collapse

`spectralCalculus (genToGroup Δ) (logExpSym t) (E({1})Ω) = E({1})Ω`: on the spectral atom `{1}` the
base symbol acts as its value `logExpSym t 1 = 1`. Limit-free clone of `modularSqrt_atom_apply`. -/

/-- **Atom collapse.** On the spectral atom `E_Δ({1})Ω`,
`spectralCalculus (genToGroup Δ) (logExpSym t)` acts as the identity, because
`logExpSym t · 1_{{1}} = 1_{{1}}` (as `logExpSym t 1 = 1`). -/
theorem logExpSym_atom_apply (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) (t : ℝ) :
    spectralCalculus (genToGroup (modΔ hcyc hsep)) (logExpSym t)
        (measurable_logExpSym t) (logExpSym_bdd t)
        (spectralProjection (genToGroup (modΔ hcyc hsep)) ({(1 : ℝ)} : Set ℝ)
          (measurableSet_singleton 1) Ω)
      = spectralProjection (genToGroup (modΔ hcyc hsep)) ({(1 : ℝ)} : Set ℝ)
          (measurableSet_singleton 1) Ω := by
  set U := genToGroup (modΔ hcyc hsep) with _hU
  set xn := spectralProjection U ({(1 : ℝ)} : Set ℝ) (measurableSet_singleton 1) Ω with hxn
  have hE : xn = spectralCalculus U (Set.indicator ({(1 : ℝ)} : Set ℝ) fun _ => (1 : ℂ))
      (measurable_const.indicator (measurableSet_singleton 1)) (indicator_one_bdd _) Ω := by
    rw [hxn]; rfl
  rw [hE, ← ContinuousLinearMap.mul_apply,
    spectralCalculus_mul U (Set.indicator ({(1 : ℝ)} : Set ℝ) fun _ => (1 : ℂ))
      (logExpSym t)
      (measurable_const.indicator (measurableSet_singleton 1)) (indicator_one_bdd _)
      (measurable_logExpSym t) (logExpSym_bdd t)
      ((measurable_logExpSym t).mul (measurable_const.indicator (measurableSet_singleton 1)))
      (bounded_mul (logExpSym_bdd t) (indicator_one_bdd _))]
  refine congrArg (fun T : H →L[ℂ] H => T Ω) ?_
  refine spectralCalculus_congr U ?_ _ _ _ _
  funext s
  by_cases hs : s ∈ ({(1 : ℝ)} : Set ℝ)
  · rw [Set.mem_singleton_iff] at hs; subst hs
    rw [Set.indicator_of_mem (Set.mem_singleton _), mul_one, logExpSym_one]
  · rw [Set.indicator_of_notMem hs, mul_zero]

/-! ## Field 5 — `Δ^{it} Ω = Ω` -/

/-- **`Δ^{it} Ω = Ω`** (`ModularData.modularFlow_fixes_vacuum`, field 5). The modular flow fixes the
vacuum. Unconditional: `Subsingleton H` is trivial, and on `Nontrivial H` the bridge
`modularFlow_U_eq_spectralCalculus` reduces to `spectralCalculus (genToGroup Δ) (logExpSym t)`,
which fixes `Ω = E_Δ({1})Ω` (`spectralProjection_singleton_one_vacuum`) by the atom collapse. -/
theorem modularFlow_fixes_vacuum (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) (t : ℝ) :
    (modularFlow hcyc hsep).U t Ω = Ω := by
  rcases subsingleton_or_nontrivial H with _ | _
  · exact Subsingleton.elim _ _
  · rw [modularFlow_U_eq_spectralCalculus hcyc hsep t]
    set U := genToGroup (modΔ hcyc hsep) with _hU
    have hEfix : spectralProjection U ({(1 : ℝ)} : Set ℝ) (measurableSet_singleton 1) Ω = Ω :=
      spectralProjection_singleton_one_vacuum hcyc hsep
    calc spectralCalculus U (logExpSym t) (measurable_logExpSym t) (logExpSym_bdd t) Ω
        = spectralCalculus U (logExpSym t) (measurable_logExpSym t) (logExpSym_bdd t)
            (spectralProjection U ({(1 : ℝ)} : Set ℝ) (measurableSet_singleton 1) Ω) :=
          by rw [hEfix]
      _ = spectralProjection U ({(1 : ℝ)} : Set ℝ) (measurableSet_singleton 1) Ω :=
            logExpSym_atom_apply hcyc hsep t
      _ = Ω := hEfix

end Spectra.TomitaTakesaki
