/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/

/-
Spectra: Calculus.lean
The bounded functional calculus `Φ(g)` of a one-parameter unitary group.

-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Spectra.SpectralTheory.Measure.Polarized
import Spectra.Bochner.Borel.Measure.Basic
import Spectra.Mathlib.CharFunBridge
/-!
# The bounded functional calculus

For a one-parameter unitary group `U` with polarized spectral pairing `spectralForm`,
this file constructs the operator `Φ(g) : H →L[ℂ] H` characterized by

  `⟪ξ, Φ(g) η⟫ = spectralForm ξ η g  ( "= ∫ g dμ_{ξ,η}" )`

for every bounded measurable symbol `g : ℝ → ℂ`, and proves the calculus identities.

## Conventions

* **Orientation.**  The defining identity puts `Φ(g)` in the *second* (linear) slot, so that
  `Φ(e^{it·}) = U(t)` — the opposite convention would yield `U(−t)`.  Mathlib's Riesz
  packaging `InnerProductSpace.continuousLinearMapOfBilin` produces `B♯` with
  `⟪B♯ ξ, η⟫ = B ξ η` — operator in the *first* slot — so `Φ(g) := (B♯)†`: one adjoint flip,
  after which `ContinuousLinearMap.adjoint_inner_right` gives the defining identity.
* **Hypotheses.**  `spectralCalculus` takes the symbol's measurability and boundedness as
  `Prop` arguments; proof irrelevance makes `Φ g h₁ h₂` independent of the proofs, so lemmas
  freely take their own `(hm) (hb)` arguments.  Lemmas about *specific* symbols (`e^{it·}`,
  `1`) supply canonical proofs.

## Main statements

* `spectralCalculus` — the operator `Φ(g)`, with `inner_spectralCalculus` its defining identity.
* `spectralCalculus_char` — `Φ(e^{it·}) = U(t)`; `spectralCalculus_one` — `Φ(1) = 1`.
* `spectralCalculus_add`, `spectralCalculus_smul` — linearity in the symbol.
* `spectralCalculus_one_add_smul` — `Φ(1 + c·g) = 1 + c • Φ(g)` in one call.
* `spectralCalculus_adjoint` — `Φ(g)† = Φ(conj g)`.
* `spectralForm_calculus_right` — **the weighted-measure theorem**
  `"dμ_{ξ, Φ(g)η} = g · dμ_{ξ,η}"`, i.e. `spectralForm ξ (Φ(g)η) h = spectralForm ξ η (h·g)`.
* `spectralCalculus_mul` — `Φ(h)Φ(g) = Φ(hg)`; `spectralCalculus_comm` — commutativity.
* `norm_sq_spectralCalculus_apply` — `‖Φ(g)ξ‖² = ∫ ‖g‖² dμ_ξ` (drives the DCT stage).
* `norm_spectralCalculus_le` — the sharp bound `‖Φ(g)‖ ≤ C` for `‖g‖ ≤ C`.
-/

open Complex MeasureTheory
open scoped InnerProductSpace
open Spectra.Fourier
open Spectra.Borel
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.QuantumMechanics.SpectralTheory
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-! ## Symbol helpers -/

/-- Products of bounded functions are bounded. -/
lemma bounded_mul {g₁ g₂ : ℝ → ℂ} (h₁ : ∃ C, ∀ ω, ‖g₁ ω‖ ≤ C) (h₂ : ∃ C, ∀ ω, ‖g₂ ω‖ ≤ C) :
    ∃ C, ∀ ω, ‖g₁ ω * g₂ ω‖ ≤ C := by
  obtain ⟨C₁, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  refine ⟨max C₁ 0 * max C₂ 0, fun ω => ?_⟩
  rw [norm_mul]
  exact mul_le_mul ((hC₁ ω).trans (le_max_left _ _)) ((hC₂ ω).trans (le_max_left _ _))
    (norm_nonneg _) (le_max_right _ _)

/-- Canonical boundedness proof for the character symbol. -/
lemma char_bdd (t : ℝ) : ∃ C, ∀ ω : ℝ, ‖cexp (I * ω * t)‖ ≤ C :=
  ⟨1, fun ω => char_norm_le_one t ω⟩

/-! ## Riesz packaging -/

/-- The polarized pairing `(ξ, η) ↦ spectralForm ξ η g`, bundled as a continuous sesquilinear
map.  Sesquilinearity is `spectralForm_add_left` / `_smul_left` / `_add_right` / `_smul_right`;
the (crude) bound is `norm_spectralForm_le` at the constant extracted from `hg_bdd`. -/
noncomputable def spectralFormBilin (g : ℝ → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) :
    H →L⋆[ℂ] H →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
      (fun ξ η => spectralForm U_grp ξ η g)
      (fun ξ₁ ξ₂ η => spectralForm_add_left U_grp ξ₁ ξ₂ η hg_meas hg_bdd)
      (fun c ξ η => by
        rw [spectralForm_smul_left U_grp ξ η c hg_meas hg_bdd, smul_eq_mul])
      (fun ξ η₁ η₂ => spectralForm_add_right U_grp ξ η₁ η₂ hg_meas hg_bdd)
      (fun c ξ η => by
        rw [spectralForm_smul_right U_grp ξ η c hg_meas hg_bdd, RingHom.id_apply,
          smul_eq_mul]))
    (2 * hg_bdd.choose)
    (fun ξ η => norm_spectralForm_le U_grp ξ η hg_meas hg_bdd.choose_spec)

@[simp] lemma spectralFormBilin_apply (g : ℝ → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (ξ η : H) :
    spectralFormBilin U_grp g hg_meas hg_bdd ξ η = spectralForm U_grp ξ η g :=
  rfl

/-- **The bounded functional calculus** `Φ(g)`.

`continuousLinearMapOfBilin` represents the form with the operator in the first slot
(`⟪B♯ ξ, η⟫ = B ξ η`); the adjoint flips it to the second, which is the orientation under
which `Φ(e^{it·}) = U(t)` (see `inner_spectralCalculus`, `spectralCalculus_char`). -/
noncomputable def spectralCalculus (g : ℝ → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) : H →L[ℂ] H :=
  ContinuousLinearMap.adjoint
    (InnerProductSpace.continuousLinearMapOfBilin (spectralFormBilin U_grp g hg_meas hg_bdd))

/-- The defining identity of the calculus: `⟪ξ, Φ(g) η⟫ = "∫ g dμ_{ξ,η}"`. -/
theorem inner_spectralCalculus (g : ℝ → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (ξ η : H) :
    ⟪ξ, spectralCalculus U_grp g hg_meas hg_bdd η⟫_ℂ = spectralForm U_grp ξ η g := by
  simp only [spectralCalculus]
  rw [ContinuousLinearMap.adjoint_inner_right,
    InnerProductSpace.continuousLinearMapOfBilin_apply, spectralFormBilin_apply]

omit [CompleteSpace H] in
/-- Operators agreeing against all pairings are equal (left-slot separation). -/
private lemma calculus_ext {A B : H →L[ℂ] H}
    (h : ∀ ξ η : H, ⟪ξ, A η⟫_ℂ = ⟪ξ, B η⟫_ℂ) : A = B :=
  ContinuousLinearMap.ext fun η => ext_inner_left ℂ fun ξ => h ξ η

/-! ## The calculus on distinguished symbols -/

/-- `Φ(e^{it·}) = U(t)`: the calculus extends the group.  This is the orientation check —
with the opposite convention this comes out as `U(−t)`. -/
theorem spectralCalculus_char (t : ℝ) :
    spectralCalculus U_grp (fun l => cexp (I * l * t)) (char_measurable t) (char_bdd t)
      = U_grp.U t := by
  refine calculus_ext fun ξ η => ?_
  rw [inner_spectralCalculus, spectralForm_char]

/-- `Φ(1) = 1` (normalization; `spectralForm_one`). -/
theorem spectralCalculus_one :
    spectralCalculus U_grp (fun _ => (1 : ℂ)) measurable_const ⟨1, fun _ => norm_one.le⟩
      = ContinuousLinearMap.id ℂ H := by
  refine calculus_ext fun ξ η => ?_
  rw [inner_spectralCalculus, spectralForm_one, ContinuousLinearMap.id_apply]

/-- Additivity in the symbol. -/
theorem spectralCalculus_add (g₁ g₂ : ℝ → ℂ)
    (h₁m : Measurable g₁) (h₁b : ∃ C, ∀ ω, ‖g₁ ω‖ ≤ C)
    (h₂m : Measurable g₂) (h₂b : ∃ C, ∀ ω, ‖g₂ ω‖ ≤ C)
    (hm : Measurable fun l => g₁ l + g₂ l) (hb : ∃ C, ∀ ω, ‖g₁ ω + g₂ ω‖ ≤ C) :
    spectralCalculus U_grp (fun l => g₁ l + g₂ l) hm hb
      = spectralCalculus U_grp g₁ h₁m h₁b + spectralCalculus U_grp g₂ h₂m h₂b := by
  refine calculus_ext fun ξ η => ?_
  rw [inner_spectralCalculus U_grp _ hm hb ξ η,
    spectralForm_add_fun U_grp ξ η h₁m h₁b h₂m h₂b, ContinuousLinearMap.add_apply,
    inner_add_right, inner_spectralCalculus U_grp g₁ h₁m h₁b ξ η,
    inner_spectralCalculus U_grp g₂ h₂m h₂b ξ η]

/-- Homogeneity in the symbol. -/
theorem spectralCalculus_smul (c : ℂ) (g : ℝ → ℂ)
    (hm : Measurable g) (hb : ∃ C, ∀ ω, ‖g ω‖ ≤ C)
    (hcm : Measurable fun l => c * g l) (hcb : ∃ C, ∀ ω, ‖c * g ω‖ ≤ C) :
    spectralCalculus U_grp (fun l => c * g l) hcm hcb
      = c • spectralCalculus U_grp g hm hb := by
  refine calculus_ext fun ξ η => ?_
  rw [inner_spectralCalculus U_grp _ hcm hcb ξ η, spectralForm_smul_fun,
    ContinuousLinearMap.smul_apply, inner_smul_right,
    inner_spectralCalculus U_grp g hm hb ξ η]

/-- **`Φ(1 + c·g) = 1 + c • Φ(g)`**: the calculus applied to a symbol of the shape
`s ↦ 1 + c · g(s)`, packaged in one call. Collapses the `spectralCalculus_one` /
`spectralCalculus_add` / `spectralCalculus_smul` eta-expansion bookkeeping that a bare
`1 + c·g` split otherwise needs, since `spectralCalculus_add` expects its two summands as
literal `fun l => g₁ l + g₂ l`, not the constant function `1` and `c • g` directly. -/
theorem spectralCalculus_one_add_smul (c : ℂ) (g : ℝ → ℂ)
    (hm : Measurable g) (hb : ∃ C, ∀ ω, ‖g ω‖ ≤ C)
    (hcm : Measurable fun l => c * g l) (hcb : ∃ C, ∀ ω, ‖c * g ω‖ ≤ C)
    (hsm : Measurable fun l => (1 : ℂ) + c * g l)
    (hsb : ∃ C, ∀ ω, ‖(1 : ℂ) + c * g ω‖ ≤ C) :
    spectralCalculus U_grp (fun l => (1 : ℂ) + c * g l) hsm hsb
      = ContinuousLinearMap.id ℂ H + c • spectralCalculus U_grp g hm hb := by
  rw [spectralCalculus_add U_grp (fun _ => (1 : ℂ)) (fun l => c * g l)
      measurable_const ⟨1, fun _ => norm_one.le⟩ hcm hcb hsm hsb,
    spectralCalculus_one, spectralCalculus_smul U_grp c g hm hb hcm hcb]

/-- **The calculus is a `*`-map**: `Φ(g)† = Φ(conj ∘ g)`.  Bookkeeping on
`spectralForm_conj_symm`. -/
theorem spectralCalculus_adjoint (g : ℝ → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C)
    (hcg_meas : Measurable fun l => (starRingEnd ℂ) (g l))
    (hcg_bdd : ∃ C, ∀ ω, ‖(starRingEnd ℂ) (g ω)‖ ≤ C) :
    ContinuousLinearMap.adjoint (spectralCalculus U_grp g hg_meas hg_bdd)
      = spectralCalculus U_grp (fun l => (starRingEnd ℂ) (g l)) hcg_meas hcg_bdd := by
  refine calculus_ext fun ξ η => ?_
  calc ⟪ξ, ContinuousLinearMap.adjoint (spectralCalculus U_grp g hg_meas hg_bdd) η⟫_ℂ
      = ⟪spectralCalculus U_grp g hg_meas hg_bdd ξ, η⟫_ℂ :=
        ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = (starRingEnd ℂ) ⟪η, spectralCalculus U_grp g hg_meas hg_bdd ξ⟫_ℂ :=
        (inner_conj_symm _ _).symm
    _ = (starRingEnd ℂ) (spectralForm U_grp η ξ g) := by
        rw [inner_spectralCalculus U_grp g hg_meas hg_bdd η ξ]
    _ = (starRingEnd ℂ) ((starRingEnd ℂ)
          (spectralForm U_grp ξ η (fun l => (starRingEnd ℂ) (g l)))) := by
        rw [spectralForm_conj_symm U_grp ξ η hg_meas hg_bdd]
    _ = spectralForm U_grp ξ η (fun l => (starRingEnd ℂ) (g l)) := Complex.conj_conj _
    _ = ⟪ξ, spectralCalculus U_grp (fun l => (starRingEnd ℂ) (g l)) hcg_meas hcg_bdd η⟫_ℂ :=
        (inner_spectralCalculus U_grp _ hcg_meas hcg_bdd ξ η).symm

/-! ## The weighted-measure theorem and multiplicativity -/

/-- **Weighted-measure theorem**: `"dμ_{ξ, Φ(g)η} = g · dμ_{ξ,η}"`, i.e. pairing against
`Φ(g)η` twists the symbol:

  `spectralForm ξ (Φ(g)η) h = spectralForm ξ η (h·g)`.

Instance of `integral_combination_ext` (densities `1` against `g`); on characters `e^{i·s}`
the identity is `spectralForm_unitary_left` at `−s` after passing the group across the inner
product, `⟪ξ, U(s) Φ(g)η⟫ = ⟪U(−s)ξ, Φ(g)η⟫`, and reading off `inner_spectralCalculus`.
With the symbol stated as `h·g` (in this order) the workhorse's conclusion matches the
unfolded goal directly — no integrand flip. -/
theorem spectralForm_calculus_right (g h : ℝ → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C)
    (hh_meas : Measurable h) (hh_bdd : ∃ C, ∀ ω, ‖h ω‖ ≤ C) (ξ η : H) :
    spectralForm U_grp ξ (spectralCalculus U_grp g hg_meas hg_bdd η) h
      = spectralForm U_grp ξ η (fun l => h l * g l) := by
  set Φg : H →L[ℂ] H := spectralCalculus U_grp g hg_meas hg_bdd with _hΦ
  have key := integral_combination_ext
    (![1 / 4, -(1 / 4), I / 4, -(I / 4)])
    (fun i => borelMeasure U_grp
      (![ξ + Φg η, ξ - Φg η, ξ - I • Φg η, ξ + I • Φg η] i))
    (fun _ _ => (1 : ℂ))
    (![1 / 4, -(1 / 4), I / 4, -(I / 4)])
    (fun j => borelMeasure U_grp (![ξ + η, ξ - η, ξ - I • η, ξ + I • η] j))
    (fun _ => g)
    (fun _ => measurable_const) (fun _ => ⟨1, fun _ => by simp⟩)
    (fun _ => hg_meas) (fun _ => hg_bdd)
    (fun s => by
      -- The operator algebra, at the `spectralForm` level.
      have hUU : U_grp.U s (U_grp.U (-s) ξ) = ξ := by
        rw [← ContinuousLinearMap.comp_apply, ← U_grp.group_law,
          show s + -s = 0 from by ring, U_grp.identity, ContinuousLinearMap.id_apply]
      have hstep : spectralForm U_grp ξ (Φg η) (fun l => cexp (I * l * s))
          = spectralForm U_grp ξ η (fun l => cexp (I * l * s) * g l) := by
        calc spectralForm U_grp ξ (Φg η) (fun l => cexp (I * l * s))
            = ⟪ξ, U_grp.U s (Φg η)⟫_ℂ := spectralForm_char U_grp ξ (Φg η) s
          _ = ⟪U_grp.U s (U_grp.U (-s) ξ), U_grp.U s (Φg η)⟫_ℂ := by rw [hUU]
          _ = ⟪U_grp.U (-s) ξ, Φg η⟫_ℂ := U_grp.unitary s _ _
          _ = spectralForm U_grp (U_grp.U (-s) ξ) η g :=
              inner_spectralCalculus U_grp g hg_meas hg_bdd _ η
          _ = spectralForm U_grp ξ η (fun l => cexp (-(I * l * ((-s : ℝ) : ℂ))) * g l) :=
              spectralForm_unitary_left U_grp ξ η (-s) hg_meas hg_bdd
          _ = spectralForm U_grp ξ η (fun l => cexp (I * l * s) * g l) := by
              congr 1
              funext l
              rw [show -(I * (l : ℂ) * ((-s : ℝ) : ℂ)) = I * (l : ℂ) * ((s : ℝ) : ℂ) from by
                push_cast; ring]
      simp only [spectralForm] at hstep
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, add_zero, mul_one]
      linear_combination hstep)
    hh_meas hh_bdd
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    add_zero, mul_one] at key
  simp only [spectralForm]
  linear_combination key

/-- **Multiplicativity**: `Φ(h) Φ(g) = Φ(h·g)`.  Pure bookkeeping on the weighted-measure
theorem — no Stone–Weierstrass, no density argument. -/
theorem spectralCalculus_mul (g h : ℝ → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C)
    (hh_meas : Measurable h) (hh_bdd : ∃ C, ∀ ω, ‖h ω‖ ≤ C)
    (hhg_meas : Measurable fun l => h l * g l) (hhg_bdd : ∃ C, ∀ ω, ‖h ω * g ω‖ ≤ C) :
    spectralCalculus U_grp h hh_meas hh_bdd * spectralCalculus U_grp g hg_meas hg_bdd
      = spectralCalculus U_grp (fun l => h l * g l) hhg_meas hhg_bdd := by
  refine calculus_ext fun ξ η => ?_
  rw [ContinuousLinearMap.mul_apply,
    inner_spectralCalculus U_grp h hh_meas hh_bdd ξ
      (spectralCalculus U_grp g hg_meas hg_bdd η),
    spectralForm_calculus_right U_grp g h hg_meas hg_bdd hh_meas hh_bdd ξ η,
    inner_spectralCalculus U_grp (fun l => h l * g l) hhg_meas hhg_bdd ξ η]

/-- The calculus is commutative: `Φ(h) Φ(g) = Φ(g) Φ(h)`. -/
theorem spectralCalculus_comm (g h : ℝ → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C)
    (hh_meas : Measurable h) (hh_bdd : ∃ C, ∀ ω, ‖h ω‖ ≤ C) :
    spectralCalculus U_grp h hh_meas hh_bdd * spectralCalculus U_grp g hg_meas hg_bdd
      = spectralCalculus U_grp g hg_meas hg_bdd * spectralCalculus U_grp h hh_meas hh_bdd := by
  refine calculus_ext fun ξ η => ?_
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
    inner_spectralCalculus U_grp h hh_meas hh_bdd ξ
      (spectralCalculus U_grp g hg_meas hg_bdd η),
    spectralForm_calculus_right U_grp g h hg_meas hg_bdd hh_meas hh_bdd ξ η,
    inner_spectralCalculus U_grp g hg_meas hg_bdd ξ
      (spectralCalculus U_grp h hh_meas hh_bdd η),
    spectralForm_calculus_right U_grp h g hh_meas hh_bdd hg_meas hg_bdd ξ η]
  congr 1
  funext l
  ring

open SpectralMeasure
/-! ## The norm identity -/

/-- **The `L²` identity**: `‖Φ(g)ξ‖² = ∫ ‖g‖² dμ_ξ`.

Route: `‖Φ(g)ξ‖² = ⟪Φ(g)ξ, Φ(g)ξ⟫ = ⟪ξ, Φ(conj g)(Φ(g)ξ)⟫ = spectralForm ξ ξ (conj g · g)
= ∫ ‖g‖² dμ_ξ`, by the adjoint identity, the weighted-measure theorem at `η = ξ`, and
`spectralForm_self`.  This is the engine of the dominated-convergence stage:
`‖Φ(g)ξ − Φ(gₙ)ξ‖² = ∫ ‖g − gₙ‖² dμ_ξ → 0`. -/
theorem norm_sq_spectralCalculus_apply (g : ℝ → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (ξ : H) :
    ‖spectralCalculus U_grp g hg_meas hg_bdd ξ‖ ^ 2
      = ∫ l, ‖g l‖ ^ 2 ∂(borelMeasure U_grp ξ) := by
  have hcg_meas : Measurable fun l : ℝ => (starRingEnd ℂ) (g l) :=
    Complex.continuous_conj.measurable.comp hg_meas
  have hcg_bdd : ∃ C, ∀ ω, ‖(starRingEnd ℂ) (g ω)‖ ≤ C := by
    obtain ⟨C, hC⟩ := hg_bdd
    exact ⟨C, fun ω => by rw [RCLike.norm_conj]; exact hC ω⟩
  have h1 : ⟪spectralCalculus U_grp g hg_meas hg_bdd ξ,
      spectralCalculus U_grp g hg_meas hg_bdd ξ⟫_ℂ
      = ∫ l, (starRingEnd ℂ) (g l) * g l ∂(borelMeasure U_grp ξ) := by
    calc ⟪spectralCalculus U_grp g hg_meas hg_bdd ξ,
          spectralCalculus U_grp g hg_meas hg_bdd ξ⟫_ℂ
        = ⟪ξ, ContinuousLinearMap.adjoint (spectralCalculus U_grp g hg_meas hg_bdd)
            (spectralCalculus U_grp g hg_meas hg_bdd ξ)⟫_ℂ :=
          (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
      _ = ⟪ξ, spectralCalculus U_grp (fun l => (starRingEnd ℂ) (g l)) hcg_meas hcg_bdd
            (spectralCalculus U_grp g hg_meas hg_bdd ξ)⟫_ℂ := by
          rw [spectralCalculus_adjoint U_grp g hg_meas hg_bdd hcg_meas hcg_bdd]
      _ = spectralForm U_grp ξ (spectralCalculus U_grp g hg_meas hg_bdd ξ)
            (fun l => (starRingEnd ℂ) (g l)) :=
          inner_spectralCalculus U_grp _ hcg_meas hcg_bdd ξ _
      _ = spectralForm U_grp ξ ξ (fun l => (starRingEnd ℂ) (g l) * g l) :=
          spectralForm_calculus_right U_grp g (fun l => (starRingEnd ℂ) (g l))
            hg_meas hg_bdd hcg_meas hcg_bdd ξ ξ
      _ = ∫ l, (starRingEnd ℂ) (g l) * g l ∂(borelMeasure U_grp ξ) :=
          spectralForm_self U_grp ξ (hcg_meas.mul hg_meas) (bounded_mul hcg_bdd hg_bdd)
  have h2 : (∫ l, (starRingEnd ℂ) (g l) * g l ∂(borelMeasure U_grp ξ))
      = ∫ l, ((‖g l‖ ^ 2 : ℝ) : ℂ) ∂(borelMeasure U_grp ξ) :=
    integral_congr_ae (.of_forall fun l => by simp only [RCLike.conj_mul]; norm_cast)
  erw [integral_ofReal] at h2
  rw [inner_self_eq_norm_sq_to_K] at h1
  exact_mod_cast h1.trans h2

/-- **The sharp operator-norm bound**: `‖Φ(g)‖ ≤ C` whenever `‖g‖ ≤ C` pointwise — the
crude `2C` of `norm_spectralForm_le` was only scaffolding. -/
theorem norm_spectralCalculus_le (g : ℝ → ℂ) (hg_meas : Measurable g)
    (hg_bdd : ∃ C', ∀ ω, ‖g ω‖ ≤ C') {C : ℝ} (hC : ∀ ω, ‖g ω‖ ≤ C) :
    ‖spectralCalculus U_grp g hg_meas hg_bdd‖ ≤ C := by
  have hC0 : 0 ≤ C := (norm_nonneg (g 0)).trans (hC 0)
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun ξ => ?_
  haveI : IsFiniteMeasure (borelMeasure U_grp ξ) := borelMeasure_isFiniteMeasure U_grp ξ
  have hint : (∫ l, ‖g l‖ ^ 2 ∂(borelMeasure U_grp ξ)) ≤ C ^ 2 * ‖ξ‖ ^ 2 := by
    calc (∫ l, ‖g l‖ ^ 2 ∂(borelMeasure U_grp ξ))
        ≤ ∫ _, C ^ 2 ∂(borelMeasure U_grp ξ) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun l => sq_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall fun l => ?_)
          nlinarith [hC l, norm_nonneg (g l)]
      _ = C ^ 2 * ‖ξ‖ ^ 2 := by
          rw [integral_const, smul_eq_mul, Measure.real_def, borelMeasure_mass, mul_comm]
  have hsq : ‖spectralCalculus U_grp g hg_meas hg_bdd ξ‖ ^ 2 ≤ (C * ‖ξ‖) ^ 2 := by
    rw [norm_sq_spectralCalculus_apply U_grp g hg_meas hg_bdd ξ]
    calc (∫ l, ‖g l‖ ^ 2 ∂(borelMeasure U_grp ξ)) ≤ C ^ 2 * ‖ξ‖ ^ 2 := hint
      _ = (C * ‖ξ‖) ^ 2 := by ring
  calc ‖spectralCalculus U_grp g hg_meas hg_bdd ξ‖
      = Real.sqrt (‖spectralCalculus U_grp g hg_meas hg_bdd ξ‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((C * ‖ξ‖) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = C * ‖ξ‖ := Real.sqrt_sq (mul_nonneg hC0 (norm_nonneg _))

end Spectra.QuantumMechanics.SpectralTheory
