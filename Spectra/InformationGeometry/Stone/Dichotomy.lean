/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: InformationGeometry/Stone/Dichotomy.lean
Target: Mathlib v4.31.0-rc1
-/
import Spectra.InformationGeometry.Stone.GeometricData
/-!
# The Classical–Quantum Dichotomy for Continuous Symmetries

Two computations, one punchline.

**The classical bit** (`classicalBitData`).  The binomial model
`p_α = (cos²α, sin²α)`, `α ∈ (0, π/2)`, in the Hellinger angle chart.
By hand: the score is `∂_α log p = (−2 tan α, 2 cot α)`, so

  `g(α) = E[(∂ℓ)²] = cos²α·4tan²α + sin²α·4cot²α = 4`        (constant!)
  `C(α) = E[(∂ℓ)³] = −8 sin³α/cos α + 8 cos³α/sin α = 16 cot 2α`.

The chart is the round quarter-circle of radius 2.  The metric *alone*
admits a one-parameter family of would-be symmetries (Hellinger
rotations, `X = c·∂_α`): Killing's equation in one dimension with
constant `g` forces only `X' = 0`.  It is the **cubic tensor** that
rigidifies: `L_X C = X·C' + 3C·X' = c·(−32/sin²2α) ≠ 0` unless `c = 0`.
Theorem `classicalBit_rigid`: every generator of this data vanishes
identically on the domain.  Note the structure of the proof — it is
*pointwise*, no ODE theory: at each `θ`, Killing kills the derivative,
then cubic preservation kills the value.

**The qubit** (`qubitData`).  Pure states of a two-level system form
the Bloch sphere; the quantum (SLD) Fisher metric on it is the round
metric — in the polar chart `(α, β)`, `g = diag(1, sin²α)` — and the
canonical cubic tensor **vanishes**: it is a unitarily invariant odd
symmetric tensor on a space where the isotropy group acts transitively
on tangent directions, and an `SO(2)`-invariant cubic form on the plane
is zero.  Consequently `preserves_cubic` is vacuous and the generators
are exactly the Killing fields of the round sphere — an `so(3) ≅ su(2)`
worth.  Here we exhibit the cheap one: the azimuthal rotation
`X = ∂_β` (`qubitRotation`), a constant field that is Killing because
the metric does not depend on `β`.

**The dichotomy** (`classical_quantum_dichotomy`): the classical bit
admits *no* nonzero generator; the qubit admits a generator whose field
vanishes *nowhere*.  Juxtaposed with the two Stone theorems of this
project, this is Hardy's "continuous reversibility" axiom in theorem
form: classical state space supports no nontrivial continuous
divergence-preserving dynamics, and quantum state space does — which is
precisely why the quantum Stone correspondence has content
(`d² − 1` dimensions of it) while the classical one is a no-go.

## Honesty ledger

* The data here are *declared* in coordinates.  That `classicalBitData`
  is the Fisher/Amari–Chentsov data of the actual binomial measure
  model, and that `qubitData` is the pure-qubit SLD metric (Braunstein–
  Caves, with the factor-4 normalization absorbed by rescaling the
  chart — constant rescaling does not change the generator algebra),
  are the by-hand derivations recorded above.  Formalizing those two
  bridges (`E[(∂ℓ)ᵏ]` over a two-point space is a finite sum; the qubit
  side goes through `quantumRLDFisherModel`) is deferred, deliberately:
  the geometric content of the dichotomy is already a theorem without
  them.
* Only one of the three qubit Killing fields is exhibited.  `L_x` and
  `L_y` have non-constant components and need real trigonometric work;
  the full `su(2)` bijection (every Killing field of the round sphere
  is a rotation field) is the expensive converse.  None of that is
  needed for the dichotomy, which only requires `0` versus `≥ 1`.

## References

* N. N. Chentsov, *Statistical Decision Rules and Optimal Inference*,
  AMS, 1982 — uniqueness of the Fisher/AC pair under sufficiency.
* S. Amari, H. Nagaoka, *Methods of Information Geometry*, AMS, 2000.
* S. L. Braunstein, C. M. Caves, "Statistical distance and the geometry
  of quantum states", *Phys. Rev. Lett.* **72** (1994), 3439–3443.
* L. Hardy, "Quantum theory from five reasonable axioms",
  arXiv:quant-ph/0101012 (2001) — the continuous reversibility axiom.

## Tags

rigidity, Killing field, Amari–Chentsov tensor, Bloch sphere, Hardy
-/

open Finset

namespace Spectra.InformationGeometry

namespace GeometricData

/-! ### Chart calculus helpers

Directional derivatives of a function of a single coordinate.  These
are the only two facts about `fderiv` on `ParamSpace n` the file needs:
differentiating `F ∘ projᵢ` in direction `eᵢ` gives `F'`, and in any
other coordinate direction gives `0`. -/

/-- The directional derivative of `θ ↦ F (θ i)` in the direction `eᵢ`
is the derivative of `F`. -/
lemma fderiv_coord_apply {n : ℕ} {F : ℝ → ℝ} {θ : ParamSpace n} {d : ℝ}
    (i : Fin n) (hF : HasDerivAt F d (θ i)) :
    fderiv ℝ (fun θ' : ParamSpace n => F (θ' i)) θ
      (EuclideanSpace.single i 1) = d := by
  have hfn : (fun θ' : ParamSpace n => F (θ' i))
      = F ∘ ⇑(EuclideanSpace.proj i : ParamSpace n →L[ℝ] ℝ) := by
    funext θ'
    simp [EuclideanSpace.coe_proj]
  have hproj : HasFDerivAt
      (⇑(EuclideanSpace.proj i : ParamSpace n →L[ℝ] ℝ))
      (EuclideanSpace.proj i : ParamSpace n →L[ℝ] ℝ) θ :=
    (EuclideanSpace.proj i : ParamSpace n →L[ℝ] ℝ).hasFDerivAt
  have hcomp : HasFDerivAt
      (F ∘ ⇑(EuclideanSpace.proj i : ParamSpace n →L[ℝ] ℝ))
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) d).comp
        (EuclideanSpace.proj i)) θ :=
    hF.hasFDerivAt.comp θ hproj
  rw [hfn, hcomp.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply]

/-- The directional derivative of `θ ↦ F (θ i)` in any *other*
coordinate direction `eₖ`, `k ≠ i`, vanishes. -/
lemma fderiv_coord_apply_ne {n : ℕ} {F : ℝ → ℝ} {θ : ParamSpace n} {d : ℝ}
    {i k : Fin n} (hF : HasDerivAt F d (θ i)) (hki : k ≠ i) :
    fderiv ℝ (fun θ' : ParamSpace n => F (θ' i)) θ
      (EuclideanSpace.single k 1) = 0 := by
  have hfn : (fun θ' : ParamSpace n => F (θ' i))
      = F ∘ ⇑(EuclideanSpace.proj i : ParamSpace n →L[ℝ] ℝ) := by
    funext θ'
    simp [EuclideanSpace.coe_proj]
  have hproj : HasFDerivAt
      (⇑(EuclideanSpace.proj i : ParamSpace n →L[ℝ] ℝ))
      (EuclideanSpace.proj i : ParamSpace n →L[ℝ] ℝ) θ :=
    (EuclideanSpace.proj i : ParamSpace n →L[ℝ] ℝ).hasFDerivAt
  have hcomp : HasFDerivAt
      (F ∘ ⇑(EuclideanSpace.proj i : ParamSpace n →L[ℝ] ℝ))
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) d).comp
        (EuclideanSpace.proj i)) θ :=
    hF.hasFDerivAt.comp θ hproj
  rw [hfn, hcomp.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, Ne.symm hki]

/-! ### The classical bit -/

/-- The Amari–Chentsov component of the binomial model in the Hellinger
angle chart: `C(α) = 16 cot 2α = E[(∂_α log p_α)³]` for
`p_α = (cos²α, sin²α)`. -/
noncomputable def bitCubic (α : ℝ) : ℝ :=
  16 * (Real.cos (2 * α) / Real.sin (2 * α))

/-- `C'(α) = −32 / sin²2α` wherever `sin 2α ≠ 0`. -/
lemma bitCubic_hasDerivAt {α : ℝ} (h : Real.sin (2 * α) ≠ 0) :
    HasDerivAt bitCubic (-32 / Real.sin (2 * α) ^ 2) α := by
  unfold bitCubic
  have h2 : HasDerivAt (fun x : ℝ => 2 * x) 2 α := by
    simpa using (hasDerivAt_id α).const_mul (2 : ℝ)
  have hq := (h2.cos).div (h2.sin) h
  have hnum : -Real.sin (2 * α) * 2 * Real.sin (2 * α) -
      Real.cos (2 * α) * (Real.cos (2 * α) * 2) = -2 := by
    linear_combination (-2 : ℝ) * Real.sin_sq_add_cos_sq (2 * α)
  rw [hnum] at hq
  have h16 := hq.const_mul (16 : ℝ)
  rw [show (16 : ℝ) * (-2 / Real.sin (2 * α) ^ 2)
      = -32 / Real.sin (2 * α) ^ 2 from by ring] at h16
  exact h16

/-- **The classical bit**, as geometric data: the binomial model in the
Hellinger angle chart `α ∈ (0, π/2)`.  Metric `g ≡ 4` (the chart is the
round quarter-circle of radius 2); cubic tensor `C = 16 cot 2α`. -/
noncomputable def classicalBitData : GeometricData 1 where
  domain := {θ : ParamSpace 1 | 0 < θ 0 ∧ θ 0 < Real.pi / 2}
  metric := fun _ _ _ => 4
  cubic := fun θ _ _ _ => bitCubic (θ 0)

/-- **Classical rigidity.**  Every generator of the classical bit
vanishes identically on the domain.

The proof is pointwise.  Killing's equation with constant metric reads
`8·X'(θ) = 0`, killing the derivative; cubic preservation then reads
`X(θ)·C'(θ) = 0`, and `C'(θ) = −32/sin²2θ ≠ 0` kills the value.  Note
the division of labor: the *metric clause alone would not suffice* —
constant-`g` Killing leaves the constant fields (Hellinger rotations)
alive, and it is exactly the third KL jet, the cubic tensor, that
removes them.  Classically, `C` is the rigidifier. -/
theorem classicalBit_rigid (G : classicalBitData.Generator)
    {θ : ParamSpace 1} (hθ : θ ∈ classicalBitData.domain) (l : Fin 1) :
    G.vectorField θ l = 0 := by
  obtain rfl : l = 0 := Subsingleton.elim l 0
  have hmem : 0 < θ 0 ∧ θ 0 < Real.pi / 2 := hθ
  have hs : Real.sin (2 * θ 0) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hmem.1])
      (by linarith [hmem.2]))
  -- Step 1: Killing with constant metric forces the field's derivative
  -- to vanish at θ.
  have hD : fderiv ℝ (fun θ' => G.vectorField θ' 0) θ
      (EuclideanSpace.single 0 1) = 0 := by
    have hk := G.killing θ hθ 0 0
    dsimp only [classicalBitData] at hk
    rw [Fin.sum_univ_one] at hk
    rw [(hasFDerivAt_const (4 : ℝ) θ).fderiv] at hk
    simp only [ContinuousLinearMap.zero_apply, mul_zero, zero_add] at hk
    linarith
  -- Step 2: cubic preservation then pins the field's value.
  have hc := G.preserves_cubic θ hθ 0 0 0
  dsimp only [classicalBitData] at hc
  rw [Fin.sum_univ_one] at hc
  rw [hD] at hc
  rw [fderiv_coord_apply 0 (bitCubic_hasDerivAt hs)] at hc
  simp only [mul_zero, add_zero] at hc
  have hne : (-32 : ℝ) / Real.sin (2 * θ 0) ^ 2 ≠ 0 :=
    div_ne_zero (by norm_num) (pow_ne_zero 2 hs)
  exact (mul_eq_zero.mp hc).resolve_right hne

/-! ### The qubit -/

/-- **The qubit**, as geometric data: pure states of a two-level system
in the Bloch polar chart `(α, β)`, `α ∈ (0, π)`.  Metric: the round
sphere, `g = diag(1, sin²α)` — the pure-state quantum Fisher metric up
to its constant normalization.  Cubic tensor: identically zero, by
unitary isotropy (an invariant odd symmetric tensor on a 2-point-
homogeneous space vanishes). -/
noncomputable def qubitData : GeometricData 2 where
  domain := {θ : ParamSpace 2 | 0 < θ 0 ∧ θ 0 < Real.pi}
  metric := fun θ i j =>
    if i = j then (if i = 0 then 1 else Real.sin (θ 0) ^ 2) else 0
  cubic := fun _ _ _ _ => 0

/-- **The azimuthal rotation generator** `X = ∂_β` on the qubit: the
constant field `(0, 1)`.  Killing because the metric is independent of
`β`; cubic-preserving because the cubic tensor is zero.  In `su(2)`
terms this is (the projectivization of) `σ_z/2`. -/
noncomputable def qubitRotation : qubitData.Generator where
  vectorField := fun _ => EuclideanSpace.single 1 1
  smooth := contDiff_const
  killing := by
    intro θ _ i j
    dsimp only [qubitData]
    rw [Fin.sum_univ_two]
    -- The field is constant, so both displacement derivatives vanish.
    rw [(hasFDerivAt_const ((EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 0) θ).fderiv,
        (hasFDerivAt_const ((EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 1) θ).fderiv]
    simp only [ContinuousLinearMap.zero_apply, mul_zero, add_zero,
      PiLp.single_apply, one_ne_zero, if_false, if_true,  one_mul]
    -- Remaining: the β-derivative of the metric entry vanishes.
    by_cases hij : i = j
    · subst hij
      by_cases hi : i = 0
      · subst hi
        simp only [if_true]
        rw [(hasFDerivAt_const (1 : ℝ) θ).fderiv]
        simp
      · simp only [if_neg hi, Fin.isValue, zero_ne_one,
          ↓reduceIte, zero_mul, zero_add]
        exact fderiv_coord_apply_ne (F := fun t => Real.sin t ^ 2)
          ((Real.hasDerivAt_sin (θ 0)).pow 2) (by norm_num)
    · simp only [if_neg hij]
      rw [(hasFDerivAt_const (0 : ℝ) θ).fderiv]
      simp
  preserves_cubic := by
    intro θ _ i j k
    dsimp only [qubitData]
    simp [(hasFDerivAt_const (0 : ℝ) θ).fderiv]

/-! ### The dichotomy -/

/-- **The classical–quantum dichotomy.**  The classical bit admits no
nonzero infinitesimal symmetry of its information geometry; the qubit
admits one whose field vanishes nowhere.

Together with the two Stone theorems of this development — the
information-geometric one, whose objects are exactly these generators,
and the quantum-mechanical one, whose objects are self-adjoint
operators — this is the geometric core of Hardy's continuous
reversibility axiom: continuous reversible dynamics on state space is
impossible classically and abundant quantumly, and demanding its
existence already forces the quantum side of the divide. -/
theorem classical_quantum_dichotomy :
    (∀ G : classicalBitData.Generator,
      ∀ θ ∈ classicalBitData.domain, ∀ l : Fin 1, G.vectorField θ l = 0) ∧
    (∃ G : qubitData.Generator,
      ∀ θ : ParamSpace 2, G.vectorField θ 1 ≠ 0) := by
  refine ⟨fun G θ hθ l => classicalBit_rigid G hθ l,
    ⟨qubitRotation, fun θ => ?_⟩⟩
  dsimp only [qubitRotation]
  simp only [Fin.isValue, PiLp.single_eq_same, ne_eq,
    one_ne_zero, not_false_eq_true]

end GeometricData

end Spectra.InformationGeometry
