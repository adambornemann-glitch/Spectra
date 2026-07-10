/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.GeometricData
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
are Killing fields of the round metric.  We exhibit the azimuthal
rotations `X = c·∂_β` (`qubitRotation`), constant fields that are
Killing because the metric does not depend on `β` — and we *classify*:
`qubit_generator_azimuthal` proves these are, on the domain, the only
generators.  (On the sphere itself the Killing algebra is
`so(3) ≅ su(2)`, but the other two rotation fields have `cot α`
components, which do not extend even continuously to the chart image
`α ∈ {0, π}` of the poles; since a generator's field is *globally*
smooth on the chart plane, only the azimuthal `so(2)` survives.
Recovering the full `su(2)` requires atlas-level smoothness — a
manifold-flavored refinement, deliberately out of scope.)

**The dichotomy** (`classical_quantum_dichotomy`): the classical bit
admits *only the zero* generator, while the qubit's generators are, on
the domain, *exactly* the line `ℝ · ∂_β` — every scalar multiple occurs
and nothing else does.  Juxtaposed with the two Stone theorems of this
project, this is Hardy's "continuous reversibility" axiom in theorem
form: classical state space supports no nontrivial continuous
divergence-preserving dynamics, and quantum state space does — which is
precisely why the quantum Stone correspondence has content
(`d² − 1` dimensions of it on the full state space) while the classical
one is a no-go.

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
* The qubit classification is a *chart-level* statement.  Of the
  sphere's three independent rotation fields only the azimuthal one is
  smooth on the whole chart plane, so `qubit_generator_azimuthal` — the
  once-"expensive converse", now a theorem — identifies the generators
  with `ℝ·∂_β`, not with `so(3)`.  The dichotomy needs only `0` versus
  `≥ 1`, so it is insensitive to this; the full `su(2)` statement is an
  atlas-level (manifold) refinement.

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
    {θ : ParamSpace 1} (hθ : θ ∈ classicalBitData.domain) :
    G.vectorField θ = 0 := by
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
  have hval : G.vectorField θ 0 = 0 := (mul_eq_zero.mp hc).resolve_right hne
  ext l
  obtain rfl : l = 0 := Subsingleton.elim l 0
  simpa using hval

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

/-- **The azimuthal rotation generators** `X = c·∂_β` on the qubit: the
constant fields `(0, c)`.  Killing because the metric is independent of
`β`; cubic-preserving because the cubic tensor is zero.  In `su(2)`
terms these are (the projectivizations of) the real multiples of
`σ_z/2`.  By `qubit_generator_azimuthal` below, on the domain they are
the *only* generators. -/
noncomputable def qubitRotation (c : ℝ) : qubitData.Generator where
  vectorField := fun _ => c • EuclideanSpace.single 1 1
  smooth := contDiff_const
  killing := by
    intro θ _ i j
    dsimp only [qubitData]
    rw [Fin.sum_univ_two]
    -- The field is constant, so both displacement derivatives vanish.
    rw [(hasFDerivAt_const ((c • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 0) θ).fderiv,
        (hasFDerivAt_const ((c • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 1) θ).fderiv]
    simp only [ContinuousLinearMap.zero_apply, mul_zero, add_zero,
      PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, one_ne_zero, if_false,
      if_true, mul_one]
    -- Remaining: the β-derivative of the metric entry vanishes.
    by_cases hij : i = j
    · subst hij
      by_cases hi : i = 0
      · subst hi
        simp only [if_true]
        rw [(hasFDerivAt_const (1 : ℝ) θ).fderiv]
        simp
      · simp only [if_neg hi, Fin.isValue, zero_ne_one, ↓reduceIte]
        rw [fderiv_coord_apply_ne (F := fun t => Real.sin t ^ 2) (k := (1 : Fin 2))
          ((Real.hasDerivAt_sin (θ 0)).pow 2) (by norm_num)]
        ring
    · simp only [if_neg hij]
      rw [(hasFDerivAt_const (0 : ℝ) θ).fderiv]
      simp
  preserves_cubic := by
    intro θ _ i j k
    dsimp only [qubitData]
    simp [(hasFDerivAt_const (0 : ℝ) θ).fderiv]

/-! ### Classification of the qubit generators

The converse to `qubitRotation`: *every* generator of `qubitData` is, on
the domain, a constant multiple of `∂_β`.  The three Killing equations in
the chart `g = diag(1, sin²α)` read

  `(0,0)`: `∂_α X⁰ = 0`
  `(0,1)`: `∂_β X⁰ + sin²α · ∂_α X¹ = 0`
  `(1,1)`: `X⁰ · 2 sin α cos α + 2 sin²α · ∂_β X¹ = 0`.

From `(0,0)`, `X⁰` is constant along each meridian `β = const`; `(1,1)`
then gives `sin α · ∂_β X¹ = −X⁰ cos α` along it.  The left side extends
continuously by `0` to the chart image `α = 0` of the pole (the field is
globally smooth), while the right side tends to `−X⁰`; hence `X⁰ = 0`.
The remaining equations force `∇X¹ = 0`, and the domain is
coordinate-connected, so `X¹` is a constant. -/

/-- Values of a real function whose derivative vanishes on `Set.Ioo a b`
agree across the interval (mean value theorem). -/
private lemma eq_of_hasDerivAt_zero_Ioo {F : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ x ∈ Set.Ioo a b, HasDerivAt F 0 x) :
    ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, F x = F y := by
  have key : ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, x < y → F x = F y := by
    intro x hx y hy hxy
    have hsub : Set.Icc x y ⊆ Set.Ioo a b := fun z hz =>
      ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩
    have hcont : ContinuousOn F (Set.Icc x y) := fun z hz =>
      (hF z (hsub hz)).continuousAt.continuousWithinAt
    obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope F (fun _ => 0) hxy hcont
      (fun z hz => hF z (hsub ⟨hz.1.le, hz.2.le⟩))
    have h0 : (F y - F x) / (y - x) = 0 := by simpa using hc.symm
    have := (div_eq_zero_iff.mp h0).resolve_right (sub_ne_zero.mpr hxy.ne')
    linarith
  intro x hx y hy
  rcases lt_trichotomy x y with h | h | h
  · exact key x hx y hy h
  · rw [h]
  · exact (key y hy x hx h).symm

/-- The parameter domain of the qubit is open (a coordinate slab). -/
private lemma qubitData_domain_isOpen : IsOpen qubitData.domain := by
  have h : qubitData.domain =
      (⇑(EuclideanSpace.proj (0 : Fin 2) : ParamSpace 2 →L[ℝ] ℝ)) ⁻¹'
        Set.Ioo 0 Real.pi := by
    ext θ
    simp [qubitData, EuclideanSpace.coe_proj, Set.mem_Ioo]
  rw [h]
  exact isOpen_Ioo.preimage
    (EuclideanSpace.proj (0 : Fin 2) : ParamSpace 2 →L[ℝ] ℝ).continuous

/-- Killing equation `(0,0)` of the qubit: `∂_α X⁰ = 0` on the domain. -/
private lemma qubit_killing₀₀ (G : qubitData.Generator) {θ : ParamSpace 2}
    (hθ : θ ∈ qubitData.domain) :
    fderiv ℝ (fun θ' => G.vectorField θ' 0) θ (EuclideanSpace.single 0 1) = 0 := by
  have hk := G.killing θ hθ 0 0
  dsimp only [qubitData] at hk
  rw [Fin.sum_univ_two] at hk
  simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, one_ne_zero] at hk
  rw [(hasFDerivAt_const (1 : ℝ) θ).fderiv] at hk
  simp only [ContinuousLinearMap.zero_apply, mul_zero, zero_mul, one_mul,
    add_zero, zero_add] at hk
  linarith

/-- Killing equation `(0,1)` of the qubit:
`∂_β X⁰ + sin²α · ∂_α X¹ = 0` on the domain. -/
private lemma qubit_killing₀₁ (G : qubitData.Generator) {θ : ParamSpace 2}
    (hθ : θ ∈ qubitData.domain) :
    fderiv ℝ (fun θ' => G.vectorField θ' 0) θ (EuclideanSpace.single 1 1) +
      Real.sin (θ 0) ^ 2 *
        fderiv ℝ (fun θ' => G.vectorField θ' 1) θ (EuclideanSpace.single 0 1)
      = 0 := by
  have hk := G.killing θ hθ 0 1
  dsimp only [qubitData] at hk
  rw [Fin.sum_univ_two] at hk
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one] at hk
  rw [(hasFDerivAt_const (0 : ℝ) θ).fderiv] at hk
  simp only [ContinuousLinearMap.zero_apply, mul_zero, zero_mul, one_mul,
    add_zero, zero_add] at hk
  linarith

/-- Killing equation `(1,1)` of the qubit:
`X⁰ · 2 sin α cos α + 2 sin²α · ∂_β X¹ = 0` on the domain. -/
private lemma qubit_killing₁₁ (G : qubitData.Generator) {θ : ParamSpace 2}
    (hθ : θ ∈ qubitData.domain) :
    G.vectorField θ 0 * (2 * Real.sin (θ 0) * Real.cos (θ 0)) +
      2 * Real.sin (θ 0) ^ 2 *
        fderiv ℝ (fun θ' => G.vectorField θ' 1) θ (EuclideanSpace.single 1 1)
      = 0 := by
  have hk := G.killing θ hθ 1 1
  dsimp only [qubitData] at hk
  rw [Fin.sum_univ_two] at hk
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one] at hk
  rw [fderiv_coord_apply (F := fun t => Real.sin t ^ 2) 0
      ((Real.hasDerivAt_sin (θ 0)).pow 2),
    fderiv_coord_apply_ne (F := fun t => Real.sin t ^ 2) (k := (1 : Fin 2))
      ((Real.hasDerivAt_sin (θ 0)).pow 2) (by norm_num)] at hk
  simp only [mul_zero, zero_mul, add_zero, zero_add, Nat.cast_ofNat] at hk
  linear_combination hk

/-- **Classification of the qubit's infinitesimal symmetries.**  Every
generator of `qubitData` restricts on the domain to a constant multiple
of the azimuthal field `∂_β`; with `qubitRotation` this identifies the
generators-on-the-domain with `ℝ · ∂_β`.

This is the honest, chart-level replacement for the naive "an `so(3)`'s
worth of Killing fields" count: the polar rotation fields `L_x, L_y`
have `cot α` components, which do not extend even continuously to the
chart image `α ∈ {0, π}` of the poles, so a *globally* smooth field can
realize only the azimuthal `so(2)`.  Recovering the full `su(2)` needs
atlas-level (manifold) smoothness, not a single chart. -/
theorem qubit_generator_azimuthal (G : qubitData.Generator) :
    ∃ c : ℝ, ∀ θ ∈ qubitData.domain,
      G.vectorField θ = c • EuclideanSpace.single 1 1 := by
  -- component regularity
  have hX₀d : Differentiable ℝ fun θ' => G.vectorField θ' 0 :=
    (G.contDiff_component 0).differentiable (by simp)
  have hX₁d : Differentiable ℝ fun θ' => G.vectorField θ' 1 :=
    (G.contDiff_component 1).differentiable (by simp)
  -- the meridian curves s ↦ (s, β), their coordinates and derivatives
  set mer : ℝ → ℝ → ParamSpace 2 := fun β s =>
    s • EuclideanSpace.single 0 1 + β • EuclideanSpace.single 1 1 with hmer_def
  have hmer0 : ∀ β s, mer β s 0 = s := by
    intro β s
    simp [hmer_def, PiLp.add_apply, PiLp.smul_apply]
  have hmer1 : ∀ β s, mer β s 1 = β := by
    intro β s
    simp [hmer_def, PiLp.add_apply, PiLp.smul_apply]
  have hmer_mem : ∀ β s, s ∈ Set.Ioo 0 Real.pi → mer β s ∈ qubitData.domain := by
    intro β s hs
    change 0 < mer β s 0 ∧ mer β s 0 < Real.pi
    rw [hmer0]
    exact ⟨hs.1, hs.2⟩
  have hmer_diag : ∀ θ : ParamSpace 2, mer (θ 1) (θ 0) = θ := by
    intro θ
    ext k
    fin_cases k
    · simpa using hmer0 (θ 1) (θ 0)
    · simpa using hmer1 (θ 1) (θ 0)
  have hmer_deriv : ∀ β s, HasDerivAt (mer β) (EuclideanSpace.single 0 1) s := by
    intro β s
    have h1 : HasDerivAt (fun t : ℝ => t • (EuclideanSpace.single 0 1 : ParamSpace 2))
        ((1 : ℝ) • EuclideanSpace.single 0 1) s :=
      (hasDerivAt_id s).smul_const _
    simpa [hmer_def] using h1.add_const (β • (EuclideanSpace.single 1 1 : ParamSpace 2))
  -- ═══ Step 1: X⁰ ≡ 0 on the domain ═══
  -- X⁰ is constant along each meridian; then (1,1) reads
  -- sin s · ∂_βX¹ = −X⁰ cos s along it, whose left side extends
  -- continuously by 0 to s = 0 while the right side tends to −X⁰.
  have hX₀_zero : ∀ θ ∈ qubitData.domain, G.vectorField θ 0 = 0 := by
    intro θ hθ
    have hmem : 0 < θ 0 ∧ θ 0 < Real.pi := hθ
    -- constancy of X⁰ along the meridian through θ
    have hψ : ∀ s ∈ Set.Ioo 0 Real.pi,
        HasDerivAt (fun t => G.vectorField (mer (θ 1) t) 0) 0 s := by
      intro s hs
      have h := (hX₀d (mer (θ 1) s)).hasFDerivAt.comp_hasDerivAt s
        (hmer_deriv (θ 1) s)
      rwa [qubit_killing₀₀ G (hmer_mem (θ 1) s hs)] at h
    have hconst := eq_of_hasDerivAt_zero_Ioo hψ
    have hval : ∀ s ∈ Set.Ioo 0 Real.pi,
        G.vectorField (mer (θ 1) s) 0 = G.vectorField θ 0 := by
      intro s hs
      have h := hconst s hs (θ 0) ⟨hmem.1, hmem.2⟩
      rwa [hmer_diag θ] at h
    -- ∂_βX¹ along the meridian
    set q : ℝ → ℝ := fun s => fderiv ℝ (fun θ' => G.vectorField θ' 1)
      (mer (θ 1) s) (EuclideanSpace.single 1 1) with hq_def
    have hq_cont : Continuous q := by
      have h1 : Continuous fun θ' => fderiv ℝ (fun θ'' => G.vectorField θ'' 1) θ' :=
        (G.contDiff_component 1).continuous_fderiv (by simp)
      have h2 : Continuous (mer (θ 1)) := by
        have := (continuous_id.smul continuous_const :
          Continuous fun s : ℝ => s • (EuclideanSpace.single 0 1 : ParamSpace 2))
        exact this.add continuous_const
      exact ((h1.comp h2).clm_apply continuous_const)
    -- the boundary identity sin s · q s = −X⁰(θ) cos s on (0, π)
    have hL : ∀ s ∈ Set.Ioo 0 Real.pi,
        Real.sin s * q s = -(G.vectorField θ 0 * Real.cos s) := by
      intro s hs
      have hk := qubit_killing₁₁ G (hmer_mem (θ 1) s hs)
      rw [hmer0 (θ 1) s, hval s hs] at hk
      have hsin : (0 : ℝ) < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs.1 hs.2
      have h2 : (2 * Real.sin s) * (Real.sin s * q s) =
          (2 * Real.sin s) * (-(G.vectorField θ 0 * Real.cos s)) := by
        rw [hq_def]
        ring_nf
        ring_nf at hk
        linarith
      exact mul_left_cancel₀ (by positivity) h2
    -- limits along 𝓝[>] 0: the left side → 0, the right side → −X⁰(θ)
    have h1 : Filter.Tendsto (fun s => Real.sin s * q s) (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
      have hc : Continuous fun s => Real.sin s * q s := Real.continuous_sin.mul hq_cont
      have := hc.tendsto 0
      rw [Real.sin_zero, zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h2 : Filter.Tendsto (fun s => Real.sin s * q s) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (-(G.vectorField θ 0))) := by
      have hc : Continuous fun s => -(G.vectorField θ 0 * Real.cos s) :=
        (continuous_const.mul Real.continuous_cos).neg
      have hlim := hc.tendsto 0
      rw [Real.cos_zero, mul_one] at hlim
      refine Filter.Tendsto.congr' ?_ (hlim.mono_left nhdsWithin_le_nhds)
      filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with s hs
      exact (hL s hs).symm
    have h0 := tendsto_nhds_unique h1 h2
    linarith
  -- ═══ Step 2: ∇X¹ ≡ 0 on the domain ═══
  have hDX₀ : ∀ θ ∈ qubitData.domain,
      fderiv ℝ (fun θ' => G.vectorField θ' 0) θ = 0 := by
    intro θ hθ
    have hev : (fun θ' => G.vectorField θ' 0) =ᶠ[nhds θ] fun _ => (0 : ℝ) := by
      filter_upwards [qubitData_domain_isOpen.mem_nhds hθ] with θ' hθ'
      exact hX₀_zero θ' hθ'
    rw [hev.fderiv_eq, (hasFDerivAt_const (0 : ℝ) θ).fderiv]
  have hsin_ne : ∀ θ ∈ qubitData.domain, Real.sin (θ 0) ≠ 0 := by
    intro θ hθ
    have hmem : 0 < θ 0 ∧ θ 0 < Real.pi := hθ
    exact (Real.sin_pos_of_pos_of_lt_pi hmem.1 hmem.2).ne'
  have hDX₁e₀ : ∀ θ ∈ qubitData.domain,
      fderiv ℝ (fun θ' => G.vectorField θ' 1) θ (EuclideanSpace.single 0 1) = 0 := by
    intro θ hθ
    have hk := qubit_killing₀₁ G hθ
    rw [hDX₀ θ hθ] at hk
    simp only [ContinuousLinearMap.zero_apply, zero_add] at hk
    exact (mul_eq_zero.mp hk).resolve_left (pow_ne_zero 2 (hsin_ne θ hθ))
  have hDX₁e₁ : ∀ θ ∈ qubitData.domain,
      fderiv ℝ (fun θ' => G.vectorField θ' 1) θ (EuclideanSpace.single 1 1) = 0 := by
    intro θ hθ
    have hk := qubit_killing₁₁ G hθ
    rw [hX₀_zero θ hθ] at hk
    simp only [zero_mul, zero_add] at hk
    have h2 : (2 : ℝ) * Real.sin (θ 0) ^ 2 ≠ 0 :=
      mul_ne_zero two_ne_zero (pow_ne_zero 2 (hsin_ne θ hθ))
    exact (mul_eq_zero.mp hk).resolve_left h2
  -- ═══ Step 3: X¹ is a single constant across the domain ═══
  have hhalf : Real.pi / 2 ∈ Set.Ioo 0 Real.pi :=
    ⟨by positivity, half_lt_self Real.pi_pos⟩
  refine ⟨G.vectorField (mer 0 (Real.pi / 2)) 1, fun θ hθ => ?_⟩
  have hmem : 0 < θ 0 ∧ θ 0 < Real.pi := hθ
  -- (i) along θ's meridian, X¹ is constant: X¹(θ) = X¹(θ 1, π/2)
  have hζ : ∀ s ∈ Set.Ioo 0 Real.pi,
      HasDerivAt (fun t => G.vectorField (mer (θ 1) t) 1) 0 s := by
    intro s hs
    have h := (hX₁d (mer (θ 1) s)).hasFDerivAt.comp_hasDerivAt s
      (hmer_deriv (θ 1) s)
    rwa [hDX₁e₀ _ (hmer_mem (θ 1) s hs)] at h
  have hstep1 : G.vectorField θ 1 = G.vectorField (mer (θ 1) (Real.pi / 2)) 1 := by
    have h := eq_of_hasDerivAt_zero_Ioo hζ (θ 0) ⟨hmem.1, hmem.2⟩ (Real.pi / 2) hhalf
    rwa [hmer_diag θ] at h
  -- (ii) along the equator α = π/2, X¹ is constant: X¹(β, π/2) = X¹(0, π/2)
  have hpar_deriv : ∀ t : ℝ,
      HasDerivAt (fun β => mer β (Real.pi / 2)) (EuclideanSpace.single 1 1) t := by
    intro t
    have h1 : HasDerivAt (fun β : ℝ => β • (EuclideanSpace.single 1 1 : ParamSpace 2))
        ((1 : ℝ) • EuclideanSpace.single 1 1) t :=
      (hasDerivAt_id t).smul_const _
    simpa [hmer_def] using
      h1.const_add ((Real.pi / 2) • (EuclideanSpace.single 0 1 : ParamSpace 2))
  have hξ : ∀ t : ℝ, HasDerivAt (fun β => G.vectorField (mer β (Real.pi / 2)) 1) 0 t := by
    intro t
    have h := (hX₁d (mer t (Real.pi / 2))).hasFDerivAt.comp_hasDerivAt t (hpar_deriv t)
    rwa [hDX₁e₁ _ (hmer_mem t (Real.pi / 2) hhalf)] at h
  have hstep2 : G.vectorField (mer (θ 1) (Real.pi / 2)) 1 =
      G.vectorField (mer 0 (Real.pi / 2)) 1 :=
    is_const_of_deriv_eq_zero (fun t => (hξ t).differentiableAt)
      (fun t => (hξ t).deriv) _ _
  -- assemble the vector identity
  ext k
  fin_cases k
  · simpa [PiLp.smul_apply, PiLp.single_apply] using hX₀_zero θ hθ
  · simpa [PiLp.smul_apply, PiLp.single_apply] using hstep1.trans hstep2

/-! ### The dichotomy -/

/-- **The classical–quantum dichotomy.**  The classical bit admits *only
the zero* infinitesimal symmetry of its information geometry; the
qubit's symmetries are, on the domain, *exactly* the line `ℝ · ∂_β` —
every multiple of the azimuthal rotation occurs (`qubitRotation`), and
nothing else does (`qubit_generator_azimuthal`).

Together with the two Stone theorems of this development — the
information-geometric one, whose objects are exactly these generators,
and the quantum-mechanical one, whose objects are self-adjoint
operators — this is the geometric core of Hardy's continuous
reversibility axiom: continuous reversible dynamics on state space is
impossible classically and abundant quantumly, and demanding its
existence already forces the quantum side of the divide. -/
theorem classical_quantum_dichotomy :
    (∀ G : classicalBitData.Generator,
      ∀ θ ∈ classicalBitData.domain, G.vectorField θ = 0) ∧
    (∀ c : ℝ, ∃ G : qubitData.Generator,
      ∀ θ : ParamSpace 2, G.vectorField θ = c • EuclideanSpace.single 1 1) ∧
    (∀ G : qubitData.Generator, ∃ c : ℝ,
      ∀ θ ∈ qubitData.domain, G.vectorField θ = c • EuclideanSpace.single 1 1) :=
  ⟨fun G _ hθ => classicalBit_rigid G hθ,
   fun c => ⟨qubitRotation c, fun _ => rfl⟩,
   fun G => qubit_generator_azimuthal G⟩

end GeometricData

end Spectra.InformationGeometry
