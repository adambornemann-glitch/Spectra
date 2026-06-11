/-
Spectra: TomitaTakesaki.lean
Tomita–Takesaki modular theory, rebuilt on the constructed spectral machinery.

Filename: ModularTheory/TomitaTakesaki.lean
Target: Mathlib master (2026-06-10)
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Star.Subalgebra
import Spectra.QuantumMechanics.Stone.Basic
import Spectra.SpectralTheory.Antilinear.Conjugation
/-!
# Tomita–Takesaki Modular Theory

This file rebuilds the old `LogosLibrary…ModularTheory/TomitaTakesaki.lean` on the
constructed spectral machinery.  The redesign in one line: **the modular operator is
carried as the one-parameter unitary group `t ↦ Δ^{it}`**, not as a bounded operator
with an axiomatized spectral measure.

| old (hypothesis/field — and in two cases *wrong*)        | new                                              |
| --------------------------------------------------------- | ------------------------------------------------ |
| `ModularOperatorData.op : H →L[ℂ] H` (Δ bounded — false in general) | `ModularData.flow : OneParameterUnitaryGroup` (`t ↦ Δ^{it}`) |
| `spectralMeasure` + `IsSpectralMeasure` (axiomatized)      | `spectralCalculus md.flow` = `g(log Δ)`, already constructed |
| `spectralPowerFunction t` (`λ^{it}`)                       | the character `e^{itω}` after `ω = log λ`; the group itself |
| `modularUnitary_group_law/zero/adjoint` (via old calculus) | theorems of `OneParameterUnitaryGroup` (group_law, identity, `inverse_eq_adjoint`) |
| `ClosabilityFromDenseAdjoint` (Prop hypothesis)            | `isClosableOn_of_formal_adjoint` (**theorem**, Reed–Simon VIII.1) |
| `separating`, `separating_commutant` (structure fields)    | **theorems** from cyclicity of the other algebra |
| `AntilinearOp` (bespoke structure)                         | plain semilinear maps `p →ₗ⋆[ℂ] H` on an explicit `Submodule` |
| `ModularConjugationData` (bespoke J)                       | `Conjugation` from `Operator/Antilinear/Conjugation.lean` |
| strong continuity of `t ↦ Δ^{it}ψ`, `t ↦ σ_t(a)ψ` (absent) | theorems (`strong_continuous`, `continuous_U_apply`) |
| `modularUnitary_isUnitary` (clunky `let`-statement)        | unitarity is a field of the group; adjoint = `U(−t)` is a theorem |

The single-state and *relative* pre-Tomita operators are unified into one definition
`preTomitaOpTo M Ω' : aΩ ↦ a*Ω'`; the relative file specializes it, killing the
four duplicated antilinearity proofs of the old pair of files.

## What is still a hypothesis (honest inventory)

* `ModularData` (existence of the flow `Δ^{it}` and the conjugation `J` with
  `JΩ = Ω`, `Δ^{it}Ω = Ω`, `JΔ^{it} = Δ^{it}J`) — this is the **polar
  decomposition of the closure of `S₀`**.  The closure itself is within reach
  (closability is proved below); the polar decomposition of a closed antilinear
  operator is the declared next milestone.  The KMS characterization of the flow
  belongs to the PeriodicStrip development.
* `TomitaTheorem` (`JMJ ⊆ M'` and `Δ^{it}MΔ^{-it} ⊆ M`) — the deep theorem
  (Takesaki, *TOA I*, Ch. VI).  Note `σ_t(M) = M` (equality) is *derived* from the
  one inclusion for all `t` (`modularAutomorphism_mem_iff`).

## Main definitions

* `commutant` — commutant of a set of bounded operators.
* `VNAlgebraWithVector` — a `*`-subalgebra of `B(H)` with a unit vector that is
  cyclic for it and for its commutant.  `separating` (both) are now theorems.
* `preTomitaOpTo M Ω'` — the conjugate-linear map `aΩ ↦ a*Ω'` on `MΩ`
  (`Ω' = M.Ω` gives the Tomita `S₀`; another state's vector gives `S_{ψ,φ}`).
* `preCoTomitaOpTo M Ω'` — `b'Ω ↦ b'*Ω'` on `M'Ω` (the formal adjoint partner).
* `IsClosableOn`, `isClosableOn_of_formal_adjoint` — closability, **proved**.
* `ModularData` — the flow `t ↦ Δ^{it}` and the conjugation `J`.
* `modularAutomorphism` — `σ_t(a) = Δ^{it} a Δ^{-it}` with the full lemma suite.
* `TomitaTheorem` — Tomita's theorem as a `Prop`-valued bundle.
* `vacuumState` — `ω = ⟪Ω, ·Ω⟫`, with normalization, positivity, faithfulness,
  and σ-invariance, all proved.
* `modularHamiltonian` — `K = log Δ = generator md.flow`, with `KΩ = 0` proved.

## References

* [Takesaki, *Theory of Operator Algebras I*][takesaki1979], Ch. VI
* [Bratteli–Robinson, *Operator Algebras and QSM 1*][bratteli1987], §2.5
* [Reed–Simon, *Methods of Modern Mathematical Physics I*][reedsimon1980], Thm. VIII.1
-/
open Complex Filter Topology
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## Unitary-group lemmas

Small additions to `OneParameterUnitaryGroup`: the group law in `*`-form, inverses,
the cancellation lemmas that drive every modular-algebra computation below by
`simp only [mul_assoc, U_neg_mul_cancel]`, and joint strong continuity
`t ↦ U(t)(f t)` (uniform boundedness `‖U(t)‖ = 1` makes the ε/3 argument one-sided). -/

namespace Spectra.QuantumMechanics.OneParameterUnitaryGroup

variable [CompleteSpace H] (W : OneParameterUnitaryGroup (H := H))

/-- The group law in multiplicative form: `U(s)·U(t) = U(s+t)`. -/
lemma U_mul (s t : ℝ) : W.U s * W.U t = W.U (s + t) := by
  ext ψ
  rw [ContinuousLinearMap.mul_apply, W.group_law s t, ContinuousLinearMap.comp_apply]

/-- `U(0) = 1`. -/
lemma U_zero : W.U 0 = 1 := by
  rw [W.identity, ContinuousLinearMap.one_def]

/-- `U(t)·U(−t) = 1`. -/
lemma U_mul_neg (t : ℝ) : W.U t * W.U (-t) = 1 := by
  rw [U_mul, add_neg_cancel, U_zero]

/-- `U(−t)·U(t) = 1`. -/
lemma U_neg_mul (t : ℝ) : W.U (-t) * W.U t = 1 := by
  rw [U_mul, neg_add_cancel, U_zero]

/-- Cancellation: `U(−t)·(U(t)·x) = x`.  The workhorse `simp` lemma for all the
telescoping products in the modular automorphism algebra and the cocycle identity. -/
lemma U_neg_mul_cancel (t : ℝ) (x : H →L[ℂ] H) : W.U (-t) * (W.U t * x) = x := by
  rw [← mul_assoc, U_neg_mul, one_mul]

/-- Cancellation: `U(t)·(U(−t)·x) = x`. -/
lemma U_mul_neg_cancel (t : ℝ) (x : H →L[ℂ] H) : W.U t * (W.U (-t) * x) = x := by
  rw [← mul_assoc, U_mul_neg, one_mul]

/-- **Joint strong continuity**: if `f : ℝ → H` is continuous, so is `t ↦ U(t)(f t)`.
`‖U(t)(f t) − U(t₀)(f t₀)‖ ≤ ‖f t − f t₀‖ + ‖U(t)(f t₀) − U(t₀)(f t₀)‖`, using
isometry for the first term and strong continuity for the second. -/
lemma continuous_U_apply {f : ℝ → H} (hf : Continuous f) :
    Continuous fun t => W.U t (f t) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have h1 : Tendsto (fun t => W.U t (f t) - W.U t (f t₀)) (𝓝 t₀) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have heq : ∀ t, ‖W.U t (f t) - W.U t (f t₀)‖ = ‖f t - f t₀‖ := fun t => by
      rw [← map_sub, norm_preserving]
    have h2 : Tendsto (fun t => ‖f t - f t₀‖) (𝓝 t₀) (𝓝 0) := by
      have h3 : Tendsto (fun t => f t - f t₀) (𝓝 t₀) (𝓝 (f t₀ - f t₀)) :=
        (hf.tendsto t₀).sub tendsto_const_nhds
      rw [sub_self] at h3
      simpa using h3.norm
    exact h2.congr fun t => (heq t).symm
  have h2 : Tendsto (fun t => W.U t (f t₀)) (𝓝 t₀) (𝓝 (W.U t₀ (f t₀))) :=
    (W.strong_continuous (f t₀)).tendsto t₀
  have h3 := h1.add h2
  rw [zero_add] at h3
  exact h3.congr fun t => by abel

end Spectra.QuantumMechanics.OneParameterUnitaryGroup

/-! ## Conjugation by an antiunitary, bundled as a bounded operator

For `J` a `Conjugation` and `a` bounded linear, `ψ ↦ J(a(Jψ))` is *linear* (the two
conjugations cancel on scalars) and bounded with the same norm.  This is the map
`a ↦ JaJ` whose range lies in the commutant by Tomita's theorem; bundling it as a
`ContinuousLinearMap` lets `JMJ ⊆ M'` be stated as plain membership. -/

namespace Spectra.QuantumMechanics.SpectralTheory.Conjugation

/-- Conjugation of a bounded operator by an antiunitary: `(conjAd J a)ψ = J(a(Jψ))`. -/
noncomputable def conjAd (J : Conjugation H) (a : H →L[ℂ] H) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun ψ => J (a (J ψ))
      map_add' := fun ψ φ => by
        simp only [Conjugation.map_add, map_add];
        simp; exact map_add J (a (J ψ)) (a (J φ))
      map_smul' := fun c ψ => by
        simp only [Conjugation.map_smul, RingHom.id_apply]
        -- ⊢ J (a ((starRingEnd ℂ) c • J ψ)) = c • J (a (J ψ))
        rw [a.map_smul, Conjugation.map_smul, Complex.conj_conj] }
    ‖a‖
    (fun ψ => by
      show ‖J (a (J ψ))‖ ≤ ‖a‖ * ‖ψ‖
      rw [Conjugation.norm_map]
      calc ‖a (J ψ)‖ ≤ ‖a‖ * ‖J ψ‖ := a.le_opNorm _
        _ = ‖a‖ * ‖ψ‖ := by rw [Conjugation.norm_map])

@[simp] lemma conjAd_apply (J : Conjugation H) (a : H →L[ℂ] H) (ψ : H) :
    conjAd J a ψ = J (a (J ψ)) := rfl

end Spectra.QuantumMechanics.SpectralTheory.Conjugation

namespace Spectra.QuantumMechanics.ModularTheory

open Spectra.QuantumMechanics OneParameterUnitaryGroup
open Spectra.QuantumMechanics.SpectralTheory

variable [CompleteSpace H]

/-! ## Adjoint bookkeeping

`star = adjoint` on `H →L[ℂ] H`; these three lemmas keep that rewrite in one place. -/

/-- The adjoint reverses products. -/
lemma adjoint_mul (A B : H →L[ℂ] H) :
    ContinuousLinearMap.adjoint (A * B)
      = ContinuousLinearMap.adjoint B * ContinuousLinearMap.adjoint A := by
  have h : star (A * B) = star B * star A := star_mul A B
  rwa [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.star_eq_adjoint] at h

/-- `1† = 1`. -/
lemma adjoint_one : ContinuousLinearMap.adjoint (1 : H →L[ℂ] H) = 1 := by
  have h : star (1 : H →L[ℂ] H) = 1 := star_one _
  rwa [ContinuousLinearMap.star_eq_adjoint] at h

/-- A `*`-subalgebra is closed under taking adjoints. -/
lemma adjoint_mem {A : StarSubalgebra ℂ (H →L[ℂ] H)} {a : H →L[ℂ] H} (ha : a ∈ A) :
    ContinuousLinearMap.adjoint a ∈ A := by
  have h : star a ∈ A := star_mem ha
  rwa [ContinuousLinearMap.star_eq_adjoint] at h

omit [CompleteSpace H] in
/-- A vector orthogonal (in the second slot) to a dense set is zero. -/
theorem eq_zero_of_inner_left_dense {s : Set H} (hs : Dense s) {x : H}
    (h : ∀ v ∈ s, ⟪v, x⟫_ℂ = 0) : x = 0 := by
  have hcont : Continuous fun v : H => ⟪v, x⟫_ℂ := continuous_id.inner continuous_const
  have hfun : (fun v : H => ⟪v, x⟫_ℂ) = fun _ => (0 : ℂ) :=
    Continuous.ext_on hs hcont continuous_const h
  exact inner_self_eq_zero.mp (congrFun hfun x)

/-!
## Section 1: Von Neumann algebra with cyclic vector

A `*`-subalgebra `M ⊆ B(H)` with a unit vector `Ω` that is cyclic for `M` *and* for
the commutant `M'`.  This is leaner than the old structure: `separating` for `M`
and for `M'` were fields there; here they are **theorems** (`b'Ω = 0` with `b' ∈ M'`
forces `b'` to vanish on the dense set `MΩ` by commutativity, and symmetrically).
The remaining genuinely independent fields — cyclicity of `Ω` for `M'` — would
follow from `separating` only via the double-commutant theorem, so we keep it.
-/

/-- The commutant of a set of bounded operators. -/
def commutant (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H) :=
  {b | ∀ a ∈ S, a * b = b * a}

omit [CompleteSpace H] in
lemma mem_commutant_iff {S : Set (H →L[ℂ] H)} {b : H →L[ℂ] H} :
    b ∈ commutant S ↔ ∀ a ∈ S, a * b = b * a := Iff.rfl

omit [CompleteSpace H] in
lemma commutant_add_mem {S : Set (H →L[ℂ] H)} {b c : H →L[ℂ] H}
    (hb : b ∈ commutant S) (hc : c ∈ commutant S) : b + c ∈ commutant S :=
  fun a ha => by rw [mul_add, add_mul, hb a ha, hc a ha]

omit [CompleteSpace H] in
lemma commutant_smul_mem {S : Set (H →L[ℂ] H)} (z : ℂ) {b : H →L[ℂ] H}
    (hb : b ∈ commutant S) : z • b ∈ commutant S :=
  fun a ha => by rw [mul_smul_comm, hb a ha, ← smul_mul_assoc]

omit [CompleteSpace H] in
lemma commutant_zero_mem {S : Set (H →L[ℂ] H)} : (0 : H →L[ℂ] H) ∈ commutant S :=
  fun a _ => by rw [mul_zero, zero_mul]

/-- The ambient data for Tomita–Takesaki theory: a `*`-subalgebra of `B(H)` with a
distinguished unit vector that is cyclic for the algebra and for its commutant.

The vector plays the role of the vacuum in QFT, or the GNS vector of a faithful
normal state.  Both *separating* properties are theorems (`separating`,
`separating_commutant`), not fields. -/
structure VNAlgebraWithVector (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The algebra, as a `*`-subalgebra of `B(H)`. -/
  algebra : StarSubalgebra ℂ (H →L[ℂ] H)
  /-- The distinguished vector. -/
  Ω : H
  /-- Ω is normalized. -/
  Ω_norm : ‖Ω‖ = 1
  /-- **Cyclic**: `MΩ` is dense in `H`. -/
  cyclic : Dense {ξ : H | ∃ a ∈ algebra, a Ω = ξ}
  /-- Ω is cyclic for the commutant `M'`.  (Equivalent to Ω being separating for
  `M` once the double-commutant theorem is available; independent until then.) -/
  cyclic_commutant : Dense {ξ : H | ∃ b ∈ commutant (algebra : Set (H →L[ℂ] H)), b Ω = ξ}

namespace VNAlgebraWithVector

variable (M : VNAlgebraWithVector H)

lemma Ω_ne_zero : M.Ω ≠ 0 := by
  intro h
  have h1 := M.Ω_norm
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

/-- **Ω is separating for `M`** — a theorem now: if `aΩ = 0` then `a` kills the
dense set `M'Ω` (commute `a` past `b'`), hence `a = 0` by continuity. -/
theorem separating : ∀ a ∈ M.algebra, a M.Ω = 0 → a = 0 := by
  intro a ha h0
  have hvanish : ∀ ξ ∈ {ξ : H | ∃ b ∈ commutant (M.algebra : Set (H →L[ℂ] H)), b M.Ω = ξ},
      a ξ = (fun _ => (0 : H)) ξ := by
    rintro _ ⟨b, hb, rfl⟩
    calc a (b M.Ω) = b (a M.Ω) := by
          have h := congrArg (fun A : H →L[ℂ] H => A M.Ω) (hb a ha)
          simpa [ContinuousLinearMap.mul_apply] using h
      _ = (fun _ => (0 : H)) (b M.Ω) := by rw [h0, map_zero]
  have hfun : (⇑a : H → H) = fun _ => 0 :=
    Continuous.ext_on M.cyclic_commutant a.continuous continuous_const hvanish
  ext ψ
  rw [ContinuousLinearMap.zero_apply]
  exact congrFun hfun ψ

/-- **Ω is separating for `M'`** — symmetric argument against the dense set `MΩ`. -/
theorem separating_commutant :
    ∀ b ∈ commutant (M.algebra : Set (H →L[ℂ] H)), b M.Ω = 0 → b = 0 := by
  intro b hb h0
  have hvanish : ∀ ξ ∈ {ξ : H | ∃ a ∈ M.algebra, a M.Ω = ξ},
      b ξ = (fun _ => (0 : H)) ξ := by
    rintro _ ⟨a, ha, rfl⟩
    calc b (a M.Ω) = a (b M.Ω) := by
          have h := congrArg (fun A : H →L[ℂ] H => A M.Ω) (hb a ha).symm
          simpa [ContinuousLinearMap.mul_apply] using h
      _ = (fun _ => (0 : H)) (a M.Ω) := by rw [h0, map_zero]
  have hfun : (⇑b : H → H) = fun _ => 0 :=
    Continuous.ext_on M.cyclic b.continuous continuous_const hvanish
  ext ψ
  rw [ContinuousLinearMap.zero_apply]
  exact congrFun hfun ψ

/-- The dense subspace `MΩ = {aΩ : a ∈ M}`. -/
def algebraΩ : Submodule ℂ H where
  carrier := {ξ | ∃ a ∈ M.algebra, a M.Ω = ξ}
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, M.algebra.add_mem ha hb, by simp [ContinuousLinearMap.add_apply]⟩
  zero_mem' := ⟨0, M.algebra.zero_mem, by simp⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, rfl⟩
    exact ⟨c • a, M.algebra.smul_mem ha c, by simp [ContinuousLinearMap.smul_apply]⟩

/-- The dense subspace `M'Ω = {b'Ω : b' ∈ M'}`. -/
def commutantΩ : Submodule ℂ H where
  carrier := {ξ | ∃ b ∈ commutant (M.algebra : Set (H →L[ℂ] H)), b M.Ω = ξ}
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, commutant_add_mem ha hb, by simp [ContinuousLinearMap.add_apply]⟩
  zero_mem' := ⟨0, commutant_zero_mem, by simp⟩
  smul_mem' := by
    rintro c _ ⟨b, hb, rfl⟩
    exact ⟨c • b, commutant_smul_mem c hb, by simp [ContinuousLinearMap.smul_apply]⟩

/-- `MΩ` is dense (definitionally the `cyclic` field). -/
lemma algebraΩ_dense : Dense (M.algebraΩ : Set H) := M.cyclic

/-- `M'Ω` is dense (definitionally the `cyclic_commutant` field). -/
lemma commutantΩ_dense : Dense (M.commutantΩ : Set H) := M.cyclic_commutant

/-!
### Representatives

By separability, every `ξ ∈ MΩ` is `aΩ` for a *unique* `a ∈ M`; `algebraΩ_repr`
picks it.  The `_add`/`_smul` lemmas are the only place uniqueness is exercised;
the semilinear-map construction below consumes them.
-/

/-- The unique representative: `a ∈ M` with `aΩ = ξ`. -/
noncomputable def algebraΩ_repr (ξ : M.algebraΩ) : H →L[ℂ] H :=
  Classical.choose ξ.property

lemma algebraΩ_repr_mem (ξ : M.algebraΩ) : M.algebraΩ_repr ξ ∈ M.algebra :=
  (Classical.choose_spec ξ.property).1

lemma algebraΩ_repr_spec (ξ : M.algebraΩ) : M.algebraΩ_repr ξ M.Ω = (ξ : H) :=
  (Classical.choose_spec ξ.property).2

/-- The representative is unique (Ω separating for `M`). -/
lemma algebraΩ_repr_unique (ξ : M.algebraΩ) (a : H →L[ℂ] H)
    (ha : a ∈ M.algebra) (haΩ : a M.Ω = (ξ : H)) :
    a = M.algebraΩ_repr ξ := by
  have h_diff : (a - M.algebraΩ_repr ξ) M.Ω = 0 := by
    simp [ContinuousLinearMap.sub_apply, haΩ, M.algebraΩ_repr_spec ξ]
  have h_mem : a - M.algebraΩ_repr ξ ∈ M.algebra :=
    M.algebra.sub_mem ha (M.algebraΩ_repr_mem ξ)
  exact sub_eq_zero.mp (M.separating _ h_mem h_diff)

lemma algebraΩ_repr_add (ξ φ : M.algebraΩ) :
    M.algebraΩ_repr (ξ + φ) = M.algebraΩ_repr ξ + M.algebraΩ_repr φ := by
  symm
  apply M.algebraΩ_repr_unique
  · exact M.algebra.add_mem (M.algebraΩ_repr_mem ξ) (M.algebraΩ_repr_mem φ)
  · simp [ContinuousLinearMap.add_apply, M.algebraΩ_repr_spec]

lemma algebraΩ_repr_smul (c : ℂ) (ξ : M.algebraΩ) :
    M.algebraΩ_repr (c • ξ) = c • M.algebraΩ_repr ξ := by
  symm
  apply M.algebraΩ_repr_unique
  · exact M.algebra.smul_mem (M.algebraΩ_repr_mem ξ) c
  · simp [ContinuousLinearMap.smul_apply, M.algebraΩ_repr_spec]

/-- The unique commutant representative: `b' ∈ M'` with `b'Ω = η`. -/
noncomputable def commutantΩ_repr (η : M.commutantΩ) : H →L[ℂ] H :=
  Classical.choose η.property

lemma commutantΩ_repr_mem (η : M.commutantΩ) :
    M.commutantΩ_repr η ∈ commutant (M.algebra : Set (H →L[ℂ] H)) :=
  (Classical.choose_spec η.property).1

lemma commutantΩ_repr_spec (η : M.commutantΩ) :
    M.commutantΩ_repr η M.Ω = (η : H) :=
  (Classical.choose_spec η.property).2

/-- The commutant representative is unique (Ω separating for `M'`). -/
lemma commutantΩ_repr_unique (η : M.commutantΩ) (b : H →L[ℂ] H)
    (hb : b ∈ commutant (M.algebra : Set (H →L[ℂ] H))) (hbΩ : b M.Ω = (η : H)) :
    b = M.commutantΩ_repr η := by
  have h_diff : (b - M.commutantΩ_repr η) M.Ω = 0 := by
    simp [ContinuousLinearMap.sub_apply, hbΩ, M.commutantΩ_repr_spec η]
  have h_mem : b - M.commutantΩ_repr η ∈ commutant (M.algebra : Set (H →L[ℂ] H)) := by
    intro a ha
    simp [mul_sub, sub_mul, hb a ha, M.commutantΩ_repr_mem η a ha]
  exact sub_eq_zero.mp (M.separating_commutant _ h_mem h_diff)

lemma commutantΩ_repr_add (η₁ η₂ : M.commutantΩ) :
    M.commutantΩ_repr (η₁ + η₂) = M.commutantΩ_repr η₁ + M.commutantΩ_repr η₂ := by
  symm
  apply M.commutantΩ_repr_unique
  · exact commutant_add_mem (M.commutantΩ_repr_mem η₁) (M.commutantΩ_repr_mem η₂)
  · simp [ContinuousLinearMap.add_apply, M.commutantΩ_repr_spec]

lemma commutantΩ_repr_smul (c : ℂ) (η : M.commutantΩ) :
    M.commutantΩ_repr (c • η) = c • M.commutantΩ_repr η := by
  symm
  apply M.commutantΩ_repr_unique
  · exact commutant_smul_mem c (M.commutantΩ_repr_mem η)
  · simp [ContinuousLinearMap.smul_apply, M.commutantΩ_repr_spec]

end VNAlgebraWithVector

/-!
## Section 2: Closability of densely defined antilinear operators

Unbounded antilinear operators are carried as plain semilinear maps
`p →ₗ⋆[ℂ] H` on an explicit dense `Submodule ℂ H` — no bespoke `AntilinearOp`,
and no dependence on `LinearPMap`'s (still `RingHom.id`-only) closure API.

The Reed–Simon closability criterion is now a **theorem**: an operator with a
densely defined formal adjoint is closable.  This discharges the old
`ClosabilityFromDenseAdjoint` hypothesis.
-/

/-- `T : p → H` is closable: if `ξₙ → 0` in `H` with `T ξₙ → η`, then `η = 0`
(i.e. `(0, η)` in the graph closure forces `η = 0`). -/
def IsClosableOn (p : Submodule ℂ H) (T : p →ₗ⋆[ℂ] H) : Prop :=
  ∀ (ξs : ℕ → p) (η : H),
    Tendsto (fun n => (ξs n : H)) atTop (𝓝 0) →
    Tendsto (fun n => T (ξs n)) atTop (𝓝 η) →
    η = 0

omit [CompleteSpace H] in
/-- **Closability from a densely defined formal adjoint** (Reed–Simon, Thm. VIII.1,
antilinear version).  If `⟪Tξ, η⟫ = ⟪Fη, ξ⟫` with `dom F` dense, then for `ξₙ → 0`,
`Tξₙ → η`: `⟪η, η'⟫ = lim ⟪Tξₙ, η'⟫ = lim ⟪Fη', ξₙ⟫ = 0` on the dense `dom F`. -/
theorem isClosableOn_of_formal_adjoint {p q : Submodule ℂ H}
    (T : p →ₗ⋆[ℂ] H) (F : q →ₗ⋆[ℂ] H)
    (hq : Dense (q : Set H))
    (hadj : ∀ (ξ : p) (η : q), ⟪T ξ, (η : H)⟫_ℂ = ⟪F η, (ξ : H)⟫_ℂ) :
    IsClosableOn p T := by
  intro ξs η hξ0 hTη
  refine eq_zero_of_inner_left_dense hq fun v hv => ?_
  have key : ⟪η, v⟫_ℂ = 0 := by
    have h1 : Tendsto (fun n => ⟪T (ξs n), v⟫_ℂ) atTop (𝓝 ⟪η, v⟫_ℂ) :=
      hTη.inner tendsto_const_nhds
    have h2 : Tendsto (fun n => ⟪T (ξs n), v⟫_ℂ) atTop (𝓝 0) := by
      have h3 : Tendsto (fun n => ⟪F ⟨v, hv⟩, (ξs n : H)⟫_ℂ) atTop
          (𝓝 ⟪F ⟨v, hv⟩, (0 : H)⟫_ℂ) :=
        tendsto_const_nhds.inner hξ0
      rw [inner_zero_right] at h3
      exact h3.congr fun n => (hadj (ξs n) ⟨v, hv⟩).symm
    exact tendsto_nhds_unique h1 h2
  rw [← inner_conj_symm, key, map_zero]

/-!
## Section 3: The Tomita operator, with arbitrary target vector

One definition serves both the single-state theory and the relative theory:

  `preTomitaOpTo M Ω' : MΩ → H,  aΩ ↦ a*Ω'`

`Ω' = M.Ω` gives the Tomita `S₀`; `Ω' = Ω_ψ` (another cyclic/separating vector for
the same algebra) gives the relative `S_{ψ,φ}` — see `RelativeModular.lean`.
Antilinearity: `S(c·aΩ) = (ca)*Ω' = c̄·a*Ω'`.  The formal adjoint partner is
`preCoTomitaOpTo M Ω' : M'Ω → H, b'Ω ↦ b'*Ω'`, and the adjointness chain

  `⟪a*Ω', b'Ω⟫ = ⟪Ω', a b'Ω⟫ = ⟪Ω', b' aΩ⟫ = ⟪b'*Ω', aΩ⟫`

works *uniformly in the target* — both sides decompose over the base `Ω`.
-/

variable (M : VNAlgebraWithVector H)

open VNAlgebraWithVector

/-- The (possibly relative) pre-Tomita operator `aΩ ↦ a*Ω'`. -/
noncomputable def preTomitaOpTo (Ω' : H) : M.algebraΩ →ₗ⋆[ℂ] H where
  toFun ξ := ContinuousLinearMap.adjoint (M.algebraΩ_repr ξ) Ω'
  map_add' ξ φ := by
    rw [M.algebraΩ_repr_add ξ φ]
    have h : ContinuousLinearMap.adjoint (M.algebraΩ_repr ξ + M.algebraΩ_repr φ)
        = ContinuousLinearMap.adjoint (M.algebraΩ_repr ξ)
          + ContinuousLinearMap.adjoint (M.algebraΩ_repr φ) := by
      change star (_ + _) = star _ + star _
      exact star_add _ _
    rw [h, ContinuousLinearMap.add_apply]
  map_smul' c ξ := by
    rw [M.algebraΩ_repr_smul c ξ]
    have h : ContinuousLinearMap.adjoint (c • M.algebraΩ_repr ξ)
        = starRingEnd ℂ c • ContinuousLinearMap.adjoint (M.algebraΩ_repr ξ) := by
      change star (c • _) = starRingEnd ℂ c • star _
      exact star_smul c _
    rw [h, ContinuousLinearMap.smul_apply]

@[simp] lemma preTomitaOpTo_apply (Ω' : H) (ξ : M.algebraΩ) :
    preTomitaOpTo M Ω' ξ = ContinuousLinearMap.adjoint (M.algebraΩ_repr ξ) Ω' := rfl

/-- The (possibly relative) pre-co-Tomita operator `b'Ω ↦ b'*Ω'` on `M'Ω`. -/
noncomputable def preCoTomitaOpTo (Ω' : H) : M.commutantΩ →ₗ⋆[ℂ] H where
  toFun η := ContinuousLinearMap.adjoint (M.commutantΩ_repr η) Ω'
  map_add' η₁ η₂ := by
    rw [M.commutantΩ_repr_add η₁ η₂]
    have h : ContinuousLinearMap.adjoint (M.commutantΩ_repr η₁ + M.commutantΩ_repr η₂)
        = ContinuousLinearMap.adjoint (M.commutantΩ_repr η₁)
          + ContinuousLinearMap.adjoint (M.commutantΩ_repr η₂) := by
      change star (_ + _) = star _ + star _
      exact star_add _ _
    rw [h, ContinuousLinearMap.add_apply]
  map_smul' c η := by
    rw [M.commutantΩ_repr_smul c η]
    have h : ContinuousLinearMap.adjoint (c • M.commutantΩ_repr η)
        = starRingEnd ℂ c • ContinuousLinearMap.adjoint (M.commutantΩ_repr η) := by
      change star (c • _) = starRingEnd ℂ c • star _
      exact star_smul c _
    rw [h, ContinuousLinearMap.smul_apply]

@[simp] lemma preCoTomitaOpTo_apply (Ω' : H) (η : M.commutantΩ) :
    preCoTomitaOpTo M Ω' η = ContinuousLinearMap.adjoint (M.commutantΩ_repr η) Ω' := rfl

/-- Well-definedness: the value depends only on `ξ`, not on the representative. -/
lemma preTomitaOpTo_wellDefined (Ω' : H) (a : H →L[ℂ] H) (ha : a ∈ M.algebra)
    (ξ : M.algebraΩ) (haξ : a M.Ω = (ξ : H)) :
    ContinuousLinearMap.adjoint a Ω' = preTomitaOpTo M Ω' ξ := by
  rw [preTomitaOpTo_apply]
  exact congrArg (fun b => ContinuousLinearMap.adjoint b Ω')
    (M.algebraΩ_repr_unique ξ a ha haξ)

/-- The base vector maps to the target: `S(1·Ω) = 1*·Ω' = Ω'`. -/
lemma preTomitaOpTo_vacuum (Ω' : H) :
    preTomitaOpTo M Ω' ⟨M.Ω, ⟨1, M.algebra.one_mem, by simp⟩⟩ = Ω' := by
  rw [preTomitaOpTo_apply]
  have h1 : M.algebraΩ_repr ⟨M.Ω, ⟨1, M.algebra.one_mem, by simp⟩⟩ = 1 := by
    symm
    apply M.algebraΩ_repr_unique
    · exact M.algebra.one_mem
    · simp
  rw [h1, adjoint_one, ContinuousLinearMap.one_apply]

/-- **Formal adjointness, uniformly in the target**:
`⟪S(aΩ), b'Ω⟫ = ⟪F(b'Ω), aΩ⟫` for `S = preTomitaOpTo M Ω'`, `F = preCoTomitaOpTo M Ω'`.

The chain `⟪a*Ω', b'Ω⟫ = ⟪Ω', a(b'Ω)⟫ = ⟪Ω', b'(aΩ)⟫ = ⟪b'*Ω', aΩ⟫` uses only
that `a ∈ M` and `b' ∈ M'` commute; the target `Ω'` rides along in the first slot.
At `Ω' = M.Ω` this is the classical Tomita formal adjointness; at `Ω' = Ω_ψ` it is
the relative version (with the *same* proof — the reason the two old files'
duplicated arguments could be collapsed). -/
theorem preTomitaOpTo_formal_adjoint (Ω' : H) (ξ : M.algebraΩ) (η : M.commutantΩ) :
    ⟪preTomitaOpTo M Ω' ξ, (η : H)⟫_ℂ = ⟪preCoTomitaOpTo M Ω' η, (ξ : H)⟫_ℂ := by
  rw [preTomitaOpTo_apply, preCoTomitaOpTo_apply]
  set a := M.algebraΩ_repr ξ with ha_def
  set b := M.commutantΩ_repr η with hb_def
  have ha_mem := M.algebraΩ_repr_mem ξ
  have hb_mem := M.commutantΩ_repr_mem η
  have h_comm : a * b = b * a := hb_mem a ha_mem
  rw [← M.algebraΩ_repr_spec ξ, ← M.commutantΩ_repr_spec η]
  calc ⟪ContinuousLinearMap.adjoint a Ω', b M.Ω⟫_ℂ
      = ⟪Ω', a (b M.Ω)⟫_ℂ := by
        rw [ContinuousLinearMap.adjoint_inner_left]
    _ = ⟪Ω', b (a M.Ω)⟫_ℂ := by
        congr 1
        have h := congrArg (fun A : H →L[ℂ] H => A M.Ω) h_comm
        simpa [ContinuousLinearMap.mul_apply] using h
    _ = ⟪ContinuousLinearMap.adjoint b Ω', a M.Ω⟫_ℂ := by
        rw [ContinuousLinearMap.adjoint_inner_left]

/-- **Closability** (theorem, not hypothesis): for every target `Ω'`, the operator
`aΩ ↦ a*Ω'` is closable, since `b'Ω ↦ b'*Ω'` is a densely defined formal adjoint. -/
theorem preTomitaOpTo_isClosable (Ω' : H) :
    IsClosableOn M.algebraΩ (preTomitaOpTo M Ω') :=
  isClosableOn_of_formal_adjoint (preTomitaOpTo M Ω') (preCoTomitaOpTo M Ω')
    M.commutantΩ_dense (preTomitaOpTo_formal_adjoint M Ω')

/-! ### The single-state specializations -/

/-- **The Tomita operator** `S₀ : aΩ ↦ a*Ω` (target = base vector). -/
noncomputable def preTomitaOp : M.algebraΩ →ₗ⋆[ℂ] H := preTomitaOpTo M M.Ω

/-- **The co-Tomita operator** `F₀ : b'Ω ↦ b'*Ω` on `M'Ω`. -/
noncomputable def preCoTomitaOp : M.commutantΩ →ₗ⋆[ℂ] H := preCoTomitaOpTo M M.Ω

@[simp] lemma preTomitaOp_apply (ξ : M.algebraΩ) :
    preTomitaOp M ξ = ContinuousLinearMap.adjoint (M.algebraΩ_repr ξ) M.Ω := rfl

@[simp] lemma preCoTomitaOp_apply (η : M.commutantΩ) :
    preCoTomitaOp M η = ContinuousLinearMap.adjoint (M.commutantΩ_repr η) M.Ω := rfl

/-- Formal adjointness of `S₀` and `F₀`: `⟪S₀(aΩ), b'Ω⟫ = ⟪F₀(b'Ω), aΩ⟫`. -/
theorem preTomita_formal_adjoint (ξ : M.algebraΩ) (η : M.commutantΩ) :
    ⟪preTomitaOp M ξ, (η : H)⟫_ℂ = ⟪preCoTomitaOp M η, (ξ : H)⟫_ℂ :=
  preTomitaOpTo_formal_adjoint M M.Ω ξ η

/-- `S₀` is closable. -/
theorem preTomitaOp_isClosable : IsClosableOn M.algebraΩ (preTomitaOp M) :=
  preTomitaOpTo_isClosable M M.Ω

/-- `S₀` maps `MΩ` into itself: `S₀(aΩ) = a*Ω ∈ MΩ`. -/
lemma preTomitaOp_mem (ξ : M.algebraΩ) : preTomitaOp M ξ ∈ M.algebraΩ :=
  ⟨ContinuousLinearMap.adjoint (M.algebraΩ_repr ξ),
    adjoint_mem (M.algebraΩ_repr_mem ξ), (preTomitaOp_apply M ξ).symm⟩

/-- **`S₀` is an involution on `MΩ`**: `S₀(S₀(aΩ)) = S₀(a*Ω) = a**Ω = aΩ`. -/
lemma preTomitaOp_involutive (ξ : M.algebraΩ) :
    preTomitaOp M ⟨preTomitaOp M ξ, preTomitaOp_mem M ξ⟩ = (ξ : H) := by
  have hrepr : M.algebraΩ_repr ⟨preTomitaOp M ξ, preTomitaOp_mem M ξ⟩
      = ContinuousLinearMap.adjoint (M.algebraΩ_repr ξ) := by
    symm
    apply M.algebraΩ_repr_unique
    · exact adjoint_mem (M.algebraΩ_repr_mem ξ)
    · exact (preTomitaOp_apply M ξ).symm
  rw [preTomitaOp_apply, hrepr, ContinuousLinearMap.adjoint_adjoint,
    M.algebraΩ_repr_spec ξ]

/-!
## Section 4: The modular structure

The output of the (future) polar decomposition `S = JΔ^{1/2}`, packaged as the
data actually used downstream:

* the **modular flow** `t ↦ Δ^{it}` as a `OneParameterUnitaryGroup` — so the
  group law, `Δ^{i·0} = 1`, `(Δ^{it})† = Δ^{−it}`, unitarity, and strong
  continuity are theorems of the Stone development, not stored fields; and the
  bounded calculus `g(log Δ) = spectralCalculus flow g` is available whenever
  the calculus files are imported (e.g. `Δ^{it} = Φ(e^{itω})` is
  `spectralCalculus_char`);
* the **modular conjugation** `J` as a `Conjugation`;
* the kinematic identities they satisfy: `Δ^{it}Ω = Ω`, `JΩ = Ω`, and
  `JΔ^{it} = Δ^{it}J` — the unitary-group form of `JΔJ = Δ⁻¹` (antilinearity of
  `J` conjugates the `i`; the inverse flips it back: `(Δ⁻¹)^{−it} = Δ^{it}`;
  cf. Bratteli–Robinson Prop. 2.5.11).

Constructing a term of this structure from a `VNAlgebraWithVector` is the polar
decomposition project; the KMS characterization of the flow belongs to the
PeriodicStrip development.  The old `ModularOperatorData` (bounded `Δ`,
axiomatized spectral measure) and `ModularConjugationData` are both subsumed.
-/

/-- The modular data of `(M, Ω)`: the flow `t ↦ Δ^{it}` and the conjugation `J`,
with the kinematic identities from the polar decomposition. -/
structure ModularData (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : VNAlgebraWithVector H) where
  /-- The modular flow `t ↦ Δ^{it}`. -/
  flow : OneParameterUnitaryGroup (H := H)
  /-- The modular conjugation `J`. -/
  J : Conjugation H
  /-- `Δ^{it}Ω = Ω` for all `t` (equivalently `Ω ∈ ker(log Δ)`,
  see `modularHamiltonian_vacuum`). -/
  flow_fixes_vacuum : ∀ t : ℝ, flow.U t M.Ω = M.Ω
  /-- `JΩ = Ω`. -/
  J_fixes_vacuum : J M.Ω = M.Ω
  /-- `JΔ^{it} = Δ^{it}J` — the unitary form of `JΔJ = Δ⁻¹`. -/
  J_flow_comm : ∀ (t : ℝ) (ψ : H), J (flow.U t ψ) = flow.U t (J ψ)

variable {M}
variable (md : ModularData H M)

/-- The modular unitary `Δ^{it}` (notation for the flow). -/
noncomputable abbrev modularUnitary (t : ℝ) : H →L[ℂ] H := md.flow.U t

/-- `Δ^{i(s+t)} = Δ^{is}·Δ^{it}`. -/
lemma modularUnitary_group_law (s t : ℝ) :
    modularUnitary md (s + t) = modularUnitary md s * modularUnitary md t :=
  (U_mul md.flow s t).symm

/-- `Δ^{i·0} = 1`. -/
lemma modularUnitary_zero : modularUnitary md 0 = 1 := U_zero md.flow

/-- `(Δ^{it})† = Δ^{−it}`. -/
lemma modularUnitary_adjoint (t : ℝ) :
    ContinuousLinearMap.adjoint (modularUnitary md t) = modularUnitary md (-t) :=
  (inverse_eq_adjoint md.flow t).symm

/-!
### The modular automorphism group

`σ_t(a) = Δ^{it} a Δ^{−it}`.  Every algebraic identity below is closed by the
cancellation `simp` set `[mul_assoc, U_neg_mul_cancel]` after expanding the group
laws — the telescoping that took explicit `calc` blocks in the old file.
-/

/-- The modular automorphism `σ_t(a) = Δ^{it} a Δ^{−it}`. -/
noncomputable def modularAutomorphism (t : ℝ) (a : H →L[ℂ] H) : H →L[ℂ] H :=
  md.flow.U t * a * md.flow.U (-t)

/-- `σ₀ = id`. -/
lemma modularAutomorphism_zero (a : H →L[ℂ] H) :
    modularAutomorphism md 0 a = a := by
  simp only [modularAutomorphism, neg_zero, U_zero, one_mul, mul_one]

/-- `σ_{s+t} = σ_s ∘ σ_t`. -/
lemma modularAutomorphism_group_law (s t : ℝ) (a : H →L[ℂ] H) :
    modularAutomorphism md (s + t) a
      = modularAutomorphism md s (modularAutomorphism md t a) := by
  simp only [modularAutomorphism]
  rw [← U_mul md.flow s t, show -(s + t) = -t + -s from by ring,
    ← U_mul md.flow (-t) (-s)]
  simp only [mul_assoc]

/-- `σ_{−t} ∘ σ_t = id`. -/
lemma modularAutomorphism_neg_comp (t : ℝ) (a : H →L[ℂ] H) :
    modularAutomorphism md (-t) (modularAutomorphism md t a) = a := by
  rw [← modularAutomorphism_group_law, neg_add_cancel, modularAutomorphism_zero]

/-- `σ_t` is multiplicative: `σ_t(ab) = σ_t(a)·σ_t(b)`. -/
lemma modularAutomorphism_mul (t : ℝ) (a b : H →L[ℂ] H) :
    modularAutomorphism md t (a * b)
      = modularAutomorphism md t a * modularAutomorphism md t b := by
  simp only [modularAutomorphism, mul_assoc, U_neg_mul_cancel]

/-- `σ_t` is a `*`-map: `σ_t(a†) = σ_t(a)†`. -/
lemma modularAutomorphism_star (t : ℝ) (a : H →L[ℂ] H) :
    modularAutomorphism md t (ContinuousLinearMap.adjoint a)
      = ContinuousLinearMap.adjoint (modularAutomorphism md t a) := by
  simp only [modularAutomorphism]
  rw [adjoint_mul, adjoint_mul, ← inverse_eq_adjoint md.flow t,
    ← inverse_eq_adjoint md.flow (-t), neg_neg, mul_assoc]

/-- `t ↦ σ_t(a)ψ` is continuous — joint strong continuity of the conjugated flow.
(Absent from the old file; needed for the cocycle to be a `ModularCocycle`.) -/
lemma modularAutomorphism_strongly_continuous (a : H →L[ℂ] H) (ψ : H) :
    Continuous fun t => modularAutomorphism md t a ψ := by
  have hf : Continuous fun t : ℝ => a (md.flow.U (-t) ψ) := by
    apply a.continuous.comp
    exact (md.flow.strong_continuous ψ).comp continuous_neg
  have h := continuous_U_apply md.flow hf
  have heq : (fun t => md.flow.U t (a (md.flow.U (-t) ψ)))
      = fun t => modularAutomorphism md t a ψ := by
    funext t
    simp [modularAutomorphism, ContinuousLinearMap.mul_apply]
  rw [← heq]
  exact h

/-!
## Section 5: Tomita's theorem

The two deep inclusions, as a `Prop`-valued bundle over the modular data.
`σ_t(M) = M` (equality) is derived; `JMJ = M'` (equality) needs the reverse
inclusion through the double-commutant theorem and is deliberately not assumed.
-/

/-- **Tomita's theorem**: `JMJ ⊆ M'` and `Δ^{it} M Δ^{−it} ⊆ M`.
(Takesaki, *Theory of Operator Algebras I*, Ch. VI.) -/
structure TomitaTheorem (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : VNAlgebraWithVector H) (md : ModularData H M) : Prop where
  /-- `JMJ ⊆ M'`: conjugation by `J` lands in the commutant. -/
  conjugation_mem : ∀ a ∈ M.algebra,
    Conjugation.conjAd md.J a ∈ commutant (M.algebra : Set (H →L[ℂ] H))
  /-- `σ_t(M) ⊆ M` for every `t`. -/
  automorphism_mem : ∀ (t : ℝ), ∀ a ∈ M.algebra, modularAutomorphism md t a ∈ M.algebra

/-- The inclusion for all `t` upgrades itself to an equality:
`σ_t(a) ∈ M ↔ a ∈ M` (apply `σ_{−t}` and telescope). -/
lemma modularAutomorphism_mem_iff (hTT : TomitaTheorem H M md) (t : ℝ)
    (a : H →L[ℂ] H) :
    modularAutomorphism md t a ∈ M.algebra ↔ a ∈ M.algebra := by
  constructor
  · intro h
    have h2 := hTT.automorphism_mem (-t) _ h
    rwa [modularAutomorphism_neg_comp] at h2
  · exact hTT.automorphism_mem t a

/-!
## Section 6: The vacuum state

`ω(a) = ⟪Ω, aΩ⟫`.  Normalization, positivity, faithfulness (from separability),
and σ-invariance (from `Δ^{it}Ω = Ω`) are all theorems.
-/

/-- The vacuum (vector) state `ω(a) = ⟪Ω, aΩ⟫`. -/
noncomputable def vacuumState (M : VNAlgebraWithVector H) (a : H →L[ℂ] H) : ℂ :=
  ⟪M.Ω, a M.Ω⟫_ℂ

/-- Normalization: `ω(1) = 1`. -/
lemma vacuumState_one : vacuumState M 1 = 1 := by
  simp only [vacuumState, ContinuousLinearMap.one_apply]
  rw [inner_self_eq_norm_sq_to_K, M.Ω_norm]
  norm_num

/-- Positivity, quantitatively: `ω(a†a) = ‖aΩ‖²`. -/
lemma vacuumState_star_mul_self (a : H →L[ℂ] H) :
    vacuumState M (ContinuousLinearMap.adjoint a * a) = (‖a M.Ω‖ : ℂ) ^ 2 := by
  simp only [vacuumState, ContinuousLinearMap.mul_apply]
  simp [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]


/-- **Faithfulness on `M`** (from Ω separating): `ω(a†a) = 0 ⟹ a = 0`. -/
lemma vacuumState_faithful (a : H →L[ℂ] H) (ha : a ∈ M.algebra)
    (h : vacuumState M (ContinuousLinearMap.adjoint a * a) = 0) : a = 0 := by
  rw [vacuumState_star_mul_self] at h
  have h2 : (‖a M.Ω‖ : ℂ) = 0 := (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp h
  have h3 : a M.Ω = 0 := by
    rw [← norm_eq_zero]
    exact_mod_cast h2
  exact M.separating a ha h3

/-- **σ-invariance of the vacuum state**: `ω(σ_t(a)) = ω(a)`, from `Δ^{it}Ω = Ω`. -/
lemma vacuumState_modular_invariant (t : ℝ) (a : H →L[ℂ] H) :
    vacuumState M (modularAutomorphism md t a) = vacuumState M a := by
  simp only [vacuumState, modularAutomorphism]
  calc ⟪M.Ω, (md.flow.U t * a * md.flow.U (-t)) M.Ω⟫_ℂ
      = ⟪M.Ω, md.flow.U t (a M.Ω)⟫_ℂ := by
        simp [ContinuousLinearMap.mul_apply, md.flow_fixes_vacuum (-t)]
    _ = ⟪ContinuousLinearMap.adjoint (md.flow.U t) M.Ω, a M.Ω⟫_ℂ := by
        rw [ContinuousLinearMap.adjoint_inner_left]
    _ = ⟪md.flow.U (-t) M.Ω, a M.Ω⟫_ℂ := by
        rw [← inverse_eq_adjoint md.flow t]
    _ = ⟪M.Ω, a M.Ω⟫_ℂ := by rw [md.flow_fixes_vacuum (-t)]

/-!
## Section 7: The modular Hamiltonian

The generator of the modular flow is `K = log Δ` — Stone's construction gives it
as an honest `LinearPMap`, symmetric by `generator_isFormalAdjoint`.  The vacuum
lies in its domain and is annihilated: `KΩ = 0`, the infinitesimal form of
`Δ^{it}Ω = Ω`.  This is the "modular Hamiltonian" of the physics literature; the
thermal interpretation (KMS at inverse temperature 1) is the PeriodicStrip story.
-/

/-- The modular Hamiltonian `K = log Δ`, the constructed generator of the flow. -/
noncomputable abbrev modularHamiltonian : H →ₗ.[ℂ] H := generator md.flow

/-- The vacuum is in the domain of `log Δ`: its difference quotients vanish
identically since `Δ^{it}Ω = Ω`. -/
lemma vacuum_mem_modularHamiltonian_domain : M.Ω ∈ generatorDomain md.flow := by
  refine mem_generatorDomain.mpr ⟨0, ?_⟩
  have hfun : genDiffQuot md.flow M.Ω = fun _ => (0 : H) := by
    funext t
    simp [genDiffQuot_apply, md.flow_fixes_vacuum t]
  rw [hfun]
  exact tendsto_const_nhds

/-- **The modular Hamiltonian annihilates the vacuum**: `KΩ = (log Δ)Ω = 0`. -/
lemma modularHamiltonian_vacuum :
    generator md.flow ⟨M.Ω, vacuum_mem_modularHamiltonian_domain md⟩ = 0 := by
  have hfun : genDiffQuot md.flow M.Ω = fun _ => (0 : H) := by
    funext t
    simp [genDiffQuot_apply, md.flow_fixes_vacuum t]
  refine tendsto_nhds_unique
    (generator_tendsto md.flow ⟨M.Ω, vacuum_mem_modularHamiltonian_domain md⟩) ?_
  rw [hfun]
  exact tendsto_const_nhds

end Spectra.QuantumMechanics.ModularTheory
