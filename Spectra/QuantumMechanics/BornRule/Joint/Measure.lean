/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.BornRule.Joint.Basic
/-!
# Joint spectral measures — the per-state joint measure `μ_ξ` (Carathéodory extension)

This file builds the genuine per-state joint measure `μ_ξ` on `ℝ²` (G2.2) for a strongly-commuting
pair, by Carathéodory extension of the rectangle content `m(S × T) = ‖E_A(S)E_B(T)ξ‖²` along the
rectangle semiring `jointRectangles` (`Joint.Basic`).  The crux is finite additivity of the content
over an *arbitrary* disjoint rectangle partition of a rectangle (`AddContent.sUnion'`), which by
Pythagoras reduces to **vector completeness** `∑ₖ E_A(Sₖ)E_B(Tₖ)ξ = E_A(S)E_B(T)ξ` (a grid/atom
refinement via `Spectra.AxisGrid`).  Compact inner regularity (Alexandrov) then discharges
∅-continuity, the multivariate spectral theorem's measure-theoretic core, and Carathéodory produces
the finite Borel measure `jointScalarMeasure`.  The whole development is `sorry`-free and
axiom-clean.

## Main definitions

* `jointRectVal` — the `ℝ≥0∞`-valued rectangle content value `ENNReal.ofReal (‖E_A(S)E_B(T)ξ‖²)`.
* `jointContent` — that content packaged as a `MeasureTheory.AddContent` on `jointRectangles`.
* `rectVec`, `jointVectorContent` — the effect vector `E_A(S)E_B(T)ξ` attached to a rectangle, and
  the partition-independent sum over a disjoint rectangle cover of an elementary set.
* `jointScalarMeasure` — the per-state joint measure `μ_ξ`, the Carathéodory extension of
  `jointContent`.

## Main statements

* `jointVectorContent_eq` — partition independence of the vector content, the crux reduction for the
  finite additivity of `jointContent`.
* `jointContentRing_tendsto_empty` — ∅-continuity of the ring content (Route T / tightness), the
  multivariate spectral theorem's core estimate; proved via compact inner regularity and a
  finite-intersection-property argument.
* `jointContent_isSigmaSubadditive` — σ-subadditivity of the rectangle content, the Carathéodory
  input.
* `jointScalarMeasure_prod` — `μ_ξ(S ×ˢ T) = μ^A_{E_B(T)ξ}(S)`, the bimeasure value on rectangles.
* `jointScalarMeasure_isFiniteMeasure` — `μ_ξ` is a finite measure, with total mass `‖ξ‖²`.

## Implementation notes

The finite-additivity obligation `AddContent.sUnion'` is reduced by Pythagoras to the vector
identity `jointVector_sUnion`, proved by refining both axes over a common Boolean sign-atom grid
(`Spectra.AxisGrid.signAtom`) and multiplicity counting, rather than by induction.  ∅-continuity is
not recoverable from the marginal data alone; it is discharged by Route T (tightness / Alexandrov),
where the approximation *defect* — but not the mass — is marginal-controlled through
`jointRect_diff_defect_le`, the one place the commuting-projection structure genuinely enters.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*], §VIII.5 (strong commutativity and the
  multivariate spectral theorem).
* [Reed, Simon, *Methods of Modern Mathematical Physics IV*] (joint spectral measures).
* [Cohn, *Measure Theory*], Ch. 1 (Carathéodory extension from a semiring; the Alexandrov / compact
  inner regularity ∅-continuity argument).
-/

open MeasureTheory Complex Spectra Filter Topology
open scoped InnerProductSpace
open Spectra.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.QuantumMechanics.BornRule

open PVM Spectra.ProjValMeasure Spectra.AxisGrid

/-! ## G2.2 — the per-state joint measure `μ_ξ` (the bimeasure → measure extension)

The rectangle content `m(S × T) = ‖E_A(S)E_B(T)ξ‖²` is extended to a genuine finite measure on the
Borel sets of `ℝ²` by Carathéodory on the rectangle semiring (`isSetSemiring_jointRectangles`).  The
crux is finite additivity of the content over an *arbitrary* disjoint rectangle partition of a
rectangle (`AddContent.sUnion'`), which by Pythagoras reduces to the **vector completeness**
`∑ₖ E_A(Sₖ)E_B(Tₖ)ξ = E_A(S)E_B(T)ξ` (a grid/atom refinement). -/

/-- **Generalized orthogonality.**  For two *disjoint rectangles* `S₁×T₁` and `S₂×T₂`, the vectors
`E_A(S₁)E_B(T₁)ξ` and `E_A(S₂)E_B(T₂)ξ` are orthogonal.  Disjointness of the rectangles means
`(S₁∩S₂)×(T₁∩T₂) = ∅`, i.e. `S₁∩S₂ = ∅` or `T₁∩T₂ = ∅`; either way the product effect
`E_A(S₁∩S₂)E_B(T₁∩T₂)` (= `(E_A(S₁)E_B(T₁))·(E_A(S₂)E_B(T₂))` by `jointRect_mul`) vanishes, and a
self-adjoint move (`jointRect_isStarProjection`) reads off the inner product.  This generalizes
`jointRect_orthogonal` (the same-`S` case) and is the Pythagoras input for the grid additivity. -/
theorem jointRect_orthogonal_general (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) {S₁ S₂ T₁ T₂ : Set ℝ}
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂)
    (hT₁ : MeasurableSet T₁) (hT₂ : MeasurableSet T₂)
    (hd : Disjoint (S₁ ×ˢ T₁) (S₂ ×ˢ T₂)) (ξ : H) :
    ⟪(A.spectralPVM.proj S₁ hS₁ * B.spectralPVM.proj T₁ hT₁) ξ,
      (A.spectralPVM.proj S₂ hS₂ * B.spectralPVM.proj T₂ hT₂) ξ⟫_ℂ = 0 := by
  have hsa : IsSelfAdjoint (A.spectralPVM.proj S₁ hS₁ * B.spectralPVM.proj T₁ hT₁) :=
    (jointRect_isStarProjection A B hSC hS₁ hT₁).isSelfAdjoint
  -- the product effect of two disjoint rectangles annihilates every vector
  have hzero : (A.spectralPVM.proj S₁ hS₁ * B.spectralPVM.proj T₁ hT₁)
      ((A.spectralPVM.proj S₂ hS₂ * B.spectralPVM.proj T₂ hT₂) ξ) = 0 := by
    rw [← ContinuousLinearMap.mul_apply, jointRect_mul A B hSC hS₁ hS₂ hT₁ hT₂]
    have hcap : (S₁ ∩ S₂) ×ˢ (T₁ ∩ T₂) = (∅ : Set (ℝ × ℝ)) := by
      rw [← Set.prod_inter_prod]; exact Set.disjoint_iff_inter_eq_empty.mp hd
    rcases Set.prod_eq_empty_iff.mp hcap with hSe | hTe
    · rw [A.spectralPVM.proj_congr hSe (hS₁.inter hS₂) MeasurableSet.empty,
        A.spectralPVM.proj_empty]; simp
    · rw [B.spectralPVM.proj_congr hTe (hT₁.inter hT₂) MeasurableSet.empty,
        B.spectralPVM.proj_empty]; simp
  -- move the self-adjoint left factor across the inner product and read off the annihilation
  rw [← hsa.adjoint_eq, ContinuousLinearMap.adjoint_inner_left, hzero, inner_zero_right]

/-- **The grid collapse (vector completeness).**  If a `Fintype`-indexed family `σ` of pairwise
disjoint measurable sets exhausts `S₀`, and likewise `τ` exhausts `T₀`, then the rectangle-effect
vectors over the product grid sum to the whole-rectangle effect:
`∑_{(a,b)} E_A(σ a)E_B(τ b)ξ = E_A(S₀)E_B(T₀)ξ`.  Pure finite additivity of each PVM
(`proj_biUnion`) plus bilinearity of the operator product — no orthogonality, no induction. -/
theorem jointVector_grid_collapse (A B : Spectra.Operator.SelfAdjointOperator H)
    {α β : Type*} [Fintype α] [Fintype β] (σ : α → Set ℝ) (τ : β → Set ℝ)
    (hσ : ∀ a, MeasurableSet (σ a)) (hτ : ∀ b, MeasurableSet (τ b))
    {S₀ T₀ : Set ℝ} (hS₀ : MeasurableSet S₀) (hT₀ : MeasurableSet T₀)
    (hσd : Pairwise (Function.onFun Disjoint σ)) (hτd : Pairwise (Function.onFun Disjoint τ))
    (hσsup : ⋃ a, σ a = S₀) (hτsup : ⋃ b, τ b = T₀) (ξ : H) :
    ∑ p : α × β,
        (A.spectralPVM.proj (σ p.1) (hσ p.1) * B.spectralPVM.proj (τ p.2) (hτ p.2)) ξ
      = (A.spectralPVM.proj S₀ hS₀ * B.spectralPVM.proj T₀ hT₀) ξ := by
  classical
  have hSproj : A.spectralPVM.proj S₀ hS₀ = ∑ a, A.spectralPVM.proj (σ a) (hσ a) := by
    have hbu : (⋃ a ∈ (Finset.univ : Finset α), σ a) = S₀ := by simpa using hσsup
    have hU : MeasurableSet (⋃ a ∈ (Finset.univ : Finset α), σ a) :=
      Finset.measurableSet_biUnion _ fun a _ => hσ a
    rw [← A.spectralPVM.proj_congr hbu hU hS₀,
      A.spectralPVM.proj_biUnion hσ Finset.univ (fun a _ b _ hab => hσd hab) hU]
  have hTproj : B.spectralPVM.proj T₀ hT₀ = ∑ b, B.spectralPVM.proj (τ b) (hτ b) := by
    have hbu : (⋃ b ∈ (Finset.univ : Finset β), τ b) = T₀ := by simpa using hτsup
    have hU : MeasurableSet (⋃ b ∈ (Finset.univ : Finset β), τ b) :=
      Finset.measurableSet_biUnion _ fun b _ => hτ b
    rw [← B.spectralPVM.proj_congr hbu hU hT₀,
      B.spectralPVM.proj_biUnion hτ Finset.univ (fun b _ c _ hbc => hτd hbc) hU]
  rw [hSproj, hTproj, Finset.sum_mul_sum, Fintype.sum_prod_type]
  simp only [ContinuousLinearMap.sum_apply]

/-- **Grid-cell orthogonality.**  Distinct cells of the product grid give orthogonal effect vectors
— immediate from `jointRect_orthogonal_general`, since distinct cells differ in some axis atom, and
distinct atoms are disjoint, so the rectangles are disjoint. -/
theorem jointGridCell_orthogonal (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) {α β : Type*}
    (σ : α → Set ℝ) (τ : β → Set ℝ)
    (hσ : ∀ a, MeasurableSet (σ a)) (hτ : ∀ b, MeasurableSet (τ b))
    (hσd : Pairwise (Function.onFun Disjoint σ)) (hτd : Pairwise (Function.onFun Disjoint τ))
    (ξ : H) (p q : α × β) (hpq : p ≠ q) :
    ⟪(A.spectralPVM.proj (σ p.1) (hσ p.1) * B.spectralPVM.proj (τ p.2) (hτ p.2)) ξ,
      (A.spectralPVM.proj (σ q.1) (hσ q.1) * B.spectralPVM.proj (τ q.2) (hτ q.2)) ξ⟫_ℂ = 0 := by
  have hd : Disjoint (σ p.1 ×ˢ τ p.2) (σ q.1 ×ˢ τ q.2) := by
    rw [Set.disjoint_prod]
    rcases not_and_or.mp (fun h => hpq (Prod.ext_iff.mpr h)) with h1 | h2
    · exact Or.inl (hσd h1)
    · exact Or.inr (hτd h2)
  exact jointRect_orthogonal_general A B hSC (hσ p.1) (hσ q.1) (hτ p.2) (hτ q.2) hd ξ

/-- **Vector completeness via multiplicity counting.**  If a `Fintype`-indexed family of measurable
rectangles `Sp k ×ˢ Tp k` is pairwise disjoint and covers `S₀ ×ˢ T₀`, then the rectangle-effect
vectors sum to the whole-rectangle effect: `∑ₖ E_A(Sp k)E_B(Tp k)ξ = E_A(S₀)E_B(T₀)ξ`.  Proof:
refine both axes over the *common* sign-atom grid of the augmented family `Sfam, Tfam` indexed by
`Option κ` (the extra index `none` carries `S₀, T₀`).  Each side becomes a double sum over sign
vectors with a `ℕ`-multiplicity coefficient; pointwise, a nonzero atom cell witnesses a point lying
in exactly one cover rectangle (`card_filter_mem_eq_ite` + `hcover`), matching the multiplicity `1`
the whole rectangle assigns.  This is the grid/atom refinement feeding the `AddContent.sUnion'`
finite additivity (G2.2). -/
theorem jointVector_sUnion (A B : Spectra.Operator.SelfAdjointOperator H)
    {κ : Type*} [Fintype κ] (Sp Tp : κ → Set ℝ)
    (hSp : ∀ k, MeasurableSet (Sp k)) (hTp : ∀ k, MeasurableSet (Tp k))
    {S₀ T₀ : Set ℝ} (hS₀ : MeasurableSet S₀) (hT₀ : MeasurableSet T₀)
    (hdisj : Pairwise (Function.onFun Disjoint (fun k => Sp k ×ˢ Tp k)))
    (hcover : ⋃ k, Sp k ×ˢ Tp k = S₀ ×ˢ T₀) (ξ : H) :
    ∑ k, (A.spectralPVM.proj (Sp k) (hSp k) * B.spectralPVM.proj (Tp k) (hTp k)) ξ
      = (A.spectralPVM.proj S₀ hS₀ * B.spectralPVM.proj T₀ hT₀) ξ := by
  classical
  -- Augmented axis families over `Option κ`: index `none` carries `S₀, T₀`.
  set Sfam : Option κ → Set ℝ := fun o => o.elim S₀ Sp with _hSfam_def
  set Tfam : Option κ → Set ℝ := fun o => o.elim T₀ Tp with _hTfam_def
  have hSfam : ∀ o, MeasurableSet (Sfam o) := by
    rintro (_ | k)
    · exact hS₀
    · exact hSp k
  have hTfam : ∀ o, MeasurableSet (Tfam o) := by
    rintro (_ | k)
    · exact hT₀
    · exact hTp k
  -- the building block: an atom-pair effect vector
  set g : (Option κ → Bool) → (Option κ → Bool) → H :=
    fun u v => (A.spectralPVM.proj (signAtom Sfam u) (signAtom_measurableSet hSfam u)
      * B.spectralPVM.proj (signAtom Tfam v) (signAtom_measurableSet hTfam v)) ξ with hg_def
  -- expand a rectangle effect `(E_A(Sfam i) * E_B(Tfam i)) ξ` over the common grid
  have hcell : ∀ i : Option κ,
      (A.spectralPVM.proj (Sfam i) (hSfam i) * B.spectralPVM.proj (Tfam i) (hTfam i)) ξ
        = ∑ u ∈ Finset.univ.filter (fun u : Option κ → Bool => u i = true),
            ∑ v ∈ Finset.univ.filter (fun v : Option κ → Bool => v i = true), g u v := by
    intro i
    rw [proj_eq_sum_signAtom A.spectralPVM hSfam i (hSfam i),
      proj_eq_sum_signAtom B.spectralPVM hTfam i (hTfam i), Finset.sum_mul_sum]
    simp only [ContinuousLinearMap.sum_apply, hg_def]
  -- RHS: `(E_A(S₀) * E_B(T₀)) ξ = (E_A(Sfam none) * E_B(Tfam none)) ξ`
  have hRHS : (A.spectralPVM.proj S₀ hS₀ * B.spectralPVM.proj T₀ hT₀) ξ
      = ∑ u ∈ Finset.univ.filter (fun u : Option κ → Bool => u none = true),
          ∑ v ∈ Finset.univ.filter (fun v : Option κ → Bool => v none = true), g u v := by
    rw [A.spectralPVM.proj_congr (rfl : S₀ = Sfam none) hS₀ (hSfam none),
      B.spectralPVM.proj_congr (rfl : T₀ = Tfam none) hT₀ (hTfam none)]
    exact hcell none
  -- LHS: `∑ k, (E_A(Sp k) * E_B(Tp k)) ξ = ∑ k, (E_A(Sfam (some k)) * E_B(Tfam (some k))) ξ`
  have hLHS : ∑ k, (A.spectralPVM.proj (Sp k) (hSp k) * B.spectralPVM.proj (Tp k) (hTp k)) ξ
      = ∑ k, ∑ u ∈ Finset.univ.filter (fun u : Option κ → Bool => u (some k) = true),
          ∑ v ∈ Finset.univ.filter (fun v : Option κ → Bool => v (some k) = true), g u v := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [A.spectralPVM.proj_congr (rfl : Sp k = Sfam (some k)) (hSp k) (hSfam (some k)),
      B.spectralPVM.proj_congr (rfl : Tp k = Tfam (some k)) (hTp k) (hTfam (some k))]
    exact hcell (some k)
  rw [hLHS, hRHS]
  -- Convert filtered sums to full `univ` sums with `if`-coefficients, and collapse the nested
  -- `if`s into a single conjunction-condition (so everything is `∑ ... if P then g u v else 0`).
  have hcollapse : ∀ i : Option κ,
      (∑ u ∈ Finset.univ.filter (fun u : Option κ → Bool => u i = true),
        ∑ v ∈ Finset.univ.filter (fun v : Option κ → Bool => v i = true), g u v)
      = ∑ u, ∑ v, if (u i = true ∧ v i = true) then g u v else 0 := by
    intro i
    simp only [Finset.sum_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h1 : u i = true
    · rw [if_pos h1]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases h2 : v i = true <;> simp [h1, h2]
    · rw [if_neg h1]
      symm
      refine (Finset.sum_congr rfl fun v _ => ?_).trans Finset.sum_const_zero
      rw [if_neg (fun h => h1 h.1)]
  rw [hcollapse none]
  simp only [hcollapse (some _)]
  -- reorder `∑ k` innermost: `∑ k, ∑ u, ∑ v, F` → `∑ u, ∑ v, ∑ k, F`.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  -- Goal: ∑ k, (if (u (some k) ∧ v (some k)) then g u v else 0)
  --        = if (u none ∧ v none) then g u v else 0
  -- ∑ k, (if P k then c else 0) = (filter P univ).card • c, with `c = g u v` constant in k.
  rw [← Finset.sum_filter, Finset.sum_const]
  -- Pointwise scalar equality suffices, then dispatch the two `if`s.
  by_cases hg0 : g u v = 0
  · rw [hg0, smul_zero]; simp
  · -- `g u v ≠ 0` forces both atom cells to be nonempty.
    have hSne : (signAtom Sfam u).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]; intro he
      apply hg0
      simp only [hg_def]
      rw [A.spectralPVM.proj_congr he (signAtom_measurableSet hSfam u) MeasurableSet.empty,
        A.spectralPVM.proj_empty]
      simp
    have hTne : (signAtom Tfam v).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]; intro he
      apply hg0
      simp only [hg_def]
      rw [B.spectralPVM.proj_congr he (signAtom_measurableSet hTfam v) MeasurableSet.empty,
        B.spectralPVM.proj_empty]
      simp
    obtain ⟨a, ha⟩ := hSne
    obtain ⟨b, hb⟩ := hTne
    rw [mem_signAtom] at ha hb
    -- the per-k predicate equals membership of `(a,b)` in the `k`-th rectangle
    have hfilt : (Finset.univ.filter
          (fun k => u (some k) = true ∧ v (some k) = true))
        = (Finset.univ.filter (fun k => (a, b) ∈ Sp k ×ˢ Tp k)) := by
      refine Finset.filter_congr fun k _ => ?_
      have h1 : u (some k) = true ↔ a ∈ Sp k := ha (some k)
      have h2 : v (some k) = true ↔ b ∈ Tp k := hb (some k)
      rw [Set.mem_prod]
      exact ⟨fun ⟨p, q⟩ => ⟨h1.mp p, h2.mp q⟩, fun ⟨p, q⟩ => ⟨h1.mpr p, h2.mpr q⟩⟩
    have hcard : (Finset.univ.filter (fun k => (a, b) ∈ Sp k ×ˢ Tp k)).card
        = if (a, b) ∈ S₀ ×ˢ T₀ then 1 else 0 := by
      have := card_filter_mem_eq_ite (fun k => Sp k ×ˢ Tp k) hdisj (a, b)
      rw [hcover] at this
      convert this using 3
    rw [hfilt, hcard]
    -- now match the `if (a,b) ∈ S₀ ×ˢ T₀` count against `if (u none ∧ v none)`
    have hcond : ((a, b) ∈ S₀ ×ˢ T₀) ↔ (u none = true ∧ v none = true) := by
      have h1 : u none = true ↔ a ∈ S₀ := ha none
      have h2 : v none = true ↔ b ∈ T₀ := hb none
      rw [Set.mem_prod]
      exact ⟨fun ⟨p, q⟩ => ⟨h1.mpr p, h2.mpr q⟩, fun ⟨p, q⟩ => ⟨h1.mp p, h2.mp q⟩⟩
    by_cases hc : (a, b) ∈ S₀ ×ˢ T₀
    · rw [if_pos hc, if_pos (hcond.mp hc), one_smul]
    · rw [if_neg hc, if_neg (fun h => hc (hcond.mpr h)), zero_smul]

/-- **The norm-squared payload.**  Pairing vector completeness (`jointVector_sUnion`) with grid
orthogonality: over a disjoint rectangle cover of `S₀ ×ˢ T₀`, the whole-rectangle effect's squared
norm splits as the sum of the cell effects' squared norms.  This is the Pythagoras identity the
`AddContent.sUnion'` finite-additivity obligation (G2.2) consumes. -/
theorem jointRect_sUnion_norm_sq (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) {κ : Type*} [Fintype κ] (Sp Tp : κ → Set ℝ)
    (hSp : ∀ k, MeasurableSet (Sp k)) (hTp : ∀ k, MeasurableSet (Tp k))
    {S₀ T₀ : Set ℝ} (hS₀ : MeasurableSet S₀) (hT₀ : MeasurableSet T₀)
    (hdisj : Pairwise (Function.onFun Disjoint (fun k => Sp k ×ˢ Tp k)))
    (hcover : ⋃ k, Sp k ×ˢ Tp k = S₀ ×ˢ T₀) (ξ : H) :
    ‖(A.spectralPVM.proj S₀ hS₀ * B.spectralPVM.proj T₀ hT₀) ξ‖ ^ 2
      = ∑ k, ‖(A.spectralPVM.proj (Sp k) (hSp k) * B.spectralPVM.proj (Tp k) (hTp k)) ξ‖ ^ 2 := by
  rw [← jointVector_sUnion A B Sp Tp hSp hTp hS₀ hT₀ hdisj hcover ξ]
  refine norm_sum_sq_orthogonal Finset.univ
    (fun k => (A.spectralPVM.proj (Sp k) (hSp k) * B.spectralPVM.proj (Tp k) (hTp k)) ξ)
    (fun i _ j _ hij => ?_)
  exact jointRect_orthogonal_general A B hSC (hSp i) (hSp j) (hTp i) (hTp j) (hdisj hij) ξ

/-! ## G2.2 — the joint rectangle content as a `MeasureTheory.AddContent`

The nonnegative rectangle content `m(S ×ˢ T) = ‖E_A(S)E_B(T)ξ‖²` (in `ℝ≥0∞`) is packaged as a
`MeasureTheory.AddContent` on the rectangle semiring `jointRectangles`.  Its `empty'` is immediate
(`E_A(∅) = 0`); its `sUnion'` finite-additivity obligation is discharged by the Pythagoras payload
`jointRect_sUnion_norm_sq` (vector completeness + grid orthogonality) lifted to `ℝ≥0∞`.  This is the
content the Carathéodory extension (`AddContent.measure`) consumes to build `μ_ξ`. -/

/-- **The `ℝ≥0∞`-valued rectangle content value.**  On a rectangle `R = S ×ˢ T` it is
`ENNReal.ofReal (‖E_A(S)E_B(T)ξ‖²)`; off the rectangle semiring it is `0`.  Defined as an `⨆` over
all rectangle representations of `R`; representation independence (proved in `jointRectVal_prod`)
makes the supremum collapse to the common value, and the empty index set gives `0` for
non-rectangles. -/
noncomputable def jointRectVal (A B : Spectra.Operator.SelfAdjointOperator H) (ξ : H)
    (R : Set (ℝ × ℝ)) : ENNReal :=
  ⨆ (S : Set ℝ) (T : Set ℝ) (hS : MeasurableSet S) (hT : MeasurableSet T) (_ : R = S ×ˢ T),
    ENNReal.ofReal (‖(A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ‖ ^ 2)

/-- **Representation independence.**  Two presentations `S ×ˢ T = S' ×ˢ T'` of the same rectangle
give the same content value.  If the factors agree it is `proj_congr`; if some factor is empty then
both products carry an `E(∅) = 0` factor and both values are `ENNReal.ofReal 0 = 0`. -/
theorem jointRectVal_aux_indep (A B : Spectra.Operator.SelfAdjointOperator H) (ξ : H)
    {S T S' T' : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hS' : MeasurableSet S') (hT' : MeasurableSet T') (heq : S ×ˢ T = S' ×ˢ T') :
    ENNReal.ofReal (‖(A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ‖ ^ 2)
      = ENNReal.ofReal (‖(A.spectralPVM.proj S' hS' * B.spectralPVM.proj T' hT') ξ‖ ^ 2) := by
  -- an empty factor makes the rectangle effect annihilate `ξ`, so the value is `0`
  have hzero : ∀ {U V : Set ℝ} (hU : MeasurableSet U) (hV : MeasurableSet V),
      U = ∅ ∨ V = ∅ →
      ENNReal.ofReal (‖(A.spectralPVM.proj U hU * B.spectralPVM.proj V hV) ξ‖ ^ 2) = 0 := by
    rintro U V hU hV (hUe | hVe)
    · rw [ContinuousLinearMap.mul_apply,
        A.spectralPVM.proj_congr hUe hU MeasurableSet.empty, A.spectralPVM.proj_empty]
      simp
    · rw [ContinuousLinearMap.mul_apply,
        B.spectralPVM.proj_congr hVe hV MeasurableSet.empty, B.spectralPVM.proj_empty,
        ContinuousLinearMap.zero_apply, map_zero]
      simp
  rcases Set.prod_eq_prod_iff.mp heq with ⟨rfl, rfl⟩ | ⟨he, he'⟩
  · rw [A.spectralPVM.proj_congr rfl hS hS', B.spectralPVM.proj_congr rfl hT hT']
  · rw [hzero hS hT he, hzero hS' hT' he']

/-- **The content value on a rectangle.**  `jointRectVal A B ξ (S ×ˢ T) = ENNReal.ofReal
(‖E_A(S)E_B(T)ξ‖²)`.  The defining `⨆` collapses to the single common value by representation
independence (`jointRectVal_aux_indep`). -/
theorem jointRectVal_prod (A B : Spectra.Operator.SelfAdjointOperator H) (ξ : H)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    jointRectVal A B ξ (S ×ˢ T)
      = ENNReal.ofReal (‖(A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ‖ ^ 2) := by
  apply le_antisymm
  · -- every term of the `⨆` equals the target value (representation independence)
    refine iSup_le fun S' => iSup_le fun T' => iSup_le fun hS' => iSup_le fun hT' =>
      iSup_le fun heq => ?_
    rw [jointRectVal_aux_indep A B ξ hS' hT' hS hT heq.symm]
  · -- the `(S, T)` representation is one of the terms
    refine le_iSup_of_le S (le_iSup_of_le T (le_iSup_of_le hS (le_iSup_of_le hT
      (le_iSup_of_le rfl ?_))))
    rw [A.spectralPVM.proj_congr rfl hS hS, B.spectralPVM.proj_congr rfl hT hT]

/-- **The diagonal-measure form of the content value.**  Restating `jointRectVal_prod` through the
content bridge `jointRect_norm_sq_eq_diag`: on a rectangle the content is `μ^A_{E_B(T)ξ}(S)`. -/
theorem jointRectVal_prod_diag (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) (ξ : H) {S T : Set ℝ} (hS : MeasurableSet S)
    (hT : MeasurableSet T) :
    jointRectVal A B ξ (S ×ˢ T)
      = (A.spectralPVM.diag (B.spectralPVM.proj T hT ξ)) S := by
  rw [jointRectVal_prod A B ξ hS hT, jointRect_norm_sq_eq_diag A B hSC hS hT ξ,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **The joint rectangle content as a `MeasureTheory.AddContent`.**  `toFun = jointRectVal`;
`empty'` is `E_A(∅) = 0`; `sUnion'` is the Pythagoras payload `jointRect_sUnion_norm_sq` lifted to
`ℝ≥0∞` via `ENNReal.ofReal_sum_of_nonneg`.  This is the per-state content extended to `μ_ξ`. -/
noncomputable def jointContent (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) (ξ : H) : MeasureTheory.AddContent ENNReal jointRectangles where
  toFun := jointRectVal A B ξ
  empty' := by
    have he : (∅ : Set (ℝ × ℝ)) = (∅ : Set ℝ) ×ˢ (∅ : Set ℝ) := by simp
    rw [he, jointRectVal_prod A B ξ MeasurableSet.empty MeasurableSet.empty,
      ContinuousLinearMap.mul_apply, A.spectralPVM.proj_empty]
    simp
  sUnion' := by
    classical
    intro I h_ss h_dis h_mem
    -- the union is a rectangle `S₀ ×ˢ T₀`
    obtain ⟨S₀, T₀, hS₀, hT₀, hST₀⟩ := h_mem
    -- index `I` by its coercion fintype; each member is a rectangle `Sp R ×ˢ Tp R`
    set κ := {R : Set (ℝ × ℝ) // R ∈ I} with _hκ
    have hmemR : ∀ R : κ, R.1 ∈ jointRectangles := fun R => h_ss R.2
    set Sp : κ → Set ℝ := fun R => (hmemR R).choose with _hSp_def
    set Tp : κ → Set ℝ := fun R => (hmemR R).choose_spec.choose with _hTp_def
    have hSp : ∀ R, MeasurableSet (Sp R) := fun R => (hmemR R).choose_spec.choose_spec.1
    have hTp : ∀ R, MeasurableSet (Tp R) := fun R => (hmemR R).choose_spec.choose_spec.2.1
    have hR : ∀ R : κ, R.1 = Sp R ×ˢ Tp R := fun R => (hmemR R).choose_spec.choose_spec.2.2
    -- pairwise disjointness of the rectangle cells, transported through `hR`
    have hdisj : Pairwise (Function.onFun Disjoint (fun R : κ => Sp R ×ˢ Tp R)) := by
      intro R R' hRR'
      have hne : R.1 ≠ R'.1 := fun h => hRR' (Subtype.ext h)
      have := h_dis R.2 R'.2 hne
      rw [Function.onFun, ← hR R, ← hR R']
      simpa [Function.onFun, id] using this
    -- the cells cover `S₀ ×ˢ T₀`
    have hcover : ⋃ R : κ, Sp R ×ˢ Tp R = S₀ ×ˢ T₀ := by
      rw [← hST₀, Set.sUnion_eq_iUnion]
      exact Set.iUnion_congr fun R => (hR R).symm
    -- the Pythagoras payload
    have hpyth := jointRect_sUnion_norm_sq A B hSC Sp Tp hSp hTp hS₀ hT₀ hdisj hcover ξ
    -- lift to `ℝ≥0∞`
    change jointRectVal A B ξ (⋃₀ ↑I) = ∑ u ∈ I, jointRectVal A B ξ u
    rw [hST₀, jointRectVal_prod A B ξ hS₀ hT₀, hpyth,
      ENNReal.ofReal_sum_of_nonneg (fun R _ => sq_nonneg _)]
    -- `∑ R : κ, ofReal ‖..‖² = ∑ R : κ, jointRectVal R.1 = ∑ u ∈ I, jointRectVal u`
    rw [← Finset.sum_coe_sort I (jointRectVal A B ξ)]
    refine Finset.sum_congr rfl fun R _ => ?_
    rw [(by rw [hR R] : jointRectVal A B ξ R.1 = jointRectVal A B ξ (Sp R ×ˢ Tp R)),
      jointRectVal_prod A B ξ (hSp R) (hTp R)]

/-- **The content never takes the value `∞`.**  On a rectangle the value is `ENNReal.ofReal _`,
which is finite.  (Feeds the local finiteness needed by the Carathéodory extension.) -/
theorem jointContent_ne_top (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) (ξ : H) {R : Set (ℝ × ℝ)} (hR : R ∈ jointRectangles) :
    jointContent A B hSC ξ R ≠ ⊤ := by
  obtain ⟨S, T, hS, hT, rfl⟩ := hR
  change jointRectVal A B ξ (S ×ˢ T) ≠ ⊤
  rw [jointRectVal_prod A B ξ hS hT]
  exact ENNReal.ofReal_ne_top

/-- **Total mass.**  The content of the full plane `univ ×ˢ univ` is `‖ξ‖²`: both factor projections
are the identity (`proj_univ`), so the rectangle effect is the identity and `‖id ξ‖² = ‖ξ‖²`. -/
theorem jointContent_univ (A B : Spectra.Operator.SelfAdjointOperator H) (hSC : StronglyCommute A B)
    (ξ : H) : jointContent A B hSC ξ (Set.univ ×ˢ Set.univ) = ENNReal.ofReal (‖ξ‖ ^ 2) := by
  change jointRectVal A B ξ (Set.univ ×ˢ Set.univ) = ENNReal.ofReal (‖ξ‖ ^ 2)
  rw [jointRectVal_prod A B ξ MeasurableSet.univ MeasurableSet.univ,
    ContinuousLinearMap.mul_apply, A.spectralPVM.proj_univ, B.spectralPVM.proj_univ,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply]

/-! ## G2.2 — the per-state joint scalar measure `μ_ξ` (Carathéodory extension)

The `MeasureTheory.AddContent` `jointContent` (on the rectangle *semiring*) is extended to a genuine
finite Borel measure on `ℝ × ℝ` by Carathéodory (`AddContent.measure`).  This needs σ-subadditivity
of the content, which on a *semiring* follows from σ-additivity on the generated *ring* (the
sup-closure), which in turn (Mathlib's `addContent_iUnion_eq_sum_of_tendsto_zero`) reduces to
**continuity at `∅`** of the ring content.  That ∅-continuity is the one genuine analytic nut of
G2.2 (`jointContentRing_tendsto_empty`); it is discharged here by the tightness / Alexandrov
argument, so the whole development is `sorry`-free. -/

/-- **Finiteness on the sup-closure ring.**  The ring content (the sup-closure of `jointContent`)
never takes the value `⊤`: an element of the sup-closure is a finite disjoint union of rectangles
(`mem_supClosure_iff`), its content is the finite sum of the rectangle values
(`supClosure_apply_finpartition`), and each summand is finite (`jointContent_ne_top`). -/
theorem jointContentRing_ne_top (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) (ξ : H) {s : Set (ℝ × ℝ)} (hs : s ∈ supClosure jointRectangles) :
    (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles s ≠ ⊤ := by
  obtain ⟨P, hP⟩ := (isSetSemiring_jointRectangles.mem_supClosure_iff).mp hs
  rw [(jointContent A B hSC ξ).supClosure_apply_finpartition isSetSemiring_jointRectangles hP]
  rw [ENNReal.sum_ne_top]
  exact fun p hp => jointContent_ne_top A B hSC ξ (hP hp)

/-! ## G2.2 — the partition-independent *vector* content (the ∅-continuity reduction)

The ring content `mR(s) = (jointContent.supClosure) s` is the squared norm of a **vector**
`jointVectorContent ξ s ∈ H`, defined on the elementary sets (finite disjoint unions of rectangles)
and *additive* there.  Concretely, for any disjoint rectangle partition `J` of `s`,
`jointVectorContent ξ s = ∑_{R ∈ J} E_A(S_R) E_B(T_R) ξ`, a value independent of the partition
(`jointVectorContent_eq`, via the common-refinement collapse `jointVector_sUnion`).  Its squared
norm is `mR(s).toReal` (`jointVectorContent_norm_sq`, finite Pythagoras over the disjoint cells) and
it is finitely additive on disjoint elementary sets (`jointVectorContent_add`).

This reduces ∅-continuity to a **single, sharp** statement: on an antitone `sₙ` with `⋂ₙ sₙ = ∅`,
the vectors `jointVectorContent ξ sₙ` form a Cauchy sequence (the squared increments telescope the
antitone real sequence `mR(sₙ).toReal`), hence converge to a limit `w`, and the open content is
exactly `w = 0` — the joint spectral measure of the commuting pair has no mass on `∅`. -/

open scoped Classical in
/-- The effect vector `E_A(S_R) E_B(T_R) ξ` attached to a rectangle `R = S_R ×ˢ T_R` (chosen
representatives; `0` off the rectangle semiring).  Representation-independent on rectangles
(`rectVec_prod`). -/
noncomputable def rectVec (A B : Spectra.Operator.SelfAdjointOperator H) (ξ : H)
    (R : Set (ℝ × ℝ)) : H :=
  if h : R ∈ jointRectangles then
    (A.spectralPVM.proj h.choose h.choose_spec.choose_spec.1
      * B.spectralPVM.proj h.choose_spec.choose h.choose_spec.choose_spec.2.1) ξ
  else 0

/-- **Effect-vector representation independence.**  The vector form of `jointRectVal_aux_indep`: two
presentations of the same rectangle give the same effect vector (factor-agreement, or an empty
factor annihilates `ξ`). -/
theorem rectVec_aux_indep (A B : Spectra.Operator.SelfAdjointOperator H) (ξ : H)
    {S T S' T' : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hS' : MeasurableSet S') (hT' : MeasurableSet T') (heq : S ×ˢ T = S' ×ˢ T') :
    (A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ
      = (A.spectralPVM.proj S' hS' * B.spectralPVM.proj T' hT') ξ := by
  have hzero : ∀ {U V : Set ℝ} (hU : MeasurableSet U) (hV : MeasurableSet V),
      U = ∅ ∨ V = ∅ → (A.spectralPVM.proj U hU * B.spectralPVM.proj V hV) ξ = 0 := by
    rintro U V hU hV (hUe | hVe)
    · rw [ContinuousLinearMap.mul_apply,
        A.spectralPVM.proj_congr hUe hU MeasurableSet.empty, A.spectralPVM.proj_empty]; simp
    · rw [ContinuousLinearMap.mul_apply,
        B.spectralPVM.proj_congr hVe hV MeasurableSet.empty, B.spectralPVM.proj_empty,
        ContinuousLinearMap.zero_apply, map_zero]
  rcases Set.prod_eq_prod_iff.mp heq with ⟨rfl, rfl⟩ | ⟨he, he'⟩
  · rw [A.spectralPVM.proj_congr rfl hS hS', B.spectralPVM.proj_congr rfl hT hT']
  · rw [hzero hS hT he, hzero hS' hT' he']

/-- **`rectVec` on a rectangle is the effect vector.**  `rectVec ξ (S ×ˢ T) = E_A(S) E_B(T) ξ`,
independent of the chosen presentation (`rectVec_aux_indep`). -/
theorem rectVec_prod (A B : Spectra.Operator.SelfAdjointOperator H) (ξ : H)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    rectVec A B ξ (S ×ˢ T) = (A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ := by
  classical
  have hmem : (S ×ˢ T) ∈ jointRectangles := ⟨S, T, hS, hT, rfl⟩
  rw [rectVec, dif_pos hmem]
  exact (rectVec_aux_indep A B ξ hmem.choose_spec.choose_spec.1
    hmem.choose_spec.choose_spec.2.1 hS hT hmem.choose_spec.choose_spec.2.2.symm)

open scoped Classical in
/-- The vector content of an elementary set `s`, as the sum of the rectangle effect vectors over a
chosen disjoint rectangle partition (`0` off the sup-closure).  Partition-independent
(`jointVectorContent_eq`). -/
noncomputable def jointVectorContent (A B : Spectra.Operator.SelfAdjointOperator H) (ξ : H)
    (s : Set (ℝ × ℝ)) : H :=
  if h : s ∈ supClosure jointRectangles then
    ∑ R ∈ ((isSetSemiring_jointRectangles.mem_supClosure_iff).mp h).choose.parts,
      rectVec A B ξ R
  else 0

/-- **Partition independence (the crux).**  For *any* disjoint rectangle cover `J` of `s` (parts in
`jointRectangles`), the sum of the rectangle effect vectors equals `jointVectorContent ξ s`.  Proof:
the chosen partition `K` (from `mem_supClosure_iff`) and `J` have a common refinement
`{R ∩ R' : R ∈ J, R' ∈ K}`; for each fixed `R ∈ J`, `{R ∩ R' : R' ∈ K}` is a disjoint rectangle
cover of the rectangle `R` (since `R ⊆ s = ⋃ K`), so `jointVector_sUnion` collapses
`∑_{R'} E(R ∩ R') = E(R)`.  Summing over `J` and symmetrizing in `J, K` gives equality. -/
theorem jointVectorContent_eq (A B : Spectra.Operator.SelfAdjointOperator H) (ξ : H)
    {s : Set (ℝ × ℝ)} (hs : s ∈ supClosure jointRectangles)
    {J : Finset (Set (ℝ × ℝ))} (hJC : ↑J ⊆ jointRectangles)
    (hJd : (J : Set (Set (ℝ × ℝ))).PairwiseDisjoint id) (hJs : s = ⋃₀ ↑J) :
    ∑ R ∈ J, rectVec A B ξ R = jointVectorContent A B ξ s := by
  classical
  -- expand the chosen-partition definition first, then name the chosen partition `K`
  rw [jointVectorContent, dif_pos hs]
  set K := ((isSetSemiring_jointRectangles.mem_supClosure_iff).mp hs).choose with _hKdef
  have hKC : ↑K.parts ⊆ jointRectangles :=
    ((isSetSemiring_jointRectangles.mem_supClosure_iff).mp hs).choose_spec
  have hKd : (K.parts : Set (Set (ℝ × ℝ))).PairwiseDisjoint id := K.disjoint
  have hKs : s = ⋃₀ ↑K.parts := by
    have h := K.sup_parts
    rw [Finset.sup_set_eq_biUnion] at h
    rw [Set.sUnion_eq_biUnion]
    exact h.symm
  -- The general two-cover agreement
  have agree : ∀ (J₁ J₂ : Finset (Set (ℝ × ℝ))),
      (↑J₁ ⊆ jointRectangles) → (↑J₂ ⊆ jointRectangles) →
      (∀ a ∈ J₂, ∀ b ∈ J₂, a ≠ b → Disjoint a b) →
      (⋃ R ∈ J₁, R) = (⋃ R ∈ J₂, R) →
      ∑ R ∈ J₁, rectVec A B ξ R = ∑ R ∈ J₁, ∑ R' ∈ J₂, rectVec A B ξ (R ∩ R') := by
    intro J₁ J₂ hJ₁C hJ₂C hJ₂d hcov
    refine Finset.sum_congr rfl fun R hR => ?_
    -- `R = S_R ×ˢ T_R` is a rectangle
    obtain ⟨SR, TR, hSR, hTR, hReq⟩ := hJ₁C hR
    -- index the cover of `R` by `R' ∈ J₂` (subtype)
    rw [← Finset.sum_coe_sort J₂ (fun R' => rectVec A B ξ (R ∩ R'))]
    -- represent each `R ∩ R'` as a rectangle `(SR ∩ S') ×ˢ (TR ∩ T')`
    set Sp : {R' // R' ∈ J₂} → Set ℝ := fun R' => SR ∩ (hJ₂C R'.2).choose with _hSpdef
    set Tp : {R' // R' ∈ J₂} → Set ℝ :=
      fun R' => TR ∩ (hJ₂C R'.2).choose_spec.choose with _hTpdef
    have hS'm : ∀ R' : {R' // R' ∈ J₂}, MeasurableSet (hJ₂C R'.2).choose :=
      fun R' => (hJ₂C R'.2).choose_spec.choose_spec.1
    have hT'm : ∀ R' : {R' // R' ∈ J₂}, MeasurableSet (hJ₂C R'.2).choose_spec.choose :=
      fun R' => (hJ₂C R'.2).choose_spec.choose_spec.2.1
    have hR'eq : ∀ R' : {R' // R' ∈ J₂},
        R'.1 = (hJ₂C R'.2).choose ×ˢ (hJ₂C R'.2).choose_spec.choose :=
      fun R' => (hJ₂C R'.2).choose_spec.choose_spec.2.2
    have hSpm : ∀ R', MeasurableSet (Sp R') := fun R' => hSR.inter (hS'm R')
    have hTpm : ∀ R', MeasurableSet (Tp R') := fun R' => hTR.inter (hT'm R')
    have hcell : ∀ R' : {R' // R' ∈ J₂},
        rectVec A B ξ (R ∩ R'.1) = rectVec A B ξ (Sp R' ×ˢ Tp R') := by
      intro R'
      congr 1
      rw [hReq, hR'eq R', Set.prod_inter_prod]
    simp_rw [hcell]
    simp_rw [rectVec_prod A B ξ (hSpm _) (hTpm _)]
    -- rewrite the LHS `rectVec A B ξ R` to the whole-rectangle effect `E_A(SR)E_B(TR)ξ`
    have hLHSeq : rectVec A B ξ R = (A.spectralPVM.proj SR hSR * B.spectralPVM.proj TR hTR) ξ := by
      rw [hReq]; exact rectVec_prod A B ξ hSR hTR
    rw [hLHSeq]
    -- the cells `Sp R' ×ˢ Tp R'` are disjoint and cover `R = SR ×ˢ TR`
    refine (jointVector_sUnion A B Sp Tp hSpm hTpm hSR hTR ?_ ?_ ξ).symm
    · -- disjointness: descends from `J₂` disjointness (cells ⊆ distinct `R'`)
      intro R₁ R₂ hR₁₂
      have hne : R₁.1 ≠ R₂.1 := fun h => hR₁₂ (Subtype.ext h)
      have hd := hJ₂d R₁.1 R₁.2 R₂.1 R₂.2 hne
      rw [Function.onFun]
      rw [show Sp R₁ ×ˢ Tp R₁ = R ∩ R₁.1 by rw [hReq, hR'eq R₁, Set.prod_inter_prod],
        show Sp R₂ ×ˢ Tp R₂ = R ∩ R₂.1 by rw [hReq, hR'eq R₂, Set.prod_inter_prod]]
      exact (hd.mono inf_le_right inf_le_right)
    · -- cover: `⋃ R' (R ∩ R') = R ∩ (⋃ J₂) = R ∩ s = R`
      have hRsub : R ⊆ ⋃ R'' ∈ J₂, R'' := by
        rw [← hcov]; exact Set.subset_biUnion_of_mem (u := fun R => R) hR
      have : ⋃ R' : {R' // R' ∈ J₂}, Sp R' ×ˢ Tp R' = R := by
        have hcells : ∀ R' : {R' // R' ∈ J₂}, Sp R' ×ˢ Tp R' = R ∩ R'.1 := fun R' => by
          rw [hReq, hR'eq R', Set.prod_inter_prod]
        simp_rw [hcells]
        rw [← Set.inter_iUnion]
        rw [show (⋃ R' : {R' // R' ∈ J₂}, R'.1) = ⋃ R'' ∈ J₂, R'' by
          rw [Set.iUnion_subtype]]
        exact Set.inter_eq_left.mpr hRsub
      rw [this, hReq]
  -- apply agreement both ways and conclude
  have hKd' : ∀ a ∈ K.parts, ∀ b ∈ K.parts, a ≠ b → Disjoint a b :=
    fun a ha b hb hab => hKd ha hb hab
  have hJd' : ∀ a ∈ J, ∀ b ∈ J, a ≠ b → Disjoint a b :=
    fun a ha b hb hab => hJd ha hb hab
  -- the covers, in `⋃ R ∈ _, R` form
  have hJbi : (⋃ R ∈ J, R) = s := by rw [hJs]; exact (Set.sUnion_eq_biUnion).symm
  have hKbi : (⋃ R ∈ K.parts, R) = s := by
    conv_rhs => rw [hKs]
    exact (Set.sUnion_eq_biUnion).symm
  have hcovJK : (⋃ R ∈ J, R) = ⋃ R ∈ K.parts, R := by rw [hJbi, hKbi]
  have h1 := agree J K.parts hJC hKC hKd' hcovJK
  have h2 := agree K.parts J hKC hJC hJd' hcovJK.symm
  rw [h1, h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun R' _ => Finset.sum_congr rfl fun R _ => ?_
  rw [Set.inter_comm]

/-- **The content of a rectangle is `‖rectVec‖²`.**  For `R ∈ jointRectangles`,
`jointContent ξ R = ENNReal.ofReal (‖rectVec ξ R‖²)`.  Restates `jointRectVal_prod` through
`rectVec` (`rectVec_prod`). -/
theorem jointContent_rectVec (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) (ξ : H) {R : Set (ℝ × ℝ)} (hR : R ∈ jointRectangles) :
    jointContent A B hSC ξ R = ENNReal.ofReal (‖rectVec A B ξ R‖ ^ 2) := by
  obtain ⟨S, T, hS, hT, rfl⟩ := hR
  change jointRectVal A B ξ (S ×ˢ T) = _
  rw [jointRectVal_prod A B ξ hS hT, rectVec_prod A B ξ hS hT]

/-- **The squared norm of the vector content is the ring content.**
`‖jointVectorContent ξ s‖² = mR(s).toReal`.  Over the chosen rectangle partition `K` of `s`,
`mR(s) = ∑_{R ∈ K} ofReal ‖rectVec R‖²` (`supClosure_apply_finpartition` + `jointContent_rectVec`),
whose `.toReal` is `∑ ‖rectVec R‖²` (`toReal_sum`), which is `‖∑ rectVec R‖²` (finite Pythagoras
over the pairwise-orthogonal disjoint cells, `jointRect_orthogonal_general`), i.e.
`‖jointVectorContent‖²` (`jointVectorContent_eq`). -/
theorem jointVectorContent_norm_sq (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) (ξ : H) {s : Set (ℝ × ℝ)} (hs : s ∈ supClosure jointRectangles) :
    ‖jointVectorContent A B ξ s‖ ^ 2
      = ((jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles s).toReal := by
  classical
  -- the chosen rectangle partition `K`
  obtain ⟨K, hKC⟩ := (isSetSemiring_jointRectangles.mem_supClosure_iff).mp hs
  -- ring content over `K`
  rw [(jointContent A B hSC ξ).supClosure_apply_finpartition isSetSemiring_jointRectangles hKC]
  -- each summand is `ofReal ‖rectVec‖²`
  have hsummand : ∀ R ∈ K.parts,
      jointContent A B hSC ξ R = ENNReal.ofReal (‖rectVec A B ξ R‖ ^ 2) :=
    fun R hR => jointContent_rectVec A B hSC ξ (hKC hR)
  rw [Finset.sum_congr rfl hsummand,
    ← ENNReal.ofReal_sum_of_nonneg (fun R _ => sq_nonneg _), ENNReal.toReal_ofReal
      (Finset.sum_nonneg fun R _ => sq_nonneg _)]
  -- Pythagoras: the cells are pairwise orthogonal
  have hortho : ∀ R₁ ∈ K.parts, ∀ R₂ ∈ K.parts, R₁ ≠ R₂ →
      ⟪rectVec A B ξ R₁, rectVec A B ξ R₂⟫_ℂ = 0 := by
    intro R₁ hR₁ R₂ hR₂ hne
    obtain ⟨S₁, T₁, hS₁, hT₁, hR₁eq⟩ := hKC hR₁
    obtain ⟨S₂, T₂, hS₂, hT₂, hR₂eq⟩ := hKC hR₂
    have hd : Disjoint (S₁ ×ˢ T₁) (S₂ ×ˢ T₂) := by
      rw [← hR₁eq, ← hR₂eq]; exact K.disjoint hR₁ hR₂ hne
    rw [show rectVec A B ξ R₁ = (A.spectralPVM.proj S₁ hS₁ * B.spectralPVM.proj T₁ hT₁) ξ by
        rw [hR₁eq]; exact rectVec_prod A B ξ hS₁ hT₁,
      show rectVec A B ξ R₂ = (A.spectralPVM.proj S₂ hS₂ * B.spectralPVM.proj T₂ hT₂) ξ by
        rw [hR₂eq]; exact rectVec_prod A B ξ hS₂ hT₂]
    exact jointRect_orthogonal_general A B hSC hS₁ hS₂ hT₁ hT₂ hd ξ
  rw [← norm_sum_sq_orthogonal K.parts (rectVec A B ξ) hortho]
  -- identify `∑ rectVec = jointVectorContent`
  have hKd : (K.parts : Set (Set (ℝ × ℝ))).PairwiseDisjoint id := K.disjoint
  have hKs : s = ⋃₀ ↑K.parts := by
    have h := K.sup_parts
    rw [Finset.sup_set_eq_biUnion] at h
    rw [Set.sUnion_eq_biUnion]; exact h.symm
  rw [jointVectorContent_eq A B ξ hs hKC hKd hKs]

/-- **Finite additivity of the vector content** on disjoint elementary sets.
`jointVectorContent ξ (a ∪ b) = jointVectorContent ξ a + jointVectorContent ξ b` for disjoint
`a, b ∈ supClosure jointRectangles`.  Proof: chosen partitions `Ja, Jb` of `a, b` combine to a
disjoint rectangle partition `Ja ∪ Jb` of `a ∪ b`; `jointVectorContent_eq` evaluates all three sides
and `Finset.sum_union` (disjoint part-sets, since `a, b` disjoint) splits the sum. -/
theorem jointVectorContent_add (A B : Spectra.Operator.SelfAdjointOperator H) (ξ : H)
    {a b : Set (ℝ × ℝ)} (ha : a ∈ supClosure jointRectangles) (hb : b ∈ supClosure jointRectangles)
    (hab : Disjoint a b) :
    jointVectorContent A B ξ (a ∪ b)
      = jointVectorContent A B ξ a + jointVectorContent A B ξ b := by
  classical
  obtain ⟨Ja, hJaC⟩ := (isSetSemiring_jointRectangles.mem_supClosure_iff).mp ha
  obtain ⟨Jb, hJbC⟩ := (isSetSemiring_jointRectangles.mem_supClosure_iff).mp hb
  have hJad : (Ja.parts : Set (Set (ℝ × ℝ))).PairwiseDisjoint id := Ja.disjoint
  have hJbd : (Jb.parts : Set (Set (ℝ × ℝ))).PairwiseDisjoint id := Jb.disjoint
  have hJas : a = ⋃₀ ↑Ja.parts := by
    have h := Ja.sup_parts; rw [Finset.sup_set_eq_biUnion] at h
    rw [Set.sUnion_eq_biUnion]; exact h.symm
  have hJbs : b = ⋃₀ ↑Jb.parts := by
    have h := Jb.sup_parts; rw [Finset.sup_set_eq_biUnion] at h
    rw [Set.sUnion_eq_biUnion]; exact h.symm
  -- the part-sets are disjoint as Finsets (members of `Ja` ⊆ `a`, of `Jb` ⊆ `b`, and `a, b`
  -- disjoint)
  have hpartDisjoint : Disjoint Ja.parts Jb.parts := by
    rw [Finset.disjoint_left]
    intro R hRa hRb
    -- `R ⊆ a` and `R ⊆ b`, but each `R` is nonempty in a Finpartition (⊥ ∉ parts)... handle empty
    -- too
    have hRsuba : R ⊆ a := by rw [hJas]; exact Set.subset_sUnion_of_mem hRa
    have hRsubb : R ⊆ b := by rw [hJbs]; exact Set.subset_sUnion_of_mem hRb
    have hRempty : R = ⊥ := by
      rw [Set.bot_eq_empty, ← Set.subset_empty_iff,
        ← Set.disjoint_iff_inter_eq_empty.mp hab]
      exact Set.subset_inter hRsuba hRsubb
    exact Ja.bot_notMem (hRempty ▸ hRa)
  -- `Ja.parts ∪ Jb.parts` is a disjoint rectangle partition of `a ∪ b`
  have hUC : ↑(Ja.parts ∪ Jb.parts) ⊆ jointRectangles := by
    rw [Finset.coe_union]; exact Set.union_subset hJaC hJbC
  have hUd : ((Ja.parts ∪ Jb.parts : Finset (Set (ℝ × ℝ))) :
      Set (Set (ℝ × ℝ))).PairwiseDisjoint id := by
    rw [Finset.coe_union]
    apply Set.PairwiseDisjoint.union hJad hJbd
    intro R₁ hR₁ R₂ hR₂ _
    have hR₁suba : R₁ ⊆ a := by rw [hJas]; exact Set.subset_sUnion_of_mem hR₁
    have hR₂subb : R₂ ⊆ b := by rw [hJbs]; exact Set.subset_sUnion_of_mem hR₂
    exact (hab.mono hR₁suba hR₂subb)
  have hUs : a ∪ b = ⋃₀ ↑(Ja.parts ∪ Jb.parts) := by
    rw [Finset.coe_union, Set.sUnion_union, ← hJas, ← hJbs]
  have hUmem : a ∪ b ∈ supClosure jointRectangles :=
    (isSetSemiring_jointRectangles.isSetRing_supClosure).union_mem ha hb
  -- evaluate all three contents over their partitions and split the sum
  rw [← jointVectorContent_eq A B ξ hUmem hUC hUd hUs,
    ← jointVectorContent_eq A B ξ ha hJaC hJad hJas,
    ← jointVectorContent_eq A B ξ hb hJbC hJbd hJbs,
    Finset.sum_union hpartDisjoint]

/-! ## G2.2 — compact inner regularity of the ring content (the tightness ∅-continuity)

The ring content `mR` is **inner regular by compact rectangles**: any elementary set is approximated
from inside by a compact elementary set up to arbitrarily small content.  Per rectangle this is the
marginal-defect bound `jointContentRing_diff_le` (the ℝ≥0∞ lift of `jointRect_diff_defect_le`) fed
by the inner regularity of the genuine marginals `μ^A_ξ, μ^B_ξ` on `ℝ`.  This is the compactness
input that discharges `jointContentRing_tendsto_empty` by the classical Alexandrov argument (a
finitely additive, compact-inner-regular content is σ-additive): a decreasing elementary sequence
with empty intersection cannot keep positive content, else the inner compact approximants would have
the finite intersection property and meet. -/

/-- The ring content of a single rectangle is `ofReal ‖E_A(S)E_B(T)ξ‖²` (`supClosure_apply_of_mem` +
`jointContent_rectVec` + `rectVec_prod`). -/
theorem jointContentRing_prod (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) (ξ : H) {S T : Set ℝ} (hS : MeasurableSet S)
    (hT : MeasurableSet T) :
    (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles (S ×ˢ T)
      = ENNReal.ofReal (‖(A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ‖ ^ 2) := by
  rw [(jointContent A B hSC ξ).supClosure_apply_of_mem isSetSemiring_jointRectangles
        ⟨S, T, hS, hT, rfl⟩,
    jointContent_rectVec A B hSC ξ ⟨S, T, hS, hT, rfl⟩, rectVec_prod A B ξ hS hT]

/-- **The marginal-defect bound on the ring content.**  The content of the difference
`(S×T) ∖ (S'×T')` is bounded by the two marginal defects `μ^A_ξ(S∖S') + μ^B_ξ(T∖T')`.  Lifts
`jointRect_diff_defect_le` from the norm² pieces to the ℝ≥0∞ ring content, via the semiring
difference decomposition `(S×T)∖(S'×T') = (S∖S')×T ⊔ (S∩S')×(T∖T')` + finite additivity
(`addContent_union`).  Together with inner regularity of `μ^A_ξ, μ^B_ξ`, this is the compact
inner-regularity input to the Alexandrov ∅-continuity argument. -/
theorem jointContentRing_diff_le (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) (ξ : H) {S S' T T' : Set ℝ} (hS : MeasurableSet S)
    (hS' : MeasurableSet S')
    (hT : MeasurableSet T) (hT' : MeasurableSet T') :
    (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles ((S ×ˢ T) \ (S' ×ˢ T'))
      ≤ A.spectralPVM.diag ξ (S \ S') + B.spectralPVM.diag ξ (T \ T') := by
  have hRing : MeasureTheory.IsSetRing (supClosure jointRectangles) :=
    isSetSemiring_jointRectangles.isSetRing_supClosure
  have hset : (S ×ˢ T) \ (S' ×ˢ T')
      = ((S \ S') ×ˢ T) ∪ ((S ∩ S') ×ˢ (T \ T')) := by
    ext ⟨x, y⟩
    simp only [Set.mem_diff, Set.mem_prod, Set.mem_union, Set.mem_inter_iff]
    tauto
  have hP₁ : ((S \ S') ×ˢ T) ∈ supClosure jointRectangles :=
    subset_supClosure ⟨S \ S', T, hS.diff hS', hT, rfl⟩
  have hP₂ : ((S ∩ S') ×ˢ (T \ T')) ∈ supClosure jointRectangles :=
    subset_supClosure ⟨S ∩ S', T \ T', hS.inter hS', hT.diff hT', rfl⟩
  have hdisj : Disjoint ((S \ S') ×ˢ T) ((S ∩ S') ×ˢ (T \ T')) := by
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ ⟨hx, _⟩ ⟨hx', _⟩
    exact hx.2 hx'.2
  rw [hset, addContent_union hRing hP₁ hP₂ hdisj,
    jointContentRing_prod A B hSC ξ (hS.diff hS') hT,
    jointContentRing_prod A B hSC ξ (hS.inter hS') (hT.diff hT'),
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  refine le_trans (ENNReal.ofReal_le_ofReal
    (jointRect_diff_defect_le A B hSC hS hS' hT hT' ξ)) ?_
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **Per-rectangle compact inner approximation.**  A measurable rectangle `S ×ˢ T` is approximated
from inside by a compact rectangle `K = S' ×ˢ T'` whose content defect is `< ε`: pick compact
`S' ⊆ S`, `T' ⊆ T` by inner regularity of the marginals `μ^A_ξ, μ^B_ξ` (each defect `< ε/2`), then
`jointContentRing_diff_le` bounds the joint defect by `μ^A_ξ(S∖S') + μ^B_ξ(T∖T') < ε`. -/
theorem jointRect_inner_compact (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) (ξ : H) {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T)
    {ε : ENNReal} (hε : ε ≠ 0) :
    ∃ K : Set (ℝ × ℝ), K ∈ jointRectangles ∧ K ⊆ S ×ˢ T ∧ IsCompact K ∧
      (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles ((S ×ˢ T) \ K) < ε := by
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε).ne'
  obtain ⟨S', hS'sub, hS'cp, hS'lt⟩ :=
    hS.exists_isCompact_diff_lt (measure_ne_top (A.spectralPVM.diag ξ) S) hε2
  obtain ⟨T', hT'sub, hT'cp, hT'lt⟩ :=
    hT.exists_isCompact_diff_lt (measure_ne_top (B.spectralPVM.diag ξ) T) hε2
  refine ⟨S' ×ˢ T',
    ⟨S', T', hS'cp.isClosed.measurableSet, hT'cp.isClosed.measurableSet, rfl⟩,
    Set.prod_mono hS'sub hT'sub, hS'cp.prod hT'cp, ?_⟩
  calc (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles ((S ×ˢ T) \ (S' ×ˢ T'))
      ≤ A.spectralPVM.diag ξ (S \ S') + B.spectralPVM.diag ξ (T \ T') :=
        jointContentRing_diff_le A B hSC ξ hS hS'cp.isClosed.measurableSet hT
          hT'cp.isClosed.measurableSet
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hS'lt hT'lt
    _ = ε := ENNReal.add_halves ε

/-- **Compact inner regularity of the ring content.**  Every elementary set `s` (a finite union of
measurable rectangles) is approximated from inside by a compact elementary set `K ⊆ s` with content
defect `mR(s ∖ K) ≤ ε`.  Induction over a rectangle cover of `s`: approximate each rectangle part by
a compact sub-rectangle (`jointRect_inner_compact`) at budget `ε/2ⁿ`, union them, and bound the
total defect by finite subadditivity (`addContent_union_le`).  This is the tightness hypothesis the
Alexandrov ∅-continuity argument feeds on. -/
theorem jointElem_inner_compact (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) (ξ : H) {s : Set (ℝ × ℝ)} (hs : s ∈ supClosure jointRectangles)
    {ε : ENNReal} (hε : ε ≠ 0) :
    ∃ K : Set (ℝ × ℝ), K ∈ supClosure jointRectangles ∧ K ⊆ s ∧ IsCompact K ∧
      (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles (s \ K) ≤ ε := by
  classical
  have hRing : MeasureTheory.IsSetRing (supClosure jointRectangles) :=
    isSetSemiring_jointRectangles.isSetRing_supClosure
  -- inner-approximate an arbitrary finite union of rectangles (no disjointness needed)
  have aux : ∀ (J : Finset (Set (ℝ × ℝ))), ↑J ⊆ jointRectangles → ∀ {δ : ENNReal}, δ ≠ 0 →
      ∃ K, K ∈ supClosure jointRectangles ∧ K ⊆ ⋃₀ ↑J ∧ IsCompact K ∧
        (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles ((⋃₀ ↑J) \ K) ≤ δ := by
    intro J
    induction J using Finset.induction with
    | empty =>
        intro _ δ _
        refine ⟨∅, hRing.empty_mem, by simp, isCompact_empty, ?_⟩
        simp only [Finset.coe_empty, Set.sUnion_empty, Set.diff_empty, addContent_empty]
        exact zero_le
    | @insert R J hRnotin ih =>
        intro hJC δ hδ
        obtain ⟨S, T, hS, hT, rfl⟩ : R ∈ jointRectangles := hJC (Finset.mem_insert_self R J)
        have hJC' : ↑J ⊆ jointRectangles := fun x hx => hJC (Finset.mem_insert_of_mem hx)
        have hδ2 : δ / 2 ≠ 0 := (ENNReal.half_pos hδ).ne'
        obtain ⟨KJ, hKJmem, hKJsub, hKJcp, hKJle⟩ := ih hJC' hδ2
        obtain ⟨KR, hKRmem, hKRsub, hKRcp, hKRlt⟩ :=
          jointRect_inner_compact A B hSC ξ hS hT hδ2
        have hB'mem : ⋃₀ (↑J : Set (Set (ℝ × ℝ))) ∈ supClosure jointRectangles := by
          rw [Set.sUnion_eq_biUnion, Finset.set_biUnion_coe]
          exact hRing.biUnion_mem J fun x hx => subset_supClosure (hJC' (Finset.mem_coe.mpr hx))
        have hSTmem : (S ×ˢ T) ∈ supClosure jointRectangles := subset_supClosure ⟨S, T, hS, hT, rfl⟩
        have hKRring : KR ∈ supClosure jointRectangles := subset_supClosure hKRmem
        refine ⟨KR ∪ KJ, hRing.union_mem hKRring hKJmem, ?_, hKRcp.union hKJcp, ?_⟩
        · rw [Finset.coe_insert, Set.sUnion_insert]
          exact Set.union_subset_union hKRsub hKJsub
        · rw [Finset.coe_insert, Set.sUnion_insert]
          have hsub : ((S ×ˢ T) ∪ ⋃₀ (↑J : Set (Set (ℝ × ℝ)))) \ (KR ∪ KJ)
              ⊆ ((S ×ˢ T) \ KR) ∪ (⋃₀ (↑J : Set (Set (ℝ × ℝ))) \ KJ) := by
            rw [Set.union_diff_distrib]
            exact Set.union_subset_union
              (Set.diff_subset_diff_right Set.subset_union_left)
              (Set.diff_subset_diff_right Set.subset_union_right)
          calc (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles
                  (((S ×ˢ T) ∪ ⋃₀ ↑J) \ (KR ∪ KJ))
              ≤ (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles
                  (((S ×ˢ T) \ KR) ∪ (⋃₀ ↑J \ KJ)) :=
                addContent_mono hRing.isSetSemiring
                  (hRing.diff_mem (hRing.union_mem hSTmem hB'mem) (hRing.union_mem hKRring hKJmem))
                  (hRing.union_mem (hRing.diff_mem hSTmem hKRring) (hRing.diff_mem hB'mem hKJmem))
                  hsub
            _ ≤ (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles ((S ×ˢ T) \ KR)
                  + (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles
                    (⋃₀ ↑J \ KJ) :=
                addContent_union_le hRing (hRing.diff_mem hSTmem hKRring)
                  (hRing.diff_mem hB'mem hKJmem)
            _ ≤ δ / 2 + δ / 2 := add_le_add hKRlt.le hKJle
            _ = δ := ENNReal.add_halves δ
  -- apply `aux` to a chosen rectangle partition of `s`
  obtain ⟨P, hPC⟩ := (isSetSemiring_jointRectangles.mem_supClosure_iff).mp hs
  have hPs : s = ⋃₀ ↑P.parts := by
    have h := P.sup_parts
    rw [Finset.sup_set_eq_biUnion] at h
    rw [Set.sUnion_eq_biUnion]; exact h.symm
  rw [hPs]
  exact aux P.parts hPC hε

/-- **Continuity at `∅` of the ring content.**  For an antitone sequence `sₙ` of elementary sets
(finite disjoint unions of rectangles) with `⋂ₙ sₙ = ∅`, the content
`mR(sₙ) = ‖jointVectorContent ξ sₙ‖²` tends to `0` — the σ-additivity input (`AddContent.measure`)
for the joint scalar measure.

The reduction `mR(sₙ) → ‖w‖²` for the in-`H` limit `w` of the Cauchy sequence of vector contents
`jointVectorContent ξ sₙ` is elementary (`jointVectorContent_norm_sq`, `_add`, ring additivity); the
sharp content is `w = 0`, the **multivariate spectral theorem's** core (the joint spectral measure
of the commuting pair assigns no mass to `∅`; *not* recoverable from the marginal data alone, cf.
`exists_coupling_always`).  It is discharged here by **Route T (tightness / Alexandrov)**: the joint
content's compact inner regularity comes from the genuine marginals via commutation + contraction
(the approximation *defect* `mR((S×T)∖(S'×T')) ≤ μ^A_ξ(S∖S') + μ^B_ξ(T∖T')` is marginal-controlled
even though the *mass* is not), and a finite-intersection-property argument on decreasing compacts
forces `w = 0`.  `sorry`-free and axiom-clean. -/
theorem jointContentRing_tendsto_empty (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) (ξ : H) ⦃s : ℕ → Set (ℝ × ℝ)⦄
    (hs : ∀ n, s n ∈ supClosure jointRectangles) (hanti : Antitone s) (hempty : (⋂ n, s n) = ∅) :
    Filter.Tendsto
      (fun n => (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles (s n))
      Filter.atTop (nhds 0) := by
  classical
  set mR := (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles with _hmRdef
  have hRing : MeasureTheory.IsSetRing (supClosure jointRectangles) :=
    isSetSemiring_jointRectangles.isSetRing_supClosure
  have hmR_ne_top : ∀ n, mR (s n) ≠ ⊤ := fun n => jointContentRing_ne_top A B hSC ξ (hs n)
  -- the vector content and the real content sequence
  set v : ℕ → H := fun n => jointVectorContent A B ξ (s n) with hvdef
  set a : ℕ → ℝ := fun n => (mR (s n)).toReal with hadef
  have hav : ∀ n, a n = ‖v n‖ ^ 2 := fun n =>
    (jointVectorContent_norm_sq A B hSC ξ (hs n)).symm
  have ha_nonneg : ∀ n, 0 ≤ a n := fun n => ENNReal.toReal_nonneg
  -- `mR` is monotone on the ring and `s` is antitone, so `a` is antitone
  have ha_anti : Antitone a := by
    intro n m hnm
    refine ENNReal.toReal_mono (hmR_ne_top n) ?_
    exact addContent_mono hRing.isSetSemiring (hs m) (hs n) (hanti hnm)
  -- the telescoping increment: for `n ≤ m`, `v n − v m = jointVectorContent ξ (s n \ s m)`
  have hdiff : ∀ n m, n ≤ m →
      v n - v m = jointVectorContent A B ξ (s n \ s m) ∧
      a n - a m = ‖jointVectorContent A B ξ (s n \ s m)‖ ^ 2 := by
    intro n m hnm
    have hsm_sub : s m ⊆ s n := hanti hnm
    have hdmem : (s n \ s m) ∈ supClosure jointRectangles := hRing.diff_mem (hs n) (hs m)
    -- decompose `s n = s m ∪ (s n \ s m)` (disjoint)
    have hunion : s n = s m ∪ (s n \ s m) := (Set.union_diff_cancel hsm_sub).symm
    have hdisj : Disjoint (s m) (s n \ s m) := disjoint_sdiff_self_right
    have hvadd : v n = v m + jointVectorContent A B ξ (s n \ s m) := by
      rw [hvdef]; dsimp only
      conv_lhs => rw [hunion]
      exact jointVectorContent_add A B ξ (hs m) hdmem hdisj
    refine ⟨by rw [hvadd]; abel, ?_⟩
    -- the real content telescopes: `a n = a m + ‖...‖²`
    have haadd : a n = a m + ‖jointVectorContent A B ξ (s n \ s m)‖ ^ 2 := by
      rw [hadef]; dsimp only
      have hcont : mR (s n) = mR (s m) + mR (s n \ s m) := by
        conv_lhs => rw [hunion]
        exact addContent_union hRing (hs m) hdmem hdisj
      rw [hcont, ENNReal.toReal_add (hmR_ne_top m)
          (jointContentRing_ne_top A B hSC ξ hdmem),
        jointVectorContent_norm_sq A B hSC ξ hdmem]
    rw [haadd]; ring
  -- symmetric norm identity: `‖v n − v m‖² = |a n − a m|`
  have hsym : ∀ n m, ‖v n - v m‖ ^ 2 = |a n - a m| := by
    intro n m
    rcases le_total n m with h | h
    · obtain ⟨hd, ha⟩ := hdiff n m h
      rw [hd, ← ha, abs_of_nonneg]
      exact sub_nonneg.mpr (ha_anti h)
    · obtain ⟨hd, ha⟩ := hdiff m n h
      have : ‖v n - v m‖ ^ 2 = ‖v m - v n‖ ^ 2 := by rw [← norm_neg, neg_sub]
      rw [this, hd, ← ha, abs_of_nonpos (by linarith [ha_anti h])]
      ring
  -- `a` converges (antitone, bounded below by 0) to its infimum `L`
  have hbdd : BddBelow (Set.range a) := ⟨0, by rintro _ ⟨n, rfl⟩; exact ha_nonneg n⟩
  set L : ℝ := ⨅ n, a n with _hLdef
  have ha_tendsto : Tendsto a atTop (𝓝 L) := tendsto_atTop_ciInf ha_anti hbdd
  have hL_le : ∀ n, L ≤ a n := fun n => ciInf_le hbdd n
  -- the Cauchy modulus `b N = √(a N − L) → 0`, dominating `dist (v n) (v m)` for `N ≤ n, m`
  set b : ℕ → ℝ := fun N => Real.sqrt (a N - L) with hbdef
  have hb_tendsto : Tendsto b atTop (𝓝 0) := by
    have : Tendsto (fun N => a N - L) atTop (𝓝 (L - L)) := ha_tendsto.sub_const L
    rw [sub_self] at this
    have := this.sqrt
    rwa [Real.sqrt_zero] at this
  have hvCauchy : CauchySeq v := by
    refine cauchySeq_of_le_tendsto_0 b (fun n m N hNn hNm => ?_) hb_tendsto
    -- `dist (v n) (v m) = ‖v n − v m‖ = √|a n − a m| ≤ √(a N − L) = b N`
    rw [dist_eq_norm]
    have hnorm : ‖v n - v m‖ = Real.sqrt |a n - a m| := by
      rw [← hsym n m, Real.sqrt_sq (norm_nonneg _)]
    rw [hnorm, hbdef]
    refine Real.sqrt_le_sqrt ?_
    -- both `a n, a m ∈ [L, a N]`, so `|a n − a m| ≤ a N − L`
    have hn := ha_anti hNn
    have hm := ha_anti hNm
    rw [abs_le]
    exact ⟨by linarith [hL_le n], by linarith [hL_le m]⟩
  -- the limit vector `w`
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hvCauchy
  -- `a n = ‖v n‖² → ‖w‖²`
  have ha_to_w : Tendsto a atTop (𝓝 (‖w‖ ^ 2)) := by
    refine (hw.norm.pow 2).congr fun n => ?_
    exact (hav n).symm
  /- The limit `w = 0` by the **tightness (Alexandrov) argument**: it suffices that `L = ⨅ₙ aₙ = 0`.
     If `L > 0`, inner-approximate each `sₙ` by a compact elementary `Cₙ ⊆ sₙ`
     (`jointElem_inner_compact`) with content defect `≤ L/4·2⁻ⁿ`; the decreasing compacts
     `Kₙ = ⋂_{j≤n} Cⱼ` then keep content `≥ L/2 > 0`, so each is nonempty, and by the finite
     intersection property `⋂ₙ Kₙ ≠ ∅` — but `Kₙ ⊆ sₙ`, contradicting `⋂ₙ sₙ = ∅`.  The defect is
     marginal-controlled (`jointRect_diff_defect_le`), the one place the genuine
     commuting-projection structure enters. -/
  have hw0 : w = 0 := by
    have hwsq : ‖w‖ ^ 2 = L := tendsto_nhds_unique ha_to_w ha_tendsto
    have hL_nonneg : 0 ≤ L := ge_of_tendsto' ha_tendsto ha_nonneg
    suffices hL0 : L = 0 by
      have hnw : ‖w‖ = 0 := by
        have h0 : ‖w‖ ^ 2 = 0 := hwsq.trans hL0
        exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h0
      exact norm_eq_zero.mp hnw
    by_contra hLne
    have hLpos : 0 < L := lt_of_le_of_ne hL_nonneg (Ne.symm hLne)
    -- per-step compact inner approximations `Cⱼ ⊆ sⱼ` with content defect `≤ ofReal (L/4·(1/2)ʲ)`
    have hbudget : ∀ j, ∃ C, C ∈ supClosure jointRectangles ∧ C ⊆ s j ∧ IsCompact C ∧
        mR (s j \ C) ≤ ENNReal.ofReal (L / 4 * (1 / 2) ^ j) := by
      intro j
      apply jointElem_inner_compact A B hSC ξ (hs j)
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact mul_pos (by linarith) (by positivity)
    choose C hCmem hCsub hCcp hCle using hbudget
    have hCclosed : ∀ j, IsClosed (C j) := fun j => (hCcp j).isClosed
    -- the decreasing compact family `Kₙ = ⋂_{j ∈ range (n+1)} Cⱼ`
    set K : ℕ → Set (ℝ × ℝ) := fun n => ⋂ j ∈ Finset.range (n + 1), C j with hKdef
    have hKsubC : ∀ n, K n ⊆ C n := fun n => by
      simp only [hKdef]; exact Set.biInter_subset_of_mem (Finset.self_mem_range_succ n)
    have hKsub0 : ∀ n, K n ⊆ C 0 := fun n => by
      simp only [hKdef]
      exact Set.biInter_subset_of_mem (Finset.mem_range.mpr (Nat.succ_pos n))
    have hKsubs : ∀ n, K n ⊆ s n := fun n => (hKsubC n).trans (hCsub n)
    have hKclosed : ∀ n, IsClosed (K n) := fun n => by
      simp only [hKdef]; exact isClosed_iInter fun j => isClosed_iInter fun _ => hCclosed j
    have hKcompact : ∀ n, IsCompact (K n) := fun n =>
      (hCcp 0).of_isClosed_subset (hKclosed n) (hKsub0 n)
    have hKmem : ∀ n, K n ∈ supClosure jointRectangles := fun n => by
      simp only [hKdef]
      exact hRing.biInter_mem (Finset.range (n + 1))
        (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n)) fun j _ => hCmem j
    have hKdec : ∀ n, K (n + 1) ⊆ K n := by
      intro n x hx
      simp only [hKdef, Set.mem_iInter, Finset.mem_range] at hx ⊢
      exact fun j hj => hx j (by omega)
    -- the cumulative defect stays `≤ ofReal (L/2)`
    have hdefect : ∀ n, mR (s n \ K n) ≤ ENNReal.ofReal (L / 2) := by
      intro n
      have hsub : s n \ K n ⊆ ⋃ j ∈ Finset.range (n + 1), (s j \ C j) := by
        intro x hx
        obtain ⟨hxsn, hxnK⟩ := hx
        simp only [hKdef, Set.mem_iInter, Finset.mem_range, not_forall, exists_prop] at hxnK
        obtain ⟨j, hj, hxCj⟩ := hxnK
        exact Set.mem_biUnion (Finset.mem_range.mpr hj) ⟨hanti (Nat.lt_succ_iff.mp hj) hxsn, hxCj⟩
      calc mR (s n \ K n)
          ≤ mR (⋃ j ∈ Finset.range (n + 1), (s j \ C j)) :=
            addContent_mono hRing.isSetSemiring (hRing.diff_mem (hs n) (hKmem n))
              (hRing.biUnion_mem _ fun j _ => hRing.diff_mem (hs j) (hCmem j)) hsub
        _ ≤ ∑ j ∈ Finset.range (n + 1), mR (s j \ C j) :=
            addContent_biUnion_le hRing fun j _ => hRing.diff_mem (hs j) (hCmem j)
        _ ≤ ∑ j ∈ Finset.range (n + 1), ENNReal.ofReal (L / 4 * (1 / 2) ^ j) :=
            Finset.sum_le_sum fun j _ => hCle j
        _ = ENNReal.ofReal (∑ j ∈ Finset.range (n + 1), L / 4 * (1 / 2) ^ j) :=
            (ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity).symm
        _ ≤ ENNReal.ofReal (L / 2) := by
            apply ENNReal.ofReal_le_ofReal
            rw [← Finset.mul_sum]
            have hgeo : ∑ j ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ j ≤ 2 :=
              (summable_geometric_two.sum_le_tsum _ fun i _ => by positivity).trans_eq
                tsum_geometric_two
            calc L / 4 * ∑ j ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ j
                ≤ L / 4 * 2 := by apply mul_le_mul_of_nonneg_left hgeo (by linarith)
              _ = L / 2 := by ring
    -- each `Kₙ` is nonempty: its content is `≥ L/2 > 0`
    have hKne : ∀ n, (K n).Nonempty := by
      intro n
      rw [Set.nonempty_iff_ne_empty]
      intro hKempty
      have hdnetop : mR (s n \ K n) ≠ ⊤ :=
        jointContentRing_ne_top A B hSC ξ (hRing.diff_mem (hs n) (hKmem n))
      have hKnetop : mR (K n) ≠ ⊤ :=
        ne_top_of_le_ne_top (hmR_ne_top n)
          (addContent_mono hRing.isSetSemiring (hKmem n) (hs n) (hKsubs n))
      have hadd : mR (s n) = mR (K n) + mR (s n \ K n) := by
        conv_lhs => rw [(Set.union_diff_cancel (hKsubs n)).symm]
        exact addContent_union hRing (hKmem n) (hRing.diff_mem (hs n) (hKmem n))
          disjoint_sdiff_self_right
      have hareal : a n = (mR (K n)).toReal + (mR (s n \ K n)).toReal := by
        rw [hadef]; dsimp only; rw [hadd, ENNReal.toReal_add hKnetop hdnetop]
      have hdtoReal : (mR (s n \ K n)).toReal ≤ L / 2 := by
        have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdefect n)
        rwa [ENNReal.toReal_ofReal (by positivity)] at h
      have hKzero : (mR (K n)).toReal = 0 := by
        rw [hKempty, addContent_empty, ENNReal.toReal_zero]
      linarith [hL_le n, hareal, hdtoReal, hKzero, hLpos]
    -- finite intersection property: `⋂ₙ Kₙ ≠ ∅`, but `Kₙ ⊆ sₙ` and `⋂ₙ sₙ = ∅`
    have hmeet : (⋂ n, K n).Nonempty :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hKdec hKne
        (hKcompact 0) hKclosed
    have hKsub_inter : (⋂ n, K n) ⊆ (⋂ n, s n) := Set.iInter_mono hKsubs
    rw [hempty] at hKsub_inter
    exact absurd (hmeet.mono hKsub_inter) (Set.not_nonempty_empty)
  -- conclude: `mR (s n) = ofReal (a n) → ofReal ‖w‖² = ofReal 0 = 0`
  have hmR_eq : ∀ n, mR (s n) = ENNReal.ofReal (a n) := fun n =>
    (ENNReal.ofReal_toReal (hmR_ne_top n)).symm
  have hgoal : Tendsto (fun n => mR (s n)) atTop (𝓝 (ENNReal.ofReal (‖w‖ ^ 2))) := by
    simp only [hmR_eq]
    exact (ENNReal.continuous_ofReal.tendsto _).comp ha_to_w
  rw [hw0, norm_zero] at hgoal
  simpa using hgoal

/-- **σ-subadditivity of the rectangle content.**  The semiring content `jointContent` is
σ-subadditive.  Proof: build the σ-additive ring content `mR` on the sup-closure ring via
`addContent_iUnion_eq_sum_of_tendsto_zero` (finiteness `jointContentRing_ne_top` + ∅-continuity
`jointContentRing_tendsto_empty`), get `mR.IsSigmaSubadditive`
(`isSigmaSubadditive_of_addContent_iUnion_eq_tsum`), then transfer down to the rectangles via
`supClosure_apply_of_mem` (a rectangle is its own one-element sup-closure value).  Rests on the
∅-continuity `jointContentRing_tendsto_empty`, which is proved, so this is `sorry`-free. -/
theorem jointContent_isSigmaSubadditive (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) (ξ : H) : (jointContent A B hSC ξ).IsSigmaSubadditive := by
  have hRing : MeasureTheory.IsSetRing (supClosure jointRectangles) :=
    isSetSemiring_jointRectangles.isSetRing_supClosure
  set mR := (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles with _hmR
  have m_iUnion : ∀ (f : ℕ → Set (ℝ × ℝ)) (_ : ∀ i, f i ∈ supClosure jointRectangles)
      (_ : (⋃ i, f i) ∈ supClosure jointRectangles)
      (_ : Pairwise (Function.onFun Disjoint f)),
      mR (⋃ i, f i) = ∑' i, mR (f i) :=
    fun f hf hUf hdisj =>
      MeasureTheory.addContent_iUnion_eq_sum_of_tendsto_zero hRing mR
        (fun s hs => jointContentRing_ne_top A B hSC ξ hs)
        (fun s hs hanti hempty => jointContentRing_tendsto_empty A B hSC ξ hs hanti hempty)
        hf hUf hdisj
  have hRsub : mR.IsSigmaSubadditive :=
    MeasureTheory.isSigmaSubadditive_of_addContent_iUnion_eq_tsum hRing m_iUnion
  intro f hf hUf
  have hfR : ∀ i, f i ∈ supClosure jointRectangles := fun i => subset_supClosure (hf i)
  have hUfR : (⋃ i, f i) ∈ supClosure jointRectangles := subset_supClosure hUf
  have key := hRsub hfR hUfR
  rwa [(jointContent A B hSC ξ).supClosure_apply_of_mem isSetSemiring_jointRectangles hUf,
    show (fun i => mR (f i)) = (fun i => jointContent A B hSC ξ (f i)) from
      funext fun i => (jointContent A B hSC ξ).supClosure_apply_of_mem
        isSetSemiring_jointRectangles (hf i)] at key

/-- **The rectangle semiring generates the Borel σ-algebra of `ℝ × ℝ`.**  `jointRectangles`
(`= image2 (· ×ˢ ·) {MeasurableSet} {MeasurableSet}` after reordering existentials) generates the
product measurable space `Prod.instMeasurableSpace`, which is the ambient instance
(`generateFrom_prod`).  Supplies the `hC_gen` equality for the Carathéodory extension. -/
theorem generateFrom_jointRectangles :
    (inferInstance : MeasurableSpace (ℝ × ℝ))
      = MeasurableSpace.generateFrom jointRectangles := by
  have hset : jointRectangles
      = Set.image2 (· ×ˢ ·) {s : Set ℝ | MeasurableSet s} {t : Set ℝ | MeasurableSet t} := by
    ext R
    simp only [jointRectangles, Set.mem_setOf_eq, Set.mem_image2]
    constructor
    · rintro ⟨S, T, hS, hT, rfl⟩; exact ⟨S, hS, T, hT, rfl⟩
    · rintro ⟨S, hS, T, hT, rfl⟩; exact ⟨S, T, hS, hT, rfl⟩
  rw [hset, generateFrom_prod]

/-- **The per-state joint scalar measure `μ_ξ`.**  The Carathéodory extension of the rectangle
content `jointContent` to a (finite, see below) Borel measure on `ℝ × ℝ`. -/
noncomputable def jointScalarMeasure (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) (ξ : H) : MeasureTheory.Measure (ℝ × ℝ) :=
  (jointContent A B hSC ξ).measure isSetSemiring_jointRectangles
    generateFrom_jointRectangles.le (jointContent_isSigmaSubadditive A B hSC ξ)

/-- **`μ_ξ` on a rectangle is the bimeasure value.**  `μ_ξ(S ×ˢ T) = μ^A_{E_B(T)ξ}(S)` — the
Carathéodory measure agrees with the content on the semiring (`AddContent.measure_eq`), and the
content on a rectangle is the diagonal form (`jointRectVal_prod_diag`). -/
theorem jointScalarMeasure_prod (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) (ξ : H) {S T : Set ℝ} (hS : MeasurableSet S)
    (hT : MeasurableSet T) :
    jointScalarMeasure A B hSC ξ (S ×ˢ T)
      = (A.spectralPVM.diag (B.spectralPVM.proj T hT ξ)) S := by
  have hmem : (S ×ˢ T) ∈ jointRectangles := ⟨S, T, hS, hT, rfl⟩
  rw [jointScalarMeasure, (jointContent A B hSC ξ).measure_eq isSetSemiring_jointRectangles
    generateFrom_jointRectangles (jointContent_isSigmaSubadditive A B hSC ξ) hmem]
  change jointRectVal A B ξ (S ×ˢ T) = _
  rw [jointRectVal_prod_diag A B hSC ξ hS hT]

/-- **`μ_ξ` on a rectangle, in norm² form.**  `μ_ξ(S ×ˢ T).toReal = ‖E_A(S)E_B(T)ξ‖²`. -/
theorem jointScalarMeasure_prod_norm_sq (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) (ξ : H) {S T : Set ℝ} (hS : MeasurableSet S)
    (hT : MeasurableSet T) :
    (jointScalarMeasure A B hSC ξ (S ×ˢ T)).toReal
      = ‖(A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ‖ ^ 2 := by
  rw [jointScalarMeasure_prod A B hSC ξ hS hT, ← jointRect_norm_sq_eq_diag A B hSC hS hT ξ]

/-- **`μ_ξ` is finite**, with total mass `‖ξ‖²`: `μ_ξ(univ) = μ_ξ(univ ×ˢ univ) = ‖ξ‖² < ∞`. -/
instance jointScalarMeasure_isFiniteMeasure (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) (ξ : H) :
    MeasureTheory.IsFiniteMeasure (jointScalarMeasure A B hSC ξ) := by
  constructor
  have hmem : (Set.univ ×ˢ Set.univ : Set (ℝ × ℝ)) ∈ jointRectangles :=
    ⟨Set.univ, Set.univ, MeasurableSet.univ, MeasurableSet.univ, rfl⟩
  rw [← Set.univ_prod_univ, jointScalarMeasure,
    (jointContent A B hSC ξ).measure_eq isSetSemiring_jointRectangles
      generateFrom_jointRectangles (jointContent_isSigmaSubadditive A B hSC ξ) hmem,
    jointContent_univ A B hSC ξ]
  exact ENNReal.ofReal_lt_top


end Spectra.QuantumMechanics.BornRule
