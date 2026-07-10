/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.SymmetricExtension
import Spectra.Operator.ConjugationCriterion

/-!
# Which partial von Neumann extensions are closed?

For a closed, symmetric, densely-defined `A : H →ₗ.[ℂ] H`, the partial von Neumann extension
`A_V = A*|_{D(A) ⊔ (1-V)F}` along an isometry `V : F →ₗᵢ[ℂ] N₋(A)` on `F ≤ N₊(A)` is closed
**iff** `F` is closed (`vonNeumannExtensionOn_isClosed_iff`). Together with
`Spectra.Operator.exists_eq_vonNeumannExtensionOn` (every symmetric extension is an `A_V`) and
`Spectra.Operator.vonNeumannExtensionOn_isSelfAdjoint_iff` this completes the textbook
classification: closed symmetric extensions ↔ isometries on **closed** subspaces of `N₊(A)`.

## Proof shapes

The engine is **graph-Pythagoras** (`Spectra.Operator.norm_sq_add_deficiency_decomposition`,
specialized here to the defect decomposition as `norm_sq_graph_defect`): on
`u = ψ + η - Vη`,

  `‖u‖² + ‖A_V u‖² = ‖ψ‖² + ‖Aψ‖² + 4‖η‖²`,

so the graph norm controls each component of the decomposition separately.

*⟸ (`F` closed ⟹ `A_V` closed)*: a graph-convergent sequence in `Γ(A_V)` has graph-Cauchy
decomposition components — `(ψₙ, Aψₙ)` Cauchy in `Γ(A)` (closed since `A` is), `ηₙ` Cauchy in
`F` (closed by hypothesis), `Vηₙ` Cauchy by isometry — and the limits reassemble to a point
of `Γ(A_V)`.

*⟹ (`A_V` closed ⟹ `F` closed)*: for `ηₙ → η` in `F`, the defect vectors `ηₙ - Vηₙ` form a
graph-convergent sequence in `Γ(A_V)` (isometry gives the `V`-limit `ξ`), so `η - ξ ∈ D(A_V)`;
decomposing it and comparing with the first von Neumann formula's **unique** decomposition
(`existsUnique_deficiency_decomposition`) forces `η ∈ F`.

## Main statements

* `norm_sq_graph_defect` — graph-Pythagoras on the defect decomposition.
* `vonNeumannExtensionOn_isClosed_of_isClosed` — `F` closed ⟹ `A_V` closed.
* `isClosed_of_vonNeumannExtensionOn_isClosed` — `A_V` closed ⟹ `F` closed.
* `vonNeumannExtensionOn_isClosed_iff` — **the characterization**.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975], Section X.1.
* [Akhiezer, Glazman, *Theory of Linear Operators in Hilbert Space*][akhiezer1993], Section 80.
-/

open Complex Filter Topology
open scoped InnerProductSpace

namespace Spectra.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →ₗ.[ℂ] H) {F : Submodule ℂ H}

/-! ### Graph-Pythagoras on the defect decomposition -/

/-- **Graph-Pythagoras for defect vectors**: on `u = ψ + η - Vη`,
`‖u‖² + ‖A_V u‖² = ‖ψ‖² + ‖Aψ‖² + 4‖η‖²` — the defect direction carries graph norm `2‖η‖`
from each of `η` and `Vη`. -/
theorem norm_sq_graph_defect (hdense : Dense (A.domain : Set H))
    (hF : F ≤ deficiencySubspacePlus A) (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A)
    (ψ : A.domain) (η : F) :
    ‖(ψ : H) + (η : H) - ((V η : deficiencySubspaceMinus A) : H)‖ ^ 2
      + ‖A ψ + I • (η : H) + I • ((V η : deficiencySubspaceMinus A) : H)‖ ^ 2
      = ‖(ψ : H)‖ ^ 2 + ‖A ψ‖ ^ 2 + 4 * ‖(η : H)‖ ^ 2 := by
  have h := norm_sq_add_deficiency_decomposition A hdense ψ ⟨(η : H), hF η.2⟩ (-(V η))
  simp only [Submodule.coe_neg] at h
  rw [smul_neg, sub_neg_eq_add, norm_neg, ← sub_eq_add_neg] at h
  have hVnorm : ‖((V η : deficiencySubspaceMinus A) : H)‖ = ‖(η : H)‖ := by
    rw [← Submodule.coe_norm, V.norm_map, Submodule.coe_norm]
  rw [hVnorm] at h
  linarith [h]

/-! ### `F` closed ⟹ `A_V` closed -/

/-- **A closed `F` gives a closed extension**: graph-Pythagoras transfers the graph-Cauchy
property of a convergent sequence in `Γ(A_V)` to its three decomposition components, whose
limits live in `Γ(A)` (closed), `F` (closed), and `N₋(A)` respectively, and reassemble. -/
theorem vonNeumannExtensionOn_isClosed_of_isClosed (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hclosed : IsClosed (A.graph : Set (H × H)))
    (hF : F ≤ deficiencySubspacePlus A) (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A)
    (hFc : IsClosed (F : Set H)) :
    (vonNeumannExtensionOn A hsym hdense hF V).IsClosed := by
  apply IsSeqClosed.isClosed
  rintro pn ⟨u, v⟩ hmem hlim
  choose un hun1 hun2 using fun n =>
    (LinearPMap.mem_graph_iff (vonNeumannExtensionOn A hsym hdense hF V)).mp (hmem n)
  have hu : Tendsto (fun n => ((un n : (vonNeumannExtensionOn A hsym hdense hF V).domain) : H))
      atTop (𝓝 u) := by
    have h := hlim.fst_nhds
    simpa only [← hun1] using h
  have hv : Tendsto (fun n => vonNeumannExtensionOn A hsym hdense hF V (un n)) atTop (𝓝 v) := by
    have h := hlim.snd_nhds
    simpa only [← hun2] using h
  -- decompose each `un n`
  choose xn ηn hdec using fun n =>
    vonNeumannDomainOn_cases A
      (show ((un n : (vonNeumannExtensionOn A hsym hdense hF V).domain) : H)
          ∈ vonNeumannDomainOn A V from (un n).2)
  -- the master estimate: graph distance controls all three components
  have hkey : ∀ m k : ℕ,
      ‖((un m : (vonNeumannExtensionOn A hsym hdense hF V).domain) : H)
          - ((un k : (vonNeumannExtensionOn A hsym hdense hF V).domain) : H)‖ ^ 2
        + ‖vonNeumannExtensionOn A hsym hdense hF V (un m)
            - vonNeumannExtensionOn A hsym hdense hF V (un k)‖ ^ 2
      = ‖((xn m - xn k : A.domain) : H)‖ ^ 2 + ‖A (xn m - xn k)‖ ^ 2
        + 4 * ‖((ηn m - ηn k : F) : H)‖ ^ 2 := by
    intro m k
    have hud : ((un m : (vonNeumannExtensionOn A hsym hdense hF V).domain) : H)
        - ((un k : (vonNeumannExtensionOn A hsym hdense hF V).domain) : H)
        = ((xn m - xn k : A.domain) : H) + ((ηn m - ηn k : F) : H)
          - ((V (ηn m - ηn k) : deficiencySubspaceMinus A) : H) := by
      rw [hdec m, hdec k, Submodule.coe_sub, Submodule.coe_sub, V.map_sub, Submodule.coe_sub]
      abel
    have hAd : vonNeumannExtensionOn A hsym hdense hF V (un m)
        - vonNeumannExtensionOn A hsym hdense hF V (un k)
        = A (xn m - xn k) + I • ((ηn m - ηn k : F) : H)
          + I • ((V (ηn m - ηn k) : deficiencySubspaceMinus A) : H) := by
      rw [vonNeumannExtensionOn_apply_add_defect A hsym hdense hF V (xn m) (ηn m)
          (un m) (hdec m),
        vonNeumannExtensionOn_apply_add_defect A hsym hdense hF V (xn k) (ηn k)
          (un k) (hdec k),
        A.map_sub, Submodule.coe_sub, V.map_sub, Submodule.coe_sub, smul_sub, smul_sub]
      abel
    have h := norm_sq_graph_defect A hdense hF V (xn m - xn k) (ηn m - ηn k)
    rw [← hud, ← hAd] at h
    exact h
  -- three Cauchy sequences from one estimate
  have hCu : CauchySeq fun n =>
      ((un n : (vonNeumannExtensionOn A hsym hdense hF V).domain) : H) := hu.cauchySeq
  have hCv : CauchySeq fun n => vonNeumannExtensionOn A hsym hdense hF V (un n) := hv.cauchySeq
  have hcomp : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m ≥ N, ∀ k ≥ N,
      ‖((xn m - xn k : A.domain) : H)‖ < ε ∧ ‖A (xn m - xn k)‖ < ε
        ∧ ‖((ηn m - ηn k : F) : H)‖ < ε := by
    intro ε hε
    rw [Metric.cauchySeq_iff] at hCu hCv
    obtain ⟨N₁, hN₁⟩ := hCu (ε / 2) (by positivity)
    obtain ⟨N₂, hN₂⟩ := hCv (ε / 2) (by positivity)
    refine ⟨max N₁ N₂, fun m hm k hk => ?_⟩
    have h1 := hN₁ m (le_trans (le_max_left _ _) hm) k (le_trans (le_max_left _ _) hk)
    have h2 := hN₂ m (le_trans (le_max_right _ _) hm) k (le_trans (le_max_right _ _) hk)
    rw [dist_eq_norm] at h1 h2
    have hk' := hkey m k
    have hsum : ‖((xn m - xn k : A.domain) : H)‖ ^ 2 + ‖A (xn m - xn k)‖ ^ 2
        + 4 * ‖((ηn m - ηn k : F) : H)‖ ^ 2 < ε ^ 2 / 2 := by
      rw [← hk']
      have _hb1 : ‖((un m : (vonNeumannExtensionOn A hsym hdense hF V).domain) : H)
          - ((un k : (vonNeumannExtensionOn A hsym hdense hF V).domain) : H)‖ < ε / 2 := h1
      have _hb2 : ‖vonNeumannExtensionOn A hsym hdense hF V (un m)
          - vonNeumannExtensionOn A hsym hdense hF V (un k)‖ < ε / 2 := h2
      nlinarith [norm_nonneg (((un m : (vonNeumannExtensionOn A hsym hdense hF V).domain) : H)
          - ((un k : (vonNeumannExtensionOn A hsym hdense hF V).domain) : H)),
        norm_nonneg (vonNeumannExtensionOn A hsym hdense hF V (un m)
          - vonNeumannExtensionOn A hsym hdense hF V (un k))]
    refine ⟨?_, ?_, ?_⟩ <;>
      nlinarith [norm_nonneg (((xn m - xn k : A.domain) : H)),
        norm_nonneg (A (xn m - xn k)), norm_nonneg (((ηn m - ηn k : F) : H)),
        sq_nonneg ε, hε]
  have hCxn : CauchySeq fun n => ((xn n : A.domain) : H) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcomp ε hε
    refine ⟨N, fun m hm k hk => ?_⟩
    rw [dist_eq_norm, ← Submodule.coe_sub]
    exact (hN m hm k hk).1
  have hCAxn : CauchySeq fun n => A (xn n) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcomp ε hε
    refine ⟨N, fun m hm k hk => ?_⟩
    rw [dist_eq_norm, ← A.map_sub]
    exact (hN m hm k hk).2.1
  have hCηn : CauchySeq fun n => ((ηn n : F) : H) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcomp ε hε
    refine ⟨N, fun m hm k hk => ?_⟩
    rw [dist_eq_norm, ← Submodule.coe_sub]
    exact (hN m hm k hk).2.2
  -- limits
  obtain ⟨xL, hx⟩ := cauchySeq_tendsto_of_complete hCxn
  obtain ⟨yL, hy⟩ := cauchySeq_tendsto_of_complete hCAxn
  obtain ⟨ηL, hη⟩ := cauchySeq_tendsto_of_complete hCηn
  -- the `A`-component lands in the closed graph of `A`
  have hpair : (xL, yL) ∈ A.graph :=
    hclosed.mem_of_tendsto (hx.prodMk_nhds hy)
      (Filter.Eventually.of_forall fun n => A.mem_graph (xn n))
  rw [LinearPMap.mem_graph_iff] at hpair
  obtain ⟨x', hx'1, hx'2⟩ := hpair
  -- the `F`-component lands in the closed `F`
  have hηLF : ηL ∈ F :=
    hFc.mem_of_tendsto hη (Filter.Eventually.of_forall fun n => (ηn n).2)
  -- the `V`-component converges by isometry
  have hVlim : Tendsto (fun n => ((V (ηn n) : deficiencySubspaceMinus A) : H)) atTop
      (𝓝 ((V ⟨ηL, hηLF⟩ : deficiencySubspaceMinus A) : H)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hnorm : ∀ n, ‖((V (ηn n) : deficiencySubspaceMinus A) : H)
        - ((V ⟨ηL, hηLF⟩ : deficiencySubspaceMinus A) : H)‖
        = ‖((ηn n : F) : H) - ηL‖ := by
      intro n
      rw [← Submodule.coe_sub, ← V.map_sub, ← Submodule.coe_norm, V.norm_map,
        Submodule.coe_norm, Submodule.coe_sub]
    rw [show (fun n => ‖((V (ηn n) : deficiencySubspaceMinus A) : H)
        - ((V ⟨ηL, hηLF⟩ : deficiencySubspaceMinus A) : H)‖)
        = fun n => ‖((ηn n : F) : H) - ηL‖ from funext hnorm]
    exact (tendsto_iff_norm_sub_tendsto_zero.mp hη)
  -- identify the limit pair
  have hueq : u = (x' : H) + ηL - ((V ⟨ηL, hηLF⟩ : deficiencySubspaceMinus A) : H) := by
    have hulim2 : Tendsto
        (fun n => ((un n : (vonNeumannExtensionOn A hsym hdense hF V).domain) : H)) atTop
        (𝓝 ((x' : H) + ηL - ((V ⟨ηL, hηLF⟩ : deficiencySubspaceMinus A) : H))) := by
      rw [show (fun n => ((un n : (vonNeumannExtensionOn A hsym hdense hF V).domain) : H))
          = fun n => ((xn n : A.domain) : H) + ((ηn n : F) : H)
            - ((V (ηn n) : deficiencySubspaceMinus A) : H) from funext hdec]
      have hx1 : (x' : H) = xL := hx'1
      have hx'' : Tendsto (fun n => ((xn n : A.domain) : H)) atTop (𝓝 (x' : H)) := by
        rw [hx1]; exact hx
      exact (hx''.add hη).sub hVlim
    exact tendsto_nhds_unique hu hulim2
  have hveq : v = A x' + I • ηL + I • ((V ⟨ηL, hηLF⟩ : deficiencySubspaceMinus A) : H) := by
    have hvlim2 : Tendsto (fun n => vonNeumannExtensionOn A hsym hdense hF V (un n)) atTop
        (𝓝 (A x' + I • ηL + I • ((V ⟨ηL, hηLF⟩ : deficiencySubspaceMinus A) : H))) := by
      rw [show (fun n => vonNeumannExtensionOn A hsym hdense hF V (un n))
          = fun n => A (xn n) + I • ((ηn n : F) : H)
            + I • ((V (ηn n) : deficiencySubspaceMinus A) : H) from
        funext fun n =>
          vonNeumannExtensionOn_apply_add_defect A hsym hdense hF V (xn n) (ηn n)
            (un n) (hdec n)]
      have hy2 : A x' = yL := hx'2
      have hy'' : Tendsto (fun n => A (xn n)) atTop (𝓝 (A x')) := by
        rw [hy2]; exact hy
      exact (hy''.add (hη.const_smul I)).add (hVlim.const_smul I)
    exact tendsto_nhds_unique hv hvlim2
  -- reassemble
  have humem : u ∈ vonNeumannDomainOn A V := by
    rw [hueq]
    exact mem_vonNeumannDomainOn A V x' ⟨ηL, hηLF⟩
  refine (LinearPMap.mem_graph_iff (vonNeumannExtensionOn A hsym hdense hF V)).mpr
    ⟨⟨u, humem⟩, rfl, ?_⟩
  rw [vonNeumannExtensionOn_apply_add_defect A hsym hdense hF V x' ⟨ηL, hηLF⟩
    ⟨u, humem⟩ hueq]
  exact hveq.symm

/-! ### `A_V` closed ⟹ `F` closed -/

/-- **A closed extension forces `F` closed**: for `ηₙ → η` in `F`, the defect vectors
`ηₙ - Vηₙ` graph-converge (isometry supplies the `V`-limit), so the limit lies in `D(A_V)`;
its unique first-formula decomposition pins `η` inside `F`. -/
theorem isClosed_of_vonNeumannExtensionOn_isClosed (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hclosed : IsClosed (A.graph : Set (H × H)))
    (hF : F ≤ deficiencySubspacePlus A) (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A)
    (hAV : (vonNeumannExtensionOn A hsym hdense hF V).IsClosed) :
    IsClosed (F : Set H) := by
  apply IsSeqClosed.isClosed
  intro ηs η hmemF hηlim
  -- the `V`-images converge by isometry
  have hCV : CauchySeq fun n => ((V ⟨ηs n, hmemF n⟩ : deficiencySubspaceMinus A) : H) := by
    have hCη : CauchySeq ηs := hηlim.cauchySeq
    rw [Metric.cauchySeq_iff] at hCη ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hCη ε hε
    refine ⟨N, fun m hm k hk => ?_⟩
    have hd : dist ((V ⟨ηs m, hmemF m⟩ : deficiencySubspaceMinus A) : H)
        ((V ⟨ηs k, hmemF k⟩ : deficiencySubspaceMinus A) : H) = dist (ηs m) (ηs k) := by
      rw [dist_eq_norm, dist_eq_norm, ← Submodule.coe_sub, ← V.map_sub,
        ← Submodule.coe_norm, V.norm_map, Submodule.coe_norm, Submodule.coe_sub]
    rw [hd]
    exact hN m hm k hk
  obtain ⟨ξ, hξlim⟩ := cauchySeq_tendsto_of_complete hCV
  have hξN : ξ ∈ deficiencySubspaceMinus A :=
    (deficiencySubspaceMinus_isClosed A hdense).mem_of_tendsto hξlim
      (Filter.Eventually.of_forall fun n => (V ⟨ηs n, hmemF n⟩).2)
  have hηN : η ∈ deficiencySubspacePlus A :=
    (deficiencySubspacePlus_isClosed A hdense).mem_of_tendsto hηlim
      (Filter.Eventually.of_forall fun n => hF (hmemF n))
  -- the defect vectors are graph points of `A_V`
  have humem : ∀ n, ηs n - ((V ⟨ηs n, hmemF n⟩ : deficiencySubspaceMinus A) : H)
      ∈ vonNeumannDomainOn A V := fun n => by
    simpa using mem_vonNeumannDomainOn A V 0 ⟨ηs n, hmemF n⟩
  have hval : ∀ n, vonNeumannExtensionOn A hsym hdense hF V
      ⟨ηs n - ((V ⟨ηs n, hmemF n⟩ : deficiencySubspaceMinus A) : H), humem n⟩
      = I • ηs n + I • ((V ⟨ηs n, hmemF n⟩ : deficiencySubspaceMinus A) : H) := by
    intro n
    have h := vonNeumannExtensionOn_apply_add_defect A hsym hdense hF V 0 ⟨ηs n, hmemF n⟩
      ⟨ηs n - ((V ⟨ηs n, hmemF n⟩ : deficiencySubspaceMinus A) : H), humem n⟩
      (by simp)
    simpa using h
  -- the graph limit `(η - ξ, iη + iξ)` lies in the closed graph
  have hseq : Tendsto (fun n =>
      ((ηs n - ((V ⟨ηs n, hmemF n⟩ : deficiencySubspaceMinus A) : H),
        vonNeumannExtensionOn A hsym hdense hF V
          ⟨ηs n - ((V ⟨ηs n, hmemF n⟩ : deficiencySubspaceMinus A) : H), humem n⟩) : H × H))
      atTop (𝓝 (η - ξ, I • η + I • ξ)) := by
    apply Tendsto.prodMk_nhds
    · exact hηlim.sub hξlim
    · rw [show (fun n => vonNeumannExtensionOn A hsym hdense hF V
          ⟨ηs n - ((V ⟨ηs n, hmemF n⟩ : deficiencySubspaceMinus A) : H), humem n⟩)
          = fun n => I • ηs n + I • ((V ⟨ηs n, hmemF n⟩ : deficiencySubspaceMinus A) : H) from
        funext hval]
      exact (hηlim.const_smul I).add (hξlim.const_smul I)
  have hpair : (η - ξ, I • η + I • ξ)
      ∈ (vonNeumannExtensionOn A hsym hdense hF V).graph :=
    hAV.mem_of_tendsto hseq (Filter.Eventually.of_forall fun n =>
      (vonNeumannExtensionOn A hsym hdense hF V).mem_graph
        ⟨ηs n - ((V ⟨ηs n, hmemF n⟩ : deficiencySubspaceMinus A) : H), humem n⟩)
  rw [LinearPMap.mem_graph_iff] at hpair
  obtain ⟨w, hw1, _hw2⟩ := hpair
  -- decompose `η - ξ` inside `D(A_V)` and compare with the first-formula decomposition
  have hwdom : η - ξ ∈ vonNeumannDomainOn A V := by
    have h := w.2
    rwa [show ((w : (vonNeumannExtensionOn A hsym hdense hF V).domain) : H) = η - ξ from hw1]
      at h
  obtain ⟨x, η', hcases⟩ := vonNeumannDomainOn_cases A hwdom
  have huadj : η - ξ ∈ A.adjoint.domain :=
    A.adjoint.domain.sub_mem
      (mem_adjoint_domain_of_mem_deficiencySubspacePlus A hηN)
      (mem_adjoint_domain_of_mem_deficiencySubspaceMinus A hξN)
  have huniq := existsUnique_deficiency_decomposition A hsym hdense hclosed huadj
  have h1 : η - ξ = ((0 : A.domain) : H) + ((⟨η, hηN⟩ :
      deficiencySubspacePlus A) : H) + ((-(⟨ξ, hξN⟩ : deficiencySubspaceMinus A) :
        deficiencySubspaceMinus A) : H) := by
    change η - ξ = 0 + η + (-ξ)
    rw [zero_add, sub_eq_add_neg]
  have h2 : η - ξ = ((x : H)) + ((⟨(η' : H), hF η'.2⟩ : deficiencySubspacePlus A) : H)
      + ((-(V η') : deficiencySubspaceMinus A) : H) := by
    calc η - ξ = (x : H) + (η' : H) - ((V η' : deficiencySubspaceMinus A) : H) := hcases
      _ = ((x : H)) + ((⟨(η' : H), hF η'.2⟩ : deficiencySubspacePlus A) : H)
          + ((-(V η') : deficiencySubspaceMinus A) : H) := by
        rw [Submodule.coe_neg, sub_eq_add_neg]
  have hcomp := huniq.unique
    (y₁ := ⟨0, ⟨η, hηN⟩, -(⟨ξ, hξN⟩ : deficiencySubspaceMinus A)⟩)
    (y₂ := ⟨x, ⟨(η' : H), hF η'.2⟩, -(V η')⟩) h1 h2
  have hplus : (⟨η, hηN⟩ : deficiencySubspacePlus A) = ⟨(η' : H), hF η'.2⟩ :=
    congrArg (fun p => p.2.1) hcomp
  have : η = (η' : H) := Subtype.ext_iff.mp hplus
  rw [this]
  exact η'.2

/-! ### The characterization -/

/-- **Closedness of the partial von Neumann extension, characterized** (closed `A`):
`A_V` is closed iff `F` is closed. -/
theorem vonNeumannExtensionOn_isClosed_iff (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hclosed : IsClosed (A.graph : Set (H × H)))
    (hF : F ≤ deficiencySubspacePlus A) (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    (vonNeumannExtensionOn A hsym hdense hF V).IsClosed ↔ IsClosed (F : Set H) :=
  ⟨isClosed_of_vonNeumannExtensionOn_isClosed A hsym hdense hclosed hF V,
   vonNeumannExtensionOn_isClosed_of_isClosed A hsym hdense hclosed hF V⟩

end Spectra.Operator
