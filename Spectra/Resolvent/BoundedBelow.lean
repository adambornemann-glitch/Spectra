/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Spectrum

/-!
# Bounded below ⟹ resolvent point

The parametric core shared by the library's resolvent constructions: for a densely-defined
operator with `c·‖ψ‖ ≤ ‖(A - z)ψ‖` for some `c > 0` (a *bounded-below* or *quasi-regular*
point `z`), the range of `A - z` is closed (given a closed graph), injectivity is automatic,
and surjectivity upgrades to a genuine two-sided bounded inverse — `z ∈ resolventSet A`
(`mem_resolventSet_of_boundedBelow_surjective`). For self-adjoint `A` and **real** `λ`,
density of the range is automatic (`range_dense_of_boundedBelow_real` — anything orthogonal
to `ran(A - λ)` is a `λ`-eigenvector, killed by the bound), so a real bounded-below point is
always a resolvent point (`mem_resolventSet_of_boundedBelow_real`).

This is the third instantiation of the closed-range/dense-range/`mkContinuous` architecture
(after `Resolvent/Range.lean`'s `resolvent` at `|Im z|` and
`Resolvent/NumericalRangeSpectrum.lean`'s `numResolvent` at `dist(z, W(A))`), stated with the
lower bound as an explicit hypothesis so that both prior instances — and the Weyl-criterion
and regularity-field arguments downstream — can consume a single parametric core. The
existing files are deliberately left untouched.

## Main statements

* `range_isClosed_of_boundedBelow` — closed graph + lower bound ⟹ `ran(A - z)` closed.
  No symmetry hypothesis (the bound replaces `op_lower_bound` entirely).
* `range_dense_of_boundedBelow_real` — self-adjoint + lower bound at real `λ` ⟹ `ran(A - λ)`
  dense.
* `sub_smul_injective_of_boundedBelow` — the bound forces injectivity of `A - z`.
* `mem_resolventSet_of_boundedBelow_surjective` — lower bound + surjectivity ⟹
  `z ∈ resolventSet A`, with resolvent norm at most `1/c`.
* `mem_resolventSet_of_boundedBelow_real` — **the packaging**: for self-adjoint `A`, a real
  bounded-below point is a resolvent point.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII.3.
* [Weidmann, *Linear Operators in Hilbert Spaces*][weidmann1980], Section 8.1.
-/

open InnerProductSpace Complex Filter Topology
open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.Resolvent

/-! ### Closed range from a lower bound -/

/-- **Closed graph + lower bound ⟹ closed range.** The parametric form of
`Spectra.YosidaHille.op_range_isClosed`: the symmetry hypothesis is gone — it was consumed
only to produce the off-axis lower bound, which is now the hypothesis `hbound`. -/
lemma range_isClosed_of_boundedBelow {A : H →ₗ.[ℂ] H}
    (hgr : IsClosed (A.graph : Set (H × H))) (z : ℂ) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ ψ : A.domain, c * ‖(ψ : H)‖ ≤ ‖A ψ - z • (ψ : H)‖) :
    IsClosed (Set.range fun ψ : A.domain => A ψ - z • (ψ : H)) := by
  apply IsSeqClosed.isClosed
  intro φn φ hmem hlim
  choose xn hxn using hmem
  have hφC : CauchySeq φn := hlim.cauchySeq
  have hCx : CauchySeq fun n => (xn n : H) := by
    rw [Metric.cauchySeq_iff] at hφC ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hφC (c * ε) (by positivity)
    refine ⟨N, fun m hm k hk => ?_⟩
    have hsub : (↑(xn m) - ↑(xn k) : H) ∈ A.domain := A.domain.sub_mem (xn m).2 (xn k).2
    have hAsub : A ⟨↑(xn m) - ↑(xn k), hsub⟩ - z • (↑(xn m) - ↑(xn k)) = φn m - φn k := by
      have hms : A ⟨↑(xn m) - ↑(xn k), hsub⟩ = A (xn m) - A (xn k) := by
        have := A.map_sub (xn m) (xn k); convert this using 2
      rw [hms, smul_sub, ← hxn m, ← hxn k]; abel_nf
      grind only
    have hlb := hbound ⟨↑(xn m) - ↑(xn k), hsub⟩
    rw [hAsub] at hlb
    rw [dist_eq_norm]
    have hd : ‖φn m - φn k‖ < c * ε := by rw [← dist_eq_norm]; exact hN m hm k hk
    have : c * ‖(↑(xn m) - ↑(xn k) : H)‖ < c * ε := lt_of_le_of_lt hlb hd
    exact lt_of_mul_lt_mul_left this (le_of_lt hc)
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hCx
  have hAx : Tendsto (fun n => A (xn n)) atTop (𝓝 (φ + z • u)) := by
    have heq : (fun n => A (xn n)) = fun n => φn n + z • (↑(xn n) : H) := by
      funext n; rw [← hxn n]; abel_nf; grind only
    rw [heq]; exact hlim.add (hu.const_smul z)
  have hpair : (u, φ + z • u) ∈ A.graph :=
    hgr.mem_of_tendsto (hu.prodMk_nhds hAx)
      (Filter.Eventually.of_forall fun n => A.mem_graph (xn n))
  rw [LinearPMap.mem_graph_iff] at hpair
  obtain ⟨y, hy1, hy2⟩ := hpair
  have e1 : (y : H) = u := hy1
  have e2 : A y = φ + z • u := hy2
  exact ⟨y, by simp only [e2, e1]; abel⟩

/-! ### Dense range from a lower bound, at real `λ` -/

/-- **Self-adjoint + lower bound at real `λ` ⟹ dense range.** The real-axis form of
`Spectra.YosidaHille.op_range_dense`: an orthogonal vector is placed in `D(A*) = D(A)` with
`Aχ = λ̄χ = λχ` by the generic adjoint-domain-membership argument, and the lower bound (in
place of `|Im z|`) kills it. -/
lemma range_dense_of_boundedBelow_real {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (lam : ℝ) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ ψ : A.domain, c * ‖(ψ : H)‖ ≤ ‖A ψ - (lam : ℂ) • (ψ : H)‖) :
    Dense (Set.range fun ψ : A.domain => A ψ - (lam : ℂ) • (ψ : H)) := by
  have hdense : Dense (A.domain : Set H) := hA.dense_domain
  have hadj : A.adjoint = A := LinearPMap.isSelfAdjoint_def.mp hA
  set R : Submodule ℂ H := LinearMap.range (A.toFun - (lam : ℂ) • A.domain.subtype) with _hRdef
  have hRset : (Set.range fun x : A.domain => A x - (lam : ℂ) • (x : H)) = (R : Set H) := by
    ext y; constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, by simp [LinearMap.sub_apply]⟩
    · rintro ⟨x, rfl⟩; exact ⟨x, by simp [LinearMap.sub_apply]⟩
  rw [hRset]
  have hbot : Rᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro χ hχ
    have horth : ∀ x : A.domain, ⟪A x - (lam : ℂ) • (x : H), χ⟫_ℂ = 0 := by
      intro x; exact hχ _ ⟨x, by simp [LinearMap.sub_apply]⟩
    -- χ lies in the adjoint domain (the functional x ↦ ⟪χ, A x⟫ is continuous)
    have hcont : Continuous fun x : A.domain => ⟪χ, A x⟫_ℂ := by
      have hfun : (fun x : A.domain => ⟪χ, A x⟫_ℂ)
          = fun x : A.domain => (lam : ℂ) * ⟪χ, (x : H)⟫_ℂ := by
        funext x
        have h0 := horth x
        rw [inner_sub_left, inner_smul_left, sub_eq_zero] at h0
        have hc' := congrArg (starRingEnd ℂ) h0
        rwa [inner_conj_symm, map_mul, Complex.conj_conj, inner_conj_symm] at hc'
      rw [hfun]
      exact continuous_const.mul (continuous_const.inner A.domain.subtypeL.continuous)
    have hχdom : χ ∈ A.adjoint.domain :=
      (LinearPMap.mem_adjoint_domain_iff A χ).mpr hcont
    -- A†χ = λ̄χ, pinned by orthogonality to the dense domain
    have hval : A.adjoint ⟨χ, hχdom⟩ = conj (lam : ℂ) • χ := by
      have hkey : ∀ x : A.domain,
          ⟪A.adjoint ⟨χ, hχdom⟩ - conj (lam : ℂ) • χ, (x : H)⟫_ℂ = 0 := by
        intro x
        have hfa := LinearPMap.adjoint_isFormalAdjoint hdense ⟨χ, hχdom⟩ x
        rw [inner_sub_left, hfa, inner_smul_left, Complex.conj_conj]
        have h0 := horth x
        rw [inner_sub_left, inner_smul_left, sub_eq_zero] at h0
        have hc' := congrArg (starRingEnd ℂ) h0
        rw [inner_conj_symm, map_mul, Complex.conj_conj, inner_conj_symm] at hc'
        rw [hc']; ring
      set d := A.adjoint ⟨χ, hχdom⟩ - conj (lam : ℂ) • χ with hd
      have hd0 : d = 0 := by
        have hg : Continuous fun w => ⟪d, w⟫_ℂ := continuous_const.inner continuous_id
        have hg0 : (fun w => ⟪d, w⟫_ℂ) = fun _ => (0 : ℂ) :=
          Continuous.ext_on hdense hg continuous_const fun w hw => by
            simpa using hkey ⟨w, hw⟩
        have : ⟪d, d⟫_ℂ = 0 := by have := congrFun hg0 d; simpa using this
        exact inner_self_eq_zero.mp this
      rwa [hd, sub_eq_zero] at hd0
    -- transport across A† = A, drop the conjugate (λ is real), kill via the bound
    have hχdomA : χ ∈ A.domain := hadj ▸ hχdom
    have hAχ : A ⟨χ, hχdomA⟩ = conj (lam : ℂ) • χ := by
      have hle := (le_of_eq hadj).2 (x := ⟨χ, hχdom⟩) (y := ⟨χ, hχdomA⟩) rfl
      rw [← hle]; exact hval
    rw [Complex.conj_ofReal] at hAχ
    have hzero : A ⟨χ, hχdomA⟩ - (lam : ℂ) • χ = 0 := by rw [hAχ, sub_self]
    have hlb := hbound ⟨χ, hχdomA⟩
    rw [hzero, norm_zero] at hlb
    have : ‖χ‖ ≤ 0 := by nlinarith [norm_nonneg χ, hlb, hc]
    simpa using le_antisymm this (norm_nonneg χ)
  have hcl : R.topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hbot, Submodule.bot_orthogonal_eq_top]
  exact (Submodule.dense_iff_topologicalClosure_eq_top).mpr hcl

/-! ### Injectivity and the two-sided inverse -/

omit [CompleteSpace H] in
/-- The lower bound forces injectivity of `A - z`. -/
lemma sub_smul_injective_of_boundedBelow {A : H →ₗ.[ℂ] H} (z : ℂ) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ ψ : A.domain, c * ‖(ψ : H)‖ ≤ ‖A ψ - z • (ψ : H)‖)
    {ψ ψ' : A.domain} (h : A ψ - z • (ψ : H) = A ψ' - z • (ψ' : H)) : ψ = ψ' := by
  have h0 : A (ψ - ψ') - z • ((ψ - ψ' : A.domain) : H) = 0 := by
    calc A (ψ - ψ') - z • ((ψ - ψ' : A.domain) : H)
        = (A ψ - z • (ψ : H)) - (A ψ' - z • (ψ' : H)) := by
          rw [A.map_sub, Submodule.coe_sub, smul_sub]; abel
      _ = 0 := by rw [h, sub_self]
  have hlb := hbound (ψ - ψ')
  rw [h0, norm_zero] at hlb
  have hnorm : ‖((ψ - ψ' : A.domain) : H)‖ = 0 := by
    have h1 : ‖((ψ - ψ' : A.domain) : H)‖ ≤ 0 := by
      nlinarith [norm_nonneg ((ψ - ψ' : A.domain) : H)]
    exact le_antisymm h1 (norm_nonneg _)
  have hzero : (ψ - ψ' : A.domain) = 0 :=
    Subtype.ext (by simpa using norm_eq_zero.mp hnorm)
  exact sub_eq_zero.mp hzero

omit [CompleteSpace H] in
/-- Lower bound + surjectivity give existence and uniqueness of the resolvent solution. -/
lemma existsUnique_sub_smul_eq_of_boundedBelow {A : H →ₗ.[ℂ] H} (z : ℂ) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ ψ : A.domain, c * ‖(ψ : H)‖ ≤ ‖A ψ - z • (ψ : H)‖)
    (hsurj : ∀ φ : H, ∃ ψ : A.domain, A ψ - z • (ψ : H) = φ) (φ : H) :
    ∃! ψ : A.domain, A ψ - z • (ψ : H) = φ := by
  obtain ⟨ψ, hψ⟩ := hsurj φ
  exact ⟨ψ, hψ, fun ψ' hψ' =>
    sub_smul_injective_of_boundedBelow z hc hbound (hψ'.trans hψ.symm)⟩

section Gluing

variable {A : H →ₗ.[ℂ] H} (z : ℂ) {c : ℝ} (hc : 0 < c)
  (hbound : ∀ ψ : A.domain, c * ‖(ψ : H)‖ ≤ ‖A ψ - z • (ψ : H)‖)
  (hsurj : ∀ φ : H, ∃ ψ : A.domain, A ψ - z • (ψ : H) = φ)

/-- The vector `ψ ∈ dom(A)` solving `(A - z)ψ = φ`. -/
private noncomputable def bbSolution (φ : H) : H :=
  ((Classical.choose (existsUnique_sub_smul_eq_of_boundedBelow z hc hbound hsurj φ).exists :
      A.domain) : H)

omit [CompleteSpace H] in
private lemma bbSolution_mem (φ : H) : bbSolution z hc hbound hsurj φ ∈ A.domain :=
  (Classical.choose (existsUnique_sub_smul_eq_of_boundedBelow z hc hbound hsurj φ).exists :
      A.domain).property

omit [CompleteSpace H] in
private lemma bbSolution_eq (φ : H) :
    A ⟨bbSolution z hc hbound hsurj φ, bbSolution_mem z hc hbound hsurj φ⟩
      - z • bbSolution z hc hbound hsurj φ = φ :=
  Classical.choose_spec (existsUnique_sub_smul_eq_of_boundedBelow z hc hbound hsurj φ).exists

omit [CompleteSpace H] in
private lemma bbSolution_add (φ₁ φ₂ : H) :
    bbSolution z hc hbound hsurj (φ₁ + φ₂)
      = bbSolution z hc hbound hsurj φ₁ + bbSolution z hc hbound hsurj φ₂ := by
  set a := bbSolution z hc hbound hsurj φ₁
  set b := bbSolution z hc hbound hsurj φ₂
  have ha_mem := bbSolution_mem z hc hbound hsurj φ₁
  have hb_mem := bbSolution_mem z hc hbound hsurj φ₂
  have ha_eq := bbSolution_eq z hc hbound hsurj φ₁
  have hb_eq := bbSolution_eq z hc hbound hsurj φ₂
  have hab_mem : a + b ∈ A.domain := A.domain.add_mem ha_mem hb_mem
  have hab_eq : A ⟨a + b, hab_mem⟩ - z • (a + b) = φ₁ + φ₂ := by
    have op_add : A ⟨a + b, hab_mem⟩ = A ⟨a, ha_mem⟩ + A ⟨b, hb_mem⟩ := by
      rw [← A.map_add]; rfl
    rw [op_add, smul_add]
    rw [show A ⟨a, ha_mem⟩ + A ⟨b, hb_mem⟩ - (z • a + z • b)
          = (A ⟨a, ha_mem⟩ - z • a) + (A ⟨b, hb_mem⟩ - z • b) by abel]
    rw [ha_eq, hb_eq]
  have huniq := (existsUnique_sub_smul_eq_of_boundedBelow z hc hbound hsurj (φ₁ + φ₂)).unique
    (bbSolution_eq z hc hbound hsurj (φ₁ + φ₂)) hab_eq
  exact congrArg Subtype.val huniq

omit [CompleteSpace H] in
private lemma bbSolution_smul (r : ℂ) (φ : H) :
    bbSolution z hc hbound hsurj (r • φ) = r • bbSolution z hc hbound hsurj φ := by
  set s := bbSolution z hc hbound hsurj φ
  have hs_mem := bbSolution_mem z hc hbound hsurj φ
  have hs_eq := bbSolution_eq z hc hbound hsurj φ
  have hcs_mem : r • s ∈ A.domain := A.domain.smul_mem r hs_mem
  have hcs_eq : A ⟨r • s, hcs_mem⟩ - z • (r • s) = r • φ := by
    have op_smul : A ⟨r • s, hcs_mem⟩ = r • A ⟨s, hs_mem⟩ := by
      rw [← A.map_smul]; rfl
    rw [op_smul, smul_comm z r, ← smul_sub, hs_eq]
  have huniq := (existsUnique_sub_smul_eq_of_boundedBelow z hc hbound hsurj (r • φ)).unique
    (bbSolution_eq z hc hbound hsurj (r • φ)) hcs_eq
  exact congrArg Subtype.val huniq

omit [CompleteSpace H] in
private lemma bbSolution_norm_le (φ : H) :
    ‖bbSolution z hc hbound hsurj φ‖ ≤ (1 / c) * ‖φ‖ := by
  have hb := hbound ⟨bbSolution z hc hbound hsurj φ, bbSolution_mem z hc hbound hsurj φ⟩
  rw [bbSolution_eq z hc hbound hsurj φ] at hb
  calc ‖bbSolution z hc hbound hsurj φ‖
      = (1 / c) * (c * ‖bbSolution z hc hbound hsurj φ‖) := by field_simp
    _ ≤ (1 / c) * ‖φ‖ := by
        apply mul_le_mul_of_nonneg_left hb
        positivity

omit [CompleteSpace H] in
include hc hbound hsurj in
/-- **Lower bound + surjectivity ⟹ resolvent point.** The generic gluing: the solution map is
linear (by uniqueness) and bounded by `1/c` (by the lower bound), so `LinearMap.mkContinuous`
produces a genuine two-sided bounded inverse of `A - z`. -/
theorem mem_resolventSet_of_boundedBelow_surjective : z ∈ resolventSet A := by
  refine ⟨LinearMap.mkContinuous
    { toFun := bbSolution z hc hbound hsurj
      map_add' := bbSolution_add z hc hbound hsurj
      map_smul' := fun r φ => by simpa using bbSolution_smul z hc hbound hsurj r φ }
    (1 / c) (bbSolution_norm_le z hc hbound hsurj), ?_, ?_⟩
  · intro ψ
    have heq := bbSolution_eq z hc hbound hsurj (A ψ - z • (ψ : H))
    have huniq := (existsUnique_sub_smul_eq_of_boundedBelow z hc hbound hsurj
      (A ψ - z • (ψ : H))).unique heq rfl
    exact congrArg Subtype.val huniq
  · intro φ
    exact ⟨bbSolution_mem z hc hbound hsurj φ, bbSolution_eq z hc hbound hsurj φ⟩

end Gluing

/-! ### The real self-adjoint packaging -/

/-- **A real bounded-below point of a self-adjoint operator is a resolvent point**: the range
of `A - λ` is closed (`range_isClosed_of_boundedBelow`) and dense
(`range_dense_of_boundedBelow_real`), hence all of `H`, and the gluing applies. -/
theorem mem_resolventSet_of_boundedBelow_real {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (lam : ℝ) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ ψ : A.domain, c * ‖(ψ : H)‖ ≤ ‖A ψ - (lam : ℂ) • (ψ : H)‖) :
    (lam : ℂ) ∈ resolventSet A := by
  have hclR := range_isClosed_of_boundedBelow hA.isClosed (lam : ℂ) hc hbound
  have hdsR := range_dense_of_boundedBelow_real hA lam hc hbound
  have hsurj : ∀ φ : H, ∃ ψ : A.domain, A ψ - (lam : ℂ) • (ψ : H) = φ := by
    intro φ
    have hmem : φ ∈ Set.range fun x : A.domain => A x - (lam : ℂ) • (x : H) := by
      rw [← hclR.closure_eq, hdsR.closure_eq]; trivial
    exact hmem
  exact mem_resolventSet_of_boundedBelow_surjective (lam : ℂ) hc hbound hsurj

end Spectra.Resolvent
