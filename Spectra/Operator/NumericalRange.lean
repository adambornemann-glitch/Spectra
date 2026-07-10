/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.NormExpansion
/-!
# The numerical range of an unbounded operator

The **numerical range** `W(A) = {⟪ψ, Aψ⟫ : ψ ∈ dom A, ‖ψ‖ = 1}` of an operator. For symmetric
`A` it is real, and it controls the growth of `(A - z)`: `dist(z, W(A)) · ‖ψ‖ ≤ ‖(A - z)ψ‖` for
every `ψ ∈ dom A`. This generalizes `Resolvent.lower_bound_estimate` (which only exploits
`|Im z|`, the special case `W(A) ⊆ ℝ` gives via `dist(z, ℝ) = |Im z|`) to a bound that is sharp
even for real `z` outside the numerical range — e.g. below the bottom of a semibounded operator's
spectrum.

## Main definitions

* `Spectra.Operator.numericalRange`

## Main results

* `numericalRange_subset_range_ofReal`: `W(A) ⊆ ℝ` for symmetric `A`.
* `infDist_mul_norm_le_norm_sub_smul`: `dist(z, W(A)) · ‖ψ‖ ≤ ‖Aψ - zψ‖`, for any operator
  (symmetric or not).
* `injOn_sub_smul_of_notMem_closure_numericalRange`: `A - z` is injective whenever `z` lies
  strictly outside `closure (W(A))`.
* `numericalRange_range_isClosed`: `ran(A - z)` is closed for self-adjoint `A` whenever `z` lies
  outside `closure (W(A))` — the numerical-range analogue of `Spectra.YosidaHille.op_range_isClosed`
  (which only reaches the imaginary axis).
* `numericalRange_conj_notMem_of_notMem`: `closure (W(A))` is conjugation-invariant for symmetric
  `A` (it is real), so `z ∉ closure (W(A))` alone already excludes `conj z` too.
* `numericalRange_range_dense`: `ran(A - z)` is dense for self-adjoint `A` whenever `z` lies
  outside `closure (W(A))` — the numerical-range analogue of `Spectra.YosidaHille.op_range_dense`.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII, Problem 8.
* [Kato, *Perturbation Theory for Linear Operators*][kato1995], Section V.3.
-/
open scoped InnerProductSpace ComplexConjugate
open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

namespace Spectra.Operator

/-- The **numerical range** `W(A) = {⟪ψ, Aψ⟫ : ψ ∈ dom A, ‖ψ‖ = 1}` of an operator `A`. -/
def numericalRange (A : H →ₗ.[ℂ] H) : Set ℂ :=
  {z | ∃ ψ : A.domain, ‖(ψ : H)‖ = 1 ∧ ⟪(ψ : H), A ψ⟫_ℂ = z}

/-- For a symmetric operator, the numerical range is real. -/
lemma numericalRange_subset_range_ofReal {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) :
    numericalRange A ⊆ Set.range ((↑) : ℝ → ℂ) := by
  rintro z ⟨ψ, -, rfl⟩
  refine ⟨(⟪(ψ : H), A ψ⟫_ℂ).re, ?_⟩
  have hswap : ⟪(ψ : H), A ψ⟫_ℂ = ⟪A ψ, (ψ : H)⟫_ℂ := (hsym ψ ψ).symm
  have him : (⟪A ψ, (ψ : H)⟫_ℂ).im = 0 :=
    Spectra.Resolvent.inner_self_im_eq_zero_of_symmetric hsym ψ
  rw [hswap, ← Complex.re_add_im ⟪A ψ, (ψ : H)⟫_ℂ, him]
  simp

/-- The Rayleigh quotient of any nonzero vector in the domain lies in the numerical range. -/
lemma rayleighQuotient_mem_numericalRange {A : H →ₗ.[ℂ] H} {ψ : H} (hψ : ψ ∈ A.domain)
    (hne : ψ ≠ 0) : ⟪ψ, A ⟨ψ, hψ⟩⟫_ℂ / (‖ψ‖ : ℂ) ^ 2 ∈ numericalRange A := by
  have hnorm_pos : (0 : ℝ) < ‖ψ‖ := norm_pos_iff.mpr hne
  have hmemφ : (‖ψ‖ : ℂ)⁻¹ • ψ ∈ A.domain := A.domain.smul_mem _ hψ
  refine ⟨⟨(‖ψ‖ : ℂ)⁻¹ • ψ, hmemφ⟩, ?_, ?_⟩
  · change ‖(‖ψ‖ : ℂ)⁻¹ • ψ‖ = 1
    rw [norm_smul]
    simp [hnorm_pos.ne']
  · have hcast : (⟨(‖ψ‖ : ℂ)⁻¹ • ψ, hmemφ⟩ : A.domain)
        = (‖ψ‖ : ℂ)⁻¹ • (⟨ψ, hψ⟩ : A.domain) := rfl
    change ⟪(‖ψ‖ : ℂ)⁻¹ • ψ, A ⟨(‖ψ‖ : ℂ)⁻¹ • ψ, hmemφ⟩⟫_ℂ = ⟪ψ, A ⟨ψ, hψ⟩⟫_ℂ / (‖ψ‖ : ℂ) ^ 2
    rw [hcast, A.map_smul, inner_smul_left, inner_smul_right]
    have hconj : (starRingEnd ℂ) ((‖ψ‖ : ℂ)⁻¹) = (‖ψ‖ : ℂ)⁻¹ := by
      have : ((‖ψ‖ : ℂ))⁻¹ = ((‖ψ‖⁻¹ : ℝ) : ℂ) := by norm_cast
      rw [this]; exact Complex.conj_ofReal _
    have hnorm_ne : (‖ψ‖ : ℂ) ≠ 0 := by exact_mod_cast hnorm_pos.ne'
    rw [hconj]
    field_simp

/-- **The numerical-range resolvent bound.** `dist(z, W(A)) · ‖ψ‖ ≤ ‖Aψ - zψ‖` for every
`ψ ∈ dom A` and every `z : ℂ` — a pure Cauchy–Schwarz fact, no symmetry needed. -/
theorem infDist_mul_norm_le_norm_sub_smul {A : H →ₗ.[ℂ] H} (z : ℂ) (ψ : H)
    (hψ : ψ ∈ A.domain) :
    Metric.infDist z (numericalRange A) * ‖ψ‖ ≤ ‖A ⟨ψ, hψ⟩ - z • ψ‖ := by
  rcases eq_or_ne ψ 0 with rfl | hne
  · simp
  have hnorm_pos : (0 : ℝ) < ‖ψ‖ := norm_pos_iff.mpr hne
  have hcast_norm : ‖((‖ψ‖ : ℂ)) ^ 2‖ = ‖ψ‖ ^ 2 := by
    simp
  have hmem := rayleighQuotient_mem_numericalRange hψ hne
  have hle : Metric.infDist z (numericalRange A)
      ≤ ‖z - ⟪ψ, A ⟨ψ, hψ⟩⟫_ℂ / (‖ψ‖ : ℂ) ^ 2‖ := by
    rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hmem
  have hexpand : ⟪ψ, A ⟨ψ, hψ⟩ - z • ψ⟫_ℂ
      = ⟪ψ, A ⟨ψ, hψ⟩⟫_ℂ - z * (‖ψ‖ : ℂ) ^ 2 := by
    rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hnormeq : z - ⟪ψ, A ⟨ψ, hψ⟩⟫_ℂ / (‖ψ‖ : ℂ) ^ 2
      = -⟪ψ, A ⟨ψ, hψ⟩ - z • ψ⟫_ℂ / (‖ψ‖ : ℂ) ^ 2 := by
    have hnorm_ne : (‖ψ‖ : ℂ) ≠ 0 := by exact_mod_cast hnorm_pos.ne'
    rw [hexpand]; field_simp; ring
  rw [hnormeq, norm_div, norm_neg, hcast_norm] at hle
  rw [le_div_iff₀ (by positivity)] at hle
  have hCS : ‖⟪ψ, A ⟨ψ, hψ⟩ - z • ψ⟫_ℂ‖ ≤ ‖ψ‖ * ‖A ⟨ψ, hψ⟩ - z • ψ‖ :=
    norm_inner_le_norm ψ (A ⟨ψ, hψ⟩ - z • ψ)
  have hfinal : Metric.infDist z (numericalRange A) * ‖ψ‖ * ‖ψ‖
      ≤ ‖A ⟨ψ, hψ⟩ - z • ψ‖ * ‖ψ‖ := by
    calc Metric.infDist z (numericalRange A) * ‖ψ‖ * ‖ψ‖
        = Metric.infDist z (numericalRange A) * ‖ψ‖ ^ 2 := by ring
      _ ≤ ‖⟪ψ, A ⟨ψ, hψ⟩ - z • ψ⟫_ℂ‖ := hle
      _ ≤ ‖ψ‖ * ‖A ⟨ψ, hψ⟩ - z • ψ‖ := hCS
      _ = ‖A ⟨ψ, hψ⟩ - z • ψ‖ * ‖ψ‖ := mul_comm _ _
  exact le_of_mul_le_mul_right hfinal hnorm_pos

/-- `A - z` is injective on its domain whenever `z` lies strictly outside the closure of the
numerical range (which requires the numerical range to be nonempty — automatic once `A`'s domain
contains a nonzero vector). -/
theorem injOn_sub_smul_of_notMem_closure_numericalRange {A : H →ₗ.[ℂ] H} {z : ℂ}
    (hne : (numericalRange A).Nonempty) (hz : z ∉ closure (numericalRange A))
    {ψ φ : H} (hψ : ψ ∈ A.domain) (hφ : φ ∈ A.domain)
    (heq : A ⟨ψ, hψ⟩ - z • ψ = A ⟨φ, hφ⟩ - z • φ) : ψ = φ := by
  have hpos : 0 < Metric.infDist z (numericalRange A) :=
    (Metric.infDist_pos_iff_notMem_closure hne).mp hz
  have hsub : ψ - φ ∈ A.domain := A.domain.sub_mem hψ hφ
  have hval_eq : (⟨ψ - φ, hsub⟩ : A.domain) = (⟨ψ, hψ⟩ : A.domain) - ⟨φ, hφ⟩ := rfl
  have hAsub : A ⟨ψ - φ, hsub⟩ - z • (ψ - φ) = 0 := by
    have hmap : A ⟨ψ - φ, hsub⟩ = A ⟨ψ, hψ⟩ - A ⟨φ, hφ⟩ := by
      rw [hval_eq]; exact A.map_sub (⟨ψ, hψ⟩ : A.domain) ⟨φ, hφ⟩
    rw [hmap, smul_sub]
    rw [show A ⟨ψ, hψ⟩ - A ⟨φ, hφ⟩ - (z • ψ - z • φ)
        = (A ⟨ψ, hψ⟩ - z • ψ) - (A ⟨φ, hφ⟩ - z • φ) by abel, heq, sub_self]
  have hbound := infDist_mul_norm_le_norm_sub_smul z (ψ - φ) hsub
  rw [hAsub, norm_zero] at hbound
  have hle0 : ‖ψ - φ‖ ≤ 0 := by
    by_contra hcon
    push Not at hcon
    nlinarith [hbound, hpos]
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hle0 (norm_nonneg _)))

/-- **Closed range from the numerical range.** `ran(A - z)` is closed for self-adjoint `A`
whenever `z` lies outside `closure (W(A))` — the numerical-range analogue of
`Spectra.YosidaHille.op_range_isClosed`, which only reaches `z` off the imaginary axis. The proof
is the same Cauchy-sequence argument, with `infDist_mul_norm_le_norm_sub_smul` in place of the
imaginary-axis bound. -/
theorem numericalRange_range_isClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (z : ℂ)
    (hne : (numericalRange A).Nonempty) (hz : z ∉ closure (numericalRange A)) :
    IsClosed (Set.range fun x : A.domain => A x - z • (x : H)) := by
  apply IsSeqClosed.isClosed
  intro φn φ hmem hlim
  choose xn hxn using hmem
  have hzpos : (0 : ℝ) < Metric.infDist z (numericalRange A) :=
    (Metric.infDist_pos_iff_notMem_closure hne).mp hz
  have hφC : CauchySeq φn := hlim.cauchySeq
  have hCx : CauchySeq fun n => (xn n : H) := by
    rw [Metric.cauchySeq_iff] at hφC ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hφC (Metric.infDist z (numericalRange A) * ε) (by positivity)
    refine ⟨N, fun m hm k hk => ?_⟩
    have hsub : (↑(xn m) - ↑(xn k) : H) ∈ A.domain := A.domain.sub_mem (xn m).2 (xn k).2
    have hAsub : A ⟨↑(xn m) - ↑(xn k), hsub⟩ - z • (↑(xn m) - ↑(xn k)) = φn m - φn k := by
      have hms : A ⟨↑(xn m) - ↑(xn k), hsub⟩ = A (xn m) - A (xn k) := by
        have := A.map_sub (xn m) (xn k); convert this using 2
      rw [hms, smul_sub, ← hxn m, ← hxn k]; abel_nf
      grind only
    have hlb := infDist_mul_norm_le_norm_sub_smul z (↑(xn m) - ↑(xn k) : H) hsub
    rw [hAsub] at hlb
    rw [dist_eq_norm]
    have hd : ‖φn m - φn k‖ < Metric.infDist z (numericalRange A) * ε := by
      rw [← dist_eq_norm]; exact hN m hm k hk
    have : Metric.infDist z (numericalRange A) * ‖(↑(xn m) - ↑(xn k) : H)‖
        < Metric.infDist z (numericalRange A) * ε := lt_of_le_of_lt hlb hd
    exact lt_of_mul_lt_mul_left this (le_of_lt hzpos)
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hCx
  have hAx : Tendsto (fun n => A (xn n)) atTop (𝓝 (φ + z • u)) := by
    have heq : (fun n => A (xn n)) = fun n => φn n + z • (↑(xn n) : H) := by
      funext n; rw [← hxn n]; abel_nf; grind only
    rw [heq]; exact hlim.add (hu.const_smul z)
  have hpair : (u, φ + z • u) ∈ A.graph :=
    hA.isClosed.mem_of_tendsto (hu.prodMk_nhds hAx)
      (Filter.Eventually.of_forall fun n => A.mem_graph (xn n))
  rw [LinearPMap.mem_graph_iff] at hpair
  obtain ⟨y, hy1, hy2⟩ := hpair
  have e1 : (y : H) = u := hy1
  have e2 : A y = φ + z • u := hy2
  exact ⟨y, by simp only [e2, e1]; abel⟩

/-- **Conjugate-invariance of `closure (W(A))`.** For symmetric `A`, `W(A) ⊆ ℝ`
(`numericalRange_subset_range_ofReal`) and `ℝ` is closed in `ℂ`, so `closure (W(A)) ⊆ ℝ` too —
every point of the closure is fixed by conjugation. Hence `z ∉ closure (W(A))` already excludes
`conj z` as well, with no separate hypothesis needed. -/
theorem numericalRange_conj_notMem_of_notMem {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (z : ℂ) (hz : z ∉ closure (numericalRange A)) :
    (starRingEnd ℂ) z ∉ closure (numericalRange A) := by
  intro hmem
  have hsub : closure (numericalRange A) ⊆ Set.range ((↑) : ℝ → ℂ) :=
    closure_minimal (numericalRange_subset_range_ofReal hsym)
      Complex.isUniformEmbedding_ofReal.isClosedEmbedding.isClosed_range
  obtain ⟨r, hr⟩ := hsub hmem
  have hzz : z = (starRingEnd ℂ) z := by
    have hconj := congrArg (starRingEnd ℂ) hr
    rw [Complex.conj_conj] at hconj
    rw [← hr, ← hconj]
    simp
  exact hz (hzz ▸ hmem)

/-- **Dense range from the numerical range.** `ran(A - z)` is dense for self-adjoint `A`
whenever `z` lies outside `closure (W(A))` — the numerical-range analogue of
`Spectra.YosidaHille.op_range_dense`. The proof reuses `op_range_dense`'s adjoint-domain-membership
technique verbatim up to the weak eigenvalue equation `Aχ = conj z • χ`, then kills `χ` via
`infDist_mul_norm_le_norm_sub_smul` (at `conj z`, automatically excluded by
`numericalRange_conj_notMem_of_notMem`) instead of the imaginary-axis bound. -/
theorem numericalRange_range_dense {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (z : ℂ)
    (hne : (numericalRange A).Nonempty) (hz : z ∉ closure (numericalRange A)) :
    Dense (Set.range fun x : A.domain => A x - z • (x : H)) := by
  have hdense : Dense (A.domain : Set H) := hA.dense_domain
  have hsym : A.IsFormalAdjoint A := by
    have h : A.adjoint.IsFormalAdjoint A := LinearPMap.adjoint_isFormalAdjoint hdense
    rwa [LinearPMap.isSelfAdjoint_def.mp hA] at h
  have hadj : A.adjoint = A := LinearPMap.isSelfAdjoint_def.mp hA
  have hzconj : (starRingEnd ℂ) z ∉ closure (numericalRange A) :=
    numericalRange_conj_notMem_of_notMem hsym z hz
  set R : Submodule ℂ H := LinearMap.range (A.toFun - z • A.domain.subtype) with _hRdef
  have hRset : (Set.range fun x : A.domain => A x - z • (x : H)) = (R : Set H) := by
    ext y; constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, by simp [LinearMap.sub_apply]⟩
    · rintro ⟨x, rfl⟩; exact ⟨x, by simp [LinearMap.sub_apply]⟩
  rw [hRset]
  have hbot : Rᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro χ hχ
    have horth : ∀ x : A.domain, ⟪A x - z • (x : H), χ⟫_ℂ = 0 := by
      intro x; exact hχ _ ⟨x, by simp [LinearMap.sub_apply]⟩
    have hcont : Continuous fun x : A.domain => ⟪χ, A x⟫_ℂ := by
      have hfun : (fun x : A.domain => ⟪χ, A x⟫_ℂ)
          = fun x : A.domain => z * ⟪χ, (x : H)⟫_ℂ := by
        funext x
        have h0 := horth x
        rw [inner_sub_left, inner_smul_left, sub_eq_zero] at h0
        have hc := congrArg (starRingEnd ℂ) h0
        rwa [inner_conj_symm, map_mul, Complex.conj_conj, inner_conj_symm] at hc
      rw [hfun]
      exact continuous_const.mul (continuous_const.inner A.domain.subtypeL.continuous)
    have hχdom : χ ∈ A.adjoint.domain :=
      (LinearPMap.mem_adjoint_domain_iff A χ).mpr hcont
    have hval : A.adjoint ⟨χ, hχdom⟩ = conj z • χ := by
      have hkey : ∀ x : A.domain, ⟪A.adjoint ⟨χ, hχdom⟩ - conj z • χ, (x : H)⟫_ℂ = 0 := by
        intro x
        have hfa := LinearPMap.adjoint_isFormalAdjoint hdense ⟨χ, hχdom⟩ x
        rw [inner_sub_left, hfa, inner_smul_left, Complex.conj_conj]
        have h0 := horth x
        rw [inner_sub_left, inner_smul_left, sub_eq_zero] at h0
        have hc := congrArg (starRingEnd ℂ) h0
        rw [inner_conj_symm, map_mul, Complex.conj_conj, inner_conj_symm] at hc
        rw [hc]; ring
      set d := A.adjoint ⟨χ, hχdom⟩ - conj z • χ with hd
      have hd0 : d = 0 := by
        have hg : Continuous fun w => ⟪d, w⟫_ℂ := continuous_const.inner continuous_id
        have hg0 : (fun w => ⟪d, w⟫_ℂ) = fun _ => (0 : ℂ) :=
          Continuous.ext_on hdense hg continuous_const fun w hw => by
            simpa using hkey ⟨w, hw⟩
        have : ⟪d, d⟫_ℂ = 0 := by have := congrFun hg0 d; simpa using this
        exact inner_self_eq_zero.mp this
      rwa [hd, sub_eq_zero] at hd0
    have hχdomA : χ ∈ A.domain := hadj ▸ hχdom
    have hAχ : A ⟨χ, hχdomA⟩ = conj z • χ := by
      have hle := (le_of_eq hadj).2 (x := ⟨χ, hχdom⟩) (y := ⟨χ, hχdomA⟩) rfl
      rw [← hle]; exact hval
    have hzero : A ⟨χ, hχdomA⟩ - conj z • χ = 0 := by rw [hAχ, sub_self]
    have hlb := infDist_mul_norm_le_norm_sub_smul (conj z) χ hχdomA
    rw [hzero, norm_zero] at hlb
    have hpos : 0 < Metric.infDist (conj z) (numericalRange A) :=
      (Metric.infDist_pos_iff_notMem_closure hne).mp hzconj
    have : ‖χ‖ ≤ 0 := by nlinarith [norm_nonneg χ, hlb, hpos]
    simpa using le_antisymm this (norm_nonneg χ)
  have hcl : R.topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hbot, Submodule.bot_orthogonal_eq_top]
  exact (Submodule.dense_iff_topologicalClosure_eq_top).mpr hcl

end Spectra.Operator
