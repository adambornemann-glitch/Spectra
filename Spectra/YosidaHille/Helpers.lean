/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.OneParameterUnitaryGroup.Basic

/-!
# Operator lower bounds and the self-adjoint surjectivity criterion

Off-axis lower bounds for a symmetric operator and their consequences. For `z` off the real axis,
`|z.im|·‖x‖ ≤ ‖A x - z•x‖`, from which the range of `A - z` is closed and dense — hence all of `H`.
Specialized to `z = ± I`, this gives the deficiency-index criterion (`A ± I` surjective) that
underlies Stone's theorem, and shows a self-adjoint operator has no proper self-adjoint extension.

## Main statements

* `op_lower_bound` — `|z.im|·‖x‖ ≤ ‖A x - z•x‖` for symmetric `A`.
* `op_range_isClosed` / `op_range_dense` — the range of `A - z` is closed and dense.
* `selfAdjoint_surjective_sub_smul` — `A - z` is surjective for `z` off the real axis.
* `isSelfAdjoint_to_surjective` — `A ± I` are surjective for self-adjoint `A`.
* `IsSelfAdjoint.eq_of_le` — a self-adjoint operator has no proper self-adjoint extension.
-/

open InnerProductSpace Complex Filter Topology
open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.YosidaHille

omit [CompleteSpace H] in
/-- Lower bound for a symmetric operator off the real axis: `|z.im|·‖x‖ ≤ ‖A x − z•x‖`.
Gives injectivity and the Cauchy estimate for closed range. -/
lemma op_lower_bound {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (z : ℂ) (x : A.domain) :
    |z.im| * ‖(x : H)‖ ≤ ‖A x - z • (x : H)‖ := by
  have hreal : (⟪A x, (x : H)⟫_ℂ).im = 0 := by
    have h := hsym x x
    have hc : conj ⟪A x, (x : H)⟫_ℂ = ⟪A x, (x : H)⟫_ℂ := by
      simp only [inner_conj_symm]
      exact h.symm
    exact Complex.conj_eq_iff_im.mp hc
  have hxx_im : (⟪(x : H), (x : H)⟫_ℂ).im = 0 := by
    rw [inner_self_eq_norm_sq_to_K]; simp only [coe_algebraMap]
    rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _
  have hxx_re : (⟪(x : H), (x : H)⟫_ℂ).re = ‖(x : H)‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]; simp only [coe_algebraMap]
    rw [← Complex.ofReal_pow]; exact Complex.ofReal_re _
  have himeq : (⟪A x - z • (x : H), (x : H)⟫_ℂ).im = z.im * ‖(x : H)‖ ^ 2 := by
    rw [inner_sub_left, inner_smul_left, Complex.sub_im, hreal, Complex.mul_im,
        hxx_im, hxx_re, Complex.conj_im, Complex.conj_re]; ring
  have hbound : |z.im| * ‖(x : H)‖ ^ 2 ≤ ‖A x - z • (x : H)‖ * ‖(x : H)‖ := by
    have heq : |z.im| * ‖(x : H)‖ ^ 2 = |(⟪A x - z • (x : H), (x : H)⟫_ℂ).im| := by
      rw [himeq, abs_mul]
      simp only [abs_pow, abs_norm]
    rw [heq]
    calc |(⟪A x - z • (x : H), (x : H)⟫_ℂ).im|
        ≤ ‖⟪A x - z • (x : H), (x : H)⟫_ℂ‖ := Complex.abs_im_le_norm _
      _ ≤ ‖A x - z • (x : H)‖ * ‖(x : H)‖ := norm_inner_le_norm _ _
  rcases eq_or_ne (x : H) 0 with h0 | h0
  · simp [h0]
  · have hp : 0 < ‖(x : H)‖ := norm_pos_iff.mpr h0
    rw [sq, ← mul_assoc] at hbound
    exact le_of_mul_le_mul_right hbound hp

/-- The range of `A − z` is closed (closed operator + bounded below). -/
lemma op_range_isClosed {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hgr : IsClosed (A.graph : Set (H × H))) (z : ℂ) (hz : z.im ≠ 0) :
    IsClosed (Set.range fun x : A.domain => A x - z • (x : H)) := by
  apply IsSeqClosed.isClosed
  intro φn φ hmem hlim
  choose xn hxn using hmem                              -- hxn n : A (xn n) - z • ↑(xn n) = φn n
  have hzpos : (0 : ℝ) < |z.im| := abs_pos.mpr hz
  have hφC : CauchySeq φn := hlim.cauchySeq
  have hCx : CauchySeq fun n => (xn n : H) := by
    rw [Metric.cauchySeq_iff] at hφC ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hφC (|z.im| * ε) (by positivity)
    refine ⟨N, fun m hm k hk => ?_⟩
    have hsub : (↑(xn m) - ↑(xn k) : H) ∈ A.domain := A.domain.sub_mem (xn m).2 (xn k).2
    have hAsub : A ⟨↑(xn m) - ↑(xn k), hsub⟩ - z • (↑(xn m) - ↑(xn k)) = φn m - φn k := by
      have hsub_eq : (⟨↑(xn m) - ↑(xn k), hsub⟩ : A.domain) = xn m - xn k := by
        apply Subtype.ext
        rfl
      have hms : A ⟨↑(xn m) - ↑(xn k), hsub⟩ = A (xn m) - A (xn k) := by
        rw [hsub_eq, A.map_sub]
      rw [hms, smul_sub, ← hxn m, ← hxn k]; abel_nf
      grind only
    have hlb := op_lower_bound hsym z ⟨↑(xn m) - ↑(xn k), hsub⟩
    rw [hAsub] at hlb
    rw [dist_eq_norm]
    have hd : ‖φn m - φn k‖ < |z.im| * ε := by rw [← dist_eq_norm]; exact hN m hm k hk
    have : |z.im| * ‖(↑(xn m) - ↑(xn k) : H)‖ < |z.im| * ε := lt_of_le_of_lt hlb hd
    exact lt_of_mul_lt_mul_left this (le_of_lt hzpos)
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

/-- The range of `A − z` is dense (self-adjointness kills the orthogonal complement). -/
lemma op_range_dense {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) :
    Dense (Set.range fun x : A.domain => A x - z • (x : H)) := by
  have hdense : Dense (A.domain : Set H) := hA.dense_domain
  have hsym : A.IsFormalAdjoint A := by
    have h : A.adjoint.IsFormalAdjoint A := LinearPMap.adjoint_isFormalAdjoint hdense
    rwa [LinearPMap.isSelfAdjoint_def.mp hA] at h
  have hadj : A.adjoint = A := LinearPMap.isSelfAdjoint_def.mp hA
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
    -- χ lies in the adjoint domain (the functional x ↦ ⟪χ, A x⟫ is continuous)
    have hcont : Continuous fun x : A.domain => ⟪χ, A x⟫_ℂ := by
      have hfun : (fun x : A.domain => ⟪χ, A x⟫_ℂ)
          = fun x : A.domain => z * ⟪χ, (x : H)⟫_ℂ := by
        funext x
        have h0 := horth x
        rw [inner_sub_left, inner_smul_left, sub_eq_zero] at h0  -- ⟪Ax,χ⟫ = conj z * ⟪↑x,χ⟫
        have hc := congrArg (starRingEnd ℂ) h0
        rwa [inner_conj_symm, map_mul, Complex.conj_conj, inner_conj_symm] at hc
      rw [hfun]
      exact continuous_const.mul (continuous_const.inner A.domain.subtypeL.continuous)
    have hχdom : χ ∈ A.adjoint.domain :=
      (LinearPMap.mem_adjoint_domain_iff A χ).mpr hcont
    -- A† χ = conj z • χ, hence (via self-adjointness) A χ = conj z • χ
    have hval : A.adjoint ⟨χ, hχdom⟩ = conj z • χ := by
      have hkey : ∀ x : A.domain, ⟪A.adjoint ⟨χ, hχdom⟩ - conj z • χ, (x : H)⟫_ℂ = 0 := by
        intro x
        have hfa := LinearPMap.adjoint_isFormalAdjoint hdense ⟨χ, hχdom⟩ x  -- ⟪A†χ,↑x⟫ = ⟪χ,A x⟫
        rw [inner_sub_left, hfa, inner_smul_left, Complex.conj_conj]
        have h0 := horth x
        rw [inner_sub_left, inner_smul_left, sub_eq_zero] at h0
        have hc := congrArg (starRingEnd ℂ) h0
        rw [inner_conj_symm, map_mul, Complex.conj_conj, inner_conj_symm] at hc  -- ⟪χ,Ax⟫=z*⟪χ,↑x⟫
        rw [hc]; ring
      -- orthogonal to a dense set ⇒ zero
      set d := A.adjoint ⟨χ, hχdom⟩ - conj z • χ with hd
      have hd0 : d = 0 := by
        have hg : Continuous fun w => ⟪d, w⟫_ℂ := continuous_const.inner continuous_id
        have hg0 : (fun w => ⟪d, w⟫_ℂ) = fun _ => (0 : ℂ) :=
          Continuous.ext_on hdense hg continuous_const fun w hw => by
            simpa using hkey ⟨w, hw⟩
        have : ⟪d, d⟫_ℂ = 0 := by have := congrFun hg0 d; simpa using this
        exact inner_self_eq_zero.mp this
      rwa [hd, sub_eq_zero] at hd0
    -- transport across A† = A and kill via the lower bound
    have hχdomA : χ ∈ A.domain := hadj ▸ hχdom
    have hAχ : A ⟨χ, hχdomA⟩ = conj z • χ := by
      have hle := (le_of_eq hadj).2 (x := ⟨χ, hχdom⟩) (y := ⟨χ, hχdomA⟩) rfl
      rw [← hle]; exact hval
    have hzero : A ⟨χ, hχdomA⟩ - conj z • χ = 0 := by rw [hAχ, sub_self]
    have hlb := op_lower_bound hsym (conj z) ⟨χ, hχdomA⟩
    rw [hzero, norm_zero] at hlb
    have : ‖χ‖ ≤ 0 := by
      have him : |(conj z).im| = |z.im| := by rw [Complex.conj_im, abs_neg]
      rw [him] at hlb
      have hzpos : (0 : ℝ) < |z.im| := abs_pos.mpr hz
      nlinarith [norm_nonneg χ, hlb, hzpos]
    simpa using le_antisymm this (norm_nonneg χ)
  have hcl : R.topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hbot, Submodule.bot_orthogonal_eq_top]
  exact (Submodule.dense_iff_topologicalClosure_eq_top).mpr hcl

/-- Self-adjoint ⇒ `A − z` surjective for `z` off the real axis. -/
lemma selfAdjoint_surjective_sub_smul {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (z : ℂ) (hz : z.im ≠ 0) :
    ∀ φ : H, ∃ ψ : A.domain, A ψ - z • (ψ : H) = φ := by
  have hdense : Dense (A.domain : Set H) := hA.dense_domain
  have hsym : A.IsFormalAdjoint A := by
    have h : A.adjoint.IsFormalAdjoint A := LinearPMap.adjoint_isFormalAdjoint hdense
    rwa [LinearPMap.isSelfAdjoint_def.mp hA] at h
  have hclR := op_range_isClosed hsym hA.isClosed z hz
  have hdsR := op_range_dense hA z hz
  intro φ
  have hmem : φ ∈ Set.range fun x : A.domain => A x - z • (x : H) := by
    rw [← hclR.closure_eq, hdsR.closure_eq]; trivial
  obtain ⟨ψ, hψ⟩ := hmem
  exact ⟨ψ, hψ⟩

/-- Deficiency indices of a self-adjoint operator vanish: the converse of
`isSelfAdjoint_of_surjective_addSub`. -/
lemma isSelfAdjoint_to_surjective {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    (∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) ∧
    (∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) := by
  refine ⟨fun φ => ?_, fun φ => ?_⟩
  · obtain ⟨ψ, hψ⟩ := selfAdjoint_surjective_sub_smul hA (-I) (by simp) φ
    exact ⟨ψ, by rw [← hψ, neg_smul, sub_neg_eq_add]⟩
  · exact selfAdjoint_surjective_sub_smul hA I (by simp) φ

/-- A self-adjoint operator has no proper self-adjoint extension. -/
lemma IsSelfAdjoint.eq_of_le {A B : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hle : A ≤ B) : A = B := by
  have hsymB : B.IsFormalAdjoint B := by
    have h : B.adjoint.IsFormalAdjoint B := LinearPMap.adjoint_isFormalAdjoint hB.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp hB] at h
  obtain ⟨_, hAminus⟩ := isSelfAdjoint_to_surjective hA
  have hdom : ∀ w (_hw : w ∈ B.domain), w ∈ A.domain := by
    intro w hw
    obtain ⟨v, hv⟩ := hAminus (B ⟨w, hw⟩ - I • w)
    have hvB : (v : H) ∈ B.domain := hle.1 v.2
    have hagree : A v = B ⟨(v : H), hvB⟩ := hle.2 (x := v) (y := ⟨(v : H), hvB⟩) rfl
    have hBv : B ⟨(v : H), hvB⟩ - I • (v : H) = B ⟨w, hw⟩ - I • w := by rw [← hagree]; exact hv
    have hsub : (v : H) - w ∈ B.domain := B.domain.sub_mem hvB hw
    have hzero : B ⟨(v : H) - w, hsub⟩ - I • ((v : H) - w) = 0 := by
      have hsub_eq : (⟨(v : H) - w, hsub⟩ : B.domain) =
          ⟨(v : H), hvB⟩ - ⟨w, hw⟩ := by
        apply Subtype.ext
        rfl
      have op_eq : B ⟨(v : H) - w, hsub⟩ = B ⟨(v : H), hvB⟩ - B ⟨w, hw⟩ := by
        rw [hsub_eq, B.map_sub]
      rw [op_eq, smul_sub, sub_sub_sub_comm, hBv, sub_self]
    have hvw : (v : H) - w = 0 := by
      have hlb := op_lower_bound hsymB I ⟨(v : H) - w, hsub⟩
      rw [hzero] at hlb
      simp only [Complex.I_im, abs_one, one_mul, norm_zero] at hlb
      exact norm_le_zero_iff.mp hlb
    have hwv : w = (v : H) := (sub_eq_zero.mp hvw).symm
    rw [hwv]; exact v.2
  have hB_le : B ≤ A :=
    ⟨fun w hw => hdom w hw, fun x y hxy => (hle.2 (x := y) (y := x) hxy.symm).symm⟩
  exact le_antisymm hle hB_le

end Spectra.YosidaHille
