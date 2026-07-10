/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SpectralTheory.Weak
import Spectra.SpectralTheory.Measure.GeneratorLink
import Spectra.SpectralTheory.Calculus.Bounded

/-!
# Eigenvalues ↔ spectral atoms

For a self-adjoint operator `A` on a complex Hilbert space, with projection-valued measure
`E = spectralPVM hA`, the spectral projection onto a singleton `{λ}` **is** the orthogonal
projection onto the `λ`-eigenspace:

  `E({λ}) ψ = ψ  ↔  A ψ = λ ψ`   (`ψ ∈ D(A)`),

equivalently `range E({λ}) = ker(A − λ)`.  This is the bridge between the *abstract* spectral
measure and the *concrete* eigenvectors — the keystone for identifying explicit eigenfunction
expansions (e.g. hydrogen) with the spectral projections of the Hamiltonian.

## Main results

* `spectralPVM_sq_dist_integral` — `∫ (s − c)² dμ_ψ = ‖Aψ − c·ψ‖²` for any real `c` (the
  central second moment about an arbitrary point; generalizes `spectralPVM_central_moment`).
* `spectralPVM_proj_singleton_eq_self_of_eigen` — **`Aψ = λψ ⟹ E({λ})ψ = ψ`** (eigenvector lies
  in the atom).  Via the moment identity: `∫ (s−λ)² dμ_ψ = 0` forces `μ_ψ({λ}ᶜ) = 0`.
* `generator_spectralProjection_singleton` — **`A (E({λ})ψ) = λ · E({λ})ψ`** (the atom's range
  consists of eigenvectors), at the one-parameter-group level.
-/

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace
open Spectra.Borel
open Spectra.OneParameterUnitaryGroup
open Spectra.YosidaHille

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.QuantumMechanics.SpectralTheory

/-! ## The central second moment about an arbitrary point -/

/-- **The second central moment about any real point `c`**: `∫ (s − c)² dμ_ψ = ‖Aψ − c·ψ‖²`,
for `ψ ∈ D(A)`.  Both sides expand to `‖Aψ‖² − 2c·⟪ψ,Aψ⟫.re + c²‖ψ‖²` using the first and
second moments and the total mass.  (`spectralPVM_central_moment` is the case `c = mean`.) -/
theorem spectralPVM_sq_dist_integral {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (ψ : H)
    (hψ : ψ ∈ A.domain) (c : ℝ) :
    ∫ s, (s - c) ^ 2 ∂((PVM.spectralPVM hA).diag ψ)
      = ‖A ⟨ψ, hψ⟩ - (c : ℂ) • ψ‖ ^ 2 := by
  haveI : IsFiniteMeasure ((PVM.spectralPVM hA).diag ψ) := (PVM.spectralPVM hA).diag_finite ψ
  set μ := (PVM.spectralPVM hA).diag ψ with _hμ
  have hint1 : Integrable (fun s : ℝ => s) μ := spectralPVM_integrable_id hA ψ hψ
  have hint2 : Integrable (fun s : ℝ => s ^ 2) μ := spectralPVM_integrable_sq hA ψ hψ
  have hI1 : ∫ s, s ∂μ = (⟪ψ, A ⟨ψ, hψ⟩⟫_ℂ).re := spectralPVM_integral_id hA ψ hψ
  have hI2 : ∫ s, s ^ 2 ∂μ = ‖A ⟨ψ, hψ⟩‖ ^ 2 := spectralPVM_integral_sq hA ψ hψ
  have hmass : (μ Set.univ).toReal = ‖ψ‖ ^ 2 :=
    ProjValMeasure.diag_univ_toReal (PVM.spectralPVM hA) ψ
  have hLHS : ∫ s, (s - c) ^ 2 ∂μ
      = ‖A ⟨ψ, hψ⟩‖ ^ 2 - 2 * c * (⟪ψ, A ⟨ψ, hψ⟩⟫_ℂ).re + c ^ 2 * ‖ψ‖ ^ 2 := by
    have hpt : ∀ s : ℝ, (s - c) ^ 2 = s ^ 2 - 2 * c * s + c ^ 2 := fun s => by ring
    simp_rw [hpt]
    rw [integral_add, integral_sub, integral_const_mul, integral_const, measureReal_def, hI2,
      hI1, hmass, smul_eq_mul]
    · ring
    · exact hint2
    · exact hint1.const_mul (2 * c)
    · exact hint2.sub (hint1.const_mul (2 * c))
    · exact integrable_const _
  have hconj : (⟪A ⟨ψ, hψ⟩, ψ⟫_ℂ).re = (⟪ψ, A ⟨ψ, hψ⟩⟫_ℂ).re := by
    rw [← inner_conj_symm, Complex.conj_re]
  have hRHS : ‖A ⟨ψ, hψ⟩ - (c : ℂ) • ψ‖ ^ 2
      = ‖A ⟨ψ, hψ⟩‖ ^ 2 - 2 * c * (⟪ψ, A ⟨ψ, hψ⟩⟫_ℂ).re + c ^ 2 * ‖ψ‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    simp only [RCLike.re_to_complex, Complex.re_ofReal_mul, hconj]
    rw [mul_pow, sq_abs]
    ring
  rw [hLHS, hRHS]

/-! ## Eigenvector ⟹ spectral atom (`ker(A − λ) ⊆ range E({λ})`) -/

/-- **An eigenvector lies in the corresponding spectral atom**: if `A ψ = λ ψ` (with
`ψ ∈ D(A)`), then `E({λ}) ψ = ψ`.  Proof: the moment identity gives `∫ (s−λ)² dμ_ψ =
‖Aψ − λψ‖² = 0`; since `(s−λ)² ≥ 0`, the measure `μ_ψ` is supported on `{λ}`, so
`E({λ}ᶜ) ψ = 0`, and `E({λ}) + E({λ}ᶜ) = id`. -/
theorem spectralPVM_proj_singleton_eq_self_of_eigen {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {lam : ℝ} (ψ : H) (hψ : ψ ∈ A.domain) (heig : A ⟨ψ, hψ⟩ = (lam : ℂ) • ψ) :
    (PVM.spectralPVM hA).proj {lam} (measurableSet_singleton lam) ψ = ψ := by
  haveI : IsFiniteMeasure ((PVM.spectralPVM hA).diag ψ) := (PVM.spectralPVM hA).diag_finite ψ
  set μ := (PVM.spectralPVM hA).diag ψ with hμ
  -- the central moment about `lam` vanishes
  have hcm : ∫ s, (s - lam) ^ 2 ∂μ = 0 := by
    rw [hμ, spectralPVM_sq_dist_integral hA ψ hψ lam, heig, sub_self, norm_zero]; norm_num
  -- `(s − lam)²` is integrable
  have hint : Integrable (fun s : ℝ => (s - lam) ^ 2) μ := by
    have hrw : (fun s : ℝ => (s - lam) ^ 2)
        = (fun s : ℝ => s ^ 2 - 2 * lam * s + lam ^ 2) := by funext s; ring
    rw [hrw]
    exact ((spectralPVM_integrable_sq hA ψ hψ).sub
      ((spectralPVM_integrable_id hA ψ hψ).const_mul (2 * lam))).add (integrable_const _)
  -- hence `(s − lam)² = 0` a.e., so `μ {lam}ᶜ = 0`
  have hae : (fun s : ℝ => (s - lam) ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall fun s => sq_nonneg _) hint).mp
      hcm
  have hnull : μ {lam}ᶜ = 0 := by
    have hset : {s : ℝ | ¬ (fun s : ℝ => (s - lam) ^ 2) s = (0 : ℝ → ℝ) s} = {lam}ᶜ := by
      ext s
      simp only [Set.mem_setOf_eq, Pi.zero_apply, ne_eq, pow_eq_zero_iff, OfNat.ofNat_ne_zero,
        not_false_eq_true, sub_eq_zero, Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [Filter.EventuallyEq, ae_iff, hset] at hae
    exact hae
  -- `E({lam}ᶜ) ψ = 0`
  have hcompl0 : (PVM.spectralPVM hA).proj {lam}ᶜ (measurableSet_singleton lam).compl ψ = 0 := by
    have hnsq := ProjValMeasure.norm_sq_proj_apply (PVM.spectralPVM hA) {lam}ᶜ
      (measurableSet_singleton lam).compl ψ
    rw [← hμ, hnull, ENNReal.toReal_zero] at hnsq
    have : ‖(PVM.spectralPVM hA).proj {lam}ᶜ (measurableSet_singleton lam).compl ψ‖ = 0 := by
      nlinarith [norm_nonneg ((PVM.spectralPVM hA).proj {lam}ᶜ
        (measurableSet_singleton lam).compl ψ)]
    exact norm_eq_zero.mp this
  -- `E({lam}) + E({lam}ᶜ) = id`, evaluated at `ψ`
  have hid : (PVM.spectralPVM hA).proj {lam} (measurableSet_singleton lam)
      + (PVM.spectralPVM hA).proj {lam}ᶜ (measurableSet_singleton lam).compl
      = ContinuousLinearMap.id ℂ H := by
    rw [← (PVM.spectralPVM hA).proj_union (measurableSet_singleton lam)
        (measurableSet_singleton lam).compl disjoint_compl_right,
      (PVM.spectralPVM hA).proj_congr (Set.union_compl_self {lam})
        ((measurableSet_singleton lam).union (measurableSet_singleton lam).compl)
        MeasurableSet.univ,
      (PVM.spectralPVM hA).proj_univ]
  have happ := congrArg (fun T : H →L[ℂ] H => T ψ) hid
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply, hcompl0,
    add_zero] at happ
  exact happ

/-! ## Spectral atom ⟹ eigenvector (`range E({λ}) ⊆ ker(A − λ)`) -/

variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- The range of a singleton spectral projection lies in the generator's domain (the symbol
`s·1_{λ}` is bounded — it is `λ·1_{λ}`). -/
theorem spectralProjection_singleton_mem_generatorDomain (lam : ℝ) (φ : H) :
    spectralProjection U_grp {lam} (measurableSet_singleton lam) φ ∈ (generator U_grp).domain :=
  spectralProjection_mem_generatorDomain U_grp (measurableSet_singleton lam) (R := |lam|)
    (fun x hx => le_of_eq (by rw [Set.mem_singleton_iff.mp hx])) φ

/-- **The generator acts as multiplication by `λ` on the range of `E({λ})`**:
`A (E({λ}) φ) = λ · E({λ}) φ`.  Group level: `A(E({λ})φ) = Φ(s·1_{λ})φ = Φ(λ·1_{λ})φ =
λ·E({λ})φ`. -/
theorem generator_spectralProjection_singleton (lam : ℝ) (φ : H) :
    generator U_grp ⟨spectralProjection U_grp {lam} (measurableSet_singleton lam) φ,
        spectralProjection_singleton_mem_generatorDomain U_grp lam φ⟩
      = (lam : ℂ) • spectralProjection U_grp {lam} (measurableSet_singleton lam) φ := by
  classical
  have hR : ∀ x ∈ ({lam} : Set ℝ), |x| ≤ |lam| :=
    fun x hx => le_of_eq (by rw [Set.mem_singleton_iff.mp hx])
  -- The symbol identity `s·1_{λ} = λ·1_{λ}`.
  have hsym : (fun l : ℝ => (l : ℂ) * Set.indicator ({lam} : Set ℝ) (fun _ => (1 : ℂ)) l)
      = (fun l : ℝ => (lam : ℂ) * Set.indicator ({lam} : Set ℝ) (fun _ => (1 : ℂ)) l) := by
    funext l
    by_cases h : l = lam
    · subst h; rfl
    · rw [Set.indicator_of_notMem (by simpa using h), mul_zero, mul_zero]
  have hm2 : Measurable
      (fun l : ℝ => (lam : ℂ) * Set.indicator ({lam} : Set ℝ) (fun _ => (1 : ℂ)) l) :=
    measurable_const.mul (measurable_const.indicator (measurableSet_singleton lam))
  have hb2 : ∃ C, ∀ ω, ‖(lam : ℂ) * Set.indicator ({lam} : Set ℝ) (fun _ => (1 : ℂ)) ω‖ ≤ C := by
    obtain ⟨C, hC⟩ := indicator_one_bdd ({lam} : Set ℝ)
    exact ⟨‖(lam : ℂ)‖ * C, fun ω => by rw [norm_mul]; gcongr; exact hC ω⟩
  -- The operator identity `Φ(s·1_{λ}) = λ • E({λ})`.
  have hΦ : spectralCalculus U_grp
        (fun l : ℝ => (l : ℂ) * Set.indicator ({lam} : Set ℝ) (fun _ => (1 : ℂ)) l)
        (id_indicator_measurable (measurableSet_singleton lam)) (id_indicator_bdd hR)
      = (lam : ℂ) • spectralProjection U_grp {lam} (measurableSet_singleton lam) := by
    rw [spectralCalculus_congr U_grp hsym (id_indicator_measurable (measurableSet_singleton lam))
        (id_indicator_bdd hR) hm2 hb2,
      spectralCalculus_smul U_grp (lam : ℂ) (Set.indicator ({lam} : Set ℝ) (fun _ => (1 : ℂ)))
        (measurable_const.indicator (measurableSet_singleton lam)) (indicator_one_bdd _) hm2 hb2]
    rfl
  rw [generator_spectralProjection U_grp (measurableSet_singleton lam) (R := |lam|) hR φ,
    ← ContinuousLinearMap.smul_apply]
  exact congrArg (fun T : H →L[ℂ] H => T φ) hΦ

/-- **An element of `range E({λ})` is a `λ`-eigenvector of `A`** (self-adjoint level): for any
`φ`, `E({λ}) φ ∈ D(A)` and `A (E({λ})φ) = λ · E({λ})φ`.  Transferred from the group level via
Stone's theorem `generator (genToGroup hA) = A`. -/
theorem spectralPVM_proj_singleton_apply_isEigen {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (lam : ℝ) (φ : H) :
    ∃ hmem : (PVM.spectralPVM hA).proj {lam} (measurableSet_singleton lam) φ ∈ A.domain,
      A ⟨(PVM.spectralPVM hA).proj {lam} (measurableSet_singleton lam) φ, hmem⟩
        = (lam : ℂ) • (PVM.spectralPVM hA).proj {lam} (measurableSet_singleton lam) φ := by
  set v : H := (PVM.spectralPVM hA).proj {lam} (measurableSet_singleton lam) φ with _hv
  -- membership at the group level (the PVM projection is the group's spectral projection)
  have hmem_gen : v ∈ (generator (genToGroup hA)).domain :=
    spectralProjection_singleton_mem_generatorDomain (genToGroup hA) lam φ
  have hmemA : v ∈ A.domain := by rw [← generator_genToGroup hA]; exact hmem_gen
  refine ⟨hmemA, ?_⟩
  -- value: transfer `A → generator (genToGroup hA)`, then apply the group eigenvalue identity
  have hgen : generator (genToGroup hA) ⟨v, hmem_gen⟩ = (lam : ℂ) • v :=
    generator_spectralProjection_singleton (genToGroup hA) lam φ
  have htrans : A ⟨v, hmemA⟩ = generator (genToGroup hA) ⟨v, hmem_gen⟩ :=
    ((le_of_eq (generator_genToGroup hA)).2 rfl).symm
  rw [htrans]; exact hgen

/-! ## The eigenspace characterization (`range E({λ}) = ker(A − λ)`) -/

/-- **The spectral atom `{λ}` is exactly the `λ`-eigenspace.**  A vector is fixed by the
spectral projection `E({λ})` iff it is a `λ`-eigenvector of `A`:

  `E({λ}) ψ = ψ  ↔  ∃ (h : ψ ∈ D(A)), A ψ = λ ψ`.

Since `E({λ})` is the orthogonal projection onto its range (its fixed-point set), this says
`range E({λ}) = ker(A − λ)` — the bridge from the abstract spectral measure to concrete
eigenvectors. -/
theorem spectralPVM_proj_singleton_eq_self_iff {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {lam : ℝ} (ψ : H) :
    (PVM.spectralPVM hA).proj {lam} (measurableSet_singleton lam) ψ = ψ
      ↔ ∃ h : ψ ∈ A.domain, A ⟨ψ, h⟩ = (lam : ℂ) • ψ := by
  constructor
  · intro hfix
    obtain ⟨hmem, hval⟩ := spectralPVM_proj_singleton_apply_isEigen hA lam ψ
    have hψdom : ψ ∈ A.domain := hfix ▸ hmem
    refine ⟨hψdom, ?_⟩
    have hpt : (⟨ψ, hψdom⟩ : A.domain)
        = ⟨(PVM.spectralPVM hA).proj {lam} (measurableSet_singleton lam) ψ, hmem⟩ :=
      Subtype.ext hfix.symm
    rw [hpt, hval, hfix]
  · rintro ⟨h, heig⟩
    exact spectralPVM_proj_singleton_eq_self_of_eigen hA ψ h heig

end Spectra.QuantumMechanics.SpectralTheory
