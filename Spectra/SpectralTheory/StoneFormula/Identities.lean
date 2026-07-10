/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.SpectralRepresentation
import Spectra.Kernel.Lorentzian
import Spectra.Kernel.Resolvent
import Spectra.QuantumMechanics.DiracEquation.Operators
import Mathlib.Analysis.SpecificLimits.Normed
/-!
# Resolvent identities (rebuilt on the constructed calculus)

The old Logos-Library version of this file routed every identity through a hypothesized
spectral measure.  Several of its theorems are now upstream theorems of the Resolvent
stack, the rest collapse onto `solution_unique` and the constructed calculus:

| old                                       | new                                          |
| ------------------------------------------ | -------------------------------------------- |
| `resolvent_kernel_identity`, product lemmas | dropped — `resolvent_identity` is proved at the |
|                                              | operator level upstream |
| `first_resolvent_identity`                 | upstream: `resolvent_identity`               |
| `resolvent_opNorm_bound`                   | upstream: `resolvent_bound`                  |
| `resolvent_comm`                           | `resolvent_comm` (two lines via |
|                                              | `spectralCalculus_comm`) |
| `resolvent_maps_to_domain`                 | `resolvent_mem_domain` (definitional)        |
| `resolventFun_left_inverse` (private, | `resolvent_left_inverse` (via `solution_unique`) |
| ~60 lines) | |
| `second_resolvent_identity`                | same statement, abstract operators           |
| `born_series` (custom `neumannSeries`)     | `born_series` via Mathlib's `Units.oneSub`   |
| `resolvent_norm_blowup_at_spectrum`        | ported to `spectralProjection`/`borelMeasure` |
| `stieltjes_inversion`                      | ported; consumes `im_inner_resolvent_diag`   |

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII
* [Kato, *Perturbation Theory for Linear Operators*][kato1995], Chapter V
-/
open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace
open Spectra.Borel
open SpectralMeasure
open Spectra.Kernels
open Spectra.QuantumMechanics.SpectralTheory
open Spectra.OneParameterUnitaryGroup
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Resolvent
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-! ## Structural facts, read off the construction -/

/-- The resolvent maps into the operator's domain — definitional, since `R(z)φ` is the
`Classical.choose` witness of `self_adjoint_range_all_z`. -/
lemma resolvent_mem_domain
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (z : ℂ) (hz : z.im ≠ 0) (φ : H) :
    resolvent z hz hsym hplus hminus φ ∈ A.domain :=
  (Classical.choose (self_adjoint_range_all_z hsym hplus hminus z hz φ).exists).2

/-- The defining equation of the resolvent: `(A − z)(R(z)φ) = φ`. -/
lemma resolvent_solves
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (z : ℂ) (hz : z.im ≠ 0) (φ : H) :
    A ⟨resolvent z hz hsym hplus hminus φ, resolvent_mem_domain hsym hplus hminus z hz φ⟩
        - z • resolvent z hz hsym hplus hminus φ = φ :=
  Classical.choose_spec (self_adjoint_range_all_z hsym hplus hminus z hz φ).exists

/-- **Left inverse**: `R(z)(Aψ − z•ψ) = ψ` for `ψ ∈ D(A)`.  Solution uniqueness, nothing
more — the old proof re-derived injectivity of `A − z` by hand. -/
lemma resolvent_left_inverse
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (z : ℂ) (hz : z.im ≠ 0) (ψ : A.domain) :
    resolvent z hz hsym hplus hminus (A ψ - z • (ψ : H)) = (ψ : H) := by
  set φ : H := A ψ - z • (ψ : H) with hφ
  let R_sub : A.domain :=
    Classical.choose (self_adjoint_range_all_z hsym hplus hminus z hz φ).exists
  have hR_eq : A R_sub - z • (R_sub : H) = φ :=
    Classical.choose_spec (self_adjoint_range_all_z hsym hplus hminus z hz φ).exists
  have hres : resolvent z hz hsym hplus hminus φ = (R_sub : H) := rfl
  rw [hres]
  exact congrArg Subtype.val (solution_unique hsym z hz φ R_sub ψ hR_eq hφ.symm)

/-! ## Commutativity, via the calculus -/

/-- The resolvent commutes with itself at different spectral parameters:
`R(z) R(w) = R(w) R(z)`.  Both are `Φ` of commuting symbols. -/
theorem resolvent_comm (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    resolvent z hz (generator_isFormalAdjoint U_grp)
        (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp)
      * resolvent w hw (generator_isFormalAdjoint U_grp)
        (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp)
      = resolvent w hw (generator_isFormalAdjoint U_grp)
          (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp)
        * resolvent z hz (generator_isFormalAdjoint U_grp)
            (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) := by
  rw [resolvent_eq_spectralCalculus U_grp z hz, resolvent_eq_spectralCalculus U_grp w hw]
  exact spectralCalculus_comm U_grp (fun s : ℝ => ((s : ℂ) - w)⁻¹)
    (fun s : ℝ => ((s : ℂ) - z)⁻¹) (kernel_measurable w hw) (kernel_bdd w hw)
    (kernel_measurable z hz) (kernel_bdd z hz)

/-! ## Second resolvent identity (perturbation identity) -/

/-- **Second Resolvent Identity**: for two self-adjoint-packaged operators `A`, `B`,

  `R_A(z)ψ − R_B(z)ψ = R_A(z)·(B − A)·R_B(z)ψ`,

stated pointwise with the single domain hypothesis `R_B(z)ψ ∈ D(A)` (membership in
`D(B)` is automatic).  Purely algebraic: decompose `ψ = (Bχ − Aχ) + (Aχ − zχ)` for
`χ := R_B(z)ψ` and collapse the second summand by `resolvent_left_inverse`. -/
theorem second_resolvent_identity
    {A B : H →ₗ.[ℂ] H}
    (hsymA : A.IsFormalAdjoint A)
    (hplusA : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminusA : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (hsymB : B.IsFormalAdjoint B)
    (hplusB  : ∀ φ : H, ∃ ψ : B.domain, B ψ + I • (ψ : H) = φ)
    (hminusB : ∀ φ : H, ∃ ψ : B.domain, B ψ - I • (ψ : H) = φ)
    (z : ℂ) (hz : z.im ≠ 0) (ψ : H)
    (hA_dom : resolvent z hz hsymB hplusB hminusB ψ ∈ A.domain) :
    resolvent z hz hsymA hplusA hminusA ψ - resolvent z hz hsymB hplusB hminusB ψ
      = resolvent z hz hsymA hplusA hminusA
          (B ⟨resolvent z hz hsymB hplusB hminusB ψ,
              resolvent_mem_domain hsymB hplusB hminusB z hz ψ⟩
            - A ⟨resolvent z hz hsymB hplusB hminusB ψ, hA_dom⟩) := by
  set χ : H := resolvent z hz hsymB hplusB hminusB ψ with _hχ
  have hmemB : χ ∈ B.domain := resolvent_mem_domain hsymB hplusB hminusB z hz ψ
  have hψ_eq : B ⟨χ, hmemB⟩ - z • χ = ψ := resolvent_solves hsymB hplusB hminusB z hz ψ
  have h_decomp : ψ = (B ⟨χ, hmemB⟩ - A ⟨χ, hA_dom⟩) + (A ⟨χ, hA_dom⟩ - z • χ) := by
    rw [← hψ_eq]; abel
  have hinv : resolvent z hz hsymA hplusA hminusA (A ⟨χ, hA_dom⟩ - z • χ) = χ :=
    resolvent_left_inverse hsymA hplusA hminusA z hz ⟨χ, hA_dom⟩
  calc resolvent z hz hsymA hplusA hminusA ψ - χ
      = resolvent z hz hsymA hplusA hminusA
          ((B ⟨χ, hmemB⟩ - A ⟨χ, hA_dom⟩) + (A ⟨χ, hA_dom⟩ - z • χ)) - χ := by
        rw [← h_decomp]
    _ = resolvent z hz hsymA hplusA hminusA (B ⟨χ, hmemB⟩ - A ⟨χ, hA_dom⟩)
          + resolvent z hz hsymA hplusA hminusA (A ⟨χ, hA_dom⟩ - z • χ) - χ := by
        rw [map_add]
    _ = resolvent z hz hsymA hplusA hminusA (B ⟨χ, hmemB⟩ - A ⟨χ, hA_dom⟩) := by
        rw [hinv]; abel

/-! ## Born series -/

/-- **Born series** for the perturbed resolvent.  For `A = B + V` with `V` bounded,
`D(A) = D(B)`, and `‖V·R_B(z)‖ < 1`:

  `R_A(z) = R_B(z) · Σₙ (−V·R_B(z))ⁿ`.

The inverse `(1 + V·R_B(z))⁻¹ = Σₙ (−V·R_B(z))ⁿ` is Mathlib's `Units.oneSub`; the only
content is the algebraic identity `R_A(z)·(1 + V·R_B(z)) = R_B(z)`, which is
`resolvent_left_inverse` after substituting `A = B + V` into `(B − z)R_B(z) = 1`. -/
theorem born_series
    {A B : H →ₗ.[ℂ] H}
    (hsymA : A.IsFormalAdjoint A)
    (hplusA : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminusA : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (hsymB : B.IsFormalAdjoint B)
    (hplusB  : ∀ φ : H, ∃ ψ : B.domain, B ψ + I • (ψ : H) = φ)
    (hminusB : ∀ φ : H, ∃ ψ : B.domain, B ψ - I • (ψ : H) = φ)
    (V : H →L[ℂ] H)
    (h_dom : A.domain = B.domain)
    (hV : ∀ (ψ : H) (hψ : ψ ∈ A.domain), A ⟨ψ, hψ⟩ = B ⟨ψ, h_dom ▸ hψ⟩ + V ψ)
    (z : ℂ) (hz : z.im ≠ 0)
    (h_small : ‖V * resolvent z hz hsymB hplusB hminusB‖ < 1) :
    resolvent z hz hsymA hplusA hminusA
      = resolvent z hz hsymB hplusB hminusB
        * ∑' n : ℕ, (-(V * resolvent z hz hsymB hplusB hminusB)) ^ n := by
  set R_B : H →L[ℂ] H := resolvent z hz hsymB hplusB hminusB with _hRB_def
  set T : H →L[ℂ] H := -(V * R_B) with hT_def
  have hT : ‖T‖ < 1 := by rw [hT_def, norm_neg]; exact h_small
  -- The algebraic identity: `R_A · (1 − T) = R_B`.
  have h_key : resolvent z hz hsymA hplusA hminusA * (1 - T) = R_B := by
    ext ψ
    simp only [ContinuousLinearMap.mul_apply, hT_def, sub_neg_eq_add]
    -- ⊢ R_A (ψ + V (R_B ψ)) = R_B ψ
    have hmemB : R_B ψ ∈ B.domain := resolvent_mem_domain hsymB hplusB hminusB z hz ψ
    have hmemA : R_B ψ ∈ A.domain := by rw [h_dom]; exact hmemB
    have hB_eq : B ⟨R_B ψ, hmemB⟩ - z • R_B ψ = ψ :=
      resolvent_solves hsymB hplusB hminusB z hz ψ
    have h_arg : ψ + V (R_B ψ) = A ⟨R_B ψ, hmemA⟩ - z • R_B ψ := by
      have hB' : B ⟨R_B ψ, hmemB⟩ = ψ + z • R_B ψ := eq_add_of_sub_eq hB_eq
      rw [hV (R_B ψ) hmemA,
        show B ⟨R_B ψ, h_dom ▸ hmemA⟩ = B ⟨R_B ψ, hmemB⟩ from rfl, hB']
      abel
    have hinv : resolvent z hz hsymA hplusA hminusA (A ⟨R_B ψ, hmemA⟩ - z • R_B ψ)
        = R_B ψ :=
      resolvent_left_inverse hsymA hplusA hminusA z hz ⟨R_B ψ, hmemA⟩
    simp [h_arg, hinv]
  -- Invert `1 − T` with the Neumann series unit and peel it off `h_key`.
  calc resolvent z hz hsymA hplusA hminusA
      = resolvent z hz hsymA hplusA hminusA * ((1 - T) * ∑' n : ℕ, T ^ n) := by
        rw [show (1 - T) * ∑' n : ℕ, T ^ n = 1 from (Units.oneSub T hT).val_inv, mul_one]
    _ = (resolvent z hz hsymA hplusA hminusA * (1 - T)) * ∑' n : ℕ, T ^ n := by
        rw [mul_assoc]
    _ = R_B * ∑' n : ℕ, T ^ n := by rw [h_key]

/-! ## Norm blowup at the spectrum -/

/-- The resolvent norm blows up near the spectrum: if every interval around `λ₀` carries
a nonzero spectral projection, then `‖R(λ₀ + iε)‖ → ∞` as `ε → 0⁺`.

Route: take `φ = E(B)ψ₀` for `B = (λ₀ − η, λ₀ + η)` with `η = 1/(2M)`.  Then `μ_φ` is
supported on `B` (`borelMeasure_spectralProjection_supported`), where
`‖s − (λ₀ + iε)‖ < 2η = 1/M`, so the `L²` identity forces `‖R(z)φ‖ ≥ M·‖φ‖`. -/
lemma resolvent_norm_blowup_at_spectrum (lambda₀ : ℝ)
    (h_spec : ∀ δ > 0, spectralProjection U_grp
      (Set.Ioo (lambda₀ - δ) (lambda₀ + δ)) measurableSet_Ioo ≠ 0) :
    Tendsto (fun ε : ℝ => if hε : 0 < ε then
        ‖resolvent (⟨lambda₀, ε⟩ : ℂ) hε.ne' (generator_isFormalAdjoint U_grp)
          (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp)‖
      else 0) (𝓝[>] 0) atTop := by
  rw [Filter.tendsto_atTop]
  intro M
  -- Trivial case: `M ≤ 0`.
  by_cases hM : M ≤ 0
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [Set.mem_Ioi] at hε
    simp only [dif_pos hε]
    linarith [norm_nonneg (resolvent (⟨lambda₀, ε⟩ : ℂ) hε.ne'
      (generator_isFormalAdjoint U_grp)
      (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp))]
  push Not at hM
  -- `η = 1/(2M)`, so `η + η = 1/M`.
  set η := 1 / (2 * M) with hη_def
  have hη_pos : 0 < η := by positivity
  have h2η : η + η = 1 / M := by
    have hη' : η = 1 / M / 2 := by rw [hη_def, div_div, mul_comm]
    rw [hη']
    ring
  -- A nonzero spectrally supported vector `φ = E(B)ψ₀`.
  set B := Set.Ioo (lambda₀ - η) (lambda₀ + η) with _hB_def
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀, spectralProjection U_grp B measurableSet_Ioo ψ₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact h_spec η hη_pos (ContinuousLinearMap.ext h)
  set φ := spectralProjection U_grp B measurableSet_Ioo ψ₀ with _hφ_def
  have hφ_pos : 0 < ‖φ‖ := norm_pos_iff.mpr hψ₀
  have h_supp : borelMeasure U_grp φ Bᶜ = 0 :=
    borelMeasure_spectralProjection_supported U_grp B measurableSet_Ioo ψ₀
  haveI : IsFiniteMeasure (borelMeasure U_grp φ) := borelMeasure_isFiniteMeasure U_grp φ
  -- Work on `ε ∈ (0, η)`.
  have h_Ioo_mem : Set.Ioo (0 : ℝ) η ∈ 𝓝[>] (0 : ℝ) := by
    rw [← Set.Ioi_inter_Iio]
    exact inter_mem_nhdsWithin _ (Iio_mem_nhds hη_pos)
  filter_upwards [h_Ioo_mem] with ε hε
  obtain ⟨hε_pos, hε_lt⟩ := hε
  simp only [dif_pos hε_pos]
  -- Triangle inequality on `B`: `‖s − (λ₀ + iε)‖ < η + η = 1/M`.
  have h_norm_bound : ∀ s ∈ B, ‖(s : ℂ) - (⟨lambda₀, ε⟩ : ℂ)‖ < 1 / M := by
    intro s hs
    have hs_abs : |s - lambda₀| < η :=
      abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have _hre : (⟨lambda₀, ε⟩ : ℂ).re = lambda₀ := rfl
    have _him : (⟨lambda₀, ε⟩ : ℂ).im = ε := rfl
    have hsplit : (s : ℂ) - (⟨lambda₀, ε⟩ : ℂ) = ((s - lambda₀ : ℝ) : ℂ) - ↑ε * I := by
      apply Complex.ext <;> norm_num
    calc ‖(s : ℂ) - (⟨lambda₀, ε⟩ : ℂ)‖
        = ‖((s - lambda₀ : ℝ) : ℂ) - ↑ε * I‖ := by rw [hsplit]
      _ ≤ ‖((s - lambda₀ : ℝ) : ℂ)‖ + ‖(↑ε * I : ℂ)‖ := norm_sub_le _ _
      _ = |s - lambda₀| + ε := by
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε_pos]
      _ < η + η := add_lt_add hs_abs hε_lt
      _ = 1 / M := h2η
  -- Hence `M² ≤ ‖(s − z)⁻¹‖²` on `B`.
  have h_fz_bound : ∀ s ∈ B, M ^ 2 ≤ ‖((s : ℂ) - (⟨lambda₀, ε⟩ : ℂ))⁻¹‖ ^ 2 := by
    intro s hs
    have h_pos : 0 < ‖(s : ℂ) - (⟨lambda₀, ε⟩ : ℂ)‖ :=
      norm_pos_iff.mpr (sub_ne_zero_of_im_ne_zero _ hε_pos.ne' s)
    have h_inv : M < ‖(s : ℂ) - (⟨lambda₀, ε⟩ : ℂ)‖⁻¹ := by
      rw [inv_eq_one_div, lt_div_iff₀ h_pos]
      calc M * ‖(s : ℂ) - (⟨lambda₀, ε⟩ : ℂ)‖
          < M * (1 / M) := mul_lt_mul_of_pos_left (h_norm_bound s hs) hM
        _ = 1 := by field_simp
    rw [norm_inv]
    exact pow_le_pow_left₀ hM.le h_inv.le 2
  -- Reduce `M ≤ ‖R(z)‖` to the squared vector bound.
  suffices h_lower : M * ‖φ‖ ≤ ‖resolvent (⟨lambda₀, ε⟩ : ℂ) hε_pos.ne'
      (generator_isFormalAdjoint U_grp) (range_plus_i_eq_top U_grp)
      (range_minus_i_eq_top U_grp) φ‖ by
    exact le_of_mul_le_mul_right
      (h_lower.trans (ContinuousLinearMap.le_opNorm _ φ)) hφ_pos
  suffices h_sq : (M * ‖φ‖) ^ 2 ≤ ‖resolvent (⟨lambda₀, ε⟩ : ℂ) hε_pos.ne'
      (generator_isFormalAdjoint U_grp) (range_plus_i_eq_top U_grp)
      (range_minus_i_eq_top U_grp) φ‖ ^ 2 by
    have h := Real.sqrt_le_sqrt h_sq
    rwa [Real.sqrt_sq (mul_nonneg hM.le (norm_nonneg _)),
      Real.sqrt_sq (norm_nonneg _)] at h
  -- The `L²` identity: `‖R(z)φ‖² = ∫ ‖(s − z)⁻¹‖² dμ_φ`.
  rw [resolvent_eq_spectralCalculus U_grp (⟨lambda₀, ε⟩ : ℂ) hε_pos.ne',
    norm_sq_spectralCalculus_apply, mul_pow]
  -- a.e. lower bound, from support of `μ_φ` in `B`.
  have h_mem_ae : ∀ᵐ s ∂(borelMeasure U_grp φ), s ∈ B := ae_iff.mpr h_supp
  have h_ae : ∀ᵐ (s : ℝ) ∂(borelMeasure U_grp φ),
      M ^ 2 ≤ ‖((s : ℂ) - (⟨lambda₀, ε⟩ : ℂ))⁻¹‖ ^ 2 :=
    h_mem_ae.mono fun s hs => h_fz_bound s hs
  -- Integrability of `‖(s − z)⁻¹‖²`, from the kernel bound at height `ε`.
  have h_int : Integrable (fun s : ℝ => ‖((s : ℂ) - (⟨lambda₀, ε⟩ : ℂ))⁻¹‖ ^ 2)
      (borelMeasure U_grp φ) := by
    refine (integrable_const ((1 / ε) ^ 2)).mono
      (((kernel_measurable _ hε_pos.ne').norm.pow_const 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have hb : ‖((s : ℂ) - (⟨lambda₀, ε⟩ : ℂ))⁻¹‖ ≤ 1 / ε := by
      have h := Spectra.Kernels.resolvent_integrand_bound (⟨lambda₀, ε⟩ : ℂ) hε_pos.ne' s
      rwa [show ((⟨lambda₀, ε⟩ : ℂ)).im = ε from rfl, abs_of_pos hε_pos] at h
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  -- Integrate the pointwise bound.
  calc M ^ 2 * ‖φ‖ ^ 2
      = ∫ _, M ^ 2 ∂(borelMeasure U_grp φ) := by
        rw [integral_const, smul_eq_mul, Measure.real_def, borelMeasure_mass, mul_comm]
    _ ≤ ∫ (s : ℝ), ‖((s : ℂ) - (⟨lambda₀, ε⟩ : ℂ))⁻¹‖ ^ 2 ∂(borelMeasure U_grp φ) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity)
          h_int h_ae

/-! ## Stieltjes inversion -/

/-- **Stieltjes inversion**: recovering the spectral density from the resolvent.  If
`μ_ψ` has a continuous nonneg density `ρ` w.r.t. Lebesgue measure, then

  `(1/π) · Im ⟪ψ, R(λ₀ + iε)ψ⟫ → ρ(λ₀)` as `ε → 0⁺`.

Route: `im_inner_resolvent_diag` turns the left side into the Lorentzian smearing of
`μ_ψ = ρ·dx`, and `lorentzian_approx_delta` is the approximate-identity limit. -/
theorem stieltjes_inversion (ψ : H) (lambda₀ : ℝ)
    (ρ : ℝ → ℝ) (hρ_cont : Continuous ρ) (hρ_nn : ∀ s, 0 ≤ ρ s)
    (hρ_density : ∀ B, MeasurableSet B →
      borelMeasure U_grp ψ B = ∫⁻ s in B, ENNReal.ofReal (ρ s)) :
    Tendsto (fun ε : ℝ => if hε : 0 < ε then
        (1 / Real.pi) * (⟪ψ, resolvent (⟨lambda₀, ε⟩ : ℂ) hε.ne'
          (generator_isFormalAdjoint U_grp) (range_plus_i_eq_top U_grp)
          (range_minus_i_eq_top U_grp) ψ⟫_ℂ).im
      else 0) (𝓝[>] 0) (𝓝 (ρ lambda₀)) := by
  set μ := borelMeasure U_grp ψ with _hμ_def
  haveI hμ_fin : IsFiniteMeasure μ := borelMeasure_isFiniteMeasure U_grp ψ
  -- ═══ Step 0: reduce via the Poisson representation ═══
  suffices h_main : Tendsto (fun ε : ℝ =>
      (1 / Real.pi) * ∫ s, ε / ((s - lambda₀) ^ 2 + ε ^ 2) ∂μ)
      (𝓝[>] 0) (𝓝 (ρ lambda₀)) by
    refine h_main.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    simp only [dif_pos hε]
    congr 1
    exact (im_inner_resolvent_diag U_grp lambda₀ hε ψ).symm
  -- ═══ Step 1: `μ = ρ · volume` ═══
  have h_wd : μ = volume.withDensity (fun s => ENNReal.ofReal (ρ s)) :=
    Measure.ext fun B hB => by rw [hρ_density B hB]; exact (withDensity_apply _ hB).symm
  -- ═══ Step 2: integrability of `ρ` ═══
  have hρ_lint_ne_top : ∫⁻ s, ENNReal.ofReal (ρ s) ≠ ⊤ := by
    have h := hρ_density Set.univ MeasurableSet.univ
    simp only [Measure.restrict_univ] at h
    rw [← h]
    exact measure_ne_top μ Set.univ
  have hρ_int : Integrable ρ volume :=
    (integrable_toReal_of_lintegral_ne_top
      (hρ_cont.measurable.ennreal_ofReal.aemeasurable) hρ_lint_ne_top).congr
      (Filter.Eventually.of_forall fun s => ENNReal.toReal_ofReal (hρ_nn s))
  -- ═══ Step 3: `lorentzian_approx_delta` applied to `ofReal ∘ ρ` ═══
  have hρ_cint : Integrable (Complex.ofReal ∘ ρ) volume :=
    hρ_int.mono (Complex.continuous_ofReal.comp hρ_cont).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => by simp [Real.norm_eq_abs])
  have h_approx := lorentzian_approx_delta (Complex.ofReal ∘ ρ)
    (Complex.continuous_ofReal.comp hρ_cont) hρ_cint lambda₀
  -- ═══ Step 4: take `.re` ═══
  have h_re : Tendsto (fun ε : ℝ =>
      ((1 / (Real.pi : ℝ)) • ∫ s, (ε / ((s - lambda₀) ^ 2 + ε ^ 2)) •
        (↑(ρ s) : ℂ)).re) (𝓝[>] 0) (𝓝 (ρ lambda₀)) := by
    have h := (Complex.continuous_re.tendsto _).comp h_approx
    simp only [Function.comp_def, Complex.ofReal_re] at h
    exact h
  -- ═══ Step 5: connect the two forms ═══
  refine h_re.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (_hε : 0 < ε)
  set K := fun s => ε / ((s - lambda₀) ^ 2 + ε ^ 2) with hK_def
  -- `.re` of the ℝ-smul: `(r • z).re = r * z.re`.
  have h_smul_re : ((1 / (Real.pi : ℝ)) • ∫ s, K s • (↑(ρ s) : ℂ)).re =
      (1 / Real.pi) * (∫ s, K s • (↑(ρ s) : ℂ)).re := by
    simp [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [h_smul_re]
  congr 1
  -- `.re` of the integral: both factors are real.
  have h_re_integral : (∫ s, K s • (↑(ρ s) : ℂ)).re = ∫ s, K s * ρ s := by
    have h_eq : (fun s => K s • (↑(ρ s) : ℂ)) = fun s => (↑(K s * ρ s) : ℂ) := by
      ext s; simp [Complex.real_smul, Complex.ofReal_mul]
    rw [h_eq]
    calc (∫ s, (↑(K s * ρ s) : ℂ)).re
        = (↑(∫ s, K s * ρ s) : ℂ).re := by
          congr 1
          exact integral_complex_ofReal
      _ = ∫ s, K s * ρ s := Complex.ofReal_re _
  rw [h_re_integral]
  -- Change of measure: `∫ K dμ = ∫ K·ρ dvol`.
  rw [h_wd, show (fun s => ENNReal.ofReal (ρ s)) = (fun s => ↑((ρ s).toNNReal)) from rfl,
    integral_withDensity_eq_integral_smul hρ_cont.measurable.real_toNNReal]
  congr 1
  ext s
  simp only [hK_def, NNReal.smul_def, Real.coe_toNNReal _ (hρ_nn s), mul_comm]
  exact Eq.symm (smul_eq_mul (ρ s) (ε / ((s - lambda₀) ^ 2 + ε ^ 2)))

end Spectra.Resolvent
