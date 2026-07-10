/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SpectralTheory.Essential.Defs
import Spectra.SpectralTheory.Essential.WeakCompact
import Spectra.SpectralTheory.ResolventForm
import Spectra.SpectralTheory.StoneFormula.Identities

/-!
# Weyl's theorem: invariance of the essential spectrum under a compact resolvent perturbation

If `A`, `B` are self-adjoint operators whose resolvents at `i` differ by a **compact** operator,
then `essSpectrum hA = essSpectrum hB`.

The hypothesis is purely about the *bounded* operators: `IsCompactOperator (R_B(i) − R_A(i))`.
It is symmetric in `A` and `B` (via `IsCompactOperator.neg`), so the equality follows from a
single inclusion proved twice.

## The proof (one inclusion)

Given a Weyl sequence `ψ` for `A` at `λ`, set `φ n := R_B(i)·(A − i)ψ n ∈ D(B)`.  Since
`R_A(i)·(A − i)ψ n = ψ n` and `K := R_B(i) − R_A(i)` is compact, `φ n = ψ n + K·(A − i)ψ n`, and
`(A − i)ψ n` is bounded and weakly null, so `K·(A − i)ψ n → 0`
(`IsCompactOperator.tendsto_norm_apply_of_weaklyNull`).  Hence `φ n = ψ n + o(1)`: it is
asymptotically normalized and weakly null.  Finally `(B − i)φ n = (A − i)ψ n`, so
`(B − λ)φ n = (A − λ)ψ n + (λ − i)(ψ n − φ n) → 0`.  Thus `φ` is a Weyl sequence for `B` at `λ`.

## Main results

* `Spectra.Essential.essSpectrum_subset_of_isCompactOperator_resolvent_sub`
* `Spectra.Essential.essSpectrum_eq_of_isCompactOperator_resolvent_sub` — **Weyl's theorem**.
-/

open Filter Topology Complex
open scoped InnerProductSpace
open Spectra.Resolvent Spectra.QuantumMechanics.SpectralTheory Spectra.YosidaHille

namespace Spectra.Essential

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `i` is off the real axis, the spectral parameter used throughout. -/
theorem I_im_ne_zero : (Complex.I).im ≠ 0 := by rw [Complex.I_im]; exact one_ne_zero

/-! ### The bounded resolvent, repackaged from the raw `Resolvent.resolvent` lemmas -/

/-- The resolvent maps into the domain. -/
theorem selfAdjointResolvent_mem_domain {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (z : ℂ)
    (hz : z.im ≠ 0) (φ : H) : selfAdjointResolvent hA z hz φ ∈ A.domain :=
  resolvent_mem_domain _ _ _ z hz φ

/-- `(A − z)(R(z)φ) = φ`. -/
theorem selfAdjointResolvent_solves {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (z : ℂ)
    (hz : z.im ≠ 0) (φ : H) :
    A ⟨selfAdjointResolvent hA z hz φ, selfAdjointResolvent_mem_domain hA z hz φ⟩
        - z • selfAdjointResolvent hA z hz φ = φ :=
  resolvent_solves _ _ _ z hz φ

/-- `R(z)(Aψ − z•ψ) = ψ` for `ψ ∈ D(A)`. -/
theorem selfAdjointResolvent_left_inverse {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (z : ℂ)
    (hz : z.im ≠ 0) (ψ : A.domain) :
    selfAdjointResolvent hA z hz (A ψ - z • (ψ : H)) = (ψ : H) :=
  resolvent_left_inverse _ _ _ z hz ψ

/-! ### Weyl's theorem -/

/-- **One inclusion of Weyl's theorem.**  If the resolvent difference `R_B(i) − R_A(i)` is compact,
then `essSpectrum hA ⊆ essSpectrum hB`. -/
theorem essSpectrum_subset_of_isCompactOperator_resolvent_sub
    {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hcompact : IsCompactOperator
      ((selfAdjointResolvent hB I I_im_ne_zero
        - selfAdjointResolvent hA I I_im_ne_zero : H →L[ℂ] H) : H → H)) :
    essSpectrum hA ⊆ essSpectrum hB := by
  intro lam hlam
  obtain ⟨ψ, hψ_norm, hψ_weak, hψ_eig⟩ := hlam
  -- `R_A(i)·(A − i)ψ n = ψ n`.
  have hRAinv : ∀ n, selfAdjointResolvent hA I I_im_ne_zero
      (A (ψ n) - I • (ψ n : H)) = (ψ n : H) :=
    fun n => selfAdjointResolvent_left_inverse hA I I_im_ne_zero (ψ n)
  -- `R_B(i)·(A − i)ψ n = ψ n + K·(A − i)ψ n`.
  have hΦval : ∀ n, selfAdjointResolvent hB I I_im_ne_zero (A (ψ n) - I • (ψ n : H))
      = (ψ n : H) + (selfAdjointResolvent hB I I_im_ne_zero
          - selfAdjointResolvent hA I I_im_ne_zero) (A (ψ n) - I • (ψ n : H)) := by
    intro n
    rw [ContinuousLinearMap.sub_apply, hRAinv n]; abel
  -- `(A − λ)ψ n → 0` as vectors.
  have hAeig : Tendsto (fun n => A (ψ n) - (lam : ℂ) • (ψ n : H)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hψ_eig
  -- `(A − i)ψ n` is weakly null.
  have hw_weak : ∀ g : H, Tendsto (fun n => ⟪g, A (ψ n) - I • (ψ n : H)⟫_ℂ) atTop (𝓝 0) := by
    intro g
    have e1 : Tendsto (fun n => ⟪g, A (ψ n) - (lam : ℂ) • (ψ n : H)⟫_ℂ) atTop (𝓝 0) := by
      have h : Tendsto (fun n => ⟪g, A (ψ n) - (lam : ℂ) • (ψ n : H)⟫_ℂ) atTop
          (𝓝 (⟪g, (0 : H)⟫_ℂ)) := Tendsto.inner tendsto_const_nhds hAeig
      simpa only [inner_zero_right] using h
    have e2 : Tendsto (fun n => ((lam : ℂ) - I) * ⟪g, (ψ n : H)⟫_ℂ) atTop (𝓝 0) := by
      simpa using (hψ_weak g).const_mul ((lam : ℂ) - I)
    have hsum := e1.add e2
    rw [add_zero] at hsum
    refine hsum.congr (fun n => ?_)
    rw [inner_sub_right, inner_smul_right, inner_sub_right, inner_smul_right]; ring
  -- `(A − i)ψ n` is bounded.
  have hw_bdd : ∃ C, ∀ n, ‖A (ψ n) - I • (ψ n : H)‖ ≤ C := by
    have hb : Tendsto (fun n => ‖A (ψ n) - (lam : ℂ) • (ψ n : H)‖
        + ‖(lam : ℂ) - I‖ * ‖(ψ n : H)‖) atTop (𝓝 (0 + ‖(lam : ℂ) - I‖ * 1)) :=
      hψ_eig.add (hψ_norm.const_mul ‖(lam : ℂ) - I‖)
    obtain ⟨C, hC⟩ := hb.bddAbove_range
    refine ⟨C, fun n => le_trans ?_ (hC (Set.mem_range_self n))⟩
    calc ‖A (ψ n) - I • (ψ n : H)‖
        = ‖(A (ψ n) - (lam : ℂ) • (ψ n : H)) + ((lam : ℂ) - I) • (ψ n : H)‖ := by
          congr 1; module
      _ ≤ ‖A (ψ n) - (lam : ℂ) • (ψ n : H)‖ + ‖((lam : ℂ) - I) • (ψ n : H)‖ := norm_add_le _ _
      _ = ‖A (ψ n) - (lam : ℂ) • (ψ n : H)‖ + ‖(lam : ℂ) - I‖ * ‖(ψ n : H)‖ := by rw [norm_smul]
  -- `K·(A − i)ψ n → 0`.
  obtain ⟨C, hC⟩ := hw_bdd
  have hKw : Tendsto (fun n => ‖(selfAdjointResolvent hB I I_im_ne_zero
      - selfAdjointResolvent hA I I_im_ne_zero) (A (ψ n) - I • (ψ n : H))‖) atTop (𝓝 0) :=
    IsCompactOperator.tendsto_norm_apply_of_weaklyNull hcompact hC hw_weak
  have hKw0 : Tendsto (fun n => (selfAdjointResolvent hB I I_im_ne_zero
      - selfAdjointResolvent hA I I_im_ne_zero) (A (ψ n) - I • (ψ n : H))) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hKw
  -- `R_B(i)·(A − i)ψ n − ψ n = K·(A − i)ψ n`.
  have hsub : ∀ n, selfAdjointResolvent hB I I_im_ne_zero (A (ψ n) - I • (ψ n : H)) - (ψ n : H)
      = (selfAdjointResolvent hB I I_im_ne_zero - selfAdjointResolvent hA I I_im_ne_zero)
          (A (ψ n) - I • (ψ n : H)) := fun n => by rw [hΦval n]; abel
  -- Assemble the perturbed Weyl sequence `φ n := R_B(i)·(A − i)ψ n`.
  refine mem_essSpectrum_of_seq hB lam
    (fun n => selfAdjointResolvent hB I I_im_ne_zero (A (ψ n) - I • (ψ n : H)))
    (fun n => selfAdjointResolvent_mem_domain hB I I_im_ne_zero _) ?_ ?_ ?_
  · -- `‖φ n‖ → 1`.
    have hgtend : Tendsto (fun n => -‖(selfAdjointResolvent hB I I_im_ne_zero
        - selfAdjointResolvent hA I I_im_ne_zero) (A (ψ n) - I • (ψ n : H))‖) atTop (𝓝 0) := by
      simpa only [neg_zero] using hKw.neg
    have hnormdiff : Tendsto (fun n => ‖selfAdjointResolvent hB I I_im_ne_zero
        (A (ψ n) - I • (ψ n : H))‖ - ‖(ψ n : H)‖) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hgtend hKw ?_ ?_
      · intro n
        have hb := abs_norm_sub_norm_le (selfAdjointResolvent hB I I_im_ne_zero
          (A (ψ n) - I • (ψ n : H))) ((ψ n : H))
        rw [hsub n] at hb
        exact (abs_le.mp hb).1
      · intro n
        have hb := abs_norm_sub_norm_le (selfAdjointResolvent hB I I_im_ne_zero
          (A (ψ n) - I • (ψ n : H))) ((ψ n : H))
        rw [hsub n] at hb
        exact (abs_le.mp hb).2
    have hfin := hnormdiff.add hψ_norm
    rw [zero_add] at hfin
    exact hfin.congr (fun n => by ring)
  · -- `φ` weakly null.
    intro g
    have e1 : Tendsto (fun n => ⟪g, (ψ n : H)⟫_ℂ) atTop (𝓝 0) := hψ_weak g
    have e2 : Tendsto (fun n => ⟪g, (selfAdjointResolvent hB I I_im_ne_zero
        - selfAdjointResolvent hA I I_im_ne_zero) (A (ψ n) - I • (ψ n : H))⟫_ℂ) atTop (𝓝 0) := by
      have h : Tendsto (fun n => ⟪g, (selfAdjointResolvent hB I I_im_ne_zero
          - selfAdjointResolvent hA I I_im_ne_zero) (A (ψ n) - I • (ψ n : H))⟫_ℂ) atTop
          (𝓝 (⟪g, (0 : H)⟫_ℂ)) := Tendsto.inner tendsto_const_nhds hKw0
      simpa only [inner_zero_right] using h
    have hsum := e1.add e2
    rw [add_zero] at hsum
    refine hsum.congr (fun n => ?_)
    rw [← inner_add_right, ← hΦval n]
  · -- `(B − λ)φ n → 0`.
    have hKterm : Tendsto (fun n => ((lam : ℂ) - I) • (selfAdjointResolvent hB I I_im_ne_zero
        - selfAdjointResolvent hA I I_im_ne_zero) (A (ψ n) - I • (ψ n : H))) atTop (𝓝 0) := by
      simpa only [smul_zero] using hKw0.const_smul ((lam : ℂ) - I)
    have hc_vec : Tendsto (fun n =>
        B ⟨selfAdjointResolvent hB I I_im_ne_zero (A (ψ n) - I • (ψ n : H)),
            selfAdjointResolvent_mem_domain hB I I_im_ne_zero (A (ψ n) - I • (ψ n : H))⟩
          - (lam : ℂ) • selfAdjointResolvent hB I I_im_ne_zero (A (ψ n) - I • (ψ n : H)))
        atTop (𝓝 0) := by
      have hsum := hAeig.sub hKterm
      rw [sub_zero] at hsum
      refine hsum.congr (fun n => ?_)
      have hsolve := selfAdjointResolvent_solves hB I I_im_ne_zero (A (ψ n) - I • (ψ n : H))
      have hBΦ : B ⟨selfAdjointResolvent hB I I_im_ne_zero (A (ψ n) - I • (ψ n : H)),
          selfAdjointResolvent_mem_domain hB I I_im_ne_zero (A (ψ n) - I • (ψ n : H))⟩
          = (A (ψ n) - I • (ψ n : H))
            + I • selfAdjointResolvent hB I I_im_ne_zero (A (ψ n) - I • (ψ n : H)) :=
        sub_eq_iff_eq_add.mp hsolve
      rw [hBΦ, hΦval n]; module
    exact tendsto_zero_iff_norm_tendsto_zero.mp hc_vec

/-- **Weyl's theorem.**  If the resolvents `R_A(i)`, `R_B(i)` of two self-adjoint operators differ
by a compact operator, then `A` and `B` have the same essential spectrum. -/
theorem essSpectrum_eq_of_isCompactOperator_resolvent_sub
    {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hcompact : IsCompactOperator
      ((selfAdjointResolvent hB I I_im_ne_zero
        - selfAdjointResolvent hA I I_im_ne_zero : H →L[ℂ] H) : H → H)) :
    essSpectrum hA = essSpectrum hB := by
  apply Set.Subset.antisymm
  · exact essSpectrum_subset_of_isCompactOperator_resolvent_sub hA hB hcompact
  · apply essSpectrum_subset_of_isCompactOperator_resolvent_sub hB hA
    have hCLM : (selfAdjointResolvent hA I I_im_ne_zero - selfAdjointResolvent hB I I_im_ne_zero
          : H →L[ℂ] H)
        = -(selfAdjointResolvent hB I I_im_ne_zero - selfAdjointResolvent hA I I_im_ne_zero) := by
      abel
    rw [hCLM]
    exact hcompact.neg

/-! ### On-ramp: relatively compact perturbations -/

/-- **On-ramp from a relatively compact perturbation.**  If `B − A` is represented on `D(A)` by a
*bounded compact* operator post-composed with the resolvent — i.e. there is a compact
`W : H →L[ℂ] H` with `(B − A)χ = W ((A − i)χ)` for every `χ ∈ D(A)` (think `W = V·(A − i)⁻¹`) —
then the resolvent difference `R_B(i) − R_A(i)` is compact.

The proof is the second resolvent identity in disguise: `R_B(i)ψ = R_A(i)ψ − R_B(i)(W ψ)`, so
`R_B(i) − R_A(i) = −R_B(i) ∘ W`, compact because `W` is. -/
theorem isCompactOperator_resolvent_sub_of_isCompactOperator_perturb
    {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hdom : A.domain = B.domain) (W : H →L[ℂ] H) (hW : IsCompactOperator (W : H → H))
    (hVW : ∀ (χ : H) (hχ : χ ∈ A.domain),
        B ⟨χ, hdom ▸ hχ⟩ - A ⟨χ, hχ⟩ = W (A ⟨χ, hχ⟩ - I • χ)) :
    IsCompactOperator ((selfAdjointResolvent hB I I_im_ne_zero
        - selfAdjointResolvent hA I I_im_ne_zero : H →L[ℂ] H) : H → H) := by
  have key : (selfAdjointResolvent hB I I_im_ne_zero - selfAdjointResolvent hA I I_im_ne_zero)
      = -((selfAdjointResolvent hB I I_im_ne_zero).comp W) := by
    ext ψ
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.comp_apply]
    set χ := selfAdjointResolvent hA I I_im_ne_zero ψ with _hχ
    have memA : χ ∈ A.domain := selfAdjointResolvent_mem_domain hA I I_im_ne_zero ψ
    have hsolveA : A ⟨χ, memA⟩ - I • χ = ψ := selfAdjointResolvent_solves hA I I_im_ne_zero ψ
    have hinvB : selfAdjointResolvent hB I I_im_ne_zero (B ⟨χ, hdom ▸ memA⟩ - I • χ) = χ :=
      selfAdjointResolvent_left_inverse hB I I_im_ne_zero ⟨χ, hdom ▸ memA⟩
    have hWχ : B ⟨χ, hdom ▸ memA⟩ - A ⟨χ, memA⟩ = W ψ := by rw [hVW χ memA, hsolveA]
    have hRBψ : selfAdjointResolvent hB I I_im_ne_zero ψ
        = χ - selfAdjointResolvent hB I I_im_ne_zero (W ψ) := by
      have h1 : ψ = (B ⟨χ, hdom ▸ memA⟩ - I • χ) - (B ⟨χ, hdom ▸ memA⟩ - A ⟨χ, memA⟩) := by
        rw [← hsolveA]; abel
      calc selfAdjointResolvent hB I I_im_ne_zero ψ
          = selfAdjointResolvent hB I I_im_ne_zero
              ((B ⟨χ, hdom ▸ memA⟩ - I • χ) - (B ⟨χ, hdom ▸ memA⟩ - A ⟨χ, memA⟩)) := by rw [h1]
        _ = selfAdjointResolvent hB I I_im_ne_zero (B ⟨χ, hdom ▸ memA⟩ - I • χ)
              - selfAdjointResolvent hB I I_im_ne_zero (B ⟨χ, hdom ▸ memA⟩ - A ⟨χ, memA⟩) := by
            rw [map_sub]
        _ = χ - selfAdjointResolvent hB I I_im_ne_zero (W ψ) := by rw [hinvB, hWχ]
    rw [hRBψ]; abel
  rw [key]
  exact (hW.clm_comp (selfAdjointResolvent hB I I_im_ne_zero)).neg

/-- **Weyl's theorem for relatively compact perturbations.**  If `B − A` is given on `D(A)` by a
compact `W = V·(A − i)⁻¹` (see `isCompactOperator_resolvent_sub_of_isCompactOperator_perturb`),
then `A` and `B` have the same essential spectrum.  This is the form that applies to Schrödinger
operators `B = −Δ + V` with `V` relatively compact (e.g. the hydrogen Hamiltonian). -/
theorem essSpectrum_eq_of_isCompactOperator_perturb
    {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hdom : A.domain = B.domain) (W : H →L[ℂ] H) (hW : IsCompactOperator (W : H → H))
    (hVW : ∀ (χ : H) (hχ : χ ∈ A.domain),
        B ⟨χ, hdom ▸ hχ⟩ - A ⟨χ, hχ⟩ = W (A ⟨χ, hχ⟩ - I • χ)) :
    essSpectrum hA = essSpectrum hB :=
  essSpectrum_eq_of_isCompactOperator_resolvent_sub hA hB
    (isCompactOperator_resolvent_sub_of_isCompactOperator_perturb hA hB hdom W hW hVW)

end Spectra.Essential
