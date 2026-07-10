/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SpectralTheory.Spectrum
import Spectra.SpectralTheory.Essential.Defs
import Spectra.SpectralTheory.Eigenspace
import Spectra.SpectralTheory.Measure.GeneratorLink
import Mathlib.Data.Nat.Nth

/-!
# Spectrum below the essential spectrum is point spectrum (the discreteness theorem)

The hard half of the Weyl theory: a spectral point of a self-adjoint operator that is **not** in
the essential spectrum is an **eigenvalue**.  Equivalently, a spectral point that is not an
eigenvalue (`E({λ}) = 0`) carries a *singular Weyl sequence*, so it is essential spectrum.

## Strategy (no weak limits, no closed-operator analysis)

The core is `mem_essSpectrum_of_proj_singleton_eq_zero`: if `λ ∈ spectrum A` and `E({λ}) = 0` we
build an **orthonormal approximate eigensequence** directly out of the spectral measure, using
disjoint *spectral annuli* `Cₖ = Dₖ \ Dₖ₊₁` where `Dₖ = (λ − 1/(k+1), λ + 1/(k+1))`:

* `λ ∈ spectrum` forces `E(Dₖ) ≠ 0` for every `k`; with `E({λ}) = 0` and countable
  *sub*additivity of the (finite) diagonal measures, **infinitely many** annuli carry nonzero
  spectral mass;
* pick a unit vector `ψₙ ∈ range E(C_{kₙ})` along an increasing index sequence — the annuli are
  pairwise disjoint, so the `ψₙ` are orthonormal, and the spectral localization bound
  `generator_sub_smul_norm_le_Icc` gives `‖A ψₙ − λ ψₙ‖ ≤ 1/(kₙ+1) → 0`;
* `mem_essSpectrum_of_orthonormal` finishes.

The contrapositive is `mem_pointSpectrum_of_mem_spectrum_notMem_essSpectrum`, which extracts a
genuine eigenvector from `E({λ}) ≠ 0` via `spectralPVM_proj_singleton_apply_isEigen`.
-/

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal
open Spectra.Borel SpectralMeasure
open Spectra.OneParameterUnitaryGroup Spectra.YosidaHille Spectra.Resolvent Spectra.Essential

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.ProjValMeasure

/-- **Orthogonality of disjoint spectral subspaces.**  For a projection-valued measure `P` and
disjoint measurable sets `B₁`, `B₂`, the ranges of `E(B₁)` and `E(B₂)` are orthogonal. -/
lemma inner_proj_eq_zero_of_disjoint (P : Spectra.ProjValMeasure H)
    {B₁ B₂ : Set ℝ} (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂)
    (hd : Disjoint B₁ B₂) (x y : H) :
    inner ℂ (P.proj B₁ hB₁ x) (P.proj B₂ hB₂ y) = 0 := by
  have hinter : B₁ ∩ B₂ = (∅ : Set ℝ) := Set.disjoint_iff_inter_eq_empty.mp hd
  have key : P.proj B₁ hB₁ (P.proj B₂ hB₂ y) = 0 := by
    have hmul : (P.proj B₁ hB₁ * P.proj B₂ hB₂) y = P.proj (B₁ ∩ B₂) (hB₁.inter hB₂) y := by
      rw [P.proj_inter B₁ B₂ hB₁ hB₂]
    have hz : P.proj (B₁ ∩ B₂) (hB₁.inter hB₂) = 0 := by
      rw [P.proj_congr hinter (hB₁.inter hB₂) MeasurableSet.empty]; exact P.proj_empty
    rw [ContinuousLinearMap.mul_apply] at hmul
    rw [hmul, hz, ContinuousLinearMap.zero_apply]
  have hadj : ContinuousLinearMap.adjoint (P.proj B₁ hB₁) = P.proj B₁ hB₁ := by
    have := P.isSelfAdjoint_proj B₁ hB₁
    rwa [ContinuousLinearMap.isSelfAdjoint_iff'] at this
  calc inner ℂ (P.proj B₁ hB₁ x) (P.proj B₂ hB₂ y)
      = inner ℂ x (ContinuousLinearMap.adjoint (P.proj B₁ hB₁) (P.proj B₂ hB₂ y)) :=
        (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
    _ = inner ℂ x (P.proj B₁ hB₁ (P.proj B₂ hB₂ y)) := by rw [hadj]
    _ = inner ℂ x (0 : H) := by rw [key]
    _ = 0 := inner_zero_right _

/-- A vector in the range of `E(B')` is fixed by `E(B)` whenever `B' ⊆ B`. -/
lemma proj_apply_of_subset (P : Spectra.ProjValMeasure H)
    {B B' : Set ℝ} (hB : MeasurableSet B) (hB' : MeasurableSet B') (hsub : B' ⊆ B) (x : H) :
    P.proj B hB (P.proj B' hB' x) = P.proj B' hB' x := by
  have hmul : (P.proj B hB * P.proj B' hB') x = P.proj (B ∩ B') (hB.inter hB') x := by
    rw [P.proj_inter B B' hB hB']
  rw [ContinuousLinearMap.mul_apply] at hmul
  rw [hmul, P.proj_congr (Set.inter_eq_right.mpr hsub) (hB.inter hB') hB']

/-- If `E(B) y = 0` then the diagonal measure of `y` vanishes on `B`. -/
lemma diag_apply_eq_zero_of_proj_apply_eq_zero (P : Spectra.ProjValMeasure H)
    {B : Set ℝ} (hB : MeasurableSet B) {y : H} (h : P.proj B hB y = 0) : (P.diag y) B = 0 := by
  haveI := P.diag_finite y
  have hh := P.norm_sq_proj_apply B hB y
  rw [h, norm_zero] at hh
  have h0 : ((P.diag y) B).toReal = 0 := by rw [← hh]; ring
  rcases (ENNReal.toReal_eq_zero_iff _).mp h0 with h1 | htop
  · exact h1
  · exact absurd htop (measure_ne_top _ _)

/-- If the diagonal measure of `y` vanishes on `B` then `E(B) y = 0`. -/
lemma proj_apply_eq_zero_of_diag_apply_eq_zero (P : Spectra.ProjValMeasure H)
    {B : Set ℝ} (hB : MeasurableSet B) {y : H} (h : (P.diag y) B = 0) : P.proj B hB y = 0 := by
  have hh := P.norm_sq_proj_apply B hB y
  rw [h, ENNReal.toReal_zero] at hh
  have : ‖P.proj B hB y‖ = 0 := by nlinarith [norm_nonneg (P.proj B hB y), hh]
  exact norm_eq_zero.mp this

/-- A vector orthogonal to the range of the (self-adjoint) projection `E(B)` is annihilated
by it. -/
lemma proj_apply_eq_zero_of_mem_orthogonal (P : Spectra.ProjValMeasure H)
    {B : Set ℝ} (hB : MeasurableSet B) {y : H}
    (hy : y ∈ (LinearMap.range (P.proj B hB : H →ₗ[ℂ] H))ᗮ) : P.proj B hB y = 0 := by
  have h0 : inner ℂ (P.proj B hB y) y = 0 :=
    (Submodule.mem_orthogonal _ y).mp hy _ ⟨y, rfl⟩
  have hadj : ContinuousLinearMap.adjoint (P.proj B hB) = P.proj B hB := by
    have := P.isSelfAdjoint_proj B hB; rwa [ContinuousLinearMap.isSelfAdjoint_iff'] at this
  have hidem : P.proj B hB (P.proj B hB y) = P.proj B hB y :=
    P.proj_apply_of_subset hB hB (subset_refl _) y
  have hself : inner ℂ (P.proj B hB y) (P.proj B hB y) = 0 := by
    have e1 : inner ℂ (ContinuousLinearMap.adjoint (P.proj B hB) y) (P.proj B hB y)
        = inner ℂ y (P.proj B hB (P.proj B hB y)) := ContinuousLinearMap.adjoint_inner_left _ _ _
    rw [hadj, hidem] at e1
    rw [e1, ← inner_conj_symm, h0, map_zero]
  exact inner_self_eq_zero.mp hself

end Spectra.ProjValMeasure

namespace Spectra.QuantumMechanics.SpectralTheory

/-- **The contrapositive core of the discreteness theorem.**  If `λ` is in the spectrum of the
self-adjoint operator `A` but is *not* an eigenvalue (the spectral atom `E({λ})` vanishes), then
`λ` lies in the essential spectrum: a singular Weyl sequence is built from disjoint spectral
annuli accumulating at `λ`. -/
theorem mem_essSpectrum_of_proj_singleton_eq_zero {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {lam : ℝ} (hspec : lam ∈ spectrum A)
    (hsing : (PVM.spectralPVM hA).proj {lam} (measurableSet_singleton lam) = 0) :
    lam ∈ essSpectrum hA := by
  classical
  set P := PVM.spectralPVM hA with _hP
  set U := genToGroup hA with hU
  have hgenU : generator U = A := by rw [hU]; exact generator_genToGroup hA
  set D : ℕ → Set ℝ := fun k => Set.Ioo (lam - 1 / (k + 1)) (lam + 1 / (k + 1)) with hD
  have hDm : ∀ k, MeasurableSet (D k) := fun _ => measurableSet_Ioo
  set C : ℕ → Set ℝ := fun k => D k \ D (k + 1) with hC
  have hCm : ∀ k, MeasurableSet (C k) := fun k => (hDm k).diff (hDm (k + 1))
  have hpos : ∀ k : ℕ, (0 : ℝ) < 1 / (k + 1) := fun k => by positivity
  have hDmem : ∀ (k : ℕ) (y : ℝ), y ∈ D k ↔ |y - lam| < 1 / (k + 1) := by
    intro k y
    rw [hD]; simp only [Set.mem_Ioo, abs_lt]
    constructor <;> intro h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hlam_mem : ∀ k, lam ∈ D k := fun k => (hDmem k lam).mpr (by simpa using hpos k)
  have hDanti : Antitone D := by
    intro a b hab y hy
    rw [hDmem] at hy ⊢
    have : 1 / ((b : ℝ) + 1) ≤ 1 / (a + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
    linarith
  have hCsubD : ∀ k, C k ⊆ D k := fun k => Set.diff_subset
  -- finite-measure ↔ projection-zero
  have proj_zero_diag_zero : ∀ {B : Set ℝ} (hB : MeasurableSet B),
      P.proj B hB = 0 → ∀ φ, (P.diag φ) B = 0 := by
    intro B hB hzero φ
    haveI := P.diag_finite φ
    have h := P.norm_sq_proj_apply B hB φ
    rw [hzero, ContinuousLinearMap.zero_apply, norm_zero] at h
    have h0 : ((P.diag φ) B).toReal = 0 := by rw [← h]; ring
    rcases (ENNReal.toReal_eq_zero_iff _).mp h0 with h1 | htop
    · exact h1
    · exact absurd htop (measure_ne_top _ _)
  have diag_zero_proj_zero : ∀ {B : Set ℝ} (hB : MeasurableSet B),
      (∀ φ, (P.diag φ) B = 0) → P.proj B hB = 0 := by
    intro B hB hd
    ext φ
    have h := P.norm_sq_proj_apply B hB φ
    rw [hd φ, ENNReal.toReal_zero] at h
    have : ‖P.proj B hB φ‖ = 0 := by nlinarith [norm_nonneg (P.proj B hB φ), h]
    rw [norm_eq_zero] at this
    simpa using this
  have hlam_diag : ∀ φ, (P.diag φ) {lam} = 0 :=
    proj_zero_diag_zero (measurableSet_singleton lam) hsing
  -- cover `Dₙ \ {λ} ⊆ ⋃ⱼ C(n+j)`
  have hcover : ∀ N : ℕ, D N \ {lam} ⊆ ⋃ j, C (N + j) := by
    intro N x hx
    obtain ⟨hxD, hxne⟩ := hx
    have hxne' : x ≠ lam := by simpa using hxne
    have hex : ∃ m, x ∉ D m := by
      have hp : (0 : ℝ) < |x - lam| := by rw [abs_pos]; exact sub_ne_zero.mpr hxne'
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hp
      exact ⟨m, fun hmem => absurd ((hDmem m x).mp hmem) (not_lt.mpr hm.le)⟩
    have hm₀spec : x ∉ D (Nat.find hex) := Nat.find_spec hex
    have hposm : N < Nat.find hex := by
      by_contra hle
      push Not at hle
      exact hm₀spec (hDanti hle hxD)
    have hxprev : x ∈ D (Nat.find hex - 1) := by
      by_contra hno
      exact absurd (Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega))
        (by simpa using hno)
    refine Set.mem_iUnion.mpr ⟨Nat.find hex - 1 - N, ?_⟩
    have hidx : N + (Nat.find hex - 1 - N) = Nat.find hex - 1 := by omega
    rw [hidx]
    refine ⟨hxprev, ?_⟩
    have hsucc : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [hsucc]; exact hm₀spec
  -- pairwise disjointness of annuli
  have hCdisj : ∀ a b : ℕ, a ≠ b → Disjoint (C a) (C b) := by
    have key : ∀ a b : ℕ, a < b → Disjoint (C a) (C b) := by
      intro a b hab
      rw [Set.disjoint_left]
      rintro x ⟨_, hxa⟩ ⟨hxb, _⟩
      exact hxa (hDanti (by omega : a + 1 ≤ b) hxb)
    intro a b hab
    rcases lt_or_gt_of_ne hab with h | h
    · exact key a b h
    · exact (key b a h).symm
  -- STEP 1: infinitely many annuli carry nonzero spectral mass
  have hstep : ∀ N : ℕ, ∃ k, N ≤ k ∧ P.proj (C k) (hCm k) ≠ 0 := by
    intro N
    by_contra hcon
    push Not at hcon
    have hDNzero : P.proj (D N) (hDm N) = 0 := by
      refine diag_zero_proj_zero (hDm N) (fun φ => ?_)
      haveI := P.diag_finite φ
      have hsub : ({lam} : Set ℝ) ⊆ D N := by
        intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy; exact hlam_mem N
      have hpart : (P.diag φ) (D N) = (P.diag φ) {lam} + (P.diag φ) (D N \ {lam}) := by
        rw [← measure_inter_add_diff (D N) (measurableSet_singleton lam),
          Set.inter_eq_right.mpr hsub]
      have htail : (P.diag φ) (D N \ {lam}) = 0 := by
        have hle : (P.diag φ) (D N \ {lam}) ≤ ∑' j, (P.diag φ) (C (N + j)) :=
          le_trans (measure_mono (hcover N)) (measure_iUnion_le (fun j => C (N + j)))
        have hterms : ∀ j, (P.diag φ) (C (N + j)) = 0 := fun j =>
          proj_zero_diag_zero (hCm _) (hcon _ (by omega)) φ
        rw [tsum_congr hterms, tsum_zero] at hle
        exact le_zero_iff.mp hle
      rw [hpart, hlam_diag φ, htail, add_zero]
    have hne := (mem_spectrum_iff_forall_spectralPVM_proj_Ioo_ne_zero hA).mp hspec
      (1 / (N + 1)) (hpos N)
    exact hne ((P.proj_congr rfl measurableSet_Ioo (hDm N)).trans hDNzero)
  -- STEP 2: build the orthonormal approximate eigensequence
  set p : ℕ → Prop := fun k => P.proj (C k) (hCm k) ≠ 0 with _hp
  have hp_inf : {k | p k}.Infinite := by
    intro hfin
    obtain ⟨B, hB⟩ := hfin.bddAbove
    obtain ⟨k, hk, hpk⟩ := hstep (B + 1)
    exact absurd (hB hpk) (by omega)
  set kn : ℕ → ℕ := Nat.nth p with _hkn
  have hkn_mem : ∀ n, P.proj (C (kn n)) (hCm (kn n)) ≠ 0 :=
    fun n => Nat.nth_mem_of_infinite hp_inf n
  have hkn_mono : StrictMono kn := Nat.nth_strictMono hp_inf
  have hkn_tendsto : Tendsto kn atTop atTop := hkn_mono.tendsto_atTop
  have hexφ : ∀ n, ∃ x, P.proj (C (kn n)) (hCm (kn n)) x ≠ 0 := fun n => by
    rcases DFunLike.ne_iff.mp (hkn_mem n) with ⟨x, hx⟩; exact ⟨x, by simpa using hx⟩
  choose φ hφ using hexφ
  set v : ℕ → H := fun n => P.proj (C (kn n)) (hCm (kn n)) (φ n) with hv
  have hvne : ∀ n, v n ≠ 0 := fun n => by rw [hv]; exact hφ n
  have hvpos : ∀ n, 0 < ‖v n‖ := fun n => norm_pos_iff.mpr (hvne n)
  set w : ℕ → H := fun n => ((‖v n‖⁻¹ : ℝ) : ℂ) • v n with hw
  have hwnorm : ∀ n, ‖w n‖ = 1 := by
    intro n
    rw [hw, norm_smul]
    have : ‖((‖v n‖⁻¹ : ℝ) : ℂ)‖ = ‖v n‖⁻¹ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos (hvpos n)]
    rw [this, inv_mul_cancel₀ (hvpos n).ne']
  have hwfix : ∀ n, P.proj (C (kn n)) (hCm (kn n)) (w n) = w n := by
    intro n
    rw [hw, map_smul, hv,
      P.proj_apply_of_subset (hCm (kn n)) (hCm (kn n)) (subset_refl _) (φ n)]
  -- orthonormality
  have hortho : Orthonormal ℂ w := by
    rw [orthonormal_iff_ite]
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, inner_self_eq_norm_sq_to_K, hwnorm]; norm_num
    · rw [if_neg hij]
      have hkij : kn i ≠ kn j := fun h => hij (hkn_mono.injective h)
      calc inner ℂ (w i) (w j)
          = inner ℂ (P.proj (C (kn i)) (hCm (kn i)) (w i))
              (P.proj (C (kn j)) (hCm (kn j)) (w j)) := by rw [hwfix i, hwfix j]
        _ = 0 := P.inner_proj_eq_zero_of_disjoint _ _ (hCdisj _ _ hkij) (w i) (w j)
  -- domain membership
  have hbound : ∀ x ∈ Set.Icc (lam - 1) (lam + 1), |x| ≤ |lam| + 1 := by
    intro x hx
    rw [Set.mem_Icc] at hx
    rcases abs_cases lam with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [abs_le] <;> constructor <;> linarith [hx.1, hx.2]
  have hD0 : D 0 = Set.Ioo (lam - 1) (lam + 1) := by rw [hD]; norm_num
  have hCsubIcc1 : ∀ n, C (kn n) ⊆ Set.Icc (lam - 1) (lam + 1) := by
    intro n
    refine (hCsubD (kn n)).trans ((hDanti (Nat.zero_le _)).trans ?_)
    rw [hD0]; exact Set.Ioo_subset_Icc_self
  have hIcc1fix : ∀ n, P.proj (Set.Icc (lam - 1) (lam + 1)) measurableSet_Icc (w n) = w n := by
    intro n
    have hh := P.proj_apply_of_subset measurableSet_Icc (hCm (kn n)) (hCsubIcc1 n) (w n)
    rw [hwfix n] at hh; exact hh
  have hmemU : ∀ n, w n ∈ (generator U).domain := by
    intro n
    have hd := spectralProjection_mem_generatorDomain U measurableSet_Icc hbound (w n)
    rwa [show spectralProjection U (Set.Icc (lam - 1) (lam + 1)) measurableSet_Icc (w n) = w n from
      hIcc1fix n] at hd
  have hmemA : ∀ n, w n ∈ A.domain := fun n => by rw [← hgenU]; exact hmemU n
  -- the approximate-eigenvalue bound
  have hbnd : ∀ n, ‖A ⟨w n, hmemA n⟩ - (lam : ℂ) • w n‖ ≤ 1 / ((kn n : ℝ) + 1) := by
    intro n
    set a := lam - 1 / ((kn n : ℝ) + 1) with ha
    set b := lam + 1 / ((kn n : ℝ) + 1) with hb
    have has : a ≤ lam := by rw [ha]; linarith [hpos (kn n)]
    have hsb : lam ≤ b := by rw [hb]; linarith [hpos (kn n)]
    have hCsubIccn : C (kn n) ⊆ Set.Icc a b := by
      refine (hCsubD (kn n)).trans ?_
      rw [hD, ha, hb]; exact Set.Ioo_subset_Icc_self
    have hfixn : spectralProjection U (Set.Icc a b) measurableSet_Icc (w n) = w n := by
      have hh := P.proj_apply_of_subset measurableSet_Icc (hCm (kn n)) hCsubIccn (w n)
      rw [hwfix n] at hh; exact hh
    have hmemU' : spectralProjection U (Set.Icc a b) measurableSet_Icc (w n)
        ∈ (generator U).domain := by rw [hfixn]; exact hmemU n
    have hloc := generator_sub_smul_norm_le_Icc U a b lam has hsb (w n) hmemU'
    have hsubeq : (⟨spectralProjection U (Set.Icc a b) measurableSet_Icc (w n), hmemU'⟩ :
        (generator U).domain) = ⟨w n, hmemU n⟩ := Subtype.ext hfixn
    rw [hsubeq, hfixn, hwnorm, mul_one] at hloc
    have hmax : max (lam - a) (b - lam) = 1 / ((kn n : ℝ) + 1) := by
      have h1 : lam - a = 1 / ((kn n : ℝ) + 1) := by rw [ha]; ring
      have h2 : b - lam = 1 / ((kn n : ℝ) + 1) := by rw [hb]; ring
      rw [h1, h2, max_self]
    rw [hmax] at hloc
    have hval : generator U ⟨w n, hmemU n⟩ = A ⟨w n, hmemA n⟩ := (le_of_eq hgenU).2 rfl
    have hsmul : (lam : ℝ) • w n = (lam : ℂ) • w n := (Complex.coe_smul lam (w n)).symm
    calc ‖A ⟨w n, hmemA n⟩ - (lam : ℂ) • w n‖
        = ‖generator U ⟨w n, hmemU n⟩ - lam • w n‖ := by rw [← hval, ← hsmul]
      _ ≤ 1 / ((kn n : ℝ) + 1) := hloc
  -- finish with `mem_essSpectrum_of_orthonormal`
  refine mem_essSpectrum_of_orthonormal hA lam (fun n => ⟨w n, hmemA n⟩) hortho ?_
  have htend0 : Tendsto (fun n => 1 / ((kn n : ℝ) + 1)) atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat).comp hkn_tendsto
  exact squeeze_zero (fun n => norm_nonneg _) hbnd htend0

/-- **Discreteness theorem (Weyl, hard half).**  A spectral point of a self-adjoint operator that is
not in the essential spectrum is an eigenvalue. -/
theorem mem_pointSpectrum_of_mem_spectrum_notMem_essSpectrum {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {lam : ℝ} (hspec : lam ∈ spectrum A) (hne : lam ∉ essSpectrum hA) :
    ∃ ψ : A.domain, (ψ : H) ≠ 0 ∧ A ψ = (lam : ℂ) • (ψ : H) := by
  classical
  -- contrapositive of the core: `E({λ}) ≠ 0`
  have hsing : (PVM.spectralPVM hA).proj {lam} (measurableSet_singleton lam) ≠ 0 := fun h =>
    hne (mem_essSpectrum_of_proj_singleton_eq_zero hA hspec h)
  obtain ⟨φ, hφ⟩ := DFunLike.ne_iff.mp hsing
  set ψ := (PVM.spectralPVM hA).proj {lam} (measurableSet_singleton lam) φ with hψ
  obtain ⟨hmem, hval⟩ := spectralPVM_proj_singleton_apply_isEigen hA lam φ
  refine ⟨⟨ψ, hmem⟩, by simpa using hφ, ?_⟩
  simpa [hψ] using hval

/-- **The spectral projection vanishes off the spectrum (brick G3).**  If every point of a
measurable set `B` lies in the resolvent set, then `E(B) = 0`.  Each resolvent point has an open
interval of zero spectral mass (`spectralPVM_proj_Ioo_eq_zero_of_mem_resolventSet`); the diagonal
measures are then locally null on `B`, hence null on `B` (`measure_null_of_locally_null`, using
second-countability of `ℝ`). -/
theorem spectralPVM_proj_eq_zero_of_subset_resolventSet {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {B : Set ℝ} (hB : MeasurableSet B)
    (hsub : ∀ lam ∈ B, (lam : ℂ) ∈ resolventSet A) :
    (PVM.spectralPVM hA).proj B hB = 0 := by
  set P := PVM.spectralPVM hA with hP
  have hdiag : ∀ φ, (P.diag φ) B = 0 := by
    intro φ
    haveI := P.diag_finite φ
    refine measure_null_of_locally_null B ?_
    intro lam hlam
    obtain ⟨ε, hε, hz⟩ := spectralPVM_proj_Ioo_eq_zero_of_mem_resolventSet hA (hsub lam hlam)
    rw [← hP] at hz
    refine ⟨Set.Ioo (lam - ε) (lam + ε),
      mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)), ?_⟩
    have h := P.norm_sq_proj_apply (Set.Ioo (lam - ε) (lam + ε)) measurableSet_Ioo φ
    rw [hz, ContinuousLinearMap.zero_apply, norm_zero] at h
    have h0 : ((P.diag φ) (Set.Ioo (lam - ε) (lam + ε))).toReal = 0 := by rw [← h]; ring
    rcases (ENNReal.toReal_eq_zero_iff _).mp h0 with h1 | htop
    · exact h1
    · exact absurd htop (measure_ne_top _ _)
  ext φ
  have h := P.norm_sq_proj_apply B hB φ
  rw [hdiag φ, ENNReal.toReal_zero] at h
  have : ‖P.proj B hB φ‖ = 0 := by nlinarith [norm_nonneg (P.proj B hB φ), h]
  rw [norm_eq_zero] at this
  simpa using this

end Spectra.QuantumMechanics.SpectralTheory
