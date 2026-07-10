/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SpectralTheory.Essential.Weyl
import Spectra.SpectralTheory.Essential.Defs
import Spectra.SpectralTheory.ResolventForm

/-!
# Real scaling of self-adjoint operators: self-adjointness, essential spectrum, resolvent

For an unbounded self-adjoint operator `A : H →ₗ.[ℂ] H` and a **real** nonzero scalar `c`, this
file develops the scaling bridge `c • A`:

* **L1** `isSelfAdjoint_smul_real` — `(c : ℂ) • A` is self-adjoint (formal self-adjointness for
  real `c` + surjectivity of `(c•A) ± i` via von Neumann's criterion).
* **L2** `essSpectrum_smul_real` — `essSpectrum (c • A) = (· * c) '' essSpectrum A` (Weyl
  sequences transfer: `(c•A − cλ)ψ = c•(A − λ)ψ`), with the positive-cone corollary
  `essSpectrum_smul_pos_Ici` : `essSpectrum A = [0,∞)` and `c > 0` ⟹ `essSpectrum (c•A) = [0,∞)`.
* **L3** `selfAdjointResolvent_smul_real` — `(c•A − z)⁻¹ = c⁻¹ • (A − z/c)⁻¹`.

These are convention-independent operator lemmas; the immediate application is rescaling the free
Laplacian `−Δ` to the textbook kinetic operator `−½Δ = (½ : ℂ) • laplacianPMap`, transferring the
essential-spectrum and resolvent machinery without re-deriving it.
-/

open Filter Topology Complex
open scoped InnerProductSpace ComplexConjugate
open Spectra.Resolvent Spectra.QuantumMechanics.SpectralTheory Spectra.YosidaHille

namespace Spectra.Essential

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Auxiliary: scalar multiplication of a `LinearPMap` -/

omit [CompleteSpace H] in
/-- The application of a scaled operator. -/
lemma smul_pmap_apply (c : ℂ) (A : H →ₗ.[ℂ] H) (x : (c • A).domain) :
    (c • A) x = c • A x := LinearPMap.smul_apply c A x

/-! ## L1: self-adjointness under real scaling -/

omit [CompleteSpace H] in
/-- For a real scalar `c`, `c • A` is formally self-adjoint when `A` is. -/
lemma isFormalAdjoint_smul_real {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (c : ℝ) : (((c : ℂ)) • A).IsFormalAdjoint (((c : ℂ)) • A) := by
  intro x y
  rw [LinearPMap.smul_apply, LinearPMap.smul_apply, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, hsym x y]

/-- Surjectivity of `c•A - w` reduces to surjectivity of `A - w/c` (real `c ≠ 0`). -/
lemma smul_surjective_sub_smul {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (c : ℝ) (hc : c ≠ 0) (w : ℂ) (hw : w.im ≠ 0) :
    ∀ φ : H, ∃ ψ : ((c : ℂ) • A).domain, ((c : ℂ) • A) ψ - w • (ψ : H) = φ := by
  intro φ
  have hcℂ : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hwc : (w / (c : ℂ)).im ≠ 0 := by
    rw [Complex.div_ofReal_im]
    exact div_ne_zero hw hc
  obtain ⟨ψ, hψ⟩ := selfAdjoint_surjective_sub_smul hA (w / (c : ℂ)) hwc ((c : ℂ)⁻¹ • φ)
  refine ⟨ψ, ?_⟩
  rw [LinearPMap.smul_apply]
  have hkey : (c : ℂ) • (A ψ - (w / (c : ℂ)) • (ψ : H)) = (c : ℂ) • ((c : ℂ)⁻¹ • φ) :=
    congrArg (fun v => (c : ℂ) • v) hψ
  rw [smul_sub, smul_smul, smul_smul] at hkey
  rw [mul_div_cancel₀ _ hcℂ, mul_inv_cancel₀ hcℂ, one_smul] at hkey
  exact hkey

/-- **L1.**  If `A` is self-adjoint and `c : ℝ` is nonzero, then `(c : ℂ) • A` is self-adjoint. -/
theorem isSelfAdjoint_smul_real {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (c : ℝ) (hc : c ≠ 0) : IsSelfAdjoint ((c : ℂ) • A) := by
  have hsymA : A.IsFormalAdjoint A := isFormalAdjoint_of_isSelfAdjoint hA
  have hsym : ((c : ℂ) • A).IsFormalAdjoint ((c : ℂ) • A) := isFormalAdjoint_smul_real hsymA c
  have hdense : Dense (((c : ℂ) • A).domain : Set H) := by
    rw [LinearPMap.smul_domain]; exact hA.dense_domain
  have hplus : ∀ φ : H, ∃ ψ : ((c : ℂ) • A).domain, ((c : ℂ) • A) ψ + I • (ψ : H) = φ := by
    intro φ
    obtain ⟨ψ, hψ⟩ := smul_surjective_sub_smul hA c hc (-I) (by simp) φ
    exact ⟨ψ, by rw [← hψ, neg_smul, sub_neg_eq_add]⟩
  have hminus : ∀ φ : H, ∃ ψ : ((c : ℂ) • A).domain, ((c : ℂ) • A) ψ - I • (ψ : H) = φ :=
    smul_surjective_sub_smul hA c hc I (by simp)
  exact Spectra.OneParameterUnitaryGroup.isSelfAdjoint_of_surjective_addSub
    ((c : ℂ) • A) hsym hdense hplus hminus

/-! ## L2: essential spectrum under real scaling -/

/-- A Weyl sequence for `A` at `λ` is a Weyl sequence for `c • A` at `c·λ` (real `c`). -/
lemma mem_essSpectrum_smul_real {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (c : ℝ) (hc : c ≠ 0) {lam : ℝ} (hlam : lam ∈ essSpectrum hA) :
    c * lam ∈ essSpectrum (isSelfAdjoint_smul_real hA c hc) := by
  obtain ⟨ψ, hnorm, hweak, heig⟩ := hlam
  have hmem : ∀ n, (ψ n : H) ∈ ((c : ℂ) • A).domain := by
    intro n; rw [LinearPMap.smul_domain]; exact (ψ n).2
  refine mem_essSpectrum_of_seq (isSelfAdjoint_smul_real hA c hc) (c * lam)
    (fun n => (ψ n : H)) hmem hnorm hweak ?_
  have hrw : ∀ n,
      ‖((c : ℂ) • A) ⟨(ψ n : H), hmem n⟩ - ((c * lam : ℝ) : ℂ) • (ψ n : H)‖
        = |c| * ‖A (ψ n) - (lam : ℂ) • (ψ n : H)‖ := by
    intro n
    rw [LinearPMap.smul_apply]
    have hAeq : A ⟨(ψ n : H), hmem n⟩ = A (ψ n) := by congr
    rw [hAeq]
    have hsm : (c : ℂ) • A (ψ n) - ((c * lam : ℝ) : ℂ) • (ψ n : H)
        = (c : ℂ) • (A (ψ n) - (lam : ℂ) • (ψ n : H)) := by
      rw [smul_sub, smul_smul]; push_cast; ring_nf
    rw [hsm, norm_smul]
    congr 1
    exact RCLike.norm_ofReal c
  rw [show (𝓝 (0 : ℝ)) = 𝓝 (|c| * 0) by rw [mul_zero]]
  simp_rw [hrw]
  exact heig.const_mul |c|

/-- `essSpectrum` depends only on the operator, not on the self-adjointness witness. -/
lemma essSpectrum_congr_op {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (h : A = B) : essSpectrum hA = essSpectrum hB := by
  subst h; rfl

omit [CompleteSpace H] in
/-- Scaling by `c` then by `c⁻¹` is the identity operator (real `c ≠ 0`). -/
lemma smul_inv_smul_pmap {A : H →ₗ.[ℂ] H} (c : ℝ) (hc : c ≠ 0) :
    ((c⁻¹ : ℝ) : ℂ) • (((c : ℂ)) • A) = A := by
  have hcℂ : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  rw [smul_smul]
  rw [show (((c⁻¹ : ℝ) : ℂ)) * (c : ℂ) = 1 by push_cast; field_simp]
  exact one_smul _ A

/-- **L2.**  The essential spectrum scales by a real nonzero `c`:
`essSpectrum (c • A) = (· * c) '' essSpectrum A`. -/
theorem essSpectrum_smul_real {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (c : ℝ) (hc : c ≠ 0) :
    essSpectrum (isSelfAdjoint_smul_real hA c hc) = (fun μ => c * μ) '' essSpectrum hA := by
  apply Set.eq_of_subset_of_subset
  · intro μ hμ
    have _hcℂ : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    have hcA_SA : IsSelfAdjoint ((c : ℂ) • A) := isSelfAdjoint_smul_real hA c hc
    have hstep := mem_essSpectrum_smul_real hcA_SA c⁻¹ (inv_ne_zero hc) hμ
    have hop : ((c⁻¹ : ℝ) : ℂ) • (((c : ℂ)) • A) = A := smul_inv_smul_pmap c hc
    refine ⟨c⁻¹ * μ, ?_, by field_simp⟩
    have hess : essSpectrum (isSelfAdjoint_smul_real hcA_SA c⁻¹ (inv_ne_zero hc))
        = essSpectrum hA :=
      essSpectrum_congr_op _ hA hop
    rw [hess] at hstep
    exact hstep
  · rintro μ ⟨lam, hlam, rfl⟩
    exact mem_essSpectrum_smul_real hA c hc hlam

/-! ## L3: resolvent under real scaling -/

/-- The scaled spectral parameter `c⁻¹ • z` is still off the real axis (real `c ≠ 0`). -/
lemma smul_inv_im_ne_zero {c : ℝ} (hc : c ≠ 0) {z : ℂ} (hz : z.im ≠ 0) :
    (((c⁻¹ : ℝ) : ℂ) * z).im ≠ 0 := by
  rw [Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  exact mul_ne_zero (inv_ne_zero hc) hz

/-- **L3.**  Resolvent scaling: for real `c ≠ 0` and `z` off the real axis,
`(c•A − z)⁻¹ = c⁻¹ • (A − z/c)⁻¹`. -/
theorem selfAdjointResolvent_smul_real {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (c : ℝ) (hc : c ≠ 0) (z : ℂ) (hz : z.im ≠ 0) :
    selfAdjointResolvent (isSelfAdjoint_smul_real hA c hc) z hz
      = ((c⁻¹ : ℝ) : ℂ) • selfAdjointResolvent hA (((c⁻¹ : ℝ) : ℂ) * z)
          (smul_inv_im_ne_zero hc hz) := by
  have hcℂ : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hcA_SA : IsSelfAdjoint ((c : ℂ) • A) := isSelfAdjoint_smul_real hA c hc
  set z' : ℂ := ((c⁻¹ : ℝ) : ℂ) * z with hz'def
  set hz' : z'.im ≠ 0 := smul_inv_im_ne_zero hc hz with _hhz'
  ext φ
  obtain ⟨ψ, hψ⟩ := smul_surjective_sub_smul hA c hc z hz φ
  have hLHS : selfAdjointResolvent hcA_SA z hz φ = (ψ : H) := by
    rw [← hψ]
    exact selfAdjointResolvent_left_inverse hcA_SA z hz ψ
  have hψA : (ψ : H) ∈ A.domain := ψ.2
  have hzc : z = (c : ℂ) * z' := by
    rw [hz'def, ← mul_assoc, show (c : ℂ) * ((c⁻¹ : ℝ) : ℂ) = 1 by push_cast; field_simp,
      one_mul]
  have hψ' : (((c : ℂ)) • A) ψ - z • (ψ : H) = (c : ℂ) • (A ⟨(ψ : H), hψA⟩ - z' • (ψ : H)) := by
    rw [LinearPMap.smul_apply, smul_sub, smul_smul, ← hzc]
    have hAeq : A ψ = A ⟨(ψ : H), hψA⟩ := by congr
    rw [hAeq]
  have hRHS : selfAdjointResolvent hA z' hz' φ = (c : ℂ) • (ψ : H) := by
    rw [← hψ, hψ', map_smul]
    rw [selfAdjointResolvent_left_inverse hA z' hz' ⟨(ψ : H), hψA⟩]
  change selfAdjointResolvent hcA_SA z hz φ
      = ((c⁻¹ : ℝ) : ℂ) • selfAdjointResolvent hA z' hz' φ
  rw [hLHS, hRHS, smul_smul]
  rw [show (((c⁻¹ : ℝ) : ℂ)) * (c : ℂ) = 1 by push_cast; field_simp, one_smul]

/-- Corollary: if `essSpectrum A = [0, ∞)` and `c > 0`, then `essSpectrum (c•A) = [0, ∞)`. -/
theorem essSpectrum_smul_pos_Ici {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (c : ℝ) (hc : 0 < c) (hAspec : essSpectrum hA = Set.Ici (0 : ℝ)) :
    essSpectrum (isSelfAdjoint_smul_real hA c hc.ne') = Set.Ici (0 : ℝ) := by
  rw [essSpectrum_smul_real hA c hc.ne', hAspec]
  ext μ
  simp only [Set.mem_image, Set.mem_Ici]
  constructor
  · rintro ⟨ν, hν, rfl⟩; positivity
  · intro hμ
    exact ⟨c⁻¹ * μ, by positivity, by field_simp⟩

end Spectra.Essential
