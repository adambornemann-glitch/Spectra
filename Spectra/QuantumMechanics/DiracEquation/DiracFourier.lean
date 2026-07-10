/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.DiracEquation.SpinorSpaceL2
import Spectra.QuantumMechanics.DiracEquation.Dispersion
import Spectra.Spaces.Sobolev.FourierDecay
/-!
# Fourier analysis of the free Dirac operator

This file builds the Fourier-side machinery for inverting the free Dirac operator, i.e. for the
surjectivity of `D₀ ± iμ` that underlies its self-adjointness (`FreeHamiltonian.lean`).

The vector Fourier transform `spinorFourierL2` is the componentwise `ℓ²` lift of the scalar
Plancherel transform `fourierL2` to `L²(ℝ³; ℂ⁴)`. Under it the kinetic operator `D₀ = -iα·∇`
becomes multiplication by the Hermitian matrix symbol `D(ξ) = 2π (α·ξ)`, whose square is the
scalar Laplacian symbol `(2π)²‖ξ‖²` times the identity (the dispersion relation
`diracMomentumOp_sq`). Consequently `D(ξ) ± iμ` is inverted by the **bounded** matrix multiplier

  `(D(ξ) ∓ iμ) / ((2π)²‖ξ‖² + μ²)`,

since the denominator never vanishes for `μ ≠ 0`. This is the spinor analogue of the scalar
resolvent symbol `resolventSymbol` from `Hydrogen/Laplacian.lean`.

The second half of the file supplies the Sobolev-regularity input to the same surjectivity
argument, at the level of the *scalar* Fourier transform. `fourier_weakGradient` diagonalises the
first weak derivative (`𝓕(∂ₖf) = derivSymbol k · 𝓕f` a.e.), the first-order analogue of the
Laplacian symbol; `memSobolevH1_of_fourier_decay` reads this backwards, promoting Fourier decay of
`derivSymbol k · 𝓕ψ` to membership in `H¹(ℝ³)` (the resolvent solution lands in `H¹`, not `H²`);
and `scalarResolventSolve` solves the scalar shifted equation `(-Δ + c)χ = g` in `H²` for `c > 0`
via the bounded multiplier `1/(laplacianSymbol ξ + c)`. Both of the latter two are consumed
downstream by `FreeHamiltonian.lean`.

## Main definitions

* `spinorFourierL2` — the Fourier transform on `L²(ℝ³; ℂ⁴)`, an isometric equivalence.
* `diracKineticSymbol` — the matrix symbol `D(ξ) = 2π (α·ξ)`.
* `diracResolventSymbol` — the bounded inverse multiplier of `D(ξ) ± iμ`.

## Main statements

* `spinorFourierL2_apply` — `(𝓕ψ)ₐ = 𝓕(ψₐ)` componentwise.
* `diracKineticSymbol_hermitian` — `D(ξ)` is Hermitian.
* `diracKineticSymbol_sq` — `D(ξ)² = ((2π)²‖ξ‖²) • 1` (dispersion relation).
* `diracResolventSymbol_add_inverse` — `(D(ξ) + iμ)` is inverted by the resolvent symbol (the
  `D(ξ) - iμ` case is recovered by negating `μ`).
* `fourier_weakGradient` — the Fourier transform diagonalises the first weak derivative:
  `𝓕(∂ₖf) = derivSymbol k · 𝓕f` a.e.
* `memSobolevH1_of_fourier_decay` — `H¹`-membership from Fourier decay: if each
  `derivSymbol k · 𝓕ψ ∈ L²`, then `ψ ∈ H¹(ℝ³)`.
* `scalarResolventSolve` — the scalar shift `-Δ + c` (for `c > 0`) is surjective onto `L²(ℝ³)`,
  with the solution in `H²`.

## References

* [Thaller, *The Dirac Equation*][thaller1992], Chapter 1
* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975], §IX.7

## Tags

Dirac equation, Fourier transform, Plancherel, resolvent, Fourier multiplier
-/
open Complex Matrix MeasureTheory InnerProductSpace
open Spectra.Sobolev
open FourierTransform
open scoped SchwartzMap

namespace Spectra.QuantumMechanics.Dirac

/-! ## The vector Fourier transform on `L²(ℝ³; ℂ⁴)` -/

/-- The Fourier transform on the spinor Hilbert space `L²(ℝ³; ℂ⁴)`, as an isometric equivalence:
the componentwise `ℓ²` lift of the scalar Plancherel transform `fourierL2`. -/
noncomputable def spinorFourierL2 : DiracSpinorL2 ≃ₗᵢ[ℂ] DiracSpinorL2 :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin 4 => fourierL2)

/-- The vector Fourier transform acts componentwise: its `a`-th component is the scalar Plancherel
transform `fourierL2` of the `a`-th component of `ψ`. -/
@[simp] lemma spinorFourierL2_apply (ψ : DiracSpinorL2) (a : Fin 4) :
    spinorFourierL2 ψ a = fourierL2 (ψ a) := by
  simp only [spinorFourierL2, LinearIsometryEquiv.piLpCongrRight_apply, PiLp.toLp_apply]

/-- Coefficientwise a.e. value of a finite `L²`-sum of scalar multiples: if each `F i` agrees a.e.
with `g i`, then `∑ i, c i • F i` agrees a.e. with `ξ ↦ ∑ i, c i · g i ξ`. (There is no
`Lp.coeFn_sum` in Mathlib, so this is proved by induction from `coeFn_add`/`coeFn_smul`.) -/
lemma l2_coeFn_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℂ) (F : ι → l2R3)
    (g : ι → R3 → ℂ) (hg : ∀ i ∈ s, (F i : R3 → ℂ) =ᵐ[volume] g i) :
    ((∑ i ∈ s, c i • F i : l2R3) : R3 → ℂ) =ᵐ[volume] fun ξ => ∑ i ∈ s, c i * g i ξ := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure R3))] with ξ h
    rw [h, Pi.zero_apply]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (c a • F a) (∑ i ∈ s, c i • F i),
      Lp.coeFn_smul (c a) (F a), hg a (Finset.mem_insert_self a s),
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)] with ξ e0 e1 e2 e3
    rw [e0]
    simp only [Pi.add_apply, e1, Pi.smul_apply, smul_eq_mul, e2, e3, Finset.sum_insert ha]

/-- Coefficientwise a.e. value of a finite `L²`-sum (no scalars): the plain-sum companion of
`l2_coeFn_sum_smul`, used for the outer sum in the kinetic diagonalisation. -/
lemma l2_coeFn_sum {ι : Type*} (s : Finset ι) (F : ι → l2R3) (g : ι → R3 → ℂ)
    (hg : ∀ i ∈ s, (F i : R3 → ℂ) =ᵐ[volume] g i) :
    ((∑ i ∈ s, F i : l2R3) : R3 → ℂ) =ᵐ[volume] fun ξ => ∑ i ∈ s, g i ξ := by
  simpa using l2_coeFn_sum_smul s (fun _ => (1 : ℂ)) F g hg

/-! ## The matrix Fourier symbol of the kinetic operator -/

/-- The relativistic energy of the massless symbol equals `‖ξ‖²`. -/
lemma energyMomentumSq_eq_normSq (ξ : R3) :
    energyMomentumSq (fun i => ξ i) 0 = ‖ξ‖ ^ 2 := by
  rw [energyMomentumSq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  ring

/-- The matrix Fourier symbol of the kinetic Dirac operator `D₀ = -iα·∇`, namely
`D(ξ) = 2π (α·ξ)`. Built from the momentum-space symbol `diracMomentumOp` at zero mass. -/
noncomputable def diracKineticSymbol (ξ : R3) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) • diracMomentumOp (fun i => ξ i) 0

/-- The kinetic symbol is Hermitian (it is `2π` times the Hermitian `α·ξ`). -/
lemma diracKineticSymbol_hermitian (ξ : R3) :
    (diracKineticSymbol ξ).conjTranspose = diracKineticSymbol ξ := by
  rw [diracKineticSymbol, Matrix.conjTranspose_smul, diracMomentumOp_hermitian, RCLike.star_def,
    Complex.conj_ofReal]

/-- **The dispersion relation in Fourier form**: `D(ξ)² = (2π)²‖ξ‖² · I = (laplacianSymbol ξ) • I`.
This is `diracMomentumOp_sq` transported through the `2π` scaling. -/
lemma diracKineticSymbol_sq (ξ : R3) :
    diracKineticSymbol ξ * diracKineticSymbol ξ = (laplacianSymbol ξ : ℂ) • 1 := by
  simp only [diracKineticSymbol, Matrix.smul_mul, Matrix.mul_smul, diracMomentumOp_sq, smul_smul]
  rw [energyMomentumSq_eq_normSq, laplacianSymbol]
  congr 1
  push_cast
  ring

/-! ## The resolvent symbol -/

/-- Positivity of the resolvent denominator `(2π)²‖ξ‖² + μ²` for `μ ≠ 0`. -/
lemma laplacianSymbol_add_sq_pos (μ : ℝ) (hμ : μ ≠ 0) (ξ : R3) :
    0 < laplacianSymbol ξ + μ ^ 2 := by
  have h2 : 0 < μ ^ 2 := by positivity
  have h1 := laplacianSymbol_nonneg ξ
  linarith

/-- The resolvent symbol `(D(ξ) - iμ) / ((2π)²‖ξ‖² + μ²)`, the bounded matrix multiplier that
inverts `D(ξ) + iμ`. -/
noncomputable def diracResolventSymbol (μ : ℝ) (ξ : R3) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((laplacianSymbol ξ + μ ^ 2 : ℝ) : ℂ)⁻¹ • (diracKineticSymbol ξ - (Complex.I * (μ : ℂ)) • 1)

/-- The kinetic symbol commutes with the central scalar matrix `iμ • 1`. -/
lemma diracKineticSymbol_commute (μ : ℝ) (ξ : R3) :
    Commute (diracKineticSymbol ξ) ((Complex.I * (μ : ℂ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) := by
  unfold Commute SemiconjBy
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

/-- **The resolvent symbol inverts `D(ξ) + iμ`**: `(D(ξ) + iμ) · resolvent = 1` for `μ ≠ 0`.
The numerator product is `(D(ξ) + iμ)(D(ξ) - iμ) = D(ξ)² + μ² = ((2π)²‖ξ‖² + μ²) • 1`, which
cancels the denominator. -/
lemma diracResolventSymbol_add_inverse (μ : ℝ) (hμ : μ ≠ 0) (ξ : R3) :
    (diracKineticSymbol ξ + (Complex.I * (μ : ℂ)) • 1) * diracResolventSymbol μ ξ = 1 := by
  have hne : ((laplacianSymbol ξ + μ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (laplacianSymbol_add_sq_pos μ hμ ξ).ne'
  have hbb : ((Complex.I * (μ : ℂ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ))
      * ((Complex.I * (μ : ℂ)) • 1) = (-(μ : ℂ) ^ 2) • 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    congr 1
    linear_combination (μ : ℂ) ^ 2 * Complex.I_sq
  rw [diracResolventSymbol, Matrix.mul_smul,
    show (diracKineticSymbol ξ + (Complex.I * (μ : ℂ)) • 1)
          * (diracKineticSymbol ξ - (Complex.I * (μ : ℂ)) • 1)
        = diracKineticSymbol ξ * diracKineticSymbol ξ
          - ((Complex.I * (μ : ℂ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) * ((Complex.I * (μ : ℂ)) • 1)
        from by rw [mul_sub, add_mul, add_mul, (diracKineticSymbol_commute μ ξ).eq]; abel,
    diracKineticSymbol_sq, hbb, ← sub_smul, smul_smul]
  rw [show (laplacianSymbol ξ : ℂ) - -(μ : ℂ) ^ 2 = ((laplacianSymbol ξ + μ ^ 2 : ℝ) : ℂ) from by
    push_cast; ring, inv_mul_cancel₀ hne, one_smul]

/-! ## Fourier diagonalisation of the first weak derivative -/

/-- **Fourier diagonalises the weak derivative**: `𝓕(∂ₖf) = derivSymbol k · 𝓕f` a.e., where
`derivSymbol k ξ = 2πi⟪ξ, eₖ⟫`. The first-order analogue of `fourier_weakLaplacian`. -/
lemma fourier_weakGradient (f : l2R3) (hf : MemSobolevH1 f) (k : Fin 3) :
    (fourierL2 (weakGradient f hf k) : R3 → ℂ) =ᵐ[volume]
      fun ξ => derivSymbol k ξ * (fourierL2 f : R3 → ℂ) ξ := by
  have hg₀ : Function.HasTemperateGrowth
      (fun ξ : R3 => ((inner ℝ ξ (EuclideanSpace.single k (1 : ℝ)) : ℝ) : ℂ)) := by fun_prop
  have key : Lp.toTemperedDistribution (𝓕 (weakGradient f hf k))
      = TemperedDistribution.smulLeftCLM ℂ (derivSymbol k) (Lp.toTemperedDistribution (𝓕 f)) := by
    rw [← Lp.fourier_toTemperedDistribution_eq (weakGradient f hf k),
      ← lineDerivOp_toTD_weakGradient f hf k, TemperedDistribution.fourier_lineDerivOp_eq,
      Lp.fourier_toTemperedDistribution_eq, ← ContinuousLinearMap.smul_apply,
      ← TemperedDistribution.smulLeftCLM_smul hg₀]
    congr 2
  have locInt : LocallyIntegrable
      (fun ξ => derivSymbol k ξ * ((𝓕 f : l2R3) : R3 → ℂ) ξ) volume := by
    have hLI : LocallyIntegrable ((𝓕 f : l2R3) : R3 → ℂ) volume :=
      (Lp.memLp (𝓕 f)).locallyIntegrable one_le_two
    rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    exact IntegrableOn.continuousOn_mul
      (Continuous.continuousOn (by unfold derivSymbol; fun_prop))
      (hLI.integrableOn_isCompact hK) hK
  simp only [fourierL2_eq]
  exact aeEq_of_toTD_smulLeft (derivSymbol_hasTemperateGrowth k) locInt key

/-- **`H¹` from Fourier decay**: if each `derivSymbol k · 𝓕ψ ∈ L²`, then `ψ ∈ H¹(ℝ³)`. The
first-order regularity criterion (the resolvent solution lands in `H¹`, not `H²`), built directly
from `weakDeriv_construct`. -/
theorem memSobolevH1_of_fourier_decay (ψ : l2R3)
    (h : ∀ k : Fin 3, MemLp (fun ξ => derivSymbol k ξ * (fourierL2 ψ : R3 → ℂ) ξ) 2 volume) :
    MemSobolevH1 ψ :=
  fun k => ⟨(weakDeriv_construct ψ k (h k)).choose,
    (weakDeriv_construct ψ k (h k)).choose_spec.1⟩

/-! ## The scalar real-shift resolvent -/

/-- **Scalar real-shift resolvent**: for `c > 0`, `-Δ + c` is surjective onto `L²(ℝ³)` — there is
`χ ∈ H²` with `(laplacianSymbol ξ + c)·𝓕χ = 𝓕g` a.e. Built from the bounded Fourier multiplier
`1/(laplacianSymbol ξ + c)`. The bounds (`1/c`, `1/c + 1/(2π)²`) are elementary because the shift
`c > 0` keeps the denominator away from `0`. -/
lemma scalarResolventSolve (c : ℝ) (hc : 0 < c) (g : l2R3) :
    ∃ χ : l2R3, MemSobolevH2 χ ∧
      (fun ξ => ((laplacianSymbol ξ + c : ℝ) : ℂ) * (fourierL2 χ : R3 → ℂ) ξ)
        =ᵐ[volume] (fourierL2 g : R3 → ℂ) := by
  have hpos : ∀ ξ : R3, (0 : ℝ) < laplacianSymbol ξ + c :=
    fun ξ => by have := laplacianSymbol_nonneg ξ; linarith
  set m : R3 → ℂ := fun ξ => (((laplacianSymbol ξ + c)⁻¹ : ℝ) : ℂ) with hm
  have hbase : Continuous (fun ξ : R3 => laplacianSymbol ξ + c) := by
    simp only [laplacianSymbol]
    exact (continuous_const.mul ((continuous_norm.pow 2))).add continuous_const
  have hmcont : Continuous m :=
    Complex.continuous_ofReal.comp (hbase.inv₀ fun ξ => (hpos ξ).ne')
  have hmeas : AEStronglyMeasurable m volume := hmcont.aestronglyMeasurable
  have hbound : ∀ ξ : R3, ‖m ξ‖ ≤ 1 / c := by
    intro ξ
    have hnorm : ‖m ξ‖ = (laplacianSymbol ξ + c)⁻¹ := by
      simp only [hm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hpos ξ))]
    rw [hnorm, inv_eq_one_div]
    exact one_div_le_one_div_of_le hc (by have := laplacianSymbol_nonneg ξ; linarith)
  have hwbound : ∀ ξ : R3, ‖((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ) * m ξ‖ ≤ 1 / c + 1 / (2 * Real.pi) ^ 2 := by
    intro ξ
    have hnorm : ‖((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ) * m ξ‖
        = (1 + ‖ξ‖ ^ 2) * (laplacianSymbol ξ + c)⁻¹ := by
      simp only [hm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 + ‖ξ‖ ^ 2), abs_of_pos (inv_pos.mpr (hpos ξ))]
    rw [hnorm, ← div_eq_mul_inv, laplacianSymbol, ← sub_nonneg]
    have hN : 1 / c + 1 / (2 * Real.pi) ^ 2
          - (1 + ‖ξ‖ ^ 2) / ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 + c)
        = ((2 * Real.pi) ^ 4 * ‖ξ‖ ^ 2 + c ^ 2)
          / (c * (2 * Real.pi) ^ 2 * ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 + c)) := by
      have hc' := hc.ne'
      have _hp2' : ((2 * Real.pi) ^ 2 : ℝ) ≠ 0 := by positivity
      have _hd' : ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 + c : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    rw [hN]; positivity
  have hmeas1 : AEStronglyMeasurable (fun ξ : R3 => ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ)) volume := by fun_prop
  have hbound' : ∀ᵐ ξ ∂(volume : Measure R3), ‖m ξ‖ ≤ 1 / c := Filter.Eventually.of_forall hbound
  have hwbound' : ∀ᵐ ξ ∂(volume : Measure R3),
      ‖((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ) * m ξ‖ ≤ 1 / c + 1 / (2 * Real.pi) ^ 2 :=
    Filter.Eventually.of_forall hwbound
  have hmem := memLp_two_boundedMul hmeas hbound' (fourierL2 g)
  set χ₀ : l2R3 := fourierL2.symm (hmem.toLp (fun ξ => m ξ * (fourierL2 g : R3 → ℂ) ξ)) with hχ₀
  have hχf : (fourierL2 χ₀ : R3 → ℂ) =ᵐ[volume]
      fun ξ => m ξ * (fourierL2 g : R3 → ℂ) ξ := by
    rw [hχ₀, LinearIsometryEquiv.apply_symm_apply]; exact hmem.coeFn_toLp
  refine ⟨χ₀, ?_, ?_⟩
  · apply memSobolevH2_of_fourier_decay
    have hmemw := memLp_two_boundedMul (hmeas1.mul hmeas) hwbound' (fourierL2 g)
    refine hmemw.ae_eq ?_
    filter_upwards [hχf] with ξ hξ
    simp only [Pi.mul_apply]
    rw [hξ]; ring
  · filter_upwards [hχf] with ξ hξ
    simp only [hξ, hm]
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (hpos ξ).ne',
      Complex.ofReal_one, one_mul]

end Spectra.QuantumMechanics.Dirac
