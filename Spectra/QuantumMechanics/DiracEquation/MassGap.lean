/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.DiracEquation.NegativeEnergy
/-!
# The mass gap of the free Dirac operator (Step (b)/4, Half A)

The dispersion relation `Ĥ(ξ)² = E(ξ)²·I` forces `‖Ĥ(ξ)v‖ = E(ξ)‖v‖ ≥ |mc²|·‖v‖` pointwise, hence
the operator lower bound `‖H_D ψ‖ ≥ |mc²|·‖ψ‖`.  By the spectral-gap engine
(`spectralProjection_Ioo_eq_zero_of_norm_ge`) this means the free Dirac operator has **no spectral
mass in the open gap `(−|mc²|, |mc²|)`** — the relativistic mass gap of width `2mc²`.

This is the "`σ ⊆ (−∞,−mc²]∪[mc²,∞)`" half of the spectrum characterisation.

## Main results

* `diracFullSymbol_mulVec_dotProduct_self`, `diracFullSymbol_mulVec_normSq` : the pointwise
  dispersion identity `‖Ĥ(ξ)v‖² = E(ξ)²·‖v‖²`, from `Ĥᴴ = Ĥ` and `Ĥ² = E²·I`.
* `diracSpinorL2_normSq_integral` : Plancherel for `DiracSpinorL2`, summed over spinor components.
* `diracHamiltonian_normSq_ge`, `diracHamiltonian_norm_ge` : the operator lower bound
  `‖H_D ψ‖ ≥ |mc²|·‖ψ‖`, from integrating the pointwise identity against the dispersion bound
  `E(ξ)² ≥ mc²`.
* `diracHamiltonian_mass_gap` : the headline result — the free Dirac unitary group's spectral
  projection onto `(−|mc²|, |mc²|)` vanishes.

## Implementation notes

The argument is Plancherel plus a generic spectral-gap engine, not a bespoke spectral calculation:
`diracFullSymbol_mulVec_normSq` establishes the pointwise identity on Fourier space, which is
integrated (via `diracSpinorL2_normSq_integral`) into the operator bound
`diracHamiltonian_norm_ge`. That bound is then handed to the abstract
`spectralProjection_Ioo_eq_zero_of_norm_ge` engine (shared with other operators in this library),
which converts a norm lower bound on the generator's domain into vanishing of the spectral
projection on the corresponding gap.

## References

* [Thaller, *The Dirac Equation*][thaller1992], Section 1.4
* [Bjorken, Drell, *Relativistic Quantum Mechanics*][bjorkendrell1964], Chapter 3

## Tags

mass gap, Dirac operator, spectral gap, dispersion relation, Plancherel, free Dirac equation,
relativistic spectrum
-/

open Complex MeasureTheory Matrix
open Spectra.Sobolev
open Spectra.OneParameterUnitaryGroup
open Spectra.QuantumMechanics.SpectralTheory

noncomputable section
namespace Spectra.QuantumMechanics.Dirac

/-! ## The pointwise dispersion norm identity `‖Ĥ(ξ)v‖² = E(ξ)²‖v‖²` -/

/-- **Finite-dimensional adjoint transfer**: `⟪u, Aᴴ w⟫ = ⟪Au, w⟫` for the dot product. -/
lemma star_mulVec_dotProduct (A : Matrix (Fin 4) (Fin 4) ℂ) (u w : Fin 4 → ℂ) :
    star u ⬝ᵥ A.conjTranspose *ᵥ w = star (A *ᵥ u) ⬝ᵥ w := by
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec]

/-- **`(v†v).re = Σ ‖vₐ‖²`.** -/
lemma star_dotProduct_self_re (w : Fin 4 → ℂ) : (star w ⬝ᵥ w).re = ∑ a, ‖w a‖ ^ 2 := by
  rw [dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Pi.star_apply, ← starRingEnd_apply, mul_comm, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

/-- **The ℂ-valued dispersion identity** `(Ĥv)†(Ĥv) = E² · (v†v)`, from `Ĥᴴ = Ĥ` and `Ĥ² = E²·I`. -/
lemma diracFullSymbol_mulVec_dotProduct_self (mc2 : ℝ) (ξ : R3) (v : Fin 4 → ℂ) :
    star (diracFullSymbol mc2 ξ *ᵥ v) ⬝ᵥ (diracFullSymbol mc2 ξ *ᵥ v)
      = ((diracEnergy mc2 ξ ^ 2 : ℝ) : ℂ) * (star v ⬝ᵥ v) := by
  have hH : (diracFullSymbol mc2 ξ).conjTranspose = diracFullSymbol mc2 ξ :=
    diracMomentumOp_hermitian (momScale ξ) mc2
  have hsq : diracFullSymbol mc2 ξ * diracFullSymbol mc2 ξ
      = ((diracEnergy mc2 ξ ^ 2 : ℝ) : ℂ) • 1 := by
    have he : diracEnergy mc2 ξ ^ 2 = energyMomentumSq (momScale ξ) mc2 := energyMomentum_sq _ _
    rw [diracFullSymbol, diracMomentumOp_sq, he]
  rw [← star_mulVec_dotProduct, hH, Matrix.mulVec_mulVec, hsq, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]

/-- **Pointwise dispersion norm identity**: `Σₐ ‖(Ĥ(ξ)v)ₐ‖² = E(ξ)² · Σₐ ‖vₐ‖²`. -/
lemma diracFullSymbol_mulVec_normSq (mc2 : ℝ) (ξ : R3) (v : Fin 4 → ℂ) :
    ∑ a, ‖(diracFullSymbol mc2 ξ *ᵥ v) a‖ ^ 2
      = diracEnergy mc2 ξ ^ 2 * ∑ a, ‖v a‖ ^ 2 := by
  have h := (star_dotProduct_self_re (diracFullSymbol mc2 ξ *ᵥ v)).symm
  rw [diracFullSymbol_mulVec_dotProduct_self, Complex.re_ofReal_mul,
    star_dotProduct_self_re] at h
  exact h

/-! ## The operator lower bound `‖H_D ψ‖ ≥ |mc²|·‖ψ‖` -/

/-- **Plancherel for `DiracSpinorL2`**: `‖x‖² = ∫ Σₐ ‖𝓕(x)ₐ(ξ)‖²`, summed over spinor components. -/
lemma diracSpinorL2_normSq_integral (x : DiracSpinorL2) :
    ‖x‖ ^ 2 = ∫ ξ, ∑ a, ‖(fourierL2 (x a) : R3 → ℂ) ξ‖ ^ 2 ∂volume := by
  have hint : ∀ a : Fin 4,
      Integrable (fun ξ => ‖(fourierL2 (x a) : R3 → ℂ) ξ‖ ^ 2) volume := fun a => by
    have h := (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (fourierL2 (x a))
      (fourierL2 (x a))).re
    exact h.congr (Filter.Eventually.of_forall fun ξ => inner_self_eq_norm_sq (𝕜 := ℂ) _)
  rw [PiLp.norm_sq_eq_of_L2, integral_finsetSum _ (fun a _ => hint a)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← L2_normSq_integral (fourierL2 (x a)), LinearIsometryEquiv.norm_map]

/-- **Integrability of the Plancherel integrand**: `ξ ↦ Σₐ ‖𝓕(x)ₐ(ξ)‖²` is integrable. -/
lemma integrable_spinor_normSq (x : DiracSpinorL2) :
    Integrable (fun ξ => ∑ a, ‖(fourierL2 (x a) : R3 → ℂ) ξ‖ ^ 2) volume :=
  integrable_finsetSum _ fun a _ => by
    have h := (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (fourierL2 (x a))
      (fourierL2 (x a))).re
    exact h.congr (Filter.Eventually.of_forall fun ξ => inner_self_eq_norm_sq (𝕜 := ℂ) _)

/-- **The free Dirac operator is bounded below in norm-square by `mc²·‖ψ‖²`** (the dispersion
relation `E(ξ)² ≥ mc²` integrated). -/
lemma diracHamiltonian_normSq_ge (mc2 : ℝ) (ψ : DiracSpinorL2) (hψ : MemSobolevDiracH1 ψ) :
    mc2 ^ 2 * ‖ψ‖ ^ 2 ≤ ‖diracHamiltonian mc2 ⟨ψ, hψ⟩‖ ^ 2 := by
  have hGS : (fun ξ => ∑ a, ‖(fourierL2 ((diracHamiltonian mc2 ⟨ψ, hψ⟩) a) : R3 → ℂ) ξ‖ ^ 2)
      =ᵐ[volume] fun ξ => diracEnergy mc2 ξ ^ 2
        * ∑ a, ‖(fourierL2 (ψ a) : R3 → ℂ) ξ‖ ^ 2 := by
    have hall : ∀ᵐ ξ ∂volume, ∀ a,
        (fourierL2 ((diracHamiltonian mc2 ⟨ψ, hψ⟩) a) : R3 → ℂ) ξ
          = ∑ b, diracFullSymbol mc2 ξ a b * (fourierL2 (ψ b) : R3 → ℂ) ξ :=
      ae_all_iff.2 fun a => fourier_diracHamiltonian_symbol mc2 ψ hψ a
    filter_upwards [hall] with ξ hξ
    have hpt : ∀ a, (fourierL2 ((diracHamiltonian mc2 ⟨ψ, hψ⟩) a) : R3 → ℂ) ξ
        = (diracFullSymbol mc2 ξ *ᵥ fun b => (fourierL2 (ψ b) : R3 → ℂ) ξ) a := fun a => by
      rw [hξ a]; rfl
    simp_rw [hpt]
    exact diracFullSymbol_mulVec_normSq mc2 ξ _
  rw [diracSpinorL2_normSq_integral (diracHamiltonian mc2 ⟨ψ, hψ⟩),
    diracSpinorL2_normSq_integral ψ, ← integral_const_mul]
  refine integral_mono_ae ((integrable_spinor_normSq ψ).const_mul _)
    (integrable_spinor_normSq (diracHamiltonian mc2 ⟨ψ, hψ⟩)) ?_
  filter_upwards [hGS] with ξ hξ
  rw [hξ]
  have hE : mc2 ^ 2 ≤ diracEnergy mc2 ξ ^ 2 := by
    rw [diracEnergy_sq]; nlinarith [laplacianSymbol_nonneg ξ]
  have hS : 0 ≤ ∑ a, ‖(fourierL2 (ψ a) : R3 → ℂ) ξ‖ ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  nlinarith [hE, hS]

/-- **The free Dirac operator is bounded below in norm by `|mc²|·‖ψ‖`.** -/
lemma diracHamiltonian_norm_ge (mc2 : ℝ) (ψ : DiracSpinorL2) (hψ : MemSobolevDiracH1 ψ) :
    |mc2| * ‖ψ‖ ≤ ‖diracHamiltonian mc2 ⟨ψ, hψ⟩‖ := by
  have h1 : (|mc2| * ‖ψ‖) ^ 2 ≤ ‖diracHamiltonian mc2 ⟨ψ, hψ⟩‖ ^ 2 := by
    rw [mul_pow, sq_abs]; exact diracHamiltonian_normSq_ge mc2 ψ hψ
  calc |mc2| * ‖ψ‖ = Real.sqrt ((|mc2| * ‖ψ‖) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt (‖diracHamiltonian mc2 ⟨ψ, hψ⟩‖ ^ 2) := Real.sqrt_le_sqrt h1
    _ = ‖diracHamiltonian mc2 ⟨ψ, hψ⟩‖ := Real.sqrt_sq (norm_nonneg _)

/-! ## The mass gap -/

/-- **The free Dirac operator has no spectral mass in the open gap `(−|mc²|, |mc²|)`** — the
relativistic mass gap of width `2mc²`.  Combines the operator lower bound `‖H_D ψ‖ ≥ |mc²|·‖ψ‖` with
the spectral-gap engine. -/
theorem diracHamiltonian_mass_gap (mc2 : ℝ) :
    spectralProjection (diracUnitaryGroup mc2) (Set.Ioo (-|mc2|) |mc2|) measurableSet_Ioo = 0 := by
  refine spectralProjection_Ioo_eq_zero_of_norm_ge (diracUnitaryGroup mc2) |mc2| fun ψ => ?_
  have hsob : (ψ : DiracSpinorL2) ∈ SobolevDiracH1 := by
    rw [← generator_diracUnitaryGroup_domain mc2]; exact ψ.2
  have htrans : generator (diracUnitaryGroup mc2) ψ
      = diracHamiltonian mc2 ⟨(ψ : DiracSpinorL2), hsob⟩ := by
    have h := (LinearPMap.ext_iff.mp (generator_diracUnitaryGroup mc2)).2 (hf := ψ.2) (hg := hsob)
    rwa [Subtype.coe_eta] at h
  rw [htrans]
  exact diracHamiltonian_norm_ge mc2 (ψ : DiracSpinorL2) hsob

end Spectra.QuantumMechanics.Dirac
end
