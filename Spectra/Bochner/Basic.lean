/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Bochner.GNS.PosDefFun
import Spectra.Bochner.Borel.Measure.Basic

/-!
# Bochner's Theorem

This file assembles Bochner's theorem — a function `f : ℝ → ℂ` is continuous and positive
definite if and only if it is the Fourier–Stieltjes transform of a unique finite positive Borel
measure on `ℝ` — from the pieces built in the `Bochner.GNS` and `Bochner.Borel` directories.

The existence direction is the spectral route:

1. **GNS** (`Bochner.GNS.PosDefFun`): a continuous positive definite function `f` gives a Hilbert
   space `H`, a strongly continuous group of isometries `U(t)`, and a cyclic vector `ξ` with
   `f(t) = ⟨ξ, U(t)ξ⟩`.
2. **Stone's theorem** (`OneParameterUnitaryGroup.Basic`): the group `U(t)` has a self-adjoint
   generator `A` with `U(t) = exp(itA)`.
3. **The spectral theorem** (`Bochner.Borel.Measure.Basic`): the self-adjoint operator `A` has a
   projection-valued measure `E`, giving `⟨U(t)ξ, ξ⟩ = ∫ e^{itλ} d⟨E(λ)ξ, ξ⟩`.

The representing measure is `μ(S) = ⟨E(S)ξ, ξ⟩`. In one line:

```
f(t) = ⟨ξ, U(t)ξ⟩                       [GNS]
     = ⟨ξ, exp(itA)ξ⟩                   [Stone]
     = ∫ e^{itλ} d⟨E(λ)ξ, ξ⟩            [spectral theorem]
     = ∫ e^{itλ} dμ(λ)                  [define μ := ⟨E(·)ξ, ξ⟩]
```

The converse direction — every Fourier–Stieltjes transform of a finite positive measure is
continuous and positive definite — is proved directly in this file (continuity by dominated
convergence, Hermitian symmetry by conjugating under the integral, positive definiteness by
recognizing the double sum `∑ᵢⱼ c̄ᵢcⱼ ∫ e^{iω(tⱼ-tᵢ)} dμ` as `∫ ‖∑ⱼ cⱼe^{iωtⱼ}‖² dμ ≥ 0`).

## Main definitions

* `bochnerMeasureSpectral` — the representing measure for `f`, built via GNS → Stone → the
  spectral theorem.

## Main statements

* `bochner_existence` — every continuous positive definite `f` is the Fourier–Stieltjes transform
  of some finite positive Borel measure.
* `bochnerMeasureSpectral_total_mass` — the representing measure has total mass `(f 0).re`.
* `bochner_theorem` — Bochner's theorem: `f` continuous and positive definite implies `f` is the
  Fourier–Stieltjes transform of a *unique* finite positive Borel measure.
* `bochner_theorem_iff` — the full characterization, as an `iff`.
* `isContinuous_fourierStieltjes` — the converse direction: the Fourier–Stieltjes transform of a
  finite positive Borel measure is continuous and positive definite.

## Implementation notes

The existence direction goes through the spectral theorem for self-adjoint operators rather than
Bochner's classical compactness argument (Stone–Weierstrass / Helly selection on the space of
positive definite functions), since Spectra already has the spectral theorem and Stone's theorem
as reusable infrastructure; the composition is shorter than re-deriving compactness from scratch.

## References

* [Rudin, *Fourier Analysis on Groups*][rudin1962], §1.4.3
* [Reed–Simon, *Methods of Modern Mathematical Physics I*][reedsimon1980], §VII
-/

open Complex MeasureTheory Filter Topology
open Spectra.Bochner.GNS
open Spectra.Fourier
open Spectra.PositiveDefinite
open Spectra.Borel
open SpectralMeasure

namespace Spectra.Bochner

/-- Puts the `NormedAddCommGroup`/`InnerProductSpace`/`CompleteSpace` instances of a GNS Hilbert
space `gns.H` into scope, given `gns : GNSUnitaryGroup f`. Collapses the three-line
`letI`/`letI`/`haveI` boilerplate shared by every proof below that unfolds
`gnsUnitaryConstruction`. -/
local macro "gnsInstances " g:term : tactic =>
  `(tactic| (letI := ($g).instNACG; letI := ($g).instIPS; haveI := ($g).instComplete))

/-- **The Bochner measure via the spectral route.**
Given `f` continuous and positive definite:
1. GNS gives `(H, U, ξ)` with `f(t) = ⟨ξ, U(t)ξ⟩`.
2. Stone gives self-adjoint `A` with `U(t) = exp(itA)`.
3. The spectral theorem gives a PVM `E` for `A`.
4. Define `μ(S) = ⟨E(S)ξ, ξ⟩`.
Then `μ` is a finite positive Borel measure with `f(t) = ∫ e^{itλ} dμ(λ)`. -/
noncomputable def bochnerMeasureSpectral (f : ℝ → ℂ) (hf : IsContinuous f) : Measure ℝ := by
  let gns := gnsUnitaryConstruction hf
  gnsInstances gns
  exact (spectral_scalar_measure_exists (toOneParameterUnitaryGroup gns)
    (gnsCyclic gns.toGNSData)).choose

/-- The Bochner measure is finite. -/
lemma bochnerMeasureSpectral_finite {f : ℝ → ℂ} (hf : IsContinuous f) :
    IsFiniteMeasure (bochnerMeasureSpectral f hf) := by
  let gns := gnsUnitaryConstruction hf
  gnsInstances gns
  exact (spectral_scalar_measure_exists (toOneParameterUnitaryGroup gns)
    (gnsCyclic gns.toGNSData)).choose_spec.1

/-- The defining Fourier representation of the Bochner measure: `f(t) = ∫ e^{itω} dμ(ω)` for
`μ = bochnerMeasureSpectral f hf`. Recorded standalone since both `bochner_existence` and
`bochnerMeasureSpectral_total_mass` need it. -/
lemma bochnerMeasureSpectral_fourier {f : ℝ → ℂ} (hf : IsContinuous f) (t : ℝ) :
    f t = ∫ ω, cexp (I * (ω : ℂ) * (t : ℂ)) ∂(bochnerMeasureSpectral f hf) := by
  let gns := gnsUnitaryConstruction hf
  gnsInstances gns
  rw [← gns_representation gns t]
  exact (spectral_scalar_measure_exists
    (toOneParameterUnitaryGroup gns) (gnsCyclic gns.toGNSData)).choose_spec.2 t

/-- **Total mass of the Bochner measure.** Evaluating `bochnerMeasureSpectral_fourier` at `t = 0`
gives `f(0) = ∫ 1 dμ = μ(univ)`, and `μ(univ)` is real (as a finite-measure total mass), so the
total mass is `(f 0).re`. -/
lemma bochnerMeasureSpectral_total_mass {f : ℝ → ℂ} (hf : IsContinuous f) :
    haveI := bochnerMeasureSpectral_finite hf
    ((bochnerMeasureSpectral f hf) Set.univ).toReal = (f 0).re := by
  haveI := bochnerMeasureSpectral_finite hf
  have h := bochnerMeasureSpectral_fourier hf 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, integral_const] at h
  rw [Complex.real_smul, mul_one, Measure.real_def] at h
  rw [h, Complex.ofReal_re]

variable (μ : Measure ℝ) [IsFiniteMeasure μ]

/-! ## Continuity -/

/-- The Fourier–Stieltjes transform of a finite measure is continuous
(dominated convergence with constant bound `1`). -/
lemma fourierStieltjes_continuous :
    Continuous (fun t : ℝ => ∫ ω, cexp (I * (ω : ℂ) * (t : ℂ)) ∂μ) := by
  apply continuous_of_dominated (bound := fun _ : ℝ => (1 : ℝ))
  · intro t
    exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  · intro t
    filter_upwards with ω
    have h0 : (I * (ω : ℂ) * (t : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    exact le_of_eq (by rw [Complex.norm_exp, h0, Real.exp_zero])
  · exact integrable_const (1 : ℝ)
  · filter_upwards with ω
    exact Complex.continuous_exp.comp (by fun_prop)

/-! ## Hermitian symmetry -/

omit [IsFiniteMeasure μ] in
/-- Hermitian symmetry of the Fourier–Stieltjes transform: conjugation
passes through the (real, positive) measure. -/
lemma fourierStieltjes_conj_neg (t : ℝ) :
    (∫ ω, cexp (I * (ω : ℂ) * ((-t : ℝ) : ℂ)) ∂μ)
      = starRingEnd ℂ (∫ ω, cexp (I * (ω : ℂ) * (t : ℂ)) ∂μ) := by
  rw [← integral_conj]
  refine integral_congr_ae (.of_forall fun ω => ?_)
  simp [← Complex.exp_conj]

/-! ## Positive definiteness -/

/-- **Core positivity computation.** For any `t : Fin n → ℝ`, `c : Fin n → ℂ`,
`∑ᵢⱼ c̄ᵢ cⱼ ∫ e^{iω(tⱼ-tᵢ)} dμ = ∫ ‖∑ⱼ cⱼ e^{iωtⱼ}‖² dμ ≥ 0`. -/
lemma fourierStieltjes_double_sum_nonneg {n : ℕ} (t : Fin n → ℝ) (c : Fin n → ℂ) :
    0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        ∫ ω, cexp (I * (ω : ℂ) * ((t j - t i : ℝ) : ℂ)) ∂μ).re := by
  classical
  -- the "vector" aᵢ(ω) = cᵢ e^{iωtᵢ}
  set a : Fin n → ℝ → ℂ := fun i ω => c i * cexp (I * (ω : ℂ) * (t i : ℂ)) with ha
  have ha_cont : ∀ i, Continuous (a i) := by
    intro i
    simp only [ha]
    exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))
  have ha_norm : ∀ (i : Fin n) (ω : ℝ), ‖a i ω‖ = ‖c i‖ := by
    intro i ω
    have h0 : (I * (ω : ℂ) * (t i : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    simp only [ha, norm_mul, Complex.norm_exp]
    rw [h0, Real.exp_zero, mul_one]
  -- each pairing is integrable: bounded by ‖cᵢ‖·‖cⱼ‖, μ finite
  have ha_int : ∀ i j, Integrable (fun ω => starRingEnd ℂ (a i ω) * a j ω) μ := by
    intro i j
    have hcont : Continuous fun ω : ℝ => starRingEnd ℂ (a i ω) * a j ω :=
      (Complex.continuous_conj.comp (ha_cont i)).mul (ha_cont j)
    refine (integrable_const (‖c i‖ * ‖c j‖)).mono' hcont.aestronglyMeasurable ?_
    filter_upwards with ω
    exact le_of_eq (by rw [norm_mul, RCLike.norm_conj, ha_norm i ω, ha_norm j ω])
  -- pointwise:  c̄ᵢ cⱼ e^{iω(tⱼ-tᵢ)}  =  conj(aᵢ ω) · aⱼ ω
  have hptwise : ∀ (i j : Fin n) (ω : ℝ),
      starRingEnd ℂ (c i) * c j * cexp (I * (ω : ℂ) * ((t j - t i : ℝ) : ℂ))
        = starRingEnd ℂ (a i ω) * a j ω := by
    intro i j ω
    have hexp : -I * (ω : ℂ) * (t i : ℂ) + I * (ω : ℂ) * (t j : ℂ)
        = I * (ω : ℂ) * ((t j - t i : ℝ) : ℂ) := by
      push_cast
      ring
    simp only [ha, map_mul, ← Complex.exp_conj, Complex.conj_I, Complex.conj_ofReal]
    rw [mul_mul_mul_comm, ← Complex.exp_add, hexp]
  -- the double sum is ∫ ‖∑ⱼ aⱼ‖² dμ
  have key : (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        ∫ ω, cexp (I * (ω : ℂ) * ((t j - t i : ℝ) : ℂ)) ∂μ)
      = ((∫ ω, Complex.normSq (∑ j, a j ω) ∂μ : ℝ) : ℂ) :=
    calc (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
            ∫ ω, cexp (I * (ω : ℂ) * ((t j - t i : ℝ) : ℂ)) ∂μ)
        -- (1) pull the constants into the integrals
        = ∑ i, ∑ j, ∫ ω, starRingEnd ℂ (a i ω) * a j ω ∂μ := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [← integral_const_mul]
          exact integral_congr_ae (.of_forall fun ω => hptwise i j ω)
        -- (2) swap the finite sums with the integral
      _ = ∑ i, ∫ ω, ∑ j, starRingEnd ℂ (a i ω) * a j ω ∂μ :=
          Finset.sum_congr rfl fun i _ =>
            (integral_finsetSum _ fun j _ => ha_int i j).symm
      _ = ∫ ω, ∑ i, ∑ j, starRingEnd ℂ (a i ω) * a j ω ∂μ :=
          (integral_finsetSum _ fun i _ =>
            integrable_finsetSum _ fun j _ => ha_int i j).symm
        -- (3) recognize  ∑ᵢⱼ conj(aᵢ)·aⱼ = conj(∑aᵢ)·(∑aⱼ) = ‖∑aⱼ‖²
      _ = ∫ ω, ((Complex.normSq (∑ j, a j ω) : ℝ) : ℂ) ∂μ := by
          refine integral_congr_ae (.of_forall fun ω => ?_)
          simp [show ((Complex.normSq (∑ j, a j ω) : ℝ) : ℂ)
                = starRingEnd ℂ (∑ i, a i ω) * ∑ j, a j ω from
              Complex.normSq_eq_conj_mul_self,
            map_sum, Finset.sum_mul_sum]
        -- (4) the integral of a real-valued function is real
      _ = ((∫ ω, Complex.normSq (∑ j, a j ω) ∂μ : ℝ) : ℂ) := integral_ofReal
  rw [key, Complex.ofReal_re]
  exact integral_nonneg fun ω => Complex.normSq_nonneg _

/-! ## Glue: `IsContinuous` for the Fourier–Stieltjes transform

The three lemmas below are the only place the precise definitions of
`IsPositiveDefinite` / `IsHermitian` are consumed; adjust here if the
project's conventions differ from the assumptions in the module docstring. -/

/-- The Fourier–Stieltjes transform of a finite positive measure is
positive definite. -/
lemma isPositiveDefinite_fourierStieltjes :
    IsPositiveDefinite (fun t : ℝ => ∫ ω, cexp (I * (ω : ℂ) * (t : ℂ)) ∂μ) := by
  intro n t c
  have h := fourierStieltjes_double_sum_nonneg μ (fun i => -t i) c
  simp only [neg_sub_neg] at h
  simpa using h

omit [IsFiniteMeasure μ] in
/-- The Fourier–Stieltjes transform of a finite positive measure is
Hermitian. -/
lemma isHermitian_fourierStieltjes :
    IsHermitian (fun t : ℝ => ∫ ω, cexp (I * (ω : ℂ) * (t : ℂ)) ∂μ) := by
  intro t
  simpa using fourierStieltjes_conj_neg μ t

/-- **Bochner's theorem (converse direction).**
The Fourier–Stieltjes transform of a finite positive Borel measure is a
continuous positive definite function. -/
theorem isContinuous_fourierStieltjes :
    IsContinuous (fun t : ℝ => ∫ ω, cexp (I * (ω : ℂ) * (t : ℂ)) ∂μ) :=
  ⟨isPositiveDefinite_fourierStieltjes μ, isHermitian_fourierStieltjes μ,
    (fourierStieltjes_continuous μ).continuousAt⟩

/-! ## Bochner's theorem as a characterization -/

/-- **Bochner's theorem (Existence).**
Every continuous positive definite function on `ℝ` is the
Fourier–Stieltjes transform of a finite positive Borel measure.
The proof composes GNS, Stone, and the spectral theorem:
`f(t) = ⟨ξ, U(t)ξ⟩ = ⟨ξ, e^{itA}ξ⟩ = ∫ e^{itλ} dμ(λ)`. -/
theorem bochner_existence (f : ℝ → ℂ) (hf : IsContinuous f) :
    ∃ (μ : Measure ℝ), IsFiniteMeasure μ ∧
      ∀ t, f t = ∫ ω, cexp (I * (ω : ℂ) * (t : ℂ)) ∂μ :=
  ⟨bochnerMeasureSpectral f hf, bochnerMeasureSpectral_finite hf,
    fun t => bochnerMeasureSpectral_fourier hf t⟩

/-- **Bochner's Theorem (Complete).**
A function `f : ℝ → ℂ` is continuous and positive definite if and only
if it is the Fourier–Stieltjes transform of a unique finite positive
Borel measure on `ℝ`. -/
theorem bochner_theorem (f : ℝ → ℂ) (hf : IsContinuous f) :
    ∃! (μ : Measure ℝ), IsFiniteMeasure μ ∧
      ∀ t, f t = ∫ ω, cexp (I * (ω : ℂ) * (t : ℂ)) ∂μ := by
  obtain ⟨μ, hμ_fin, hμ_rep⟩ := bochner_existence f hf
  refine ⟨μ, ⟨hμ_fin, hμ_rep⟩, ?_⟩
  intro ν ⟨hν_fin, hν_rep⟩
  haveI := hμ_fin
  haveI := hν_fin
  exact (fourier_uniqueness μ ν
    (fun t => (hμ_rep t).symm.trans (hν_rep t))).symm

/-- **Bochner's Theorem (iff form).**
A function `f : ℝ → ℂ` is continuous and positive definite if and only
if it is the Fourier–Stieltjes transform of a unique finite positive
Borel measure on `ℝ`. -/
theorem bochner_theorem_iff (f : ℝ → ℂ) :
    IsContinuous f ↔
      ∃! (μ : Measure ℝ), IsFiniteMeasure μ ∧
        ∀ t, f t = ∫ ω, cexp (I * (ω : ℂ) * (t : ℂ)) ∂μ := by
  constructor
  · exact bochner_theorem f
  · rintro ⟨μ, ⟨hμ_fin, hμ_rep⟩, -⟩
    haveI := hμ_fin
    rw [funext hμ_rep]
    exact isContinuous_fourierStieltjes μ

end Spectra.Bochner
