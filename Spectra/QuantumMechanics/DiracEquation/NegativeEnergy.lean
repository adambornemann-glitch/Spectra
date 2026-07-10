/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.DiracEquation.ConcreteSpectrum
/-!
# Negative-energy wavepackets for the free Dirac operator (Step (b)/3)

This file discharges the last hypothesis of `ConcreteSpectrum.lean`'s conditional theorems by
constructing, for every `N`, a nonzero `H¹` spinor `ψ` with `Re⟪H_D ψ, ψ⟫ < N·‖ψ‖²` — making
`diracHamiltonian_unbounded_below` (hence `_not_semibounded`) unconditional.

## Strategy

On the Fourier side the free Dirac operator is multiplication by the matrix symbol
`Ĥ(ξ) = 2π(α·ξ) + mc²β = diracMomentumOp (2π·ξ) mc²`, with `Ĥ(ξ)² = E(ξ)²·I` and
`E(ξ) = √((2π‖ξ‖)² + (mc²)²)` (`diracEnergy`).  By the mass-shell factorisation
`(Ĥ+E)(Ĥ−E) = 0` (`diracMomentumOp_factor`), the vector `w(ξ) = (Ĥ(ξ) − E(ξ)·I) v₀` is a
negative-energy eigenvector: `Ĥ(ξ) w(ξ) = −E(ξ) w(ξ)`.

We take `ψ̂(ξ) = g(ξ)·w(ξ)` with `g` an L² bump on a high-momentum ball `B` (where `E(ξ) ≥ E₀`
is large), and `ψ = 𝓕⁻¹ ψ̂`.  Then `⟪H_D ψ, ψ⟫ = −∫ E(ξ)‖ψ̂(ξ)‖² ≤ −E₀‖ψ‖²`, and choosing `B` far
enough out makes `−E₀ < N`.

This file is built bottom-up: this first section is the **matrix/vector layer** (symbol, energy,
the eigenvector, its nonvanishing component, continuity).

## Main definitions

* `diracFullSymbol` — the full Dirac Fourier symbol `Ĥ(ξ) = 2π(α·ξ) + mc²β`.
* `diracEnergy` — the on-shell energy `E(ξ) = √((2π‖ξ‖)² + (mc²)²)`.
* `negEnergyVec` — the fibre eigenvector `w(ξ) = (Ĥ(ξ) − E(ξ)·I) v`.
* `momBall`, `bumpFn` — the receding high-momentum ball `B(R)` and its L² indicator bump.
* `wpSpinor` — the negative-energy wavepacket `ψ = 𝓕⁻¹ ψ̂` on `L²(ℝ³; ℂ⁴)`.

## Main results

* `diracFullSymbol_mulVec_negEnergyVec` — the eigen-equation `Ĥ(ξ) w(ξ) = −E(ξ) w(ξ)`.
* `wpSpinor_ne_zero` — the wavepacket is nonzero (its `0`-component is supported on `B(R)`).
* `wpSpinor_energy_le` — the energy form is bounded above by `−2π(R−1)·‖ψ‖²`.
* `dirac_energy_witness` — for every `N` a state with `Re⟪H_D ψ, ψ⟫ < N·‖ψ‖²`.
* `diracHamiltonian_unbounded_below_unconditional`,
  `diracHamiltonian_not_semibounded_unconditional` — the unconditional Dirac-sea prediction.

## References

* [Thaller, *The Dirac Equation*][thaller1992], Section 1.4 and Chapter 10 (the negative-energy
  plane-wave / Dirac-sea construction formalized here)

## Tags

Dirac operator, negative energy, Dirac sea, unbounded below, semiboundedness, wavepacket,
mass shell, Fourier symbol
-/

open Complex MeasureTheory Matrix
open scoped InnerProductSpace
open Spectra.Sobolev
open Spectra.OneParameterUnitaryGroup

noncomputable section
namespace Spectra.QuantumMechanics.Dirac

/-! ## The full Fourier symbol `Ĥ(ξ)` and the on-shell energy `E(ξ)` -/

/-- The momentum vector `2π·ξ` feeding the Dirac symbol. -/
def momScale (ξ : R3) : Fin 3 → ℝ := fun i => 2 * Real.pi * ξ i

/-- The **full Dirac Fourier symbol** `Ĥ(ξ) = 2π(α·ξ) + mc²β = diracMomentumOp (2π·ξ) mc²`. -/
def diracFullSymbol (mc2 : ℝ) (ξ : R3) : Matrix (Fin 4) (Fin 4) ℂ :=
  diracMomentumOp (momScale ξ) mc2

/-- The **on-shell energy** `E(ξ) = √((2π‖ξ‖)² + (mc²)²)`. -/
def diracEnergy (mc2 : ℝ) (ξ : R3) : ℝ := energyMomentum (momScale ξ) mc2

/-- `Ĥ(ξ) = diracKineticSymbol ξ + mc²·β`: the kinetic symbol plus the mass term. -/
lemma diracFullSymbol_eq (mc2 : ℝ) (ξ : R3) :
    diracFullSymbol mc2 ξ = diracKineticSymbol ξ + (mc2 : ℂ) • diracBeta := by
  ext a b
  simp only [diracFullSymbol, diracMomentumOp, momScale, diracKineticSymbol, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Complex.ofReal_zero]
  push_cast
  ring

/-- The `(0,0)` entry of the full symbol is the bare mass `mc²` (the velocity matrices are
off-diagonal). -/
lemma diracFullSymbol_zero_zero (mc2 : ℝ) (ξ : R3) :
    diracFullSymbol mc2 ξ 0 0 = (mc2 : ℂ) := by
  rw [diracFullSymbol, diracMomentumOp]
  simp [diracAlpha1, diracAlpha2, diracAlpha3, diracBeta, Matrix.add_apply]

/-- `E(ξ)² = (2π‖ξ‖)² + (mc²)²`. -/
lemma diracEnergy_sq (mc2 : ℝ) (ξ : R3) :
    diracEnergy mc2 ξ ^ 2 = laplacianSymbol ξ + mc2 ^ 2 := by
  unfold diracEnergy
  rw [energyMomentum_sq]
  have h := energyMomentumSq_eq_normSq ξ
  unfold energyMomentumSq momScale laplacianSymbol
  unfold energyMomentumSq at h
  simp only at h ⊢
  linear_combination (2 * Real.pi) ^ 2 * h

/-- `0 ≤ E(ξ)`. -/
lemma diracEnergy_nonneg (mc2 : ℝ) (ξ : R3) : 0 ≤ diracEnergy mc2 ξ :=
  Real.sqrt_nonneg _

/-- `2π‖ξ‖ ≤ E(ξ)`: the energy dominates the kinetic part. -/
lemma diracEnergy_ge (mc2 : ℝ) (ξ : R3) : 2 * Real.pi * ‖ξ‖ ≤ diracEnergy mc2 ξ := by
  have h1 : laplacianSymbol ξ ≤ diracEnergy mc2 ξ ^ 2 := by
    rw [diracEnergy_sq]; nlinarith [sq_nonneg mc2]
  calc 2 * Real.pi * ‖ξ‖ = Real.sqrt (laplacianSymbol ξ) := (sqrt_laplacianSymbol ξ).symm
    _ ≤ Real.sqrt (diracEnergy mc2 ξ ^ 2) := Real.sqrt_le_sqrt h1
    _ = diracEnergy mc2 ξ := Real.sqrt_sq (diracEnergy_nonneg mc2 ξ)

/-! ## The negative-energy eigenvector `w(ξ) = (Ĥ(ξ) − E(ξ)·I) v₀` -/

/-- The candidate negative-energy fibre vector `w(ξ) = (Ĥ(ξ) − E(ξ)·I) v`. -/
def negEnergyVec (mc2 : ℝ) (v : Fin 4 → ℂ) (ξ : R3) : Fin 4 → ℂ :=
  (diracFullSymbol mc2 ξ - (diracEnergy mc2 ξ : ℂ) • 1) *ᵥ v

lemma negEnergyVec_apply (mc2 : ℝ) (v : Fin 4 → ℂ) (ξ : R3) (a : Fin 4) :
    negEnergyVec mc2 v ξ a
      = ∑ b, (diracFullSymbol mc2 ξ - (diracEnergy mc2 ξ : ℂ) • 1) a b * v b := rfl

/-- **The eigen-equation**: `Ĥ(ξ) w(ξ) = −E(ξ) w(ξ)`, from the mass-shell factorisation. -/
lemma diracFullSymbol_mulVec_negEnergyVec (mc2 : ℝ) (v : Fin 4 → ℂ) (ξ : R3) :
    diracFullSymbol mc2 ξ *ᵥ negEnergyVec mc2 v ξ
      = (-(diracEnergy mc2 ξ) : ℂ) • negEnergyVec mc2 v ξ := by
  have hfac : (diracFullSymbol mc2 ξ + (diracEnergy mc2 ξ : ℂ) • 1)
      * (diracFullSymbol mc2 ξ - (diracEnergy mc2 ξ : ℂ) • 1) = 0 :=
    diracMomentumOp_factor (momScale ξ) mc2
  have key : (diracFullSymbol mc2 ξ + (diracEnergy mc2 ξ : ℂ) • 1) *ᵥ negEnergyVec mc2 v ξ = 0 := by
    rw [negEnergyVec, Matrix.mulVec_mulVec, hfac, Matrix.zero_mulVec]
  have hexpand : diracFullSymbol mc2 ξ *ᵥ negEnergyVec mc2 v ξ
      + (diracEnergy mc2 ξ : ℂ) • negEnergyVec mc2 v ξ = 0 := by
    rw [← key, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [neg_smul]
  exact eq_neg_of_add_eq_zero_left hexpand

/-- The `0`-component of `w(ξ)` for `v₀ = e₀` is `mc² − E(ξ)`, nonzero whenever `E(ξ) > mc²`. -/
lemma negEnergyVec_zero_eq (mc2 : ℝ) (ξ : R3) :
    negEnergyVec mc2 (Pi.single 0 1) ξ 0 = (mc2 : ℂ) - (diracEnergy mc2 ξ : ℂ) := by
  rw [negEnergyVec_apply]
  rw [Fintype.sum_eq_single (0 : Fin 4) (fun b hb => by
    rw [Pi.single_eq_of_ne hb, mul_zero])]
  rw [Pi.single_eq_same, mul_one, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one, diracFullSymbol_zero_zero]

/-! ## Continuity (needed to bound the wavepacket on the compact momentum ball) -/

/-- Each coordinate `ξ ↦ ξ i` on `ℝ³` is continuous. -/
lemma continuous_coord (i : Fin 3) : Continuous (fun ξ : R3 => ξ i) :=
  (EuclideanSpace.proj i).continuous

lemma continuous_momScale (i : Fin 3) : Continuous (fun ξ : R3 => momScale ξ i) := by
  unfold momScale; exact continuous_const.mul (continuous_coord i)

lemma continuous_diracFullSymbol_entry (mc2 : ℝ) (a b : Fin 4) :
    Continuous (fun ξ : R3 => diracFullSymbol mc2 ξ a b) := by
  simp only [diracFullSymbol, diracMomentumOp, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  refine ((((Complex.continuous_ofReal.comp (continuous_momScale 0)).mul continuous_const).add
    ((Complex.continuous_ofReal.comp (continuous_momScale 1)).mul continuous_const)).add
    ((Complex.continuous_ofReal.comp (continuous_momScale 2)).mul continuous_const)).add
    continuous_const

lemma continuous_diracEnergy (mc2 : ℝ) : Continuous (diracEnergy mc2) := by
  unfold diracEnergy energyMomentum
  refine Real.continuous_sqrt.comp ?_
  unfold energyMomentumSq
  exact ((((continuous_momScale 0).pow 2).add ((continuous_momScale 1).pow 2)).add
    ((continuous_momScale 2).pow 2)).add continuous_const

lemma continuous_negEnergyVec_apply (mc2 : ℝ) (v : Fin 4 → ℂ) (a : Fin 4) :
    Continuous (fun ξ : R3 => negEnergyVec mc2 v ξ a) := by
  simp only [negEnergyVec_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  refine continuous_finsetSum _ fun b _ => ?_
  exact ((continuous_diracFullSymbol_entry mc2 a b).sub
    ((Complex.continuous_ofReal.comp (continuous_diracEnergy mc2)).mul continuous_const)).mul
    continuous_const

/-! ## The Fourier symbol action of `H_D`

`𝓕(H_D ψ)_a(ξ) = (Ĥ(ξ)·𝓕ψ(ξ))_a` a.e.: the kinetic part is `fourier_diracKineticFn_symbol`, the
mass part is the componentwise commutation `𝓕 ∘ matrixOp = matrixOp ∘ 𝓕`. -/

/-- **Mass-term Fourier commutation**: `𝓕((matrixOp M ψ)_a) =ᵐ ξ ↦ Σ_b M_{ab}·𝓕(ψ_b)(ξ)`.
Since `𝓕` is componentwise-linear and `matrixOp` mixes components by the constant matrix `M`. -/
lemma fourier_matrixOp (M : Matrix (Fin 4) (Fin 4) ℂ) (ψ : DiracSpinorL2) (a : Fin 4) :
    (fourierL2 ((matrixOp M ψ) a) : R3 → ℂ) =ᵐ[volume]
      fun ξ => ∑ b, M a b * (fourierL2 (ψ b) : R3 → ℂ) ξ := by
  have h1 : fourierL2 ((matrixOp M ψ) a) = ∑ b, M a b • fourierL2 (ψ b) := by
    rw [matrixOp_apply, map_sum]
    exact Finset.sum_congr rfl fun b _ => map_smul fourierL2 (M a b) (ψ b)
  rw [h1]
  exact l2_coeFn_sum_smul Finset.univ (fun b => M a b) (fun b => fourierL2 (ψ b))
    (fun b => (fourierL2 (ψ b) : R3 → ℂ)) (fun b _ => Filter.EventuallyEq.rfl)

/-- **The full Fourier symbol of `H_D`**: `𝓕(H_D ψ)_a(ξ) =ᵐ Σ_b Ĥ(ξ)_{ab}·𝓕(ψ_b)(ξ)`. -/
lemma fourier_diracHamiltonian_symbol (mc2 : ℝ) (ψ : DiracSpinorL2)
    (hψ : MemSobolevDiracH1 ψ) (a : Fin 4) :
    (fourierL2 ((diracHamiltonian mc2 ⟨ψ, hψ⟩) a) : R3 → ℂ) =ᵐ[volume]
      fun ξ => ∑ b, diracFullSymbol mc2 ξ a b * (fourierL2 (ψ b) : R3 → ℂ) ξ := by
  have hval : (diracHamiltonian mc2 ⟨ψ, hψ⟩) a
      = (diracKineticFn ψ hψ) a + (matrixOp ((mc2 : ℂ) • diracBeta) ψ) a := rfl
  rw [hval, map_add]
  filter_upwards [Lp.coeFn_add (fourierL2 ((diracKineticFn ψ hψ) a))
      (fourierL2 ((matrixOp ((mc2 : ℂ) • diracBeta) ψ) a)),
    fourier_diracKineticFn_symbol ψ hψ a,
    fourier_matrixOp ((mc2 : ℂ) • diracBeta) ψ a] with ξ hadd hkin hmass
  rw [hadd, Pi.add_apply, hkin, hmass, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [diracFullSymbol_eq, Matrix.add_apply, add_mul]

/-! ## The high-momentum ball and the L² bump -/

/-- A high-momentum centre `(R, 0, 0) ∈ ℝ³`. -/
def momCenter (R : ℝ) : R3 := EuclideanSpace.single (0 : Fin 3) R

/-- The momentum ball `B(R)` of radius `1` around `(R,0,0)`; on it `‖ξ‖ ≥ R − 1`. -/
def momBall (R : ℝ) : Set R3 := Metric.closedBall (momCenter R) 1

lemma momBall_measurable (R : ℝ) : MeasurableSet (momBall R) := measurableSet_closedBall

lemma momBall_finite (R : ℝ) : volume (momBall R) ≠ ⊤ := measure_closedBall_lt_top.ne

lemma momBall_pos (R : ℝ) : 0 < volume (momBall R) :=
  Metric.measure_closedBall_pos volume (momCenter R) one_pos

/-- Lower bound on the momentum modulus inside the ball: `R − 1 ≤ ‖ξ‖`. -/
lemma momBall_norm_ge (R : ℝ) (hR : 0 ≤ R) (ξ : R3) (hξ : ξ ∈ momBall R) :
    R - 1 ≤ ‖ξ‖ := by
  rw [momBall, Metric.mem_closedBall] at hξ
  have hc : ‖momCenter R‖ = R := by
    rw [momCenter, PiLp.norm_single, Real.norm_eq_abs, abs_of_nonneg hR]
  have h1 : ‖momCenter R‖ - ‖ξ‖ ≤ dist ξ (momCenter R) := by
    rw [dist_eq_norm, norm_sub_rev]; exact norm_sub_norm_le _ _
  rw [hc] at h1; linarith

/-- The raw bump function: the indicator of the momentum ball. -/
def bumpFn (R : ℝ) : R3 → ℂ := Set.indicator (momBall R) (fun _ => 1)

/-- **Bounded continuous multiplier × bump is L²**: for `m` continuous, `ξ ↦ m ξ · 1_{B(R)}(ξ)`
is in `L²`, since `m` is bounded on the compact ball `B(R)` and the bump has finite-measure
support. -/
lemma memLp_mul_bump (R : ℝ) (m : R3 → ℂ) (hm : Continuous m) :
    MemLp (fun ξ => m ξ * bumpFn R ξ) 2 volume := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (momCenter R) 1).exists_bound_of_continuousOn
    hm.continuousOn
  refine MemLp.of_le_mul (c := C)
    (memLp_indicator_const 2 (momBall_measurable R) (1 : ℂ) (Or.inr (momBall_finite R)))
    (hm.aestronglyMeasurable.mul
      ((measurable_const.indicator (momBall_measurable R)).aestronglyMeasurable))
    (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [bumpFn]
  by_cases hξ : ξ ∈ momBall R
  · simp only [Set.indicator_of_mem hξ, mul_one, NormOneClass.norm_one, mul_one]; exact hC ξ hξ
  · simp [Set.indicator_of_notMem hξ]

/-! ## The negative-energy wavepacket `ψ` -/

/-- The Fourier-side components of the wavepacket: `ψ̂_a(ξ) = w(ξ)_a · 1_{B(R)}(ξ)`. -/
def wpFn (mc2 R : ℝ) (a : Fin 4) : R3 → ℂ :=
  fun ξ => negEnergyVec mc2 (Pi.single 0 1) ξ a * bumpFn R ξ

lemma wpFn_memLp (mc2 R : ℝ) (a : Fin 4) : MemLp (wpFn mc2 R a) 2 volume :=
  memLp_mul_bump R (fun ξ => negEnergyVec mc2 (Pi.single 0 1) ξ a)
    (continuous_negEnergyVec_apply mc2 (Pi.single 0 1) a)

/-- The **negative-energy wavepacket** `ψ = 𝓕⁻¹ ψ̂` on `L²(ℝ³; ℂ⁴)`. -/
def wpSpinor (mc2 R : ℝ) : DiracSpinorL2 :=
  diracSpinorCLE.symm (fun a => fourierL2.symm ((wpFn_memLp mc2 R a).toLp (wpFn mc2 R a)))

/-- The Fourier transform of `ψ`'s `a`-component agrees a.e. with `ψ̂_a`. -/
lemma wpSpinor_fourier (mc2 R : ℝ) (a : Fin 4) :
    (fourierL2 ((wpSpinor mc2 R) a) : R3 → ℂ) =ᵐ[volume] wpFn mc2 R a := by
  change (fourierL2 (fourierL2.symm ((wpFn_memLp mc2 R a).toLp (wpFn mc2 R a))) : R3 → ℂ)
      =ᵐ[volume] wpFn mc2 R a
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (wpFn_memLp mc2 R a).coeFn_toLp

/-- `ψ ∈ H¹(ℝ³; ℂ⁴)`: each component has L² Fourier decay, since `derivSymbol · ψ̂_a` is again a
bounded continuous multiplier on the compact bump support. -/
lemma wpSpinor_memH1 (mc2 R : ℝ) : MemSobolevDiracH1 (wpSpinor mc2 R) := by
  intro a
  apply memSobolevH1_of_fourier_decay
  intro k
  have hbase : MemLp (fun ξ => (derivSymbol k ξ * negEnergyVec mc2 (Pi.single 0 1) ξ a)
      * bumpFn R ξ) 2 volume :=
    memLp_mul_bump R (fun ξ => derivSymbol k ξ * negEnergyVec mc2 (Pi.single 0 1) ξ a)
      ((by unfold derivSymbol; fun_prop : Continuous (derivSymbol k)).mul
        (continuous_negEnergyVec_apply mc2 (Pi.single 0 1) a))
  refine hbase.ae_eq ?_
  filter_upwards [wpSpinor_fourier mc2 R a] with ξ hξ
  change (derivSymbol k ξ * negEnergyVec mc2 (Pi.single 0 1) ξ a) * bumpFn R ξ
      = derivSymbol k ξ * (fourierL2 ((wpSpinor mc2 R) a) : R3 → ℂ) ξ
  rw [hξ]; simp only [wpFn]; ring

/-! ## Nonvanishing -/

/-- On the ball (with `R > 1`), `w(ξ)_0 = mc² − E(ξ) ≠ 0`, since `E(ξ) > mc²`. -/
lemma negEnergyVec_zero_ne_on_ball (mc2 R : ℝ) (hR : 1 < R) (ξ : R3) (hξ : ξ ∈ momBall R) :
    negEnergyVec mc2 (Pi.single 0 1) ξ 0 ≠ 0 := by
  have hnorm : 0 < ‖ξ‖ := by
    have := momBall_norm_ge R (by linarith) ξ hξ; linarith
  have hsq : mc2 ^ 2 < diracEnergy mc2 ξ ^ 2 := by
    rw [diracEnergy_sq, laplacianSymbol]
    nlinarith [mul_pos (show (0 : ℝ) < (2 * Real.pi) ^ 2 by positivity) (pow_pos hnorm 2)]
  have hE : mc2 < diracEnergy mc2 ξ :=
    lt_of_le_of_lt (le_abs_self mc2) (by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq (diracEnergy_nonneg mc2 ξ)]
      exact Real.sqrt_lt_sqrt (sq_nonneg mc2) hsq)
  rw [negEnergyVec_zero_eq]
  intro h
  rw [sub_eq_zero] at h
  exact absurd (Complex.ofReal_injective h) (ne_of_lt hE)

/-- **`ψ ≠ 0`**: the `0`-component is `(mc² − E)·1_{B}`, nonzero on the positive-measure ball. -/
lemma wpSpinor_ne_zero (mc2 R : ℝ) (hR : 1 < R) : wpSpinor mc2 R ≠ 0 := by
  -- it suffices the 0-component is nonzero
  have hcomp : (wpSpinor mc2 R) 0 ≠ 0 := by
    -- ψ_0 = 𝓕⁻¹(toLp ψ̂_0); nonzero since ψ̂_0 is not a.e. 0
    have hne_ae : ¬ (wpFn mc2 R 0 =ᵐ[volume] 0) := by
      intro hae
      have h0 : ∀ᵐ ξ ∂volume, wpFn mc2 R 0 ξ = 0 := hae
      rw [MeasureTheory.ae_iff] at h0
      have hsub : momBall R ⊆ {ξ | ¬ wpFn mc2 R 0 ξ = 0} := by
        intro ξ hξ
        simp only [Set.mem_setOf_eq, wpFn, bumpFn, Set.indicator_of_mem hξ, mul_one]
        exact negEnergyVec_zero_ne_on_ball mc2 R hR ξ hξ
      have hle : volume (momBall R) ≤ volume {ξ | ¬ wpFn mc2 R 0 ξ = 0} := measure_mono hsub
      rw [h0] at hle
      exact (momBall_pos R).ne' (nonpos_iff_eq_zero.mp hle)
    have htoLp : (wpFn_memLp mc2 R 0).toLp (wpFn mc2 R 0) ≠ 0 := by
      intro h
      apply hne_ae
      have hz : MemLp (0 : R3 → ℂ) 2 volume := MemLp.zero
      rw [← hz.toLp_zero] at h
      exact (MemLp.toLp_eq_toLp_iff (wpFn_memLp mc2 R 0) hz).1 h
    change fourierL2.symm ((wpFn_memLp mc2 R 0).toLp (wpFn mc2 R 0)) ≠ 0
    intro h
    exact htoLp (by simpa using congrArg fourierL2 h)
  intro h
  exact hcomp (by rw [h]; rfl)

/-! ## The eigen identity for the wavepacket and the energy form -/

/-- **The wavepacket is a generalized negative-energy eigenfunction**:
`𝓕(H_D ψ)_a(ξ) =ᵐ −E(ξ)·𝓕(ψ)_a(ξ)`.  Combines the full symbol action with the pointwise
eigen-equation `Ĥ(ξ) w(ξ) = −E(ξ) w(ξ)`. -/
lemma wpSpinor_fourier_eigen (mc2 R : ℝ) (a : Fin 4) :
    (fourierL2 ((diracHamiltonian mc2 ⟨wpSpinor mc2 R, wpSpinor_memH1 mc2 R⟩) a) : R3 → ℂ)
      =ᵐ[volume]
      fun ξ => (-(diracEnergy mc2 ξ) : ℂ) * (fourierL2 ((wpSpinor mc2 R) a) : R3 → ℂ) ξ := by
  have hae : ∀ᵐ ξ ∂volume, ∀ b,
      (fourierL2 ((wpSpinor mc2 R) b) : R3 → ℂ) ξ = wpFn mc2 R b ξ :=
    ae_all_iff.2 (fun b => wpSpinor_fourier mc2 R b)
  filter_upwards [fourier_diracHamiltonian_symbol mc2 (wpSpinor mc2 R) (wpSpinor_memH1 mc2 R) a,
    wpSpinor_fourier mc2 R a, hae] with ξ hsym hfa haeξ
  rw [hsym, hfa]
  simp only [haeξ, wpFn]
  have keya : ∑ b, diracFullSymbol mc2 ξ a b * negEnergyVec mc2 (Pi.single 0 1) ξ b
      = (-(diracEnergy mc2 ξ) : ℂ) * negEnergyVec mc2 (Pi.single 0 1) ξ a := by
    have h := congrFun (diracFullSymbol_mulVec_negEnergyVec mc2 (Pi.single 0 1) ξ) a
    rw [Pi.smul_apply, smul_eq_mul] at h
    exact h
  calc ∑ b, diracFullSymbol mc2 ξ a b
        * (negEnergyVec mc2 (Pi.single 0 1) ξ b * bumpFn R ξ)
      = (∑ b, diracFullSymbol mc2 ξ a b * negEnergyVec mc2 (Pi.single 0 1) ξ b) * bumpFn R ξ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun b _ => by ring
    _ = (-(diracEnergy mc2 ξ) : ℂ) * (negEnergyVec mc2 (Pi.single 0 1) ξ a * bumpFn R ξ) := by
        rw [keya]; ring

/-- L²-norm² as an integral of the pointwise norm²: `‖f‖² = ∫ ‖f(ξ)‖²`. -/
lemma L2_normSq_integral (f : l2R3) : ‖f‖ ^ 2 = ∫ ξ, ‖(f : R3 → ℂ) ξ‖ ^ 2 ∂volume := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) f, MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner f f)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => inner_self_eq_norm_sq _)

/-- The scalar inner-product identity `⟪c·y, y⟫ = ↑(c·‖y‖²)` for real `c` (top-level form). -/
private lemma inner_ofReal_mul_self (c : ℝ) (y : ℂ) :
    (⟪(c : ℂ) * y, y⟫_ℂ : ℂ) = ((c * ‖y‖ ^ 2 : ℝ) : ℂ) := by
  have h : (⟪y, y⟫_ℂ : ℂ) = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [show (c : ℂ) * y = (c : ℂ) • y from (smul_eq_mul _ _).symm, inner_smul_left,
    Complex.conj_ofReal, h, ← Complex.ofReal_mul]

/-- **Per-component energy form**: `Re⟪(H_D ψ)_a, ψ_a⟫ = ∫ −E(ξ)·‖𝓕(ψ)_a(ξ)‖²`, from the eigen
identity (the `H_D`-image is `−E·ψ̂` componentwise) and Plancherel. -/
lemma wpSpinor_energy_eq (mc2 R : ℝ) (a : Fin 4) :
    (⟪diracHamiltonian mc2 ⟨wpSpinor mc2 R, wpSpinor_memH1 mc2 R⟩ a, (wpSpinor mc2 R) a⟫_ℂ).re
      = ∫ ξ, -(diracEnergy mc2 ξ)
          * ‖(fourierL2 ((wpSpinor mc2 R) a) : R3 → ℂ) ξ‖ ^ 2 ∂volume := by
  have hceq : (⟪diracHamiltonian mc2 ⟨wpSpinor mc2 R, wpSpinor_memH1 mc2 R⟩ a,
        (wpSpinor mc2 R) a⟫_ℂ)
      = ∫ ξ, ((-(diracEnergy mc2 ξ)
          * ‖(fourierL2 ((wpSpinor mc2 R) a) : R3 → ℂ) ξ‖ ^ 2 : ℝ) : ℂ) ∂volume := by
    rw [← fourierL2.inner_map_map
      (diracHamiltonian mc2 ⟨wpSpinor mc2 R, wpSpinor_memH1 mc2 R⟩ a) ((wpSpinor mc2 R) a),
      MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [wpSpinor_fourier_eigen mc2 R a] with ξ heig
    rw [heig, ← Complex.ofReal_neg, inner_ofReal_mul_self]
  rw [hceq, integral_complex_ofReal, Complex.ofReal_re]

/-- **Per-component energy bound**: `Re⟪(H_D ψ)_a, ψ_a⟫ ≤ −2π(R−1)·‖ψ_a‖²`, since `E(ξ) ≥ 2π(R−1)`
on the high-momentum ball that supports `ψ̂`. -/
lemma wpSpinor_energy_component_le (mc2 R : ℝ) (hR : 1 < R) (a : Fin 4) :
    (⟪diracHamiltonian mc2 ⟨wpSpinor mc2 R, wpSpinor_memH1 mc2 R⟩ a, (wpSpinor mc2 R) a⟫_ℂ).re
      ≤ -(2 * Real.pi * (R - 1)) * ‖(wpSpinor mc2 R) a‖ ^ 2 := by
  rw [wpSpinor_energy_eq]
  have hSint : Integrable
      (fun ξ => ‖(fourierL2 ((wpSpinor mc2 R) a) : R3 → ℂ) ξ‖ ^ 2) volume := by
    have h := (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (fourierL2 ((wpSpinor mc2 R) a))
      (fourierL2 ((wpSpinor mc2 R) a))).re
    exact h.congr (Filter.Eventually.of_forall fun ξ => inner_self_eq_norm_sq (𝕜 := ℂ) _)
  have hae : (fun ξ => ⟪(fourierL2 (diracHamiltonian mc2
        ⟨wpSpinor mc2 R, wpSpinor_memH1 mc2 R⟩ a) : R3 → ℂ) ξ,
        (fourierL2 ((wpSpinor mc2 R) a) : R3 → ℂ) ξ⟫_ℂ)
      =ᵐ[volume] fun ξ => ((-(diracEnergy mc2 ξ)
        * ‖(fourierL2 ((wpSpinor mc2 R) a) : R3 → ℂ) ξ‖ ^ 2 : ℝ) : ℂ) := by
    filter_upwards [wpSpinor_fourier_eigen mc2 R a] with ξ heig
    rw [heig, ← Complex.ofReal_neg, inner_ofReal_mul_self]
  have hcint : Integrable (fun ξ => -(diracEnergy mc2 ξ)
      * ‖(fourierL2 ((wpSpinor mc2 R) a) : R3 → ℂ) ξ‖ ^ 2) volume := by
    have h2 := ((MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
      (fourierL2 (diracHamiltonian mc2 ⟨wpSpinor mc2 R, wpSpinor_memH1 mc2 R⟩ a))
      (fourierL2 ((wpSpinor mc2 R) a))).congr hae).re
    exact h2.congr (Filter.Eventually.of_forall fun ξ => Complex.ofReal_re _)
  have hbound : (fun ξ => -(diracEnergy mc2 ξ)
        * ‖(fourierL2 ((wpSpinor mc2 R) a) : R3 → ℂ) ξ‖ ^ 2)
      ≤ᵐ[volume] fun ξ => -(2 * Real.pi * (R - 1))
        * ‖(fourierL2 ((wpSpinor mc2 R) a) : R3 → ℂ) ξ‖ ^ 2 := by
    filter_upwards [wpSpinor_fourier mc2 R a] with ξ hfa
    by_cases hξ : ξ ∈ momBall R
    · have hE : 2 * Real.pi * (R - 1) ≤ diracEnergy mc2 ξ :=
        (mul_le_mul_of_nonneg_left (momBall_norm_ge R (by linarith) ξ hξ)
          (by positivity)).trans (diracEnergy_ge mc2 ξ)
      nlinarith [mul_nonneg (sub_nonneg.mpr hE)
        (sq_nonneg ‖(fourierL2 ((wpSpinor mc2 R) a) : R3 → ℂ) ξ‖)]
    · have hz : (fourierL2 ((wpSpinor mc2 R) a) : R3 → ℂ) ξ = 0 := by
        rw [hfa]; simp [wpFn, bumpFn, Set.indicator_of_notMem hξ]
      simp [hz]
  calc ∫ ξ, -(diracEnergy mc2 ξ)
          * ‖(fourierL2 ((wpSpinor mc2 R) a) : R3 → ℂ) ξ‖ ^ 2 ∂volume
      ≤ ∫ ξ, -(2 * Real.pi * (R - 1))
          * ‖(fourierL2 ((wpSpinor mc2 R) a) : R3 → ℂ) ξ‖ ^ 2 ∂volume :=
        integral_mono_ae hcint (hSint.const_mul _) hbound
    _ = -(2 * Real.pi * (R - 1))
          * ∫ ξ, ‖(fourierL2 ((wpSpinor mc2 R) a) : R3 → ℂ) ξ‖ ^ 2 ∂volume := by
        rw [integral_const_mul]
    _ = -(2 * Real.pi * (R - 1)) * ‖(wpSpinor mc2 R) a‖ ^ 2 := by
        rw [← L2_normSq_integral (fourierL2 ((wpSpinor mc2 R) a)),
          LinearIsometryEquiv.norm_map]

/-- **The full energy form is bounded above by `−2π(R−1)·‖ψ‖²`** (sum of the component bounds). -/
lemma wpSpinor_energy_le (mc2 R : ℝ) (hR : 1 < R) :
    (⟪diracHamiltonian mc2 ⟨wpSpinor mc2 R, wpSpinor_memH1 mc2 R⟩, wpSpinor mc2 R⟫_ℂ).re
      ≤ -(2 * Real.pi * (R - 1)) * ‖wpSpinor mc2 R‖ ^ 2 := by
  rw [DiracSpinorL2.inner_eq, Complex.re_sum, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => wpSpinor_energy_component_le mc2 R hR a

/-! ## Step 3 main result: the energy criterion holds, discharging unboundedness -/

/-- **The free Dirac energy form is unbounded below**: for every `N`, the wavepacket at a
sufficiently high momentum gives a state with `Re⟪H_D ψ, ψ⟫ < N·‖ψ‖²`.  This discharges the
hypothesis of `dirac_spectrum_below_of_energy` / `diracHamiltonian_unbounded_below`. -/
theorem dirac_energy_witness (mc2 : ℝ) (N : ℝ) :
    ∃ ψ : (generator (diracUnitaryGroup mc2)).domain,
      (⟪generator (diracUnitaryGroup mc2) ψ, (ψ : DiracSpinorL2)⟫_ℂ).re
        < N * ‖(ψ : DiracSpinorL2)‖ ^ 2 := by
  -- choose the ball far enough out that 2π(R−1) > |N|
  obtain ⟨R, hR1, hRN⟩ : ∃ R : ℝ, 1 < R ∧ |N| < 2 * Real.pi * (R - 1) := by
    refine ⟨2 + |N| / (2 * Real.pi), ?_, ?_⟩
    · have : (0 : ℝ) ≤ |N| / (2 * Real.pi) := by positivity
      linarith
    · have heq : 2 * Real.pi * (2 + |N| / (2 * Real.pi) - 1) = 2 * Real.pi + |N| := by
        field_simp; ring
      rw [heq]; linarith [Real.pi_pos]
  have hmem : wpSpinor mc2 R ∈ (generator (diracUnitaryGroup mc2)).domain := by
    rw [generator_diracUnitaryGroup_domain]; exact wpSpinor_memH1 mc2 R
  refine ⟨⟨wpSpinor mc2 R, hmem⟩, ?_⟩
  have htrans : generator (diracUnitaryGroup mc2) ⟨wpSpinor mc2 R, hmem⟩
      = diracHamiltonian mc2 ⟨wpSpinor mc2 R, wpSpinor_memH1 mc2 R⟩ :=
    (LinearPMap.ext_iff.mp (generator_diracUnitaryGroup mc2)).2
      (hf := hmem) (hg := wpSpinor_memH1 mc2 R)
  change (⟪generator (diracUnitaryGroup mc2) ⟨wpSpinor mc2 R, hmem⟩, wpSpinor mc2 R⟫_ℂ).re
      < N * ‖wpSpinor mc2 R‖ ^ 2
  rw [htrans]
  have hpos : (0 : ℝ) < ‖wpSpinor mc2 R‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (wpSpinor_ne_zero mc2 R hR1)) 2
  have hlt : -(2 * Real.pi * (R - 1)) < N := by linarith [neg_abs_le N]
  calc (⟪diracHamiltonian mc2 ⟨wpSpinor mc2 R, wpSpinor_memH1 mc2 R⟩, wpSpinor mc2 R⟫_ℂ).re
      ≤ -(2 * Real.pi * (R - 1)) * ‖wpSpinor mc2 R‖ ^ 2 := wpSpinor_energy_le mc2 R hR1
    _ < N * ‖wpSpinor mc2 R‖ ^ 2 := mul_lt_mul_of_pos_right hlt hpos

/-! ## Unconditional concrete theorems (Step (b) complete) -/

/-- **The free Dirac operator is unbounded below — unconditional.**

The parameter `κ : DiracConstants` is unused filler required only by the abstract-bundle API of
`diracHamiltonian_unbounded_below`: no field of `κ` appears in the statement or the proof (the
witness `dirac_energy_witness mc2` does not take `κ` at all). The result is universally true over
`κ` — it does not depend on the rest mass, `ℏ`, or `c`. -/
theorem diracHamiltonian_unbounded_below_unconditional (mc2 : ℝ) (κ : DiracConstants) :
    ∀ bound : ℝ, ∃ ψ : (generator (diracUnitaryGroup mc2)).domain,
      (⟪generator (diracUnitaryGroup mc2) ψ, (ψ : DiracSpinorL2)⟫_ℂ).re
        < bound * ‖(ψ : DiracSpinorL2)‖ ^ 2 :=
  diracHamiltonian_unbounded_below mc2 κ (dirac_energy_witness mc2)

/-- **The free Dirac operator is NOT semibounded — unconditional**: the Dirac-sea / antimatter
prediction, for the honest operator on `L²(ℝ³; ℂ⁴)`.

As in `diracHamiltonian_unbounded_below_unconditional`, the parameter `κ : DiracConstants` is
unused filler demanded by the abstract-bundle API: no field of `κ` is inspected, the witness
`dirac_energy_witness mc2` does not take `κ`, and the result holds universally over `κ` —
independently of the rest mass, `ℏ`, or `c`. -/
theorem diracHamiltonian_not_semibounded_unconditional (mc2 : ℝ) (κ : DiracConstants) :
    ¬∃ bound : ℝ, ∀ ψ : (generator (diracUnitaryGroup mc2)).domain,
      bound * ‖(ψ : DiracSpinorL2)‖ ^ 2
        ≤ (⟪generator (diracUnitaryGroup mc2) ψ, (ψ : DiracSpinorL2)⟫_ℂ).re :=
  diracHamiltonian_not_semibounded mc2 κ (dirac_energy_witness mc2)

end Spectra.QuantumMechanics.Dirac
end
