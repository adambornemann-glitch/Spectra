/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.DiracEquation.SpinorSpaceL2
import Spectra.QuantumMechanics.DiracEquation.DiracFourier
import Spectra.Spaces.Sobolev.Submodules
import Spectra.Spaces.Sobolev.IntegrationByParts
import Spectra.Spaces.Sobolev.DensityResults
import Spectra.Operator.KatoRellich
import Spectra.Operator.SelfAdjoint
import Spectra.YosidaHille.Basic
/-!
# The free Dirac operator on `L²(ℝ³; ℂ⁴)`

This file assembles the concrete **free Dirac Hamiltonian** `H_D = c α·p + βmc²` (natural units
`ℏ = c = 1`) as an honest unbounded self-adjoint operator on the spinor Hilbert space
`DiracSpinorL2 = L²(ℝ³; ℂ⁴)`, and connects it to the spectral pipeline (Stone's theorem, the
one-parameter unitary group). It is the relativistic analogue of `Hydrogen/Hamiltonian.lean`.

## Architecture

* The **kinetic operator** `D₀ = -i α·∇` is a first-order matrix-differential operator with
  domain the spinor Sobolev space `H¹(ℝ³; ℂ⁴)` (`SobolevDiracH1`). Its action is built
  componentwise from the scalar `weakGradient`. Its self-adjointness follows from von Neumann's
  surjectivity criterion `isSelfAdjoint_of_surjective_addSub_smul`.
* The **mass term** `mc² β` is bounded and self-adjoint (`matrixOp_massTerm_isSelfAdjoint`).
* The **full Hamiltonian** `H_D = D₀ + mc² β` is then self-adjoint by `kato_rellich_bounded`
  (a bounded self-adjoint perturbation does not change the domain), and Stone's theorem gives the
  evolution `e^{-itH_D}` with generator `H_D`.

Once self-adjoint, `H_D` is the operator on which `Operators.lean`'s abstract spectral hypotheses
(`h_spectrum_below/above`) are discharged. That bridge is built in `ConcreteSpectrum.lean`, which
instantiates the abstract `DiracHamiltonian` with `diracUnitaryGroup` (`diracHamiltonianAbstract`)
and proves `generator (diracHamiltonianAbstract mc2 κ).U_grp = diracHamiltonian mc2`
(`generator_diracHamiltonianAbstract`), so `diracHamiltonian` is consumed directly downstream.

## Implementation notes

This file is sorry-free. The self-adjointness *assembly* (`diracKinetic_isSelfAdjoint`,
`diracHamiltonian_isSelfAdjoint`, the observable / unitary group / generator), the operator and its
action, its linearity (`diracKineticFn_add`/`diracKineticFn_smul`), its symmetry
(`diracKinetic_symmetric`, `diracKineticPMap_isFormalAdjoint`), and the density of its domain
(`diracKineticPMap_domain_dense`) are all complete. The two surjectivity inputs are now proved:

* `diracKinetic_add_smul_surjective` / `diracKinetic_sub_smul_surjective` — surjectivity of
  `D₀ ± iμ`, via Fourier diagonalization: the symbol `D(ξ) = 2π(α·ξ)` is Hermitian
  (`diracMomentumOp_hermitian`) with `D(ξ)² = 4π²|ξ|² I` (`diracMomentumOp_sq`), so
  `(D(ξ) ∓ iμ)/(4π²|ξ|² + μ²)` (`diracResolventSymbol`) is a bounded matrix multiplier inverting
  `D₀ ± iμ`. The construction mirrors the scalar `Hydrogen.laplacian_range_general`: the candidate
  `ψ = 𝓕⁻¹(R·𝓕φ)` lands in `H¹(ℝ³; ℂ⁴)` because the resolvent entries are uniformly bounded
  (Hermiticity + dispersion give `‖D(ξ)_{ab}‖ ≤ √(laplacianSymbol ξ)`).

## Main definitions

* `SobolevDiracH1` — the spinor Sobolev space `H¹(ℝ³; ℂ⁴)`.
* `diracKineticPMap` — the kinetic Dirac operator `-i α·∇`.
* `diracHamiltonian` — the full free Hamiltonian `H_D = -i α·∇ + mc² β`.
* `diracHamiltonianObservable`, `diracUnitaryGroup` — `H_D` as an observable and its evolution.

## Main statements

* `diracKinetic_isSelfAdjoint` — `D₀` is self-adjoint on `H¹(ℝ³; ℂ⁴)`.
* `diracHamiltonian_isSelfAdjoint` — `H_D` is self-adjoint (Kato–Rellich, bounded mass term).
* `generator_diracUnitaryGroup` — the generator of `e^{-itH_D}` is `H_D`.
* *Auxiliary* (the Fourier-symbol machinery inverting `D₀ ± iμ`):
  `diracKineticSymbol_entry_normSq_le` bounds each kinetic-symbol entry by `laplacianSymbol ξ`;
  `diracResolventSymbol_apply` expands the resolvent multiplier entrywise; and
  `norm_diracResolventSymbol_entry_le` gives the uniform bound `‖R(ξ)_{ab}‖ ≤ 3/(2|μ|)` that lands
  the resolvent solution in `L²`.

## References

* [Thaller, *The Dirac Equation*][thaller1992], Chapter 1
* [Reed, Simon, *Methods of Modern Mathematical Physics IV*][reed1978], §X.4

## Tags

Dirac equation, free Dirac operator, self-adjoint, unbounded operator, Stone's theorem
-/
open MeasureTheory InnerProductSpace
open scoped InnerProductSpace
open Spectra.Sobolev
open Spectra.Operator
open Spectra.OneParameterUnitaryGroup
open Spectra.YosidaHille

noncomputable section
namespace Spectra.QuantumMechanics.Dirac

/-! ## The spinor Sobolev space `H¹(ℝ³; ℂ⁴)` -/

/-- Uniform access to the velocity matrices: `diracAlphaMat 0 = α¹`, etc. -/
def diracAlphaMat : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ
  | 0 => diracAlpha1
  | 1 => diracAlpha2
  | 2 => diracAlpha3

/-- Each velocity matrix is Hermitian, in index form: `conj (αᵏ)_{ab} = (αᵏ)_{ba}`. -/
lemma diracAlphaMat_conj (k : Fin 3) (a b : Fin 4) :
    (starRingEnd ℂ) (diracAlphaMat k a b) = diracAlphaMat k b a := by
  have h : (diracAlphaMat k).conjTranspose = diracAlphaMat k := by
    fin_cases k
    · exact diracAlpha1_hermitian
    · exact diracAlpha2_hermitian
    · exact diracAlpha3_hermitian
  rw [starRingEnd_apply, ← Matrix.conjTranspose_apply, h]

/-- A spinor field is in `H¹` iff each of its four components is in the scalar `H¹(ℝ³)`. -/
def MemSobolevDiracH1 (ψ : DiracSpinorL2) : Prop :=
  ∀ a : Fin 4, MemSobolevH1 (ψ a)

/-- The spinor Sobolev space `H¹(ℝ³; ℂ⁴)` as a `ℂ`-submodule of `L²(ℝ³; ℂ⁴)`; the domain of the
free Dirac operator. Closure is componentwise from the scalar `SobolevH1`. -/
def SobolevDiracH1 : Submodule ℂ DiracSpinorL2 where
  carrier := { ψ | MemSobolevDiracH1 ψ }
  zero_mem' := fun _ => SobolevH1.zero_mem
  add_mem' := fun hx hy a => SobolevH1.add_mem (hx a) (hy a)
  smul_mem' := fun c _ hx a => SobolevH1.smul_mem c (hx a)

/-! ## The kinetic Dirac operator `D₀ = -i α·∇` -/

/-- The pointwise action of the kinetic Dirac operator `-i α·∇` on an `H¹` spinor:
`(D₀ ψ)_a = -i Σ_k Σ_b (αᵏ)_{ab} ∂_k ψ_b`, built from the scalar `weakGradient`. -/
def diracKineticFn (ψ : DiracSpinorL2) (hψ : MemSobolevDiracH1 ψ) : DiracSpinorL2 :=
  diracSpinorCLE.symm fun a => -Complex.I •
    ∑ k : Fin 3, ∑ b : Fin 4, diracAlphaMat k a b • weakGradient (ψ b) (hψ b) k

@[simp] lemma diracKineticFn_apply (ψ : DiracSpinorL2) (hψ : MemSobolevDiracH1 ψ) (a : Fin 4) :
    diracKineticFn ψ hψ a
      = -Complex.I • ∑ k : Fin 3, ∑ b : Fin 4, diracAlphaMat k a b • weakGradient (ψ b) (hψ b) k :=
  rfl

/-- Additivity of the kinetic action: `D₀(ψ + φ) = D₀ψ + D₀φ`. The componentwise weak gradients
add by uniqueness of the weak derivative (`hasWeakDerivative_unique` against
`hasWeakDerivative_add`), and the matrix/sum/scalar structure distributes. -/
lemma diracKineticFn_add (f g : DiracSpinorL2)
    (hf : MemSobolevDiracH1 f) (hg : MemSobolevDiracH1 g) (hfg : MemSobolevDiracH1 (f + g)) :
    diracKineticFn (f + g) hfg = diracKineticFn f hf + diracKineticFn g hg := by
  have key : ∀ (k : Fin 3) (b : Fin 4),
      weakGradient ((f + g) b) (hfg b) k
        = weakGradient (f b) (hf b) k + weakGradient (g b) (hg b) k := fun k b =>
    hasWeakDerivative_unique ((f + g) b) k _ _ (weakGradient_spec ((f + g) b) (hfg b) k)
      (hasWeakDerivative_add (f b) (g b) k _ _
        (weakGradient_spec (f b) (hf b) k) (weakGradient_spec (g b) (hg b) k))
  unfold diracKineticFn
  rw [← map_add]
  congr 1
  funext a
  simp only [Pi.add_apply, key, smul_add, Finset.sum_add_distrib]

/-- Homogeneity of the kinetic action: `D₀(c • ψ) = c • D₀ψ`. -/
lemma diracKineticFn_smul (c : ℂ) (f : DiracSpinorL2)
    (hf : MemSobolevDiracH1 f) (hcf : MemSobolevDiracH1 (c • f)) :
    diracKineticFn (c • f) hcf = c • diracKineticFn f hf := by
  have key : ∀ (k : Fin 3) (b : Fin 4),
      weakGradient ((c • f) b) (hcf b) k = c • weakGradient (f b) (hf b) k := fun k b =>
    hasWeakDerivative_unique ((c • f) b) k _ _ (weakGradient_spec ((c • f) b) (hcf b) k)
      (hasWeakDerivative_smul c (f b) k _ (weakGradient_spec (f b) (hf b) k))
  unfold diracKineticFn
  rw [← map_smul]
  congr 1
  funext a
  simp only [Pi.smul_apply, key, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  ring

/-- The kinetic Dirac operator as a linear map on the `H¹` domain. -/
def diracKineticLM : SobolevDiracH1 →ₗ[ℂ] DiracSpinorL2 where
  toFun := fun ψ => diracKineticFn ψ.1 ψ.2
  map_add' := fun x y => diracKineticFn_add x.1 y.1 x.2 y.2 (x + y).2
  map_smul' := fun c x => diracKineticFn_smul c x.1 x.2 (c • x).2

/-- The **kinetic Dirac operator** `D₀ = -i α·∇` as an unbounded operator on `L²(ℝ³; ℂ⁴)`,
with domain `H¹(ℝ³; ℂ⁴)`. -/
def diracKineticPMap : DiracSpinorL2 →ₗ.[ℂ] DiracSpinorL2 where
  domain := SobolevDiracH1
  toFun := diracKineticLM

@[simp] theorem diracKineticPMap_domain : diracKineticPMap.domain = SobolevDiracH1 := rfl

theorem diracKineticPMap_apply (ψ : SobolevDiracH1) :
    diracKineticPMap ψ = diracKineticFn ψ.1 ψ.2 := rfl

/-! ## Self-adjointness of the kinetic operator

Density and symmetry are proved above; surjectivity of `D₀ ± iμ` is established below by Fourier
diagonalisation, and the assembly via von Neumann's criterion is complete. -/

/-- Scalar `H¹(ℝ³)` is dense in `L²(ℝ³)` (it contains the dense `H²`). -/
theorem sobolevH1_dense : Dense (SobolevH1 (d := 3) : Set l2R3) :=
  sobolevH2_dense.mono fun _ hx => sobolevH2_le_sobolevH1 hx

/-- The domain `H¹(ℝ³; ℂ⁴)` is dense in `L²(ℝ³; ℂ⁴)`. Componentwise density of `H¹` in `L²`
(`sobolevH1_dense`) gives density of the product, transported through the `diracSpinorCLE`
homeomorphism between the `ℓ²`-model and the plain product. -/
theorem diracKineticPMap_domain_dense :
    Dense (diracKineticPMap.domain : Set DiracSpinorL2) := by
  have hpi : Dense (Set.univ.pi fun _ : Fin 4 => (SobolevH1 (d := 3) : Set l2R3)) :=
    dense_pi Set.univ fun _ _ => sobolevH1_dense
  have hset : (diracKineticPMap.domain : Set DiracSpinorL2)
      = ⇑diracSpinorCLE.toHomeomorph ⁻¹' (Set.univ.pi fun _ : Fin 4 =>
      (SobolevH1 (d := 3) : Set l2R3)) := by
    ext ψ
    simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    exact Iff.rfl
  rw [hset]
  exact hpi.preimage diracSpinorCLE.toHomeomorph.isOpenMap

/-- **Symmetry of the kinetic Dirac operator**: `⟪D₀ψ, φ⟫ = ⟪ψ, D₀φ⟫` for `ψ, φ ∈ H¹(ℝ³; ℂ⁴)`.
The momentum part `-i∂ₖ` is skew-symmetric by integration by parts (`weakGradient_inner_skew`); the
factor `i` together with Hermiticity of the velocity matrices (`diracAlphaMat_conj`) makes the
combination symmetric. The final step relabels the spinor indices `a ↔ b`. -/
lemma diracKinetic_symmetric (ψ φ : DiracSpinorL2)
    (hψ : MemSobolevDiracH1 ψ) (hφ : MemSobolevDiracH1 φ) :
    ⟪diracKineticFn ψ hψ, φ⟫_ℂ = ⟪ψ, diracKineticFn φ hφ⟫_ℂ := by
  rw [DiracSpinorL2.inner_eq, DiracSpinorL2.inner_eq]
  have skew : ∀ (b a : Fin 4) (k : Fin 3),
      ⟪weakGradient (ψ b) (hψ b) k, φ a⟫_ℂ = -⟪ψ b, weakGradient (φ a) (hφ a) k⟫_ℂ :=
    fun b a k => weakGradient_inner_skew (ψ b) (φ a) (hψ b) (hφ a) k
  have hR : ∀ a, ⟪ψ a, diracKineticFn φ hφ a⟫_ℂ
      = ∑ k, ∑ b, -Complex.I * diracAlphaMat k a b * ⟪ψ a, weakGradient (φ b) (hφ b) k⟫_ℂ := by
    intro a
    rw [diracKineticFn_apply, inner_smul_right, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [inner_smul_right]; ring
  have hL : ∀ a, ⟪diracKineticFn ψ hψ a, φ a⟫_ℂ
      = ∑ k, ∑ b, -Complex.I * diracAlphaMat k b a * ⟪ψ b, weakGradient (φ a) (hφ a) k⟫_ℂ := by
    intro a
    rw [diracKineticFn_apply, inner_smul_left, sum_inner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_inner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [inner_smul_left, skew b a k, diracAlphaMat_conj]
    simp only [map_neg, Complex.conj_I, neg_neg]
    ring
  simp only [hL, hR]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]

/-- Symmetry of the kinetic operator as a formal adjoint statement. -/
theorem diracKineticPMap_isFormalAdjoint :
    diracKineticPMap.IsFormalAdjoint diracKineticPMap :=
  fun ψ φ => diracKinetic_symmetric ψ.1 φ.1 ψ.2 φ.2

/-- **Fourier diagonalisation of the kinetic operator**: `𝓕(D₀ψ)ₐ = D(ξ)·(𝓕ψ)`, componentwise
`𝓕(D₀ψ)ₐ(ξ) = Σₖ Σ_b (-i (αᵏ)_{ab}) · derivSymbol k ξ · 𝓕(ψ_b)(ξ)` a.e. Each weak gradient
Fourier-transforms by `fourier_weakGradient`, and `fourierL2` is linear. -/
lemma fourier_diracKineticFn (ψ : DiracSpinorL2) (hψ : MemSobolevDiracH1 ψ) (a : Fin 4) :
    (fourierL2 (diracKineticFn ψ hψ a) : R3 → ℂ) =ᵐ[volume]
      fun ξ => ∑ k : Fin 3, ∑ b : Fin 4, (-Complex.I * diracAlphaMat k a b) *
        (derivSymbol k ξ * (fourierL2 (ψ b) : R3 → ℂ) ξ) := by
  have hel : fourierL2 (diracKineticFn ψ hψ a)
      = ∑ k : Fin 3, ∑ b : Fin 4,
          (-Complex.I * diracAlphaMat k a b) • fourierL2 (weakGradient (ψ b) (hψ b) k) := by
    rw [diracKineticFn_apply]
    simp only [map_smul, map_sum, Finset.smul_sum, smul_smul]
  rw [hel]
  exact l2_coeFn_sum Finset.univ
    (fun k => ∑ b : Fin 4,
      (-Complex.I * diracAlphaMat k a b) • fourierL2 (weakGradient (ψ b) (hψ b) k))
    (fun k ξ => ∑ b : Fin 4, (-Complex.I * diracAlphaMat k a b) *
      (derivSymbol k ξ * (fourierL2 (ψ b) : R3 → ℂ) ξ))
    (fun k _ => l2_coeFn_sum_smul Finset.univ (fun b => -Complex.I * diracAlphaMat k a b)
      (fun b => fourierL2 (weakGradient (ψ b) (hψ b) k))
      (fun b ξ => derivSymbol k ξ * (fourierL2 (ψ b) : R3 → ℂ) ξ)
      (fun b _ => fourier_weakGradient (ψ b) (hψ b) k))

/-! ### Symbol form of the kinetic diagonalisation and uniform multiplier bounds

The remaining analytic inputs for inverting `D₀ ± iμ`: the kinetic operator becomes
multiplication by the Hermitian matrix symbol `D(ξ)` (`fourier_diracKineticFn_symbol`), whose
entries are bounded by `√(laplacianSymbol ξ) = 2π‖ξ‖` (`norm_diracKineticSymbol_entry_le`), so the
resolvent multiplier `diracResolventSymbol` has uniformly bounded entries. These are exactly the
ingredients `memLp_two_boundedMul` and `memSobolevH1_of_fourier_decay` need. -/

/-- **The kinetic symbol entries are controlled by the Laplacian symbol**:
`‖D(ξ)_{ab}‖² ≤ laplacianSymbol ξ`. Since `D(ξ)` is Hermitian with `D(ξ)² = laplacianSymbol ξ · I`,
the `(a,a)` entry of `D(ξ)²` is `Σ_c ‖D(ξ)_{ac}‖² = laplacianSymbol ξ`, and a single term is bounded
by the sum. -/
lemma diracKineticSymbol_entry_normSq_le (ξ : R3) (a b : Fin 4) :
    ‖diracKineticSymbol ξ a b‖ ^ 2 ≤ laplacianSymbol ξ := by
  -- `(a,a)` entry of `D(ξ)² = laplacianSymbol ξ • 1`
  have hentry : ∑ c, diracKineticSymbol ξ a c * diracKineticSymbol ξ c a
      = (laplacianSymbol ξ : ℂ) := by
    have h := congrFun (congrFun (diracKineticSymbol_sq ξ) a) a
    rwa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
  -- hermiticity: `D(ξ)_{ca} = conj (D(ξ)_{ac})`
  have hherm : ∀ c, diracKineticSymbol ξ c a = (starRingEnd ℂ) (diracKineticSymbol ξ a c) := by
    intro c
    have h := congrFun (congrFun (diracKineticSymbol_hermitian ξ) a) c
    rw [Matrix.conjTranspose_apply] at h
    rw [← h, starRingEnd_apply, star_star]
  -- the diagonal sum is `Σ_c ‖D(ξ)_{ac}‖²`
  have hsumC : (∑ c, (‖diracKineticSymbol ξ a c‖ : ℂ) ^ 2) = (laplacianSymbol ξ : ℂ) := by
    rw [← hentry]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hherm c]
    exact (RCLike.mul_conj (diracKineticSymbol ξ a c)).symm
  have hsum : (∑ c, (‖diracKineticSymbol ξ a c‖ ^ 2 : ℝ)) = laplacianSymbol ξ := by
    exact_mod_cast hsumC
  calc ‖diracKineticSymbol ξ a b‖ ^ 2
      ≤ ∑ c, ‖diracKineticSymbol ξ a c‖ ^ 2 :=
        Finset.single_le_sum (f := fun c => ‖diracKineticSymbol ξ a c‖ ^ 2)
          (fun c _ => sq_nonneg _) (Finset.mem_univ b)
    _ = laplacianSymbol ξ := hsum

/-- `√(laplacianSymbol ξ) = 2π‖ξ‖`. -/
lemma sqrt_laplacianSymbol (ξ : R3) : Real.sqrt (laplacianSymbol ξ) = 2 * Real.pi * ‖ξ‖ := by
  rw [laplacianSymbol, show (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 = (2 * Real.pi * ‖ξ‖) ^ 2 from by ring,
    Real.sqrt_sq (by positivity)]

/-- Each kinetic symbol entry is bounded by `2π‖ξ‖`. -/
lemma norm_diracKineticSymbol_entry_le (ξ : R3) (a b : Fin 4) :
    ‖diracKineticSymbol ξ a b‖ ≤ 2 * Real.pi * ‖ξ‖ := by
  rw [← sqrt_laplacianSymbol, ← Real.sqrt_sq (norm_nonneg (diracKineticSymbol ξ a b))]
  exact Real.sqrt_le_sqrt (diracKineticSymbol_entry_normSq_le ξ a b)

/-- The first-derivative symbol is bounded by `2π‖ξ‖` (as in `Hydrogen/Laplacian.lean`). -/
lemma norm_derivSymbol_le (k : Fin 3) (ξ : R3) : ‖derivSymbol k ξ‖ ≤ 2 * Real.pi * ‖ξ‖ := by
  have hi : |(inner ℝ ξ (EuclideanSpace.single k (1 : ℝ)) : ℝ)| ≤ ‖ξ‖ := by
    simpa using abs_real_inner_le_norm ξ (EuclideanSpace.single k (1 : ℝ))
  have hnorm : ‖derivSymbol k ξ‖
      = 2 * Real.pi * |(inner ℝ ξ (EuclideanSpace.single k (1 : ℝ)) : ℝ)| := by
    simp only [derivSymbol, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
      Real.norm_eq_abs, mul_one, abs_of_pos Real.pi_pos]
  rw [hnorm]
  nlinarith [Real.pi_pos, abs_nonneg (inner ℝ ξ (EuclideanSpace.single k (1 : ℝ)) : ℝ), hi]

/-- **The kinetic symbol entry as a sum of derivative symbols**:
`D(ξ)_{ab} = Σₖ (-i (αᵏ)_{ab}) · derivSymbol k ξ`. The key algebraic identity letting us read the
raw Fourier diagonalisation `fourier_diracKineticFn` as multiplication by `D(ξ)`. -/
lemma diracKineticSymbol_apply_eq (ξ : R3) (a b : Fin 4) :
    diracKineticSymbol ξ a b
      = ∑ k : Fin 3, (-Complex.I * diracAlphaMat k a b) * derivSymbol k ξ := by
  have hinner : ∀ k : Fin 3,
      ((inner ℝ ξ (EuclideanSpace.single k (1 : ℝ)) : ℝ) : ℂ) = (ξ k : ℂ) := by
    intro k; rw [EuclideanSpace.inner_single_right]; simp
  have hterm : ∀ k : Fin 3, (-Complex.I * diracAlphaMat k a b) * derivSymbol k ξ
      = ((2 * Real.pi : ℝ) : ℂ) * (ξ k : ℂ) * diracAlphaMat k a b := by
    intro k
    rw [derivSymbol, hinner]
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    push_cast
    linear_combination (-(2 * (Real.pi : ℂ)) * (ξ k : ℂ) * diracAlphaMat k a b) * hI
  simp only [hterm]
  rw [diracKineticSymbol, diracMomentumOp]
  simp only [Fin.sum_univ_three, diracAlphaMat, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  push_cast
  ring

/-- **Symbol form of the kinetic Fourier diagonalisation**:
`𝓕(D₀ψ)ₐ(ξ) = Σ_b D(ξ)_{ab} · 𝓕(ψ_b)(ξ)` a.e. Folds the `k`-sum of `fourier_diracKineticFn` into
the matrix symbol via `diracKineticSymbol_apply_eq`. -/
lemma fourier_diracKineticFn_symbol (ψ : DiracSpinorL2) (hψ : MemSobolevDiracH1 ψ) (a : Fin 4) :
    (fourierL2 (diracKineticFn ψ hψ a) : R3 → ℂ) =ᵐ[volume]
      fun ξ => ∑ b : Fin 4, diracKineticSymbol ξ a b * (fourierL2 (ψ b) : R3 → ℂ) ξ := by
  filter_upwards [fourier_diracKineticFn ψ hψ a] with ξ hξ
  rw [hξ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [diracKineticSymbol_apply_eq, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Entrywise expansion of the resolvent symbol, used for measurability and bounds. -/
lemma diracResolventSymbol_apply (μ : ℝ) (ξ : R3) (a b : Fin 4) :
    diracResolventSymbol μ ξ a b
      = ((laplacianSymbol ξ + μ ^ 2 : ℝ) : ℂ)⁻¹
        * (diracKineticSymbol ξ a b
            - (Complex.I * (μ : ℂ)) * (1 : Matrix (Fin 4) (Fin 4) ℂ) a b) := by
  simp only [diracResolventSymbol, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]

/-- Each resolvent symbol entry is a (continuous, hence) a.e.-strongly-measurable function of `ξ`.
-/
lemma aestronglyMeasurable_diracResolventSymbol_entry (μ : ℝ) (hμ : μ ≠ 0) (a b : Fin 4) :
    AEStronglyMeasurable (fun ξ : R3 => diracResolventSymbol μ ξ a b) volume := by
  apply Continuous.aestronglyMeasurable
  simp only [diracResolventSymbol_apply]
  have hden : Continuous (fun ξ : R3 => ((laplacianSymbol ξ + μ ^ 2 : ℝ) : ℂ)) := by
    unfold laplacianSymbol; fun_prop
  have hne : ∀ ξ : R3, ((laplacianSymbol ξ + μ ^ 2 : ℝ) : ℂ) ≠ 0 := fun ξ => by
    exact_mod_cast (laplacianSymbol_add_sq_pos μ hμ ξ).ne'
  have hDc : Continuous (fun ξ : R3 => diracKineticSymbol ξ a b) := by
    simp only [diracKineticSymbol_apply_eq]
    refine continuous_finsetSum _ fun k _ => continuous_const.mul ?_
    unfold derivSymbol; fun_prop
  exact (hden.inv₀ hne).mul (hDc.sub continuous_const)

/-- Auxiliary explicit bound on a resolvent entry: `‖R(ξ)_{ab}‖ ≤ (s + μ²)⁻¹ (√s + |μ|)` where
`s = laplacianSymbol ξ`. The numerator splits as `‖D(ξ)_{ab}‖ + |μ| ≤ √s + |μ|`. -/
lemma norm_diracResolventSymbol_entry_le_aux (μ : ℝ) (ξ : R3) (a b : Fin 4) :
    ‖diracResolventSymbol μ ξ a b‖
      ≤ (laplacianSymbol ξ + μ ^ 2)⁻¹ * (Real.sqrt (laplacianSymbol ξ) + |μ|) := by
  have hden_nonneg : 0 ≤ laplacianSymbol ξ + μ ^ 2 := by
    have := laplacianSymbol_nonneg ξ; positivity
  have h1ab : ‖(1 : Matrix (Fin 4) (Fin 4) ℂ) a b‖ ≤ 1 := by
    rcases eq_or_ne a b with h | h
    · rw [h, Matrix.one_apply_eq]; simp
    · rw [Matrix.one_apply_ne h]; simp
  rw [diracResolventSymbol_apply, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hden_nonneg]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sub_le _ _).trans ?_
  gcongr
  · rw [sqrt_laplacianSymbol]; exact norm_diracKineticSymbol_entry_le ξ a b
  · calc ‖Complex.I * (μ : ℂ) * (1 : Matrix (Fin 4) (Fin 4) ℂ) a b‖
        = |μ| * ‖(1 : Matrix (Fin 4) (Fin 4) ℂ) a b‖ := by
          rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
      _ ≤ |μ| * 1 := by gcongr
      _ = |μ| := mul_one _

/-- **Uniform bound on the resolvent symbol entries**: `‖R(ξ)_{ab}‖ ≤ 3 / (2|μ|)` for all `ξ`. -/
lemma norm_diracResolventSymbol_entry_le (μ : ℝ) (hμ : μ ≠ 0) (ξ : R3) (a b : Fin 4) :
    ‖diracResolventSymbol μ ξ a b‖ ≤ 3 / (2 * |μ|) := by
  refine (norm_diracResolventSymbol_entry_le_aux μ ξ a b).trans ?_
  have hs0 : 0 ≤ laplacianSymbol ξ := laplacianSymbol_nonneg ξ
  have hden_pos : 0 < laplacianSymbol ξ + μ ^ 2 := laplacianSymbol_add_sq_pos μ hμ ξ
  have hm : 0 < |μ| := abs_pos.mpr hμ
  have ht2 : Real.sqrt (laplacianSymbol ξ) ^ 2 = laplacianSymbol ξ := Real.sq_sqrt hs0
  rw [← div_eq_inv_mul, div_le_div_iff₀ hden_pos (by positivity : (0 : ℝ) < 2 * |μ|)]
  nlinarith [ht2, sq_abs μ, sq_nonneg (Real.sqrt (laplacianSymbol ξ) - |μ|),
    sq_nonneg (Real.sqrt (laplacianSymbol ξ)), hm, Real.sqrt_nonneg (laplacianSymbol ξ)]

/-- **Uniform bound on the `H¹`-weighted resolvent entries**:
`‖derivSymbol k ξ · R(ξ)_{ab}‖ ≤ 3/2`. This is what lands the resolvent solution in `H¹`. -/
lemma norm_derivSymbol_mul_diracResolventSymbol_entry_le
    (μ : ℝ) (hμ : μ ≠ 0) (k : Fin 3) (ξ : R3) (a b : Fin 4) :
    ‖derivSymbol k ξ * diracResolventSymbol μ ξ a b‖ ≤ 3 / 2 := by
  have hs0 : 0 ≤ laplacianSymbol ξ := laplacianSymbol_nonneg ξ
  have hden_pos : 0 < laplacianSymbol ξ + μ ^ 2 := laplacianSymbol_add_sq_pos μ hμ ξ
  have hm : 0 < |μ| := abs_pos.mpr hμ
  have ht2 : Real.sqrt (laplacianSymbol ξ) ^ 2 = laplacianSymbol ξ := Real.sq_sqrt hs0
  have hd : ‖derivSymbol k ξ‖ ≤ Real.sqrt (laplacianSymbol ξ) := by
    rw [sqrt_laplacianSymbol]; exact norm_derivSymbol_le k ξ
  rw [norm_mul]
  refine (mul_le_mul hd (norm_diracResolventSymbol_entry_le_aux μ ξ a b)
    (norm_nonneg _) (Real.sqrt_nonneg _)).trans ?_
  rw [show Real.sqrt (laplacianSymbol ξ)
        * ((laplacianSymbol ξ + μ ^ 2)⁻¹ * (Real.sqrt (laplacianSymbol ξ) + |μ|))
      = (Real.sqrt (laplacianSymbol ξ) * (Real.sqrt (laplacianSymbol ξ) + |μ|))
        / (laplacianSymbol ξ + μ ^ 2) from by rw [div_eq_mul_inv]; ring,
    div_le_iff₀ hden_pos]
  nlinarith [ht2, sq_abs μ, sq_nonneg (Real.sqrt (laplacianSymbol ξ) - |μ|),
    sq_nonneg (Real.sqrt (laplacianSymbol ξ)), hm, Real.sqrt_nonneg (laplacianSymbol ξ)]

/-- **Surjectivity of `D₀ + iμ`** (`μ ≠ 0`), via Fourier diagonalisation. The candidate solution is
`ψ = 𝓕⁻¹(R(ξ)·𝓕φ)` with the bounded matrix multiplier `R = diracResolventSymbol`; it lands in
`H¹(ℝ³; ℂ⁴)` by the first-order Fourier-decay criterion, and `(D(ξ) + iμ)·R(ξ) = 1`
(`diracResolventSymbol_add_inverse`) gives the equation back on the Fourier side. This is the spinor
analogue of `Hydrogen.laplacian_range_general`. -/
theorem diracKinetic_add_smul_surjective (μ : ℝ) (hμ : μ ≠ 0) (φ : DiracSpinorL2) :
    ∃ ψ : diracKineticPMap.domain,
      diracKineticPMap ψ + (Complex.I * (μ : ℂ)) • (ψ : DiracSpinorL2) = φ := by
  -- componentwise Fourier transform of the candidate solution: `𝓕ψ_a = R(ξ)·𝓕φ`
  set ĝ : Fin 4 → R3 → ℂ := fun a ξ =>
    ∑ b : Fin 4, diracResolventSymbol μ ξ a b * (fourierL2 (φ b) : R3 → ℂ) ξ with hĝ
  -- each component is `L²`: a finite sum of bounded multipliers of `L²` data
  have hmem : ∀ a, MemLp (ĝ a) 2 volume := by
    intro a
    have hrw : ĝ a
        = ∑ b : Fin 4, fun ξ => diracResolventSymbol μ ξ a b * (fourierL2 (φ b) : R3 → ℂ) ξ := by
      funext ξ; simp only [hĝ, Finset.sum_apply]
    rw [hrw]
    refine memLp_finsetSum' _ fun b _ => ?_
    exact memLp_two_boundedMul (aestronglyMeasurable_diracResolventSymbol_entry μ hμ a b)
      (Filter.Eventually.of_forall fun ξ => norm_diracResolventSymbol_entry_le μ hμ ξ a b)
      (fourierL2 (φ b))
  -- the solution `ψ = 𝓕⁻¹ (R·𝓕φ)`
  set ψ : DiracSpinorL2 := diracSpinorCLE.symm (fun a => fourierL2.symm ((hmem a).toLp (ĝ a)))
    with _hψdef
  have hFψ : ∀ a, (fourierL2 (ψ a) : R3 → ℂ) =ᵐ[volume] ĝ a := by
    intro a
    change (fourierL2 (fourierL2.symm ((hmem a).toLp (ĝ a))) : R3 → ℂ) =ᵐ[volume] ĝ a
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact (hmem a).coeFn_toLp
  -- `ψ ∈ H¹(ℝ³; ℂ⁴)` componentwise, via the first-order Fourier-decay criterion
  have hψmem : MemSobolevDiracH1 ψ := by
    intro a
    apply memSobolevH1_of_fourier_decay
    intro k
    have hbase : MemLp (∑ b : Fin 4, fun ξ =>
        (derivSymbol k ξ * diracResolventSymbol μ ξ a b) * (fourierL2 (φ b) : R3 → ℂ) ξ)
        2 volume := by
      refine memLp_finsetSum' _ fun b _ => ?_
      exact memLp_two_boundedMul
        (((by unfold derivSymbol; fun_prop : Continuous (derivSymbol k)).aestronglyMeasurable).mul
          (aestronglyMeasurable_diracResolventSymbol_entry μ hμ a b))
        (Filter.Eventually.of_forall fun ξ =>
          norm_derivSymbol_mul_diracResolventSymbol_entry_le μ hμ k ξ a b)
        (fourierL2 (φ b))
    refine hbase.ae_eq ?_
    filter_upwards [hFψ a] with ξ hξ
    simp only [Finset.sum_apply, hξ, hĝ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  -- the equation, checked componentwise on the Fourier side
  refine ⟨⟨ψ, hψmem⟩, ?_⟩
  change diracKineticFn ψ hψmem + (Complex.I * (μ : ℂ)) • ψ = φ
  refine PiLp.ext fun a => ?_
  simp only [PiLp.add_apply, PiLp.smul_apply]
  apply fourierL2.injective
  rw [map_add, map_smul]
  apply L2_ext
  have hae : ∀ᵐ ξ ∂(volume : Measure R3), ∀ c, (fourierL2 (ψ c) : R3 → ℂ) ξ = ĝ c ξ :=
    ae_all_iff.2 hFψ
  filter_upwards [Lp.coeFn_add (fourierL2 (diracKineticFn ψ hψmem a))
      ((Complex.I * (μ : ℂ)) • fourierL2 (ψ a)),
    Lp.coeFn_smul (Complex.I * (μ : ℂ)) (fourierL2 (ψ a)),
    fourier_diracKineticFn_symbol ψ hψmem a, hae] with ξ hadd hsmul hsym haeξ
  rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, hsym, smul_eq_mul]
  simp only [haeξ, hĝ]
  -- contraction: `∑_b D_ab (∑_d R_bd 𝓕φ_d) + iμ ∑_d R_ad 𝓕φ_d = ((D + iμ)·R)_a · 𝓕φ = 𝓕φ_a`
  have hL : (∑ b, diracKineticSymbol ξ a b
        * (∑ d, diracResolventSymbol μ ξ b d * (fourierL2 (φ d) : R3 → ℂ) ξ))
      = ∑ d, (∑ b, diracKineticSymbol ξ a b * diracResolventSymbol μ ξ b d)
          * (fourierL2 (φ d) : R3 → ℂ) ξ := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hstep : ∀ d, (∑ b, diracKineticSymbol ξ a b * diracResolventSymbol μ ξ b d)
        * (fourierL2 (φ d) : R3 → ℂ) ξ
      + Complex.I * (μ : ℂ) * (diracResolventSymbol μ ξ a d * (fourierL2 (φ d) : R3 → ℂ) ξ)
      = ((diracKineticSymbol ξ + (Complex.I * (μ : ℂ)) • 1) * diracResolventSymbol μ ξ) a d
          * (fourierL2 (φ d) : R3 → ℂ) ξ := by
    intro d
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply,
      Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hL, Finset.mul_sum, ← Finset.sum_add_distrib]
  simp only [hstep, diracResolventSymbol_add_inverse μ hμ ξ]
  simp [Matrix.one_apply, Finset.sum_ite_eq]

/-- **Surjectivity of `D₀ - iμ`** (`μ ≠ 0`); reduces to `diracKinetic_add_smul_surjective` at `-μ`,
since `D₀ - iμ = D₀ + i(-μ)`. -/
theorem diracKinetic_sub_smul_surjective (μ : ℝ) (hμ : μ ≠ 0) (φ : DiracSpinorL2) :
    ∃ ψ : diracKineticPMap.domain,
      diracKineticPMap ψ - (Complex.I * (μ : ℂ)) • (ψ : DiracSpinorL2) = φ := by
  obtain ⟨ψ, hψ⟩ := diracKinetic_add_smul_surjective (-μ) (neg_ne_zero.mpr hμ) φ
  refine ⟨ψ, ?_⟩
  have hcast : Complex.I * ((-μ : ℝ) : ℂ) = -(Complex.I * (μ : ℂ)) := by push_cast; ring
  rw [sub_eq_add_neg, ← neg_smul, ← hcast]
  exact hψ

/-- **The kinetic Dirac operator `D₀ = -i α·∇` is self-adjoint** on `H¹(ℝ³; ℂ⁴)`.
Assembled from symmetry + density + surjectivity of `D₀ ± i` via von Neumann's criterion. -/
theorem diracKinetic_isSelfAdjoint : IsSelfAdjoint diracKineticPMap :=
  isSelfAdjoint_of_surjective_addSub_smul diracKineticPMap
    diracKineticPMap_isFormalAdjoint diracKineticPMap_domain_dense (1 : ℝ)
    (fun φ => diracKinetic_add_smul_surjective 1 one_ne_zero φ)
    (fun φ => diracKinetic_sub_smul_surjective 1 one_ne_zero φ)

/-! ## The full free Dirac Hamiltonian `H_D = D₀ + mc² β` -/

/-- The **free Dirac Hamiltonian** `H_D = -i α·∇ + mc² β` as an unbounded operator on
`L²(ℝ³; ℂ⁴)`, with domain `H¹(ℝ³; ℂ⁴)`. The mass term is the bounded operator `matrixOp (mc² β)`
restricted to the kinetic domain. -/
def diracHamiltonian (mc2 : ℝ) : DiracSpinorL2 →ₗ.[ℂ] DiracSpinorL2 :=
  perturbedOp diracKineticPMap
    ((matrixOp ((mc2 : ℂ) • diracBeta)).comp
      (Submodule.subtypeL diracKineticPMap.domain)).toLinearMap

@[simp] theorem diracHamiltonian_domain (mc2 : ℝ) :
    (diracHamiltonian mc2).domain = SobolevDiracH1 := rfl

/-- **The free Dirac Hamiltonian is self-adjoint** on `H¹(ℝ³; ℂ⁴)`: a bounded self-adjoint mass
perturbation of the self-adjoint kinetic operator (Kato–Rellich). -/
theorem diracHamiltonian_isSelfAdjoint (mc2 : ℝ) : IsSelfAdjoint (diracHamiltonian mc2) :=
  kato_rellich_bounded diracKinetic_isSelfAdjoint (matrixOp_massTerm_isSelfAdjoint mc2)

/-- The free Dirac Hamiltonian bundled as a `SelfAdjointOperator`. -/
def diracHamiltonianObservable (mc2 : ℝ) : SelfAdjointOperator DiracSpinorL2 where
  toLinearPMap := diracHamiltonian mc2
  selfAdjoint := diracHamiltonian_isSelfAdjoint mc2

/-- The Dirac evolution `U(t) = e^{-itH_D}` (Stone's theorem). -/
def diracUnitaryGroup (mc2 : ℝ) : OneParameterUnitaryGroup (H := DiracSpinorL2) :=
  genToGroup (diracHamiltonian_isSelfAdjoint mc2)

/-- The generator of the Dirac evolution is the Dirac Hamiltonian. -/
theorem generator_diracUnitaryGroup (mc2 : ℝ) :
    generator (diracUnitaryGroup mc2) = diracHamiltonian mc2 :=
  generator_genToGroup (diracHamiltonian_isSelfAdjoint mc2)

end Spectra.QuantumMechanics.Dirac
end
