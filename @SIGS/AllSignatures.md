# Signature Map: `Spectra`

**Total declarations:** 1090
**By kind:** 145 theorems, 765 lemmas, 147 defs, 17 structures, 10 instances, 6 abbrevs
**Sorry count:** 0

## Summary by Kind

| Kind | Count | Sorry |
|------|------:|------:|
| `theorem` | 145 | 0 |
| `lemma` | 765 | 0 |
| `def` | 147 | 0 |
| `structure` | 17 | 0 |
| `instance` | 10 | 0 |
| `abbrev` | 6 | 0 |

## Declarations by Directory

| Directory | Count | Sorry |
|-----------|------:|------:|
| `Bochner` | 11 | 0 |
| `Bochner/Borel` | 48 | 0 |
| `Bochner/GNS` | 83 | 0 |
| `CayleyTransform` | 78 | 0 |
| `Fourier` | 5 | 0 |
| `Herglotz` | 47 | 0 |
| `Herglotz/Stieltjes` | 26 | 0 |
| `Kernel` | 24 | 0 |
| `Kernel/Poisson` | 16 | 0 |
| `Mathlib` | 17 | 0 |
| `Mathlib/MeasureTheory` | 9 | 0 |
| `Operator` | 33 | 0 |
| `Operator/Unitary` | 32 | 0 |
| `PositiveDefinite` | 34 | 0 |
| `ProjValMeasure` | 9 | 0 |
| `QuantumMechanics` | 20 | 0 |
| `QuantumMechanics/BornRule` | 15 | 0 |
| `QuantumMechanics/DiracEquation` | 120 | 0 |
| `QuantumMechanics/Generator` | 11 | 0 |
| `QuantumMechanics/Observable` | 8 | 0 |
| `QuantumMechanics/Stone` | 105 | 0 |
| `QuantumMechanics/Uncertainty` | 18 | 0 |
| `QuantumMechanics/Unitarity` | 23 | 0 |
| `Resolvent` | 63 | 0 |
| `Resolvent/Diagonal` | 27 | 0 |
| `Resolvent/Integral` | 66 | 0 |
| `Resolvent/Range` | 12 | 0 |
| `SpectralTheory` | 21 | 0 |
| `SpectralTheory/Antilinear` | 15 | 0 |
| `SpectralTheory/Calculus` | 16 | 0 |
| `SpectralTheory/Measure` | 50 | 0 |
| `SpectralTheory/StoneFormula` | 28 | 0 |

## Full Catalogue

### `Bochner/`

#### `Basic.lean` (11 decl)

```lean
noncomputable def bochnerMeasureSpectral (f : ℝ → ℂ) (hf : IsContinuous f) : Measure ℝ

lemma bochnerMeasureSpectral_finite {f : ℝ → ℂ} (hf : IsContinuous f) : IsFiniteMeasure (bochnerMeasureSpectral f hf)

lemma fourierStieltjes_continuous : Continuous (fun t : ℝ => ∫ ω, cexp (I * (ω : ℂ) * (t : ℂ)) ∂μ)

lemma fourierStieltjes_conj_neg (t : ℝ) : (∫ ω, cexp (I * (ω : ℂ) * ((-t : ℝ) : ℂ)) ∂μ) = starRingEnd ℂ (∫ ω, cexp (I * (ω : ℂ) * (t : ℂ)) ∂μ)

theorem fourierStieltjes_double_sum_nonneg {n : ℕ} (t : Fin n → ℝ) (c : Fin n → ℂ) : 0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * ∫ ω, cexp (I * (ω : ℂ) * ((t j - t i : ℝ) : ℂ)) ∂μ).re

lemma isPositiveDefinite_fourierStieltjes : IsPositiveDefinite (fun t : ℝ => ∫ ω, cexp (I * (ω : ℂ) * (t : ℂ)) ∂μ)

lemma isHermitian_fourierStieltjes : IsHermitian (fun t : ℝ => ∫ ω, cexp (I * (ω : ℂ) * (t : ℂ)) ∂μ)

theorem isContinuous_fourierStieltjes : IsContinuous (fun t : ℝ => ∫ ω, cexp (I * (ω : ℂ) * (t : ℂ)) ∂μ)

lemma bochner_existence (f : ℝ → ℂ) (hf : IsContinuous f) : ∃ (μ : Measure ℝ), IsFiniteMeasure μ ∧ ∀ t, f t = ∫ ω, exp (I * ↑ω * ↑t) ∂μ

theorem bochner_theorem (f : ℝ → ℂ) (hf : IsContinuous f) : ∃! (μ : Measure ℝ), IsFiniteMeasure μ ∧ ∀ t, f t = ∫ ω, exp (I * ↑ω * ↑t) ∂μ

theorem bochner_theorem_iff (f : ℝ → ℂ) : IsContinuous f ↔ ∃! (μ : Measure ℝ), IsFiniteMeasure μ ∧ ∀ t, f t = ∫ ω, exp (I * ↑ω * ↑t) ∂μ
```

### `Bochner/Borel/`

#### `CDF.lean` (17 decl)

```lean
noncomputable def borelCDF (U_grp : OneParameterUnitaryGroup (H

lemma borelCDF_mono (U_grp : OneParameterUnitaryGroup (H

lemma borelCDF_nonneg (U_grp : OneParameterUnitaryGroup (H

lemma borelCDF_le (U_grp : OneParameterUnitaryGroup (H

lemma borelCDF_tendsto_atBot (U_grp : OneParameterUnitaryGroup (H

lemma borelCDF_continuous (U_grp : OneParameterUnitaryGroup (H

lemma borelEps_pos (n : ℕ) : (0 : ℝ) < 1 / ((n : ℝ) + 1)

noncomputable def borelApproxCDF (U_grp : OneParameterUnitaryGroup (H

lemma borelApproxCDF_mono (U_grp : OneParameterUnitaryGroup (H

lemma borelApproxCDF_bnd (U_grp : OneParameterUnitaryGroup (H

lemma borelHelly (U_grp : OneParameterUnitaryGroup (H

noncomputable def borelLimitCDF (U_grp : OneParameterUnitaryGroup (H

lemma borelLimitCDF_mono (U_grp : OneParameterUnitaryGroup (H

noncomputable def borelMeasure (U_grp : OneParameterUnitaryGroup (H

lemma borelMeasure_univ_le (U_grp : OneParameterUnitaryGroup (H

lemma borelMeasure_real_univ_le (U_grp : OneParameterUnitaryGroup (H

instance borelMeasure_isFiniteMeasure (U_grp : OneParameterUnitaryGroup (H
```

#### `Density.lean` (12 decl)

```lean
noncomputable def borelDensity (U_grp : OneParameterUnitaryGroup (H

lemma fourier_integral_eq_density (U_grp : OneParameterUnitaryGroup (H

lemma regularized_density_value (U_grp : OneParameterUnitaryGroup (H

lemma borelDensity_nonneg (U_grp : OneParameterUnitaryGroup (H

lemma poisson_integral_tendsto (U_grp : OneParameterUnitaryGroup (H

lemma borelDensity_continuous (U_grp : OneParameterUnitaryGroup (H

lemma regularized_mass_tendsto (U_grp : OneParameterUnitaryGroup (H

lemma borelDensity_le (U_grp : OneParameterUnitaryGroup (H

theorem borelDensity_mass (U_grp : OneParameterUnitaryGroup (H

lemma fourier_regularized_value (U_grp : OneParameterUnitaryGroup (H

lemma fourier_poisson_tendsto (U_grp : OneParameterUnitaryGroup (H

theorem borelDensity_fourier (U_grp : OneParameterUnitaryGroup (H
```

#### `Fubini.lean` (1 decl)

```lean
lemma fubini_regularized (U_grp : OneParameterUnitaryGroup (H
```

### `Bochner/Borel/Identity/`

#### `BoundedCDF.lean` (1 decl)

```lean
lemma integral_Ioc_tendsto_of_cdf_tendsto {F : ℕ → ℝ → ℝ} {G : ℝ → ℝ} {φ : ℕ → ℕ} (mono_F : ∀ N, Monotone (F N)) (mono_G : Monotone G) (rc_F : ∀ N x, Function.rightLim (F N) x = F N x) (conv : ∀ x, ContinuousAt G x → Tendsto (fun k => F (φ k) x) atTop (𝓝 (G x))) {a b : ℝ} (hab : a ≤ b) (ha : ContinuousAt G a) (hb : ContinuousAt G b) {g : ℝ → ℂ} (hg : Continuous g) : Tendsto (fun k => ∫ x in Set.Ioc a b, g x ∂((mono_F (φ k)).stieltjesFunction.measure)) atTop (𝓝 (∫ x in Set.Ioc a b, g x ∂(mono_...
```

#### `CauchyTransform.lean` (8 decl)

```lean
noncomputable def borelSubseq (U_grp : OneParameterUnitaryGroup (H

noncomputable def borelCauchyApprox (U_grp : OneParameterUnitaryGroup (H

private lemma borelSubseq_eps_tendsto (U_grp : OneParameterUnitaryGroup (H

lemma borelSubseq_strictMono (U_grp : OneParameterUnitaryGroup (H

lemma borelApproxCDF_tendsto_rat (U_grp : OneParameterUnitaryGroup (H

lemma borelApproxCDF_tendsto_continuousAt (U_grp : OneParameterUnitaryGroup (H

lemma cauchy_density_integral_conj (ρ : ℝ → ℝ) (z : ℂ) : (starRingEnd ℂ) (∫ l, ((l : ℝ) - z)⁻¹ * (ρ l : ℝ)) = ∫ l, ((l : ℝ) - starRingEnd ℂ z)⁻¹ * (ρ l : ℂ)

lemma borel_cauchy_approx_tendsto (U_grp : OneParameterUnitaryGroup (H
```

#### `CauchyVague.lean` (1 decl)

```lean
lemma borel_cauchy_vague (U_grp : OneParameterUnitaryGroup (H
```

### `Bochner/Borel/Measure/`

#### `Basic.lean` (8 decl)

```lean
private lemma two_sided_split {h : ℝ → ℂ} (hcont : Continuous h) {C : ℝ} (hbnd : ∀ t, ‖h t‖ ≤ C) (hherm : ∀ t, h (-t) = starRingEnd ℂ (h t)) (s : ℝ) {ε : ℝ} (hε : 0 < ε) : (∫ t : ℝ, cexp (-(I * (s:ℂ) * (t:ℂ))) * cexp (-((ε:ℂ) * ((|t| : ℝ):ℂ))) * h t) = (∫ t in Set.Ici (0:ℝ), cexp (-(I * ((s:ℂ) - (ε:ℂ) * I) * (t:ℂ))) * h t) + starRingEnd ℂ (∫ t in Set.Ici (0:ℝ), cexp (-(I * ((s:ℂ) - (ε:ℂ) * I) * (t:ℂ))) * h t)

lemma m_eq_cauchy_transform (U_grp : OneParameterUnitaryGroup (H

theorem borelMeasure_fourier (U_grp : OneParameterUnitaryGroup (H

theorem spectral_scalar_measure_exists (U_grp : OneParameterUnitaryGroup (H

lemma borelMeasure_mass (ξ : H) : ((borelMeasure U_grp ξ) Set.univ).toReal = ‖ξ‖ ^ 2

lemma borelMeasure_smul (c : ℂ) (ξ : H) : borelMeasure U_grp (c • ξ) = (‖c‖₊ ^ 2) • borelMeasure U_grp ξ

lemma borelMeasure_zero : borelMeasure U_grp (0 : H) = 0

lemma borel_combination_ext {n m : ℕ} (c : Fin n → ℂ) (v : Fin n → H) (d : Fin m → ℂ) (w : Fin m → H) (h : ∀ t : ℝ, ∑ i, c i * ⟪v i, U_grp.U t (v i)⟫_ℂ = ∑ j, d j * ⟪w j, U_grp.U t (w j)⟫_ℂ) {g : ℝ → ℂ} (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) : ∑ i, c i * ∫ ω, g ω ∂(borelMeasure U_grp (v i)) = ∑ j, d j * ∫ ω, g ω ∂(borelMeasure U_grp (w j))
```

### `Bochner/GNS/`

#### `Continuity.lean` (7 decl)

```lean
structure IsContinuous (f : ℝ → ℂ) : Prop where pd : IsPositiveDefinite f hermitian : IsHermitian f continuous_at_zero : ContinuousAt f 0

lemma IsContinuous.norm_bound (hf : IsContinuous f) (t : ℝ) : ‖f t‖ ≤ (f 0).re

lemma IsContinuous.at_zero_nonneg (hf : IsContinuous f) : 0 ≤ (f 0).re

lemma IsContinuous.at_zero_real (hf : IsContinuous f) : (f 0).im = 0

lemma IsContinuous.variance_tendsto (hf : IsContinuous f) : Filter.Tendsto (pdVariance f) (𝓝 0) (𝓝 0)

lemma pd_oscillation_sq (hf : IsPositiveDefinite f) (hH : IsHermitian f) (s t : ℝ) : ‖f s - f t‖ ^ 2 ≤ 2 * (f 0).re * pdVariance f (s - t)

lemma IsContinuous.continuity (hf : IsContinuous f) : Continuous f
```

### `Bochner/GNS/Hilbert/`

#### `Bundler.lean` (1 decl)

```lean
structure GNSData (f : ℝ → ℂ) where H : Type* instNACG : NormedAddCommGroup H instIPS : @InnerProductSpace ℂ H _ instNACG.toSeminormedAddCommGroup instComplete : @CompleteSpace H instNACG.toUniformSpace embed : letI := instNACG; letI := instIPS; (ℝ →₀ ℂ) →ₗ[ℂ] H embed_inner : ∀ (α β : ℝ →₀ ℂ), @inner ℂ H instIPS.toInner (embed α) (embed β) = pdInner f α β embed_dense : letI := instNACG; Dense (Set.range embed) embed_ker : letI := instNACG; ∀ α, embed α = 0 ↔ α ∈ pdNullSpace f
```

#### `Constructor.lean` (2 decl)

```lean
lemma gnsQuotient_uniformContinuousConstSMul {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) : letI : NormedAddCommGroup (GNSQuotient hPD hH)

noncomputable def gnsConstruction {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) : GNSData f
```

#### `NullSpace.lean` (15 decl)

```lean
def pdNullSpace (f : ℝ → ℂ) : Set (ℝ →₀ ℂ)

lemma mem_pdNullSpace (f : ℝ → ℂ) (α : ℝ →₀ ℂ) : α ∈ pdNullSpace f ↔ pdInner f α α = 0

lemma pdInner_eq_zero_of_null {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) {α : ℝ →₀ ℂ} (hα : α ∈ pdNullSpace f) (β : ℝ →₀ ℂ) : pdInner f α β = 0

lemma pdNullSpace_submodule {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) : ∀ (α β : ℝ →₀ ℂ), α ∈ pdNullSpace f → β ∈ pdNullSpace f → α + β ∈ pdNullSpace f

lemma pdNullSpace_translate_invariant {f : ℝ → ℂ} {α : ℝ →₀ ℂ} (hα : α ∈ pdNullSpace f) (t : ℝ) : translate t α ∈ pdNullSpace f

lemma pdNullSpace_smul_mem {f : ℝ → ℂ} (hH : IsHermitian f) (c : ℂ) {α : ℝ →₀ ℂ} (hα : α ∈ pdNullSpace f) : c • α ∈ pdNullSpace f

def pdNullSubmodule {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) : Submodule ℂ (ℝ →₀ ℂ) where carrier

lemma pdInner_eq_zero_of_null_right {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (α : ℝ →₀ ℂ) {β : ℝ →₀ ℂ} (hβ : β ∈ pdNullSpace f) : pdInner f α β = 0

lemma pdInner_resp_left {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) {α₁ α₂ : ℝ →₀ ℂ} (h : α₁ - α₂ ∈ pdNullSpace f) (β : ℝ →₀ ℂ) : pdInner f α₁ β = pdInner f α₂ β

lemma pdInner_resp_right {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (α : ℝ →₀ ℂ) {β₁ β₂ : ℝ →₀ ℂ} (h : β₁ - β₂ ∈ pdNullSpace f) : pdInner f α β₁ = pdInner f α β₂

abbrev GNSQuotient {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f)

noncomputable def quotientInner {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (x y : GNSQuotient hPD hH) : ℂ

lemma quotientInner_mk {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (a b : ℝ →₀ ℂ) : quotientInner hPD hH (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = pdInner f a b

noncomputable def quotientCore {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) : @InnerProductSpace.Core ℂ (GNSQuotient hPD hH) _ (inferInstance : AddCommGroup _) (inferInstance : Module ℂ _) where inner

lemma quotientInner_definite {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (x : GNSQuotient hPD hH) (hx : quotientInner hPD hH x x = 0) : x = 0
```

### `Bochner/GNS/`

#### `PosDefFun.lean` (1 decl)

```lean
theorem gns_theorem {f : ℝ → ℂ} (hf : IsContinuous f) : ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H) (U : ℝ → H →ₗ[ℂ] H) (ξ : H), (∀ t ψ φ, @inner ℂ H ‹InnerProductSpace ℂ H›.toInner (U t ψ) (U t φ) = @inner ℂ H ‹InnerProductSpace ℂ H›.toInner ψ φ) ∧ (∀ s t ψ, U (s + t) ψ = U s (U t ψ)) ∧ (∀ ψ, U 0 ψ = ψ) ∧ (∀ ψ, Continuous (fun t => U t ψ)) ∧ (∀ t, @inner ℂ H ‹InnerProductSpace ℂ H›.toInner ξ (U t ξ) = f t)
```

#### `PreHilbert.lean` (1 decl)

```lean
lemma pdInner_cauchy_schwarz_re {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (α β : ℝ →₀ ℂ) : (pdInner f α β).re ^ 2 ≤ (pdInner f α α).re * (pdInner f β β).re
```

### `Bochner/GNS/PreHilbert/`

#### `Conjugate.lean` (3 decl)

```lean
lemma pdInner_conj_symm {f : ℝ → ℂ} (hH : IsHermitian f) (α β : ℝ →₀ ℂ) : pdInner f β α = starRingEnd ℂ (pdInner f α β)

lemma pdInner_add_left {f : ℝ → ℂ} (hH : IsHermitian f) (α₁ α₂ β : ℝ →₀ ℂ) : pdInner f (α₁ + α₂) β = pdInner f α₁ β + pdInner f α₂ β

lemma pdInner_smul_left {f : ℝ → ℂ} (hH : IsHermitian f) (c : ℂ) (α β : ℝ →₀ ℂ) : pdInner f (c • α) β = starRingEnd ℂ c * pdInner f α β
```

#### `Cyclic.lean` (3 decl)

```lean
noncomputable def cyclicVector : ℝ →₀ ℂ

lemma translate_cyclicVector (t : ℝ) : translate t cyclicVector = Finsupp.single t 1

theorem pdInner_cyclic (f : ℝ → ℂ) (t : ℝ) : pdInner f cyclicVector (translate t cyclicVector) = f t
```

#### `Defs.lean` (2 decl)

```lean
noncomputable def pdInner (f : ℝ → ℂ) (α β : ℝ →₀ ℂ) : ℂ

noncomputable def translate (t : ℝ) (α : ℝ →₀ ℂ) : ℝ →₀ ℂ
```

#### `Evolution.lean` (3 decl)

```lean
lemma pdInner_aux_zero (f : ℝ → ℂ) (β : ℝ →₀ ℂ) (t : ℝ) : (β.sum fun s ds => starRingEnd ℂ (0 : ℂ) * ds * f (s - t)) = 0

lemma pdInner_single_single (f : ℝ → ℂ) (a b : ℝ) (ca cb : ℂ) : pdInner f (Finsupp.single a ca) (Finsupp.single b cb) = starRingEnd ℂ ca * cb * f (b - a)

lemma pdInner_single_one (f : ℝ → ℂ) (a b : ℝ) : pdInner f (Finsupp.single a 1) (Finsupp.single b 1) = f (b - a)
```

#### `Linearity.lean` (4 decl)

```lean
lemma pdInner_zero_left (f : ℝ → ℂ) (β : ℝ →₀ ℂ) : pdInner f 0 β = 0

lemma pdInner_zero_right (f : ℝ → ℂ) (α : ℝ →₀ ℂ) : pdInner f α 0 = 0

lemma pdInner_add_right (f : ℝ → ℂ) (α β₁ β₂ : ℝ →₀ ℂ) : pdInner f α (β₁ + β₂) = pdInner f α β₁ + pdInner f α β₂

lemma pdInner_smul_right (f : ℝ → ℂ) (α : ℝ →₀ ℂ) (c : ℂ) (β : ℝ →₀ ℂ) : pdInner f α (c • β) = c * pdInner f α β
```

#### `NormEst.lean` (3 decl)

```lean
lemma pdInner_translate_diff_cyclic (f : ℝ → ℂ) (hH : IsHermitian f) (t : ℝ) : pdInner f (translate t cyclicVector - cyclicVector) (translate t cyclicVector - cyclicVector) = 2 * (f 0).re - f t - starRingEnd ℂ (f t)

lemma pdInner_translate_diff_re {f : ℝ → ℂ} (_hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) : (pdInner f (translate t cyclicVector - cyclicVector) (translate t cyclicVector - cyclicVector)).re = 2 * ((f 0).re - (f t).re)

theorem pdInner_translate_diff_eq_variance {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) : (pdInner f (translate t cyclicVector - cyclicVector) (translate t cyclicVector - cyclicVector)).re = 2 * pdVariance f t
```

#### `PosSemiDef.lean` (3 decl)

```lean
lemma pdInner_self_eq_fin_sum (f : ℝ → ℂ) (α : ℝ →₀ ℂ) : pdInner f α α = let S

theorem pdInner_self_re_nonneg {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (α : ℝ →₀ ℂ) : 0 ≤ (pdInner f α α).re

lemma pdInner_self_im_eq_zero {f : ℝ → ℂ} (hH : IsHermitian f) (α : ℝ →₀ ℂ) : (pdInner f α α).im = 0
```

#### `TransAction.lean` (6 decl)

```lean
lemma translate_single (t s : ℝ) (c : ℂ) : translate t (Finsupp.single s c) = Finsupp.single (s + t) c

lemma translate_add_right (t : ℝ) (α β : ℝ →₀ ℂ) : translate t (α + β) = translate t α + translate t β

lemma translate_smul (t : ℝ) (c : ℂ) (α : ℝ →₀ ℂ) : translate t (c • α) = c • translate t α

lemma translate_zero (α : ℝ →₀ ℂ) : translate 0 α = α

lemma translate_translate (s t : ℝ) (α : ℝ →₀ ℂ) : translate s (translate t α) = translate (s + t) α

lemma pdInner_translate {f : ℝ → ℂ} (t : ℝ) (α β : ℝ →₀ ℂ) : pdInner f (translate t α) (translate t β) = pdInner f α β
```

### `Bochner/GNS/Representation/`

#### `Cyclic.lean` (3 decl)

```lean
noncomputable def gns_cyclic (gns : GNSData f) : gns.H

theorem gns_representation {f : ℝ → ℂ} (gns : GNSUnitaryGroup f) (t : ℝ) : @inner ℂ gns.H gns.instIPS.toInner (gns_cyclic gns.toGNSData) (gns.unitaryAction t (gns_cyclic gns.toGNSData)) = f t

lemma gns_cyclic_norm_sq {f : ℝ → ℂ} (_hH : IsHermitian f) (gns : GNSData f) : @inner ℂ gns.H gns.instIPS.toInner (gns_cyclic gns) (gns_cyclic gns) = f 0
```

#### `Lemmas.lean` (16 decl)

```lean
noncomputable def translateLM (t : ℝ) : (ℝ →₀ ℂ) →ₗ[ℂ] (ℝ →₀ ℂ) where toFun

lemma translateLM_preserves_null {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) : pdNullSubmodule hPD hH ≤ (pdNullSubmodule hPD hH).comap (translateLM t)

noncomputable def quotientTranslate {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) : GNSQuotient hPD hH →ₗ[ℂ] GNSQuotient hPD hH

lemma quotientTranslate_mk {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) (α : ℝ →₀ ℂ) : quotientTranslate hPD hH t (Submodule.Quotient.mk α) = Submodule.Quotient.mk (translate t α)

lemma quotientTranslate_inner {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) (x y : GNSQuotient hPD hH) : quotientInner hPD hH (quotientTranslate hPD hH t x) (quotientTranslate hPD hH t y) = quotientInner hPD hH x y

lemma quotientTranslate_comp {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (s t : ℝ) (x : GNSQuotient hPD hH) : quotientTranslate hPD hH s (quotientTranslate hPD hH t x) = quotientTranslate hPD hH (s + t) x

lemma quotientTranslate_zero {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (x : GNSQuotient hPD hH) : quotientTranslate hPD hH 0 x = x

lemma quotientTranslate_norm {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) (x : GNSQuotient hPD hH) : letI

noncomputable def quotientTranslateLI {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) : letI

lemma quotientTranslate_uniformContinuous {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) : letI

noncomputable def completionTranslate {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) : letI : NormedAddCommGroup (GNSQuotient hPD hH)

lemma completionTranslate_coe {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) (a : GNSQuotient hPD hH) : letI : NormedAddCommGroup (GNSQuotient hPD hH)

lemma completionTranslate_comp {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (s t : ℝ) : letI : NormedAddCommGroup (GNSQuotient hPD hH)

lemma completionTranslate_zero' {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) : letI : NormedAddCommGroup (GNSQuotient hPD hH)

lemma completionTranslate_inner {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) : letI : NormedAddCommGroup (GNSQuotient hPD hH)

lemma completionTranslate_compat {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) (α : ℝ →₀ ℂ) : letI : NormedAddCommGroup (GNSQuotient hPD hH)
```

#### `StronglyCont.lean` (5 decl)

```lean
lemma pdInner_translate_left_continuous {f : ℝ → ℂ} (hf : IsContinuous f) (α β : ℝ →₀ ℂ) : Continuous (fun t => pdInner f (translate t α) β)

lemma quotientTranslate_continuous {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (hf : IsContinuous f) (α : ℝ →₀ ℂ) : letI : NormedAddCommGroup (GNSQuotient hPD hH)

lemma completionTranslate_continuous_on_dense {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (hf : IsContinuous f) (α : ℝ →₀ ℂ) : letI : NormedAddCommGroup (GNSQuotient hPD hH)

lemma completionTranslate_dist {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) : letI : NormedAddCommGroup (GNSQuotient hPD hH)

theorem completionTranslate_strong_continuous {f : ℝ → ℂ} (hPD : IsPositiveDefinite f) (hH : IsHermitian f) (hf : IsContinuous f) : letI : NormedAddCommGroup (GNSQuotient hPD hH)
```

#### `StronglyEx.lean` (2 decl)

```lean
lemma strong_continuity_on_dense {f : ℝ → ℂ} (hf : IsContinuous f) (gns : GNSData f) (U : letI

lemma strong_continuity_extends {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (U : ℝ → H →ₗ[ℂ] H) (hiso : ∀ t ψ, ‖U t ψ‖ = ‖ψ‖) (_hgroup : ∀ s t ψ, U (s + t) ψ = U s (U t ψ)) (_hid : ∀ ψ, U 0 ψ = ψ) (D : Set H) (hD : Dense D) (hD_cont : ∀ φ ∈ D, Continuous (fun t => U t φ)) : ∀ ψ, Continuous (fun t => U t ψ)
```

#### `ToStone.lean` (1 decl)

```lean
noncomputable def toOneParameterUnitaryGroup {f : ℝ → ℂ} (gns : GNSUnitaryGroup f) : @QuantumMechanics.OneParameterUnitaryGroup gns.H gns.instNACG gns.instIPS gns.instComplete
```

#### `UnitaryConstructor.lean` (1 decl)

```lean
noncomputable def gnsUnitaryConstruction {f : ℝ → ℂ} (hf : IsContinuous f) : GNSUnitaryGroup f
```

#### `UnitaryGroup.lean` (1 decl)

```lean
structure GNSUnitaryGroup (f : ℝ → ℂ) extends GNSData f where unitaryAction : ℝ → H →ₗ[ℂ] H isometry : ∀ (t : ℝ) (ψ φ : H), @inner ℂ H instIPS.toInner (unitaryAction t ψ) (unitaryAction t φ) = @inner ℂ H instIPS.toInner ψ φ group_law : ∀ (s t : ℝ) (ψ : H), unitaryAction (s + t) ψ = unitaryAction s (unitaryAction t ψ) identity : ∀ (ψ : H), unitaryAction 0 ψ = ψ strong_continuous : ∀ (ψ : H), Continuous (fun t => unitaryAction t ψ) compat : ∀ (t : ℝ) (α : ℝ →₀ ℂ), unitaryAction t (toGNSData.emb...
```

### `CayleyTransform/`

#### `BoundedBelow.lean` (5 decl)

```lean
def HasEigenvalue (A : H →ₗ.[ℂ] H) (μ : ℂ) : Prop

def IsBoundedBelow (A : H →ₗ.[ℂ] H) (μ : ℂ) : Prop

lemma isBoundedBelow_of_cayleyTransform_sub_smul_boundedBelow {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (μ : ℝ) (hμ_ne : (↑μ : ℂ) + I ≠ 0) (c : ℝ) (hc_pos : 0 < c) (hc_bound : ∀ φ, c * ‖φ‖ ≤ ‖(cayleyTransform hsym hplus - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H) φ‖) : IsBoundedBelow A μ

lemma isBoundedBelow_of_isUnit_cayleyTransform_sub_smul [Nontrivial H] {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (μ : ℝ) (h_unit : IsUnit (cayleyTransform hsym hplus - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H)) : IsBoundedBelow A μ

lemma norm_lower_bound_of_approx_eigenvalue_of_unit {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (μ : ℝ) (ψ : A.domain) (h_norm : ‖A ψ + I • (ψ : H)‖ = 1) (δ : ℝ) (hδ_pos : 0 ≤ δ) (hδ_small : δ ^ 2 < 1 + μ ^ 2) (h_approx : ‖A ψ - (↑μ : ℂ) • (ψ : H)‖ ≤ δ) : (Real.sqrt (1 + μ ^ 2 - δ ^ 2) - |μ| * δ) / (1 + μ ^ 2) ≤ ‖(ψ : H)‖
```

#### `Eigenvalue.lean` (7 decl)

```lean
theorem cayley_neg_one_eigenvalue_iff {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) : (∃ φ : H, φ ≠ 0 ∧ cayleyTransform hsym hplus φ = -φ) ↔ (∃ ψ : A.domain, (ψ : H) ≠ 0 ∧ A ψ = 0)

lemma cayley_shift_identity {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (μ : ℝ) (hμ_ne : (↑μ : ℂ) + I ≠ 0) (ψ : A.domain) : (cayleyTransform hsym hplus - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H) (A ψ + I • (ψ : H)) = ((1 : ℂ) - (↑μ - I) * (↑μ + I)⁻¹) • (A ψ - (↑μ : ℂ) • (ψ : H))

theorem cayley_eigenvalue_correspondence {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (μ : ℝ) : (∃ ψ : A.domain, (ψ : H) ≠ 0 ∧ A ψ = (↑μ : ℂ) • (ψ : H)) ↔ (∃ φ : H, φ ≠ 0 ∧ cayleyTransform hsym hplus φ = ((↑μ - I) * (↑μ + I)⁻¹) • φ)

lemma cayley_shift_injective {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (μ : ℝ) (hC : ∃ C > 0, ∀ ψ (hψ : ψ ∈ A.domain), ‖A ⟨ψ, hψ⟩ - (↑μ : ℂ) • ψ‖ ≥ C * ‖ψ‖) : let U

lemma self_adjoint_norm_sq_add {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) : ‖A ψ + I • (ψ : H)‖ ^ 2 = ‖A ψ‖ ^ 2 + ‖(ψ : H)‖ ^ 2

lemma cayley_approx_eigenvalue_backward {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (μ : ℝ) (hμ_ne : (↑μ : ℂ) + I ≠ 0) : (∀ ε > 0, ∃ φ, ‖φ‖ = 1 ∧ ‖(cayleyTransform hsym hplus - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H) φ‖ < ε) → (∀ C > 0, ∃ ψ : A.domain, (ψ : H) ≠ 0 ∧ ‖A ψ - (↑μ : ℂ) • (ψ : H)‖ < C * ‖(ψ : H)‖)

lemma cayley_approx_eigenvalue_forward {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (μ : ℝ) (hμ_ne : (↑μ : ℂ) + I ≠ 0) : (∀ C > 0, ∃ ψ : A.domain, (ψ : H) ≠ 0 ∧ ‖A ψ - (↑μ : ℂ) • (ψ : H)‖ < C * ‖(ψ : H)‖) → (∀ ε > 0, ∃ φ, ‖φ‖ = 1 ∧ ‖(cayleyTransform hsym hplus - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H) φ‖ < ε)
```

#### `Image.lean` (4 decl)

```lean
lemma Complex.eq_coe_re_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : z = ↑z.re

def cayleyImage (B : Set ℝ) : Set ℂ

def inverseCayleyImage (S : Set ℂ) : Set ℝ

lemma cayleyImage_inverseCayleyImage (S : Set ℂ) (hS : S ⊆ {w | ‖w‖ = 1 ∧ w ≠ 1}) : cayleyImage (inverseCayleyImage S) = S
```

#### `Inverse.lean` (10 decl)

```lean
lemma one_minus_cayley_apply {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (ψ : A.domain) : (ContinuousLinearMap.id ℂ H - cayleyTransform hsym hplus) (A ψ + I • (ψ : H)) = (2 * I) • (ψ : H)

lemma one_plus_cayley_apply {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (ψ : A.domain) : (ContinuousLinearMap.id ℂ H + cayleyTransform hsym hplus) (A ψ + I • (ψ : H)) = (2 : ℂ) • A ψ

lemma inverse_cayley_relation {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (ψ : A.domain) : (2 * I) • A ψ = I • ((ContinuousLinearMap.id ℂ H + cayleyTransform hsym hplus) (A ψ + I • (ψ : H)))

lemma inverse_cayley_formula {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (ψ : A.domain) : (ContinuousLinearMap.id ℂ H - cayleyTransform hsym hplus) (A ψ + I • (ψ : H)) = (2 * I) • (ψ : H) ∧ (ContinuousLinearMap.id ℂ H + cayleyTransform hsym hplus) (A ψ + I • (ψ : H)) = (2 : ℂ) • A ψ

lemma range_one_minus_cayley {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) : ∀ ψ : H, ψ ∈ A.domain → ∃ φ : H, (ContinuousLinearMap.id ℂ H - cayleyTransform hsym hplus) φ = (2 * I) • ψ

lemma inverse_cayley_domain {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (ψ : A.domain) : (ψ : H) = ((-I) / 2) • ((ContinuousLinearMap.id ℂ H - cayleyTransform hsym hplus) (A ψ + I • (ψ : H)))

lemma cayley_bijection {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (ψ : A.domain) : ((-I) / 2) • ((ContinuousLinearMap.id ℂ H - cayleyTransform hsym hplus) (A ψ + I • (ψ : H))) = (ψ : H) ∧ ((1 : ℂ) / 2) • ((ContinuousLinearMap.id ℂ H + cayleyTransform hsym hplus) (A ψ + I • (ψ : H))) = A ψ

noncomputable def inverseCayleyOp (U : H →L[ℂ] H) (_ : ∀ ψ φ, ⟪U ψ, U φ⟫_ℂ = ⟪ψ, φ⟫_ℂ) (h_one : ∀ ψ, U ψ = ψ → ψ = 0) (_ : ∀ ψ, U ψ = -ψ → ψ = 0) : LinearMap.range (↑(ContinuousLinearMap.id ℂ H - U) : H →ₗ[ℂ] H) →ₗ[ℂ] H where toFun

lemma inverseCayleyOp_symmetric (U : H →L[ℂ] H) (hU : ∀ ψ φ, ⟪U ψ, U φ⟫_ℂ = ⟪ψ, φ⟫_ℂ) (h_one : ∀ ψ, U ψ = ψ → ψ = 0) (h_neg_one : ∀ ψ, U ψ = -ψ → ψ = 0) : ∀ ψ φ : LinearMap.range (↑(ContinuousLinearMap.id ℂ H - U) : H →ₗ[ℂ] H), ⟪inverseCayleyOp U hU h_one h_neg_one ψ, (φ : H)⟫_ℂ = ⟪(ψ : H), inverseCayleyOp U hU h_one h_neg_one φ⟫_ℂ

theorem generator_domain_eq_range_one_minus_cayley {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) : (A.domain : Set H) = ↑(LinearMap.range (↑(ContinuousLinearMap.id ℂ H - cayleyTransform hsym hplus) : H →ₗ[ℂ] H))
```

#### `MapsResolvent.lean` (3 decl)

```lean
lemma resolvent_at_neg_i_eq_cfc {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus  : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) : resolvent_at_neg_i hsym hplus = cfc (fun w : ℂ => (1 - w) / (2 * I)) (cayleyTransform hsym hplus)

lemma spectrum_resolvent_at_neg_i {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus  : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) : spectrum ℂ (resolvent_at_neg_i hsym hplus) = (fun w : ℂ => (1 - w) / (2 * I)) '' (spectrum ℂ (cayleyTransform hsym hplus))

theorem cayley_maps_resolvent [Nontrivial H] {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus  : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (z : ℂ) (hz : z.im ≠ 0) : let w
```

#### `Mobius.lean` (12 decl)

```lean
lemma real_add_I_ne_zero : (↑μ : ℂ) + I ≠ 0

lemma mobius_norm_one (hμ_ne : (↑μ : ℂ) + I ≠ 0) : ‖(↑μ - I) * (↑μ + I)⁻¹‖ = 1

lemma mobius_norm_eq_one (hμ_ne : (↑μ : ℂ) + I ≠ 0) : ‖(↑μ - I) * (↑μ + I)⁻¹‖ = 1

lemma one_sub_mobius (hμ_ne : (↑μ : ℂ) + I ≠ 0) : (1 : ℂ) - (↑μ - I) * (↑μ + I)⁻¹ = 2 * I / (↑μ + I)

lemma one_add_mobius (hμ_ne : (↑μ : ℂ) + I ≠ 0) : (1 : ℂ) + (↑μ - I) * (↑μ + I)⁻¹ = 2 * ↑μ / (↑μ + I)

lemma mobius_coeff_identity (hμ_ne : (↑μ : ℂ) + I ≠ 0) : let w

lemma one_sub_mobius_ne_zero (hμ_ne : (↑μ : ℂ) + I ≠ 0) : (1 : ℂ) - (↑μ - I) * (↑μ + I)⁻¹ ≠ 0

lemma one_sub_mobius_norm_pos (hμ_ne : (↑μ : ℂ) + I ≠ 0) : ‖(1 : ℂ) - (↑μ - I) * (↑μ + I)⁻¹‖ > 0

noncomputable def inverseMobius (w : ℂ) : ℂ

lemma inverseMobius_real (w : ℂ) (hw_norm : ‖w‖ = 1) (hw_ne : w ≠ 1) : (inverseMobius w).im = 0

lemma mobius_inverseMobius (w : ℂ) (_  : ‖w‖ = 1) (hw_ne : w ≠ 1) : (inverseMobius w - I) * (inverseMobius w + I)⁻¹ = w

lemma inverseMobius_mobius (μ : ℝ) : inverseMobius ((↑μ - I) * (↑μ + I)⁻¹) = μ
```

#### `RieszMarkov.lean` (19 decl)

```lean
lemma cfc_conjMul_inner_eq_normSq (U : H →L[ℂ] H) (_hn : IsStarNormal U) (g : ℂ → ℂ) (hg : ContinuousOn g (spectrum ℂ U)) (ξ : H) : ⟪ξ, cfc (fun z => star (g z) * g z) U ξ⟫_ℂ = (‖cfc g U ξ‖ : ℂ) ^ 2

lemma cfc_re_inner_ofReal_nonneg (U : H →L[ℂ] H) (hn : IsStarNormal U) (f : ℂ → ℝ) (hf : ContinuousOn f (spectrum ℂ U)) (hf0 : ∀ z ∈ spectrum ℂ U, 0 ≤ f z) (ξ : H) : 0 ≤ (⟪ξ, cfc (fun z => (f z : ℂ)) U ξ⟫_ℂ).re

lemma cfcHom_conjMul_inner_eq_normSq (U : H →L[ℂ] H) (hn : IsStarNormal U) (φ : C(spectrum ℂ U, ℂ)) (ξ : H) : ⟪ξ, (cfcHom hn (star φ * φ)) ξ⟫_ℂ = (‖(cfcHom hn φ) ξ‖ : ℂ) ^ 2

noncomputable def complexify (U : H →L[ℂ] H) : C(spectrum ℂ U, ℝ) →L[ℝ] C(spectrum ℂ U, ℂ)

noncomputable def rieszFunctional (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ : H) : C(spectrum ℂ U, ℝ) →ₗ[ℝ] ℝ where toFun ψ

lemma rieszFunctional_nonneg (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ : H) (ψ : C(spectrum ℂ U, ℝ)) (hψ : 0 ≤ ψ) : 0 ≤ rieszFunctional U hn ξ ψ

def ccToC (U : H →L[ℂ] H) : C_c(spectrum ℂ U, ℝ) →ₗ[ℝ] C(spectrum ℂ U, ℝ) where toFun

noncomputable def spectralMeasure (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ : H) : Measure (spectrum ℂ U)

lemma integral_spectralMeasure (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ : H) (ψ : C_c(spectrum ℂ U, ℝ)) : ∫ z, ψ z ∂(spectralMeasure U hn ξ) = (⟪ξ, cfcHom hn (complexify U ψ.toContinuousMap) ξ⟫_ℂ).re

lemma integral_spectralMeasure_continuous (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ : H) (g : C(spectrum ℂ U, ℝ)) : ∫ z, g z ∂(spectralMeasure U hn ξ) = (⟪ξ, cfcHom hn (complexify U g) ξ⟫_ℂ).re

instance instIsFiniteMeasureOnCompacts_spectralMeasure (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ : H) : IsFiniteMeasureOnCompacts (spectralMeasure U hn ξ)

instance instIsFiniteMeasure_spectralMeasure (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ : H) : IsFiniteMeasure (spectralMeasure U hn ξ)

lemma inner_cfcHom_complexify_real (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ : H) (g : C(spectrum ℂ U, ℝ)) : ⟪ξ, cfcHom hn (complexify U g) ξ⟫_ℂ = ((∫ z, g z ∂(spectralMeasure U hn ξ) : ℝ) : ℂ)

lemma spectralMeasure_real_univ (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ : H) : (spectralMeasure U hn ξ).real Set.univ = ‖ξ‖ ^ 2

lemma spectral_integrable_real (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ : H) (g : C(spectrum ℂ U, ℝ)) : Integrable (fun z => g z) (spectralMeasure U hn ξ)

lemma integral_spectralMeasure_complex (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ : H) (f : C(spectrum ℂ U, ℂ)) : ∫ z, f z ∂(spectralMeasure U hn ξ) = ⟪ξ, cfcHom hn f ξ⟫_ℂ

lemma inner_polarization_right (T : H →L[ℂ] H) (ξ η : H) : ⟪ξ, T η⟫_ℂ = (⟪ξ + η, T (ξ + η)⟫_ℂ - ⟪ξ - η, T (ξ - η)⟫_ℂ - Complex.I * ⟪ξ + Complex.I • η, T (ξ + Complex.I • η)⟫_ℂ + Complex.I * ⟪ξ - Complex.I • η, T (ξ - Complex.I • η)⟫_ℂ) / 4

lemma inner_cfcHom_polarized (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ η : H) (f : C(spectrum ℂ U, ℂ)) : ⟪ξ, cfcHom hn f η⟫_ℂ = ( ∫ z, f z ∂(spectralMeasure U hn (ξ + η)) - ∫ z, f z ∂(spectralMeasure U hn (ξ - η)) - Complex.I * ∫ z, f z ∂(spectralMeasure U hn (ξ + Complex.I • η)) + Complex.I * ∫ z, f z ∂(spectralMeasure U hn (ξ - Complex.I • η)) ) / 4

lemma norm_inner_cfcHom_le (U : H →L[ℂ] H) (hn : IsStarNormal U) (ξ η : H) (f : C(spectrum ℂ U, ℂ)) : ‖⟪ξ, cfcHom hn f η⟫_ℂ‖ ≤ ‖f‖ * ‖ξ‖ * ‖η‖
```

#### `Transform.lean` (18 decl)

```lean
noncomputable def cayleyTransform {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) : H →L[ℂ] H

lemma cayleyTransform_apply_resolvent {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (ψ : A.domain) : cayleyTransform hsym hplus (A ψ + I • (ψ : H)) = A ψ - I • (ψ : H)

theorem cayleyTransform_isometry {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (φ : H) : ‖cayleyTransform hsym hplus φ‖ = ‖φ‖

noncomputable def cayleyTransformOfGroup (U : OneParameterUnitaryGroup H) : H →L[ℂ] H

theorem cayleyTransform_surjective {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus  : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) : Function.Surjective (cayleyTransform hsym hplus)

theorem cayleyTransform_surjective_of_isSelfAdjoint [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) : Function.Surjective (cayleyTransform (isFormalAdjoint_self_of_isSelfAdjoint hA) (isSelfAdjoint_to_surjective hA).1)

theorem cayleyTransform_unitary [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus  : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) : Unitary (cayleyTransform hsym hplus)

theorem cayleyTransform_mem_unitary [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus  : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) : cayleyTransform hsym hplus ∈ unitary (H →L[ℂ] H)

lemma cayleyTransform_spectrum_subset_circle [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus  : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) : spectrum ℂ (cayleyTransform hsym hplus) ⊆ Metric.sphere (0 : ℂ) 1

theorem cayleyTransform_unitary_of_isSelfAdjoint [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) : Unitary (cayleyTransform (isFormalAdjoint_self_of_isSelfAdjoint hA) (isSelfAdjoint_to_surjective hA).1)

lemma cayleyTransform_comp_adjoint [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus  : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) : (cayleyTransform hsym hplus).comp (cayleyTransform hsym hplus).adjoint = ContinuousLinearMap.id ℂ H

lemma cayleyTransform_adjoint_comp [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus  : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) : (cayleyTransform hsym hplus).adjoint.comp (cayleyTransform hsym hplus) = ContinuousLinearMap.id ℂ H

lemma cayleyTransform_isUnit [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus  : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) : IsUnit (cayleyTransform hsym hplus)

lemma cayleyTransform_isUnit_of_isSelfAdjoint [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) : IsUnit (cayleyTransform (isFormalAdjoint_self_of_isSelfAdjoint hA) (isSelfAdjoint_to_surjective hA).1)

theorem cayleyTransform_norm_one [Nontrivial H] {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) : ‖cayleyTransform hsym hplus‖ = 1

lemma symmetric_norm_sq_add {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) : ‖A ψ + I • (ψ : H)‖ ^ 2 = ‖A ψ‖ ^ 2 + ‖(ψ : H)‖ ^ 2

lemma cayleyTransform_eq_self_imp_zero {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) {χ : H} (hχ : cayleyTransform hsym hplus χ = χ) : χ = 0

lemma cayleyTransform_isStarNormal [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus  : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) : IsStarNormal (cayleyTransform hsym hplus)
```

### `Fourier/`

#### `Identity.lean` (3 decl)

```lean
lemma inner_unitary_neg (U_grp : OneParameterUnitaryGroup (H

lemma fourier_identity (U_grp : OneParameterUnitaryGroup (H

lemma fourier_kernel_eval {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : (∫ lambda : ℝ, cexp (-(I * (lambda : ℂ) * (t : ℂ))) * (Real.exp (-(δ * |lambda|)) : ℂ)) = ((2 * δ / (t ^ 2 + δ ^ 2) : ℝ) : ℂ)
```

#### `Inversion.lean` (1 decl)

```lean
theorem eq_of_fourier_decay_eq {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (hfb : ∃ C, ∀ t, ‖f t‖ ≤ C) (hgb : ∃ C, ∀ t, ‖g t‖ ≤ C) (h : ∀ ε : ℝ, 0 < ε → ∀ s : ℝ, (∫ (t : ℝ), cexp (-(I * (s : ℂ) * (t : ℂ))) * cexp (-((ε : ℂ) * ((|t| : ℝ) : ℂ))) * f t) = ∫ (t : ℝ), cexp (-(I * (s : ℂ) * (t : ℂ))) * cexp (-((ε : ℂ) * ((|t| : ℝ) : ℂ))) * g t) : f = g
```

#### `IsUnique.lean` (1 decl)

```lean
theorem fourier_uniqueness (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : ∀ t : ℝ, ∫ ω, exp (I * ω * t) ∂μ = ∫ ω, exp (I * ω * t) ∂ν) : μ = ν
```

### `Herglotz/`

#### `Basic.lean` (3 decl)

```lean
lemma withDensity_ofReal_eq_stieltjes_measure {ρ : ℝ → ℝ} (hρ_nn : ∀ x, 0 ≤ ρ x) (hρ_int : Integrable ρ volume) {F : ℝ → ℝ} (hF : ∀ a, F a = ∫ l in Set.Iic a, ρ l ∂volume) (hF_mono : Monotone F) (hF_cont : Continuous F) (hF_atBot : Tendsto F atBot (𝓝 0)) : volume.withDensity (fun l => ENNReal.ofReal (ρ l)) = hF_mono.stieltjesFunction.measure

private lemma stieltjes_rightLim_const {F : ℝ → ℝ} (hF : Monotone F) {a M : ℝ} (hconst : ∀ x, a < x → F x = M) : Function.rightLim F a = M

lemma herglotz_lemma_stieltjes (c : ℤ → ℂ) (M : ℝ) (hM : 0 ≤ M) (_c_zero : c 0 = ↑M) (F : ℕ → ℝ → ℝ) (h_mono : ∀ N, Monotone (F N)) (h_bnd : ∀ N x, F N x ∈ Set.Icc 0 M) (h_zero : ∀ N, F N 0 = 0) (h_top : ∀ N, F N (2 * Real.pi) = M) (h_fourier : ∀ N (n : ℤ), ∫ θ in Set.Icc 0 (2 * Real.pi), exp (I * n * θ) ∂((h_mono N).stieltjesFunction.measure) = (c n * (fejerWeight N n : ℂ))) : ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ μ (Set.Icc 0 (2 * Real.pi))ᶜ = 0 ∧ (∀ n : ℤ, ∫ θ in Set.Icc 0 (2 * Real.pi), ex...
```

#### `FejerMeans.lean` (16 decl)

```lean
noncomputable def fejerWeight (N : ℕ) (n : ℤ) : ℝ

theorem fejerWeight_nonneg (N : ℕ) (n : ℤ) : 0 ≤ fejerWeight N n

theorem fejerWeight_zero (N : ℕ) : fejerWeight N 0 = 1

noncomputable def fejerMeanDensity (ψ : H) (N : ℕ) (θ : ℝ) : ℂ

private lemma exp_conj_mul (j k : ℤ) (θ : ℝ) : starRingEnd ℂ (exp (-I * ↑j * ↑θ)) * exp (-I * ↑k * ↑θ) = exp (-I * ↑(k - j) * ↑θ)

private lemma fiber_count (N : ℕ) (n : ℤ) (hn : n ∈ Finset.Icc (-(N : ℤ)) N) : (((Finset.univ : Finset (Fin (N + 1))) ×ˢ Finset.univ).filter fun p : Fin (N + 1) × Fin (N + 1) => (↑p.2 : ℤ) - ↑p.1 = n).card = N + 1 - n.natAbs

private lemma double_sum_eq_weighted (g : ℤ → ℂ) (N : ℕ) : ∑ j : Fin (N + 1), ∑ k : Fin (N + 1), g ((↑k : ℤ) - ↑j) = ∑ n ∈ Finset.Icc (-(N : ℤ)) N, (↑(N + 1 - n.natAbs) : ℂ) * g n

private lemma fejerWeight_mul_eq (N : ℕ) (n : ℤ) (hn : n.natAbs ≤ N) : (↑(N + 1) : ℂ) * (↑(fejerWeight N n) : ℂ) = ↑(N + 1 - n.natAbs)

private lemma fejer_reindex (U : H →L[ℂ] H) (ψ : H) (N : ℕ) (θ : ℝ) : (∑ j : Fin (N + 1), ∑ k : Fin (N + 1), starRingEnd ℂ (exp (-I * ↑(↑j : ℤ) * ↑θ)) * exp (-I * ↑(↑k : ℤ) * ↑θ) * unitaryCorrelation U ψ (↑k - ↑j)).re = (↑(N + 1) : ℝ) * (fejerMeanDensity U ψ N θ).re

lemma fejerMeanDensity_nonneg (hU : Operator.Unitary U) (ψ : H) (N : ℕ) (θ : ℝ) : 0 ≤ (fejerMeanDensity U ψ N θ).re

private lemma exp_nat_mul_two_pi_mul_I (n : ℕ) : Complex.exp (↑n * (2 * ↑Real.pi * I)) = 1

private lemma exp_int_mul_two_pi_mul_I (n : ℤ) : Complex.exp (↑n * (2 * ↑Real.pi * I)) = 1

private lemma hasDerivAt_cexp_div {c : ℂ} (hc : c ≠ 0) (θ : ℝ) : HasDerivAt (fun t : ℝ => exp (c * ↑t) / c) (exp (c * ↑θ)) θ

private lemma continuous_cexp_neg_int_mul (n : ℤ) : Continuous (fun θ : ℝ => exp (-I * ↑n * ↑θ))

lemma set_integral_cexp_neg_int (n : ℤ) : ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), Complex.exp (-I * ↑n * ↑θ) = if n = 0 then ↑(2 * Real.pi) else 0

lemma fejerMeanDensity_integral (ψ : H) (N : ℕ) : ∫ θ in Set.Icc 0 (2 * Real.pi), fejerMeanDensity U ψ N θ = 2 * Real.pi * unitaryCorrelation U ψ 0
```

#### `FejerMeasure.lean` (28 decl)

```lean
noncomputable def fejerMeasure (U : H →L[ℂ] H) (_hU : Operator.Unitary U) (ψ : H) (N : ℕ) : Measure ℝ

lemma fejerMeanDensity_continuous (U : H →L[ℂ] H) (ψ : H) (N : ℕ) : Continuous (fejerMeanDensity U ψ N)

lemma fejerMeasure_total (ψ : H) (N : ℕ) : (fejerMeasure U hU ψ N (Set.Icc 0 (2 * Real.pi))).toReal = ‖ψ‖ ^ 2

lemma fejerWeight_symm (N : ℕ) (n : ℤ) : fejerWeight N (-n) = fejerWeight N n

lemma fejerMeanDensity_conj (hU : Operator.Unitary U) (ψ : H) (N : ℕ) (θ : ℝ) : starRingEnd ℂ (fejerMeanDensity U ψ N θ) = fejerMeanDensity U ψ N θ

lemma fejerMeanDensity_ofReal (hU : Operator.Unitary U) (ψ : H) (N : ℕ) (θ : ℝ) : fejerMeanDensity U ψ N θ = ↑((fejerMeanDensity U ψ N θ).re)

lemma exp_neg_mul_exp_pos (k n : ℤ) (θ : ℝ) : exp (-I * ↑k * ↑θ) * exp (I * ↑n * ↑θ) = exp (I * ↑(n - k) * ↑θ)

noncomputable def fejerDensityNNReal (U : H →L[ℂ] H) (ψ : H) (N : ℕ) (θ : ℝ) : ℝ≥0

lemma fejerDensity_eq_coe (U : H →L[ℂ] H) (ψ : H) (N : ℕ) (θ : ℝ) : ENNReal.ofReal ((1 / (2 * Real.pi)) * (fejerMeanDensity U ψ N θ).re) = ↑(fejerDensityNNReal U ψ N θ)

lemma fejerDensityNNReal_measurable (U : H →L[ℂ] H) (ψ : H) (N : ℕ) : Measurable (fejerDensityNNReal U ψ N)

lemma fejerDensityNNReal_coe (hU : Operator.Unitary U) (ψ : H) (N : ℕ) (θ : ℝ) : (↑(fejerDensityNNReal U ψ N θ) : ℝ) = (1 / (2 * Real.pi)) * (fejerMeanDensity U ψ N θ).re

lemma fejer_fourier_integral (U : H →L[ℂ] H) (ψ : H) (N : ℕ) (n : ℤ) : ∫ x in Set.Icc (0 : ℝ) (2 * Real.pi), fejerMeanDensity U ψ N x * exp (I * ↑n * ↑x) = ∑ k ∈ Finset.Icc (-(N : ℤ)) N, ↑(fejerWeight N k) * unitaryCorrelation U ψ k * ∫ x in Set.Icc (0 : ℝ) (2 * Real.pi), exp (I * ↑(n - k) * ↑x)

lemma set_integral_cexp_pos_int (n : ℤ) : ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), Complex.exp (I * ↑n * ↑θ) = (if n = 0 then ↑(2 * Real.pi) else 0)

lemma fejerMeasure_fourier (ψ : H) (N : ℕ) (n : ℤ) : ∫ θ in Set.Icc 0 (2 * Real.pi), exp (I * n * θ) ∂(fejerMeasure U hU ψ N) = (fejerWeight N n : ℂ) * unitaryCorrelation U ψ n

lemma fejerWeight_tendsto (n : ℤ) : Filter.Tendsto (fun N : ℕ => fejerWeight N n) Filter.atTop (𝓝 1)

lemma fejerWeight_tendsto_complex (n : ℤ) : Filter.Tendsto (fun N : ℕ => (fejerWeight N n : ℂ)) Filter.atTop (𝓝 1)

instance fejerMeasure_isFiniteMeasure (ψ : H) (N : ℕ) : IsFiniteMeasure (fejerMeasure U hU ψ N)

abbrev Circle

private instance circleNonempty : Nonempty Circle

private instance circleCompactSpace : CompactSpace Circle

private lemma measurableEmbedding_circleVal : MeasurableEmbedding (Subtype.val : Circle → ℝ)

noncomputable def fejerMeasureOnCircle (ψ : H) (N : ℕ) : Measure Circle

private instance fejerMeasureOnCircle_finite (ψ : H) (N : ℕ) : IsFiniteMeasure (fejerMeasureOnCircle U hU ψ N)

lemma integral_circle_eq_setIntegral (f : ℝ → ℂ) (ψ : H) (N : ℕ) : ∫ x : Circle, f x.val ∂(fejerMeasureOnCircle U hU ψ N) = ∫ θ in Set.Icc 0 (2 * Real.pi), f θ ∂(fejerMeasure U hU ψ N)

noncomputable def fejerFiniteMeasure (ψ : H) (N : ℕ) : FiniteMeasure Circle

lemma fejerFiniteMeasure_mass_toReal (ψ : H) (N : ℕ) : ((fejerFiniteMeasure U hU ψ N : Measure Circle) Set.univ).toReal = ‖ψ‖ ^ 2

lemma coordinatewise_convergent_subseq (x : ℕ → ℕ → ℝ) (B : ℕ → ℝ) (_hB : ∀ n, 0 ≤ B n) (hbnd : ∀ n k, x n k ∈ Set.Icc (-(B n)) (B n)) : ∃ (L : ℕ → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ n, Filter.Tendsto (fun k => x n (φ k)) Filter.atTop (𝓝 (L n))

lemma integral_dist_le_bcf_dist (f g : BoundedContinuousFunction Circle ℝ) (μ : ProbabilityMeasure Circle) : dist (∫ x, f x ∂μ.toMeasure) (∫ x, g x ∂μ.toMeasure) ≤ dist f g
```

### `Herglotz/Stieltjes/`

#### `CumulativeDistFun.lean` (7 decl)

```lean
noncomputable def fejerCDF (ψ : H) (N : ℕ) (x : ℝ) : ℝ

lemma fejerCDF_zero (ψ : H) (N : ℕ) : fejerCDF U ψ N 0 = 0

lemma fejerCDF_two_pi (ψ : H) (N : ℕ) : fejerCDF U ψ N (2 * Real.pi) = ‖ψ‖ ^ 2

lemma fejerCDF_monotone (hU : Operator.Unitary U) (ψ : H) (N : ℕ) : Monotone (fejerCDF U ψ N)

lemma fejerCDF_bounded (hU : Operator.Unitary U) (ψ : H) (N : ℕ) (x : ℝ) : fejerCDF U ψ N x ∈ Set.Icc 0 (‖ψ‖ ^ 2)

lemma fejerCDF_continuous (ψ : H) (N : ℕ) : Continuous (fejerCDF U ψ N)

lemma fejerCDF_eq_measure (hU : Operator.Unitary U) (ψ : H) (N : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * Real.pi) : fejerCDF U ψ N b - fejerCDF U ψ N a = (fejerMeasure U hU ψ N (Set.Ioc a b)).toReal
```

#### `Hellys.lean` (4 decl)

```lean
lemma helly_selection (F : ℕ → ℝ → ℝ) (M : ℝ) (_hM : 0 ≤ M) (h_mono : ∀ N, Monotone (F N)) (h_bnd : ∀ N x, F N x ∈ Set.Icc (0 : ℝ) M) : ∃ (G : ℝ → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ Monotone G ∧ (∀ x, G x ∈ Set.Icc (0 : ℝ) M) ∧ (∀ q : ℚ, Tendsto (fun k => F (φ k) (q : ℝ)) atTop (𝓝 (G (q : ℝ)))) ∧ (∀ x : ℝ, ContinuousAt G x → Tendsto (fun k => F (φ k) x) atTop (𝓝 (G x)))

theorem helly_selection' (F : ℕ → ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M) (h_mono : ∀ N, Monotone (F N)) (h_bnd : ∀ N x, F N x ∈ Set.Icc (0 : ℝ) M) (h_zero : ∀ N, F N 0 = 0) : ∃ (G : ℝ → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ Monotone G ∧ G 0 = 0 ∧ (∀ x, G x ∈ Set.Icc (0 : ℝ) M) ∧ (∀ q : ℚ, Tendsto (fun k => F (φ k) (q : ℝ)) atTop (𝓝 (G (q : ℝ)))) ∧ (∀ x : ℝ, ContinuousAt G x → Tendsto (fun k => F (φ k) x) atTop (𝓝 (G x)))

noncomputable def hellyLimitMeasure (G : ℝ → ℝ) (h_mono : Monotone G) : Measure ℝ

lemma hellyLimitMeasure_Ioc (G : ℝ → ℝ) (h_mono : Monotone G) (a b : ℝ) : (hellyLimitMeasure G h_mono) (Set.Ioc a b) = ENNReal.ofReal (h_mono.stieltjesFunction b - h_mono.stieltjesFunction a)
```

#### `IntegralConv.lean` (15 decl)

```lean
lemma stieltjes_eq_at_continuousAt (G : ℝ → ℝ) (h_mono : Monotone G) (x : ℝ) (hx : ContinuousAt G x) : h_mono.stieltjesFunction x = G x

private lemma sum_Ico_telescope (g : ℕ → ℝ) : ∀ n, 1 ≤ n → ∑ i ∈ Finset.Ico 1 n, (g (i + 1) - g i) = g n - g 1

private lemma cdf_mass_toReal {F : ℝ → ℝ} (hF : Monotone F) (hF_rc : ∀ x, Function.rightLim F x = F x) {a b : ℝ} (hab : a ≤ b) : (hF.stieltjesFunction.measure (Set.Ioc a b)).toReal = F b - F a

private lemma cdf_mass_tendsto {F : ℕ → ℝ → ℝ} {G : ℝ → ℝ} {φ : ℕ → ℕ} (h_mono_F : ∀ N, Monotone (F N)) (h_mono_G : Monotone G) (hF_rc : ∀ N x, Function.rightLim (F N) x = F N x) (h_conv : ∀ x, ContinuousAt G x → Tendsto (fun k => F (φ k) x) atTop (𝓝 (G x))) {a b : ℝ} (hab : a ≤ b) (ha : ContinuousAt G a) (hb : ContinuousAt G b) : Tendsto (fun k => ((h_mono_F (φ k)).stieltjesFunction.measure (Set.Ioc a b)).toReal) atTop (𝓝 ((h_mono_G.stieltjesFunction.measure (Set.Ioc a b)).toReal))

private lemma exists_cont_partition {G : ℝ → ℝ} (hG : Monotone G) {δ : ℝ} (hδ : 0 < δ) : ∃ (n : ℕ) (t : ℕ → ℝ), 0 < n ∧ t 0 = 0 ∧ t n = 2 * Real.pi ∧ (∀ i, i < n → t i < t (i + 1)) ∧ (∀ i, i < n → t (i + 1) - t i < δ) ∧ (∀ i, 0 < i → i < n → ContinuousAt G (t i))

private lemma integral_Icc_split {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] {f : ℝ → ℂ} (hf : Continuous f) {t : ℕ → ℝ} {n : ℕ} (hmono : ∀ i, i < n → t i < t (i + 1)) (hn : 0 < n) : (∫ x in Set.Icc (t 0) (t n), f x ∂μ) = (∫ x in Set.Icc (t 0) (t 1), f x ∂μ) + ∑ i ∈ Finset.Ico 1 n, ∫ x in Set.Ioc (t i) (t (i + 1)), f x ∂μ

private lemma approx_bound {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] {f : ℝ → ℂ} (hf : Continuous f) {t : ℕ → ℝ} {n : ℕ} {ε : ℝ} (hmono : ∀ i, i < n → t i < t (i + 1)) (hn : 0 < n) (hosc1 : ∀ x ∈ Set.Icc (t 0) (t 1), ‖f x - f (t 1)‖ ≤ ε) (hoscI : ∀ i, 1 ≤ i → i < n → ∀ x ∈ Set.Ioc (t i) (t (i + 1)), ‖f x - f (t (i + 1))‖ ≤ ε) : ‖(∫ x in Set.Icc (t 0) (t n), f x ∂μ) - ((μ (Set.Icc (t 0) (t 1))).toReal • f (t 1) + ∑ i ∈ Finset.Ico 1 n, (μ (Set.Ioc (t i) (t (i + 1)))).toReal • f (t (i + 1)))‖ ≤...

lemma stieltjes_leftLim_zero {F : ℝ → ℝ} (hF : Monotone F) (hzero : ∀ x ≤ (0 : ℝ), F x = 0) : Function.leftLim (hF.stieltjesFunction) 0 = 0

private lemma stieltjes_rightLim_const {F : ℝ → ℝ} (hF : Monotone F) {a M : ℝ} (hconst : ∀ x, a < x → F x = M) : Function.rightLim F a = M

private lemma stieltjes_mass_Ioc {F : ℝ → ℝ} (hF : Monotone F) {a b : ℝ} (hab : a ≤ b) : (hF.stieltjesFunction.measure (Set.Ioc a b)).toReal = Function.rightLim F b - Function.rightLim F a

private lemma stieltjes_mass_Icc0 {F : ℝ → ℝ} (hF : Monotone F) (hzero : ∀ x ≤ (0 : ℝ), F x = 0) {c : ℝ} (hc : 0 ≤ c) : (hF.stieltjesFunction.measure (Set.Icc 0 c)).toReal = Function.rightLim F c

private lemma rightLim_tendsto {F : ℕ → ℝ → ℝ} {G : ℝ → ℝ} {φ : ℕ → ℕ} (h_mono_F : ∀ N, Monotone (F N)) (hDense : Dense {x : ℝ | ContinuousAt G x}) (h_conv : ∀ x, ContinuousAt G x → Tendsto (fun k => F (φ k) x) atTop (𝓝 (G x))) {x : ℝ} (hx : ContinuousAt G x) : Tendsto (fun k => Function.rightLim (F (φ k)) x) atTop (𝓝 (G x))

lemma integral_tendsto_of_cdf_tendsto (F : ℕ → ℝ → ℝ) (G : ℝ → ℝ) (φ : ℕ → ℕ) (h_mono_F : ∀ N, Monotone (F N)) (h_mono_G : Monotone G) (M : ℝ) (hM : 0 ≤ M) (h_bnd : ∀ N x, F N x ∈ Set.Icc 0 M) (h_bnd_G : ∀ x, G x ∈ Set.Icc 0 M) (h_conv : ∀ x, ContinuousAt G x → Tendsto (fun k => F (φ k) x) atTop (𝓝 (G x))) (f : ℝ → ℂ) (hf_cont : Continuous f) (_hf_bnd : ∃ C, ∀ x, ‖f x‖ ≤ C) (h_supp_F : ∀ N, F N 0 = 0 ∧ ∀ x, 2 * Real.pi < x → F N x = M) (h_supp_G : G 0 = 0 ∧ ∀ x, 2 * Real.pi < x → G x = M) : T...

lemma fourier_integral_tendsto_of_cdf_tendsto (F : ℕ → ℝ → ℝ) (G : ℝ → ℝ) (φ : ℕ → ℕ) (h_mono_F : ∀ N, Monotone (F N)) (h_mono_G : Monotone G) (M : ℝ) (hM : 0 ≤ M) (h_bnd : ∀ N x, F N x ∈ Set.Icc 0 M) (h_bnd_G : ∀ x, G x ∈ Set.Icc 0 M) (h_conv : ∀ x, ContinuousAt G x → Tendsto (fun k => F (φ k) x) atTop (𝓝 (G x))) (h_supp_F : ∀ N, F N 0 = 0 ∧ ∀ x, 2 * Real.pi < x → F N x = M) (h_supp_G : G 0 = 0 ∧ ∀ x, 2 * Real.pi < x → G x = M) (n : ℤ) : Tendsto (fun k => ∫ θ in Set.Icc 0 (2 * Real.pi), exp ...

lemma exists_partition_avoiding_countable {S : Set ℝ} (hS : S.Countable) {a b : ℝ} (hab : a < b) (ha : a ∉ S) (hb : b ∉ S) {δ : ℝ} (hδ : 0 < δ) : ∃ (n : ℕ) (t : ℕ → ℝ), 0 < n ∧ t 0 = a ∧ t n = b ∧ (∀ i < n, t i < t (i + 1)) ∧ (∀ i < n, t (i + 1) - t i < δ) ∧ (∀ i ≤ n, t i ∉ S)
```

### `Kernel/`

#### `Arctan.lean` (8 decl)

```lean
lemma lorentzian_arctan_integral (s a b ε : ℝ) (hε : ε > 0) : ∫ t in a..b, ε / ((s - t)^2 + ε^2) = Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)

noncomputable def arctanRecovery (ε : ℝ) (a b : ℝ) (ω : ℝ) : ℝ

lemma tendsto_pos_div_zero_atTop {c : ℝ} (hc : 0 < c) : Tendsto (fun ε => c / ε) (𝓝[>] (0 : ℝ)) atTop

lemma tendsto_neg_div_zero_atBot {c : ℝ} (hc : c < 0) : Tendsto (fun ε => c / ε) (𝓝[>] (0 : ℝ)) atBot

lemma arctanRecovery_tendsto_zero_of_lt {a b ω : ℝ} (hω : ω < a) {b' : ℝ} (hab : a ≤ b') (hbb : b' = b) : Tendsto (fun ε => arctanRecovery ε a b ω) (𝓝[>] 0) (𝓝 0)

lemma arctanRecovery_tendsto_zero_of_lt' {a b ω : ℝ} (hω : ω < a) (hab : a < b) : Tendsto (fun ε => arctanRecovery ε a b ω) (𝓝[>] 0) (𝓝 0)

lemma arctan_indicator_limit (a b s : ℝ) (hab : a < b) (hs_a : s ≠ a) (hs_b : s ≠ b) : Tendsto (fun ε : ℝ => (1 / Real.pi) * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε))) (𝓝[>] 0) (𝓝 (Set.indicator (Set.Ioc a b) 1 s))

lemma arctan_kernel_bound (a b s ε : ℝ) (_hε : ε > 0) : |(1 / Real.pi) * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε))| ≤ 1
```

#### `Defs.lean` (4 decl)

```lean
structure OffRealAxis where val : ℂ im_ne_zero : val.im ≠ 0

def offRealPoint (t : ℝ) (ε : ℝ) (hε : ε > 0) : OffRealAxis

def offRealPointNeg (t : ℝ) (ε : ℝ) (hε : ε > 0) : OffRealAxis

noncomputable def resolvent_integrand (z : ℂ) : ℝ → ℂ
```

#### `Lorentzian.lean` (6 decl)

```lean
private lemma lorentzian_nonneg (s t ε : ℝ) (hε : ε > 0) : 0 ≤ ε / ((s - t)^2 + ε^2)

private lemma lorentzian_bound (s t ε : ℝ) (hε : ε > 0) : ε / ((s - t)^2 + ε^2) ≤ 1 / ε

private lemma lorentzian_total_integral (t ε : ℝ) (hε : ε > 0) : ∫ s, ε / ((s - t)^2 + ε^2) = Real.pi

private lemma lorentzian_concentration (t δ : ℝ) (hδ : δ > 0) : Tendsto (fun ε : ℝ => ∫ s in Set.Iic (t - δ) ∪ Set.Ici (t + δ), ε / ((s - t)^2 + ε^2)) (𝓝[>] 0) (𝓝 0)

private lemma lorentzian_smul_integrable (f : ℝ → ℂ) (hf_int : Integrable f) (t : ℝ) (ε : ℝ) (hε : ε > 0) : Integrable (fun s => (ε / ((s - t)^2 + ε^2)) • f s)

lemma lorentzian_approx_delta (f : ℝ → ℂ) (hf_cont : Continuous f) (hf_int : Integrable f) (t : ℝ) : Tendsto (fun ε : ℝ => (1 / Real.pi) • ∫ s, (ε / ((s - t)^2 + ε^2)) • f s) (𝓝[>] 0) (𝓝 (f t))
```

### `Kernel/Poisson/`

#### `Basic.lean` (1 decl)

```lean
theorem poissonKernel_fourier {ε : ℝ} (hε : 0 < ε) (t : ℝ) : ∫ x, (poissonKernel ε x : ℂ) * exp (I * ↑x * ↑t) = exp (-(↑ε * ↑|t|) : ℂ)
```

#### `Lemmas.lean` (15 decl)

```lean
noncomputable def poissonKernel (ε : ℝ) (x : ℝ) : ℝ

lemma poissonKernel_nonneg {ε : ℝ} (hε : 0 < ε) (x : ℝ) : 0 ≤ poissonKernel ε x

lemma sq_add_sq_pos {ε : ℝ} (hε : 0 < ε) (x : ℝ) : 0 < x ^ 2 + ε ^ 2

lemma poissonKernel_continuous {ε : ℝ} (hε : 0 < ε) : Continuous (poissonKernel ε)

lemma poissonKernel_measurable {ε : ℝ} (hε : 0 < ε) : Measurable (poissonKernel ε)

lemma continuous_inv_one_add_sq : Continuous (fun x : ℝ => (1 + x ^ 2)⁻¹)

lemma poissonKernel_integrable {ε : ℝ} (hε : 0 < ε) : Integrable (poissonKernel ε) volume

lemma poissonKernel_integral_eq_one {ε : ℝ} (hε : 0 < ε) : ∫ x, poissonKernel ε x = 1

private lemma norm_cexp_neg_mul_ofReal (a : ℂ) (t : ℝ) : ‖cexp (-(a * ↑t))‖ = Real.exp (-a.re * t)

private lemma tendsto_cexp_neg_mul_ofReal_atTop {a : ℂ} (ha : 0 < a.re) : Tendsto (fun t : ℝ => cexp (-(a * ↑t))) atTop (𝓝 0)

private lemma hasDerivAt_antideriv_cexp {a : ℂ} (ha_ne : a ≠ 0) (t : ℝ) : HasDerivAt (fun t : ℝ => -a⁻¹ * cexp (-(a * ↑t))) (cexp (-(a * ↑t))) t

private lemma inv_add_conj_inv {ε ξ : ℝ} (hε : 0 < ε) : (↑ε - ↑ξ * I)⁻¹ + (↑ε + ↑ξ * I)⁻¹ = ((2 * ε / (ξ ^ 2 + ε ^ 2) : ℝ) : ℂ)

private lemma setIntegral_Iic_comp_neg (f : ℝ → ℂ) : ∫ t in Set.Iic (0 : ℝ), f t = ∫ u in Set.Ioi (0 : ℝ), f (-u)

lemma integrable_two_sided_exp {ε : ℝ} (hε : 0 < ε) (ξ : ℝ) : Integrable (fun t : ℝ => cexp (-(↑ε * ↑|t|)) * cexp (I * ↑ξ * ↑t)) volume

lemma fourier_two_sided_exp {ε : ℝ} (hε : 0 < ε) (ξ : ℝ) : ∫ t : ℝ, cexp (-(↑ε * ↑|t|)) * cexp (I * ↑ξ * ↑t) = ((2 * ε / (ξ ^ 2 + ε ^ 2) : ℝ) : ℂ)
```

### `Kernel/`

#### `Resolvent.lean` (6 decl)

```lean
lemma resolvent_integrand_bound (z : ℂ) (hz : z.im ≠ 0) (s : ℝ) : ‖((s : ℂ) - z)⁻¹‖ ≤ 1 / |z.im|

lemma resolvent_kernel_im (s t ε : ℝ) (hε : ε > 0) : (((s : ℂ) - (↑t + ↑ε * I))⁻¹).im = ε / ((s - t)^2 + ε^2)

lemma resolvent_kernel_diff (s t ε : ℝ) (hε : ε > 0) : ((s : ℂ) - (↑t + ↑ε * I))⁻¹ - ((s : ℂ) - (↑t - ↑ε * I))⁻¹ = (2 * ε * I) / ((s - t)^2 + ε^2 : ℂ)

lemma resolvent_kernel_diff_normalized (s t ε : ℝ) (hε : ε > 0) : (1 / (2 * Real.pi * I)) * (((s : ℂ) - (↑t + ↑ε * I))⁻¹ - ((s : ℂ) - (↑t - ↑ε * I))⁻¹) = ↑(ε / ((s - t)^2 + ε^2) / Real.pi)

lemma cauchy_kernel_norm_le_of_abs_ge {z : ℂ} {R : ℝ} (hR : |z.re| < R) {l : ℝ} (hl : R ≤ |l|) : ‖((l : ℂ) - z)⁻¹‖ ≤ 1 / (R - |z.re|)

lemma norm_setIntegral_cauchy_kernel_outside_le {ν : Measure ℝ} [IsFiniteMeasure ν] {z : ℂ} {R : ℝ} (hR : |z.re| < R) : ‖∫ l in (Set.Ioc (-R) R)ᶜ, ((l : ℂ) - z)⁻¹ ∂ν‖ ≤ (ν Set.univ).toReal / (R - |z.re|)
```

### `Mathlib/`

#### `CharFunBridge.lean` (17 decl)

```lean
lemma integrable_char (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) : Integrable (fun ω : ℝ => cexp (I * ω * t)) μ

lemma charFun_real (μ : Measure ℝ) (t : ℝ) : charFun μ t = ∫ ω, cexp (I * ω * t) ∂μ

lemma fourier_neg_eq_conj (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) : (∫ ω, cexp (I * ω * ((-t : ℝ) : ℂ)) ∂μ) = starRingEnd ℂ (∫ ω, cexp (I * ω * t) ∂μ)

theorem measure_ext_of_fourier {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : ∀ t : ℝ, ∫ ω, cexp (I * ω * t) ∂μ = ∫ ω, cexp (I * ω * t) ∂ν) : μ = ν

theorem measure_add_ext_of_fourier {μ₁ ν₁ μ₂ ν₂ : Measure ℝ} [IsFiniteMeasure μ₁] [IsFiniteMeasure ν₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν₂] (h : ∀ t : ℝ, (∫ ω, cexp (I * ω * t) ∂μ₁) + ∫ ω, cexp (I * ω * t) ∂ν₂ = (∫ ω, cexp (I * ω * t) ∂μ₂) + ∫ ω, cexp (I * ω * t) ∂ν₁) : μ₁ + ν₂ = μ₂ + ν₁

theorem measure_sum_ext_of_fourier {n m : ℕ} {μ : Fin n → Measure ℝ} {ν : Fin m → Measure ℝ} [∀ i, IsFiniteMeasure (μ i)] [∀ j, IsFiniteMeasure (ν j)] (h : ∀ t : ℝ, ∑ i, ∫ ω, cexp (I * ω * t) ∂(μ i) = ∑ j, ∫ ω, cexp (I * ω * t) ∂(ν j)) : ∑ i, μ i = ∑ j, ν j

private lemma integrable_of_bounded {ρ : Measure ℝ} [IsFiniteMeasure ρ] {F : ℝ → ℂ} (hF : Measurable F) {C : ℝ} (hC : ∀ ω, ‖F ω‖ ≤ C) : Integrable F ρ

private lemma measurable_char (t : ℝ) : Measurable fun ω : ℝ => cexp (I * ω * t)

private lemma norm_char_le_one (t ω : ℝ) : ‖cexp (I * ω * t)‖ ≤ 1

private lemma toNNReal_split (x : ℝ) : ((x.toNNReal : ℝ) : ℂ) - (((-x).toNNReal : ℝ) : ℂ) = (x : ℂ)

private lemma integral_const_mul' (r : ℂ) (φ : ℝ → ℂ) (ρ : Measure ℝ) : ∫ ω, r * φ ω ∂ρ = r * ∫ ω, φ ω ∂ρ

private lemma conj_char_mul (t ω : ℝ) (z : ℂ) : (starRingEnd ℂ) (cexp (I * ω * ((-t : ℝ) : ℂ)) * z) = cexp (I * ω * (t : ℂ)) * (starRingEnd ℂ) z

private lemma conj_integral_char_ofReal (v : ℝ → ℝ) (ρ : Measure ℝ) (t : ℝ) : (starRingEnd ℂ) (∫ ω, cexp (I * ω * ((-t : ℝ) : ℂ)) * (v ω : ℂ) ∂ρ) = ∫ ω, cexp (I * ω * (t : ℂ)) * (v ω : ℂ) ∂ρ

private theorem combination_ext_zero_real {ι : Type*} [Fintype ι] (M : ι → Measure ℝ) [∀ x, IsFiniteMeasure (M x)] (r : ι → ℝ → ℝ) (hr_meas : ∀ x, Measurable (r x)) (hr_bdd : ∀ x, ∃ C, ∀ ω, |r x ω| ≤ C) (h : ∀ t : ℝ, ∑ x, ∫ ω, cexp (I * ω * t) * (r x ω : ℂ) ∂(M x) = 0) {g : ℝ → ℂ} (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) : ∑ x, ∫ ω, g ω * (r x ω : ℂ) ∂(M x) = 0

theorem signed_combination_ext {n m : ℕ} (a : Fin n → ℝ) (μ : Fin n → Measure ℝ) (b : Fin m → ℝ) (ν : Fin m → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ j, IsFiniteMeasure (ν j)] (h : ∀ t : ℝ, ∑ i, (a i : ℂ) * ∫ ω, cexp (I * ω * t) ∂(μ i) = ∑ j, (b j : ℂ) * ∫ ω, cexp (I * ω * t) ∂(ν j)) {g : ℝ → ℂ} (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) : ∑ i, (a i : ℂ) * ∫ ω, g ω ∂(μ i) = ∑ j, (b j : ℂ) * ∫ ω, g ω ∂(ν j)

theorem integral_combination_ext {n m : ℕ} (c : Fin n → ℂ) (μ : Fin n → Measure ℝ) (f : Fin n → ℝ → ℂ) (d : Fin m → ℂ) (ν : Fin m → Measure ℝ) (k : Fin m → ℝ → ℂ) [∀ i, IsFiniteMeasure (μ i)] [∀ j, IsFiniteMeasure (ν j)] (hf_meas : ∀ i, Measurable (f i)) (hf_bdd : ∀ i, ∃ C, ∀ ω, ‖f i ω‖ ≤ C) (hk_meas : ∀ j, Measurable (k j)) (hk_bdd : ∀ j, ∃ C, ∀ ω, ‖k j ω‖ ≤ C) (heq : ∀ t : ℝ, ∑ i, c i * ∫ ω, cexp (I * ω * t) * f i ω ∂(μ i) = ∑ j, d j * ∫ ω, cexp (I * ω * t) * k j ω ∂(ν j)) {g : ℝ → ℂ} (hg_m...

theorem integral_combination_ext' {n m : ℕ} (c : Fin n → ℂ) (μ : Fin n → Measure ℝ) (d : Fin m → ℂ) (ν : Fin m → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ j, IsFiniteMeasure (ν j)] (heq : ∀ t : ℝ, ∑ i, c i * ∫ ω, cexp (I * ω * t) ∂(μ i) = ∑ j, d j * ∫ ω, cexp (I * ω * t) ∂(ν j)) {g : ℝ → ℂ} (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) : ∑ i, c i * ∫ ω, g ω ∂(μ i) = ∑ j, d j * ∫ ω, g ω ∂(ν j)
```

### `Mathlib/MeasureTheory/Integral/`

#### `Basic.lean` (9 decl)

```lean
lemma integral_exp_neg_Ioc (n : ℕ) : ∫ x in (0 : ℝ)..n, Real.exp (-x) = 1 - Real.exp (-n)

lemma integrableOn_exp_neg : IntegrableOn (fun t => Real.exp (-t)) (Set.Ici 0) volume

lemma integral_exp_neg_eq_one : ∫ t in Set.Ici (0 : ℝ), Real.exp (-t) = 1

lemma integrableOn_exp_neg_Ioi : IntegrableOn (fun t => Real.exp (-t)) (Set.Ioi 0) volume

lemma integrable_exp_decay_continuous (f : ℝ → E) (hf_cont : Continuous f) (C : ℝ) (hC : ∀ t ≥ 0, ‖f t‖ ≤ C) : IntegrableOn (fun t => Real.exp (-t) • f t) (Set.Ici 0) volume

lemma norm_integral_exp_decay_le (f : ℝ → E) (hf_cont : Continuous f) (C : ℝ) (hC : ∀ t ≥ 0, ‖f t‖ ≤ C) (_ : 0 ≤ C) : ‖∫ t in Set.Ici 0, Real.exp (-t) • f t‖ ≤ C

lemma hasDerivAt_integral_of_exp_decay (f : ℝ → ℝ → E) (hf_cont : Continuous (Function.uncurry f)) (hf_deriv : ∀ t s, HasDerivAt (f · s) (deriv (f · s) t) t) (hf'_cont : ∀ t, Continuous (fun s => deriv (f · s) t)) (C : ℝ) (hC : ∀ t s, s ≥ 0 → ‖f t s‖ ≤ C) (hC' : ∀ t s, s ≥ 0 → ‖deriv (f · s) t‖ ≤ C) (t : ℝ) : HasDerivAt (fun τ => ∫ s in Set.Ici 0, Real.exp (-s) • f τ s) (∫ s in Set.Ici 0, Real.exp (-s) • deriv (f · s) t) t

lemma fubini_Ioc (f : ℝ → ℝ → E) (a b c d : ℝ) (hf : Integrable (Function.uncurry f) ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc c d)))) : ∫ x in Set.Ioc a b, ∫ y in Set.Ioc c d, f x y = ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b, f x y

lemma tendsto_integral_of_dominated_convergence (f : ℕ → ℝ → E) (g : ℝ → E) (bound : ℝ → ℝ) (S : Set ℝ) (hf_meas : ∀ n, AEStronglyMeasurable (f n) (volume.restrict S)) (hbound : ∀ n, ∀ᵐ x ∂(volume.restrict S), ‖f n x‖ ≤ bound x) (hbound_int : Integrable bound (volume.restrict S)) (hf_tendsto : ∀ᵐ x ∂(volume.restrict S), Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Tendsto (fun n => ∫ x in S, f n x) atTop (𝓝 (∫ x in S, g x))
```

### `Operator/`

#### `Symmetric.lean` (33 decl)

```lean
structure SymmetricOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where toLinearPMap : H →ₗ.[ℂ] H dense : Dense (toLinearPMap.domain : Set H) symmetric : toLinearPMap.IsFormalAdjoint toLinearPMap

def domain (A : SymmetricOperator H) : Submodule ℂ H

def apply (A : SymmetricOperator H) (ψ : H) (hψ : ψ ∈ A.domain) : H

instance : CoeFun (SymmetricOperator H) (fun A => A.domain → H)

def toDomainElt (A : SymmetricOperator H) (ψ : H) (hψ : ψ ∈ A.domain) : A.domain

lemma symmetric' (A : SymmetricOperator H) {ψ φ : H} (hψ : ψ ∈ A.domain) (hφ : φ ∈ A.domain) : ⟪A ⬝ ψ ⊢ hψ, φ⟫_ℂ = ⟪ψ, A ⬝ φ ⊢ hφ⟫_ℂ

lemma inner_self_im_eq_zero (A : SymmetricOperator H) {ψ : H} (hψ : ψ ∈ A.domain) : (⟪ψ, A ⬝ ψ ⊢ hψ⟫_ℂ).im = 0

lemma inner_self_eq_re (A : SymmetricOperator H) {ψ : H} (hψ : ψ ∈ A.domain) : ⟪ψ, A ⬝ ψ ⊢ hψ⟫_ℂ = (⟪ψ, A ⬝ ψ ⊢ hψ⟫_ℂ).re

lemma apply_add (A : SymmetricOperator H) {ψ φ : H} (hψ : ψ ∈ A.domain) (hφ : φ ∈ A.domain) : A.apply (ψ + φ) (A.domain.add_mem hψ hφ) = A.apply ψ hψ + A.apply φ hφ

lemma apply_smul (A : SymmetricOperator H) {ψ : H} (c : ℂ) (hψ : ψ ∈ A.domain) : A.apply (c • ψ) (A.domain.smul_mem c hψ) = c • A.apply ψ hψ

lemma apply_sub (A : SymmetricOperator H) {ψ φ : H} (hψ : ψ ∈ A.domain) (hφ : φ ∈ A.domain) : A.apply (ψ - φ) (A.domain.sub_mem hψ hφ) = A.apply ψ hψ - A.apply φ hφ

lemma apply_smul_real (A : SymmetricOperator H) {ψ : H} (r : ℝ) (hψ : ψ ∈ A.domain) : A.apply ((r : ℂ) • ψ) (A.domain.smul_mem (r : ℂ) hψ) = (r : ℂ) • A.apply ψ hψ

structure DomainConditions (A B : SymmetricOperator H) (ψ : H) where hψ_A : ψ ∈ A.domain hψ_B : ψ ∈ B.domain hBψ_A : B.apply ψ hψ_B ∈ A.domain hAψ_B : A.apply ψ hψ_A ∈ B.domain

def Aψ (h : DomainConditions A B ψ) : H

def Bψ (h : DomainConditions A B ψ) : H

def ABψ (h : DomainConditions A B ψ) : H

def BAψ (h : DomainConditions A B ψ) : H

def commutatorAt (A B : SymmetricOperator H) (ψ : H) (h : DomainConditions A B ψ) : H

def anticommutatorAt (A B : SymmetricOperator H) (ψ : H) (h : DomainConditions A B ψ) : H

lemma commutator_re_eq_zero (A B : SymmetricOperator H) (ψ : H) (h : DomainConditions A B ψ) : (⟪ψ, commutatorAt A B ψ h⟫_ℂ).re = 0

lemma anticommutator_im_eq_zero (A B : SymmetricOperator H) (ψ : H) (h : DomainConditions A B ψ) : (⟪ψ, anticommutatorAt A B ψ h⟫_ℂ).im = 0

noncomputable def expectation (A : SymmetricOperator H) (ψ : H) (_ : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) : ℝ

noncomputable def shiftedApply (A : SymmetricOperator H) (ψ : H) (φ : H) (h_norm : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) (hφ : φ ∈ A.domain) : H

lemma shifted_symmetric (A : SymmetricOperator H) (ψ : H) (h_norm : ‖ψ‖ = 1) (hψ_dom : ψ ∈ A.domain) {φ₁ φ₂ : H} (hφ₁ : φ₁ ∈ A.domain) (hφ₂ : φ₂ ∈ A.domain) : ⟪A.shiftedApply ψ φ₁ h_norm hψ_dom hφ₁, φ₂⟫_ℂ = ⟪φ₁, A.shiftedApply ψ φ₂ h_norm hψ_dom hφ₂⟫_ℂ

noncomputable def variance (A : SymmetricOperator H) (ψ : H) (h_norm : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) : ℝ

noncomputable def stdDev (A : SymmetricOperator H) (ψ : H) (h_norm : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) : ℝ

lemma variance_nonneg (A : SymmetricOperator H) (ψ : H) (h_norm : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) : 0 ≤ A.variance ψ h_norm hψ

lemma stdDev_nonneg (A : SymmetricOperator H) (ψ : H) (h_norm : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) : 0 ≤ A.stdDev ψ h_norm hψ

structure ShiftedDomainConditions (A B : SymmetricOperator H) (ψ : H) extends DomainConditions A B ψ where h_norm : ‖ψ‖ = 1

noncomputable def A'ψ (h : ShiftedDomainConditions A B ψ) : H

noncomputable def B'ψ (h : ShiftedDomainConditions A B ψ) : H

lemma B'ψ_in_A_domain (h : ShiftedDomainConditions A B ψ) : h.B'ψ ∈ A.domain

lemma A'ψ_in_B_domain (h : ShiftedDomainConditions A B ψ) : h.A'ψ ∈ B.domain
```

### `Operator/Unitary/`

#### `Basic.lean` (17 decl)

```lean
def Unitary (U : H →L[ℂ] H) : Prop

lemma mem_unitary_iff_Unitary (U : H →L[ℂ] H) : U ∈ unitary (H →L[ℂ] H) ↔ Unitary U

lemma Unitary.inner_map_map {U : H →L[ℂ] H} (hU : Unitary U) (x y : H) : ⟪U x, U y⟫_ℂ = ⟪x, y⟫_ℂ

lemma Unitary.norm_map {U : H →L[ℂ] H} (hU : Unitary U) (x : H) : ‖U x‖ = ‖x‖

lemma Unitary.injective {U : H →L[ℂ] H} (hU : Unitary U) : Function.Injective U

lemma Unitary.surjective {U : H →L[ℂ] H} (hU : Unitary U) : Function.Surjective U

lemma Unitary.isUnit {U : H →L[ℂ] H} (hU : Unitary U) : IsUnit U

def ContinuousLinearMap.IsNormal (T : H →L[ℂ] H) : Prop

lemma unitary_sub_scalar_isNormal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (U : E →L[ℂ] E) (hU : U.adjoint * U = 1 ∧ U * U.adjoint = 1) (w : ℂ) : (U - w • 1).adjoint * (U - w • 1) = (U - w • 1) * (U - w • 1).adjoint

lemma unitary_sub_scalar_isNormal' {U : H →L[ℂ] H} (hU : Unitary U) (w : ℂ) : (U - w • 1).adjoint * (U - w • 1) = (U - w • 1) * (U - w • 1).adjoint

lemma dense_range_of_orthogonal_trivial {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (T : F →L[ℂ] F) (h : ∀ y, (∀ x, ⟪T x, y⟫_ℂ = 0) → y = 0) : Dense (Set.range T)

lemma surjective_of_isClosed_range_of_dense {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (T : E →L[ℂ] F) (hClosed : IsClosed (Set.range T)) (hDense : Dense (Set.range T)) : Function.Surjective T

lemma isUnit_bounded_below [Nontrivial H] {T : H →L[ℂ] H} (hT : IsUnit T) : ∃ c > 0, ∀ φ, ‖T φ‖ ≥ c * ‖φ‖

lemma normal_bounded_below_surjective {T : H →L[ℂ] H} (hT : T.adjoint.comp T = T.comp T.adjoint) (c : ℝ) (hc_pos : c > 0) (hc_bound : ∀ φ, ‖T φ‖ ≥ c * ‖φ‖) : Function.Surjective T

lemma normal_bounded_below_isUnit [Nontrivial H] {T : H →L[ℂ] H} (hT : T.adjoint * T = T * T.adjoint) (c : ℝ) (hc_pos : c > 0) (hc_bound : ∀ φ, ‖T φ‖ ≥ c * ‖φ‖) : IsUnit T

lemma unitary_not_isUnit_approx_eigenvalue [Nontrivial H] {U : H →L[ℂ] H} (hU : Unitary U) (w : ℂ) (h_not : ¬IsUnit (U - w • ContinuousLinearMap.id ℂ H)) : ∀ ε > 0, ∃ φ, ‖φ‖ = 1 ∧ ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ < ε

lemma unitary_not_approx_eigenvalue_isUnit [Nontrivial H] {U : H →L[ℂ] H} (hU : Unitary U) (w : ℂ) (h_not : ¬∀ ε > 0, ∃ φ, ‖φ‖ = 1 ∧ ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ < ε) : IsUnit (U - w • ContinuousLinearMap.id ℂ H)
```

#### `Bridge.lean` (4 decl)

```lean
lemma mem_unitary_of_inner_map_map_of_surjective {U : H →L[ℂ] H} (hinner : ∀ ψ φ : H, ⟪U ψ, U φ⟫_ℂ = ⟪ψ, φ⟫_ℂ) (hsurj : Function.Surjective U) : U ∈ unitary (H →L[ℂ] H)

lemma mem_unitary_iff_inner_map_map_and_surjective {U : H →L[ℂ] H} : U ∈ unitary (H →L[ℂ] H) ↔ (∀ ψ φ : H, ⟪U ψ, U φ⟫_ℂ = ⟪ψ, φ⟫_ℂ) ∧ Function.Surjective U

lemma isStarNormal_of_inner_map_map_of_surjective {U : H →L[ℂ] H} (hinner : ∀ ψ φ : H, ⟪U ψ, U φ⟫_ℂ = ⟪ψ, φ⟫_ℂ) (hsurj : Function.Surjective U) : IsStarNormal U

lemma spectrum_subset_circle_of_inner_map_map_of_surjective {U : H →L[ℂ] H} (hinner : ∀ ψ φ : H, ⟪U ψ, U φ⟫_ℂ = ⟪ψ, φ⟫_ℂ) (hsurj : Function.Surjective U) : spectrum ℂ U ⊆ Metric.sphere (0 : ℂ) 1
```

#### `Powers.lean` (11 decl)

```lean
noncomputable def unitaryZpow : ℤ → (H →L[ℂ] H) | (n : ℕ)          => U ^ n | (Int.negSucc n)   => U.adjoint ^ (n + 1)

lemma unitaryZpow_zero : unitaryZpow U 0 = 1

lemma unitaryZpow_one : unitaryZpow U 1 = U

lemma unitaryZpow_neg_one : unitaryZpow U (-1) = U.adjoint

lemma unitaryZpow_neg (n : ℕ) (hn : 0 < n) : unitaryZpow U (-↑n) = U.adjoint ^ n

private lemma unit_inv_val : ((hU.isUnit.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) = U.adjoint

private lemma unitaryZpow_eq_unit_zpow (k : ℤ) : unitaryZpow U k = ↑(hU.isUnit.unit ^ k)

lemma unitaryZpow_add (hU : Operator.Unitary U) (m n : ℤ) : unitaryZpow U (m + n) = (unitaryZpow U m).comp (unitaryZpow U n)

private lemma pow_unitary_inner (V : H →L[ℂ] H) (hV : Operator.Unitary V) (a : ℕ) (x y : H) : ⟪(V ^ a) x, (V ^ a) y⟫_ℂ = ⟪x, y⟫_ℂ

private lemma unitaryZpow_inner_map_map (hU : Operator.Unitary U) (k : ℤ) (x y : H) : ⟪unitaryZpow U k x, unitaryZpow U k y⟫_ℂ = ⟪x, y⟫_ℂ

lemma unitaryZpow_inner_shift (hU : Operator.Unitary U) (m n : ℤ) (ψ : H) : ⟪unitaryZpow U m ψ, unitaryZpow U n ψ⟫_ℂ = ⟪ψ, unitaryZpow U (n - m) ψ⟫_ℂ
```

### `PositiveDefinite/`

#### `Basic.lean` (30 decl)

```lean
def IsPositiveDefinite (f : ℝ → ℂ) : Prop

def PositiveDefiniteContinuous (f : ℝ → ℂ) : Prop

lemma tendsto_nhdsWithin_Ici_of_tendsto_nhdsWithin_Ioi {f : ℝ → ℝ} {x : ℝ} (h : Tendsto f (𝓝[>] x) (𝓝 (f x))) : ContinuousWithinAt f (Set.Ici x) x

lemma pd_at_zero_nonneg (hf : IsPositiveDefinite f) : 0 ≤ (f 0).re

lemma pd_two_point_add (hf : IsPositiveDefinite f) (t : ℝ) : 0 ≤ 2 * (f 0).re + (f t + f (-t)).re

lemma pd_two_point_sub (hf : IsPositiveDefinite f) (t : ℝ) : 0 ≤ 2 * (f 0).re - (f t + f (-t)).re

lemma pd_two_point_I (hf : IsPositiveDefinite f) (t : ℝ) : 0 ≤ (f 0 + I * f (-t) + (-(I) * f t + f 0)).re

lemma pd_two_point_neg_I (hf : IsPositiveDefinite f) (t : ℝ) : 0 ≤ (f 0 + -(I * f (-t)) + (I * f t + f 0)).re

def IsHermitian (f : ℝ → ℂ) : Prop

lemma hermitian_at_zero_im (hH : IsHermitian f) : (f 0).im = 0

lemma hermitian_at_zero_ofReal (hH : IsHermitian f) : f 0 = ↑((f 0).re)

lemma pd_hermitian_at_zero (hf : IsPositiveDefinite f) (hH : IsHermitian f) : f 0 = ↑((f 0).re) ∧ 0 ≤ (f 0).re

lemma hermitian_sum_eq_two_re (hH : IsHermitian f) (t : ℝ) : f t + f (-t) = ↑(2 * (f t).re)

lemma hermitian_diff_eq_two_im (hH : IsHermitian f) (t : ℝ) : f t - f (-t) = ↑(2 * (f t).im) * I

lemma pd_hermitian_re_le (hf : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) : (f t).re ≤ (f 0).re

lemma pd_hermitian_re_neg_le (hf : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) : -(f 0).re ≤ (f t).re

lemma pd_hermitian_re_abs_le (hf : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) : |(f t).re| ≤ (f 0).re

lemma pd_hermitian_im_le (hf : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) : (f t).im ≤ (f 0).re

lemma pd_hermitian_im_neg_le (hf : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) : -(f 0).re ≤ (f t).im

lemma pd_hermitian_im_abs_le (hf : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) : |(f t).im| ≤ (f 0).re

private lemma conj_mul_self_re (z : ℂ) : (starRingEnd ℂ z * z).re = ‖z‖ ^ 2

private lemma conj_mul_self_im (z : ℂ) : (starRingEnd ℂ z * z).im = 0

private lemma conj_mul_div_norm (z : ℂ) (hz : z ≠ 0) : starRingEnd ℂ z * z / ↑‖z‖ = ↑‖z‖

lemma pd_hermitian_norm_bound (hf : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) : ‖f t‖ ≤ (f 0).re

lemma pd_hermitian_norm_sq_bound (hf : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) : ‖f t‖ ^ 2 ≤ (f 0).re ^ 2

def pdVariance (f : ℝ → ℂ) (h : ℝ) : ℝ

lemma pdVariance_nonneg (hf : IsPositiveDefinite f) (hH : IsHermitian f) (h : ℝ) : 0 ≤ pdVariance f h

lemma pdVariance_zero (_hH : IsHermitian f) : pdVariance f 0 = 0

lemma pdVariance_le (hf : IsPositiveDefinite f) (hH : IsHermitian f) (h : ℝ) : pdVariance f h ≤ 2 * (f 0).re

lemma pdVariance_tendsto_zero (_hf : IsPositiveDefinite f) (_hH : IsHermitian f) (hcont : ContinuousAt f 0) : Filter.Tendsto (pdVariance f) (𝓝 0) (𝓝 0)
```

#### `Unitary.lean` (4 decl)

```lean
noncomputable def unitaryCorrelation (ψ : H) (n : ℤ) : ℂ

lemma unitaryCorrelation_zero (ψ : H) : unitaryCorrelation U ψ 0 = ↑(‖ψ‖ ^ 2)

lemma unitaryCorrelation_neg (hU : Operator.Unitary U) (ψ : H) (n : ℤ) : unitaryCorrelation U ψ (-n) = starRingEnd ℂ (unitaryCorrelation U ψ n)

lemma unitaryCorrelation_positive_definite (hU : Operator.Unitary U) (ψ : H) (N : ℕ) (α : Fin N → ℂ) : 0 ≤ (∑ j : Fin N, ∑ k : Fin N, starRingEnd ℂ (α j) * α k * unitaryCorrelation U ψ (↑k - ↑j)).re
```

### `ProjValMeasure/`

#### `PdInterface.lean` (9 decl)

```lean
private lemma unitaryCorrelation_smul [CompleteSpace H] (c : ℂ) (ψ : H) (n : ℤ) : unitaryCorrelation U (c • ψ) n = ↑(‖c‖ ^ 2) * unitaryCorrelation U ψ n

lemma inner_op_eq_polarization (T : H →L[ℂ] H) (ψ φ : H) : ⟪T ψ, φ⟫_ℂ = (1 / 4 : ℂ) * ( ⟪T (ψ + φ), ψ + φ⟫_ℂ - ⟪T (ψ - φ), ψ - φ⟫_ℂ - I * ⟪T (ψ + I • φ), ψ + I • φ⟫_ℂ + I * ⟪T (ψ - I • φ), ψ - I • φ⟫_ℂ )

noncomputable def crossInner (g : ℝ → ℂ) (ψ φ : H) : ℂ

lemma crossInner_eq_inner_of_diag {g : ℝ → ℂ} {T : H →L[ℂ] H} (hdiag : ∀ z : H, ⟪T z, z⟫_ℂ = ∫ θ, g θ ∂(μ z)) (ψ φ : H) : crossInner μ g ψ φ = ⟪T ψ, φ⟫_ℂ

lemma crossInner_norm_le {g : ℝ → ℂ} {C : ℝ} (_hC : 0 ≤ C) (hg : ∀ θ, ‖g θ‖ ≤ C) (hfin : ∀ z, IsFiniteMeasure (μ z)) (hmass : ∀ z, ((μ z) Set.univ).toReal = ‖z‖ ^ 2) (ψ φ : H) : ‖crossInner μ g ψ φ‖ ≤ C * (‖ψ‖ ^ 2 + ‖φ‖ ^ 2)

lemma cfc_norm_sq_eq_inner [CompleteSpace H] (U : H →L[ℂ] H) (_hU : IsStarNormal U) (f : ℂ → ℂ) (hf : ContinuousOn f (spectrum ℂ U)) (z : H) : ‖cfc f U z‖ ^ 2 = (⟪z, cfc (fun x => (starRingEnd ℂ) (f x) * f x) U z⟫_ℂ).re

lemma diag_parallelogram (A : H →L[ℂ] H) (ψ φ : H) : ⟪ψ + φ, A (ψ + φ)⟫_ℂ + ⟪ψ - φ, A (ψ - φ)⟫_ℂ = 2 * ⟪ψ, A ψ⟫_ℂ + 2 * ⟪φ, A φ⟫_ℂ

lemma measure_eq_of_fourier_eq (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : μ (Set.Icc 0 (2*Real.pi))ᶜ = 0) (hν : ν (Set.Icc 0 (2*Real.pi))ᶜ = 0) (h0μ : μ {0} = 0) (h0ν : ν {0} = 0) (h : ∀ n : ℤ, ∫ θ in Set.Ioc 0 (2*Real.pi), exp (I*n*θ) ∂μ = ∫ θ in Set.Ioc 0 (2*Real.pi), exp (I*n*θ) ∂ν) : μ = ν

lemma spectralMeasure_parallelogram (μ : H → Measure ℝ) (hfin  : ∀ z, IsFiniteMeasure (μ z)) (hsupp : ∀ z, μ z (Set.Icc 0 (2 * Real.pi))ᶜ = 0) (hatom : ∀ z, μ z {(0 : ℝ)} = 0) (mom : H → ℤ → ℂ) (hmom : ∀ z (n : ℤ), ∫ θ in Set.Ioc 0 (2 * Real.pi), Complex.exp (I * n * θ) ∂(μ z) = mom z n) (hmom_par : ∀ (n : ℤ) (a b : H), mom (a + b) n + mom (a - b) n = 2 * mom a n + 2 * mom b n) (huniq : ∀ ν₁ ν₂ : Measure ℝ, IsFiniteMeasure ν₁ → IsFiniteMeasure ν₂ → ν₁ (Set.Icc 0 (2 * Real.pi))ᶜ = 0 → ν₂ (Set....
```

### `QuantumMechanics/BornRule/`

#### `Conservation.lean` (15 decl)

```lean
lemma update_spacetimePoint_zero (t s : ℝ) (x : Fin 3 → ℝ) : Function.update (spacetimePoint t x) (0 : Fin 4) s = spacetimePoint s x

lemma update_spacetimePoint_succ (t s : ℝ) (x : Fin 3 → ℝ) (i : Fin 3) : Function.update (spacetimePoint t x) i.succ s = spacetimePoint t (Function.update x i s)

lemma update_insertNth (i : Fin 3) (a b : ℝ) (y : Fin 2 → ℝ) : Function.update (i.insertNth a y : Fin 3 → ℝ) i b = i.insertNth b y

lemma insertNth_eq_update (i : Fin 3) (x : Fin 3 → ℝ) (a : ℝ) : (i.insertNth a (fun j => x (i.succAbove j)) : Fin 3 → ℝ) = Function.update x i a

lemma hasDerivAt_re_comp (f : ℝ → ℂ) {t : ℝ} (hf : DifferentiableAt ℝ f t) : HasDerivAt (fun s => (f s).re) ((deriv f t).re) t

lemma deriv_re_comp (f : ℝ → ℂ) {t : ℝ} (hf : DifferentiableAt ℝ f t) : deriv (fun s => (f s).re) t = (deriv f t).re

lemma differentiableAt_current_slice (Γ : GammaMatrices) (ψ : Spacetime → Fin 4 → ℂ) (X : Spacetime) (μ : Fin 4) (hψ : ∀ a, DifferentiableAt ℝ (fun y => ψ y a) X) : DifferentiableAt ℝ (fun s => diracCurrent Γ (ψ (Function.update X μ s)) μ) (X μ)

lemma leibniz_integral_rule (Γ : GammaMatrices) (ψ : SpinorField) (t : ℝ) (h_diff : ∀ x a, DifferentiableAt ℝ (fun y => ψ.ψ y a) x) (h_meas : ∀ s : ℝ, AEStronglyMeasurable (fun x : Fin 3 → ℝ => probabilityDensity Γ (ψ.ψ (spacetimePoint s x))) volume) (h_int : Integrable (fun x : Fin 3 → ℝ => probabilityDensity Γ (ψ.ψ (spacetimePoint t x))) volume) (h_meas' : AEStronglyMeasurable (fun x : Fin 3 → ℝ => deriv (fun s => probabilityDensity Γ (ψ.ψ (spacetimePoint s x))) t) volume) (bound : (Fin 3 →...

theorem continuity_equation (Γ : GammaMatrices) (ψ : SpinorField) (m : ℝ) (h_dirac : ∀ x, (∑ μ : Fin 4, I • (Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x)) = (↑m : ℂ) • ψ.ψ x) (h_diff : ∀ x a, DifferentiableAt ℝ (fun y => ψ.ψ y a) x) (t : ℝ) (x : Fin 3 → ℝ) : deriv (fun s => probabilityDensity Γ (ψ.ψ (spacetimePoint s x))) t = -(∑ i : Fin 3, deriv (fun s => (diracCurrent Γ (ψ.ψ (spacetimePoint t (Function.update x i s))) i.succ).re) (x i))

lemma integral_deriv_eq_zero_of_tendsto (f : ℝ → ℝ) (hf : ∀ s, HasDerivAt f (deriv f s) s) (hint : Integrable (deriv f) volume) (htop : Tendsto f atTop (𝓝 0)) (hbot : Tendsto f atBot (𝓝 0)) : ∫ s, deriv f s = 0

lemma integral_deriv_update_eq_zero (F : (Fin 3 → ℝ) → ℝ) (i : Fin 3) (h_diff : ∀ x : Fin 3 → ℝ, DifferentiableAt ℝ (fun s => F (Function.update x i s)) (x i)) (h_line_int : ∀ x : Fin 3 → ℝ, Integrable (fun s => deriv (fun u => F (Function.update x i u)) s) volume) (h_top : ∀ x : Fin 3 → ℝ, Tendsto (fun s => F (Function.update x i s)) atTop (𝓝 0)) (h_bot : ∀ x : Fin 3 → ℝ, Tendsto (fun s => F (Function.update x i s)) atBot (𝓝 0)) (h_int : Integrable (fun x => deriv (fun s => F (Function.updat...

theorem divergence_integral_vanishes (Γ : GammaMatrices) (ψ : SpinorField) (t : ℝ) (h_diff : ∀ x a, DifferentiableAt ℝ (fun y => ψ.ψ y a) x) (h_int : ∀ i : Fin 3, Integrable (fun x : Fin 3 → ℝ => deriv (fun s => (diracCurrent Γ (ψ.ψ (spacetimePoint t (Function.update x i s))) i.succ).re) (x i)) volume) (h_line_int : ∀ (i : Fin 3) (x : Fin 3 → ℝ), Integrable (fun s : ℝ => deriv (fun u => (diracCurrent Γ (ψ.ψ (spacetimePoint t (Function.update x i u))) i.succ).re) s) volume) (h_top : ∀ (i : Fin...

theorem probability_conserved (Γ : GammaMatrices) (ψ : SpinorField) (m : ℝ) (h_dirac : ∀ x, (∑ μ : Fin 4, I • (Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x)) = (↑m : ℂ) • ψ.ψ x) (h_diff : ∀ x a, DifferentiableAt ℝ (fun y => ψ.ψ y a) x) (h_meas : ∀ s : ℝ, AEStronglyMeasurable (fun x : Fin 3 → ℝ => probabilityDensity Γ (ψ.ψ (spacetimePoint s x))) volume) (h_int : ∀ s : ℝ, Integrable (fun x : Fin 3 → ℝ => probabilityDensity Γ (ψ.ψ (spacetimePoint s x))) volume) (h_meas' : ∀ s : ℝ, AEStronglyMeasurab...

noncomputable def normalizedProbability (Γ : GammaMatrices) (ψ : SpinorField) (t : ℝ) (x : Fin 3 → ℝ) : ℝ

theorem born_rule_valid (Γ : GammaMatrices) (ψ : SpinorField) (t : ℝ) (m : ℝ) (_h_dirac : ∀ x, (∑ μ : Fin 4, I • (Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x)) = (↑m : ℂ) • ψ.ψ x) (h_nonzero : totalProbability Γ ψ t ≠ 0) : (∀ x, 0 ≤ normalizedProbability Γ ψ t x) ∧ (∫ x, normalizedProbability Γ ψ t x ∂volume = 1)
```

### `QuantumMechanics/DiracEquation/`

#### `CliffordAlgebra.lean` (43 decl)

```lean
def diracAlpha1 : Matrix (Fin 4) (Fin 4) ℂ

def diracAlpha2 : Matrix (Fin 4) (Fin 4) ℂ

def diracAlpha3 : Matrix (Fin 4) (Fin 4) ℂ

def diracBeta : Matrix (Fin 4) (Fin 4) ℂ

lemma diracAlpha1_sq : diracAlpha1 * diracAlpha1 = 1

lemma diracAlpha2_sq : diracAlpha2 * diracAlpha2 = 1

lemma diracAlpha3_sq : diracAlpha3 * diracAlpha3 = 1

lemma diracBeta_sq : diracBeta * diracBeta = 1

lemma diracAlpha12_anticommute : diracAlpha1 * diracAlpha2 + diracAlpha2 * diracAlpha1 = 0

lemma diracAlpha13_anticommute : diracAlpha1 * diracAlpha3 + diracAlpha3 * diracAlpha1 = 0

lemma diracAlpha23_anticommute : diracAlpha2 * diracAlpha3 + diracAlpha3 * diracAlpha2 = 0

lemma diracAlpha1_beta_anticommute : diracAlpha1 * diracBeta + diracBeta * diracAlpha1 = 0

lemma diracAlpha2_beta_anticommute : diracAlpha2 * diracBeta + diracBeta * diracAlpha2 = 0

lemma diracAlpha3_beta_anticommute : diracAlpha3 * diracBeta + diracBeta * diracAlpha3 = 0

lemma diracAlpha1_hermitian : diracAlpha1.conjTranspose = diracAlpha1

lemma diracAlpha2_hermitian : diracAlpha2.conjTranspose = diracAlpha2

lemma diracAlpha3_hermitian : diracAlpha3.conjTranspose = diracAlpha3

lemma diracBeta_hermitian : diracBeta.conjTranspose = diracBeta

def gamma0 : Matrix (Fin 4) (Fin 4) ℂ

def gamma1 : Matrix (Fin 4) (Fin 4) ℂ

def gamma2 : Matrix (Fin 4) (Fin 4) ℂ

def gamma3 : Matrix (Fin 4) (Fin 4) ℂ

lemma clifford_00 : gamma0 * gamma0 + gamma0 * gamma0 = 2 • (1 : Matrix (Fin 4) (Fin 4) ℂ)

lemma clifford_01 : gamma0 * gamma1 + gamma1 * gamma0 = (0 : Matrix (Fin 4) (Fin 4) ℂ)

lemma clifford_02 : gamma0 * gamma2 + gamma2 * gamma0 = (0 : Matrix (Fin 4) (Fin 4) ℂ)

lemma clifford_03 : gamma0 * gamma3 + gamma3 * gamma0 = (0 : Matrix (Fin 4) (Fin 4) ℂ)

lemma clifford_10 : gamma1 * gamma0 + gamma0 * gamma1 = (0 : Matrix (Fin 4) (Fin 4) ℂ)

lemma clifford_11 : gamma1 * gamma1 + gamma1 * gamma1 = (-2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)

lemma clifford_12 : gamma1 * gamma2 + gamma2 * gamma1 = (0 : Matrix (Fin 4) (Fin 4) ℂ)

lemma clifford_13 : gamma1 * gamma3 + gamma3 * gamma1 = (0 : Matrix (Fin 4) (Fin 4) ℂ)

lemma clifford_20 : gamma2 * gamma0 + gamma0 * gamma2 = (0 : Matrix (Fin 4) (Fin 4) ℂ)

lemma clifford_21 : gamma2 * gamma1 + gamma1 * gamma2 = (0 : Matrix (Fin 4) (Fin 4) ℂ)

lemma clifford_22 : gamma2 * gamma2 + gamma2 * gamma2 = (-2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)

lemma clifford_23 : gamma2 * gamma3 + gamma3 * gamma2 = (0 : Matrix (Fin 4) (Fin 4) ℂ)

lemma clifford_30 : gamma3 * gamma0 + gamma0 * gamma3 = (0 : Matrix (Fin 4) (Fin 4) ℂ)

lemma clifford_31 : gamma3 * gamma1 + gamma1 * gamma3 = (0 : Matrix (Fin 4) (Fin 4) ℂ)

lemma clifford_32 : gamma3 * gamma2 + gamma2 * gamma3 = (0 : Matrix (Fin 4) (Fin 4) ℂ)

lemma clifford_33 : gamma3 * gamma3 + gamma3 * gamma3 = (-2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)

lemma neg_two_eq_smul : (-2 : Matrix (Fin 4) (Fin 4) ℂ) = (-2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)

lemma gamma0_hermitian_proof : gamma0.conjTranspose = gamma0

lemma gamma1_antihermitian : gamma1.conjTranspose = -gamma1

lemma gamma2_antihermitian : gamma2.conjTranspose = -gamma2

lemma gamma3_antihermitian : gamma3.conjTranspose = -gamma3
```

#### `Conservation.lean` (17 decl)

```lean
def stdBasis (μ : Fin 4) : Spacetime

noncomputable def fourDivergence (j : (Fin 4 → ℝ) → (Fin 4 → ℂ)) : (Fin 4 → ℝ) → ℂ

noncomputable def partialDeriv' (μ : Fin 4) (ψ : Spacetime → (Fin 4 → ℂ)) (x : Spacetime) : Fin 4 → ℂ

lemma star_dotProduct_conjTranspose_mulVec (A : Matrix (Fin 4) (Fin 4) ℂ) (u w : Fin 4 → ℂ) : star u ⬝ᵥ A.conjTranspose.mulVec w = star (A.mulVec u) ⬝ᵥ w

lemma current_adjoint_transfer (Γ : GammaMatrices) (μ : Fin 4) (u v : Fin 4 → ℂ) : star u ⬝ᵥ (Γ.gamma 0 * Γ.gamma μ).mulVec v = star ((Γ.gamma μ).mulVec u) ⬝ᵥ (Γ.gamma 0).mulVec v

lemma star_smul_dotProduct_add (c : ℂ) (u v : Fin 4 → ℂ) : star (c • u) ⬝ᵥ v + star u ⬝ᵥ (c • v) = (starRingEnd ℂ c + c) * (star u ⬝ᵥ v)

lemma neg_I_mul_ofReal_add_conj (m : ℝ) : starRingEnd ℂ (-(I * ↑m)) + (-(I * ↑m)) = 0

lemma dirac_divergence_bilinear_vanishes (Γ : GammaMatrices) (m : ℝ) (ψ w : Fin 4 → ℂ) (h : I • w = (↑m : ℂ) • ψ) : star w ⬝ᵥ (Γ.gamma 0).mulVec ψ + star ψ ⬝ᵥ (Γ.gamma 0).mulVec w = 0

lemma diracCurrent_eq_dotProduct_mulVec (Γ : GammaMatrices) (v : Fin 4 → ℂ) (μ : Fin 4) : diracCurrent Γ v μ = star v ⬝ᵥ (Γ.gamma 0 * Γ.gamma μ).mulVec v

lemma hasDerivAt_update (x : Spacetime) (μ : Fin 4) : HasDerivAt (fun t => Function.update x μ t) (stdBasis μ) (x μ)

lemma deriv_comp_update (ψ : Spacetime → Fin 4 → ℂ) (x : Spacetime) (μ a : Fin 4) (hψ : DifferentiableAt ℝ (fun y => ψ y a) x) : deriv (fun t => ψ (Function.update x μ t) a) (x μ) = partialDeriv' μ ψ x a

lemma hasDerivAt_bilinear_self (M : Matrix (Fin 4) (Fin 4) ℂ) (f : ℝ → Fin 4 → ℂ) (f' : Fin 4 → ℂ) (t₀ : ℝ) (hf : HasDerivAt f f' t₀) : HasDerivAt (fun t => star (f t) ⬝ᵥ M.mulVec (f t)) (star f' ⬝ᵥ M.mulVec (f t₀) + star (f t₀) ⬝ᵥ M.mulVec f') t₀

lemma current_divergence_product_rule (Γ : GammaMatrices) (ψ : Spacetime → Fin 4 → ℂ) (x : Spacetime) (_hψ : ∀ a, DifferentiableAt ℝ (fun y => ψ y a) x) : fourDivergence (fun y => diracCurrent Γ (ψ y)) x = ∑ μ : Fin 4, (star (partialDeriv' μ ψ x) ⬝ᵥ (Γ.gamma 0 * Γ.gamma μ).mulVec (ψ x) + star (ψ x) ⬝ᵥ (Γ.gamma 0 * Γ.gamma μ).mulVec (partialDeriv' μ ψ x))

lemma finset_sum_dotProduct {ι : Type*} {s : Finset ι} (f : ι → Fin 4 → ℂ) (v : Fin 4 → ℂ) : (∑ i ∈ s, f i) ⬝ᵥ v = ∑ i ∈ s, f i ⬝ᵥ v

lemma dotProduct_finset_sum {ι : Type*} {s : Finset ι} (u : Fin 4 → ℂ) (f : ι → Fin 4 → ℂ) : u ⬝ᵥ (∑ i ∈ s, f i) = ∑ i ∈ s, u ⬝ᵥ f i

lemma mulVec_finset_sum {ι : Type*} {s : Finset ι} (M : Matrix (Fin 4) (Fin 4) ℂ) (f : ι → Fin 4 → ℂ) : M.mulVec (∑ i ∈ s, f i) = ∑ i ∈ s, M.mulVec (f i)

theorem dirac_current_conserved (Γ : GammaMatrices) (ψ : SpinorField) (m : ℝ) (h_dirac : ∀ x, ∑ μ : Fin 4, I • (Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x) = (↑m : ℂ) • ψ.ψ x) (h_diff : ∀ x a, DifferentiableAt ℝ (fun y => ψ.ψ y a) x) : ∀ x, fourDivergence (fun y => diracCurrent Γ (ψ.ψ y)) x = 0
```

#### `Current.lean` (17 decl)

```lean
structure GammaMatrices where gamma : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ clifford_minkowski : ∀ μ ν, gamma μ * gamma ν + gamma ν * gamma μ = 2 • (if μ = ν then (if μ = 0 then 1 else -1) • (1 : Matrix (Fin 4) (Fin 4) ℂ) else 0) gamma0_hermitian : (gamma 0).conjTranspose = gamma 0 gammaI_antihermitian : ∀ i : Fin 3, (gamma i.succ).conjTranspose = -gamma i.succ

def standardGammaMatrices : GammaMatrices where gamma

abbrev Spacetime

structure SpinorField where ψ : Spacetime → (Fin 4 → ℂ)

structure SpinorField' where ψ : (Fin 4 → ℝ) → (Fin 4 → ℂ) integrable : ∀ t : ℝ, Integrable (fun x : Fin 3 → ℝ => ‖ψ (Fin.cons t x)‖^2) volume

noncomputable def diracAdjoint (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) : Fin 4 → ℂ

noncomputable def diracCurrent (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) : Fin 4 → ℂ

lemma gamma0_sq (Γ : GammaMatrices) : Γ.gamma 0 * Γ.gamma 0 = 1

lemma gamma_conjTranspose_mul_gamma0 (Γ : GammaMatrices) (μ : Fin 4) : (Γ.gamma μ).conjTranspose * Γ.gamma 0 = Γ.gamma 0 * Γ.gamma μ

lemma gamma0_gamma_selfadjoint (Γ : GammaMatrices) (μ : Fin 4) : (Γ.gamma 0 * Γ.gamma μ).conjTranspose = Γ.gamma 0 * Γ.gamma μ

theorem current_zero_eq_norm_sq (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) : diracCurrent Γ ψ 0 = ∑ a, ‖ψ a‖^2

theorem current_zero_nonneg (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) : 0 ≤ (diracCurrent Γ ψ 0).re

lemma current_zero_eq_zero_iff (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) : diracCurrent Γ ψ 0 = 0 ↔ ψ = 0

noncomputable def probabilityDensity (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) : ℝ

noncomputable def probabilityCurrent (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) : Fin 3 → ℂ

def spacetimePoint (t : ℝ) (x : Fin 3 → ℝ) : Spacetime

noncomputable def totalProbability (Γ : GammaMatrices) (ψ : SpinorField) (t : ℝ) : ℝ
```

#### `GammaTrace.lean` (30 decl)

```lean
def minkowskiMetric (μ ν : Fin 4) : ℂ

def gamma5 : Matrix (Fin 4) (Fin 4) ℂ

def gammaAt (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ

lemma gamma0_trace_zero : Matrix.trace gamma0 = 0

lemma gamma1_trace_zero : Matrix.trace gamma1 = 0

lemma gamma2_trace_zero : Matrix.trace gamma2 = 0

lemma gamma3_trace_zero : Matrix.trace gamma3 = 0

lemma gamma_trace_zero (μ : Fin 4) : Matrix.trace (gammaAt μ) = 0

lemma gamma0_sq_eq_one : gamma0 * gamma0 = 1

lemma gamma1_sq_eq_neg_one : gamma1 * gamma1 = -1

lemma gamma2_sq_eq_neg_one : gamma2 * gamma2 = -1

lemma gamma3_sq_eq_neg_one : gamma3 * gamma3 = -1

lemma trace_one_fin4 : Matrix.trace (1 : Matrix (Fin 4) (Fin 4) ℂ) = 4

lemma trace_neg_one_fin4 : Matrix.trace (-(1 : Matrix (Fin 4) (Fin 4) ℂ)) = -4

lemma trace_mul_comm (A B : Matrix (Fin 4) (Fin 4) ℂ) : Matrix.trace (A * B) = Matrix.trace (B * A)

lemma trace_zero_of_anticommute (A B : Matrix (Fin 4) (Fin 4) ℂ) (h : A * B + B * A = 0) : Matrix.trace (A * B) = 0

lemma gamma_trace_two (μ ν : Fin 4) : Matrix.trace (gammaAt μ * gammaAt ν) = 4 * minkowskiMetric μ ν

lemma gamma5_sq : gamma5 * gamma5 = 1

lemma gamma5_hermitian : gamma5.conjTranspose = gamma5

lemma gamma5_anticommutes_0 : gamma5 * gamma0 = -gamma0 * gamma5

lemma gamma5_anticommutes_1 : gamma5 * gamma1 = -gamma1 * gamma5

lemma gamma5_anticommutes_2 : gamma5 * gamma2 = -gamma2 * gamma5

lemma gamma5_anticommutes_3 : gamma5 * gamma3 = -gamma3 * gamma5

lemma gamma5_anticommutes (μ : Fin 4) : gamma5 * gammaAt μ = -gammaAt μ * gamma5

lemma gamma5_trace_zero : Matrix.trace gamma5 = 0

lemma gamma5_move_through_three (μ ν ρ : Fin 4) : gamma5 * gammaAt μ * gammaAt ν * gammaAt ρ = -(gammaAt μ * gammaAt ν * gammaAt ρ * gamma5)

lemma gamma_trace_three (μ ν ρ : Fin 4) : Matrix.trace (gammaAt μ * gammaAt ν * gammaAt ρ) = 0

lemma gamma5_gammaAt_anticommute (μ : Fin 4) : gamma5 * gammaAt μ + gammaAt μ * gamma5 = 0

lemma gamma5_gamma_trace_zero (μ : Fin 4) : Matrix.trace (gamma5 * gammaAt μ) = 0

lemma gamma5_eq_product : gamma5 = I • (gamma0 * gamma1 * gamma2 * gamma3)
```

#### `Operators.lean` (13 decl)

```lean
abbrev SpinorSpace

structure DiracOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where domain : Submodule ℂ H op : domain →ₗ[ℂ] H

structure DiracConstants where hbar : ℝ c : ℝ m : ℝ hbar_pos : hbar > 0 c_pos : c > 0 m_nonneg : m ≥ 0

def DiracConstants.restEnergy (κ : DiracConstants) : ℝ

structure DiracHamiltonian (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (K M : Type*) where U_grp : OneParameterUnitaryGroup (H := H) constants : K matrices : M

abbrev domain (H_D : DiracHamiltonian H K M) : Submodule ℂ H

noncomputable abbrev op (H_D : DiracHamiltonian H K M) : (generator H_D.U_grp).domain →ₗ[ℂ] H

lemma symmetric (H_D : DiracHamiltonian H K M) (ψ φ : (generator H_D.U_grp).domain) : ⟪generator H_D.U_grp ψ, (φ : H)⟫_ℂ = ⟪(ψ : H), generator H_D.U_grp φ⟫_ℂ

noncomputable def toDiracOperator (H_D : DiracHamiltonian H K M) : DiracOperator H where domain

theorem dirac_generates_unitary (H_D : DiracHamiltonian H K M) : ∃ U : OneParameterUnitaryGroup (H

theorem dirac_unbounded_below (H_D : DiracHamiltonian H K M) (h_spectrum_below : ∀ N : ℝ, ∃ φ : H, spectralProjection H_D.U_grp (Set.Iic N) measurableSet_Iic φ ≠ 0) : ∀ bound : ℝ, ∃ ψ : (generator H_D.U_grp).domain, (⟪generator H_D.U_grp ψ, (ψ : H)⟫_ℂ).re < bound * ‖(ψ : H)‖ ^ 2

theorem dirac_unbounded_above (H_D : DiracHamiltonian H K M) (h_spectrum_above : ∀ N : ℝ, ∃ φ : H, spectralProjection H_D.U_grp (Set.Ici N) measurableSet_Ici φ ≠ 0) : ∀ bound : ℝ, ∃ ψ : (generator H_D.U_grp).domain, (⟪generator H_D.U_grp ψ, (ψ : H)⟫_ℂ).re > bound * ‖(ψ : H)‖ ^ 2

theorem dirac_not_semibounded (H_D : DiracHamiltonian H K M) (h_spectrum_below : ∀ N : ℝ, ∃ φ : H, spectralProjection H_D.U_grp (Set.Iic N) measurableSet_Iic φ ≠ 0) : ¬∃ bound : ℝ, ∀ ψ : (generator H_D.U_grp).domain, bound * ‖(ψ : H)‖ ^ 2 ≤ (⟪generator H_D.U_grp ψ, (ψ : H)⟫_ℂ).re
```

### `QuantumMechanics/`

#### `Ehrenfest.lean` (3 decl)

```lean
private lemma inner_isBoundedBilinearMap_real {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [IsScalarTower ℝ ℂ H] : IsBoundedBilinearMap ℝ (fun p : H × H => ⟪p.1, p.2⟫_ℂ) where add_left x₁ x₂ y

private lemma hasDerivAt_inner_cplx  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [IsScalarTower ℝ ℂ H] {f g : ℝ → H} {f' g' : H} {x : ℝ} (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) : HasDerivAt (fun t => ⟪f t, g t⟫_ℂ) (⟪f', g x⟫_ℂ + ⟪f x, g'⟫_ℂ) x

theorem ehrenfest_theorem (U_grp : OneParameterUnitaryGroup (H
```

### `QuantumMechanics/Generator/`

#### `Basic.lean` (11 decl)

```lean
lemma LinearPMap.apply_congr {f g : H →ₗ.[ℂ] H} (h : f = g) (x : H) (hx : x ∈ f.domain) : f ⟨x, hx⟩ = g ⟨x, h ▸ hx⟩

noncomputable def generatorObservable (U : OneParameterUnitaryGroup (H

theorem inner_generator_invariant (U : OneParameterUnitaryGroup (H

noncomputable def evolution (A : UnboundedObservable H) : OneParameterUnitaryGroup (H

lemma generator_evolution (A : UnboundedObservable H) : generator A.evolution = A.toLinearPMap

lemma evolution_generator_domain (A : UnboundedObservable H) : (generator A.evolution).domain = A.domain

lemma evolution_mem_domain (A : UnboundedObservable H) {ψ : H} (hψ : ψ ∈ A.domain) (t : ℝ) : A.evolution.U t ψ ∈ A.domain

lemma schrodingerEquation (A : UnboundedObservable H) {ψ : H} (hψ : ψ ∈ A.domain) (t : ℝ) : HasDerivAt (fun s => A.evolution.U s ψ) (I • A.toLinearPMap ⟨A.evolution.U t ψ, A.evolution_mem_domain hψ t⟩) t

theorem exists_unique_generator {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) : ∃! U : OneParameterUnitaryGroup (H

noncomputable def stoneObservableEquiv : OneParameterUnitaryGroup (H

lemma existsUnique_hamiltonian (U : OneParameterUnitaryGroup (H
```

### `QuantumMechanics/Observable/`

#### `Basic.lean` (8 decl)

```lean
lemma isFormalAdjoint_self_of_isSelfAdjoint {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) : A.IsFormalAdjoint A

structure UnboundedObservable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where toLinearPMap : H →ₗ.[ℂ] H selfAdjoint : IsSelfAdjoint toLinearPMap

def domain (A : UnboundedObservable H) : Submodule ℂ H

lemma dense (A : UnboundedObservable H) : Dense (A.domain : Set H)

lemma adjoint_eq (A : UnboundedObservable H) : A.toLinearPMap.adjoint = A.toLinearPMap

def toSymmetricOperator (A : UnboundedObservable H) : SymmetricOperator H where toLinearPMap

instance : Coe (UnboundedObservable H) (SymmetricOperator H)

lemma symmetric' (A : UnboundedObservable H) {ψ φ : H} (hψ : ψ ∈ A.domain) (hφ : φ ∈ A.domain) : ⟪A.toSymmetricOperator ⬝ ψ ⊢ hψ, φ⟫_ℂ = ⟪ψ, A.toSymmetricOperator ⬝ φ ⊢ hφ⟫_ℂ
```

### `QuantumMechanics/`

#### `PauliMatrices.lean` (12 decl)

```lean
def pauliX : Matrix (Fin 2) (Fin 2) ℂ

def pauliY : Matrix (Fin 2) (Fin 2) ℂ

def pauliZ : Matrix (Fin 2) (Fin 2) ℂ

lemma pauliX_hermitian : pauliX.conjTranspose = pauliX

lemma pauliY_hermitian : pauliY.conjTranspose = pauliY

lemma pauliZ_hermitian : pauliZ.conjTranspose = pauliZ

lemma pauliX_sq : pauliX * pauliX = 1

lemma pauliY_sq : pauliY * pauliY = 1

lemma pauliZ_sq : pauliZ * pauliZ = 1

lemma pauliXY_anticommute : pauliX * pauliY + pauliY * pauliX = 0

lemma pauliXZ_anticommute : pauliX * pauliZ + pauliZ * pauliX = 0

lemma pauliYZ_anticommute : pauliY * pauliZ + pauliZ * pauliY = 0
```

#### `SchrodingerEquation.lean` (5 decl)

```lean
theorem schrödinger_equation₂ (U_grp : OneParameterUnitaryGroup (H

theorem schrödinger_equation₁ (U_grp : OneParameterUnitaryGroup (H

theorem schrödinger_equation₃ (U_grp : OneParameterUnitaryGroup (H

lemma genToGroup_domain_invariant {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (t : ℝ) (ψ₀ : H) (hψ₀ : ψ₀ ∈ A.domain) : (genToGroup hA).U t ψ₀ ∈ A.domain

theorem schrödinger_of_selfAdjoint {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (ψ₀ : H) (hψ₀ : ψ₀ ∈ A.domain) (t : ℝ) : HasDerivAt (fun s => (genToGroup hA).U s ψ₀) (I • A ⟨(genToGroup hA).U t ψ₀, genToGroup_domain_invariant hA t ψ₀ hψ₀⟩) t
```

### `QuantumMechanics/Stone/`

#### `Basic.lean` (4 decl)

```lean
noncomputable def genToGroup {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) : OneParameterUnitaryGroup (H

lemma generator_genToGroup {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) : generator (genToGroup hA) = A

noncomputable def stoneEquiv : OneParameterUnitaryGroup (H

lemma stone_orbit_hasDerivAt (U : OneParameterUnitaryGroup (H
```

#### `Helpers.lean` (6 decl)

```lean
lemma op_lower_bound {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (z : ℂ) (x : A.domain) : |z.im| * ‖(x : H)‖ ≤ ‖A x - z • (x : H)‖

lemma op_range_isClosed {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hgr : IsClosed (A.graph : Set (H × H))) (z : ℂ) (hz : z.im ≠ 0) : IsClosed (Set.range fun x : A.domain => A x - z • (x : H))

lemma op_range_dense {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) : Dense (Set.range fun x : A.domain => A x - z • (x : H))

lemma selfAdjoint_surjective_sub_smul {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0) : ∀ φ : H, ∃ ψ : A.domain, A ψ - z • (ψ : H) = φ

lemma isSelfAdjoint_to_surjective {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) : (∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) ∧ (∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)

lemma IsSelfAdjoint.eq_of_le {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hle : A ≤ B) : A = B
```

#### `OneParameterUnitaryGroup.lean` (13 decl)

```lean
structure OneParameterUnitaryGroup (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where U : ℝ → (H →L[ℂ] H) unitary : ∀ (t : ℝ) (ψ φ : H), ⟪U t ψ, U t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ group_law : ∀ s t : ℝ, U (s + t) = (U s).comp (U t) identity : U 0 = ContinuousLinearMap.id ℂ H strong_continuous : ∀ ψ : H, Continuous (fun t : ℝ => U t ψ)

lemma inverse_eq_adjoint (U : OneParameterUnitaryGroup (H

lemma norm_preserving (U : OneParameterUnitaryGroup (H

lemma norm_one [Nontrivial H] (U : OneParameterUnitaryGroup (H

noncomputable def genDiffQuot (U : OneParameterUnitaryGroup (H

lemma genDiffQuot_add (U : OneParameterUnitaryGroup (H

lemma genDiffQuot_smul (U : OneParameterUnitaryGroup (H

def generatorDomain (U : OneParameterUnitaryGroup (H

noncomputable def generator (U : OneParameterUnitaryGroup (H

lemma generator_tendsto (U : OneParameterUnitaryGroup (H

lemma generator_isFormalAdjoint (U : OneParameterUnitaryGroup (H

lemma generator_domain_invariant (U : OneParameterUnitaryGroup (H

lemma isSelfAdjoint_of_surjective_addSub (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A) (hdense : Dense (A.domain : Set H)) (hplus  : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) : IsSelfAdjoint A
```

#### `Unique.lean` (4 decl)

```lean
lemma unitary_orbit_hasDerivAt (U : OneParameterUnitaryGroup (H

lemma generator_comm (U : OneParameterUnitaryGroup (H

lemma group_apply_curve_hasDerivAt (V : OneParameterUnitaryGroup (H

lemma group_unique (V W : OneParameterUnitaryGroup (H
```

### `QuantumMechanics/Stone/Yosida/`

#### `Bounds.lean` (3 decl)

```lean
lemma yosidaApprox_norm_bound {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (n : ℕ+) : ‖yosidaApprox hsym hplus hminus n‖ ≤ 2 * (n : ℝ)

lemma yosidaJ_norm_bound {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (n : ℕ+) : ‖(-I * (n : ℂ)) • resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus‖ ≤ 1

lemma yosidaJNeg_norm_bound {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (n : ℕ+) : ‖yosidaJNeg hsym hplus hminus n‖ ≤ 1
```

#### `Commutation.lean` (5 decl)

```lean
lemma yosidaApproxSym_commute {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus  : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (m n : ℕ+) : Commute (yosidaApproxSym hsym hplus hminus m) (yosidaApproxSym hsym hplus hminus n)

lemma commute_exp (C B : H →L[ℂ] H) (τ : ℝ) (h : Commute C B) : Commute C (expBounded B τ)

lemma norm_expBounded_skewAdjoint (B : H →L[ℂ] H) (hB : B.adjoint = -B) (τ : ℝ) (v : H) : ‖expBounded B τ v‖ = ‖v‖

lemma norm_expBounded_pairwise_le (Bm Bn : H →L[ℂ] H) (hcomm : Commute Bm Bn) (hm : Bm.adjoint = -Bm) (hn : Bn.adjoint = -Bn) (t : ℝ) (ψ : H) : ‖expBounded Bm t ψ - expBounded Bn t ψ‖ ≤ |t| * ‖(Bm - Bn) ψ‖

lemma expBounded_yosidaApproxSym_cauchy_intrinsic {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus  : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (hdense : Dense (A.domain : Set H)) (t : ℝ) (ψ : H) : CauchySeq (fun n : ℕ+ => expBounded (I • yosidaApproxSym hsym hplus hminus n) t ψ)
```

### `QuantumMechanics/Stone/Yosida/Convergence/`

#### `Approximants.lean` (7 decl)

```lean
lemma yosidaApprox_eq_J_comp_A {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (n : ℕ+) (φ : H) (hφ : φ ∈ A.domain) : yosidaApprox hsym hplus hminus n φ = yosidaJ hsym hplus hminus n (A ⟨φ, hφ⟩)

lemma yosidaApprox_tendsto_on_domain {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (h_dense : Dense (A.domain : Set H)) (ψ : H) (hψ : ψ ∈ A.domain) : Tendsto (fun n : ℕ+ => yosidaApprox hsym hplus hminus n ψ) atTop (𝓝 (A ⟨ψ, hψ⟩))

lemma yosidaApproxNeg_eq_JNeg_A {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (n : ℕ+) (φ : H) (hφ : φ ∈ A.domain) : yosidaApproxNeg hsym hplus hminus n φ = yosidaJNeg hsym hplus hminus n (A ⟨φ, hφ⟩)

lemma yosidaApproxNeg_tendsto_on_domain {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (h_dense : Dense (A.domain : Set H)) (φ : H) (hφ : φ ∈ A.domain) : Tendsto (fun n : ℕ+ => yosidaApproxNeg hsym hplus hminus n φ) atTop (𝓝 (A ⟨φ, hφ⟩))

lemma yosidaApproxSym_eq_avg {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (n : ℕ+) : yosidaApproxSym hsym hplus hminus n = (1/2 : ℂ) • (yosidaApprox hsym hplus hminus n + yosidaApproxNeg hsym hplus hminus n)

lemma yosidaApproxSym_tendsto_on_domain {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (h_dense : Dense (A.domain : Set H)) (φ : H) (hφ : φ ∈ A.domain) : Tendsto (fun n : ℕ+ => yosidaApproxSym hsym hplus hminus n φ) atTop (𝓝 (A ⟨φ, hφ⟩))

lemma yosidaApprox_commutes_resolvent {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (n : ℕ+) (z : ℂ) (hz : z.im ≠ 0) : (yosidaApprox hsym hplus hminus n).comp (resolvent z hz hsym hplus hminus) = (resolvent z hz hsym hplus hminus).comp (yosidaApprox hsym hplus hminus n)
```

#### `JNegOperator.lean` (3 decl)

```lean
lemma yosidaJNeg_eq_sub_resolvent_A {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (n : ℕ+) (φ : H) (hφ : φ ∈ A.domain) : (I * (n : ℂ)) • Resolvent.resolvent (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus φ = φ - Resolvent.resolvent (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus (A ⟨φ, hφ⟩)

lemma yosidaJNeg_tendsto_on_domain {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (φ : H) (hφ : φ ∈ A.domain) : Tendsto (fun n : ℕ+ => yosidaJNeg hsym hplus hminus n φ) atTop (𝓝 φ)

lemma yosidaJNeg_tendsto_id {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (h_dense : Dense (A.domain : Set H)) (ψ : H) : Tendsto (fun n : ℕ+ => yosidaJNeg hsym hplus hminus n ψ) atTop (𝓝 ψ)
```

#### `JOperator.lean` (3 decl)

```lean
lemma yosidaJ_eq_sub_resolvent_A {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (n : ℕ+) (φ : H) (hφ : φ ∈ A.domain) : (-I * (n : ℂ)) • Resolvent.resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus φ = φ - Resolvent.resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus (A ⟨φ, hφ⟩)

lemma yosidaJ_tendsto_on_domain {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (φ : H) (hφ : φ ∈ A.domain) : Tendsto (fun n : ℕ+ => (-I * (n : ℂ)) • Resolvent.resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus φ) atTop (𝓝 φ)

lemma yosida_J_tendsto_id {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (hdense : Dense (A.domain : Set H)) (ψ : H) : Tendsto (fun n : ℕ+ => (-I * (n : ℂ)) • resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus ψ) atTop (𝓝 ψ)
```

### `QuantumMechanics/Stone/Yosida/`

#### `Defs.lean` (8 decl)

```lean
noncomputable def resolventAtIn {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (n : ℕ+) : H →L[ℂ] H

noncomputable def resolventAtNegIn {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (n : ℕ+) : H →L[ℂ] H

noncomputable def yosidaApprox {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (n : ℕ+) : H →L[ℂ] H

noncomputable def yosidaApproxSym {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (n : ℕ+) : H →L[ℂ] H

noncomputable def yosidaJ {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (n : ℕ+) : H →L[ℂ] H

noncomputable def yosidaJNeg {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (n : ℕ+) : H →L[ℂ] H

noncomputable def yosidaApproxNeg {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (n : ℕ+) : H →L[ℂ] H

lemma resolventAtIn_bound {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (n : ℕ+) : ‖resolventAtIn hsym hplus hminus n‖ ≤ 1 / (n : ℝ)
```

### `QuantumMechanics/Stone/Yosida/ExpBounded/`

#### `Adjoint.lean` (6 decl)

```lean
lemma adjoint_pow (B : H →L[ℂ] H) (k : ℕ) : (B ^ k).adjoint = B.adjoint ^ k

lemma tsum_apply_of_summable (f : ℕ → H →L[ℂ] H) (hf : Summable f) (x : H) : (∑' n, f n) x = ∑' n, f n x

lemma inner_tsum_right' (x : H) (f : ℕ → H) (hf : Summable f) : ⟪x, ∑' n, f n⟫_ℂ = ∑' n, ⟪x, f n⟫_ℂ

lemma tsum_inner_left' (f : ℕ → H) (y : H) (hf : Summable f) : ⟪∑' n, f n, y⟫_ℂ = ∑' n, ⟪f n, y⟫_ℂ

lemma adjoint_expBounded (B : H →L[ℂ] H) (t : ℝ) : (expBounded B t).adjoint = expBounded B.adjoint t

lemma expBounded_adjoint (B : H →L[ℂ] H) (t : ℝ) : ContinuousLinearMap.adjoint (expBounded B t) = expBounded (ContinuousLinearMap.adjoint B) t
```

#### `Helpers.lean` (11 decl)

```lean
noncomputable def expBounded (B : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H

lemma expBounded_summable (B : H →L[ℂ] H) (t : ℝ) : Summable (fun k : ℕ => (1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k)

lemma expBounded_norm_summable (B : H →L[ℂ] H) (t : ℝ) : Summable (fun k : ℕ => ‖(1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k‖)

lemma expBounded_norm_bound (B : H →L[ℂ] H) (t : ℝ) : ‖expBounded B t‖ ≤ Real.exp (|t| * ‖B‖)

lemma expBounded_at_zero (B : H →L[ℂ] H) (ψ : H) : expBounded B 0 ψ = ψ

lemma expBounded_at_zero' (B : H →L[ℂ] H) : expBounded B 0 = 1

lemma expBounded_zero_op (t : ℝ) : expBounded (0 : H →L[ℂ] H) t = 1

lemma expBounded_eq_exp (B : H →L[ℂ] H) (t : ℝ) : expBounded B t = NormedSpace.exp ((t : ℂ) • B)

lemma smul_commute (B : H →L[ℂ] H) (s t : ℂ) : Commute (s • B) (t • B)

lemma B_commute_expBounded (B : H →L[ℂ] H) (τ : ℝ) : Commute B (expBounded B τ)

lemma expBounded_add_smul (B : H →L[ℂ] H) (s t : ℝ) : expBounded B (s + t) = (expBounded B s).comp (expBounded B t)
```

#### `Unitary.lean` (8 decl)

```lean
lemma expBounded_skewAdjoint_unitary (B : H →L[ℂ] H) (hB : B.adjoint = -B) (t : ℝ) : (expBounded B t).adjoint.comp (expBounded B t) = ContinuousLinearMap.id ℂ H ∧ (expBounded B t).comp (expBounded B t).adjoint = ContinuousLinearMap.id ℂ H

lemma expBounded_mem_unitary (B : H →L[ℂ] H) (hB : ContinuousLinearMap.adjoint B = -B) (t : ℝ) : expBounded B t ∈ unitary (H →L[ℂ] H)

lemma smul_I_skewSelfAdjoint (A : H →L[ℂ] H) (hA : ContinuousLinearMap.adjoint A = A) : ContinuousLinearMap.adjoint (I • A) = -(I • A)

lemma expBounded_yosidaApproxSym_unitary {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (n : ℕ+) (t : ℝ) (ψ φ : H) : ⟪expBounded (I • yosidaApproxSym hsym hplus hminus n) t ψ, expBounded (I • yosidaApproxSym hsym hplus hminus n) t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ

theorem expBounded_yosidaApproxSym_isometry {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (n : ℕ+) (t : ℝ) (ψ : H) : ‖expBounded (I • yosidaApproxSym hsym hplus hminus n) t ψ‖ = ‖ψ‖

theorem expBounded_yosida_norm_le {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (n : ℕ+) (t : ℝ) : ‖expBounded (I • yosidaApprox hsym hplus hminus n) t‖ ≤ Real.exp (|t| * ‖I • yosidaApprox hsym hplus hminus n‖)

lemma expBounded_hasDerivAt_zero (B : H →L[ℂ] H) : HasDerivAt (fun τ : ℝ => expBounded B τ) B 0

lemma expBounded_hasDerivAt (B : H →L[ℂ] H) (τ : ℝ) : HasDerivAt (fun t : ℝ => expBounded B t) (B.comp (expBounded B τ)) τ
```

### `QuantumMechanics/Stone/Yosida/`

#### `Exponential.lean` (14 decl)

```lean
private noncomputable def exponentialFun (_hdense : Dense (A.domain : Set H)) (t : ℝ) (ψ : H) : H

lemma exponentialFun_tendsto (hdense : Dense (A.domain : Set H)) (t : ℝ) (ψ : H) : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym hsym hplus hminus n) t ψ) atTop (𝓝 (exponentialFun hsym hplus hminus hdense t ψ))

private lemma exponentialFun_add (h_dense : Dense (A.domain : Set H)) (t : ℝ) (ψ₁ ψ₂ : H) : exponentialFun hsym hplus hminus h_dense t (ψ₁ + ψ₂) = exponentialFun hsym hplus hminus h_dense t ψ₁ + exponentialFun hsym hplus hminus h_dense t ψ₂

private lemma exponentialFun_smul (h_dense : Dense (A.domain : Set H)) (t : ℝ) (c : ℂ) (ψ : H) : exponentialFun hsym hplus hminus h_dense t (c • ψ) = c • exponentialFun hsym hplus hminus h_dense t ψ

private lemma exponentialFun_norm_le (h_dense : Dense (A.domain : Set H)) (t : ℝ) (ψ : H) : ‖exponentialFun hsym hplus hminus h_dense t ψ‖ ≤ 1 * ‖ψ‖

noncomputable def exponential (hdense : Dense (A.domain : Set H)) (t : ℝ) : H →L[ℂ] H

lemma exponential_unitary (h_dense : Dense (A.domain : Set H)) (t : ℝ) (ψ φ : H) : ⟪exponential hsym hplus hminus h_dense t ψ, exponential hsym hplus hminus h_dense t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ

lemma exponential_group_law (h_dense : Dense (A.domain : Set H)) (s t : ℝ) (ψ : H) : exponential hsym hplus hminus h_dense (s + t) ψ = exponential hsym hplus hminus h_dense s (exponential hsym hplus hminus h_dense t ψ)

lemma exponential_identity (h_dense : Dense (A.domain : Set H)) (ψ : H) : exponential hsym hplus hminus h_dense 0 ψ = ψ

lemma exponential_strong_continuous (h_dense : Dense (A.domain : Set H)) (ψ : H) : Continuous (fun t : ℝ => exponential hsym hplus hminus h_dense t ψ)

lemma expBounded_yosidaApproxSym_duhamel (n : ℕ+) (t : ℝ) (φ : H) : expBounded (I • yosidaApproxSym hsym hplus hminus n) t φ - φ = ∫ s in (0:ℝ)..t, expBounded (I • yosidaApproxSym hsym hplus hminus n) s (I • yosidaApproxSym hsym hplus hminus n φ)

lemma exponential_sub_eq_integral (h_dense : Dense (A.domain : Set H)) (φ : H) (hφ : φ ∈ A.domain) (t : ℝ) : exponential hsym hplus hminus h_dense t φ - φ = ∫ s in (0:ℝ)..t, I • exponential hsym hplus hminus h_dense s (A ⟨φ, hφ⟩)

lemma exponential_generator_eq (h_dense : Dense (A.domain : Set H)) (φ : H) (hφ : φ ∈ A.domain) : Tendsto (fun t : ℝ => (t⁻¹ : ℂ) • (exponential hsym hplus hminus h_dense t φ - φ)) (𝓝[≠] 0) (𝓝 (I • A ⟨φ, hφ⟩))

lemma exponential_generator_eq' (h_dense : Dense (A.domain : Set H)) (φ : H) (hφ : φ ∈ A.domain) : Tendsto (fun t : ℝ => (I * (t : ℂ))⁻¹ • (exponential hsym hplus hminus h_dense t φ - φ)) (𝓝[≠] 0) (𝓝 (A ⟨φ, hφ⟩))
```

#### `Helpers.lean` (8 decl)

```lean
lemma I_mul_pnat_im_ne_zero (n : ℕ+) : (I * (n : ℂ)).im ≠ 0

lemma neg_I_mul_pnat_im_ne_zero (n : ℕ+) : (-I * (n : ℂ)).im ≠ 0

lemma I_mul_pnat_im (n : ℕ+) : (I * (n : ℂ)).im = (n : ℝ)

lemma abs_I_mul_pnat_im (n : ℕ+) : |(I * (n : ℂ)).im| = (n : ℝ)

lemma norm_pnat_sq (n : ℕ+) : ‖((n : ℂ)^2)‖ = (n : ℝ)^2

lemma norm_I_mul_pnat (n : ℕ+) : ‖I * (n : ℂ)‖ = (n : ℝ)

lemma resolvent_spec {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (z : ℂ) (hz : z.im ≠ 0) (φ : H) : (Resolvent.resolvent z hz hsym hplus hminus φ) ∈ A.domain ∧ A ⟨Resolvent.resolvent z hz hsym hplus hminus φ, (Classical.choose (self_adjoint_range_all_z hsym hplus hminus z hz φ).exists).property⟩ - z • (Resolvent.resolvent z hz hsym hplus hminus φ) = φ

lemma resolvent_spec' {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (z : ℂ) (hz : z.im ≠ 0) (φ : H) : ∃ (h : Resolvent.resolvent z hz hsym hplus hminus φ ∈ A.domain), A ⟨Resolvent.resolvent z hz hsym hplus hminus φ, h⟩ - z • (Resolvent.resolvent z hz hsym hplus hminus φ) = φ
```

#### `Symmetry.lean` (2 decl)

```lean
lemma yosidaApproxSym_selfAdjoint {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (n : ℕ+) : (yosidaApproxSym hsym hplus hminus n).adjoint = yosidaApproxSym hsym hplus hminus n

lemma I_smul_yosidaApproxSym_skewAdjoint {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (n : ℕ+) : (I • yosidaApproxSym hsym hplus hminus n).adjoint = -(I • yosidaApproxSym hsym hplus hminus n)
```

### `QuantumMechanics/Uncertainty/`

#### `Heisenberg.lean` (4 decl)

```lean
def SatisfiesCCR (A B : UnboundedObservable H) (ψ : H) (h : ShiftedDomainConditions A.toSymmetricOperator B.toSymmetricOperator ψ) (ℏ : ℝ) : Prop

lemma norm_inner_commutator_of_ccr (A B : UnboundedObservable H) (ψ : H) (h : ShiftedDomainConditions A.toSymmetricOperator B.toSymmetricOperator ψ) (ℏ : ℝ) (hℏ : 0 ≤ ℏ) (hccr : commutatorAt A.toSymmetricOperator B.toSymmetricOperator ψ h.toDomainConditions = (Complex.I * (ℏ : ℂ)) • ψ) : ‖⟪ψ, commutatorAt A.toSymmetricOperator B.toSymmetricOperator ψ h.toDomainConditions⟫_ℂ‖ = ℏ

theorem heisenberg_uncertainty (A B : UnboundedObservable H) (ψ : H) (h : ShiftedDomainConditions A.toSymmetricOperator B.toSymmetricOperator ψ) (ℏ : ℝ) (hℏ : 0 ≤ ℏ) (hccr : SatisfiesCCR A B ψ h ℏ) : A.toSymmetricOperator.stdDev ψ h.h_norm h.hψ_A * B.toSymmetricOperator.stdDev ψ h.h_norm h.hψ_B ≥ ℏ / 2

theorem heisenberg_variance (A B : UnboundedObservable H) (ψ : H) (h : ShiftedDomainConditions A.toSymmetricOperator B.toSymmetricOperator ψ) (ℏ : ℝ) (hℏ : 0 ≤ ℏ) (hccr : SatisfiesCCR A B ψ h ℏ) : A.toSymmetricOperator.variance ψ h.h_norm h.hψ_A * B.toSymmetricOperator.variance ψ h.h_norm h.hψ_B ≥ ℏ^2 / 4
```

#### `SchrodingerRobertson.lean` (14 decl)

```lean
lemma sq_le_sq_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : x^2 ≤ y^2

lemma normSq_of_re_zero {z : ℂ} (h : z.re = 0) : Complex.normSq z = z.im^2

lemma normSq_eq_re_sq_add_im_sq (z : ℂ) : Complex.normSq z = z.re^2 + z.im^2

lemma im_inner_shifted_eq_half_commutator (A B : SymmetricOperator H) (ψ : H) (h : ShiftedDomainConditions A B ψ) : (⟪h.A'ψ, h.B'ψ⟫_ℂ).im = (1/2) * (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).im

noncomputable def covariance (A B : SymmetricOperator H) (ψ : H) (h : ShiftedDomainConditions A B ψ) : ℝ

lemma re_inner_shifted_eq_covariance (A B : SymmetricOperator H) (ψ : H) (h : ShiftedDomainConditions A B ψ) : (⟪h.A'ψ, h.B'ψ⟫_ℂ).re = covariance A B ψ h

lemma schrodinger_uncertainty (A B : SymmetricOperator H) (ψ : H) (h : ShiftedDomainConditions A B ψ) : A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B ≥ (1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2 + (covariance A B ψ h)^2

lemma schrodinger_stddev (A B : SymmetricOperator H) (ψ : H) (h : ShiftedDomainConditions A B ψ) : A.stdDev ψ h.h_norm h.hψ_A * B.stdDev ψ h.h_norm h.hψ_B ≥ Real.sqrt ((1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2 + (covariance A B ψ h)^2)

lemma robertson_uncertainty (A B : SymmetricOperator H) (ψ : H) (h : ShiftedDomainConditions A B ψ) : A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B ≥ (1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2

lemma robertson_stddev (A B : SymmetricOperator H) (ψ : H) (h : ShiftedDomainConditions A B ψ) : A.stdDev ψ h.h_norm h.hψ_A * B.stdDev ψ h.h_norm h.hψ_B ≥ (1/2) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖

lemma observable_schrodinger_uncertainty (A B : UnboundedObservable H) (ψ : H) (h : ShiftedDomainConditions A.toSymmetricOperator B.toSymmetricOperator ψ) : A.toSymmetricOperator.variance ψ h.h_norm h.hψ_A * B.toSymmetricOperator.variance ψ h.h_norm h.hψ_B ≥ (1/4) * ‖⟪ψ, commutatorAt A.toSymmetricOperator B.toSymmetricOperator ψ h.toDomainConditions⟫_ℂ‖^2 + (covariance A.toSymmetricOperator B.toSymmetricOperator ψ h)^2

lemma observable_robertson_uncertainty (A B : UnboundedObservable H) (ψ : H) (h : ShiftedDomainConditions A.toSymmetricOperator B.toSymmetricOperator ψ) : A.toSymmetricOperator.variance ψ h.h_norm h.hψ_A * B.toSymmetricOperator.variance ψ h.h_norm h.hψ_B ≥ (1/4) * ‖⟪ψ, commutatorAt A.toSymmetricOperator B.toSymmetricOperator ψ h.toDomainConditions⟫_ℂ‖^2

lemma observable_schrodinger_stddev (A B : UnboundedObservable H) (ψ : H) (h : ShiftedDomainConditions A.toSymmetricOperator B.toSymmetricOperator ψ) : A.toSymmetricOperator.stdDev ψ h.h_norm h.hψ_A * B.toSymmetricOperator.stdDev ψ h.h_norm h.hψ_B ≥ Real.sqrt ((1/4) * ‖⟪ψ, commutatorAt A.toSymmetricOperator B.toSymmetricOperator ψ h.toDomainConditions⟫_ℂ‖^2 + (covariance A.toSymmetricOperator B.toSymmetricOperator ψ h)^2)

lemma observable_robertson_stddev (A B : UnboundedObservable H) (ψ : H) (h : ShiftedDomainConditions A.toSymmetricOperator B.toSymmetricOperator ψ) : A.toSymmetricOperator.stdDev ψ h.h_norm h.hψ_A * B.toSymmetricOperator.stdDev ψ h.h_norm h.hψ_B ≥ (1/2) * ‖⟪ψ, commutatorAt A.toSymmetricOperator B.toSymmetricOperator ψ h.toDomainConditions⟫_ℂ‖
```

### `QuantumMechanics/Unitarity/`

#### `FirstLawEqiv.lean` (23 decl)

```lean
lemma group_apply_comm (s t : ℝ) (ψ : H) : U_grp.U s (U_grp.U t ψ) = U_grp.U t (U_grp.U s ψ)

lemma unitary_group_surjective (t : ℝ) : Function.Surjective (U_grp.U t)

theorem mem_unitary (t : ℝ) : U_grp.U t ∈ _root_.unitary (H →L[ℂ] H)

theorem borelMeasure_unitary_invariant (t : ℝ) (ψ : H) : borelMeasure U_grp (U_grp.U t ψ) = borelMeasure U_grp ψ

theorem quantum_liouville (t : ℝ) (ψ : H) (B : Set ℝ) : borelMeasure U_grp (U_grp.U t ψ) B = borelMeasure U_grp ψ B

theorem spectral_moment_conserved (n : ℕ) (t : ℝ) (ψ : H) : ∫ s, s ^ n ∂(borelMeasure U_grp (U_grp.U t ψ)) = ∫ s, s ^ n ∂(borelMeasure U_grp ψ)

noncomputable def energyVariance (ψ : H) : ℝ

theorem energyVariance_conserved (t : ℝ) (ψ : H) : energyVariance U_grp (U_grp.U t ψ) = energyVariance U_grp ψ

theorem spectralProjection_group_comm (B : Set ℝ) (hB : MeasurableSet B) (t : ℝ) (ψ : H) : spectralProjection U_grp B hB (U_grp.U t ψ) = U_grp.U t (spectralProjection U_grp B hB ψ)

theorem spectralProjection_norm_conserved (B : Set ℝ) (hB : MeasurableSet B) (t : ℝ) (ψ : H) : ‖spectralProjection U_grp B hB (U_grp.U t ψ)‖ = ‖spectralProjection U_grp B hB ψ‖

theorem unitary_of_borelMeasure_invariant (V : H →L[ℂ] H) (hsurj : Function.Surjective V) (hinv : ∀ ψ : H, borelMeasure U_grp (V ψ) = borelMeasure U_grp ψ) : V ∈ _root_.unitary (H →L[ℂ] H)

theorem unitary_iff_borelMeasure_invariant (t : ℝ) : U_grp.U t ∈ _root_.unitary (H →L[ℂ] H) ↔ ∀ ψ : H, borelMeasure U_grp (U_grp.U t ψ) = borelMeasure U_grp ψ

theorem generator_group_comm (t : ℝ) (x : (generator U_grp).domain) : generator U_grp ⟨U_grp.U t (x : H), generator_domain_invariant U_grp t x⟩ = U_grp.U t (generator U_grp x)

theorem energy_expectation_conserved (t : ℝ) (x : (generator U_grp).domain) : ⟪generator U_grp ⟨U_grp.U t (x : H), generator_domain_invariant U_grp t x⟩, U_grp.U t (x : H)⟫_ℂ = ⟪generator U_grp x, (x : H)⟫_ℂ

structure FirstLawEquivalence : Prop where unitary : ∀ t : ℝ, U_grp.U t ∈ _root_.unitary (H →L[ℂ] H) symmetric : (generator U_grp).IsFormalAdjoint (generator U_grp) spectral_invariant : ∀ (t : ℝ) (ψ : H), borelMeasure U_grp (U_grp.U t ψ) = borelMeasure U_grp ψ energy_conserved : ∀ (t : ℝ) (x : (generator U_grp).domain), ⟪generator U_grp ⟨U_grp.U t (x : H), generator_domain_invariant U_grp t x⟩, U_grp.U t (x : H)⟫_ℂ = ⟪generator U_grp x, (x : H)⟫_ℂ

theorem first_law : FirstLawEquivalence U_grp where unitary

noncomputable def electronProjection (H_D : DiracHamiltonian H DiracConstants M) : H →L[ℂ] H

noncomputable def positronProjection (H_D : DiracHamiltonian H DiracConstants M) : H →L[ℂ] H

theorem electron_number_conserved (H_D : DiracHamiltonian H DiracConstants M) (t : ℝ) (ψ : H) : ‖electronProjection H_D (H_D.U_grp.U t ψ)‖ = ‖electronProjection H_D ψ‖

theorem positron_number_conserved (H_D : DiracHamiltonian H DiracConstants M) (t : ℝ) (ψ : H) : ‖positronProjection H_D (H_D.U_grp.U t ψ)‖ = ‖positronProjection H_D ψ‖

theorem charge_conserved (H_D : DiracHamiltonian H DiracConstants M) (t : ℝ) (ψ : H) : ‖electronProjection H_D (H_D.U_grp.U t ψ)‖ ^ 2 - ‖positronProjection H_D (H_D.U_grp.U t ψ)‖ ^ 2 = ‖electronProjection H_D ψ‖ ^ 2 - ‖positronProjection H_D ψ‖ ^ 2

theorem sector_orthogonal (H_D : DiracHamiltonian H DiracConstants M) (hm : 0 < H_D.constants.m) : electronProjection H_D * positronProjection H_D = 0

theorem dirac_first_law {K M' : Type*} (H_D : DiracHamiltonian H K M') : FirstLawEquivalence H_D.U_grp
```

### `Resolvent/`

#### `Analytic.lean` (1 decl)

```lean
lemma resolventFun_hasSum {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (z₀ : OffRealAxis) (z : ℂ) (hz : ‖z - z₀.val‖ < |z₀.val.im|) : ∃ (hz' : z.im ≠ 0), HasSum (fun n => (z - z₀.val)^n • (resolventFun hsym hplus hminus z₀)^(n+1)) (resolvent z hz' hsym hplus hminus)
```

#### `Defs.lean` (12 decl)

```lean
def OffRealAxis : Type

lemma opNorm_pow_le (T : E →L[ℂ] E) (n : ℕ) : ‖T^n‖ ≤ ‖T‖^n

lemma opNorm_pow_tendsto_zero (T : E →L[ℂ] E) (hT : ‖T‖ < 1) : Tendsto (fun n => ‖T^n‖) atTop (𝓝 0)

noncomputable def neumannPartialSum (T : E →L[ℂ] E) (n : ℕ) : E →L[ℂ] E

noncomputable def neumannSeries (T : E →L[ℂ] E) (hT : ‖T‖ < 1) : E →L[ℂ] E

lemma neumannSeries_summable (T : E →L[ℂ] E) (hT : ‖T‖ < 1) : Summable (fun n => T ^ n)

lemma tsum_eq_neumannSeries (T : E →L[ℂ] E) (hT : ‖T‖ < 1) : ∑' n, T ^ n = neumannSeries T hT

lemma neumannSeries_hasSum (T : E →L[ℂ] E) (hT : ‖T‖ < 1) : HasSum (fun n => T ^ n) (neumannSeries T hT)

lemma neumannSeries_mul_left (T : E →L[ℂ] E) (hT : ‖T‖ < 1) : (ContinuousLinearMap.id ℂ E - T) * neumannSeries T hT = ContinuousLinearMap.id ℂ E

lemma neumannSeries_mul_right (T : E →L[ℂ] E) (hT : ‖T‖ < 1) : neumannSeries T hT * (ContinuousLinearMap.id ℂ E - T) = ContinuousLinearMap.id ℂ E

lemma isUnit_one_sub (T : E →L[ℂ] E) (hT : ‖T‖ < 1) : IsUnit (ContinuousLinearMap.id ℂ E - T)

lemma im_ne_zero_of_near {z₀ : ℂ} (_ : z₀.im ≠ 0) {z : ℂ} (hz : ‖z - z₀‖ < |z₀.im|) : z.im ≠ 0
```

### `Resolvent/Diagonal/`

#### `Basic.lean` (7 decl)

```lean
lemma resolvent_diag_laplace {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (U_grp : OneParameterUnitaryGroup (H

lemma im_resolvent_diag {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus  : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (z : ℂ) (hz : z.im ≠ 0) (ξ : H) : (⟪ξ, resolvent z hz hsym hplus hminus ξ⟫_ℂ).im = z.im * ‖resolvent z hz hsym hplus hminus ξ‖ ^ 2

lemma laplace_exp {z lambda : ℂ} (h : (lambda - z).im > 0) : ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * t)) * cexp (I * lambda * t) = I / (lambda - z)

lemma cauchy_kernel_laplace_neg_im {w : ℂ} (hw : w.im < 0) (lam : ℝ) : ((lam : ℂ) - w)⁻¹ = -I * ∫ t in Set.Ici (0 : ℝ), Complex.exp (-(I * w * (t : ℂ))) * Complex.exp (I * (lam : ℂ) * (t : ℂ))

lemma resolvent_continuous_at_height {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus  : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) {ε : ℝ} (hε : 0 < ε) (ξ : H) : Continuous (fun lambda : ℝ => resolvent (⟨lambda, ε⟩ : ℂ) hε.ne' hsym hplus hminus ξ)

lemma resolvent_diag_lower_laplace (U_grp : OneParameterUnitaryGroup (H

lemma resolvent_diag_upper_eq_conj (U_grp : OneParameterUnitaryGroup (H
```

### `Resolvent/Diagonal/IntegralZ/`

#### `Basic.lean` (1 decl)

```lean
theorem resolventIntegralZ_eq_resolvent {z : ℂ} (hz : z.im < 0) (φ : H) : resolventIntegralZ U_grp z φ = resolvent z (ne_of_lt hz) (generator_isFormalAdjoint U_grp) (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) φ
```

#### `Bulk.lean` (2 decl)

```lean
lemma genZ_bulk_pos {z : ℂ} (hz : z.im < 0) (φ : H) : Tendsto (fun h : ℝ => -((h : ℂ)⁻¹ • (cexp (I * z * (h : ℂ)) - 1) • ∫ t in Set.Ici h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)) (𝓝[>] 0) (𝓝 (-((I * z) • ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)))

lemma genZ_bulk_neg {z : ℂ} (φ : H) : Tendsto (fun h : ℝ => -(h : ℂ)⁻¹ • (cexp (I * z * (h : ℂ)) - 1) • ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) (𝓝[<] 0) (𝓝 (-((I * z) • ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)))
```

#### `Defs.lean` (3 decl)

```lean
noncomputable def resolventIntegralZ (z : ℂ) (φ : H) : H

lemma integrable_expZ_unitary {z : ℂ} (hz : z.im < 0) (φ : H) : IntegrableOn (fun t : ℝ => cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) (Set.Ici 0)

lemma unitary_apply_expZ_integral {z : ℂ} (hz : z.im < 0) (φ : H) (h : ℝ) : U_grp.U h (∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) = cexp (I * z * (h : ℂ)) • ∫ s in Set.Ici h, cexp (-(I * z * (s : ℂ))) • U_grp.U s φ
```

#### `DiffQuotient.lean` (2 decl)

```lean
lemma genZ_diffQuotient_pos {z : ℂ} (hz : z.im < 0) (φ : H) (h : ℝ) (hh : h > 0) : ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralZ U_grp z φ) - resolventIntegralZ U_grp z φ) = -((h : ℂ)⁻¹ • (cexp (I * z * (h : ℂ)) - 1) • ∫ t in Set.Ici h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) + ((h : ℂ)⁻¹ • ∫ t in Set.Ioc 0 h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)

lemma genZ_diffQuotient_neg {z : ℂ} (hz : z.im < 0) (φ : H) (h : ℝ) (hh : h < 0) : ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralZ U_grp z φ) - resolventIntegralZ U_grp z φ) = (-(h : ℂ)⁻¹ • cexp (I * z * (h : ℂ)) • ∫ t in Set.Ioc h 0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) + (-(h : ℂ)⁻¹ • (cexp (I * z * (h : ℂ)) - 1) • ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)
```

#### `GeneratorLim.lean` (2 decl)

```lean
lemma genZ_boundary_neg {z : ℂ} (φ : H) : Tendsto (fun h : ℝ => -(h : ℂ)⁻¹ • cexp (I * z * (h : ℂ)) • ∫ t in Set.Ioc h 0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) (𝓝[<] 0) (𝓝 φ)

lemma generator_limit_resolventIntegralZ {z : ℂ} (hz : z.im < 0) (φ : H) : Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h (resolventIntegralZ U_grp z φ) - resolventIntegralZ U_grp z φ)) (𝓝[≠] 0) (𝓝 (z • resolventIntegralZ U_grp z φ + φ))
```

#### `Shift.lean` (6 decl)

```lean
lemma expZ_orbit_continuous {z : ℂ} (φ : H) : Continuous (fun t : ℝ => cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)

lemma integral_Ici_orbit_split_Z {z : ℂ} (hz : z.im < 0) (φ : H) {a b : ℝ} (hab : a ≤ b) : ∫ t in Set.Ici a, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ = (∫ t in Set.Ioc a b, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) + ∫ t in Set.Ici b, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ

lemma unitary_shift_resolventIntegralZ {z : ℂ} (hz : z.im < 0) (φ : H) (h : ℝ) (hh : h > 0) : U_grp.U h (resolventIntegralZ U_grp z φ) - resolventIntegralZ U_grp z φ = (-I) • ((cexp (I * z * (h : ℂ)) - 1) • ∫ t in Set.Ici h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) - (-I) • ∫ t in Set.Ioc 0 h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ

lemma unitary_shift_resolventIntegralZ_neg {z : ℂ} (hz : z.im < 0) (φ : H) (h : ℝ) (hh : h < 0) : U_grp.U h (resolventIntegralZ U_grp z φ) - resolventIntegralZ U_grp z φ = (-I) • (cexp (I * z * (h : ℂ)) • ∫ t in Set.Ioc h 0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) + (-I) • ((cexp (I * z * (h : ℂ)) - 1) • ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)

lemma genZ_target_eq {z : ℂ} (φ : H) : z • resolventIntegralZ U_grp z φ + φ = -((I * z) • ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) + φ

lemma genZ_scalar (h : ℝ) : ((I * (h : ℂ))⁻¹ * (-I) : ℂ) = -(h : ℂ)⁻¹
```

#### `Tendsto.lean` (4 decl)

```lean
lemma tendsto_cexp_mul_sub_one_div {z : ℂ} : Tendsto (fun h : ℝ => (cexp (I * z * (h : ℂ)) - 1) / (h : ℂ)) (𝓝[≠] 0) (𝓝 (I * z))

lemma tendsto_integral_Ici_expZ_unitary {z : ℂ} (hz : z.im < 0) (φ : H) : Tendsto (fun h : ℝ => ∫ t in Set.Ici h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) (𝓝 0) (𝓝 (∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ))

lemma tendsto_average_integral_expZ_unitary {z : ℂ} (φ : H) : Tendsto (fun h : ℝ => (h⁻¹ : ℂ) • ∫ t in Set.Ioc 0 h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) (𝓝[>] 0) (𝓝 φ)

lemma tendsto_average_integral_expZ_unitary_neg {z : ℂ} (φ : H) : Tendsto (fun h : ℝ => ((-h)⁻¹ : ℂ) • ∫ t in Set.Ioc h 0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) (𝓝[<] 0) (𝓝 φ)
```

### `Resolvent/`

#### `Identities.lean` (6 decl)

```lean
lemma resolvent_identity {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : resolvent z hz hsym hplus hminus - resolvent w hw hsym hplus hminus = (z - w) • ((resolvent z hz hsym hplus hminus).comp (resolvent w hw hsym hplus hminus))

lemma resolvent_tendsto {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) {z : ℂ} (hz : z.im ≠ 0) {zn : ℕ → ℂ} (h_im_ne : ∀ n, (zn n).im ≠ 0) (h_lim : Tendsto zn atTop (𝓝 z)) (ξ : H) : Tendsto (fun n => resolvent (zn n) (h_im_ne n) hsym hplus hminus ξ) atTop (𝓝 (resolvent z hz hsym hplus hminus ξ))

lemma resolvent_commute {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus  : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : Commute (resolvent z hz hsym hplus hminus) (resolvent w hw hsym hplus hminus)

lemma resolvent_adjoint {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (z : ℂ) (hz : z.im ≠ 0) : (resolvent z hz hsym hplus hminus).adjoint = resolvent (starRingEnd ℂ z) (by simp only [Complex.conj_im, neg_ne_zero]; exact hz) hsym hplus hminus

lemma resolvent_inner_diag_conj {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) {z : ℂ} (hz : z.im ≠ 0) (hcz : (starRingEnd ℂ z).im ≠ 0) (ξ : H) : (starRingEnd ℂ) ⟪ξ, resolvent (starRingEnd ℂ z) hcz hsym hplus hminus ξ⟫_ℂ = ⟪ξ, resolvent z hz hsym hplus hminus ξ⟫_ℂ

noncomputable def resolventFun {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) : OffRealAxis → (H →L[ℂ] H)
```

### `Resolvent/Integral/`

#### `Domain.lean` (13 decl)

```lean
lemma range_plus_i_eq_top : ∀ φ : H, ∃ ψ : (generator U_grp).domain, generator U_grp ψ + I • (ψ : H) = φ

lemma range_minus_i_eq_top : ∀ φ : H, ∃ ψ : (generator U_grp).domain, generator U_grp ψ - I • (ψ : H) = φ

noncomputable def averagedVector (h : ℝ) (_ : h ≠ 0) (φ : H) : H

lemma averagedVector_tendsto (φ : H) : Tendsto (fun h : ℝ => if hh : h ≠ 0 then averagedVector U_grp h hh φ else φ) (𝓝[>] 0) (𝓝 φ)

lemma averagedVector_orbit_shift_integral (s h : ℝ) (φ : H) : U_grp.U s (∫ t in Set.Ioc 0 h, U_grp.U t φ) = ∫ t in Set.Ioc s (s + h), U_grp.U t φ

lemma integral_orbit_shift_arith (s h : ℝ) (φ : H) : (∫ t in s..(s + h), U_grp.U t φ) - ∫ t in (0:ℝ)..h, U_grp.U t φ = (∫ t in (h:ℝ)..(h + s), U_grp.U t φ) - ∫ t in (0:ℝ)..s, U_grp.U t φ

lemma averagedVector_quotient_tendsto_zero (φ : H) : Tendsto (fun s : ℝ => (s⁻¹ : ℂ) • ∫ t in (0:ℝ)..s, U_grp.U t φ) (𝓝[≠] 0) (𝓝 φ)

lemma averagedVector_quotient_tendsto_at (h : ℝ) (φ : H) : Tendsto (fun s : ℝ => (s⁻¹ : ℂ) • ∫ t in (h:ℝ)..(h + s), U_grp.U t φ) (𝓝[≠] 0) (𝓝 (U_grp.U h φ))

lemma averagedVector_difference_quotient (h : ℝ) (hh : h ≠ 0) (hpos : 0 < h) (φ : H) (s : ℝ) (_hs : s ≠ 0) : ((I * s)⁻¹ : ℂ) • (U_grp.U s (averagedVector U_grp h hh φ) - averagedVector U_grp h hh φ) = ((I * h)⁻¹ : ℂ) • (((s⁻¹ : ℂ) • ∫ t in (h:ℝ)..(h + s), U_grp.U t φ) - ((s⁻¹ : ℂ) • ∫ t in (0:ℝ)..s, U_grp.U t φ))

lemma averagedVector_in_domain (h : ℝ) (hh : h ≠ 0) (φ : H) : averagedVector U_grp h hh φ ∈ generatorDomain U_grp

lemma generatorDomain_dense_via_average : Dense (generatorDomain U_grp : Set H)

lemma generatorDomain_maximal (ψ : H) (h : ∃ η : H, Tendsto (fun t : ℝ => ((I : ℂ) * t)⁻¹ • (U_grp.U t ψ - ψ)) (𝓝[≠] 0) (𝓝 η)) : ψ ∈ generatorDomain U_grp

lemma generator_isSelfAdjoint : IsSelfAdjoint (generator U_grp)
```

#### `GroupIntegration.lean` (10 decl)

```lean
lemma continuous_unitary_apply (φ : H) : Continuous (fun t => U_grp.U t φ)

lemma integrable_exp_neg_unitary (φ : H) : IntegrableOn (fun t => Real.exp (-t) • U_grp.U t φ) (Set.Ici 0) volume

lemma integrable_exp_neg_unitary_neg (φ : H) : IntegrableOn (fun t => Real.exp (-t) • U_grp.U (-t) φ) (Set.Ici 0) volume

lemma norm_integral_exp_neg_unitary_le (φ : H) : ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ‖ ≤ ‖φ‖

lemma integrable_unitary_Ioc (φ : H) (h : ℝ) (_ : 0 < h) : IntegrableOn (fun t => U_grp.U t φ) (Set.Ioc 0 h) volume

noncomputable def resolventIntegralPlus (φ : H) : H

noncomputable def resolventIntegralMinus (φ : H) : H

lemma resolventIntegralPlus_add (φ₁ φ₂ : H) : resolventIntegralPlus U_grp (φ₁ + φ₂) = resolventIntegralPlus U_grp φ₁ + resolventIntegralPlus U_grp φ₂

lemma norm_resolventIntegralPlus_le (φ : H) : ‖resolventIntegralPlus U_grp φ‖ ≤ ‖φ‖

lemma norm_resolventIntegralMinus_le (φ : H) : ‖resolventIntegralMinus U_grp φ‖ ≤ ‖φ‖
```

### `Resolvent/Integral/Limits/`

#### `Helpers.lean` (18 decl)

```lean
lemma tendsto_exp_sub_one_div : Tendsto (fun h : ℝ => (Real.exp h - 1) / h) (𝓝[≠] 0) (𝓝 1)

lemma tendsto_integral_Ici_exp_unitary (φ : H) : Tendsto (fun h : ℝ => ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ) (𝓝 0) (𝓝 (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ))

lemma tendsto_average_integral_unitary (φ : H) : Tendsto (fun h : ℝ => (h⁻¹ : ℂ) • ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ) (𝓝[>] 0) (𝓝 φ)

lemma tendsto_average_integral_unitary_neg (φ : H) : Tendsto (fun h : ℝ => ((-h)⁻¹ : ℂ) • ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ) (𝓝[<] 0) (𝓝 φ)

lemma exp_neg_orbit_continuous (φ : H) : Continuous (fun t : ℝ => Real.exp (-t) • U_grp.U (-t) φ)

lemma exp_neg_orbit_at_zero (φ : H) : Real.exp (-(0 : ℝ)) • U_grp.U (-(0 : ℝ)) φ = φ

lemma tendsto_neg_nhdsWithin_Ioi : Tendsto (fun h : ℝ => -h) (𝓝[>] 0) (𝓝[<] 0)

lemma tendsto_neg_nhdsWithin_Iio : Tendsto (fun h : ℝ => -h) (𝓝[<] 0) (𝓝[>] 0)

lemma exp_neg_sub_one_div_tendsto_neg_one {l : Filter ℝ} (hl : Tendsto (fun h : ℝ => -h) l (𝓝[≠] 0)) : Tendsto (fun h : ℝ => (Real.exp (-h) - 1) / h) l (𝓝 (-1))

lemma exp_neg_sub_one_div_ofReal_tendsto_neg_one {l : Filter ℝ} (hl : Tendsto (fun h : ℝ => -h) l (𝓝[≠] 0)) : Tendsto (fun h : ℝ => ((Real.exp (-h) - 1) / h : ℂ)) l (𝓝 (-1))

lemma avg_exp_neg_orbit_tendsto (φ : H) : Tendsto (fun h : ℝ => h⁻¹ • ∫ t in (0:ℝ)..h, Real.exp (-t) • U_grp.U (-t) φ) (𝓝[≠] 0) (𝓝 φ)

lemma integral_Ici_sub_shift (φ : H) (h : ℝ) : ∫ t in Set.Ici 0, Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ = ∫ s in Set.Ici (-h), Real.exp (-s) • U_grp.U (-s) φ

lemma unitary_apply_Ici_orbit_integral (φ : H) (h : ℝ) : U_grp.U h (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) = Real.exp (-h) • ∫ s in Set.Ici (-h), Real.exp (-s) • U_grp.U (-s) φ

lemma integrableOn_Ici_of_Ici_zero {f : ℝ → H} (hcont : Continuous f) (h0 : IntegrableOn f (Set.Ici 0)) (b : ℝ) : IntegrableOn f (Set.Ici b)

lemma integral_Ici_split_of {f : ℝ → H} (hcont : Continuous f) (h0 : IntegrableOn f (Set.Ici 0)) {a b : ℝ} (hab : a ≤ b) : ∫ t in Set.Ici a, f t = (∫ t in Set.Ioc a b, f t) + ∫ t in Set.Ici b, f t

lemma exp_neg_orbit_continuous_plus (φ : H) : Continuous (fun t : ℝ => Real.exp (-t) • U_grp.U t φ)

lemma integrableOn_exp_neg_orbit_Ici (φ : H) (b : ℝ) : IntegrableOn (fun t => Real.exp (-t) • U_grp.U (-t) φ) (Set.Ici b)

lemma integral_Ici_orbit_split (φ : H) {a b : ℝ} (hab : a ≤ b) : ∫ t in Set.Ici a, Real.exp (-t) • U_grp.U (-t) φ = (∫ t in Set.Ioc a b, Real.exp (-t) • U_grp.U (-t) φ) + ∫ t in Set.Ici b, Real.exp (-t) • U_grp.U (-t) φ
```

#### `Minus.lean` (12 decl)

```lean
lemma unitary_shift_resolventIntegralMinus (φ : H) (h : ℝ) (hh : h > 0) : U_grp.U h (resolventIntegralMinus U_grp φ) - resolventIntegralMinus U_grp φ = I • (Real.exp (-h) • ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ) + I • ((Real.exp (-h) - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)

lemma unitary_shift_resolventIntegralMinus_neg (φ : H) (h : ℝ) (hh : h < 0) : U_grp.U h (resolventIntegralMinus U_grp φ) - resolventIntegralMinus U_grp φ = I • ((Real.exp (-h) - 1) • ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ) - I • ∫ t in Set.Ioc 0 (-h), Real.exp (-t) • U_grp.U (-t) φ

private lemma genMinus_target_eq (φ : H) : φ + I • resolventIntegralMinus U_grp φ = φ - ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ

private lemma genMinus_scalar (h : ℝ) : ((I * (h : ℂ))⁻¹ * I : ℂ) = (h : ℂ)⁻¹

private lemma genMinus_diffQuotient_pos (φ : H) (h : ℝ) (hh : h > 0) : ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralMinus U_grp φ) - resolventIntegralMinus U_grp φ) = ((h : ℂ)⁻¹ • Real.exp (-h) • ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ) + ((h : ℂ)⁻¹ • (Real.exp (-h) - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)

private lemma genMinus_diffQuotient_neg (φ : H) (h : ℝ) (hh : h < 0) : ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralMinus U_grp φ) - resolventIntegralMinus U_grp φ) = ((h : ℂ)⁻¹ • (Real.exp (-h) - 1) • ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ) + ((-(h : ℂ)⁻¹) • ∫ t in Set.Ioc 0 (-h), Real.exp (-t) • U_grp.U (-t) φ)

private lemma genMinus_bulk_pos (φ : H) : Tendsto (fun h : ℝ => (h : ℂ)⁻¹ • (Real.exp (-h) - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) (𝓝[>] 0) (𝓝 (-(∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)))

private lemma genMinus_boundary_pos (φ : H) : Tendsto (fun h : ℝ => (h : ℂ)⁻¹ • Real.exp (-h) • ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ) (𝓝[>] 0) (𝓝 φ)

private lemma genMinus_tail_continuous_neg (φ : H) : Tendsto (fun h : ℝ => ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ) (𝓝[<] 0) (𝓝 (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ))

private lemma genMinus_bulk_neg (φ : H) : Tendsto (fun h : ℝ => (h : ℂ)⁻¹ • (Real.exp (-h) - 1) • ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ) (𝓝[<] 0) (𝓝 (-(∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)))

private lemma genMinus_boundary_neg (φ : H) : Tendsto (fun h : ℝ => (-(h : ℂ)⁻¹) • ∫ t in Set.Ioc 0 (-h), Real.exp (-t) • U_grp.U (-t) φ) (𝓝[<] 0) (𝓝 φ)

lemma generator_limit_resolventIntegralMinus (φ : H) : Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h (resolventIntegralMinus U_grp φ) - resolventIntegralMinus U_grp φ)) (𝓝[≠] 0) (𝓝 (φ + I • resolventIntegralMinus U_grp φ))
```

#### `Plus.lean` (13 decl)

```lean
lemma integrableOn_exp_neg_orbit_Ici_plus (φ : H) (b : ℝ) : IntegrableOn (fun t => Real.exp (-t) • U_grp.U t φ) (Set.Ici b)

lemma integral_Ici_orbit_split_plus (φ : H) {a b : ℝ} (hab : a ≤ b) : ∫ t in Set.Ici a, Real.exp (-t) • U_grp.U t φ = (∫ t in Set.Ioc a b, Real.exp (-t) • U_grp.U t φ) + ∫ t in Set.Ici b, Real.exp (-t) • U_grp.U t φ

lemma unitary_apply_Ici_orbit_integral_plus (φ : H) (h : ℝ) : U_grp.U h (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ) = Real.exp h • ∫ s in Set.Ici h, Real.exp (-s) • U_grp.U s φ

lemma unitary_shift_resolventIntegralPlus (φ : H) (h : ℝ) (hh : h > 0) : U_grp.U h (resolventIntegralPlus U_grp φ) - resolventIntegralPlus U_grp φ = (-I) • ((Real.exp h - 1) • ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ) - (-I) • ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ

lemma unitary_shift_resolventIntegralPlus_neg (φ : H) (h : ℝ) (hh : h < 0) : U_grp.U h (resolventIntegralPlus U_grp φ) - resolventIntegralPlus U_grp φ = (-I) • (Real.exp h • ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ) + (-I) • ((Real.exp h - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)

lemma genPlus_target_eq (φ : H) : φ - I • resolventIntegralPlus U_grp φ = φ - ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ

lemma genPlus_scalar (h : ℝ) : ((I * (h : ℂ))⁻¹ * (-I) : ℂ) = -(h : ℂ)⁻¹

lemma genPlus_diffQuotient_pos (φ : H) (h : ℝ) (hh : h > 0) : ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralPlus U_grp φ) - resolventIntegralPlus U_grp φ) = -((h : ℂ)⁻¹ • (Real.exp h - 1) • ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ) + ((h : ℂ)⁻¹ • ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ)

lemma genPlus_diffQuotient_neg (φ : H) (h : ℝ) (hh : h < 0) : ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralPlus U_grp φ) - resolventIntegralPlus U_grp φ) = (-(h : ℂ)⁻¹ • Real.exp h • ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ) + (-(h : ℂ)⁻¹ • (Real.exp h - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)

lemma genPlus_bulk_pos (φ : H) : Tendsto (fun h : ℝ => -((h : ℂ)⁻¹ • (Real.exp h - 1) • ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ)) (𝓝[>] 0) (𝓝 (-(∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)))

lemma genPlus_boundary_neg (φ : H) : Tendsto (fun h : ℝ => -(h : ℂ)⁻¹ • Real.exp h • ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ) (𝓝[<] 0) (𝓝 φ)

lemma genPlus_bulk_neg (φ : H) : Tendsto (fun h : ℝ => -(h : ℂ)⁻¹ • (Real.exp h - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ) (𝓝[<] 0) (𝓝 (-(∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)))

lemma generator_limit_resolventIntegralPlus (φ : H) : Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h (resolventIntegralPlus U_grp φ) - resolventIntegralPlus U_grp φ)) (𝓝[≠] 0) (𝓝 (φ - I • resolventIntegralPlus U_grp φ))
```

### `Resolvent/`

#### `LowerBound.lean` (1 decl)

```lean
lemma lower_bound_estimate {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (z : ℂ) (_ : z.im ≠ 0) (ψ : H) (hψ : ψ ∈ A.domain) : ‖A ⟨ψ, hψ⟩ - z • ψ‖ ≥ |z.im| * ‖ψ‖
```

#### `NormExpansion.lean` (10 decl)

```lean
lemma inner_self_im_eq_zero_of_symmetric {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) : (⟪A ψ, (ψ : H)⟫_ℂ).im = 0

lemma inner_self_eq_re_of_symmetric {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) : ⟪A ψ, (ψ : H)⟫_ℂ = (⟪A ψ, (ψ : H)⟫_ℂ).re

lemma cross_term_re_eq_zero_of_symmetric {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) (s : ℂ) (hs : s.re = 0) : (⟪A ψ, s • (ψ : H)⟫_ℂ).re = 0

lemma cross_term_I_re_eq_zero {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) : (⟪A ψ, I • (ψ : H)⟫_ℂ).re = 0

lemma cross_term_neg_I_re_eq_zero {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) : (⟪A ψ, (-I) • (ψ : H)⟫_ℂ).re = 0

lemma norm_sq_sub_smul_of_symmetric {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) (s : ℂ) (hs : s.re = 0) : ‖A ψ - s • (ψ : H)‖^2 = ‖A ψ‖^2 + ‖s‖^2 * ‖(ψ : H)‖^2

lemma norm_sq_sub_I_smul {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) : ‖A ψ - I • (ψ : H)‖^2 = ‖A ψ‖^2 + ‖(ψ : H)‖^2

lemma norm_sq_add_I_smul {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) : ‖A ψ + I • (ψ : H)‖^2 = ‖A ψ‖^2 + ‖(ψ : H)‖^2

lemma norm_le_norm_sub_I_smul {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) : ‖(ψ : H)‖ ≤ ‖A ψ - I • (ψ : H)‖

lemma norm_le_norm_add_I_smul {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) : ‖(ψ : H)‖ ≤ ‖A ψ + I • (ψ : H)‖
```

#### `Range.lean` (8 decl)

```lean
private noncomputable def resolventSolution {A : H →ₗ.[ℂ] H} (z : ℂ) (hz : z.im ≠ 0) (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (φ : H) : H

private lemma resolventSolution_mem {A : H →ₗ.[ℂ] H} (z : ℂ) (hz : z.im ≠ 0) (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (φ : H) : resolventSolution z hz hsym hplus hminus φ ∈ A.domain

private lemma resolventSolution_eq {A : H →ₗ.[ℂ] H} (z : ℂ) (hz : z.im ≠ 0) (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (φ : H) : A ⟨resolventSolution z hz hsym hplus hminus φ, resolventSolution_mem z hz hsym hplus hminus φ⟩ - z • resolventSolution z hz hsym hplus hminus φ = φ

private lemma resolventSolution_add {A : H →ₗ.[ℂ] H} (z : ℂ) (hz : z.im ≠ 0) (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (φ₁ φ₂ : H) : resolventSolution z hz hsym hplus hminus (φ₁ + φ₂) = resolventSolution z hz hsym hplus hminus φ₁ + resolventSolution z hz hsym hplus hminus φ₂

private lemma resolventSolution_smul {A : H →ₗ.[ℂ] H} (z : ℂ) (hz : z.im ≠ 0) (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (c : ℂ) (φ : H) : resolventSolution z hz hsym hplus hminus (c • φ) = c • resolventSolution z hz hsym hplus hminus φ

private lemma resolventSolution_norm_le {A : H →ₗ.[ℂ] H} (z : ℂ) (hz : z.im ≠ 0) (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (φ : H) : ‖resolventSolution z hz hsym hplus hminus φ‖ ≤ (1 / |z.im|) * ‖φ‖

noncomputable def resolvent {A : H →ₗ.[ℂ] H} (z : ℂ) (hz : z.im ≠ 0) (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) : H →L[ℂ] H

theorem resolvent_bound {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (z : ℂ) (hz : z.im ≠ 0) : ‖resolvent z hz hsym hplus hminus‖ ≤ 1 / |z.im|
```

### `Resolvent/Range/`

#### `ClosedRange.lean` (3 decl)

```lean
lemma preimage_cauchySeq {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (z : ℂ) (hz : z.im ≠ 0) (ψ_seq : ℕ → A.domain) (hu_cauchy : CauchySeq (fun n => A (ψ_seq n) - z • (ψ_seq n : H))) : CauchySeq (fun n => (ψ_seq n : H))

lemma range_limit_mem {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (z : ℂ) (_  : z.im ≠ 0) (ψ_seq : ℕ → A.domain) (φ_lim : H) (hψ_seq : ∀ n, A (ψ_seq n) - z • (ψ_seq n : H) = φ_lim) (hψ_lim : ∃ ψ_lim, Tendsto (fun n => (ψ_seq n : H)) atTop (𝓝 ψ_lim)) : ∃ (ψ : A.domain), A ψ - z • (ψ : H) = φ_lim

lemma range_sub_smul_closed [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (z : ℂ) (hz : z.im ≠ 0) : IsClosed (Set.range (fun (ψ : A.domain) => A ψ - z • (ψ : H)))
```

#### `Orthogonal.lean` (4 decl)

```lean
lemma weak_eigenvalue_of_orthogonal_to_range {A : H →ₗ.[ℂ] H} (z : ℂ) (χ : H) (h_orth : ∀ (ψ : A.domain), ⟪A ψ - z • (ψ : H), χ⟫_ℂ = 0) : ∀ (ψ : H) (hψ : ψ ∈ A.domain), ⟪A ⟨ψ, hψ⟩, χ⟫_ℂ = (starRingEnd ℂ) z * ⟪ψ, χ⟫_ℂ

lemma relation_from_plus_i {A : H →ₗ.[ℂ] H} (z : ℂ) (χ : H) (h_eigen : ∀ (ψ : H) (hψ : ψ ∈ A.domain), ⟪A ⟨ψ, hψ⟩, χ⟫_ℂ = (starRingEnd ℂ) z * ⟪ψ, χ⟫_ℂ) : let z_bar

lemma relation_from_minus_i {A : H →ₗ.[ℂ] H} (z : ℂ) (χ : H) (h_eigen : ∀ (ψ : H) (hψ : ψ ∈ A.domain), ⟪A ⟨ψ, hψ⟩, χ⟫_ℂ = (starRingEnd ℂ) z * ⟪ψ, χ⟫_ℂ) : let z_bar

lemma orthogonal_range_eq_zero {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (z : ℂ) (hz : z.im ≠ 0) (χ : H) (h_orth : ∀ (ψ : A.domain), ⟪A ψ - z • (ψ : H), χ⟫_ℂ = 0) : χ = 0
```

#### `Surjectivity.lean` (5 decl)

```lean
def rangeSubmodule {A : H →ₗ.[ℂ] H} (z : ℂ) : Submodule ℂ H where carrier

lemma range_sub_smul_dense {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (z : ℂ) (hz : z.im ≠ 0) : Dense (Set.range (fun (ψ : A.domain) => A ψ - z • (ψ : H)))

lemma resolvent_unique {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (z : ℂ) (hz : z.im ≠ 0) (ψ : H) (hψ : ψ ∈ A.domain) (h : A ⟨ψ, hψ⟩ - z • ψ = 0) : ψ = 0

lemma solution_unique {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (z : ℂ) (hz : z.im ≠ 0) (φ : H) (ψ ψ' : A.domain) (hψ : A ψ - z • (ψ : H) = φ) (hψ' : A ψ' - z • (ψ' : H) = φ) : ψ = ψ'

lemma self_adjoint_range_all_z {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (z : ℂ) (hz : z.im ≠ 0) : ∀ φ : H, ∃! (ψ : A.domain), A ψ - z • (ψ : H) = φ
```

### `Resolvent/`

#### `SpecialCases.lean` (15 decl)

```lean
lemma resolvent_at_i_spec {A : H →ₗ.[ℂ] H} (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (φ : H) : ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ

lemma resolvent_at_i_unique {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (φ ψ₁ ψ₂ : H) (hψ₁ : ψ₁ ∈ A.domain) (hψ₂ : ψ₂ ∈ A.domain) (h₁ : A ⟨ψ₁, hψ₁⟩ - I • ψ₁ = φ) (h₂ : A ⟨ψ₂, hψ₂⟩ - I • ψ₂ = φ) : ψ₁ = ψ₂

noncomputable def Rminus {A : H →ₗ.[ℂ] H} (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (φ : H) : H

lemma Rminus_mem {A : H →ₗ.[ℂ] H} (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (φ : H) : Rminus hminus φ ∈ A.domain

lemma Rminus_eq {A : H →ₗ.[ℂ] H} (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (φ : H) : A ⟨Rminus hminus φ, Rminus_mem hminus φ⟩ - I • Rminus hminus φ = φ

noncomputable def resolvent_at_i {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) : H →L[ℂ] H where toFun φ

lemma resolvent_at_neg_i_unique {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (φ ψ₁ ψ₂ : H) (hψ₁ : ψ₁ ∈ A.domain) (hψ₂ : ψ₂ ∈ A.domain) (h₁ : A ⟨ψ₁, hψ₁⟩ + I • ψ₁ = φ) (h₂ : A ⟨ψ₂, hψ₂⟩ + I • ψ₂ = φ) : ψ₁ = ψ₂

noncomputable def Rplus {A : H →ₗ.[ℂ] H} (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (φ : H) : H

lemma Rplus_mem {A : H →ₗ.[ℂ] H} (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (φ : H) : Rplus hplus φ ∈ A.domain

lemma Rplus_eq {A : H →ₗ.[ℂ] H} (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (φ : H) : A ⟨Rplus hplus φ, Rplus_mem hplus φ⟩ + I • Rplus hplus φ = φ

noncomputable def resolvent_at_neg_i {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) : H →L[ℂ] H where toFun φ

lemma resolvent_at_i_bound {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) : ‖resolvent_at_i hsym hminus‖ ≤ 1

lemma resolvent_at_neg_i_bound {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) : ‖resolvent_at_neg_i hsym hplus‖ ≤ 1

lemma resolvent_at_neg_i_left_inverse {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (ψ : H) (hψ : ψ ∈ A.domain) : resolvent_at_neg_i hsym hplus (A ⟨ψ, hψ⟩ + I • ψ) = ψ

lemma resolvent_at_i_left_inverse {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (ψ : H) (hψ : ψ ∈ A.domain) : resolvent_at_i hsym hminus (A ⟨ψ, hψ⟩ - I • ψ) = ψ
```

#### `SpectralRepresentation.lean` (10 decl)

```lean
lemma sub_ne_zero_of_im_ne_zero (z : ℂ) (hz : z.im ≠ 0) (s : ℝ) : (s : ℂ) - z ≠ 0

lemma kernel_measurable (z : ℂ) (hz : z.im ≠ 0) : Measurable fun s : ℝ => ((s : ℂ) - z)⁻¹

lemma norm_kernel_le (z : ℂ) (hz : z.im ≠ 0) (s : ℝ) : ‖((s : ℂ) - z)⁻¹‖ ≤ 1 / |z.im|

lemma kernel_bdd (z : ℂ) (hz : z.im ≠ 0) : ∃ C, ∀ s : ℝ, ‖((s : ℂ) - z)⁻¹‖ ≤ C

lemma id_mul_kernel_decomp (z : ℂ) (hz : z.im ≠ 0) (s : ℝ) : (s : ℂ) * ((s : ℂ) - z)⁻¹ = 1 + z * ((s : ℂ) - z)⁻¹

lemma id_mul_kernel_measurable (z : ℂ) (hz : z.im ≠ 0) : Measurable fun s : ℝ => (s : ℂ) * ((s : ℂ) - z)⁻¹

lemma id_mul_kernel_bdd (z : ℂ) (hz : z.im ≠ 0) : ∃ C, ∀ s : ℝ, ‖(s : ℂ) * ((s : ℂ) - z)⁻¹‖ ≤ C

theorem resolvent_eq_spectralCalculus (z : ℂ) (hz : z.im ≠ 0) : resolvent z hz (generator_isFormalAdjoint U_grp) (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) = spectralCalculus U_grp (fun s : ℝ => ((s : ℂ) - z)⁻¹) (kernel_measurable z hz) (kernel_bdd z hz)

theorem inner_resolvent_diag_eq_integral (z : ℂ) (hz : z.im ≠ 0) (ξ : H) : ⟪ξ, resolvent z hz (generator_isFormalAdjoint U_grp) (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) ξ⟫_ℂ = ∫ s, ((s : ℂ) - z)⁻¹ ∂(borelMeasure U_grp ξ)

theorem im_inner_resolvent_diag (t : ℝ) {ε : ℝ} (hε : 0 < ε) (ξ : H) : (⟪ξ, resolvent (⟨t, ε⟩ : ℂ) hε.ne' (generator_isFormalAdjoint U_grp) (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) ξ⟫_ℂ).im = ∫ s, ε / ((s - t) ^ 2 + ε ^ 2) ∂(borelMeasure U_grp ξ)
```

### `SpectralTheory/`

#### `Algebra.lean` (21 decl)

```lean
theorem spectralProjection_congr {B₁ B₂ : Set ℝ} (h : B₁ = B₂) (h₁ : MeasurableSet B₁) (h₂ : MeasurableSet B₂) : spectralProjection U_grp B₁ h₁ = spectralProjection U_grp B₂ h₂

theorem spectralProjection_univ : spectralProjection U_grp Set.univ MeasurableSet.univ = ContinuousLinearMap.id ℂ H

theorem spectralProjection_empty : spectralProjection U_grp ∅ MeasurableSet.empty = 0

theorem spectralProjection_inter (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂) : spectralProjection U_grp B₁ hB₁ * spectralProjection U_grp B₂ hB₂ = spectralProjection U_grp (B₁ ∩ B₂) (hB₁.inter hB₂)

theorem spectralProjection_comm (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂) : spectralProjection U_grp B₁ hB₁ * spectralProjection U_grp B₂ hB₂ = spectralProjection U_grp B₂ hB₂ * spectralProjection U_grp B₁ hB₁

theorem spectralProjection_compl (B : Set ℝ) (hB : MeasurableSet B) : spectralProjection U_grp Bᶜ hB.compl = ContinuousLinearMap.id ℂ H - spectralProjection U_grp B hB

theorem spectralProjection_union (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂) (hdisj : Disjoint B₁ B₂) : spectralProjection U_grp (B₁ ∪ B₂) (hB₁.union hB₂) = spectralProjection U_grp B₁ hB₁ + spectralProjection U_grp B₂ hB₂

theorem norm_sq_spectralProjection (B : Set ℝ) (hB : MeasurableSet B) (φ : H) : ‖spectralProjection U_grp B hB φ‖ ^ 2 = ((borelMeasure U_grp φ) B).toReal

theorem spectralProjection_eq_zero_iff_measure_zero (B : Set ℝ) (hB : MeasurableSet B) (φ : H) : spectralProjection U_grp B hB φ = 0 ↔ borelMeasure U_grp φ B = 0

theorem borelMeasure_spectralProjection_supported (B : Set ℝ) (hB : MeasurableSet B) (φ : H) : borelMeasure U_grp (spectralProjection U_grp B hB φ) Bᶜ = 0

lemma iic_eq_iUnion_icc (N : ℝ) : Set.Iic N = ⋃ n : ℕ, Set.Icc (-(↑n : ℝ)) N

lemma ici_eq_iUnion_icc (N : ℝ) : Set.Ici N = ⋃ n : ℕ, Set.Icc N (↑n : ℝ)

theorem spectralProjection_finite_approx_below (N : ℝ) (φ : H) (hφ : spectralProjection U_grp (Set.Iic N) measurableSet_Iic φ ≠ 0) : ∃ M : ℕ, spectralProjection U_grp (Set.Icc (-(↑M : ℝ)) N) measurableSet_Icc φ ≠ 0

theorem spectralProjection_finite_approx_above (N : ℝ) (φ : H) (hφ : spectralProjection U_grp (Set.Ici N) measurableSet_Ici φ ≠ 0) : ∃ M : ℕ, spectralProjection U_grp (Set.Icc N (↑M : ℝ)) measurableSet_Icc φ ≠ 0

lemma abs_le_max_of_mem_Icc {a b s : ℝ} (hs : s ∈ Set.Icc a b) : |s| ≤ max |a| |b|

private lemma spectralProjection_re_inner_eq_integral (a b : ℝ) (φ : H) (hmem : spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ ∈ (generator U_grp).domain) : (⟪generator U_grp ⟨spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ, hmem⟩, spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ⟫_ℂ).re = (∫ s, s ∂(borelMeasure U_grp (spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ))) ∧ Integrable (fun s : ℝ => s) (borelMeasure U_grp (spectralProjection U_grp (Set.I...

theorem spectralProjection_energy_upper_bound (a b : ℝ) (φ : H) (hmem : spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ ∈ (generator U_grp).domain) : (⟪generator U_grp ⟨spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ, hmem⟩, spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ⟫_ℂ).re ≤ b * ‖spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ‖ ^ 2

theorem spectralProjection_energy_lower_bound (a b : ℝ) (φ : H) (hmem : spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ ∈ (generator U_grp).domain) : a * ‖spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ‖ ^ 2 ≤ (⟪generator U_grp ⟨spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ, hmem⟩, spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ⟫_ℂ).re

theorem generator_sub_smul_norm_le_Icc (a b s : ℝ) (has : a ≤ s) (_hsb : s ≤ b) (φ : H) (hmem : spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ ∈ (generator U_grp).domain) : ‖generator U_grp ⟨spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ, hmem⟩ - s • spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ‖ ≤ max (s - a) (b - s) * ‖spectralProjection U_grp (Set.Icc a b) measurableSet_Icc φ‖

theorem generator_has_arbitrarily_negative_energy (h_spectrum_below : ∀ N : ℝ, ∃ φ : H, spectralProjection U_grp (Set.Iic N) measurableSet_Iic φ ≠ 0) (bound : ℝ) : ∃ ψ : (generator U_grp).domain, (ψ : H) ≠ 0 ∧ (⟪generator U_grp ψ, (ψ : H)⟫_ℂ).re < bound * ‖(ψ : H)‖ ^ 2

theorem generator_has_arbitrarily_positive_energy (h_spectrum_above : ∀ N : ℝ, ∃ φ : H, spectralProjection U_grp (Set.Ici N) measurableSet_Ici φ ≠ 0) (bound : ℝ) : ∃ ψ : (generator U_grp).domain, (ψ : H) ≠ 0 ∧ (⟪generator U_grp ψ, (ψ : H)⟫_ℂ).re > bound * ‖(ψ : H)‖ ^ 2
```

### `SpectralTheory/Antilinear/`

#### `Conjugation.lean` (15 decl)

```lean
structure Conjugation (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where toLinearMap : H →ₗ⋆[ℂ] H involutive : ∀ ψ, toLinearMap (toLinearMap ψ) = ψ inner_map : ∀ ψ φ, ⟪toLinearMap ψ, toLinearMap φ⟫_ℂ = ⟪φ, ψ⟫_ℂ

instance : FunLike (Conjugation H) H H

lemma map_add (J : Conjugation H) (ψ φ : H) : J (ψ + φ) = J ψ + J φ

lemma map_smul (J : Conjugation H) (c : ℂ) (ψ : H) : J (c • ψ) = (starRingEnd ℂ c) • J ψ

lemma map_sub (J : Conjugation H) (ψ φ : H) : J (ψ - φ) = J ψ - J φ

lemma isometry (J : Conjugation H) : Isometry (⇑J)

lemma continuous (J : Conjugation H) : Continuous (⇑J)

lemma injective (J : Conjugation H) : Function.Injective (⇑J)

lemma surjective (J : Conjugation H) : Function.Surjective (⇑J)

lemma bijective (J : Conjugation H) : Function.Bijective (⇑J)

def IsTimeReversal (J : Conjugation H) (U_grp : OneParameterUnitaryGroup (H

lemma genDiffQuot_comm (hJ : IsTimeReversal J U_grp) (ψ : H) (t : ℝ) : genDiffQuot U_grp (J ψ) t = J (genDiffQuot U_grp ψ (-t))

lemma tendsto_genDiffQuot_comm (hJ : IsTimeReversal J U_grp) {ψ : H} (hψ : ψ ∈ generatorDomain U_grp) : Tendsto (genDiffQuot U_grp (J ψ)) (𝓝[≠] 0) (𝓝 (J (generator U_grp ⟨ψ, hψ⟩)))

lemma generator_mem_domain (hJ : IsTimeReversal J U_grp) {ψ : H} (hψ : ψ ∈ generatorDomain U_grp) : J ψ ∈ generatorDomain U_grp

lemma generator_comm (hJ : IsTimeReversal J U_grp) {ψ : H} (hψ : ψ ∈ generatorDomain U_grp) : generator U_grp ⟨J ψ, hJ.generator_mem_domain hψ⟩ = J (generator U_grp ⟨ψ, hψ⟩)
```

### `SpectralTheory/Calculus/`

#### `Bounded.lean` (16 decl)

```lean
lemma bounded_mul {g₁ g₂ : ℝ → ℂ} (h₁ : ∃ C, ∀ ω, ‖g₁ ω‖ ≤ C) (h₂ : ∃ C, ∀ ω, ‖g₂ ω‖ ≤ C) : ∃ C, ∀ ω, ‖g₁ ω * g₂ ω‖ ≤ C

lemma char_bdd (t : ℝ) : ∃ C, ∀ ω : ℝ, ‖cexp (I * ω * t)‖ ≤ C

noncomputable def spectralFormBilin (g : ℝ → ℂ) (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) : H →L⋆[ℂ] H →L[ℂ] ℂ

noncomputable def spectralCalculus (g : ℝ → ℂ) (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) : H →L[ℂ] H

theorem inner_spectralCalculus (g : ℝ → ℂ) (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (ξ η : H) : ⟪ξ, spectralCalculus U_grp g hg_meas hg_bdd η⟫_ℂ = spectralForm U_grp ξ η g

private lemma calculus_ext {A B : H →L[ℂ] H} (h : ∀ ξ η : H, ⟪ξ, A η⟫_ℂ = ⟪ξ, B η⟫_ℂ) : A = B

theorem spectralCalculus_char (t : ℝ) : spectralCalculus U_grp (fun l => cexp (I * l * t)) (char_measurable t) (char_bdd t) = U_grp.U t

theorem spectralCalculus_one : spectralCalculus U_grp (fun _ => (1 : ℂ)) measurable_const ⟨1, fun _ => norm_one.le⟩ = ContinuousLinearMap.id ℂ H

theorem spectralCalculus_add (g₁ g₂ : ℝ → ℂ) (h₁m : Measurable g₁) (h₁b : ∃ C, ∀ ω, ‖g₁ ω‖ ≤ C) (h₂m : Measurable g₂) (h₂b : ∃ C, ∀ ω, ‖g₂ ω‖ ≤ C) (hm : Measurable fun l => g₁ l + g₂ l) (hb : ∃ C, ∀ ω, ‖g₁ ω + g₂ ω‖ ≤ C) : spectralCalculus U_grp (fun l => g₁ l + g₂ l) hm hb = spectralCalculus U_grp g₁ h₁m h₁b + spectralCalculus U_grp g₂ h₂m h₂b

theorem spectralCalculus_smul (c : ℂ) (g : ℝ → ℂ) (hm : Measurable g) (hb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (hcm : Measurable fun l => c * g l) (hcb : ∃ C, ∀ ω, ‖c * g ω‖ ≤ C) : spectralCalculus U_grp (fun l => c * g l) hcm hcb = c • spectralCalculus U_grp g hm hb

theorem spectralCalculus_adjoint (g : ℝ → ℂ) (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (hcg_meas : Measurable fun l => (starRingEnd ℂ) (g l)) (hcg_bdd : ∃ C, ∀ ω, ‖(starRingEnd ℂ) (g ω)‖ ≤ C) : ContinuousLinearMap.adjoint (spectralCalculus U_grp g hg_meas hg_bdd) = spectralCalculus U_grp (fun l => (starRingEnd ℂ) (g l)) hcg_meas hcg_bdd

theorem spectralForm_calculus_right (g h : ℝ → ℂ) (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (hh_meas : Measurable h) (hh_bdd : ∃ C, ∀ ω, ‖h ω‖ ≤ C) (ξ η : H) : spectralForm U_grp ξ (spectralCalculus U_grp g hg_meas hg_bdd η) h = spectralForm U_grp ξ η (fun l => h l * g l)

theorem spectralCalculus_mul (g h : ℝ → ℂ) (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (hh_meas : Measurable h) (hh_bdd : ∃ C, ∀ ω, ‖h ω‖ ≤ C) (hhg_meas : Measurable fun l => h l * g l) (hhg_bdd : ∃ C, ∀ ω, ‖h ω * g ω‖ ≤ C) : spectralCalculus U_grp h hh_meas hh_bdd * spectralCalculus U_grp g hg_meas hg_bdd = spectralCalculus U_grp (fun l => h l * g l) hhg_meas hhg_bdd

theorem spectralCalculus_comm (g h : ℝ → ℂ) (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (hh_meas : Measurable h) (hh_bdd : ∃ C, ∀ ω, ‖h ω‖ ≤ C) : spectralCalculus U_grp h hh_meas hh_bdd * spectralCalculus U_grp g hg_meas hg_bdd = spectralCalculus U_grp g hg_meas hg_bdd * spectralCalculus U_grp h hh_meas hh_bdd

theorem norm_sq_spectralCalculus_apply (g : ℝ → ℂ) (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (ξ : H) : ‖spectralCalculus U_grp g hg_meas hg_bdd ξ‖ ^ 2 = ∫ l, ‖g l‖ ^ 2 ∂(borelMeasure U_grp ξ)

theorem norm_spectralCalculus_le (g : ℝ → ℂ) (hg_meas : Measurable g) (hg_bdd : ∃ C', ∀ ω, ‖g ω‖ ≤ C') {C : ℝ} (hC : ∀ ω, ‖g ω‖ ≤ C) : ‖spectralCalculus U_grp g hg_meas hg_bdd‖ ≤ C
```

### `SpectralTheory/Measure/`

#### `Convergence.lean` (10 decl)

```lean
lemma bounded_add {g₁ g₂ : ℝ → ℂ} (h₁ : ∃ C, ∀ ω, ‖g₁ ω‖ ≤ C) (h₂ : ∃ C, ∀ ω, ‖g₂ ω‖ ≤ C) : ∃ C, ∀ ω, ‖g₁ ω + g₂ ω‖ ≤ C

lemma bounded_sub {g₁ g₂ : ℝ → ℂ} (h₁ : ∃ C, ∀ ω, ‖g₁ ω‖ ≤ C) (h₂ : ∃ C, ∀ ω, ‖g₂ ω‖ ≤ C) : ∃ C, ∀ ω, ‖g₁ ω - g₂ ω‖ ≤ C

theorem spectralCalculus_congr {g₁ g₂ : ℝ → ℂ} (h : g₁ = g₂) (h₁m : Measurable g₁) (h₁b : ∃ C, ∀ ω, ‖g₁ ω‖ ≤ C) (h₂m : Measurable g₂) (h₂b : ∃ C, ∀ ω, ‖g₂ ω‖ ≤ C) : spectralCalculus U_grp g₁ h₁m h₁b = spectralCalculus U_grp g₂ h₂m h₂b

theorem spectralCalculus_sub (g₁ g₂ : ℝ → ℂ) (h₁m : Measurable g₁) (h₁b : ∃ C, ∀ ω, ‖g₁ ω‖ ≤ C) (h₂m : Measurable g₂) (h₂b : ∃ C, ∀ ω, ‖g₂ ω‖ ≤ C) (hm : Measurable fun l => g₁ l - g₂ l) (hb : ∃ C, ∀ ω, ‖g₁ ω - g₂ ω‖ ≤ C) : spectralCalculus U_grp (fun l => g₁ l - g₂ l) hm hb = spectralCalculus U_grp g₁ h₁m h₁b - spectralCalculus U_grp g₂ h₂m h₂b

theorem tendsto_spectralCalculus_apply {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {G : ι → ℝ → ℂ} {g : ℝ → ℂ} (hG_meas : ∀ n, Measurable (G n)) (hG_bdd : ∀ n, ∃ C, ∀ ω, ‖G n ω‖ ≤ C) (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) {C : ℝ} (hunif : ∀ n ω, ‖G n ω‖ ≤ C) (hlim : ∀ ω, Tendsto (fun n => G n ω) l (𝓝 (g ω))) (ξ : H) : Tendsto (fun n => spectralCalculus U_grp (G n) (hG_meas n) (hG_bdd n) ξ) l (𝓝 (spectralCalculus U_grp g hg_meas hg_bdd ξ))

lemma indicator_one_bdd (B : Set ℝ) : ∃ C, ∀ ω, ‖Set.indicator B (fun _ => (1 : ℂ)) ω‖ ≤ C

noncomputable def spectralProjection (B : Set ℝ) (hB : MeasurableSet B) : H →L[ℂ] H

theorem spectralProjection_idem (B : Set ℝ) (hB : MeasurableSet B) : spectralProjection U_grp B hB * spectralProjection U_grp B hB = spectralProjection U_grp B hB

theorem spectralProjection_adjoint (B : Set ℝ) (hB : MeasurableSet B) : ContinuousLinearMap.adjoint (spectralProjection U_grp B hB) = spectralProjection U_grp B hB

theorem inner_spectralProjection_self (B : Set ℝ) (hB : MeasurableSet B) (ξ : H) : ⟪ξ, spectralProjection U_grp B hB ξ⟫_ℂ = (((borelMeasure U_grp ξ) B).toReal : ℂ)
```

#### `GeneratorLink.lean` (21 decl)

```lean
lemma tendsto_char_diffQuot (lam : ℝ) : Tendsto (fun t : ℝ => (I * (t : ℂ))⁻¹ * (cexp (I * lam * t) - 1)) (𝓝[≠] (0 : ℝ)) (𝓝 (lam : ℂ))

lemma norm_char_sub_one_le (x : ℝ) : ‖cexp (I * x) - 1‖ ≤ 2 * |x|

lemma norm_genDiffQuot_symbol_le (g : ℝ → ℂ) {Cg : ℝ} (hC : ∀ ω, ‖(ω : ℝ) * g ω‖ ≤ Cg) (t lam : ℝ) : ‖(I * (t : ℂ))⁻¹ * (cexp (I * lam * t) * g lam - g lam)‖ ≤ 2 * Cg

lemma genDiffQuot_symbol_measurable (g : ℝ → ℂ) (hm : Measurable g) (t : ℝ) : Measurable fun l : ℝ => (I * (t : ℂ))⁻¹ * (cexp (I * l * t) * g l - g l)

lemma genDiffQuot_symbol_bdd (g : ℝ → ℂ) {Cg : ℝ} (hC : ∀ ω, ‖(ω : ℝ) * g ω‖ ≤ Cg) (t : ℝ) : ∃ C, ∀ (ω : ℝ) , ‖(I * (t : ℂ))⁻¹ * (cexp (I * ω * t) * g ω - g ω)‖ ≤ C

lemma tendsto_genDiffQuot_symbol (g : ℝ → ℂ) (lam : ℝ) : Tendsto (fun t : ℝ => (I * (t : ℂ))⁻¹ * (cexp (I * lam * t) * g lam - g lam)) (𝓝[≠] (0 : ℝ)) (𝓝 ((lam : ℂ) * g lam))

lemma genDiffQuot_spectralCalculus (g : ℝ → ℂ) (hm : Measurable g) (hb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (φ : H) (t : ℝ) (hGm : Measurable fun l : ℝ => (I * (t : ℂ))⁻¹ * (cexp (I * l * t) * g l - g l)) (hGb : ∃ C, ∀ (ω : ℝ), ‖(I * (t : ℂ))⁻¹ * (cexp (I * ω * t) * g ω - g ω)‖ ≤ C) : genDiffQuot U_grp (spectralCalculus U_grp g hm hb φ) t = spectralCalculus U_grp (fun l => (I * (t : ℂ))⁻¹ * (cexp (I * l * t) * g l - g l)) hGm hGb φ

theorem tendsto_genDiffQuot_spectralCalculus (g : ℝ → ℂ) (hm : Measurable g) (hb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (hidm : Measurable fun l : ℝ => (l : ℂ) * g l) (hidb : ∃ C, ∀ ω, ‖ω * g ω‖ ≤ C) (φ : H) : Tendsto (genDiffQuot U_grp (spectralCalculus U_grp g hm hb φ)) (𝓝[≠] (0 : ℝ)) (𝓝 (spectralCalculus U_grp (fun l => (l : ℂ) * g l) hidm hidb φ))

theorem spectralCalculus_mem_generatorDomain (g : ℝ → ℂ) (hm : Measurable g) (hb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (hidm : Measurable fun l : ℝ => (l : ℂ) * g l) (hidb : ∃ C, ∀ ω, ‖ω * g ω‖ ≤ C) (φ : H) : spectralCalculus U_grp g hm hb φ ∈ generatorDomain U_grp

theorem generator_spectralCalculus (g : ℝ → ℂ) (hm : Measurable g) (hb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (hidm : Measurable fun l : ℝ => (l : ℂ) * g l) (hidb : ∃ C, ∀ ω, ‖ω * g ω‖ ≤ C) (φ : H) : generator U_grp ⟨spectralCalculus U_grp g hm hb φ, spectralCalculus_mem_generatorDomain U_grp g hm hb hidm hidb φ⟩ = spectralCalculus U_grp (fun l => (l : ℂ) * g l) hidm hidb φ

lemma id_indicator_bdd {B : Set ℝ} {R : ℝ} (hR : ∀ x ∈ B, |x| ≤ R) : ∃ C, ∀ ω, ‖ω * Set.indicator B (fun _ => (1 : ℂ)) ω‖ ≤ C

lemma id_indicator_measurable {B : Set ℝ} (hB : MeasurableSet B) : Measurable fun l : ℝ => (l : ℂ) * Set.indicator B (fun _ => (1 : ℂ)) l

theorem spectralProjection_mem_generatorDomain {B : Set ℝ} (hB : MeasurableSet B) {R : ℝ} (hR : ∀ x ∈ B, |x| ≤ R) (φ : H) : spectralProjection U_grp B hB φ ∈ generatorDomain U_grp

theorem generator_spectralProjection {B : Set ℝ} (hB : MeasurableSet B) {R : ℝ} (hR : ∀ x ∈ B, |x| ≤ R) (φ : H) : generator U_grp ⟨spectralProjection U_grp B hB φ, spectralProjection_mem_generatorDomain U_grp hB hR φ⟩ = spectralCalculus U_grp (fun l => (l : ℂ) * Set.indicator B (fun _ => (1 : ℂ)) l) (id_indicator_measurable hB) (id_indicator_bdd hR) φ

lemma spectralCalculus_group_comm (g : ℝ → ℂ) (hm : Measurable g) (hb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (t : ℝ) (x : H) : spectralCalculus U_grp g hm hb (U_grp.U t x) = U_grp.U t (spectralCalculus U_grp g hm hb x)

lemma genDiffQuot_spectralCalculus_comm (g : ℝ → ℂ) (hm : Measurable g) (hb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (x : H) : genDiffQuot U_grp (spectralCalculus U_grp g hm hb x) = fun t => spectralCalculus U_grp g hm hb (genDiffQuot U_grp x t)

lemma tendsto_genDiffQuot_spectralCalculus_comm (g : ℝ → ℂ) (hm : Measurable g) (hb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (x : (generator U_grp).domain) : Tendsto (genDiffQuot U_grp (spectralCalculus U_grp g hm hb (x : H))) (𝓝[≠] (0 : ℝ)) (𝓝 (spectralCalculus U_grp g hm hb (generator U_grp x)))

theorem spectralCalculus_mem_generatorDomain_of_mem (g : ℝ → ℂ) (hm : Measurable g) (hb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (x : (generator U_grp).domain) : spectralCalculus U_grp g hm hb (x : H) ∈ generatorDomain U_grp

theorem generator_spectralCalculus_comm (g : ℝ → ℂ) (hm : Measurable g) (hb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (x : (generator U_grp).domain) : generator U_grp ⟨spectralCalculus U_grp g hm hb (x : H), spectralCalculus_mem_generatorDomain_of_mem U_grp g hm hb x⟩ = spectralCalculus U_grp g hm hb (generator U_grp x)

theorem spectralProjection_mem_generatorDomain_of_mem {B : Set ℝ} (hB : MeasurableSet B) (x : (generator U_grp).domain) : spectralProjection U_grp B hB (x : H) ∈ generatorDomain U_grp

theorem generator_spectralProjection_comm {B : Set ℝ} (hB : MeasurableSet B) (x : (generator U_grp).domain) : generator U_grp ⟨spectralProjection U_grp B hB (x : H), spectralProjection_mem_generatorDomain_of_mem U_grp hB x⟩ = spectralProjection U_grp B hB (generator U_grp x)
```

#### `Polarized.lean` (19 decl)

```lean
noncomputable def spectralForm (ξ η : H) (g : ℝ → ℂ) : ℂ

theorem spectralForm_char (ξ η : H) (t : ℝ) : spectralForm U_grp ξ η (fun l => cexp (I * l * t)) = ⟪ξ, U_grp.U t η⟫_ℂ

theorem spectralForm_self (ξ : H) {g : ℝ → ℂ} (_hg_meas : Measurable g) (_hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) : spectralForm U_grp ξ ξ g = ∫ l, g l ∂(borelMeasure U_grp ξ)

theorem spectralForm_one (ξ η : H) : spectralForm U_grp ξ η (fun _ => (1 : ℂ)) = ⟪ξ, η⟫_ℂ

theorem spectralForm_add_right (ξ η₁ η₂ : H) {g : ℝ → ℂ} (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) : spectralForm U_grp ξ (η₁ + η₂) g = spectralForm U_grp ξ η₁ g + spectralForm U_grp ξ η₂ g

theorem spectralForm_smul_right (ξ η : H) (c : ℂ) {g : ℝ → ℂ} (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) : spectralForm U_grp ξ (c • η) g = c * spectralForm U_grp ξ η g

theorem spectralForm_conj_symm (ξ η : H) {g : ℝ → ℂ} (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) : spectralForm U_grp η ξ g = starRingEnd ℂ (spectralForm U_grp ξ η (fun l => starRingEnd ℂ (g l)))

theorem spectralForm_add_left (ξ₁ ξ₂ η : H) {g : ℝ → ℂ} (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) : spectralForm U_grp (ξ₁ + ξ₂) η g = spectralForm U_grp ξ₁ η g + spectralForm U_grp ξ₂ η g

theorem spectralForm_smul_left (ξ η : H) (c : ℂ) {g : ℝ → ℂ} (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) : spectralForm U_grp (c • ξ) η g = (starRingEnd ℂ) c * spectralForm U_grp ξ η g

lemma integrable_of_bounded {ρ : Measure ℝ} [IsFiniteMeasure ρ] {F : ℝ → ℂ} (hF : Measurable F) {C : ℝ} (hC : ∀ ω, ‖F ω‖ ≤ C) : Integrable F ρ

theorem spectralForm_add_fun (ξ η : H) {g₁ g₂ : ℝ → ℂ} (hg₁_meas : Measurable g₁) (hg₁_bdd : ∃ C, ∀ ω, ‖g₁ ω‖ ≤ C) (hg₂_meas : Measurable g₂) (hg₂_bdd : ∃ C, ∀ ω, ‖g₂ ω‖ ≤ C) : spectralForm U_grp ξ η (fun l => g₁ l + g₂ l) = spectralForm U_grp ξ η g₁ + spectralForm U_grp ξ η g₂

theorem spectralForm_smul_fun (ξ η : H) (c : ℂ) (g : ℝ → ℂ) : spectralForm U_grp ξ η (fun l => c * g l) = c * spectralForm U_grp ξ η g

theorem norm_spectralForm_le (ξ η : H) {g : ℝ → ℂ} {C : ℝ} (hg_meas : Measurable g) (hg_bdd : ∀ ω, ‖g ω‖ ≤ C) : ‖spectralForm U_grp ξ η g‖ ≤ 2 * C * ‖ξ‖ * ‖η‖

lemma char_measurable (t : ℝ) : Measurable fun ω : ℝ => cexp (I * ω * t)

private lemma neg_char_measurable (t : ℝ) : Measurable fun ω : ℝ => cexp (-(I * ω * t))

lemma char_norm_le_one (t ω : ℝ) : ‖cexp (I * ω * t)‖ ≤ 1

private lemma neg_char_norm_le_one (t ω : ℝ) : ‖cexp (-(I * ω * t))‖ ≤ 1

theorem spectralForm_unitary_right (ξ η : H) (t : ℝ) {g : ℝ → ℂ} (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) : spectralForm U_grp ξ (U_grp.U t η) g = spectralForm U_grp ξ η (fun l => cexp (I * l * t) * g l)

theorem spectralForm_unitary_left (ξ η : H) (t : ℝ) {g : ℝ → ℂ} (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) : spectralForm U_grp (U_grp.U t ξ) η g = spectralForm U_grp ξ η (fun l => cexp (-(I * l * t)) * g l)
```

### `SpectralTheory/StoneFormula/`

#### `Basic.lean` (20 decl)

```lean
noncomputable def averagedIndicator (a b : ℝ) : ℝ → ℝ

lemma arctan_kernel_pointwise_limit (a b s : ℝ) (hab : a < b) : Tendsto (fun ε : ℝ => (1 / Real.pi) * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε))) (𝓝[>] 0) (𝓝 (averagedIndicator a b s))

lemma arctan_kernel_abs_le_one (a b s ε : ℝ) : |(1 / Real.pi) * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε))| ≤ 1

noncomputable def stoneSymbol (a b ε : ℝ) : ℝ → ℂ

lemma stoneSymbol_measurable (a b ε : ℝ) : Measurable (stoneSymbol a b ε)

lemma stoneSymbol_norm_le_one (a b ε : ℝ) (s : ℝ) : ‖stoneSymbol a b ε s‖ ≤ 1

lemma stoneSymbol_bdd (a b ε : ℝ) : ∃ C, ∀ s, ‖stoneSymbol a b ε s‖ ≤ C

noncomputable def stoneLimit (a b : ℝ) : ℝ → ℂ

lemma stoneLimit_eq_indicators (a b : ℝ) (hab : a < b) : stoneLimit a b = fun s : ℝ => Set.indicator (Set.Ioo a b) (fun _ => (1 : ℂ)) s + ((1 / 2 : ℂ) * Set.indicator {a} (fun _ => (1 : ℂ)) s + (1 / 2 : ℂ) * Set.indicator {b} (fun _ => (1 : ℂ)) s)

lemma stoneLimit_measurable (a b : ℝ) (hab : a < b) : Measurable (stoneLimit a b)

lemma stoneLimit_bdd (a b : ℝ) : ∃ C, ∀ s, ‖stoneLimit a b s‖ ≤ C

lemma stoneSymbol_tendsto (a b : ℝ) (hab : a < b) (s : ℝ) : Tendsto (fun ε : ℝ => stoneSymbol a b ε s) (𝓝[>] 0) (𝓝 (stoneLimit a b s))

lemma spectralCalculus_stoneLimit (a b : ℝ) (hab : a < b) : spectralCalculus U_grp (stoneLimit a b) (stoneLimit_measurable a b hab) (stoneLimit_bdd a b) = spectralProjection U_grp (Set.Ioo a b) measurableSet_Ioo + ((1 / 2 : ℂ) • spectralProjection U_grp {a} (measurableSet_singleton a) + (1 / 2 : ℂ) • spectralProjection U_grp {b} (measurableSet_singleton b))

theorem stonesFormula (a b : ℝ) (hab : a < b) (ξ : H) : Tendsto (fun ε : ℝ => spectralCalculus U_grp (stoneSymbol a b ε) (stoneSymbol_measurable a b ε) (stoneSymbol_bdd a b ε) ξ) (𝓝[>] 0) (𝓝 ((spectralProjection U_grp (Set.Ioo a b) measurableSet_Ioo + ((1 / 2 : ℂ) • spectralProjection U_grp {a} (measurableSet_singleton a) + (1 / 2 : ℂ) • spectralProjection U_grp {b} (measurableSet_singleton b))) ξ))

theorem stonesFormula_of_measure_atom_zero (a b : ℝ) (hab : a < b) (ξ : H) (ha : borelMeasure U_grp ξ {a} = 0) (hb : borelMeasure U_grp ξ {b} = 0) : Tendsto (fun ε : ℝ => spectralCalculus U_grp (stoneSymbol a b ε) (stoneSymbol_measurable a b ε) (stoneSymbol_bdd a b ε) ξ) (𝓝[>] 0) (𝓝 (spectralProjection U_grp (Set.Ioo a b) measurableSet_Ioo ξ))

lemma inner_resolvent_diff_diag (t : ℝ) {ε : ℝ} (hε : 0 < ε) (ξ : H) : ⟪ξ, (resolvent (⟨t, ε⟩ : ℂ) hε.ne' (generator_isFormalAdjoint U_grp) (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) - resolvent (⟨t, -ε⟩ : ℂ) (neg_ne_zero.mpr hε.ne') (generator_isFormalAdjoint U_grp) (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp)) ξ⟫_ℂ = 2 * I * ((∫ s, ε / ((s - t) ^ 2 + ε ^ 2) ∂(borelMeasure U_grp ξ) : ℝ) : ℂ)

lemma lorentzian_fubini {μ : Measure ℝ} [IsFiniteMeasure μ] (a b : ℝ) {ε : ℝ} (hε : 0 < ε) : ∫ t in Set.Icc a b, ∫ s, ε / ((s - t) ^ 2 + ε ^ 2) ∂μ = ∫ s, (∫ t in Set.Icc a b, ε / ((s - t) ^ 2 + ε ^ 2)) ∂μ

lemma setIntegral_Icc_lorentzian (s a b ε : ℝ) (hab : a ≤ b) (hε : 0 < ε) : ∫ t in Set.Icc a b, ε / ((s - t) ^ 2 + ε ^ 2) = Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)

lemma inner_stoneSymbol_eq_resolvent_integral (a b : ℝ) (hab : a ≤ b) {ε : ℝ} (hε : 0 < ε) (ξ : H) : ⟪ξ, spectralCalculus U_grp (stoneSymbol a b ε) (stoneSymbol_measurable a b ε) (stoneSymbol_bdd a b ε) ξ⟫_ℂ = (1 / (2 * Real.pi * I)) * ∫ t in Set.Icc a b, ⟪ξ, (resolvent (⟨t, ε⟩ : ℂ) hε.ne' (generator_isFormalAdjoint U_grp) (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) - resolvent (⟨t, -ε⟩ : ℂ) (neg_ne_zero.mpr hε.ne') (generator_isFormalAdjoint U_grp) (range_plus_i_eq_top U_grp) (r...

theorem stonesFormula_inner (a b : ℝ) (hab : a < b) (ξ : H) : Tendsto (fun ε : ℝ => if hε : 0 < ε then (1 / (2 * Real.pi * I)) * ∫ t in Set.Icc a b, ⟪ξ, (resolvent (⟨t, ε⟩ : ℂ) hε.ne' (generator_isFormalAdjoint U_grp) (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) - resolvent (⟨t, -ε⟩ : ℂ) (neg_ne_zero.mpr hε.ne') (generator_isFormalAdjoint U_grp) (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp)) ξ⟫_ℂ else 0) (𝓝[>] 0) (𝓝 ⟪ξ, (spectralProjection U_grp (Set.Ioo a b) measurable...
```

#### `Identities.lean` (8 decl)

```lean
lemma resolvent_mem_domain {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus  : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (z : ℂ) (hz : z.im ≠ 0) (φ : H) : resolvent z hz hsym hplus hminus φ ∈ A.domain

lemma resolvent_solves {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus  : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (z : ℂ) (hz : z.im ≠ 0) (φ : H) : A ⟨resolvent z hz hsym hplus hminus φ, resolvent_mem_domain hsym hplus hminus z hz φ⟩ - z • resolvent z hz hsym hplus hminus φ = φ

lemma resolvent_left_inverse {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (hplus  : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (z : ℂ) (hz : z.im ≠ 0) (ψ : A.domain) : resolvent z hz hsym hplus hminus (A ψ - z • (ψ : H)) = (ψ : H)

theorem resolvent_comm (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : resolvent z hz (generator_isFormalAdjoint U_grp) (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) * resolvent w hw (generator_isFormalAdjoint U_grp) (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) = resolvent w hw (generator_isFormalAdjoint U_grp) (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) * resolvent z hz (generator_isFormalAdjoint U_grp) (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp)

theorem second_resolvent_identity {A B : H →ₗ.[ℂ] H} (hsymA : A.IsFormalAdjoint A) (hplusA  : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminusA : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (hsymB : B.IsFormalAdjoint B) (hplusB  : ∀ φ : H, ∃ ψ : B.domain, B ψ + I • (ψ : H) = φ) (hminusB : ∀ φ : H, ∃ ψ : B.domain, B ψ - I • (ψ : H) = φ) (z : ℂ) (hz : z.im ≠ 0) (ψ : H) (hA_dom : resolvent z hz hsymB hplusB hminusB ψ ∈ A.domain) : resolvent z hz hsymA hplusA hminusA ψ - resolvent z hz...

theorem born_series {A B : H →ₗ.[ℂ] H} (hsymA : A.IsFormalAdjoint A) (hplusA  : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (hminusA : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) (hsymB : B.IsFormalAdjoint B) (hplusB  : ∀ φ : H, ∃ ψ : B.domain, B ψ + I • (ψ : H) = φ) (hminusB : ∀ φ : H, ∃ ψ : B.domain, B ψ - I • (ψ : H) = φ) (V : H →L[ℂ] H) (h_dom : A.domain = B.domain) (hV : ∀ (ψ : H) (hψ : ψ ∈ A.domain), A ⟨ψ, hψ⟩ = B ⟨ψ, h_dom ▸ hψ⟩ + V ψ) (z : ℂ) (hz : z.im ≠ 0) (h_small : ‖V * re...

lemma resolvent_norm_blowup_at_spectrum (lambda₀ : ℝ) (h_spec : ∀ δ > 0, spectralProjection U_grp (Set.Ioo (lambda₀ - δ) (lambda₀ + δ)) measurableSet_Ioo ≠ 0) : Tendsto (fun ε : ℝ => if hε : 0 < ε then ‖resolvent (⟨lambda₀, ε⟩ : ℂ) hε.ne' (generator_isFormalAdjoint U_grp) (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp)‖ else 0) (𝓝[>] 0) atTop

theorem stieltjes_inversion (ψ : H) (lambda₀ : ℝ) (ρ : ℝ → ℝ) (hρ_cont : Continuous ρ) (hρ_nn : ∀ s, 0 ≤ ρ s) (hρ_density : ∀ B, MeasurableSet B → borelMeasure U_grp ψ B = ∫⁻ s in B, ENNReal.ofReal (ρ s)) : Tendsto (fun ε : ℝ => if hε : 0 < ε then (1 / Real.pi) * (⟪ψ, resolvent (⟨lambda₀, ε⟩ : ℂ) hε.ne' (generator_isFormalAdjoint U_grp) (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) ψ⟫_ℂ).im else 0) (𝓝[>] 0) (𝓝 (ρ lambda₀))
```

## Declarations by Namespace

| Namespace | Count | Declarations |
|-----------|------:|--------------|
| `MeasureTheory.Integral` | 9 | `integral_exp_neg_Ioc`, `integrableOn_exp_neg`, `integral_exp_neg_eq_one`, `integrableOn_exp_neg_Ioi`, `integrable_exp_decay_continuous`, `norm_integral_exp_decay_le`, `hasDerivAt_integral_of_exp_decay`, `fubini_Ioc`, `tendsto_integral_of_dominated_convergence` |
| `Spectra.Arctan` | 8 | `lorentzian_arctan_integral`, `arctanRecovery`, `tendsto_pos_div_zero_atTop`, `tendsto_neg_div_zero_atBot`, `arctanRecovery_tendsto_zero_of_lt`, `arctanRecovery_tendsto_zero_of_lt'`, `arctan_indicator_limit`, `arctan_kernel_bound` |
| `Spectra.Bochner` | 18 | `bochnerMeasureSpectral`, `bochnerMeasureSpectral_finite`, `fourierStieltjes_continuous`, `fourierStieltjes_conj_neg`, `fourierStieltjes_double_sum_nonneg`, `isPositiveDefinite_fourierStieltjes`, `isHermitian_fourierStieltjes`, `isContinuous_fourierStieltjes`, `bochner_existence`, `bochner_theorem`, ... (+8 more) |
| `Spectra.Bochner.GNS` | 76 | `GNSData`, `gnsQuotient_uniformContinuousConstSMul`, `gnsConstruction`, `pdNullSpace`, `mem_pdNullSpace`, `pdInner_eq_zero_of_null`, `pdNullSpace_submodule`, `pdNullSpace_translate_invariant`, `pdNullSpace_smul_mem`, `pdNullSubmodule`, ... (+66 more) |
| `Spectra.Borel` | 40 | `borelCDF`, `borelCDF_mono`, `borelCDF_nonneg`, `borelCDF_le`, `borelCDF_tendsto_atBot`, `borelCDF_continuous`, `borelEps_pos`, `borelApproxCDF`, `borelApproxCDF_mono`, `borelApproxCDF_bnd`, ... (+30 more) |
| `Spectra.Borel.SpectralMeasure` | 8 | `two_sided_split`, `m_eq_cauchy_transform`, `borelMeasure_fourier`, `spectral_scalar_measure_exists`, `borelMeasure_mass`, `borelMeasure_smul`, `borelMeasure_zero`, `borel_combination_ext` |
| `Spectra.Cayley` | 59 | `HasEigenvalue`, `IsBoundedBelow`, `isBoundedBelow_of_cayleyTransform_sub_smul_boundedBelow`, `isBoundedBelow_of_isUnit_cayleyTransform_sub_smul`, `norm_lower_bound_of_approx_eigenvalue_of_unit`, `cayley_neg_one_eigenvalue_iff`, `cayley_shift_identity`, `cayley_eigenvalue_correspondence`, `cayley_shift_injective`, `self_adjoint_norm_sq_add`, ... (+49 more) |
| `Spectra.Fourier` | 38 | `inner_unitary_neg`, `fourier_identity`, `fourier_kernel_eval`, `eq_of_fourier_decay_eq`, `fourier_uniqueness`, `poissonKernel_fourier`, `poissonKernel`, `poissonKernel_nonneg`, `sq_add_sq_pos`, `poissonKernel_continuous`, ... (+28 more) |
| `Spectra.Herglotz` | 73 | `withDensity_ofReal_eq_stieltjes_measure`, `stieltjes_rightLim_const`, `herglotz_lemma_stieltjes`, `fejerWeight`, `fejerWeight_nonneg`, `fejerWeight_zero`, `fejerMeanDensity`, `exp_conj_mul`, `fiber_count`, `double_sum_eq_weighted`, ... (+63 more) |
| `Spectra.Kernels` | 16 | `OffRealAxis`, `offRealPoint`, `offRealPointNeg`, `resolvent_integrand`, `lorentzian_nonneg`, `lorentzian_bound`, `lorentzian_total_integral`, `lorentzian_concentration`, `lorentzian_smul_integrable`, `lorentzian_approx_delta`, ... (+6 more) |
| `Spectra.Operator` | 34 | `SymmetricOperator`, `ShiftedDomainConditions`, `Unitary`, `mem_unitary_iff_Unitary`, `Unitary.inner_map_map`, `Unitary.norm_map`, `Unitary.injective`, `Unitary.surjective`, `Unitary.isUnit`, `ContinuousLinearMap.IsNormal`, ... (+24 more) |
| `Spectra.Operator.ShiftedDomainConditions` | 4 | `A'ψ`, `B'ψ`, `B'ψ_in_A_domain`, `A'ψ_in_B_domain` |
| `Spectra.Operator.SymmetricOperator` | 23 | `domain`, `apply`, `(anonymous)`, `toDomainElt`, `symmetric'`, `inner_self_im_eq_zero`, `inner_self_eq_re`, `apply_add`, `apply_smul`, `apply_sub`, ... (+13 more) |
| `Spectra.Operator.SymmetricOperator.DomainConditions` | 4 | `Aψ`, `Bψ`, `ABψ`, `BAψ` |
| `Spectra.PositiveDefinite` | 34 | `IsPositiveDefinite`, `PositiveDefiniteContinuous`, `tendsto_nhdsWithin_Ici_of_tendsto_nhdsWithin_Ioi`, `pd_at_zero_nonneg`, `pd_two_point_add`, `pd_two_point_sub`, `pd_two_point_I`, `pd_two_point_neg_I`, `IsHermitian`, `hermitian_at_zero_im`, ... (+24 more) |
| `Spectra.ProjValMeasure` | 9 | `unitaryCorrelation_smul`, `inner_op_eq_polarization`, `crossInner`, `crossInner_eq_inner_of_diag`, `crossInner_norm_le`, `cfc_norm_sq_eq_inner`, `diag_parallelogram`, `measure_eq_of_fourier_eq`, `spectralMeasure_parallelogram` |
| `Spectra.QuantumMechanics` | 5 | `LinearPMap.apply_congr`, `exists_unique_generator`, `stoneObservableEquiv`, `existsUnique_hamiltonian`, `OneParameterUnitaryGroup` |
| `Spectra.QuantumMechanics.BornRule` | 15 | `update_spacetimePoint_zero`, `update_spacetimePoint_succ`, `update_insertNth`, `insertNth_eq_update`, `hasDerivAt_re_comp`, `deriv_re_comp`, `differentiableAt_current_slice`, `leibniz_integral_rule`, `continuity_equation`, `integral_deriv_eq_zero_of_tendsto`, ... (+5 more) |
| `Spectra.QuantumMechanics.Dirac` | 93 | `diracAlpha1`, `diracAlpha2`, `diracAlpha3`, `diracBeta`, `diracAlpha1_sq`, `diracAlpha2_sq`, `diracAlpha3_sq`, `diracBeta_sq`, `diracAlpha12_anticommute`, `diracAlpha13_anticommute`, ... (+83 more) |
| `Spectra.QuantumMechanics.Dirac.Conservation` | 17 | `stdBasis`, `fourDivergence`, `partialDeriv'`, `star_dotProduct_conjTranspose_mulVec`, `current_adjoint_transfer`, `star_smul_dotProduct_add`, `neg_I_mul_ofReal_add_conj`, `dirac_divergence_bilinear_vanishes`, `diracCurrent_eq_dotProduct_mulVec`, `hasDerivAt_update`, ... (+7 more) |
| `Spectra.QuantumMechanics.Dirac.Current` | 17 | `GammaMatrices`, `standardGammaMatrices`, `Spacetime`, `SpinorField`, `SpinorField'`, `diracAdjoint`, `diracCurrent`, `gamma0_sq`, `gamma_conjTranspose_mul_gamma0`, `gamma0_gamma_selfadjoint`, ... (+7 more) |
| `Spectra.QuantumMechanics.Ehrenfest` | 3 | `inner_isBoundedBilinearMap_real`, `hasDerivAt_inner_cplx`, `ehrenfest_theorem` |
| `Spectra.QuantumMechanics.Heisenberg` | 4 | `SatisfiesCCR`, `norm_inner_commutator_of_ccr`, `heisenberg_uncertainty`, `heisenberg_variance` |
| `Spectra.QuantumMechanics.Observable` | 2 | `isFormalAdjoint_self_of_isSelfAdjoint`, `UnboundedObservable` |
| `Spectra.QuantumMechanics.Observable.UnboundedObservable` | 11 | `evolution`, `generator_evolution`, `evolution_generator_domain`, `evolution_mem_domain`, `schrodingerEquation`, `domain`, `dense`, `adjoint_eq`, `toSymmetricOperator`, `(anonymous)`, ... (+1 more) |
| `Spectra.QuantumMechanics.OneParameterUnitaryGroup` | 14 | `generatorObservable`, `inner_generator_invariant`, `inverse_eq_adjoint`, `norm_preserving`, `norm_one`, `genDiffQuot`, `genDiffQuot_add`, `genDiffQuot_smul`, `generatorDomain`, `generator`, ... (+4 more) |
| `Spectra.QuantumMechanics.Pauli` | 12 | `pauliX`, `pauliY`, `pauliZ`, `pauliX_hermitian`, `pauliY_hermitian`, `pauliZ_hermitian`, `pauliX_sq`, `pauliY_sq`, `pauliZ_sq`, `pauliXY_anticommute`, ... (+2 more) |
| `Spectra.QuantumMechanics.Schrodinger` | 19 | `schrödinger_equation₂`, `schrödinger_equation₁`, `schrödinger_equation₃`, `genToGroup_domain_invariant`, `schrödinger_of_selfAdjoint`, `sq_le_sq_of_nonneg`, `normSq_of_re_zero`, `normSq_eq_re_sq_add_im_sq`, `im_inner_shifted_eq_half_commutator`, `covariance`, ... (+9 more) |
| `Spectra.QuantumMechanics.SpectralTheory` | 105 | `group_apply_comm`, `unitary_group_surjective`, `mem_unitary`, `borelMeasure_unitary_invariant`, `quantum_liouville`, `spectral_moment_conserved`, `energyVariance`, `energyVariance_conserved`, `spectralProjection_group_comm`, `spectralProjection_norm_conserved`, ... (+95 more) |
| `Spectra.QuantumMechanics.SpectralTheory.Conjugation` | 9 | `(anonymous)`, `map_add`, `map_smul`, `map_sub`, `isometry`, `continuous`, `injective`, `surjective`, `bijective` |
| `Spectra.QuantumMechanics.SpectralTheory.IsTimeReversal` | 4 | `genDiffQuot_comm`, `tendsto_genDiffQuot_comm`, `generator_mem_domain`, `generator_comm` |
| `Spectra.QuantumMechanics.Stone.Yosida` | 78 | `yosidaApprox_norm_bound`, `yosidaJ_norm_bound`, `yosidaJNeg_norm_bound`, `yosidaApproxSym_commute`, `commute_exp`, `norm_expBounded_skewAdjoint`, `norm_expBounded_pairwise_le`, `expBounded_yosidaApproxSym_cauchy_intrinsic`, `yosidaApprox_eq_J_comp_A`, `yosidaApprox_tendsto_on_domain`, ... (+68 more) |
| `Spectra.QuantumMechanics.StonesTheorem` | 4 | `genToGroup`, `generator_genToGroup`, `stoneEquiv`, `stone_orbit_hasDerivAt` |
| `Spectra.QuantumMechanics.Stoneslemma` | 10 | `op_lower_bound`, `op_range_isClosed`, `op_range_dense`, `selfAdjoint_surjective_sub_smul`, `isSelfAdjoint_to_surjective`, `IsSelfAdjoint.eq_of_le`, `unitary_orbit_hasDerivAt`, `generator_comm`, `group_apply_curve_hasDerivAt`, `group_unique` |
| `Spectra.Resolvent` | 196 | `resolventFun_hasSum`, `OffRealAxis`, `opNorm_pow_le`, `opNorm_pow_tendsto_zero`, `neumannPartialSum`, `neumannSeries`, `neumannSeries_summable`, `tsum_eq_neumannSeries`, `neumannSeries_hasSum`, `neumannSeries_mul_left`, ... (+186 more) |
| `Spectra.Riesz` | 19 | `cfc_conjMul_inner_eq_normSq`, `cfc_re_inner_ofReal_nonneg`, `cfcHom_conjMul_inner_eq_normSq`, `complexify`, `rieszFunctional`, `rieszFunctional_nonneg`, `ccToC`, `spectralMeasure`, `integral_spectralMeasure`, `integral_spectralMeasure_continuous`, ... (+9 more) |
