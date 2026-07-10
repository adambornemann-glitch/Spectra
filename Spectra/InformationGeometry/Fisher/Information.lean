/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Score

/-!
# Fisher Information

The **Fisher information** is a symmetric positive-semidefinite bilinear
form on the parameter space of a regular statistical model, defined as
the second moment (= covariance, since `E_θ[s] = 0`) of the score:

  `g_{ij}(θ) = E_θ[sᵢ · sⱼ] = ∫ sᵢ(θ, ω) · sⱼ(θ, ω) · p(θ, ω) dμ(ω)`

For tangent vectors `v, w ∈ T_θ Θ ≅ ℝⁿ` the bilinear form reads:

  `g_θ(v, w) = E_θ[⟨v, s⟩ · ⟨w, s⟩]`

where `⟨v, s⟩ = ∑ᵢ vᵢ sᵢ` is the *directional score*.

## Main definitions

* `RegularStatisticalModel.ScoreSqIntegrableModel` — the standard Fisher
  regularity condition `E_θ[sᵢ²] = ∫ sᵢ² p dμ < ∞`.
* `RegularStatisticalModel.directionalScore` — `⟨v, s(θ, ω)⟩ = ∑ᵢ vᵢ sᵢ`.
* `RegularStatisticalModel.fisherMatrix` — `g_{ij}(θ) = E_θ[sᵢ sⱼ]`.
* `RegularStatisticalModel.fisherBilin` — `g_θ(v, w) = E_θ[⟨v,s⟩ ⟨w,s⟩]`.
* `RegularStatisticalModel.ScoreInjective` — score-injectivity at `θ`.

## Main statements

* `fisherMatrix_symm` — `g_{ij} = g_{ji}` (unconditional).
* `fisherBilin_symm` — `g(v, w) = g(w, v)` (unconditional).
* `fisherBilin_self_nonneg` — `g(v, v) ≥ 0` (unconditional).
* `fisherEntry_integrable` — `sᵢ sⱼ p ∈ L¹(μ)` via AM–GM (needs `hSq`).
* `directionalScore_eq_zero_ae` — `g(v,v) = 0 ⟹ ⟨v,s⟩ = 0` a.e.
* `fisherBilin_pos_def` — positive definiteness under score-injectivity.
* `fisherMatrix_eq_cov` — Fisher = covariance (since `E[s] = 0`).
* `fisherMatrix_eq_integral_partialDensity` — `g_{ij} = ∫ (∂ᵢp)(∂ⱼp)/p dμ`.

## Design note: integrability

The Fisher matrix entries `g_{ij}(θ) = E_θ[sᵢ sⱼ]` are finite iff the
score is square-integrable under the *model* distribution `P_θ`, i.e.,
`∫ sᵢ² · p dμ < ∞`.  This is exactly the `score_sq_integrable` field in
`RegularStatisticalModel`; `ScoreSqIntegrableModel` below repackages it as
a standalone predicate for results that take it as an explicit hypothesis.

Algebraic properties (symmetry, positive semidefiniteness) hold
unconditionally — they are pointwise identities or consequences of
`integral_nonneg`, which tolerates non-integrable integrands.

Results that genuinely need finite Fisher entries carry an explicit
hypothesis `hSq : M.ScoreSqIntegrableModel θ`.  This follows the
pattern set by `RegularStatisticalModel` itself: layer the regularity
so that each result states exactly what it needs.

## References

* S. Amari, *Information Geometry and Its Applications*, §2.2, 2016.
* R. A. Fisher, "Theory of statistical estimation",
  *Proc. Cambridge Phil. Soc.* **22** (1925), 700–725.
-/

noncomputable section

open MeasureTheory ENNReal Real Set Filter Finset

open scoped Topology

namespace Spectra.InformationGeometry

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

namespace RegularStatisticalModel

variable (M : RegularStatisticalModel n Ω)

/-! ### Score square-integrability under the model distribution -/

/-- The score is square-integrable under the *model* distribution:
  `E_θ[sᵢ²] = ∫ sᵢ(θ, ω)² · p(θ, ω) dμ(ω) < ∞`.

This is the standalone-predicate form of the `score_sq_integrable` field of
`RegularStatisticalModel`; it is the standard condition in information geometry
textbooks, and `score_memLp` exhibits it directly from the field. -/
def ScoreSqIntegrableModel (θ : ParamSpace n) : Prop :=
  ∀ i : Fin n,
    Integrable
      (fun ω => M.score θ i ω ^ 2 * M.density θ ω)
      M.refMeasure

/-! ### Score measurability -/

/-- The `i`-th score component `sᵢ(θ, ·)` is `AEStronglyMeasurable`
w.r.t. the reference measure.

**Proof sketch.** The partial derivative `∂ᵢ p(θ, ·)` is
`AEStronglyMeasurable` (it is a continuous-linear-map evaluation of
`fderiv ℝ (fun θ' => p(θ', ·)) θ`, which is `AEStronglyMeasurable`
by `density_fderiv_aestronglyMeasurable`).  The density `p(θ, ·)` is
`Measurable`.  Division of an `AEStronglyMeasurable` function by a
`Measurable` one is `AEStronglyMeasurable`. -/
lemma score_aestronglyMeasurable {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain) (i : Fin n) :
    AEStronglyMeasurable (M.score θ i) M.refMeasure := by
  -- score = partialDensity / density = partialDensity * (density)⁻¹
  change AEStronglyMeasurable (fun ω => M.partialDensity θ i ω / M.density θ ω) M.refMeasure
  -- Rewrite division as multiplication by inverse
  have : (fun ω => M.partialDensity θ i ω / M.density θ ω) =
         (fun ω => M.partialDensity θ i ω * (M.density θ ω)⁻¹) := by
    ext ω; rw [div_eq_mul_inv]
  rw [this]
  -- partialDensity is AEStronglyMeasurable
  have hPartial : AEStronglyMeasurable (M.partialDensity θ i) M.refMeasure :=
    M.partialDensity_aestronglyMeasurable hθ i
  -- density⁻¹ is Measurable (composition of measurable functions)
  have hInv : Measurable (fun ω => (M.density θ ω)⁻¹) :=
    (M.toStatisticalModel.density_measurable θ hθ).inv
  -- Multiplication preserves AEStronglyMeasurable
  exact hPartial.mul hInv.aestronglyMeasurable

/-! ### Directional score -/

/-- The **directional score** in direction `v`:
  `⟨v, s(θ, ω)⟩ = ∑ᵢ vᵢ · sᵢ(θ, ω)`.

This is the derivative of the log-likelihood in the tangent
direction `v`. -/
def directionalScore (θ : ParamSpace n) (v : ParamSpace n)
    (ω : Ω) : ℝ :=
  ∑ i : Fin n, v i * M.score θ i ω

/-- The directional score in standard basis direction `eⱼ` reduces
to the `j`-th score component. -/
@[simp]
lemma directionalScore_single (θ : ParamSpace n)
    (j : Fin n) (ω : Ω) :
    M.directionalScore θ (EuclideanSpace.single j 1) ω =
      M.score θ j ω := by
  simp only [directionalScore, PiLp.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [hij]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- Linearity of the directional score in `v` (pointwise in `ω`). -/
lemma directionalScore_add (θ : ParamSpace n)
    (v w : ParamSpace n) (ω : Ω) :
    M.directionalScore θ (v + w) ω =
      M.directionalScore θ v ω +
        M.directionalScore θ w ω := by
  simp only [directionalScore, PiLp.add_apply]
  -- ⊢ ∑ x, (v x + w x) * M.score θ x ω = ∑ x, v x * M.score θ x ω + ∑ x, w x * M.score θ x ω
  rw [← Finset.sum_add_distrib]
  congr 1
  ext x
  ring

/-- Scaling of the directional score (pointwise in `ω`). -/
lemma directionalScore_smul (θ : ParamSpace n)
    (c : ℝ) (v : ParamSpace n) (ω : Ω) :
    M.directionalScore θ (c • v) ω =
      c * M.directionalScore θ v ω := by
  simp only [directionalScore, PiLp.smul_apply, smul_eq_mul]
  -- ⊢ ∑ x, c * v x * M.score θ x ω = c * ∑ x, v x * M.score θ x ω
  rw [Finset.mul_sum]
  congr 1
  ext x
  ring

/-! ### Fisher information matrix -/

/-- The `(i, j)` entry of the **Fisher information matrix** at `θ`:
  `g_{ij}(θ) = E_θ[sᵢ sⱼ]
             = ∫ ω, sᵢ(θ, ω) · sⱼ(θ, ω) · p(θ, ω) dμ(ω)`.

Since `E_θ[sᵢ] = 0` (`score_expectation_eq_zero`), this is
simultaneously the second-moment matrix and the covariance matrix
of the score. -/
def fisherMatrix (θ : ParamSpace n) (i j : Fin n) : ℝ :=
  ∫ ω, M.score θ i ω * M.score θ j ω * M.density θ ω
    ∂M.refMeasure

/-- `g_{ij}(θ) = g_{ji}(θ)`. -/
lemma fisherMatrix_symm (θ : ParamSpace n)
    (i j : Fin n) :
    M.fisherMatrix θ i j = M.fisherMatrix θ j i := by
  simp only [fisherMatrix]; congr 1; ext ω; ring

/-- `g_{ii}(θ) ≥ 0`. -/
lemma fisherMatrix_diag_nonneg {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain) (i : Fin n) :
    0 ≤ M.fisherMatrix θ i i := by
  apply integral_nonneg; intro ω
  exact mul_nonneg (mul_self_nonneg _)
    (M.density_nonneg θ hθ ω)

/-! ### Fisher information bilinear form -/

/-- The **Fisher information bilinear form** on tangent vectors:
  `g_θ(v, w) = E_θ[⟨v, s⟩ · ⟨w, s⟩]
             = ∫ (∑ᵢ vᵢ sᵢ)(∑ⱼ wⱼ sⱼ) · p dμ`.

This will be promoted to a Riemannian metric in `FisherMetric.lean`. -/
def fisherBilin (θ : ParamSpace n)
    (v w : ParamSpace n) : ℝ :=
  ∫ ω, M.directionalScore θ v ω *
    M.directionalScore θ w ω *
    M.density θ ω ∂M.refMeasure

/-- `g_θ(v, w) = g_θ(w, v)`. -/
lemma fisherBilin_symm (θ : ParamSpace n)
    (v w : ParamSpace n) :
    M.fisherBilin θ v w = M.fisherBilin θ w v := by
  simp only [fisherBilin]; congr 1; ext ω; ring

/-- On standard basis vectors, the bilinear form recovers the
matrix entry: `g_θ(eᵢ, eⱼ) = g_{ij}(θ)`. -/
lemma fisherBilin_single (θ : ParamSpace n)
    (i j : Fin n) :
    M.fisherBilin θ (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) =
      M.fisherMatrix θ i j := by
  simp [fisherBilin, fisherMatrix]

/-! ### Positive semidefiniteness -/

/-- The integrand of `g_θ(v, v)` is pointwise nonneg. -/
lemma fisherBilin_integrand_nonneg {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain) (v : ParamSpace n) (ω : Ω) :
    0 ≤ M.directionalScore θ v ω *
      M.directionalScore θ v ω *
      M.density θ ω :=
  mul_nonneg (mul_self_nonneg _) (M.density_nonneg θ hθ ω)

/-- **Positive semidefiniteness:** `g_θ(v, v) ≥ 0` for all `v`.

Holds unconditionally (even without integrability of the score
under `P_θ`) because `integral_nonneg` applies to the Bochner
integral of any pointwise-nonneg function: it returns `0` if
the function is not integrable, and `0 ≤ ∫ f` otherwise. -/
lemma fisherBilin_self_nonneg {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain) (v : ParamSpace n) :
    0 ≤ M.fisherBilin θ v v := by
  apply integral_nonneg
  exact M.fisherBilin_integrand_nonneg hθ v

/-! ### Integrability of Fisher matrix entries

These results require `ScoreSqIntegrableModel M θ`, carried
explicitly as `hSq`. -/

/-- **Cross-integrability:** if each `sᵢ² · p` is integrable
then so is `sᵢ · sⱼ · p`.

Uses the AM–GM inequality `|a b| ≤ (a² + b²)/2` to dominate the
cross-term by the (integrable) sum of diagonal terms. -/
lemma fisherEntry_integrable {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain)
    (hSq : M.ScoreSqIntegrableModel θ) (i j : Fin n) :
    Integrable
      (fun ω => M.score θ i ω * M.score θ j ω *
        M.density θ ω) M.refMeasure := by
  -- Dominating function: ½(sᵢ² p + sⱼ² p)
  apply Integrable.mono'
    (((hSq i).add (hSq j)).div_const 2)
  · -- AEStronglyMeasurable: product of measurable functions
    exact ((M.score_aestronglyMeasurable hθ i).mul
      (M.score_aestronglyMeasurable hθ j)).mul
      (Measurable.aestronglyMeasurable
        (M.toStatisticalModel.density_measurable θ hθ))
  · -- Pointwise bound via AM–GM
    apply ae_of_all; intro ω
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (M.density_nonneg θ hθ ω)]
    have hp : 0 ≤ M.density θ ω := M.density_nonneg θ hθ ω
    -- |sᵢ| · |sⱼ| · p ≤ ½(sᵢ² + sⱼ²) · p
    -- from (|sᵢ| - |sⱼ|)² ≥ 0
    calc |M.score θ i ω| * |M.score θ j ω| *
              M.density θ ω
          = (|M.score θ i ω| * |M.score θ j ω|) *
              M.density θ ω := by ring
        _ ≤ ((M.score θ i ω ^ 2 +
              M.score θ j ω ^ 2) / 2) *
              M.density θ ω := by
            apply mul_le_mul_of_nonneg_right _ hp
            have _h : 0 ≤ (|M.score θ i ω| -
              |M.score θ j ω|) ^ 2 := sq_nonneg _
            nlinarith [sq_abs (M.score θ i ω),
                       sq_abs (M.score θ j ω)]
        _ = (M.score θ i ω ^ 2 * M.density θ ω +
              M.score θ j ω ^ 2 * M.density θ ω) / 2 := by
            ring

/-- `g_θ(v, w) = ∑ᵢ ∑ⱼ vᵢ wⱼ g_{ij}(θ)`.

Requires integrability to exchange `∫` and `∑` (the sums are
finite so the exchange is `integral_finset_sum`; each summand
is integrable by `fisherEntry_integrable`). -/
lemma fisherBilin_eq_sum_fisherMatrix {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain)
    (hSq : M.ScoreSqIntegrableModel θ)
    (v w : ParamSpace n) :
    M.fisherBilin θ v w =
      ∑ i : Fin n, ∑ j : Fin n,
        v i * w j * M.fisherMatrix θ i j := by
  simp only [fisherBilin, fisherMatrix, directionalScore]
  -- Expand (∑ᵢ vᵢsᵢ)(∑ⱼ wⱼsᵢ) = ∑ᵢⱼ vᵢwⱼsᵢsⱼ inside the integrand
  have expand : ∀ ω,
      (∑ i, v i * M.score θ i ω) * (∑ j, w j * M.score θ j ω) * M.density θ ω =
      ∑ i, ∑ j, v i * w j * M.score θ i ω * M.score θ j ω * M.density θ ω := by
    intro ω
    rw [Finset.sum_mul_sum]
    simp only [Finset.sum_mul]
    congr 1; ext i
    congr 1; ext j
    ring
  simp only [expand]
  clear expand
  -- Exchange ∫ and outer ∑
  rw [integral_finsetSum]
  · congr 1; ext i
    -- Exchange ∫ and inner ∑
    rw [integral_finsetSum]
    · congr 1; ext j
      -- Factor out constants vᵢ and wⱼ
      -- Need to massage the expression to match integral_mul_left pattern
      have factorize :
          (fun a => v.ofLp i * w.ofLp j * M.score θ i a * M.score θ j a * M.density θ a) =
          (fun a => (v.ofLp i * w.ofLp j) * (M.score θ i a * M.score θ j a * M.density θ a)) := by
        ext a; ring
      simp only [factorize]
      exact MeasureTheory.integral_const_mul (v.ofLp i * w.ofLp j) _
    · -- Integrability for inner sum
      intro j _
      -- Show: Integrable (fun a => v i * w j * M.score θ i a * M.score θ j a * M.density θ a)
      have factorize : (fun a => v i * w j * M.score θ i a * M.score θ j a * M.density θ a) =
          (fun a => (v i * w j) * (M.score θ i a * M.score θ j a * M.density θ a)) := by
        ext a; ring
      rw [factorize]
      exact Integrable.const_mul (M.fisherEntry_integrable hθ hSq i j) _
  · -- Integrability for outer sum
    intro i _
    -- Use integrable_finset_sum (not Integrable.finset_sum)
    refine integrable_finsetSum _ (fun j _ => ?_)
    have factorize : (fun a => v i * w j * M.score θ i a * M.score θ j a * M.density θ a) =
        (fun a => (v i * w j) * (M.score θ i a * M.score θ j a * M.density θ a)) := by
      ext a; ring
    rw [factorize]
    exact Integrable.const_mul (M.fisherEntry_integrable hθ hSq i j) _

/-! ### Positive definiteness -/

/-- If `g_θ(v, v) = 0` then the integrand `⟨v,s⟩² · p` vanishes
`μ`-a.e.  This is the core analytical step: a nonneg integrable
function with vanishing integral must vanish a.e. -/
lemma fisherBilin_integrand_eq_zero_ae
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (v : ParamSpace n)
    (hInt : Integrable
      (fun ω => M.directionalScore θ v ω *
        M.directionalScore θ v ω *
        M.density θ ω) M.refMeasure)
    (hzero : M.fisherBilin θ v v = 0) :
    ∀ᵐ ω ∂M.refMeasure,
      M.directionalScore θ v ω *
        M.directionalScore θ v ω *
        M.density θ ω = 0 := by
  -- A nonneg integrable function with zero integral vanishes a.e.
  apply (integral_eq_zero_iff_of_nonneg_ae
    (ae_of_all _ (M.fisherBilin_integrand_nonneg hθ v))
    hInt).mp
  exact hzero

/-- Under `g_θ(v, v) = 0`, the directional score vanishes `μ`-a.e.:
`⟨v, s(θ, ω)⟩ = 0` for `μ`-a.e. `ω`.

**Proof.** Since `⟨v,s⟩² · p = 0` a.e. and `p > 0` a.e., we get
`⟨v,s⟩² = 0` a.e., whence `⟨v,s⟩ = 0` a.e. -/
lemma directionalScore_eq_zero_ae
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (v : ParamSpace n)
    (hInt : Integrable
      (fun ω => M.directionalScore θ v ω *
        M.directionalScore θ v ω *
        M.density θ ω) M.refMeasure)
    (hzero : M.fisherBilin θ v v = 0) :
    ∀ᵐ ω ∂M.refMeasure,
      M.directionalScore θ v ω = 0 := by
  have hae :=
    M.fisherBilin_integrand_eq_zero_ae hθ v hInt hzero
  filter_upwards [hae,
    M.toStatisticalModel.density_pos_ae θ hθ]
    with ω hprod hpos
  -- hprod : ⟨v,s⟩ * ⟨v,s⟩ * p(ω) = 0
  -- hpos  : 0 < p(ω)
  have hp_ne : M.density θ ω ≠ 0 := ne_of_gt hpos
  have hsq : M.directionalScore θ v ω *
      M.directionalScore θ v ω = 0 := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact h
    · exact absurd h hp_ne
  exact mul_self_eq_zero.mp hsq

/-! ### Score-injectivity and positive definiteness -/

/-- **Score-injectivity** at `θ`: the only tangent vector `v` with
`⟨v, s(θ, ω)⟩ = 0` `μ`-a.e. is `v = 0`.

Equivalently, the score components `s₁, …, sₙ` are linearly
independent in `L²(P_θ)`.  Implied by (but weaker than) local
identifiability of the parametrisation. -/
def ScoreInjective (θ : ParamSpace n) : Prop :=
  ∀ v : ParamSpace n,
    (∀ᵐ ω ∂M.refMeasure,
      M.directionalScore θ v ω = 0) → v = 0

/-- **Positive definiteness of the Fisher information.**

Under score-injectivity at `θ`, `g_θ(v, v) = 0` forces `v = 0`.
Together with `fisherBilin_self_nonneg`, this makes `g_θ` a
positive-definite inner product on `T_θ Θ ≅ ℝⁿ`. -/
lemma fisherBilin_pos_def {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain)
    (hInj : M.ScoreInjective θ)
    (hInt : ∀ w : ParamSpace n, Integrable
      (fun ω => M.directionalScore θ w ω *
        M.directionalScore θ w ω *
        M.density θ ω) M.refMeasure)
    {v : ParamSpace n}
    (hzero : M.fisherBilin θ v v = 0) :
    v = 0 :=
  hInj v
    (M.directionalScore_eq_zero_ae hθ v (hInt v) hzero)

/-- For `v ≠ 0`, score-injectivity and integrability give
strict positivity: `g_θ(v, v) > 0`.

This is the form most convenient for constructing an inner product
space instance. -/
lemma fisherBilin_pos_of_ne_zero {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain)
    (hInj : M.ScoreInjective θ)
    (hInt : ∀ w : ParamSpace n, Integrable
      (fun ω => M.directionalScore θ w ω *
        M.directionalScore θ w ω *
        M.density θ ω) M.refMeasure)
    {v : ParamSpace n} (hv : v ≠ 0) :
    0 < M.fisherBilin θ v v := by
  rcases (M.fisherBilin_self_nonneg hθ v).lt_or_eq with h | h
  · exact h
  · -- h : 0 = g(v,v), so g(v,v) = 0, contradicting v ≠ 0
    exfalso; exact hv
      (M.fisherBilin_pos_def hθ hInj hInt h.symm)

/-! ### Covariance characterisation -/

/-- `g_{ij}` equals the covariance of `sᵢ, sⱼ` under `P_θ`.
Since `E_θ[sᵢ] = 0` (`score_expectation_eq_zero`), the mean
product vanishes and `Cov = E[sᵢ sⱼ] = g_{ij}`. -/
lemma fisherMatrix_eq_cov {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain) (i j : Fin n) :
    M.fisherMatrix θ i j =
      M.fisherMatrix θ i j -
        (∫ ω, M.score θ i ω * M.density θ ω
          ∂M.refMeasure) *
        (∫ ω, M.score θ j ω * M.density θ ω
          ∂M.refMeasure) := by
  rw [M.score_expectation_eq_zero hθ i,
      M.score_expectation_eq_zero hθ j]
  ring

/-! ### Alternative formula via partial derivatives -/

/-- The Fisher matrix in terms of density derivatives:
  `g_{ij}(θ) = ∫ (∂ᵢp)(∂ⱼp) / p  dμ`.

This avoids forming the score (dividing by `p`) twice and can
be more convenient for computation. -/
lemma fisherMatrix_eq_integral_partialDensity
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (i j : Fin n) :
    M.fisherMatrix θ i j =
      ∫ ω, M.partialDensity θ i ω *
        M.partialDensity θ j ω /
        M.density θ ω ∂M.refMeasure := by
  simp only [fisherMatrix]
  apply integral_congr_ae
  filter_upwards
    [M.toStatisticalModel.density_pos_ae θ hθ]
    with ω hω
  simp only [score, partialDensity]
  field_simp

/-! ### Diagonal = variance -/

/-- The diagonal entry `g_{ii}` is the variance of `sᵢ` (= its
second moment, since the mean vanishes):
  `g_{ii}(θ) = E_θ[sᵢ²] = Var_θ(sᵢ)`. -/
lemma fisherMatrix_diag_eq_score_sq {θ : ParamSpace n}
    (i : Fin n) :
    M.fisherMatrix θ i i =
      ∫ ω, M.score θ i ω ^ 2 * M.density θ ω
        ∂M.refMeasure := by
  simp only [fisherMatrix, sq];

end RegularStatisticalModel

end Spectra.InformationGeometry
