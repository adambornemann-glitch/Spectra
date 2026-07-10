/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Quantum.State
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# The continuous functional calculus acts diagonally on eigenvectors

If `T : H →L[ℂ] H` is a self-adjoint operator and `v` is an eigenvector, `T v = μ • v` with
`μ ∈ spectrum ℝ T`, then for any function `f : ℝ → ℝ` continuous on the spectrum,
`cfc f T v = f μ • v`.  In words: the continuous functional calculus `f ↦ cfc f T` sends an
eigenvector of `T` (eigenvalue `μ`) to an eigenvector of `cfc f T` (eigenvalue `f μ`).

The proof is the standard polynomial-plus-density argument:

* **Polynomials.** For a real polynomial `q`, `aeval T q v = q.eval μ • v` (proved by induction
  on `q` using `T v = μ • v`).
* **Density.** The two maps `g ↦ cfcHom hT g v` and `g ↦ g ⟨μ, hμ⟩ • v` on `C(spectrum ℝ T, ℝ)`
  are continuous and agree on the (Stone–Weierstrass dense) subalgebra of polynomial functions,
  hence agree everywhere; specialising to (the restriction of) `f` gives the result.

## Main results

* `cfc_apply_eigenvector` — `cfc f T v = (f μ : ℂ) • v` (the vector form).
* `inner_cfc_eigenvector` — `⟪v, cfc f T v⟫ = (f μ : ℂ) * ⟪v, v⟫` (the inner-product form).
-/

open Spectra.QuantumMechanics.Channels
open scoped InnerProductSpace

namespace Spectra.InformationGeometry.Quantum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The polynomial functional calculus acts by the scalar `q.eval μ` on an eigenvector:
if `T v = μ • v` then `aeval T q v = q.eval μ • v`.  (Here `q : ℝ[X]` and `T` is regarded as an
element of the `ℝ`-algebra `H →L[ℂ] H`.) -/
private lemma aeval_apply_eigenvector {T : H →L[ℂ] H} {μ : ℝ} {v : H}
    (hv : T v = (μ : ℝ) • v) (q : Polynomial ℝ) :
    (Polynomial.aeval T q) v = (q.eval μ : ℝ) • v := by
  induction q using Polynomial.induction_on with
  | C r => simp [Algebra.algebraMap_eq_smul_one]
  | add p₁ p₂ hp₁ hp₂ => simp [map_add, hp₁, hp₂, add_smul]
  | monomial n r ih =>
    rw [pow_succ, ← mul_assoc, map_mul, ContinuousLinearMap.mul_apply, Polynomial.aeval_X, hv,
      LinearMapClass.map_smul_of_tower, ih, smul_smul]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    ring_nf

/-- The continuous functional calculus applied to an eigenvector acts by the scalar `f μ`:
if `T v = μ • v` and `f` is continuous on `spectrum ℝ T`, then `cfc f T v = f μ • v`. -/
theorem cfc_apply_eigenvector {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) {μ : ℝ} {v : H}
    (hv : T v = (μ : ℂ) • v) (hμ : μ ∈ spectrum ℝ T) {f : ℝ → ℝ}
    (hf : ContinuousOn f (spectrum ℝ T)) :
    cfc f T v = (f μ : ℂ) • v := by
  set s := spectrum ℝ T with _hs
  -- The eigenvector equation with a *real* scalar smul.
  have hvℝ : T v = (μ : ℝ) • v := by rw [hv]; exact (RCLike.real_smul_eq_coe_smul (K := ℂ) μ v).symm
  -- `Φ g = (cfcHom hT g) v` is continuous.
  have hΦcont : Continuous fun g : C(s, ℝ) => (cfcHom hT g) v :=
    (ContinuousLinearMap.apply ℂ H v).continuous.comp (cfcHom_continuous hT)
  -- `Ψ g = (g ⟨μ, hμ⟩ : ℝ) • v` is continuous.
  have hΨcont : Continuous fun g : C(s, ℝ) => (g ⟨μ, hμ⟩ : ℝ) • v :=
    (continuous_eval_const _).smul continuous_const
  -- The polynomial functions are dense in `C(s, ℝ)`.
  have hdense : Dense ((polynomialFunctions s : Set C(s, ℝ))) := by
    rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe,
      polynomialFunctions.topologicalClosure s, Algebra.coe_top]
  -- Agreement on the dense subalgebra of polynomial functions.
  have hEqOn : Set.EqOn (fun g : C(s, ℝ) => (cfcHom hT g) v)
      (fun g : C(s, ℝ) => (g ⟨μ, hμ⟩ : ℝ) • v) (polynomialFunctions s) := by
    rintro g ⟨q, -, rfl⟩
    have hcfc : cfcHom hT (Polynomial.toContinuousMapOnAlgHom s q) = Polynomial.aeval T q := by
      have h1 : cfc q.eval T = Polynomial.aeval T q := cfc_polynomial q T hT
      have h2 : cfc q.eval T
          = cfcHom hT ⟨_, ((Polynomial.continuous q).continuousOn).restrict⟩ :=
        cfc_apply q.eval T hT (Polynomial.continuous q).continuousOn
      rw [h2] at h1
      rw [← h1]
      congr 1
    change (cfcHom hT (Polynomial.toContinuousMapOnAlgHom s q)) v
      = (Polynomial.toContinuousMapOnAlgHom s q) ⟨μ, hμ⟩ • v
    rw [hcfc, aeval_apply_eigenvector hvℝ q]
    simp [Polynomial.toContinuousMapOnAlgHom_apply, Polynomial.toContinuousMapOn_apply,
      Polynomial.toContinuousMap_apply]
  -- Two continuous maps agreeing on a dense set are equal.
  have hEq := hΦcont.ext_on hdense hΨcont hEqOn
  -- Specialise to the restriction of `f`.
  have hcfcf : cfc f T = cfcHom hT ⟨_, hf.restrict⟩ := cfc_apply f T hT hf
  have hval := congrFun hEq (⟨_, hf.restrict⟩ : C(s, ℝ))
  simp only [ContinuousMap.coe_mk, Set.restrict_apply] at hval
  rw [hcfcf, hval]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) (f μ) v

/-- Inner-product form of the diagonal action of the continuous functional calculus on an
eigenvector: `⟪v, cfc f T v⟫ = f μ * ⟪v, v⟫`. -/
theorem inner_cfc_eigenvector {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) {μ : ℝ} {v : H}
    (hv : T v = (μ : ℂ) • v) (hμ : μ ∈ spectrum ℝ T) {f : ℝ → ℝ}
    (hf : ContinuousOn f (spectrum ℝ T)) :
    ⟪v, cfc f T v⟫_ℂ = (f μ : ℂ) * ⟪v, v⟫_ℂ := by
  rw [cfc_apply_eigenvector hT hv hμ hf, inner_smul_right]

end Spectra.InformationGeometry.Quantum
