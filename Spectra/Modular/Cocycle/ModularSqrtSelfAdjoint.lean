/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.Cocycle.ModularInvolution
import Spectra.SpectralTheory.Calculus.MixedProduct
/-!
# The modular square root `Δ^{½}` is self-adjoint (HC1)

For a cyclic–separating vector `Ω` of a von Neumann algebra `M`, the modular square root
`Δ^{½} = modularSqrt` (the unbounded `√` calculus of `Δ = modularOp M Ω ≥ 0`) is **self-adjoint**.

The route is von Neumann's deficiency criterion (`isSelfAdjoint_of_surjective_addSub`): a densely
defined symmetric operator whose `A + i` and `A − i` are both surjective is self-adjoint.

* **Symmetry** is `pmapOfPVM_isFormalAdjoint_self` (the `√` symbol is real).
* **Density** of `D(Δ^{½})` follows from `D(Δ) ⊆ D(Δ^{½})` and `D(Δ)` dense.
* **Surjectivity** of `Δ^{½} ± i` uses the *bounded* resolvent `R_± := Φ(1/(√·±i))`: the symbol
  `1/(√s±i)` is bounded (`‖√s±i‖ ≥ 1`), so `R_± h` is a genuine bounded-calculus vector, and the
  **mixed bounded/unbounded product law** below shows `R_± h ∈ D(Δ^{½})` and
  `Δ^{½}(R_± h) = Φ(√/(√±i)) h`, whence `(Δ^{½} ± i)(R_± h) = Φ((√±i)/(√±i)) h = Φ(1) h = h`.

## Key new infrastructure (namespace `Spectra.QuantumMechanics.SpectralTheory`)

* `borelMeasure_spectralCalculus_eq_withDensity` — `μ_{Φ(g)ξ} = μ_ξ.withDensity ‖g‖²`.
* `mem_pmapDomain_spectralCalculus` — `Φ(g)ξ ∈ D(∫f dP)` when `f·g` is bounded.
* `pmapOfPVM_spectralCalculus_of_mul_bounded` — **the mixed product law**:
  `(∫f dP)(Φ(g)ξ) = Φ(f·g)ξ` when `g`, `f·g` are bounded.
-/

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal


/-! ## The modular square root is self-adjoint -/

open Spectra.QuantumMechanics.SpectralTheory
open Spectra.YosidaHille
open Spectra.OneParameterUnitaryGroup
open Spectra.Borel

namespace Spectra.TomitaTakesaki

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

/-! ### Boundedness / measurability of the resolvent symbols `1/(√s ± i)`, `√s/(√s ± i)` -/

/-- `‖√s + i‖ ≥ 1` (the imaginary part is `1`). -/
lemma one_le_norm_sqrtC_add_I (s : ℝ) : (1 : ℝ) ≤ ‖(Real.sqrt s : ℂ) + I‖ := by
  have him : ((Real.sqrt s : ℂ) + I).im = 1 := by simp
  calc (1 : ℝ) = |((Real.sqrt s : ℂ) + I).im| := by rw [him]; norm_num
    _ ≤ ‖(Real.sqrt s : ℂ) + I‖ := Complex.abs_im_le_norm _

/-- `‖√s − i‖ ≥ 1` (the imaginary part is `−1`). -/
lemma one_le_norm_sqrtC_sub_I (s : ℝ) : (1 : ℝ) ≤ ‖(Real.sqrt s : ℂ) - I‖ := by
  have him : ((Real.sqrt s : ℂ) - I).im = -1 := by simp
  calc (1 : ℝ) = |((Real.sqrt s : ℂ) - I).im| := by rw [him]; norm_num
    _ ≤ ‖(Real.sqrt s : ℂ) - I‖ := Complex.abs_im_le_norm _

lemma sqrtC_add_I_ne_zero (s : ℝ) : (Real.sqrt s : ℂ) + I ≠ 0 := by
  intro h; have := one_le_norm_sqrtC_add_I s; rw [h, norm_zero] at this; linarith

lemma sqrtC_sub_I_ne_zero (s : ℝ) : (Real.sqrt s : ℂ) - I ≠ 0 := by
  intro h; have := one_le_norm_sqrtC_sub_I s; rw [h, norm_zero] at this; linarith

/-- `‖√s‖ ≤ ‖√s + i‖`, via `‖·‖² = normSq` and `normSq(√s+i) = (√s)² + 1`. -/
lemma norm_sqrtC_le_norm_sqrtC_add_I (s : ℝ) :
    ‖(Real.sqrt s : ℂ)‖ ≤ ‖(Real.sqrt s : ℂ) + I‖ := by
  have h1 : ‖(Real.sqrt s : ℂ)‖ ^ 2 ≤ ‖(Real.sqrt s : ℂ) + I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith [Real.sqrt_nonneg s]
  nlinarith [norm_nonneg ((Real.sqrt s : ℂ)), norm_nonneg ((Real.sqrt s : ℂ) + I), h1]

lemma norm_sqrtC_le_norm_sqrtC_sub_I (s : ℝ) :
    ‖(Real.sqrt s : ℂ)‖ ≤ ‖(Real.sqrt s : ℂ) - I‖ := by
  have h1 : ‖(Real.sqrt s : ℂ)‖ ^ 2 ≤ ‖(Real.sqrt s : ℂ) - I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith [Real.sqrt_nonneg s]
  nlinarith [norm_nonneg ((Real.sqrt s : ℂ)), norm_nonneg ((Real.sqrt s : ℂ) - I), h1]

lemma resPlus_bdd : ∃ C, ∀ s, ‖(1 : ℂ) / ((Real.sqrt s : ℂ) + I)‖ ≤ C := by
  refine ⟨1, fun s => ?_⟩
  rw [norm_div, NormOneClass.norm_one, div_le_one (by have := one_le_norm_sqrtC_add_I s; linarith)]
  exact one_le_norm_sqrtC_add_I s

lemma resMinus_bdd : ∃ C, ∀ s, ‖(1 : ℂ) / ((Real.sqrt s : ℂ) - I)‖ ≤ C := by
  refine ⟨1, fun s => ?_⟩
  rw [norm_div, NormOneClass.norm_one, div_le_one (by have := one_le_norm_sqrtC_sub_I s; linarith)]
  exact one_le_norm_sqrtC_sub_I s

lemma sqrtMulResPlus_bdd :
    ∃ C, ∀ s, ‖(Real.sqrt s : ℂ) * ((1 : ℂ) / ((Real.sqrt s : ℂ) + I))‖ ≤ C := by
  refine ⟨1, fun s => ?_⟩
  rw [mul_one_div, norm_div, div_le_one (by have := one_le_norm_sqrtC_add_I s; linarith)]
  exact norm_sqrtC_le_norm_sqrtC_add_I s

lemma sqrtMulResMinus_bdd :
    ∃ C, ∀ s, ‖(Real.sqrt s : ℂ) * ((1 : ℂ) / ((Real.sqrt s : ℂ) - I))‖ ≤ C := by
  refine ⟨1, fun s => ?_⟩
  rw [mul_one_div, norm_div, div_le_one (by have := one_le_norm_sqrtC_sub_I s; linarith)]
  exact norm_sqrtC_le_norm_sqrtC_sub_I s

lemma IResPlus_bdd : ∃ C, ∀ s, ‖I * ((1 : ℂ) / ((Real.sqrt s : ℂ) + I))‖ ≤ C := by
  obtain ⟨C, hC⟩ := resPlus_bdd
  exact ⟨‖I‖ * C, fun s => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC s) (norm_nonneg _)⟩

lemma IResMinus_bdd : ∃ C, ∀ s, ‖I * ((1 : ℂ) / ((Real.sqrt s : ℂ) - I))‖ ≤ C := by
  obtain ⟨C, hC⟩ := resMinus_bdd
  exact ⟨‖I‖ * C, fun s => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC s) (norm_nonneg _)⟩

lemma measurable_resPlus : Measurable (fun s : ℝ => (1 : ℂ) / ((Real.sqrt s : ℂ) + I)) :=
  measurable_const.div (measurable_sqrtC.add measurable_const)

lemma measurable_resMinus : Measurable (fun s : ℝ => (1 : ℂ) / ((Real.sqrt s : ℂ) - I)) :=
  measurable_const.div (measurable_sqrtC.sub measurable_const)

lemma measurable_sqrtMulResPlus :
    Measurable (fun s : ℝ => (Real.sqrt s : ℂ) * ((1 : ℂ) / ((Real.sqrt s : ℂ) + I))) :=
  measurable_sqrtC.mul measurable_resPlus

lemma measurable_sqrtMulResMinus :
    Measurable (fun s : ℝ => (Real.sqrt s : ℂ) * ((1 : ℂ) / ((Real.sqrt s : ℂ) - I))) :=
  measurable_sqrtC.mul measurable_resMinus

/-! ### Surjectivity of `Δ^{½} ± i` -/

/-- **Surjectivity of `Δ^{½} + i`.**  For every `h`, the bounded resolvent vector
`R h = Φ(1/(√+i)) h` lies in `D(Δ^{½})` (mixed-law domain membership) and
`(Δ^{½} + i)(R h) = Φ(√/(√+i)) h + Φ(i/(√+i)) h = Φ((√+i)/(√+i)) h = Φ(1) h = h`. -/
theorem modularSqrt_add_I_surjective (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    ∀ h : H, ∃ ψ : (modularSqrt hcyc hsep).domain,
      modularSqrt hcyc hsep ψ + I • (ψ : H) = h := by
  set U := genToGroup (modularOp_isSelfAdjoint hcyc hsep) with _hU
  intro h
  have hmem : spectralCalculus U (fun s => (1 : ℂ) / ((Real.sqrt s : ℂ) + I))
        measurable_resPlus resPlus_bdd h
      ∈ ProjValMeasure.pmapDomain U.toPVM (fun s => (Real.sqrt s : ℂ)) :=
    mem_pmapDomain_spectralCalculus U (fun s => (Real.sqrt s : ℂ))
      (fun s => (1 : ℂ) / ((Real.sqrt s : ℂ) + I)) measurable_sqrtC measurable_resPlus resPlus_bdd
      sqrtMulResPlus_bdd h
  refine ⟨⟨_, hmem⟩, ?_⟩
  have hsqrt : modularSqrt hcyc hsep ⟨_, hmem⟩
      = spectralCalculus U (fun s => (Real.sqrt s : ℂ) * ((1 : ℂ) / ((Real.sqrt s : ℂ) + I)))
          measurable_sqrtMulResPlus sqrtMulResPlus_bdd h :=
    pmapOfPVM_spectralCalculus_of_mul_bounded U (fun s => (Real.sqrt s : ℂ))
      (fun s => (1 : ℂ) / ((Real.sqrt s : ℂ) + I)) measurable_sqrtC measurable_resPlus resPlus_bdd
      measurable_sqrtMulResPlus sqrtMulResPlus_bdd h hmem
  rw [hsqrt]
  have hIR : I • spectralCalculus U (fun s => (1 : ℂ) / ((Real.sqrt s : ℂ) + I))
        measurable_resPlus resPlus_bdd h
      = spectralCalculus U (fun s => I * ((1 : ℂ) / ((Real.sqrt s : ℂ) + I)))
          (measurable_const.mul measurable_resPlus) IResPlus_bdd h := by
    rw [spectralCalculus_smul U I (fun s => (1 : ℂ) / ((Real.sqrt s : ℂ) + I)) measurable_resPlus
      resPlus_bdd (measurable_const.mul measurable_resPlus) IResPlus_bdd]
    rfl
  change _ + I • spectralCalculus U (fun s => (1 : ℂ) / ((Real.sqrt s : ℂ) + I))
    measurable_resPlus resPlus_bdd h = h
  rw [hIR, ← ContinuousLinearMap.add_apply,
    ← spectralCalculus_add U (fun s => (Real.sqrt s : ℂ) * ((1 : ℂ) / ((Real.sqrt s : ℂ) + I)))
      (fun s => I * ((1 : ℂ) / ((Real.sqrt s : ℂ) + I)))
      measurable_sqrtMulResPlus sqrtMulResPlus_bdd
      (measurable_const.mul measurable_resPlus) IResPlus_bdd
      (measurable_sqrtMulResPlus.add (measurable_const.mul measurable_resPlus))
      (by obtain ⟨C1, h1⟩ := sqrtMulResPlus_bdd; obtain ⟨C2, h2⟩ := IResPlus_bdd
          exact ⟨C1 + C2, fun s => (norm_add_le _ _).trans (add_le_add (h1 s) (h2 s))⟩)]
  have hcongr : (fun s => (Real.sqrt s : ℂ) * ((1 : ℂ) / ((Real.sqrt s : ℂ) + I))
      + I * ((1 : ℂ) / ((Real.sqrt s : ℂ) + I))) = (fun _ : ℝ => (1 : ℂ)) := by
    funext s
    have hne : (Real.sqrt s : ℂ) + I ≠ 0 := sqrtC_add_I_ne_zero s
    field_simp
  rw [spectralCalculus_congr U hcongr _ _ measurable_const ⟨1, fun _ => norm_one.le⟩,
    spectralCalculus_one, ContinuousLinearMap.id_apply]

/-- **Surjectivity of `Δ^{½} − i`.**  Mirror of the `+i` case with the symbol `1/(√−i)` and the
identity `√/(√−i) − i/(√−i) = (√−i)/(√−i) = 1`. -/
theorem modularSqrt_sub_I_surjective (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    ∀ h : H, ∃ ψ : (modularSqrt hcyc hsep).domain,
      modularSqrt hcyc hsep ψ - I • (ψ : H) = h := by
  set U := genToGroup (modularOp_isSelfAdjoint hcyc hsep) with _hU
  intro h
  have hmem : spectralCalculus U (fun s => (1 : ℂ) / ((Real.sqrt s : ℂ) - I))
        measurable_resMinus resMinus_bdd h
      ∈ ProjValMeasure.pmapDomain U.toPVM (fun s => (Real.sqrt s : ℂ)) :=
    mem_pmapDomain_spectralCalculus U (fun s => (Real.sqrt s : ℂ))
      (fun s => (1 : ℂ) / ((Real.sqrt s : ℂ) - I)) measurable_sqrtC measurable_resMinus resMinus_bdd
      sqrtMulResMinus_bdd h
  refine ⟨⟨_, hmem⟩, ?_⟩
  have hsqrt : modularSqrt hcyc hsep ⟨_, hmem⟩
      = spectralCalculus U (fun s => (Real.sqrt s : ℂ) * ((1 : ℂ) / ((Real.sqrt s : ℂ) - I)))
          measurable_sqrtMulResMinus sqrtMulResMinus_bdd h :=
    pmapOfPVM_spectralCalculus_of_mul_bounded U (fun s => (Real.sqrt s : ℂ))
      (fun s => (1 : ℂ) / ((Real.sqrt s : ℂ) - I)) measurable_sqrtC measurable_resMinus resMinus_bdd
      measurable_sqrtMulResMinus sqrtMulResMinus_bdd h hmem
  rw [hsqrt]
  have hIR : I • spectralCalculus U (fun s => (1 : ℂ) / ((Real.sqrt s : ℂ) - I))
        measurable_resMinus resMinus_bdd h
      = spectralCalculus U (fun s => I * ((1 : ℂ) / ((Real.sqrt s : ℂ) - I)))
          (measurable_const.mul measurable_resMinus) IResMinus_bdd h := by
    rw [spectralCalculus_smul U I (fun s => (1 : ℂ) / ((Real.sqrt s : ℂ) - I)) measurable_resMinus
      resMinus_bdd (measurable_const.mul measurable_resMinus) IResMinus_bdd]
    rfl
  change _ - I • spectralCalculus U (fun s => (1 : ℂ) / ((Real.sqrt s : ℂ) - I))
    measurable_resMinus resMinus_bdd h = h
  rw [hIR, ← ContinuousLinearMap.sub_apply,
    ← spectralCalculus_sub U (fun s => (Real.sqrt s : ℂ) * ((1 : ℂ) / ((Real.sqrt s : ℂ) - I)))
      (fun s => I * ((1 : ℂ) / ((Real.sqrt s : ℂ) - I)))
      measurable_sqrtMulResMinus sqrtMulResMinus_bdd
      (measurable_const.mul measurable_resMinus) IResMinus_bdd
      (measurable_sqrtMulResMinus.sub (measurable_const.mul measurable_resMinus))
      (by obtain ⟨C1, h1⟩ := sqrtMulResMinus_bdd; obtain ⟨C2, h2⟩ := IResMinus_bdd
          exact ⟨C1 + C2, fun s => (norm_sub_le _ _).trans (add_le_add (h1 s) (h2 s))⟩)]
  have hcongr : (fun s => (Real.sqrt s : ℂ) * ((1 : ℂ) / ((Real.sqrt s : ℂ) - I))
      - I * ((1 : ℂ) / ((Real.sqrt s : ℂ) - I))) = (fun _ : ℝ => (1 : ℂ)) := by
    funext s
    have hne : (Real.sqrt s : ℂ) - I ≠ 0 := sqrtC_sub_I_ne_zero s
    field_simp
  rw [spectralCalculus_congr U hcongr _ _ measurable_const ⟨1, fun _ => norm_one.le⟩,
    spectralCalculus_one, ContinuousLinearMap.id_apply]

/-! ### Density of `D(Δ^{½})` -/

/-- `D(Δ^{½})` is dense: `D(Δ) ⊆ D(Δ^{½})` (`modularOp_domain_le_modularSqrt_domain`) and `D(Δ)` is
dense (from `modularOp_isSelfAdjoint`'s proof, re-derived via the `1+Δ` surjective argument). -/
theorem modularSqrt_domain_dense (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    Dense ((modularSqrt hcyc hsep).domain : Set H) := by
  have hle : (modularOp M Ω).domain ≤ (modularSqrt hcyc hsep).domain :=
    modularOp_domain_le_modularSqrt_domain hcyc hsep
  have hΔdense : Dense ((modularOp M Ω).domain : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
      Submodule.eq_bot_iff]
    intro h hh
    obtain ⟨g, hg⟩ := one_add_modularOp_surjective hcyc hsep h
    have hortho : ⟪(g : H), h⟫_ℂ = 0 := (Submodule.mem_orthogonal _ h).1 hh (g : H) g.2
    rw [← hg, inner_add_right] at hortho
    have h1 : 0 ≤ RCLike.re ⟪(g : H), modularOp M Ω g⟫_ℂ := by
      rw [inner_re_symm]; exact modularOp_nonneg hcyc g
    have hre : RCLike.re ⟪(g : H), modularOp M Ω g⟫_ℂ + ‖(g : H)‖ ^ 2 = 0 := by
      have hr := congrArg RCLike.re hortho
      rwa [map_add, map_zero, inner_self_eq_norm_sq] at hr
    have hgz : (g : H) = 0 := by
      have h2 : ‖(g : H)‖ ^ 2 = 0 := by linarith [sq_nonneg ‖(g : H)‖]
      exact norm_eq_zero.mp ((pow_eq_zero_iff (n := 2) (by norm_num)).mp h2)
    have hg0 : g = 0 := Subtype.ext hgz
    rw [← hg, hg0]; simp
  exact hΔdense.mono (fun x hx => hle hx)

/-! ### The main theorem -/

/-- **The modular square root `Δ^{½}` is self-adjoint** (HC1).  Von Neumann's deficiency criterion
`isSelfAdjoint_of_surjective_addSub`: `Δ^{½}` is densely defined, symmetric (real symbol `√`), and
both `Δ^{½} + i` and `Δ^{½} − i` are surjective (bounded resolvent + mixed product law). -/
theorem modularSqrt_isSelfAdjoint (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    IsSelfAdjoint (modularSqrt hcyc hsep) := by
  have hsym : (modularSqrt hcyc hsep).IsFormalAdjoint (modularSqrt hcyc hsep) :=
    pmapOfPVM_isFormalAdjoint_self _ (fun s => (Real.sqrt s : ℂ)) measurable_sqrtC
      (fun s => by rw [Complex.conj_ofReal])
  exact isSelfAdjoint_of_surjective_addSub (modularSqrt hcyc hsep) hsym
    (modularSqrt_domain_dense hcyc hsep)
    (modularSqrt_add_I_surjective hcyc hsep) (modularSqrt_sub_I_surjective hcyc hsep)

end Spectra.TomitaTakesaki
