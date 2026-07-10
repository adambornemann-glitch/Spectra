/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SpectralTheory.Calculus.PMapBounded
import Spectra.SpectralTheory.Calculus.MixedProduct
import Spectra.SpectralTheory.Calculus.SquareSpectralMap
import Spectra.SpectralTheory.Weak
import Spectra.Modular.Cocycle.ModularSqrtSquare
/-!
# The square bridge: pointwise composition `A∘A = T` gives the spectral square `A² = T`

The generic bridge from *pointwise composition* data to the *spectral functional-calculus square*,
letting `posSqrt_unique` be consumed.  For a self-adjoint `A` and a self-adjoint `T` such that on
every `x ∈ D(T)` the composition `A(A x)` is defined and equals `T x`, we prove

> `pmapOfPVM (genToGroup hA) (·²) = T`   (`pmapOfPVM_sq_genToGroup_eq`)

i.e. the functional-calculus square `A²` **is** `T` — not merely an extension.  The inclusion
`T ≤ A²` comes from a closed-graph limit; the reverse from maximality of self-adjoint operators
(`IsSelfAdjoint.eq_of_le`), since `A²` is itself self-adjoint (`sq_isSelfAdjoint`).

Main statements (all for an arbitrary one-parameter unitary group `U_grp`, `A := generator U_grp`):

* `mem_pmapDomain_id_of_mem_generator` — `x ∈ D(A)` lies in the natural `L²` domain of the identity
  symbol (from `weak_second_moment`).
* `spectralCalculus_apply_pmapOfPVM_of_mul_bounded` — **left-bounded absorption**: for bounded `g`
  with `g·f` bounded and `ξ ∈ D(∫f dP)`, one has `Φ(g)((∫f dP)ξ) = Φ(g·f)ξ`.
* `mem_sq_domain_of_generator_comp` / `pmapOfPVM_sq_apply_generator_comp` — **the bridge**: if
  `x ∈ D(A)` and `Ax ∈ D(A)` then `x ∈ D(A²)` and `A²x = A(Ax)`, by a closed-graph limit along the
  spectral cut-offs `E([-m,m])x`.
* `pmapOfPVM_sq_genToGroup_eq` — **the packaging**: pointwise composition data `A(Ax) = Tx` on
  `D(T)` for self-adjoint `A, T` forces `pmapOfPVM (genToGroup hA) (·²) = T`.
-/

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal
open Spectra.YosidaHille

namespace Spectra.QuantumMechanics.SpectralTheory

open Spectra Spectra.Borel Spectra.OneParameterUnitaryGroup SpectralMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-! ## The generator domain sits in the natural domain of the identity symbol -/

/-- **Generator vectors lie in the natural domain of the identity symbol**: for
`x ∈ D(generator U_grp)`, `∫ ‖(s:ℂ)‖² dμ_x = ∫ s² dμ_x < ∞` by `weak_second_moment`. -/
theorem mem_pmapDomain_id_of_mem_generator (x : (generator U_grp).domain) :
    (x : H) ∈ ProjValMeasure.pmapDomain U_grp.toPVM (fun s => (s : ℂ)) := by
  rw [ProjValMeasure.mem_pmapDomain]
  refine ((weak_second_moment U_grp x).1).congr (Eventually.of_forall fun s => ?_)
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ## Left-bounded absorption -/

/-- **Left-bounded absorption.**  For measurable `f` (possibly unbounded), bounded measurable `g`
with `g·f` bounded, and `ξ ∈ D(∫f dP)`, applying the bounded `Φ(g)` *after* the unbounded
`∫f dP` collapses to the bounded `Φ(g·f)`:  `Φ(g)((∫f dP)ξ) = Φ(g·f)ξ`.

Both sides are the strong limit of `Φ(g)(Φ(truncₙ f)ξ) = Φ(g·truncₙ f)ξ`: the left by continuity
of `Φ(g)` along `pmapOfPVM_apply_tendsto`, the right by dominated convergence
(`‖g·truncₙ f‖ ≤ ‖g·f‖` pointwise), so uniqueness of limits closes the equality. -/
theorem spectralCalculus_apply_pmapOfPVM_of_mul_bounded
    (f g : ℝ → ℂ) (hf : Measurable f) (hg_meas : Measurable g)
    (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (hgf_meas : Measurable fun s => g s * f s)
    (hgf_bdd : ∃ C, ∀ s, ‖g s * f s‖ ≤ C) (ξ : H)
    (hξ : ξ ∈ ProjValMeasure.pmapDomain U_grp.toPVM f) :
    spectralCalculus U_grp g hg_meas hg_bdd (pmapOfPVM U_grp f hf ⟨ξ, hξ⟩)
      = spectralCalculus U_grp (fun s => g s * f s) hgf_meas hgf_bdd ξ := by
  have hint : Integrable (fun s => ‖f s‖ ^ 2) (borelMeasure U_grp ξ) :=
    (ProjValMeasure.mem_pmapDomain U_grp.toPVM).mp hξ
  -- limit 1: Φ(g)(Φ(truncₙ f)ξ) → Φ(g)((∫f dP)ξ), by continuity of Φ(g)
  have hlim1 : Tendsto (fun n => spectralCalculus U_grp g hg_meas hg_bdd
      (pmapTrunc U_grp f hf n ξ)) atTop
      (𝓝 (spectralCalculus U_grp g hg_meas hg_bdd (pmapOfPVM U_grp f hf ⟨ξ, hξ⟩))) :=
    ((spectralCalculus U_grp g hg_meas hg_bdd).continuous.tendsto _).comp
      (pmapOfPVM_apply_tendsto U_grp f hf hint)
  -- term-by-term: Φ(g)(Φ(truncₙ f)ξ) = Φ(g·truncₙ f)ξ
  have hstep : ∀ n, spectralCalculus U_grp g hg_meas hg_bdd (pmapTrunc U_grp f hf n ξ)
      = spectralCalculus U_grp (fun s => g s * truncSym f n s)
          (hg_meas.mul (measurable_truncSym hf n)) (bounded_mul hg_bdd (truncSym_bdd f n)) ξ := by
    intro n
    rw [pmapTrunc_apply, ← ContinuousLinearMap.mul_apply,
      spectralCalculus_mul U_grp (truncSym f n) g (measurable_truncSym hf n) (truncSym_bdd f n)
        hg_meas hg_bdd (hg_meas.mul (measurable_truncSym hf n))
        (bounded_mul hg_bdd (truncSym_bdd f n))]
  -- limit 2: Φ(g·truncₙ f)ξ → Φ(g·f)ξ (dominated convergence; `g·f` bounded)
  have hint2 : Integrable (fun s => ‖g s * f s‖ ^ 2) (borelMeasure U_grp ξ) :=
    integrable_sq_of_bounded U_grp _ hgf_meas hgf_bdd ξ
  have hlim2 : Tendsto (fun n => spectralCalculus U_grp (fun s => g s * truncSym f n s)
      (hg_meas.mul (measurable_truncSym hf n)) (bounded_mul hg_bdd (truncSym_bdd f n)) ξ) atTop
      (𝓝 (spectralCalculus U_grp (fun s => g s * f s) hgf_meas hgf_bdd ξ)) := by
    have h := tendsto_spectralCalculus_pmapOfPVM_of_dominated U_grp (fun s => g s * f s)
      hgf_meas (ξ := ξ) hint2 (fun n s => g s * truncSym f n s)
      (fun n => hg_meas.mul (measurable_truncSym hf n))
      (fun n => bounded_mul hg_bdd (truncSym_bdd f n))
      (fun n s => by
        rw [norm_mul, norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_truncSym_le f n s) (norm_nonneg (g s)))
      (fun s => (tendsto_truncSym f s).const_mul (g s))
    rwa [pmapOfPVM_apply_eq_spectralCalculus_of_bounded U_grp (fun s => g s * f s) hgf_meas
      hgf_bdd ξ ((ProjValMeasure.mem_pmapDomain U_grp.toPVM).mpr hint2)] at h
  exact tendsto_nhds_unique (hlim1.congr hstep) hlim2

/-! ## Cut-off symbols for the closed-graph limit -/

/-- The identity cut-off symbol `s · 1_{[-m,m]}(s)`. -/
private noncomputable def idCut (m : ℕ) : ℝ → ℂ :=
  fun s => (s : ℂ) * Set.indicator (Set.Icc (-(m : ℝ)) (m : ℝ)) (fun _ => (1 : ℂ)) s

private lemma idCut_meas (m : ℕ) : Measurable (idCut m) :=
  Complex.measurable_ofReal.mul (measurable_const.indicator measurableSet_Icc)

private lemma idCut_bdd (m : ℕ) : ∃ C, ∀ s, ‖idCut m s‖ ≤ C := by
  refine ⟨(m : ℝ), fun s => ?_⟩
  rw [idCut, norm_mul]
  by_cases hs : s ∈ Set.Icc (-(m : ℝ)) (m : ℝ)
  · rw [Set.indicator_of_mem hs, NormOneClass.norm_one, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    exact (abs_le_max_of_mem_Icc hs).trans (by simp)
  · rw [Set.indicator_of_notMem hs, norm_zero, mul_zero]; positivity

/-- `‖idCut m s‖ ≤ ‖(s:ℂ)‖` pointwise. -/
private lemma idCut_dom (m : ℕ) (s : ℝ) : ‖idCut m s‖ ≤ ‖(s : ℂ)‖ := by
  rw [idCut, norm_mul]
  by_cases hs : s ∈ Set.Icc (-(m : ℝ)) (m : ℝ)
  · rw [Set.indicator_of_mem hs, NormOneClass.norm_one, mul_one]
  · rw [Set.indicator_of_notMem hs, norm_zero, mul_zero]; positivity

/-- `idCut m s → (s:ℂ)` pointwise. -/
private lemma idCut_lim (s : ℝ) : Tendsto (fun m => idCut m s) atTop (𝓝 ((s : ℂ))) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_ge_atTop ⌈|s|⌉₊] with m hm
  have hmem : s ∈ Set.Icc (-(m : ℝ)) (m : ℝ) := by
    have hle : |s| ≤ (m : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hm)
    rw [Set.mem_Icc]
    exact ⟨by have := neg_abs_le s; linarith, by have := le_abs_self s; linarith⟩
  simp only [idCut, Set.indicator_of_mem hmem, mul_one]

/-- The square cut-off symbol `s² · 1_{[-m,m]}(s)`. -/
private noncomputable def sqCut (m : ℕ) : ℝ → ℂ :=
  fun s => (s : ℂ) ^ 2 * Set.indicator (Set.Icc (-(m : ℝ)) (m : ℝ)) (fun _ => (1 : ℂ)) s

private lemma sqCut_meas (m : ℕ) : Measurable (sqCut m) :=
  measurable_sq_ofReal.mul (measurable_const.indicator measurableSet_Icc)

private lemma sqCut_bdd (m : ℕ) : ∃ C, ∀ s, ‖sqCut m s‖ ≤ C := by
  refine ⟨(m : ℝ) ^ 2, fun s => ?_⟩
  rw [sqCut, norm_mul]
  by_cases hs : s ∈ Set.Icc (-(m : ℝ)) (m : ℝ)
  · rw [Set.indicator_of_mem hs, NormOneClass.norm_one, mul_one, norm_pow, Complex.norm_real,
      Real.norm_eq_abs]
    have hle : |s| ≤ (m : ℝ) := (abs_le_max_of_mem_Icc hs).trans (by simp)
    nlinarith [abs_nonneg s]
  · rw [Set.indicator_of_notMem hs, norm_zero, mul_zero]; positivity

/-- `s² · 1_{[-m,m]} = sqCut m` in the product form produced by the mixed product law. -/
private lemma sq_mul_indicator_eq_sqCut (m : ℕ) :
    (fun s : ℝ => (s : ℂ) ^ 2 * Set.indicator (Set.Icc (-(m : ℝ)) (m : ℝ)) (fun _ => (1 : ℂ)) s)
      = sqCut m := rfl

/-- `idCut m · id = sqCut m` as symbols. -/
private lemma idCut_mul_id_eq_sqCut (m : ℕ) :
    (fun s => idCut m s * (s : ℂ)) = sqCut m := by
  funext s
  rw [idCut, sqCut]
  ring

/-! ## The closed-graph limit -/

/-- The cut-off value: `A²(E([-m,m])x) = Φ(s²·1_{[-m,m]})x`, from the mixed product law. -/
private theorem sqCalc_proj_apply (ξ : H) (m : ℕ) :
    pmapOfPVM U_grp (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal
        ⟨spectralProjection U_grp (Set.Icc (-(m : ℝ)) (m : ℝ)) measurableSet_Icc ξ,
          sq_proj_Icc_mem U_grp ξ m⟩
      = spectralCalculus U_grp (sqCut m) (sqCut_meas m) (sqCut_bdd m) ξ := by
  have hfg_meas : Measurable fun s : ℝ => (s : ℂ) ^ 2 *
      Set.indicator (Set.Icc (-(m : ℝ)) (m : ℝ)) (fun _ => (1 : ℂ)) s := by
    rw [sq_mul_indicator_eq_sqCut m]; exact sqCut_meas m
  have hfg_bdd : ∃ C, ∀ s : ℝ, ‖(s : ℂ) ^ 2 *
      Set.indicator (Set.Icc (-(m : ℝ)) (m : ℝ)) (fun _ => (1 : ℂ)) s‖ ≤ C := by
    have h := sqCut_bdd m
    rw [← sq_mul_indicator_eq_sqCut m] at h
    exact h
  have hmix := pmapOfPVM_spectralCalculus_of_mul_bounded U_grp (fun s => (s : ℂ) ^ 2)
    (Set.indicator (Set.Icc (-(m : ℝ)) (m : ℝ)) (fun _ => (1 : ℂ)))
    measurable_sq_ofReal (measurable_const.indicator measurableSet_Icc) (indicator_one_bdd _)
    hfg_meas hfg_bdd ξ (sq_proj_Icc_mem U_grp ξ m)
  have hcongr := congrArg (fun T : H →L[ℂ] H => T ξ)
    (spectralCalculus_congr U_grp (sq_mul_indicator_eq_sqCut m) hfg_meas hfg_bdd
      (sqCut_meas m) (sqCut_bdd m))
  exact hmix.trans hcongr

/-- The key identity: `Φ(s²·1_{[-m,m]})x = Φ(s·1_{[-m,m]})(Ax)` for `x ∈ D(A)` — the bounded
factor `s·1_{[-m,m]}` absorbs into the identity symbol on the generator's domain. -/
private theorem sqCut_apply_eq_idCut_generator (x : (generator U_grp).domain) (m : ℕ) :
    spectralCalculus U_grp (sqCut m) (sqCut_meas m) (sqCut_bdd m) (x : H)
      = spectralCalculus U_grp (idCut m) (idCut_meas m) (idCut_bdd m) (generator U_grp x) := by
  have hξ0 := mem_pmapDomain_id_of_mem_generator U_grp x
  have hgf_meas : Measurable fun s => idCut m s * (s : ℂ) := by
    have h := sqCut_meas m
    rw [← idCut_mul_id_eq_sqCut m] at h
    exact h
  have hgf_bdd : ∃ C, ∀ s, ‖idCut m s * (s : ℂ)‖ ≤ C := by
    have h := sqCut_bdd m
    rw [← idCut_mul_id_eq_sqCut m] at h
    exact h
  have happly := spectralCalculus_apply_pmapOfPVM_of_mul_bounded U_grp (fun s => (s : ℂ))
    (idCut m) Complex.measurable_ofReal (idCut_meas m) (idCut_bdd m) hgf_meas hgf_bdd
    (x : H) hξ0
  rw [pmapOfPVM_id_eq_generator U_grp x hξ0] at happly
  rw [happly]
  exact (congrArg (fun T : H →L[ℂ] H => T (x : H))
    (spectralCalculus_congr U_grp (idCut_mul_id_eq_sqCut m) hgf_meas hgf_bdd
      (sqCut_meas m) (sqCut_bdd m))).symm

/-- Convergence of the cut-off values: `Φ(s²·1_{[-m,m]})x → A(Ax)` when `x, Ax ∈ D(A)` —
via the key identity and dominated convergence in the identity symbol at `Ax`. -/
private theorem tendsto_sqCut_generator_comp (x : (generator U_grp).domain)
    (hAx : generator U_grp x ∈ (generator U_grp).domain) :
    Tendsto (fun m => spectralCalculus U_grp (sqCut m) (sqCut_meas m) (sqCut_bdd m) (x : H))
      atTop (𝓝 (generator U_grp ⟨generator U_grp x, hAx⟩)) := by
  have hmemA : generator U_grp x ∈ ProjValMeasure.pmapDomain U_grp.toPVM (fun s => (s : ℂ)) :=
    mem_pmapDomain_id_of_mem_generator U_grp ⟨generator U_grp x, hAx⟩
  have hintA : Integrable (fun s : ℝ => ‖(s : ℂ)‖ ^ 2)
      (borelMeasure U_grp (generator U_grp x)) :=
    (ProjValMeasure.mem_pmapDomain U_grp.toPVM).mp hmemA
  have hdct := tendsto_spectralCalculus_pmapOfPVM_of_dominated U_grp (fun s => (s : ℂ))
    Complex.measurable_ofReal (ξ := generator U_grp x) hintA idCut idCut_meas idCut_bdd
    idCut_dom idCut_lim
  have hgen : pmapOfPVM U_grp (fun s => (s : ℂ)) Complex.measurable_ofReal
      ⟨generator U_grp x, (ProjValMeasure.mem_pmapDomain U_grp.toPVM).mpr hintA⟩
      = generator U_grp ⟨generator U_grp x, hAx⟩ :=
    pmapOfPVM_id_eq_generator U_grp ⟨generator U_grp x, hAx⟩
      ((ProjValMeasure.mem_pmapDomain U_grp.toPVM).mpr hintA)
  rw [hgen] at hdct
  exact hdct.congr fun m => (sqCut_apply_eq_idCut_generator U_grp x m).symm

/-- The graph pair `(x, A(Ax))` lies in the (closed) graph of `A² := pmapOfPVM U_grp (·²)`:
the pairs `(E([-m,m])x, A²(E([-m,m])x))` are in the graph and converge to it. -/
private theorem sq_graph_pair_mem (x : (generator U_grp).domain)
    (hAx : generator U_grp x ∈ (generator U_grp).domain) :
    ((x : H), generator U_grp ⟨generator U_grp x, hAx⟩)
      ∈ (pmapOfPVM U_grp (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal).graph := by
  have hclosed : IsClosed
      ((pmapOfPVM U_grp (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal).graph : Set (H × H)) :=
    (sq_isSelfAdjoint U_grp).isClosed
  have hmemgraph : ∀ m : ℕ,
      (spectralProjection U_grp (Set.Icc (-(m : ℝ)) (m : ℝ)) measurableSet_Icc (x : H),
        spectralCalculus U_grp (sqCut m) (sqCut_meas m) (sqCut_bdd m) (x : H))
      ∈ (pmapOfPVM U_grp (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal).graph := by
    intro m
    rw [LinearPMap.mem_graph_iff]
    exact ⟨⟨_, sq_proj_Icc_mem U_grp (x : H) m⟩, rfl, sqCalc_proj_apply U_grp (x : H) m⟩
  have hconv : Tendsto (fun m : ℕ =>
      (spectralProjection U_grp (Set.Icc (-(m : ℝ)) (m : ℝ)) measurableSet_Icc (x : H),
        spectralCalculus U_grp (sqCut m) (sqCut_meas m) (sqCut_bdd m) (x : H))) atTop
      (𝓝 ((x : H), generator U_grp ⟨generator U_grp x, hAx⟩)) := by
    rw [nhds_prod_eq]
    exact (tendsto_spectralProjection_Icc_univ U_grp (x : H)).prodMk
      (tendsto_sqCut_generator_comp U_grp x hAx)
  exact hclosed.mem_of_tendsto hconv (Eventually.of_forall hmemgraph)

/-! ## The bridge -/

/-- **The bridge, membership half**: if `x ∈ D(A)` and `Ax ∈ D(A)` then `x` lies in the natural
domain of the functional-calculus square `A² := pmapOfPVM U_grp (·²)`. -/
theorem mem_sq_domain_of_generator_comp (x : (generator U_grp).domain)
    (hAx : generator U_grp x ∈ (generator U_grp).domain) :
    (x : H) ∈ (pmapOfPVM U_grp (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal).domain := by
  have hg := sq_graph_pair_mem U_grp x hAx
  rw [LinearPMap.mem_graph_iff] at hg
  obtain ⟨z, hz1, hz2⟩ := hg
  simp only at hz1 hz2
  rw [← hz1]
  exact z.2

/-- **The bridge, value half**: on the composable part of `D(A)` the functional-calculus square
computes the composition, `A²x = A(Ax)`. -/
theorem pmapOfPVM_sq_apply_generator_comp (x : (generator U_grp).domain)
    (hAx : generator U_grp x ∈ (generator U_grp).domain) :
    pmapOfPVM U_grp (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal
        ⟨(x : H), mem_sq_domain_of_generator_comp U_grp x hAx⟩
      = generator U_grp ⟨generator U_grp x, hAx⟩ := by
  have hg := sq_graph_pair_mem U_grp x hAx
  rw [LinearPMap.mem_graph_iff] at hg
  obtain ⟨z, hz1, hz2⟩ := hg
  simp only at hz1 hz2
  rw [← hz2]
  congr 1
  exact Subtype.ext hz1.symm

/-! ## The `eq_of_le` packaging: the consumption interface for `posSqrt_unique` -/

/-- **Pointwise composition square ⟹ spectral square.**  For self-adjoint `A, T` such that every
`x ∈ D(T)` satisfies `x ∈ D(A)`, `Ax ∈ D(A)` and `A(Ax) = Tx`, the functional-calculus square of
`A` **equals** `T`:

`pmapOfPVM (genToGroup hA) (·²) = T`.

The composition data plus the bridge give `T ≤ A²` as partial operators; both are self-adjoint
(`sq_isSelfAdjoint`), and self-adjoint operators are maximal (`IsSelfAdjoint.eq_of_le`), so the
inclusion is an equality.  This is the input shape `posSqrt_unique` consumes. -/
theorem pmapOfPVM_sq_genToGroup_eq {A T : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hT : IsSelfAdjoint T)
    (h : ∀ x : T.domain, ∃ (hx1 : (x : H) ∈ A.domain) (hx2 : A ⟨(x : H), hx1⟩ ∈ A.domain),
      A ⟨A ⟨(x : H), hx1⟩, hx2⟩ = T x) :
    pmapOfPVM (genToGroup hA) (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal = T := by
  have hgen : generator (genToGroup hA) = A := generator_genToGroup hA
  -- transport the composition data to the generator of the constructed group
  have hdata : ∀ x : T.domain, ∃ (hx1 : (x : H) ∈ (generator (genToGroup hA)).domain)
      (hx2 : generator (genToGroup hA) ⟨(x : H), hx1⟩ ∈ (generator (genToGroup hA)).domain),
      generator (genToGroup hA) ⟨generator (genToGroup hA) ⟨(x : H), hx1⟩, hx2⟩ = T x := by
    intro x
    obtain ⟨hx1, hx2, hval⟩ := h x
    have hx1' : (x : H) ∈ (generator (genToGroup hA)).domain := by rw [hgen]; exact hx1
    have hv1 : generator (genToGroup hA) ⟨(x : H), hx1'⟩ = A ⟨(x : H), hx1⟩ :=
      (le_of_eq hgen).2 rfl
    have hx2' : generator (genToGroup hA) ⟨(x : H), hx1'⟩
        ∈ (generator (genToGroup hA)).domain := by
      rw [hv1, hgen]; exact hx2
    have hv2 : generator (genToGroup hA) ⟨generator (genToGroup hA) ⟨(x : H), hx1'⟩, hx2'⟩
        = A ⟨A ⟨(x : H), hx1⟩, hx2⟩ := (le_of_eq hgen).2 hv1
    exact ⟨hx1', hx2', hv2.trans hval⟩
  -- T ≤ A² as partial operators, via the bridge
  have hle : T ≤ pmapOfPVM (genToGroup hA) (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal := by
    refine ⟨?_, ?_⟩
    · intro ξ hξ
      obtain ⟨hx1', hx2', -⟩ := hdata ⟨ξ, hξ⟩
      exact mem_sq_domain_of_generator_comp (genToGroup hA) ⟨ξ, hx1'⟩ hx2'
    · intro x y hxy
      obtain ⟨hx1', hx2', hval⟩ := hdata x
      have happly := pmapOfPVM_sq_apply_generator_comp (genToGroup hA) ⟨(x : H), hx1'⟩ hx2'
      rw [← hval, ← happly]
      congr 1
      exact Subtype.ext hxy
  exact (IsSelfAdjoint.eq_of_le hT (sq_isSelfAdjoint (genToGroup hA)) hle).symm

end Spectra.QuantumMechanics.SpectralTheory
