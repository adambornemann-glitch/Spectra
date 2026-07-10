/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.Cocycle.ModularSqrtSquare
import Spectra.Modular.Cocycle.PolarIsometry
import Spectra.Operator.Closable
/-!
# Route B Stage 3 — `D(Δ)` is a core for `Δ^{½}`, and the extended polar `S = W ∘ Δ^{½}`

**Part 1 (kill-spike KS1).**  The modular domain `D(Δ)` is a **core** for the modular square root
`Δ^{½}` (Mathlib's `LinearPMap.HasCore`): every graph point `(y, Δ^{½}y)` is the limit of graph
points over `D(Δ)`.  The witnesses are the standard spectral cut-offs — for `y ∈ D(Δ^{½})`,

  `E([0,n]) y ∈ D(Δ)`,  `E([0,n]) y → y`,  `Δ^{½}(E([0,n]) y) = Φ(√·1_{[0,n]}) y → Δ^{½} y`,

where the vector convergence uses that the modular spectral measures are carried by `[0,∞)`
(`E([0,n])y = E([-n,n])y` a.e.), the operator identity is the mixed bounded/unbounded product law,
and the image convergence is dominated convergence of bounded approximants (`sqrtCut n → √`
pointwise everywhere, thanks to the junk value `√s = 0` for `s < 0`).

**Part 2 (the Stage-3 extension).**  The polar relation `W(Δ^{½}x) = Sx` (proved on `D(Δ)` in
`PolarIsometry.lean`) extends to the **full** square-root domain, and the polar domains coincide,
`D(S) = D(Δ^{½})` — so `S = W ∘ Δ^{½}` is a genuine operator identity.  Both directions are
sequence-free image-closure arguments: the core property pushed through the continuous
`(u,v) ↦ (u, Wv)` into the closed `Γ(S)`, and the graph-L² core fact
`Γ(S) = cl Γ(S|_{D(Δ)})` pushed through `(u,v) ↦ (u, W⁻¹v)` into the closed `Γ(Δ^{½})`.

This pins `W` on `cl(ran Δ^{½})`; per the Stage-3/Stage-4 precision note it is the *ingredient*,
not the `J²=1` closer.

## Main statements

* `modularSqrt_hasCore_modularOp_domain` — `(modularSqrt hcyc hsep).HasCore (modularOp M Ω).domain`.
* `modularSqrt_domain_le_tomitaClosure_domain`, `tomitaClosure_domain_le_modularSqrt_domain`,
  `tomitaClosure_domain_eq_modularSqrt_domain` — **`D(S) = D(Δ^{½})`**.
* `tomitaClosure_eq_modularW_modularSqrt` — **`S y = W (Δ^{½} y)` on all of `D(Δ^{½})`**.
* `norm_modularSqrt_eq_norm_tomitaClosure` — the extended isometry `‖Δ^{½}y‖ = ‖Sy‖`.
* `tomita_eq_modularConjugation_modularSqrt_full` — the extension in `J`-form,
  `toConj (J (Δ^{½} y)) = S y`.
-/

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace
open Spectra.QuantumMechanics.SpectralTheory
open Spectra.YosidaHille
open Spectra.OneParameterUnitaryGroup
open Spectra.Borel
open Spectra.Conj

namespace Spectra.TomitaTakesaki

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}
variable (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)

/-- Local abbreviation for the modular unitary group `U = genToGroup Δ`. -/
private noncomputable abbrev modU : OneParameterUnitaryGroup (H := H) :=
  genToGroup (modularOp_isSelfAdjoint hcyc hsep)

/-! ### The square-root cut-off symbols `√s · 1_{[0,n]}(s)` -/

/-- The square-root cut-off symbol `√s · 1_{[0,n]}(s)`. -/
private noncomputable def sqrtCut (n : ℕ) : ℝ → ℂ :=
  fun s => (Real.sqrt s : ℂ) * Set.indicator (Set.Icc 0 (n : ℝ)) (fun _ => (1 : ℂ)) s

private lemma sqrtCut_meas (n : ℕ) : Measurable (sqrtCut n) :=
  measurable_sqrtC.mul (measurable_const.indicator measurableSet_Icc)

private lemma sqrtCut_bdd (n : ℕ) : ∃ C, ∀ s, ‖sqrtCut n s‖ ≤ C := by
  refine ⟨Real.sqrt (n : ℝ), fun s => ?_⟩
  rw [sqrtCut, norm_mul]
  by_cases hs : s ∈ Set.Icc 0 (n : ℝ)
  · rw [Set.indicator_of_mem hs, NormOneClass.norm_one, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg s)]
    exact Real.sqrt_le_sqrt hs.2
  · rw [Set.indicator_of_notMem hs, norm_zero, mul_zero]
    positivity

/-- `‖sqrtCut n s‖ ≤ ‖(√s : ℂ)‖` pointwise. -/
private lemma sqrtCut_dom (n : ℕ) (s : ℝ) : ‖sqrtCut n s‖ ≤ ‖(Real.sqrt s : ℂ)‖ := by
  rw [sqrtCut, norm_mul]
  by_cases hs : s ∈ Set.Icc 0 (n : ℝ)
  · rw [Set.indicator_of_mem hs, NormOneClass.norm_one, mul_one]
  · rw [Set.indicator_of_notMem hs, norm_zero, mul_zero]
    positivity

/-- `sqrtCut n s → (√s : ℂ)` pointwise (for `s < 0` both sides are the junk value `0`). -/
private lemma sqrtCut_lim (s : ℝ) :
    Tendsto (fun n => sqrtCut n s) atTop (𝓝 ((Real.sqrt s : ℂ))) := by
  by_cases hs : 0 ≤ s
  · refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop ⌈s⌉₊] with n hn
    have hmem : s ∈ Set.Icc 0 (n : ℝ) := ⟨hs, (Nat.le_ceil s).trans (by exact_mod_cast hn)⟩
    rw [sqrtCut, Set.indicator_of_mem hmem, mul_one]
  · have hzero : ((Real.sqrt s : ℂ)) = 0 := by
      rw [Real.sqrt_eq_zero_of_nonpos (not_le.mp hs).le, Complex.ofReal_zero]
    rw [hzero]
    refine tendsto_const_nhds.congr fun n => ?_
    rw [sqrtCut, hzero, zero_mul]

/-! ### The three cut-off facts -/

/-- **Operator identity on cut-offs**: `Δ^{½}(E([0,n]) y) = Φ(√·1_{[0,n]}) y` — the mixed
bounded/unbounded product law applied to `f = √`, `g = 1_{[0,n]}`. -/
private theorem modularSqrt_cutoff_apply' (y : H) (n : ℕ) :
    modularSqrt hcyc hsep
        ⟨spectralProjection (modU hcyc hsep) (Set.Icc 0 (n : ℝ)) measurableSet_Icc y,
          modularOp_domain_le_modularSqrt_domain hcyc hsep
            (modular_cutoff_mem_domain hcyc hsep y n)⟩
      = spectralCalculus (modU hcyc hsep) (sqrtCut n) (sqrtCut_meas n) (sqrtCut_bdd n) y :=
  pmapOfPVM_spectralCalculus_of_mul_bounded (modU hcyc hsep)
    (fun s => (Real.sqrt s : ℂ)) (Set.indicator (Set.Icc 0 (n : ℝ)) fun _ => (1 : ℂ))
    measurable_sqrtC (measurable_const.indicator measurableSet_Icc) (indicator_one_bdd _)
    (sqrtCut_meas n) (sqrtCut_bdd n) y
    (mem_pmapDomain_spectralCalculus (modU hcyc hsep) (fun s => (Real.sqrt s : ℂ))
      (Set.indicator (Set.Icc 0 (n : ℝ)) fun _ => (1 : ℂ)) measurable_sqrtC
      (measurable_const.indicator measurableSet_Icc) (indicator_one_bdd _) (sqrtCut_bdd n) y)

/-- **Vector convergence**: `E([0,n]) y → y` for every `y` (the modular spectral measure is
carried by `[0,∞)`, so `E([0,n])y = E([-n,n])y`, and the two-sided cut-offs exhaust). -/
private theorem tendsto_cutoff_vector (y : H) :
    Tendsto (fun n : ℕ =>
        spectralProjection (modU hcyc hsep) (Set.Icc 0 (n : ℝ)) measurableSet_Icc y)
      atTop (𝓝 y) := by
  have heq : ∀ n : ℕ,
      spectralProjection (modU hcyc hsep) (Set.Icc (-(n : ℝ)) (n : ℝ)) measurableSet_Icc y
        = spectralProjection (modU hcyc hsep) (Set.Icc 0 (n : ℝ)) measurableSet_Icc y := by
    intro n
    simp only [spectralProjection]
    refine spectralCalculus_congr_ae (modU hcyc hsep) _ _ _ _ _ _ y ?_
    have hμ : borelMeasure (modU hcyc hsep) y (Set.Iio (0 : ℝ)) = 0 :=
      borelMeasure_modular_Iio_zero hcyc hsep y
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun s hs => ?_) hμ
    simp only [Set.mem_setOf_eq] at hs
    rw [Set.mem_Iio, ← not_le]
    intro hs0
    refine hs ?_
    by_cases hsn : s ≤ (n : ℝ)
    · rw [Set.indicator_of_mem (Set.mem_Icc.mpr ⟨by linarith, hsn⟩),
        Set.indicator_of_mem (Set.mem_Icc.mpr ⟨hs0, hsn⟩)]
    · rw [Set.indicator_of_notMem (fun h => hsn (Set.mem_Icc.mp h).2),
        Set.indicator_of_notMem (fun h => hsn (Set.mem_Icc.mp h).2)]
  exact (tendsto_spectralProjection_Icc_univ (modU hcyc hsep) y).congr heq

/-- **Image convergence**: `Φ(√·1_{[0,n]}) y → Δ^{½} y` for `y ∈ D(Δ^{½})` (dominated convergence
of the bounded approximants to the unbounded calculus). -/
private theorem tendsto_cutoff_image (y : (modularSqrt hcyc hsep).domain) :
    Tendsto (fun n : ℕ =>
        spectralCalculus (modU hcyc hsep) (sqrtCut n) (sqrtCut_meas n) (sqrtCut_bdd n) (y : H))
      atTop (𝓝 (modularSqrt hcyc hsep y)) :=
  tendsto_spectralCalculus_pmapOfPVM_of_dominated (modU hcyc hsep)
    (fun s => (Real.sqrt s : ℂ)) measurable_sqrtC (ξ := (y : H))
    ((ProjValMeasure.mem_pmapDomain _).mp y.2)
    sqrtCut sqrtCut_meas sqrtCut_bdd sqrtCut_dom sqrtCut_lim

/-! ### The core theorem -/

/-- **`D(Δ)` is a core for `Δ^{½}`** (Mathlib `LinearPMap.HasCore`): the closure of
`Δ^{½}|_{D(Δ)}` is `Δ^{½}`.  Via the graph-density bridge (`Δ^{½}` is closed since self-adjoint),
this says the restricted graph is dense in the full graph — witnessed by the cut-off pairs
`(E([0,n])y, Φ(√·1_{[0,n]})y) → (y, Δ^{½}y)`.

This is the Stage-3 ingredient of the Field-3 build: it lets the polar relation `W(Δ^{½}x) = Sx`
extend from `D(Δ)` to all of `D(Δ^{½})` and pins `W` on `cl(ran Δ^{½})`. -/
theorem modularSqrt_hasCore_modularOp_domain :
    (modularSqrt hcyc hsep).HasCore (modularOp M Ω).domain := by
  have hclosed : (modularSqrt hcyc hsep).IsClosed :=
    (modularSqrt_isSelfAdjoint hcyc hsep).isClosed
  rw [Spectra.Operator.hasCore_iff_topologicalClosure_graph hclosed
    (modularOp_domain_le_modularSqrt_domain hcyc hsep)]
  refine le_antisymm
    (Submodule.topologicalClosure_minimal _
      (LinearPMap.le_graph_of_le LinearPMap.domRestrict_le) hclosed) ?_
  -- the full graph lies in the closure of the restricted graph, via the cut-off pairs
  intro p hp
  rw [LinearPMap.mem_graph_iff] at hp
  obtain ⟨y, hy1, hy2⟩ := hp
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  have hpeq : p = ((y : H), modularSqrt hcyc hsep y) := by
    rw [Prod.ext_iff]
    exact ⟨hy1.symm, hy2.symm⟩
  rw [hpeq]
  -- the cut-off pairs lie in the restricted graph …
  have hg : ∀ n : ℕ,
      (spectralProjection (modU hcyc hsep) (Set.Icc 0 (n : ℝ)) measurableSet_Icc (y : H),
        spectralCalculus (modU hcyc hsep) (sqrtCut n) (sqrtCut_meas n) (sqrtCut_bdd n) (y : H))
      ∈ (((modularSqrt hcyc hsep).domRestrict (modularOp M Ω).domain).graph : Set (H × H)) := by
    intro n
    rw [SetLike.mem_coe, LinearPMap.mem_graph_iff]
    refine ⟨⟨spectralProjection (modU hcyc hsep) (Set.Icc 0 (n : ℝ)) measurableSet_Icc (y : H),
      Submodule.mem_inf.mpr ⟨modular_cutoff_mem_domain hcyc hsep (y : H) n,
        modularOp_domain_le_modularSqrt_domain hcyc hsep
          (modular_cutoff_mem_domain hcyc hsep (y : H) n)⟩⟩, rfl, ?_⟩
    rw [LinearPMap.domRestrict_apply
      (y := ⟨spectralProjection (modU hcyc hsep) (Set.Icc 0 (n : ℝ)) measurableSet_Icc (y : H),
        modularOp_domain_le_modularSqrt_domain hcyc hsep
          (modular_cutoff_mem_domain hcyc hsep (y : H) n)⟩) rfl]
    exact modularSqrt_cutoff_apply' hcyc hsep (y : H) n
  -- … and converge to the graph point `(y, Δ^{½}y)`
  have hconv : Tendsto (fun n : ℕ =>
      (spectralProjection (modU hcyc hsep) (Set.Icc 0 (n : ℝ)) measurableSet_Icc (y : H),
        spectralCalculus (modU hcyc hsep) (sqrtCut n) (sqrtCut_meas n) (sqrtCut_bdd n) (y : H)))
      atTop (𝓝 ((y : H), modularSqrt hcyc hsep y)) := by
    rw [nhds_prod_eq]
    exact (tendsto_cutoff_vector hcyc hsep (y : H)).prodMk (tendsto_cutoff_image hcyc hsep y)
  exact mem_closure_of_tendsto hconv (Eventually.of_forall hg)

/-- **Approximation form of the core property**: every graph point `(y, Δ^{½}y)` of the modular
square root is a limit of graph points over `D(Δ)` — the statement Stage 3 consumes directly. -/
theorem modularSqrt_mem_closure_graph_domRestrict (y : (modularSqrt hcyc hsep).domain) :
    ((y : H), modularSqrt hcyc hsep y)
      ∈ closure (((modularSqrt hcyc hsep).domRestrict (modularOp M Ω).domain).graph
          : Set (H × H)) :=
  Spectra.Operator.mem_closure_graph_of_hasCore
    ((modularSqrt_isSelfAdjoint hcyc hsep).isClosed)
    (modularSqrt_hasCore_modularOp_domain hcyc hsep) y

/-! ### Stage 3 — the extended polar decomposition `S = W ∘ Δ^{½}` on `D(Δ^{½}) = D(S)`

With the core property in hand, the polar relation `W(Δ^{½}x) = Sx` (proved on `D(Δ)` in
`PolarIsometry.lean`) extends to the full square-root domain, and the two polar domains coincide.
Both directions are sequence-free image-closure arguments:

* **`D(Δ^{½}) ⊆ D(S)` with `S y = W(Δ^{½}y)`** — push the core property (the graph closure of
  `Δ^{½}|_{D(Δ)}`) through the continuous `(u,v) ↦ (u, Wv)` into the *closed* graph `Γ(S)`.
* **`D(S) ⊆ D(Δ^{½})` with `Δ^{½}y = W⁻¹(S y)`** — push the graph-L² core fact
  `Γ(S) = cl Γ(S|_{D(Δ)})` (`graphL2_eq_topologicalClosure_modularGraphL2`) through the continuous
  `(u,v) ↦ (u, W⁻¹v)` into the *closed* graph `Γ(Δ^{½})`.

This pins `W` on `cl(ran Δ^{½})`.  Per the Stage-4 precision note it is the *ingredient*, not the
`J² = 1` closer: `S̃y ∈ D(Δ^{½})` is still strictly weaker than `S̃y ∈ ran Δ^{½}`. -/

/-- The graph membership behind the forward extension: for `y ∈ D(Δ^{½})`, the pair
`(y, W(Δ^{½}y))` lies in the (closed) graph of `S`. -/
private theorem mem_tomitaClosure_graph_of_modularSqrt (y : (modularSqrt hcyc hsep).domain) :
    ((y : H), modularW hcyc hsep (modularSqrt hcyc hsep y)) ∈ (tomitaClosure M Ω).graph := by
  have hφcont : Continuous fun p : H × H => (p.1, modularW hcyc hsep p.2) :=
    continuous_fst.prodMk ((modularW hcyc hsep).continuous.comp continuous_snd)
  -- `(u,v) ↦ (u, Wv)` maps the restricted graph into `Γ(S)`
  have hsub : (fun p : H × H => (p.1, modularW hcyc hsep p.2)) ''
      ((((modularSqrt hcyc hsep).domRestrict (modularOp M Ω).domain).graph :
          Submodule ℂ (H × H)) : Set (H × H))
      ⊆ ((tomitaClosure M Ω).graph : Set (H × Conj H)) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [SetLike.mem_coe, LinearPMap.mem_graph_iff] at hp
    obtain ⟨z, hz1, hz2⟩ := hp
    have hzΔ : (z : H) ∈ (modularOp M Ω).domain := (Submodule.mem_inf.mp z.2).1
    have hzS : (z : H) ∈ (modularSqrt hcyc hsep).domain := (Submodule.mem_inf.mp z.2).2
    rw [SetLike.mem_coe, LinearPMap.mem_graph_iff]
    refine ⟨⟨(z : H), modularOp_domain_le_tomita hzΔ⟩, hz1, ?_⟩
    change tomitaClosure M Ω ⟨(z : H), modularOp_domain_le_tomita hzΔ⟩
      = modularW hcyc hsep p.2
    have h1 : ((modularSqrt hcyc hsep).domRestrict (modularOp M Ω).domain) z
        = modularSqrt hcyc hsep ⟨(z : H), hzS⟩ := LinearPMap.domRestrict_apply rfl
    have h2 := modularW_apply_modularSqrt hcyc hsep ⟨(z : H), hzΔ⟩
    rw [modularSqrtOnModularDomain_apply, tomitaOnModularDomain_apply] at h2
    rw [← hz2, h1]
    exact h2.symm
  have hmem := (closure_mono hsub) (image_closure_subset_closure_image hφcont
    (Set.mem_image_of_mem _ (modularSqrt_mem_closure_graph_domRestrict hcyc hsep y)))
  rwa [(show IsClosed ((tomitaClosure M Ω).graph : Set (H × Conj H)) from
    tomitaClosure_isClosed hcyc hsep).closure_eq] at hmem

/-- **`D(Δ^{½}) ⊆ D(S)`**: the square-root domain sits inside the Tomita-closure domain. -/
theorem modularSqrt_domain_le_tomitaClosure_domain :
    (modularSqrt hcyc hsep).domain ≤ (tomitaClosure M Ω).domain := by
  intro y hy
  have h := mem_tomitaClosure_graph_of_modularSqrt hcyc hsep ⟨y, hy⟩
  rw [LinearPMap.mem_graph_iff] at h
  obtain ⟨z, hz1, -⟩ := h
  have hz1' : (z : H) = y := hz1
  exact hz1' ▸ z.2

/-- **The extended polar decomposition** `S y = W (Δ^{½} y)` on **all** of `D(Δ^{½})` —
`modularW_apply_modularSqrt` upgraded from `D(Δ)` to the full square-root domain. -/
theorem tomitaClosure_eq_modularW_modularSqrt (y : (modularSqrt hcyc hsep).domain) :
    tomitaClosure M Ω ⟨(y : H), modularSqrt_domain_le_tomitaClosure_domain hcyc hsep y.2⟩
      = modularW hcyc hsep (modularSqrt hcyc hsep y) := by
  have h := mem_tomitaClosure_graph_of_modularSqrt hcyc hsep y
  rw [LinearPMap.mem_graph_iff] at h
  obtain ⟨z, hz1, hz2⟩ := h
  have hz1' : (z : H) = (y : H) := hz1
  have hz2' : tomitaClosure M Ω z = modularW hcyc hsep (modularSqrt hcyc hsep y) := hz2
  rw [← hz2']
  congr 1
  exact Subtype.ext hz1'.symm

/-- **`D(S) ⊆ D(Δ^{½})`**: conversely, the Tomita-closure domain sits inside the square-root
domain — via the graph-L² core fact and the polar relation read backwards through `W⁻¹`. -/
theorem tomitaClosure_domain_le_modularSqrt_domain :
    (tomitaClosure M Ω).domain ≤ (modularSqrt hcyc hsep).domain := by
  intro y hy
  -- `q := toLp (y, S y)` lies in the closure of the restricted L²-graph
  have hqK : WithLp.toLp 2 ((y : H), tomitaClosure M Ω ⟨y, hy⟩)
      ∈ closure ((modularGraphL2 M Ω) : Set (WithLp 2 (H × Conj H))) := by
    rw [← Submodule.topologicalClosure_coe,
      ← graphL2_eq_topologicalClosure_modularGraphL2 hcyc hsep]
    rw [SetLike.mem_coe, mem_graphL2_iff, WithLp.ofLp_toLp]
    exact (tomitaClosure M Ω).mem_graph ⟨y, hy⟩
  -- `(u,v) ↦ (u, W⁻¹v)` is continuous and maps the restricted L²-graph into `Γ(Δ^{½})`
  have hψcont : Continuous fun w : WithLp 2 (H × Conj H) =>
      ((WithLp.ofLp w).1, (modularW hcyc hsep).symm (WithLp.ofLp w).2) :=
    (continuous_fst.comp (WithLp.prod_continuous_ofLp 2 H (Conj H))).prodMk
      ((modularW hcyc hsep).symm.continuous.comp
        (continuous_snd.comp (WithLp.prod_continuous_ofLp 2 H (Conj H))))
  have hsub : (fun w : WithLp 2 (H × Conj H) =>
        ((WithLp.ofLp w).1, (modularW hcyc hsep).symm (WithLp.ofLp w).2)) ''
        ((modularGraphL2 M Ω) : Set (WithLp 2 (H × Conj H)))
      ⊆ ((modularSqrt hcyc hsep).graph : Set (H × H)) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, LinearPMap.mem_graph_iff]
    refine ⟨⟨(x : H), modularOp_domain_le_modularSqrt_domain hcyc hsep x.2⟩, ?_, ?_⟩
    · simp [modularPairing_apply]
    · change modularSqrt hcyc hsep ⟨(x : H), modularOp_domain_le_modularSqrt_domain hcyc hsep x.2⟩
        = (modularW hcyc hsep).symm (tomitaOnModularDomain M Ω x)
      rw [← modularW_apply_modularSqrt hcyc hsep x, LinearIsometryEquiv.symm_apply_apply]
      rfl
  -- combine: `(y, W⁻¹(Sy))` lies in the closed graph of `Δ^{½}`
  have hmem := (closure_mono hsub) (image_closure_subset_closure_image hψcont
    (Set.mem_image_of_mem _ hqK))
  rw [(show IsClosed ((modularSqrt hcyc hsep).graph : Set (H × H)) from
    (modularSqrt_isSelfAdjoint hcyc hsep).isClosed).closure_eq] at hmem
  rw [SetLike.mem_coe, LinearPMap.mem_graph_iff] at hmem
  obtain ⟨z, hz1, -⟩ := hmem
  have hz1' : (z : H) = y := hz1
  exact hz1' ▸ z.2

/-- **The polar domains coincide: `D(S) = D(Δ^{½})`.** -/
theorem tomitaClosure_domain_eq_modularSqrt_domain :
    (tomitaClosure M Ω).domain = (modularSqrt hcyc hsep).domain :=
  le_antisymm (tomitaClosure_domain_le_modularSqrt_domain hcyc hsep)
    (modularSqrt_domain_le_tomitaClosure_domain hcyc hsep)

/-- **Extended polar isometry** `‖Δ^{½}y‖ = ‖Sy‖` on all of `D(Δ^{½})` — the norm identity
`norm_modularSqrt_eq_norm_tomita` upgraded from `D(Δ)` (immediate, since `W` is an isometry). -/
theorem norm_modularSqrt_eq_norm_tomitaClosure (y : (modularSqrt hcyc hsep).domain) :
    ‖modularSqrt hcyc hsep y‖
      = ‖tomitaClosure M Ω ⟨(y : H), modularSqrt_domain_le_tomitaClosure_domain hcyc hsep y.2⟩‖ :=
  by rw [tomitaClosure_eq_modularW_modularSqrt hcyc hsep y, LinearIsometryEquiv.norm_map]

/-- **The extended polar decomposition in `J`-form**: `toConj (J (Δ^{½} y)) = S y` on **all** of
`D(Δ^{½})` — `tomita_eq_modularConjugation_modularSqrt` upgraded from `D(Δ)`. -/
theorem tomita_eq_modularConjugation_modularSqrt_full (y : (modularSqrt hcyc hsep).domain) :
    (toConjₗᵢ H) (modularConjugation hcyc hsep (modularSqrt hcyc hsep y))
      = tomitaClosure M Ω ⟨(y : H), modularSqrt_domain_le_tomitaClosure_domain hcyc hsep y.2⟩ := by
  rw [modularConjugation, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply,
    ← tomitaClosure_eq_modularW_modularSqrt hcyc hsep y]

end Spectra.TomitaTakesaki
