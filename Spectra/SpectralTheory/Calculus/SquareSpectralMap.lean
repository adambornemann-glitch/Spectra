/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SpectralTheory.Calculus.SquarePushforward
import Spectra.ProjValMeasure.Map
import Spectra.SpectralTheory.Essential.Weyl
/-!
# The `s ↦ s²` spectral-mapping theorem: `E^{A²} = (spectralPVM A).map (·²)`

Building on the resolvent identity `(A² − z)⁻¹ = Φ(1/(s²−z))` (`resolvent_sq_identity`), this file
proves the **spectral-mapping theorem for squares**: for a self-adjoint `A` with
`A² := pmapOfPVM (genToGroup A) (·²)`,

> `spectralPVM (A²) = (spectralPVM A).map (fun s => s²)`   (`spectralPVM_sq_eq_pushforward`)

i.e. the spectral measure of `A²` is the `s ↦ s²` pushforward of the spectral measure of `A`. This
is the DAG-node `spectralPVM_sq_eq_pushforward` of the Field-3 polar-uniqueness plan — the
load-bearing step feeding positive-square-root uniqueness `posSqrt_unique`.

Along the way (all `J`-free, for an arbitrary one-parameter unitary group `U_grp`):

* `sq_isSelfAdjoint` — `A² := pmapOfPVM U_grp (·²)` is **self-adjoint**, via von Neumann's
  deficiency criterion: symmetry (real symbol `s²`), density of `D(A²)` (spectral cut-offs), and
  surjectivity of `A² ± i` (both read off `resolvent_sq_identity` at `z = ∓i`).
* `selfAdjointResolvent_sq_eq` — the resolvent bridge `(A² − z)⁻¹ = Φ(1/(s²−z))`, identifying the
  abstract self-adjoint resolvent with the concrete bounded calculus (via
  `selfAdjointResolvent_left_inverse`).
-/

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal
open Spectra.Essential Spectra.YosidaHille

namespace Spectra.QuantumMechanics.SpectralTheory

open Spectra Spectra.Borel Spectra.OneParameterUnitaryGroup SpectralMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-! ## `A² := pmapOfPVM U_grp (·²)` is self-adjoint -/

/-- `conj((s:ℂ)²) = (s:ℂ)²` — the square symbol is real. -/
lemma conj_sq_ofReal (s : ℝ) : (starRingEnd ℂ) ((s : ℂ) ^ 2) = (s : ℂ) ^ 2 := by
  have h : (s : ℂ) ^ 2 = ((s ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.conj_ofReal]

/-- **Symmetry of `A²`** (`A².IsFormalAdjoint A²`), from the real symbol `s²`. -/
theorem sq_isFormalAdjoint :
    (pmapOfPVM U_grp (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal).IsFormalAdjoint
      (pmapOfPVM U_grp (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal) :=
  pmapOfPVM_isFormalAdjoint_self U_grp (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal conj_sq_ofReal

/-- The cut-off `E([-N,N]) ξ` lies in `D(A²)` (the symbol `s²·1_{[-N,N]}` is bounded by `N²`). -/
lemma sq_proj_Icc_mem (ξ : H) (N : ℕ) :
    spectralProjection U_grp (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc ξ
      ∈ (pmapOfPVM U_grp (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal).domain := by
  have hfg : ∃ C, ∀ s : ℝ, ‖(s : ℂ) ^ 2 *
      Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ)) (fun _ => (1 : ℂ)) s‖ ≤ C := by
    refine ⟨(N : ℝ) ^ 2, fun s => ?_⟩
    by_cases hs : s ∈ Set.Icc (-(N : ℝ)) (N : ℝ)
    · rw [Set.indicator_of_mem hs, mul_one, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      rw [Set.mem_Icc] at hs
      have hle : |s| ≤ (N : ℝ) := abs_le.mpr hs
      nlinarith [abs_nonneg s, hle]
    · rw [Set.indicator_of_notMem hs, mul_zero, norm_zero]; positivity
  exact mem_pmapDomain_spectralCalculus U_grp (fun s => (s : ℂ) ^ 2)
    (Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ)) (fun _ => (1 : ℂ)))
    measurable_sq_ofReal (measurable_const.indicator measurableSet_Icc) (indicator_one_bdd _) hfg ξ

/-- **Density of `D(A²)`**: the cut-offs `E([-N,N]) ξ ∈ D(A²)` converge to `ξ`. -/
theorem sq_domain_dense :
    Dense ((pmapOfPVM U_grp (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal).domain : Set H) := by
  intro ξ
  exact mem_closure_of_tendsto (tendsto_spectralProjection_Icc_univ U_grp ξ)
    (Filter.Eventually.of_forall (fun N => sq_proj_Icc_mem U_grp ξ N))

/-- **Surjectivity of `A² + i`**, read off `resolvent_sq_identity` at `z = −i`. -/
theorem sq_add_I_surjective (φ : H) :
    ∃ ψ : (pmapOfPVM U_grp (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal).domain,
      pmapOfPVM U_grp (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal ψ + I • (ψ : H) = φ := by
  have hz : (-I : ℂ).im ≠ 0 := by simp
  refine ⟨⟨spectralCalculus U_grp (fun s => ((s : ℂ) ^ 2 - (-I))⁻¹) (measurable_inv_sq_sub (-I))
      (bdd_inv_sq_sub hz) φ, resolvent_sq_mem U_grp hz φ⟩, ?_⟩
  rw [resolvent_sq_identity U_grp hz φ]; module

/-- **Surjectivity of `A² − i`**, read off `resolvent_sq_identity` at `z = i`. -/
theorem sq_sub_I_surjective (φ : H) :
    ∃ ψ : (pmapOfPVM U_grp (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal).domain,
      pmapOfPVM U_grp (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal ψ - I • (ψ : H) = φ := by
  have hz : (I : ℂ).im ≠ 0 := by simp
  refine ⟨⟨spectralCalculus U_grp (fun s => ((s : ℂ) ^ 2 - I)⁻¹) (measurable_inv_sq_sub I)
      (bdd_inv_sq_sub hz) φ, resolvent_sq_mem U_grp hz φ⟩, ?_⟩
  rw [resolvent_sq_identity U_grp hz φ]; module

/-- **`A² := pmapOfPVM U_grp (·²)` is self-adjoint** (von Neumann deficiency criterion). -/
theorem sq_isSelfAdjoint :
    IsSelfAdjoint (pmapOfPVM U_grp (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal) :=
  isSelfAdjoint_of_surjective_addSub _ (sq_isFormalAdjoint U_grp) (sq_domain_dense U_grp)
    (sq_add_I_surjective U_grp) (sq_sub_I_surjective U_grp)

/-! ## The resolvent bridge and the spectral-mapping theorem -/

/-- **The resolvent bridge** `(A² − z)⁻¹ = Φ(1/(s²−z))`: the abstract self-adjoint resolvent of `A²`
equals the concrete bounded calculus of the resolvent symbol.  From `resolvent_sq_identity`
(`(A²−z) Φ(1/(s²−z)) = 1`) and `selfAdjointResolvent_left_inverse`. -/
theorem selfAdjointResolvent_sq_eq {z : ℂ} (hz : z.im ≠ 0) (φ : H) :
    selfAdjointResolvent (sq_isSelfAdjoint U_grp) z hz φ
      = spectralCalculus U_grp (fun s => ((s : ℂ) ^ 2 - z)⁻¹) (measurable_inv_sq_sub z)
          (bdd_inv_sq_sub hz) φ := by
  have hli := selfAdjointResolvent_left_inverse (sq_isSelfAdjoint U_grp) z hz
    ⟨spectralCalculus U_grp (fun s => ((s : ℂ) ^ 2 - z)⁻¹) (measurable_inv_sq_sub z)
      (bdd_inv_sq_sub hz) φ, resolvent_sq_mem U_grp hz φ⟩
  rw [resolvent_sq_identity U_grp hz φ] at hli
  simpa using hli

/-- **The `s ↦ s²` spectral-mapping theorem.**  For self-adjoint `A`, the spectral measure of
`A² := pmapOfPVM (genToGroup A) (·²)` is the `s ↦ s²` pushforward of the spectral measure of `A`:

`spectralPVM (A²) = (spectralPVM A).map (fun s => s²)`.

Via `spectralPVM_unique`: the pushforward's diagonal represents `A²`'s resolvent, using the
resolvent bridge (`selfAdjointResolvent_sq_eq`), the diagonal identity (`inner_resolvent_sq`), and
the change-of-variables `∫ (t−z)⁻¹ d(map (·²) μ) = ∫ (s²−z)⁻¹ dμ`. -/
theorem spectralPVM_sq_eq_pushforward {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    spectralPVM (sq_isSelfAdjoint (genToGroup hA))
      = (spectralPVM hA).map (fun s => s ^ 2) (by fun_prop) := by
  symm
  refine spectralPVM_unique (sq_isSelfAdjoint (genToGroup hA))
    ((spectralPVM hA).map (fun s => s ^ 2) (by fun_prop)) (fun z hz ξ => ?_)
  rw [selfAdjointResolvent_sq_eq (genToGroup hA) hz ξ, inner_resolvent_sq (genToGroup hA) hz ξ,
    ProjValMeasure.map_diag, spectralPVM_diag,
    integral_map (by fun_prop)
      ((by fun_prop : Measurable fun t : ℝ => ((t : ℂ) - z)⁻¹).aestronglyMeasurable)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
  push_cast
  ring_nf

/-! ## Injectivity of the `s ↦ s²` pushforward on `[0,∞)`-supported measures -/

/-- **Injectivity of `(·²)_*` on measures supported in `[0,∞)`.**  If `μ, ν` on `ℝ` satisfy
`μ((-∞,0)) = ν((-∞,0)) = 0` and have equal `s ↦ s²` pushforwards, then `μ = ν`.  Proof: `√` inverts
`s ↦ s²` on `[0,∞)` — `√(s²) = |s| = s` there — so `√_* ((·²)_* ρ) = ρ` for any `[0,∞)`-supported
`ρ`, whence `μ = √_*((·²)_* μ) = √_*((·²)_* ν) = ν`. -/
theorem map_sq_injective_of_supported {μ ν : Measure ℝ}
    (hμ : μ (Set.Iio 0) = 0) (hν : ν (Set.Iio 0) = 0)
    (h : Measure.map (fun s => s ^ 2) μ = Measure.map (fun s => s ^ 2) ν) : μ = ν := by
  have hsq_meas : Measurable (fun s : ℝ => s ^ 2) := by fun_prop
  have hrecover : ∀ ρ : Measure ℝ, ρ (Set.Iio 0) = 0 →
      Measure.map Real.sqrt (Measure.map (fun s => s ^ 2) ρ) = ρ := by
    intro ρ hρ
    rw [Measure.map_map Real.continuous_sqrt.measurable hsq_meas]
    have hae : (Real.sqrt ∘ fun s => s ^ 2) =ᵐ[ρ] id := by
      refine ae_iff.mpr (measure_mono_null (fun s hs => ?_) hρ)
      simp only [Set.mem_setOf_eq, Function.comp_apply, id_eq, Real.sqrt_sq_eq_abs] at hs
      by_contra hs0
      rw [Set.mem_Iio, not_lt] at hs0
      exact hs (abs_of_nonneg hs0)
    rw [Measure.map_congr hae, Measure.map_id]
  rw [← hrecover μ hμ, ← hrecover ν hν, h]

/-- **`(·²)_*` is injective on PVMs whose diagonal measures are supported in `[0,∞)`.**  If
`P.map (·²) = Q.map (·²)` and both `P, Q` have `diag ξ ((-∞,0)) = 0`, then `P = Q` (via
`ext_of_diag` and `map_sq_injective_of_supported` on each diagonal).  This is the injectivity half
of the spectral `s ↦ s²` mapping powering positive-square-root uniqueness. -/
theorem sq_pushforward_injective {P Q : ProjValMeasure H}
    (hP : ∀ ξ : H, P.diag ξ (Set.Iio 0) = 0) (hQ : ∀ ξ : H, Q.diag ξ (Set.Iio 0) = 0)
    (h : P.map (fun s => s ^ 2) (by fun_prop) = Q.map (fun s => s ^ 2) (by fun_prop)) : P = Q := by
  refine ProjValMeasure.ext_of_diag (fun ξ => ?_)
  have hd : (P.diag ξ).map (fun s => s ^ 2) = (Q.diag ξ).map (fun s => s ^ 2) := by
    have hc := congrArg (fun R : ProjValMeasure H => R.diag ξ) h
    simpa only [ProjValMeasure.map_diag] using hc
  exact map_sq_injective_of_supported (hP ξ) (hQ ξ) hd

/-! ## A self-adjoint operator is determined by its spectral measure -/

/-- `spectralPVM` congruence: propositionally equal self-adjoint operators have equal spectral
measures (proof irrelevance in the self-adjointness witness). -/
theorem spectralPVM_congr {A B : H →ₗ.[ℂ] H} (hAB : A = B)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) : spectralPVM hA = spectralPVM hB := by
  subst hAB; rfl

/-- **Equal resolvents (at `z = i`) ⟹ equal operators.**  The resolvent `R := (P − i)⁻¹` is a
bijection `H → D(P)`: `selfAdjointResolvent_mem_domain` and `selfAdjointResolvent_left_inverse` give
`D(P) = range R`, and `selfAdjointResolvent_solves` recovers the operator on that range.  So a
shared resolvent forces equal domains and equal values, i.e. `P = Q`. -/
theorem eq_of_selfAdjointResolvent_eq {P Q : H →ₗ.[ℂ] H}
    (hP : IsSelfAdjoint P) (hQ : IsSelfAdjoint Q)
    (h : selfAdjointResolvent hP I I_im_ne_zero = selfAdjointResolvent hQ I I_im_ne_zero) :
    P = Q := by
  have hdom : P.domain = Q.domain := by
    refine SetLike.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · have hli : selfAdjointResolvent hP I I_im_ne_zero (P ⟨x, hx⟩ - I • x) = x := by
        simpa using selfAdjointResolvent_left_inverse hP I I_im_ne_zero ⟨x, hx⟩
      have hxeq : x = selfAdjointResolvent hQ I I_im_ne_zero (P ⟨x, hx⟩ - I • x) := by
        rw [← h]; exact hli.symm
      rw [hxeq]; exact selfAdjointResolvent_mem_domain hQ I I_im_ne_zero _
    · have hli : selfAdjointResolvent hQ I I_im_ne_zero (Q ⟨x, hx⟩ - I • x) = x := by
        simpa using selfAdjointResolvent_left_inverse hQ I I_im_ne_zero ⟨x, hx⟩
      have hxeq : x = selfAdjointResolvent hP I I_im_ne_zero (Q ⟨x, hx⟩ - I • x) := by
        rw [h]; exact hli.symm
      rw [hxeq]; exact selfAdjointResolvent_mem_domain hP I I_im_ne_zero _
  refine LinearPMap.ext hdom (fun x hxP hxQ => ?_)
  have hvalP : selfAdjointResolvent hP I I_im_ne_zero (P ⟨x, hxP⟩ - I • x) = x := by
    simpa using selfAdjointResolvent_left_inverse hP I I_im_ne_zero ⟨x, hxP⟩
  have hvalQ : selfAdjointResolvent hQ I I_im_ne_zero (P ⟨x, hxP⟩ - I • x) = x := by
    rw [← h]; exact hvalP
  have hsQ := selfAdjointResolvent_solves hQ I I_im_ne_zero (P ⟨x, hxP⟩ - I • x)
  -- convert the `Q ⟨R φ, _⟩` term to `Q ⟨x, hxQ⟩` (value equality, no dependent rewrite)
  have hcong : (⟨selfAdjointResolvent hQ I I_im_ne_zero (P ⟨x, hxP⟩ - I • x),
      selfAdjointResolvent_mem_domain hQ I I_im_ne_zero (P ⟨x, hxP⟩ - I • x)⟩ : Q.domain)
      = ⟨x, hxQ⟩ := Subtype.ext hvalQ
  rw [hcong, hvalQ] at hsQ
  -- hsQ : Q ⟨x, hxQ⟩ - I • x = P ⟨x, hxP⟩ - I • x
  calc P ⟨x, hxP⟩ = (P ⟨x, hxP⟩ - I • x) + I • x := by abel
    _ = (Q ⟨x, hxQ⟩ - I • x) + I • x := by rw [← hsQ]
    _ = Q ⟨x, hxQ⟩ := by abel

/-- **A self-adjoint operator is determined by its spectral measure.**  Equal spectral PVMs give
equal resolvent diagonals (`spectralPVM_resolvent_formula`), hence equal resolvents (complex
polarization, `op_ext_of_inner_self`), hence equal operators (`eq_of_selfAdjointResolvent_eq`). -/
theorem spectralPVM_determines {P Q : H →ₗ.[ℂ] H} (hP : IsSelfAdjoint P) (hQ : IsSelfAdjoint Q)
    (h : spectralPVM hP = spectralPVM hQ) : P = Q := by
  refine eq_of_selfAdjointResolvent_eq hP hQ (op_ext_of_inner_self fun ξ => ?_)
  rw [spectralPVM_resolvent_formula hP I I_im_ne_zero ξ, h,
    ← spectralPVM_resolvent_formula hQ I I_im_ne_zero ξ]

/-! ## ★ Positive-square-root uniqueness (the keystone) -/

/-- **Positive-square-root uniqueness.**  For self-adjoint `P, Q` with spectral measures supported
in `[0,∞)` (`P, Q ≥ 0`), if their functional-calculus squares agree
(`pmapOfPVM (genToGroup P) (·²) = pmapOfPVM (genToGroup Q) (·²)`, i.e. `P² = Q²`), then `P = Q`.

Proof: `spectralPVM_sq_eq_pushforward` turns `P² = Q²` into
`(spectralPVM P).map(·²) = (spectralPVM Q).map(·²)`; `sq_pushforward_injective` (using `≥0` ⟹
support ⊆ `[0,∞)`) cancels the `(·²)` pushforward to give `spectralPVM P = spectralPVM Q`; and
`spectralPVM_determines` recovers `P = Q`. -/
theorem posSqrt_unique {P Q : H →ₗ.[ℂ] H} (hP : IsSelfAdjoint P) (hQ : IsSelfAdjoint Q)
    (hPnn : ∀ ξ : H, borelMeasure (genToGroup hP) ξ (Set.Iio 0) = 0)
    (hQnn : ∀ ξ : H, borelMeasure (genToGroup hQ) ξ (Set.Iio 0) = 0)
    (hsq : pmapOfPVM (genToGroup hP) (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal
         = pmapOfPVM (genToGroup hQ) (fun s => (s : ℂ) ^ 2) measurable_sq_ofReal) :
    P = Q := by
  have h1 : spectralPVM (sq_isSelfAdjoint (genToGroup hP))
      = spectralPVM (sq_isSelfAdjoint (genToGroup hQ)) :=
    spectralPVM_congr hsq _ _
  rw [spectralPVM_sq_eq_pushforward hP, spectralPVM_sq_eq_pushforward hQ] at h1
  have hsupP : ∀ ξ : H, (spectralPVM hP).diag ξ (Set.Iio 0) = 0 := fun ξ => by
    rw [spectralPVM_diag]; exact hPnn ξ
  have hsupQ : ∀ ξ : H, (spectralPVM hQ).diag ξ (Set.Iio 0) = 0 := fun ξ => by
    rw [spectralPVM_diag]; exact hQnn ξ
  exact spectralPVM_determines hP hQ (sq_pushforward_injective hsupP hsupQ h1)

end Spectra.QuantumMechanics.SpectralTheory
