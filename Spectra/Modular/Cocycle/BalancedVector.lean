/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.Cocycle.MatrixAmplification
import Spectra.Modular.KMS.GNSBridge
/-!
# The balanced vector on `H ⊕ H`: cyclic for `M₂(M)`, but NOT separating (D3-1)

The balanced state `θ = φ + ψ` on `M₂(M)` drives the Connes Radon–Nikodym cocycle.  A naive
guess for its GNS data is the **balanced vector** `Ω_θ = (Ω_φ, Ω_ψ) ∈ H ⊕ H` for the amplification
`M₂(M)` built in `MatrixAmplification.lean`.  This file settles the status of that guess, in both
directions:

* **The cyclic half is real.** `isCyclic_M2_of_isCyclic`: if `Ω_φ` and `Ω_ψ` are cyclic for `M`,
  then `(Ω_φ, Ω_ψ)` is cyclic for `M₂(M)` on `H2 H = WithLp 2 (H × H)`.  The diagonal blocks
  `[[a, 0], [0, b]]` already sweep out a dense set `{(a Ω_φ, b Ω_ψ)}`.

* **The separating half is FALSE — in-code witness.** `not_isSeparating_M2_wholeAlgebra`: for
  `M = B(H)` (the double commutant of `Set.univ`, `wholeAlgebra`) and any `Ω ≠ 0`, the vector
  `(Ω, Ω)` is **not** separating for `M₂(B(H))`: the block operator `[[1, -1], [0, 0]]` is a
  nonzero element of `M₂(B(H))` annihilating `(Ω, Ω)`.

Together these seal the "`H ⊕ H`" dead-end permanently, confirming the refutation recorded in the
balanced-cocycle synthesis plan (`PLAN-balanced-cocycle-synthesis.md`): the naive `Ω_θ` on `H ⊕ H`
is *not* a cyclic-and-separating vector for `M₂(M)`, and the vector state it induces on `M₂(M)` is
not the balanced state `θ` either.  The correct GNS carrier for `θ` has the size of `H⁴`
(`M₂(M)` acting on itself, i.e. GNS of `θ`), which is why the cocycle construction must route
through a genuine GNS representation of `θ` (Route A) rather than through `H ⊕ H`.

Along the way we record two pieces of reusable infrastructure:

* `cyclicSubmodule` / `span_cyclicSet` / `isCyclic_iff_dense_cyclicSet` — the orbit `M Ω` is
  already a `ℂ`-submodule (no span needed), so cyclicity is plain density of the orbit set;
* `wholeAlgebra` / `mem_wholeAlgebra` / `isCyclic_wholeAlgebra` — `B(H)` as a
  `VonNeumannAlgebra H` (Mathlib has no `⊤ : VonNeumannAlgebra H` instance), with every vector
  `Ω ≠ 0` cyclic for it via a rank-one operator.
-/

namespace Spectra.TomitaTakesaki

open ContinuousLinearMap
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## 1. The orbit `M Ω` is already a submodule

`a • (x Ω) + y Ω = ((a • x) + y) Ω` and `M` is closed under scalars and addition, so the set
`cyclicSet M Ω` needs no span: cyclicity is just density of the orbit. -/

/-- The orbit `M Ω = {T Ω | T ∈ M}` as a `ℂ`-submodule of `H`: `M` is closed under `0`, `+`, and
`ℂ`-scalars, and application at `Ω` is linear in the operator. -/
def cyclicSubmodule (M : VonNeumannAlgebra H) (Ω : H) : Submodule ℂ H where
  carrier := cyclicSet M Ω
  zero_mem' := ⟨0, zero_mem _, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, add_mem ha hb, by simp⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, rfl⟩
    refine ⟨c • a, ?_, by simp⟩
    rw [Algebra.smul_def]
    exact mul_mem (algebraMap_mem M.toStarSubalgebra c) ha

@[simp] lemma coe_cyclicSubmodule (M : VonNeumannAlgebra H) (Ω : H) :
    (cyclicSubmodule M Ω : Set H) = cyclicSet M Ω := rfl

/-- The span of the orbit collapses to the orbit: `span ℂ (M Ω) = M Ω`. -/
lemma span_cyclicSet (M : VonNeumannAlgebra H) (Ω : H) :
    Submodule.span ℂ (cyclicSet M Ω) = cyclicSubmodule M Ω :=
  Submodule.span_eq (cyclicSubmodule M Ω)

/-- Cyclicity is plain density of the orbit set `M Ω` (no span needed). -/
lemma isCyclic_iff_dense_cyclicSet {M : VonNeumannAlgebra H} {Ω : H} :
    IsCyclic M Ω ↔ Dense (cyclicSet M Ω) := by
  unfold IsCyclic
  rw [span_cyclicSet]
  exact Iff.rfl

/-! ## 2. ★ The balanced vector is cyclic for `M₂(M)`

The diagonal blocks `[[a, 0], [0, b]]` send `(Ω_φ, Ω_ψ)` to `(a Ω_φ, b Ω_ψ)`; density of the two
orbits in `H` gives density of the product orbit in `H × H`, and `toLp 2` transports it to
`H2 H`. -/

/-- **The balanced vector is cyclic for the amplification.**  If `Ω_φ` and `Ω_ψ` are cyclic for
`M`, then `(Ω_φ, Ω_ψ) ∈ H2 H` is cyclic for `M₂(M)`.  This is the *true* half of the naive
"balanced GNS data on `H ⊕ H`" guess; the separating half fails
(`not_isSeparating_M2_wholeAlgebra`). -/
theorem isCyclic_M2_of_isCyclic {M : VonNeumannAlgebra H} {Ωφ Ωψ : H}
    (hφ : IsCyclic M Ωφ) (hψ : IsCyclic M Ωψ) :
    IsCyclic (M2 M) (WithLp.toLp 2 (Ωφ, Ωψ)) := by
  -- Density of the product orbit in `H × H`, transported to `H2 H` along `toLp 2`.
  have hprod : Dense (cyclicSet M Ωφ ×ˢ cyclicSet M Ωψ) :=
    (isCyclic_iff_dense_cyclicSet.mp hφ).prod (isCyclic_iff_dense_cyclicSet.mp hψ)
  have himg : Dense ((WithLp.toLp 2 : H × H → H2 H) ''
      (cyclicSet M Ωφ ×ˢ cyclicSet M Ωψ)) :=
    (WithLp.toLp_surjective (p := 2)).denseRange.dense_image
      (WithLp.prod_continuous_toLp 2 H H) hprod
  -- Every point of that dense set is `blockOp a 0 0 b` applied to the balanced vector.
  refine himg.mono ?_
  rintro _ ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
  obtain ⟨a, ha, rfl⟩ := hu
  obtain ⟨b, hb, rfl⟩ := hv
  refine Submodule.subset_span
    ⟨blockOp a 0 0 b, ⟨a, ha, 0, zero_mem _, 0, zero_mem _, b, hb, rfl⟩, ?_⟩
  simp [blockOp_apply]

/-! ## 3. `B(H)` as a von Neumann algebra

Mathlib's docstring promises `⊤ : VonNeumannAlgebra H` but no such instance exists yet; we obtain
`B(H)` as the double commutant of `Set.univ` via `Spectra.KMS.doubleCommutant`. -/

/-- The full algebra `B(H)` of bounded operators, as a `VonNeumannAlgebra H`: the double
commutant of `Set.univ` (trivially star-closed). -/
noncomputable def wholeAlgebra : VonNeumannAlgebra H :=
  Spectra.KMS.doubleCommutant Set.univ (fun x _ => Set.mem_univ (star x))

/-- Every bounded operator belongs to `wholeAlgebra`: anything commuting with *all* operators
commutes in particular with `x`. -/
theorem mem_wholeAlgebra (x : H →L[ℂ] H) : x ∈ wholeAlgebra (H := H) := by
  have hx : x ∈ (Spectra.KMS.doubleCommutant (Set.univ : Set (H →L[ℂ] H))
      (fun y _ => Set.mem_univ (star y)) : Set (H →L[ℂ] H)) := by
    rw [Spectra.KMS.coe_doubleCommutant, Set.mem_centralizer_iff]
    intro y hy
    exact (Set.mem_centralizer_iff.mp hy x (Set.mem_univ x)).symm
  exact hx

/-- Every nonzero vector is cyclic for `B(H)`: the rank-one operator
`x ↦ (⟪Ω, x⟫ / ‖Ω‖²) • v` sends `Ω` to any prescribed `v`, so the orbit is *all* of `H`. -/
theorem isCyclic_wholeAlgebra {Ω : H} (hΩ : Ω ≠ 0) : IsCyclic (wholeAlgebra (H := H)) Ω := by
  rw [isCyclic_iff_dense_cyclicSet]
  have huniv : cyclicSet (wholeAlgebra (H := H)) Ω = Set.univ := by
    refine Set.eq_univ_of_forall fun v => ?_
    refine ⟨((‖Ω‖ : ℂ) ^ 2)⁻¹ • (innerSL ℂ Ω).smulRight v, mem_wholeAlgebra _, ?_⟩
    have hnorm : ((‖Ω‖ : ℂ) ^ 2) ≠ 0 := by
      exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hΩ)
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, inner_self_eq_norm_sq_to_K]
    exact inv_smul_smul₀ hnorm v
  rw [huniv]
  exact dense_univ

/-! ## 4. ★ The balanced vector is NOT separating: the in-code witness

Take `M = B(H)` and `Ω ≠ 0`.  The block operator `T = [[1, -1], [0, 0]]` lies in `M₂(B(H))`, kills
the balanced vector `(Ω, Ω)` — its first row computes `Ω - Ω = 0` — but `T ≠ 0` since
`T (Ω, 0) = (Ω, 0)`.  So `(Ω, Ω)` is cyclic for `M₂(B(H))` (by `isCyclic_M2_of_isCyclic` and
`isCyclic_wholeAlgebra`) yet **not** separating: the naive balanced GNS guess on `H ⊕ H` is dead. -/

/-- **The balanced vector `(Ω, Ω)` is not separating for `M₂(B(H))`.**  Witness:
`[[1, -1], [0, 0]] ∈ M₂(B(H))` annihilates `(Ω, Ω)` but is nonzero. -/
theorem not_isSeparating_M2_wholeAlgebra {Ω : H} (hΩ : Ω ≠ 0) :
    ¬ IsSeparating (M2 (wholeAlgebra (H := H))) (WithLp.toLp 2 (Ω, Ω)) := by
  intro hsep
  -- The witness lies in `M₂(B(H))` — all four entries are bounded operators.
  have hmem : blockOp (1 : H →L[ℂ] H) (-1) 0 0 ∈ M2 (wholeAlgebra (H := H)) :=
    ⟨1, mem_wholeAlgebra _, -1, mem_wholeAlgebra _, 0, mem_wholeAlgebra _,
      0, mem_wholeAlgebra _, rfl⟩
  -- It annihilates the balanced vector: first row `Ω - Ω = 0`, second row `0`.
  have hkill : blockOp (1 : H →L[ℂ] H) (-1) 0 0 (WithLp.toLp 2 (Ω, Ω)) = 0 := by
    simp [blockOp_apply]
  -- Separation would force the witness to vanish...
  have hT : blockOp (1 : H →L[ℂ] H) (-1) 0 0 = 0 := hsep _ hmem hkill
  -- ...but it acts as the identity on `(Ω, 0)`.
  have happ := congrArg (fun T : H2 H →L[ℂ] H2 H => WithLp.fst (T (inl₂ Ω))) hT
  simp only [blockOp_inl₂, ContinuousLinearMap.one_apply, ContinuousLinearMap.zero_apply,
    WithLp.toLp_fst] at happ
  exact hΩ happ

/-- **The dead-end, packaged.**  On any nontrivial Hilbert space there is a von Neumann algebra
`M` and a vector of `H2 H` that is cyclic for `M₂(M)` but not separating — the balanced vector
`(Ω, Ω)` over `M = B(H)`. -/
theorem exists_isCyclic_not_isSeparating_M2 [Nontrivial H] :
    ∃ (M : VonNeumannAlgebra H) (Ω₂ : H2 H),
      IsCyclic (M2 M) Ω₂ ∧ ¬ IsSeparating (M2 M) Ω₂ := by
  obtain ⟨Ω, hΩ⟩ := exists_ne (0 : H)
  exact ⟨wholeAlgebra, WithLp.toLp 2 (Ω, Ω),
    isCyclic_M2_of_isCyclic (isCyclic_wholeAlgebra hΩ) (isCyclic_wholeAlgebra hΩ),
    not_isSeparating_M2_wholeAlgebra hΩ⟩

end Spectra.TomitaTakesaki
