/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.KMS.Condition
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Convex.KreinMilman
/-!
# The State Space as a Weak-* Convex, Closed Set

To bring the state space into the scope of convex-geometry tools (ultimately Krein–Milman, for
the existence of extremal/pure states), it must be realized as a subset of a topological vector
space. The bespoke `State A` is a bare structure with no topology, so we realize states inside
Mathlib's weak-* dual `WeakDual ℂ A` as the **positive, normalized** continuous functionals.

## Main statements

* `Spectra.KMS.stateSet` — the state space `{φ | (∀ a, 0 ≤ φ(a⋆a)) ∧ φ 1 = 1}` in `WeakDual ℂ A`.
* `Spectra.KMS.stateSet_convex` — it is convex.
* `Spectra.KMS.stateSet_isClosed` — it is weak-*-closed (positivity and normalization are
  weak-*-closed conditions, evaluation being weak-*-continuous).
* `Spectra.KMS.State.toWeakDual` — the bespoke `State A` embeds into `stateSet A`.

## Remaining for extremal states

Krein–Milman additionally needs weak-* **compactness**, i.e. boundedness of `stateSet`. That is
`‖φ‖ ≤ 1` for `φ` a state — the positive-functional norm theorem `‖φ‖ = φ(1)` — which requires
the C*-spectral bound `IsSelfAdjoint.le_algebraMap_norm_self` together with Cauchy–Schwarz for the
GNS form; with boundedness in hand, `WeakDual.isCompact_of_bounded_of_closed` and
`IsCompact.extremePoints_nonempty` finish the job. That norm bound is the next step.
-/

open Complex Set
open scoped ComplexOrder

namespace Spectra.KMS

variable {A : Type*} [CStarAlgebra A]

-- The C*-algebra order on `A` is not a global instance (Mathlib enables it locally to avoid
-- diamonds); we enable the spectral order for this file's positivity/monotonicity arguments.
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

/-- The state space of `A`, realized in the weak-* dual `WeakDual ℂ A` as the positive,
normalized continuous functionals. -/
def stateSet (A : Type*) [CStarAlgebra A] : Set (WeakDual ℂ A) :=
  {φ | (∀ a : A, 0 ≤ φ (star a * a)) ∧ φ 1 = 1}

/-- Membership in `stateSet A`: positivity on `star a * a` and normalization `φ 1 = 1`. -/
@[simp] lemma mem_stateSet {φ : WeakDual ℂ A} :
    φ ∈ stateSet A ↔ (∀ a : A, 0 ≤ φ (star a * a)) ∧ φ 1 = 1 := Iff.rfl

/-- The state space is convex: a real convex combination of states is a state. -/
lemma stateSet_convex : Convex ℝ (stateSet A) := by
  rintro φ ⟨hφp, hφ1⟩ ψ ⟨hψp, hψ1⟩ s t hs ht hst
  refine ⟨fun a => ?_, ?_⟩
  · have h : (s • φ + t • ψ) (star a * a)
        = s • φ (star a * a) + t • ψ (star a * a) := rfl
    rw [h]
    exact add_nonneg (smul_nonneg hs (hφp a)) (smul_nonneg ht (hψp a))
  · have h : (s • φ + t • ψ) 1 = s • φ 1 + t • ψ 1 := rfl
    rw [h, hφ1, hψ1, Complex.real_smul, Complex.real_smul, mul_one, mul_one,
      ← Complex.ofReal_add, hst, Complex.ofReal_one]

/-- The state space is weak-*-closed. -/
lemma stateSet_isClosed : IsClosed (stateSet A) := by
  -- The nonnegative cone of `ℂ` (in `ComplexOrder`) is closed.
  have hpos : IsClosed {z : ℂ | (0 : ℂ) ≤ z} := by
    have hset : {z : ℂ | (0 : ℂ) ≤ z} = {z : ℂ | 0 ≤ z.re} ∩ {z : ℂ | z.im = 0} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Complex.nonneg_iff]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
    rw [hset]
    exact (isClosed_Ici.preimage continuous_re).inter (isClosed_singleton.preimage continuous_im)
  -- Evaluation `φ ↦ φ x` is weak-*-continuous.
  have heval : ∀ x : A, Continuous (fun φ : WeakDual ℂ A => φ x) :=
    fun x => WeakBilin.eval_continuous _ x
  have hsplit : stateSet A
      = (⋂ a : A, (fun φ : WeakDual ℂ A => φ (star a * a)) ⁻¹' {z | 0 ≤ z})
        ∩ ((fun φ : WeakDual ℂ A => φ 1) ⁻¹' {1}) := by
    ext φ
    simp only [stateSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      Set.mem_singleton_iff]
  rw [hsplit]
  exact (isClosed_iInter fun a => hpos.preimage (heval _)).inter
    (isClosed_singleton.preimage (heval 1))

/-- A bespoke `State` viewed as an element of the weak-* dual. -/
noncomputable def State.toWeakDual (ω : State A) : WeakDual ℂ A :=
  StrongDual.toWeakDual ⟨ω.toFun, ω.continuous⟩

/-- The weak-* dual element `ω.toWeakDual` evaluates as the underlying state `ω`. -/
@[simp] lemma State.toWeakDual_apply (ω : State A) (a : A) : ω.toWeakDual a = ω a := rfl

/-- Every bespoke state lands in the weak-* state space. -/
lemma State.toWeakDual_mem (ω : State A) : ω.toWeakDual ∈ stateSet A :=
  ⟨fun a => by rw [State.toWeakDual_apply]; exact ω.nonneg a,
   by rw [State.toWeakDual_apply]; exact ω.normalized⟩

/-! ## Toward compactness: positivity, monotonicity, and the norm bound -/

/-- A state is positive on **all** nonnegative elements (not just `a⋆a`): every nonnegative
element is a finite sum of such, and `φ` is additive. -/
lemma stateSet.map_nonneg {φ : WeakDual ℂ A} (hφ : φ ∈ stateSet A) {x : A} (hx : 0 ≤ x) :
    0 ≤ φ x := by
  rw [StarOrderedRing.nonneg_iff] at hx
  induction hx using AddSubmonoid.closure_induction with
  | mem y hy => obtain ⟨s, rfl⟩ := hy; exact hφ.1 s
  | zero => simp
  | add y z _ _ ihy ihz => rw [map_add]; exact add_nonneg ihy ihz

/-- A state is monotone (in the C*-order / `ComplexOrder`). -/
lemma stateSet.map_mono {φ : WeakDual ℂ A} (hφ : φ ∈ stateSet A) {x y : A} (hxy : x ≤ y) :
    φ x ≤ φ y := by
  have h : 0 ≤ φ (y - x) := stateSet.map_nonneg hφ (sub_nonneg.mpr hxy)
  rw [map_sub] at h
  exact sub_nonneg.mp h

/-- A state sends a real scalar (via `algebraMap ℝ A`) to that scalar in `ℂ`. -/
lemma stateSet.apply_algebraMap {φ : WeakDual ℂ A} (hφ : φ ∈ stateSet A) (r : ℝ) :
    φ (algebraMap ℝ A r) = (r : ℂ) := by
  rw [IsScalarTower.algebraMap_apply ℝ ℂ A, Algebra.algebraMap_eq_smul_one, map_smul, hφ.2,
    smul_eq_mul, mul_one, Complex.coe_algebraMap]

/-- The diagonal of the GNS form is bounded by the squared norm:
`(φ (a⋆a)).re ≤ ‖a‖²`. (Spectral bound `a⋆a ≤ ‖a⋆a‖•1` plus monotonicity.) -/
lemma stateSet.apply_star_mul_self_le {φ : WeakDual ℂ A} (hφ : φ ∈ stateSet A) (a : A) :
    (φ (star a * a)).re ≤ ‖a‖ * ‖a‖ := by
  have hsa : IsSelfAdjoint (star a * a) := by
    rw [isSelfAdjoint_iff, star_mul, star_star]
  have h := stateSet.map_mono hφ hsa.le_algebraMap_norm_self
  rw [stateSet.apply_algebraMap hφ, CStarRing.norm_star_mul_self] at h
  rw [Complex.le_def] at h
  simpa using h.1

/-- On a self-adjoint element the state is contractive: `‖φ h‖ ≤ ‖h‖`. The order squeeze
`-‖h‖•1 ≤ h ≤ ‖h‖•1` (spectral) pushed through `φ` simultaneously bounds the real part and
forces the imaginary part to vanish (hermiticity, for free). -/
lemma stateSet.norm_apply_le_of_isSelfAdjoint {φ : WeakDual ℂ A} (hφ : φ ∈ stateSet A)
    {h : A} (hh : IsSelfAdjoint h) : ‖φ h‖ ≤ ‖h‖ := by
  have hub := stateSet.map_mono hφ hh.le_algebraMap_norm_self
  have hlb := stateSet.map_mono hφ hh.neg_algebraMap_norm_le_self
  rw [stateSet.apply_algebraMap hφ] at hub
  rw [map_neg, stateSet.apply_algebraMap hφ] at hlb
  rw [Complex.le_def] at hub hlb
  have him : (φ h).im = 0 := by simpa using hub.2
  have hre1 : (φ h).re ≤ ‖h‖ := by simpa using hub.1
  have hre2 : -‖h‖ ≤ (φ h).re := by simpa using hlb.1
  have hz : φ h = ((φ h).re : ℂ) := by apply Complex.ext <;> simp [him]
  rw [hz, Complex.norm_real]
  exact abs_le.mpr ⟨hre2, hre1⟩

/-- A state is bounded with `‖φ a‖ ≤ 2‖a‖` (so `‖φ‖ ≤ 2`). Decompose `a = ℜa + i·ℑa` into
self-adjoint parts and apply the self-adjoint bound to each. -/
lemma stateSet.norm_apply_le {φ : WeakDual ℂ A} (hφ : φ ∈ stateSet A) (a : A) :
    ‖φ a‖ ≤ 2 * ‖a‖ := by
  have hre : ‖φ (realPart a : A)‖ ≤ ‖a‖ :=
    (stateSet.norm_apply_le_of_isSelfAdjoint hφ (realPart a).2).trans (realPart.norm_le a)
  have him : ‖φ (imaginaryPart a : A)‖ ≤ ‖a‖ :=
    (stateSet.norm_apply_le_of_isSelfAdjoint hφ (imaginaryPart a).2).trans (imaginaryPart.norm_le a)
  calc ‖φ a‖ = ‖φ ((realPart a : A) + I • (imaginaryPart a : A))‖ := by
        rw [realPart_add_I_smul_imaginaryPart a]
    _ = ‖φ (realPart a : A) + I • φ (imaginaryPart a : A)‖ := by rw [map_add, map_smul]
    _ ≤ ‖φ (realPart a : A)‖ + ‖I • φ (imaginaryPart a : A)‖ := norm_add_le _ _
    _ = ‖φ (realPart a : A)‖ + ‖φ (imaginaryPart a : A)‖ := by
        rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ ‖a‖ + ‖a‖ := add_le_add hre him
    _ = 2 * ‖a‖ := by ring

/-! ## Compactness and pure states -/

/-- **The state space is weak-*-compact** (Banach–Alaoglu): it is a weak-*-closed subset of the
weak-*-compact ball of radius `2` (states satisfy `‖φ‖ ≤ 2`). -/
lemma stateSet_isCompact : IsCompact (stateSet A) := by
  refine (WeakDual.isCompact_closedBall (0 : StrongDual ℂ A) 2).of_isClosed_subset
    stateSet_isClosed (fun φ hφ => ?_)
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
  exact (ContinuousLinearMap.opNorm_le_iff (by norm_num)).mpr fun a => stateSet.norm_apply_le hφ a

/-! ### Pure states (Krein–Milman)

`stateSet A` is convex (`stateSet_convex`) and weak-*-compact (`stateSet_isCompact`). Krein–Milman
is stated over `ℝ`, so we equip the **complex** weak dual with its **real**
locally-convex structure:
`ℝ` acts through `ℂ`, keeping scalar multiplication weak-*-continuous, and the weak topology is
`ℝ`-locally-convex (`WeakBilin.locallyConvexSpace`). The two instances below supply exactly the
real-LCTVS structure on `WeakDual ℂ A` that Mathlib does not register for a complex weak dual; with
them, the extreme points of the state space — the **pure states** — are nonempty. -/

/-- `ℝ` acts continuously on the complex weak dual (through `ℂ`). Built from weak-* evaluation
continuity so it agrees with the canonical `ℝ`-module structure Krein–Milman infers. -/
instance : ContinuousSMul ℝ (WeakDual ℂ A) where
  continuous_smul := by
    apply WeakDual.continuous_of_continuous_eval
    intro y
    exact continuous_fst.smul ((WeakDual.eval_continuous y).comp continuous_snd)

/-- The complex weak dual is locally convex over `ℝ` — the restrict-scalars instance for the weak
topology (`WeakBilin.locallyConvexSpace`), routed through the `WeakBilin` form of `WeakDual`. -/
instance : LocallyConvexSpace ℝ (WeakDual ℂ A) :=
  inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℂ A)))

/-- The **pure states** of `A`: the extreme points of the (weak-*-compact, convex) state space. -/
def pureStateSet (A : Type*) [CStarAlgebra A] : Set (WeakDual ℂ A) :=
  (stateSet A).extremePoints ℝ

/-- A pure state is a state. -/
lemma pureStateSet_subset_stateSet : pureStateSet A ⊆ stateSet A :=
  fun _ hφ => hφ.1

/-- **Pure states exist (Krein–Milman).** A nonempty weak-*-compact convex state space has an
extreme point. -/
theorem pureStateSet_nonempty (hne : (stateSet A).Nonempty) : (pureStateSet A).Nonempty :=
  stateSet_isCompact.extremePoints_nonempty hne

/-- Whenever a concrete state exists, so does a pure state. -/
theorem pureStateSet_nonempty_of_state (ω : State A) : (pureStateSet A).Nonempty :=
  pureStateSet_nonempty ⟨ω.toWeakDual, ω.toWeakDual_mem⟩

end Spectra.KMS
