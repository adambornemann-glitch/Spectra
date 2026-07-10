/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.KMS.StateTopology
import Spectra.Modular.KMS.Equivalence
/-!
# Extremal KMS States

The KMS states at a fixed `(α, β)` form a **weak-*-compact convex** subset of the state space, so by
Krein–Milman they have extreme points — the **extremal KMS states**.

The crucial point is *which* characterization of the KMS condition to use. The strip condition
(`IsKMSState`: existence of analytic strip functions) is not manifestly weak-*-closed. The
**imaginary-time** characterization (A3, `isKMSState_iff_imaginaryTime`) is: a state is KMS iff
`φ(a · σ_{iβ}(b)) = φ(b · a)` for every analytic element `b`, and each such equation is a
weak-*-closed condition (an equality of weak-*-continuous evaluations). So the KMS-state set is a
closed subset of the compact `stateSet A`, and it is convex (the imaginary-time equations are affine
in `φ`).

## Main statements

* `Spectra.KMS.kmsStateSet` — the KMS states in the weak dual (imaginary-time form).
* `Spectra.KMS.kmsStateSet_isClosed`, `_convex`, `_isCompact`.
* `Spectra.KMS.IsKMSState.toWeakDual_mem_kmsStateSet` — a concrete KMS state lands in it.
* `Spectra.KMS.extremalKMSStateSet_nonempty` — extremal KMS states exist (Krein–Milman).
-/

open Complex Set

namespace Spectra.KMS

variable {A : Type*} [CStarAlgebra A] {α : Dynamics A} {β : ℝ}

/-- The `(a, b)`-imaginary-time condition `φ(a · σ_{iβ}(b)) = φ(b · a)` as a subset of the weak
dual, for an analytic element `b`. Weak-*-closed (equality of continuous evaluations). -/
def imaginaryTimeCond (α : Dynamics A) (β : ℝ) (a b : A) (hb : α.IsAnalyticElement b) :
    Set (WeakDual ℂ A) :=
  {φ : WeakDual ℂ A | φ (a * α.sigma hb ((β : ℂ) * I)) = φ (b * a)}

/-- The **KMS states** at `(α, β)`, realized in the weak dual: the states `φ` satisfying the
imaginary-time KMS identity `φ(a · σ_{iβ}(b)) = φ(b · a)` for every `a` and every analytic element
`b`. By A3 (`isKMSState_iff_imaginaryTime`) this is exactly the set of KMS states. -/
def kmsStateSet (α : Dynamics A) (β : ℝ) : Set (WeakDual ℂ A) :=
  stateSet A ∩ ⋂ (a : A) (b : A) (hb : α.IsAnalyticElement b), imaginaryTimeCond α β a b hb

/-- The KMS-state set is contained in the state space. -/
lemma kmsStateSet_subset_stateSet : kmsStateSet α β ⊆ stateSet A := fun _ hφ => hφ.1

/-- Each imaginary-time condition is weak-*-closed. -/
lemma isClosed_imaginaryTimeCond (a b : A) (hb : α.IsAnalyticElement b) :
    IsClosed (imaginaryTimeCond α β a b hb) := by
  have hset : imaginaryTimeCond α β a b hb
      = (fun φ : WeakDual ℂ A => φ (a * α.sigma hb ((β : ℂ) * I)) - φ (b * a)) ⁻¹' {0} := by
    ext φ; simp [imaginaryTimeCond, sub_eq_zero]
  rw [hset]
  exact isClosed_singleton.preimage
    ((WeakDual.eval_continuous _).sub (WeakDual.eval_continuous _))

/-- The KMS-state set is weak-*-closed (intersection of the closed `stateSet` with the closed
imaginary-time conditions). -/
lemma kmsStateSet_isClosed : IsClosed (kmsStateSet α β) :=
  stateSet_isClosed.inter (isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_iInter fun hb => isClosed_imaginaryTimeCond a b hb)

/-- Each imaginary-time condition is convex (it is affine in `φ`). -/
lemma convex_imaginaryTimeCond (a b : A) (hb : α.IsAnalyticElement b) :
    Convex ℝ (imaginaryTimeCond α β a b hb) := by
  intro φ hφ ψ hψ s t _ _ _
  change (s • φ + t • ψ) (a * α.sigma hb ((β : ℂ) * I)) = (s • φ + t • ψ) (b * a)
  have hx : (s • φ + t • ψ) (a * α.sigma hb ((β : ℂ) * I))
      = s • φ (a * α.sigma hb ((β : ℂ) * I)) + t • ψ (a * α.sigma hb ((β : ℂ) * I)) := rfl
  have hy : (s • φ + t • ψ) (b * a) = s • φ (b * a) + t • ψ (b * a) := rfl
  rw [hx, hy, hφ, hψ]

/-- The KMS-state set is convex (intersection of convex sets). (Currently unused.) -/
lemma kmsStateSet_convex : Convex ℝ (kmsStateSet α β) :=
  stateSet_convex.inter (convex_iInter fun a => convex_iInter fun b =>
    convex_iInter fun hb => convex_imaginaryTimeCond a b hb)

/-- The KMS-state set is weak-*-compact (closed subset of the compact state space). -/
lemma kmsStateSet_isCompact : IsCompact (kmsStateSet α β) :=
  stateSet_isCompact.of_isClosed_subset kmsStateSet_isClosed kmsStateSet_subset_stateSet

/-- A concrete KMS state lands in the weak-dual KMS-state set (its imaginary-time identities hold by
A2, `IsKMSState.imaginaryTime`). -/
lemma IsKMSState.toWeakDual_mem_kmsStateSet {ω : State A} (hβ : 0 < β)
    (hkms : IsKMSState ω α β) : ω.toWeakDual ∈ kmsStateSet α β := by
  refine ⟨ω.toWeakDual_mem, ?_⟩
  simp only [Set.mem_iInter]
  intro a b hb
  change ω.toWeakDual (a * α.sigma hb ((β : ℂ) * I)) = ω.toWeakDual (b * a)
  rw [State.toWeakDual_apply, State.toWeakDual_apply]
  exact hkms.imaginaryTime hβ hb a

/-- The **extremal KMS states** at `(α, β)`: the extreme points of the KMS-state set. -/
def extremalKMSStateSet (α : Dynamics A) (β : ℝ) : Set (WeakDual ℂ A) :=
  (kmsStateSet α β).extremePoints ℝ

/-- An extremal KMS state is a KMS state. (Currently unused.) -/
lemma extremalKMSStateSet_subset : extremalKMSStateSet α β ⊆ kmsStateSet α β :=
  fun _ hφ => hφ.1

/-- **Extremal KMS states exist (Krein–Milman).** If there is a KMS state, the (nonempty,
weak-*-compact, convex) KMS-state set has an extreme point. -/
theorem extremalKMSStateSet_nonempty (hne : (kmsStateSet α β).Nonempty) :
    (extremalKMSStateSet α β).Nonempty :=
  kmsStateSet_isCompact.extremePoints_nonempty hne

/-- Whenever a concrete KMS state exists, so does an extremal KMS state. -/
theorem extremalKMSStateSet_nonempty_of_kmsState {ω : State A} (hβ : 0 < β)
    (hkms : IsKMSState ω α β) : (extremalKMSStateSet α β).Nonempty :=
  extremalKMSStateSet_nonempty ⟨ω.toWeakDual, hkms.toWeakDual_mem_kmsStateSet hβ⟩

end Spectra.KMS
