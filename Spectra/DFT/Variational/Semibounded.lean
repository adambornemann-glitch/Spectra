/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.NumericalRangeSpectrum
import Spectra.Resolvent.Meromorphic
import Spectra.Operator.NumericalRange
import Spectra.Operator.SelfAdjoint

/-!
# Semibounded operators and the bottom of the spectrum

The variational substrate for Density Functional Theory (lane **S3**): a self-adjoint operator `A`
is **semibounded below** by `c` when its energy expectation obeys `c‖ψ‖² ≤ Re⟪ψ, Aψ⟫` on the whole
domain — the abstract shape of "the electronic Hamiltonian is bounded below". The payoff is that the
spectrum then lies in `[c, ∞)`, so it is bounded below and its infimum `E₀ = inf σ(A)`
— the **bottom of the spectrum** — is a genuine real number, not the junk `sInf ∅ = 0`.

Nothing here is DFT-specific; it is a reusable statement about semibounded self-adjoint operators
(any ground-state / bottom-of-spectrum consumer can use it — cf. the Yang–Mills "mass gap" framing).

## Main definitions

* `Spectra.DFT.IsSemibounded` — `c‖ψ‖² ≤ Re⟪ψ, Aψ⟫` on `dom A`.
* `Spectra.DFT.groundStateEnergy` — `E₀ A := sInf (spectrum A)`.

## Main results

* `numericalRange_subset_image_Ici` — for symmetric semibounded `A`, `W(A) ⊆ {(r:ℂ) | c ≤ r}`.
* `spectrum_subset_Ici` — for self-adjoint semibounded `A`, `σ(A) ⊆ [c, ∞)` (via the marquee theorem
  `Spectra.Resolvent.spectrum_subset_closure_numericalRange`).
* `bddBelow_spectrum` — `σ(A)` is bounded below.
* `le_groundStateEnergy` / `spectrum_subset_Ici_groundStateEnergy` — `c ≤ E₀ A` and
  `σ(A) ⊆ [E₀ A, ∞)`.

## Implementation notes

`groundStateEnergy` uses `sInf`, whose junk value on an empty/unbounded-below set is `0`. Every
statement that reads `E₀` therefore carries either `IsSemibounded` (for boundedness below) or an
explicit `(spectrum A).Nonempty` hypothesis — never let a bare `sInf (spectrum A)` escape unguarded.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I & IV*][reed1980].
-/

open scoped InnerProductSpace ComplexConjugate
open Spectra.Operator Spectra.Resolvent

namespace Spectra.DFT

-- The numerical-range facts (below) need no completeness; the spectrum facts (further down) do.
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `A` is **semibounded below** by the constant `c` when its energy expectation dominates
`c‖ψ‖²` on the whole domain: `c‖ψ‖² ≤ Re⟪ψ, Aψ⟫`. This is the abstract "bounded below" shape. -/
def IsSemibounded (A : H →ₗ.[ℂ] H) (c : ℝ) : Prop :=
  ∀ ψ : A.domain, c * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), A ψ⟫_ℂ).re

/-- Every point of the numerical range of a semibounded operator has real part `≥ c`
(unit vectors turn `c‖ψ‖²` into `c`). -/
lemma numericalRange_re_ge {A : H →ₗ.[ℂ] H} {c : ℝ} (hb : IsSemibounded A c)
    {z : ℂ} (hz : z ∈ numericalRange A) : c ≤ z.re := by
  obtain ⟨ψ, hψ1, rfl⟩ := hz
  have h := hb ψ
  rw [hψ1] at h
  simpa using h

/-- For a symmetric semibounded operator, the numerical range sits inside the real ray `[c, ∞)`
(embedded in `ℂ`): `W(A) ⊆ {(r : ℂ) | c ≤ r}`. -/
lemma numericalRange_subset_image_Ici {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    {c : ℝ} (hb : IsSemibounded A c) :
    numericalRange A ⊆ (↑) '' (Set.Ici c) := by
  intro z hz
  have hre : c ≤ z.re := numericalRange_re_ge hb hz
  obtain ⟨r, rfl⟩ := numericalRange_subset_range_ofReal hsym hz
  exact ⟨r, by simpa using hre, rfl⟩

/-- The closure of the numerical range of a symmetric semibounded operator still sits in `[c, ∞)`,
since that real ray is closed in `ℂ`. -/
lemma closure_numericalRange_subset_image_Ici {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    {c : ℝ} (hb : IsSemibounded A c) :
    closure (numericalRange A) ⊆ (↑) '' (Set.Ici c) :=
  closure_minimal (numericalRange_subset_image_Ici hsym hb)
    (Complex.isUniformEmbedding_ofReal.isClosedEmbedding.isClosedMap _ isClosed_Ici)

-- The spectrum lives on complete spaces: `spectrum`, `resolventSet`, and `IsSelfAdjoint` all need
-- it.
variable [CompleteSpace H]

/-- **Bottom of the spectrum, containment form.** The spectrum of a self-adjoint semibounded
operator lies in `[c, ∞)`. This is the abstract "no energy below `c`" fact, obtained from the
marquee theorem `spectrum A ⊆ closure (W(A))` and `W(A) ⊆ [c, ∞)`. -/
theorem spectrum_subset_Ici {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hne : (numericalRange A).Nonempty) {c : ℝ} (hb : IsSemibounded A c) :
    spectrum A ⊆ Set.Ici c := by
  intro lam hlam
  have hcl : (lam : ℂ) ∈ closure (numericalRange A) :=
    spectrum_subset_closure_numericalRange hA hne lam hlam
  have hsym : A.IsFormalAdjoint A := isFormalAdjoint_self_of_isSelfAdjoint hA
  obtain ⟨r, hr_mem, hr_eq⟩ := closure_numericalRange_subset_image_Ici hsym hb hcl
  have hrl : r = lam := by exact_mod_cast hr_eq
  rw [Set.mem_Ici, ← hrl]
  exact hr_mem

/-- The spectrum of a self-adjoint semibounded operator is bounded below. -/
theorem bddBelow_spectrum {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hne : (numericalRange A).Nonempty) {c : ℝ} (hb : IsSemibounded A c) :
    BddBelow (spectrum A) :=
  ⟨c, fun _ hlam => spectrum_subset_Ici hA hne hb hlam⟩

/-- The **bottom of the spectrum** `E₀ = inf σ(A)`. Junk (`= 0`) if `σ(A)` is empty or unbounded
below; always used under `IsSemibounded` + a nonempty-spectrum guard (see the module docstring). -/
noncomputable def groundStateEnergy (A : H →ₗ.[ℂ] H) : ℝ := sInf (spectrum A)

/-- The semibound `c` lower-bounds the ground-state energy (given a nonempty spectrum). -/
theorem le_groundStateEnergy {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hne : (numericalRange A).Nonempty) {c : ℝ} (hb : IsSemibounded A c)
    (hSpec : (spectrum A).Nonempty) :
    c ≤ groundStateEnergy A :=
  le_csInf hSpec (fun _ hlam => spectrum_subset_Ici hA hne hb hlam)

/-- **Bottom of the spectrum, `E₀` form.** The spectrum lies in `[E₀ A, ∞)`. -/
theorem spectrum_subset_Ici_groundStateEnergy {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hne : (numericalRange A).Nonempty) {c : ℝ} (hb : IsSemibounded A c) :
    spectrum A ⊆ Set.Ici (groundStateEnergy A) :=
  fun _ hlam => csInf_le (bddBelow_spectrum hA hne hb) hlam

/-- **The bottom of the spectrum is attained:** `E₀ A ∈ σ(A)`. The spectrum is closed (its
complement `Complex.ofReal ⁻¹' resolventSet A` is open), nonempty, and bounded below, so its
infimum is a member — `E₀` is a genuine spectral value, not merely an infimum. -/
theorem groundStateEnergy_mem_spectrum {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hne : (numericalRange A).Nonempty) {c : ℝ} (hb : IsSemibounded A c)
    (hSpec : (spectrum A).Nonempty) :
    groundStateEnergy A ∈ spectrum A := by
  have hopen : IsOpen (Complex.ofReal ⁻¹' resolventSet A) :=
    (isOpen_resolventSet A).preimage Complex.continuous_ofReal
  exact hopen.isClosed_compl.csInf_mem hSpec (bddBelow_spectrum hA hne hb)

end Spectra.DFT
