/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Krein.Basic
import Spectra.Spaces.Tensor.PowerCongr
import Spectra.Spaces.HilbertSum.Congr
import Spectra.Spaces.Fock.Basic
import Spectra.Spaces.Fock.BoseFermi
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The Krein–Fock lift: second quantization of a fundamental symmetry

A fundamental symmetry `J` on the one-particle space `H` (`Spectra/Spaces/Krein/Basic.lean`)
lifts to a fundamental symmetry `Γ(J)` on the full Fock space `fullFock 𝕜 H`: the Fock space
over a Krein space is a Krein space.

This is the **Gupta–Bleuler mechanism** (Gupta 1950, Bleuler 1950): covariant quantization of
the electromagnetic field forces an indefinite metric, and that metric lives on Fock space
precisely by second-quantizing the one-particle fundamental symmetry (which flips the sign of
the timelike photon polarization). The sector lifts moreover **preserve the bosonic and
fermionic sectors** (`powerLift_mem_symPower`, `powerLift_mem_altPower`, proved via
`congr_permUnitary`), so the Gupta–Bleuler metric on the bosonic (photonic) subspace is
literally the restriction of the sector Krein form. See Mintchev, *Quantisation in indefinite
metric*, and Bognár, *Indefinite Inner Product Spaces*, for the general theory.

`Γ(J)` is built sector-wise: `J`, bundled as the unitary `J.isometryEquiv`, is lifted to each
`n`-particle sector by the tensor-power congruence `HilbertTensorPower.congr`
(`Spectra/Spaces/Tensor/PowerCongr.lean`), and the sector lifts assemble diagonally through
`LinearIsometryEquiv.lpCongrRight` (`Spectra/Spaces/HilbertSum/Congr.lean`). Self-adjointness
of the lift is free from involutivity plus unitarity. Only the second quantization of a
*unitary involution* is constructed here; the functor `Γ` on general operators is out of
scope.

## Main definitions

* `Spectra.FundamentalSymmetry.powerLift` — the sector lift `Γₙ(J)`, a unitary involution of
  the `n`-particle space `HilbertTensorPower 𝕜 n H`.
* `Spectra.FundamentalSymmetry.powerSymmetry` — `Γₙ(J)` packaged as a fundamental symmetry:
  each `n`-particle sector over a Krein space is a Krein space.
* `Spectra.FundamentalSymmetry.fockLiftEquiv` — `Γ(J)` as a unitary of `fullFock 𝕜 H`.
* `Spectra.FundamentalSymmetry.fockSymmetry` — **the Krein–Fock lift**: `Γ(J)` as a
  fundamental symmetry on `fullFock 𝕜 H`.

## Main results

* `powerLift_tprod` — `Γₙ(J)` acts slotwise on pure tensors: `Γₙ(J)(⨂ₜ xᵢ) = ⨂ₜ J xᵢ`.
* `powerLift_mem_symPower` / `powerLift_mem_altPower` — `Γₙ(J)` preserves the bosonic and
  fermionic sectors.
* `powerLift_powerLift`, `fockLiftEquiv_fockLiftEquiv` — the lifts are involutions.
* `inner_powerLift_left`, `inner_fockLiftEquiv_left` — the lifts are self-adjoint.
* `kreinInner_fockSymmetry` — the Fock Krein form decomposes over sectors:
  `[ξ, η] = ∑' n, ⟪Γₙ(J) (ξ n), η n⟫`, the sector-wise Gupta–Bleuler pairing; equivalently
  `[ξ, η] = ∑' n, [ξ n, η n]ₙ` (`kreinInner_fockSymmetry_eq_tsum_kreinInner`).
* `fockSymmetry_id_apply` — the trivial symmetry lifts to the trivial symmetry.
-/

noncomputable section

open scoped TensorProduct

namespace Spectra

namespace FundamentalSymmetry

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H] (J : FundamentalSymmetry 𝕜 H)

/-! ## The sector lift `Γₙ(J)` -/

/-- The **sector lift** `Γₙ(J)`: the fundamental symmetry `J`, bundled as the unitary
`J.isometryEquiv`, acting slotwise on the `n`-particle space via the tensor-power
congruence. -/
def powerLift (n : ℕ) : HilbertTensorPower 𝕜 n H ≃ₗᵢ[𝕜] HilbertTensorPower 𝕜 n H :=
  HilbertTensorPower.congr J.isometryEquiv

theorem powerLift_def (n : ℕ) :
    J.powerLift n = HilbertTensorPower.congr J.isometryEquiv := rfl

/-- The sector lift acts slotwise on pure tensors: `Γₙ(J)(⨂ₜ xᵢ) = ⨂ₜ J xᵢ`. -/
@[simp]
theorem powerLift_tprod (n : ℕ) (x : Fin n → H) :
    J.powerLift n (HilbertTensorPower.tprod 𝕜 x)
      = HilbertTensorPower.tprod 𝕜 fun i => J (x i) := by
  rw [powerLift_def, HilbertTensorPower.congr_tprod]
  rfl

/-- The sector lift is an involution: `Γₙ(J) (Γₙ(J) ξ) = ξ`. -/
theorem powerLift_powerLift (n : ℕ) (ξ : HilbertTensorPower 𝕜 n H) :
    J.powerLift n (J.powerLift n ξ) = ξ := by
  rw [powerLift_def, HilbertTensorPower.congr_congr, J.isometryEquiv_trans_self,
    HilbertTensorPower.congr_refl]
  rfl

/-- The sector lift is self-adjoint: `⟪Γₙ(J) ξ, η⟫ = ⟪ξ, Γₙ(J) η⟫` — for free, from
involutivity plus unitarity. -/
theorem inner_powerLift_left (n : ℕ) (ξ η : HilbertTensorPower 𝕜 n H) :
    inner 𝕜 (J.powerLift n ξ) η = inner 𝕜 ξ (J.powerLift n η) := by
  rw [powerLift_def, HilbertTensorPower.inner_congr_left, J.isometryEquiv_symm]

/-- Each `n`-particle sector over a Krein space is a Krein space: the sector lift `Γₙ(J)`,
packaged as a fundamental symmetry on `HilbertTensorPower 𝕜 n H`. -/
def powerSymmetry (n : ℕ) : FundamentalSymmetry 𝕜 (HilbertTensorPower 𝕜 n H) where
  toContinuousLinearMap := (J.powerLift n).toLinearIsometry.toContinuousLinearMap
  isSelfAdjoint' :=
    LinearMap.IsSymmetric.isSelfAdjoint fun ξ η => J.inner_powerLift_left n ξ η
  comp_self := ContinuousLinearMap.ext fun ξ => J.powerLift_powerLift n ξ

/-- The sector fundamental symmetry acts as the sector lift. -/
@[simp]
theorem powerSymmetry_apply (n : ℕ) (ξ : HilbertTensorPower 𝕜 n H) :
    J.powerSymmetry n ξ = J.powerLift n ξ := rfl

/-- The sector Krein form is the Hilbert pairing against the sector lift. -/
theorem kreinInner_powerSymmetry (n : ℕ) (ξ η : HilbertTensorPower 𝕜 n H) :
    (J.powerSymmetry n).kreinInner ξ η = inner 𝕜 (J.powerLift n ξ) η := rfl

/-! ## Sector preservation: `Γₙ(J)` respects the Bose/Fermi split -/

/-- `Γₙ(J)` preserves the **bosonic sector**: slotwise maps commute with the permutation
unitaries, so permutation-invariant states stay permutation-invariant. -/
theorem powerLift_mem_symPower {n : ℕ} {ξ : HilbertTensorPower 𝕜 n H}
    (hξ : ξ ∈ HilbertTensorPower.symPower 𝕜 n H) :
    J.powerLift n ξ ∈ HilbertTensorPower.symPower 𝕜 n H := by
  rw [HilbertTensorPower.mem_symPower_iff_forall] at hξ ⊢
  intro σ
  rw [powerLift_def, ← HilbertTensorPower.congr_permUnitary, hξ σ]

/-- `Γₙ(J)` preserves the **fermionic sector**: sign covariance survives the slotwise
map. -/
theorem powerLift_mem_altPower {n : ℕ} {ξ : HilbertTensorPower 𝕜 n H}
    (hξ : ξ ∈ HilbertTensorPower.altPower 𝕜 n H) :
    J.powerLift n ξ ∈ HilbertTensorPower.altPower 𝕜 n H := by
  rw [HilbertTensorPower.mem_altPower_iff_forall] at hξ ⊢
  intro σ
  rw [powerLift_def, ← HilbertTensorPower.congr_permUnitary, hξ σ, map_smul]

/-! ## The Fock lift `Γ(J)` -/

/-- The **Fock lift** `Γ(J)` as a unitary of the full Fock space: the sector lifts
`Γₙ(J)` acting diagonally on the Hilbert sum of the `n`-particle sectors. -/
def fockLiftEquiv : fullFock 𝕜 H ≃ₗᵢ[𝕜] fullFock 𝕜 H :=
  LinearIsometryEquiv.lpCongrRight 2 fun n => J.powerLift n

/-- The Fock lift acts sector-wise: `(Γ(J) ξ) n = Γₙ(J) (ξ n)`. -/
@[simp]
theorem fockLiftEquiv_apply (ξ : fullFock 𝕜 H) (n : ℕ) :
    J.fockLiftEquiv ξ n = J.powerLift n (ξ n) := rfl

/-- The Fock lift is an involution: `Γ(J) (Γ(J) ξ) = ξ`. -/
theorem fockLiftEquiv_fockLiftEquiv (ξ : fullFock 𝕜 H) :
    J.fockLiftEquiv (J.fockLiftEquiv ξ) = ξ :=
  lp.ext <| funext fun n => J.powerLift_powerLift n (ξ n)

/-- The Fock lift is self-adjoint: `⟪Γ(J) ξ, η⟫ = ⟪ξ, Γ(J) η⟫` — for free, from
involutivity plus unitarity. -/
theorem inner_fockLiftEquiv_left (ξ η : fullFock 𝕜 H) :
    inner 𝕜 (J.fockLiftEquiv ξ) η = inner 𝕜 ξ (J.fockLiftEquiv η) := by
  conv_lhs => rw [← J.fockLiftEquiv_fockLiftEquiv η]
  exact LinearIsometryEquiv.inner_map_map _ ξ (J.fockLiftEquiv η)

/-! ## The Krein–Fock lift -/

/-- **The Krein–Fock lift** `Γ(J)`: a fundamental symmetry on the one-particle space
second-quantizes to a fundamental symmetry on the full Fock space, exhibiting
`fullFock 𝕜 H` as a Krein space. This is the indefinite metric of Gupta–Bleuler
quantization of the electromagnetic field. -/
def fockSymmetry : FundamentalSymmetry 𝕜 (fullFock 𝕜 H) where
  toContinuousLinearMap := J.fockLiftEquiv.toLinearIsometry.toContinuousLinearMap
  isSelfAdjoint' :=
    LinearMap.IsSymmetric.isSelfAdjoint fun ξ η => J.inner_fockLiftEquiv_left ξ η
  comp_self := ContinuousLinearMap.ext fun ξ => J.fockLiftEquiv_fockLiftEquiv ξ

/-- The Krein–Fock lift acts sector-wise: `(Γ(J) ξ) n = Γₙ(J) (ξ n)`. -/
@[simp]
theorem fockSymmetry_apply (ξ : fullFock 𝕜 H) (n : ℕ) :
    J.fockSymmetry ξ n = J.powerLift n (ξ n) := rfl

/-- The Krein–Fock lift acts as the Fock lift unitary. -/
theorem fockSymmetry_coe (ξ : fullFock 𝕜 H) : J.fockSymmetry ξ = J.fockLiftEquiv ξ := rfl

/-- **Sector decomposition of the Fock Krein form** (the sector-wise Gupta–Bleuler
pairing): `[ξ, η] = ∑' n, ⟪Γₙ(J) (ξ n), η n⟫`. -/
theorem kreinInner_fockSymmetry (ξ η : fullFock 𝕜 H) :
    J.fockSymmetry.kreinInner ξ η = ∑' n, inner 𝕜 (J.powerLift n (ξ n)) (η n) := by
  rw [kreinInner_def, lp.inner_eq_tsum]
  rfl

/-- The Fock Krein form is the sum of the sector Krein forms: `[ξ, η] = ∑' n, [ξ n, η n]ₙ`. -/
theorem kreinInner_fockSymmetry_eq_tsum_kreinInner (ξ η : fullFock 𝕜 H) :
    J.fockSymmetry.kreinInner ξ η
      = ∑' n, (J.powerSymmetry n).kreinInner (ξ n) (η n) := by
  rw [J.kreinInner_fockSymmetry ξ η]
  rfl

/-! ## Naturality: the trivial symmetry lifts to the trivial symmetry -/

/-- The identity fundamental symmetry bundles to the identity unitary. -/
theorem isometryEquiv_id :
    (FundamentalSymmetry.id 𝕜 H).isometryEquiv = LinearIsometryEquiv.refl 𝕜 H :=
  LinearIsometryEquiv.ext fun _ => rfl

/-- The sector lift of the identity symmetry is the identity. -/
theorem powerLift_id (n : ℕ) (ξ : HilbertTensorPower 𝕜 n H) :
    (FundamentalSymmetry.id 𝕜 H).powerLift n ξ = ξ := by
  rw [powerLift_def, isometryEquiv_id, HilbertTensorPower.congr_refl]
  rfl

/-- The Krein–Fock lift of the identity symmetry acts as the identity: the trivial Krein
structure on `H` induces the trivial Krein structure on `fullFock 𝕜 H`. -/
theorem fockSymmetry_id_apply (ξ : fullFock 𝕜 H) :
    (FundamentalSymmetry.id 𝕜 H).fockSymmetry ξ = ξ :=
  lp.ext <| funext fun n => powerLift_id n (ξ n)

end FundamentalSymmetry

-- Sanity: the Fock space over a Krein space is a Krein space, and its Krein form restricts
-- on each sector as the sector Krein form.
section Sanity

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H] (J : FundamentalSymmetry 𝕜 H)

example : FundamentalSymmetry 𝕜 (fullFock 𝕜 H) := J.fockSymmetry

example (n : ℕ) : FundamentalSymmetry 𝕜 (HilbertTensorPower 𝕜 n H) := J.powerSymmetry n

example (ξ : fullFock 𝕜 H) : J.fockSymmetry (J.fockSymmetry ξ) = ξ :=
  J.fockSymmetry.apply_apply ξ

end Sanity

end Spectra
