/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# Finite lattice gauge theory: the combinatorial substrate

This file sets up the **combinatorics** of lattice gauge theory on a finite periodic lattice — the
sites, directions, links, plaquettes, and configuration space — with no analysis, measure theory, or
gauge-group structure beyond a bare group.  It is the substrate on which the Wilson action
(`S(U) = (2/g₀²) Σₚ Re tr(1 − U(p))`), the finite-volume Gibbs measure, and reflection positivity
are later built (Lanes L2/L3, R).

There is (per the Yang–Mills survey) **no prior lattice-gauge combinatorics anywhere in Mathlib or
Spectra**, so the design here is from scratch.  Conventions:

* **Lattice = discrete torus.** `Site d L = Fin d → ZMod L` — a `d`-dimensional periodic lattice
  with `L` sites per direction. Periodicity (`ZMod L`, not `Fin L`) is what makes a one-step shift a
  total, invertible map with no boundary special-casing — the standard choice for a finite-volume
  lattice gauge theory. It is a finite abelian group under pointwise addition.
* **Links are oriented.** A `Link` is a `base` site together with a `dir`ection `μ : Fin d`; it
  joins `base` to `shift μ base = base + eμ`. The reverse traversal carries the inverse group
  element (this is imposed by `plaquetteHolonomy`, not by the `Link` type).
* **A configuration** `Config d L G = Link d L → G` assigns a group element to every oriented link
  (the "link variables" `U`).
* **Plaquettes** are elementary oriented squares `Plaquette`: a `base` and an ordered pair of
  distinct directions `dir₁ < dir₂`. The `<` counts each geometric square once. The **plaquette
  holonomy** `plaquetteHolonomy U p` is the ordered product of the four link variables around the
  square, `U₁ · U₂ · U₃⁻¹ · U₄⁻¹` — the elementary Wilson loop.

## Main definitions

* `Spectra.GaugeTheory.Lattice.Site` / `Link` / `Plaquette` / `Config`
* `Spectra.GaugeTheory.Lattice.unitVec`, `shift`, `shiftEquiv`
* `Spectra.GaugeTheory.Lattice.plaquetteHolonomy`

## Tags

lattice gauge theory, Wilson loop, plaquette, link variable, gauge configuration, torus
-/

namespace Spectra.GaugeTheory.Lattice

/-! ## §1  Sites of the periodic lattice -/

/-- **Sites** of the `d`-dimensional periodic lattice with `L` sites per direction: the discrete
torus `(ℤ/Lℤ)^d`.  A finite abelian group under pointwise addition. -/
abbrev Site (d L : ℕ) : Type := Fin d → ZMod L

variable {d L : ℕ}

/-- The **unit lattice vector** `eμ` in direction `μ`: `1` in coordinate `μ`, `0` elsewhere. -/
def unitVec (μ : Fin d) : Site d L := Pi.single μ 1

/-- **One-step shift** `x ↦ x + eμ` in direction `μ`. -/
def shift (μ : Fin d) (x : Site d L) : Site d L := x + unitVec μ

/-- Shifting in a fixed direction is a bijection of sites (translation on the torus). -/
def shiftEquiv (μ : Fin d) : Site d L ≃ Site d L := Equiv.addRight (unitVec μ)

@[simp] lemma shiftEquiv_apply (μ : Fin d) (x : Site d L) : shiftEquiv μ x = shift μ x := rfl

@[simp] lemma shift_shiftEquiv_symm (μ : Fin d) (x : Site d L) :
    shift μ ((shiftEquiv μ).symm x) = x := (shiftEquiv μ).apply_symm_apply x

/-- The torus has `L ^ d` sites. -/
lemma card_site [NeZero L] : Fintype.card (Site d L) = L ^ d := by
  simp [Site, ZMod.card]

/-! ## §2  Links and configurations -/

/-- An **oriented link** of the lattice: the edge from `base` to `shift dir base`. -/
structure Link (d L : ℕ) where
  /-- The base site of the link. -/
  base : Site d L
  /-- The direction the link points in. -/
  dir : Fin d
deriving DecidableEq

/-- `Link d L` is equivalent to `Site d L × Fin d`. -/
@[simps] def linkEquivProd : Link d L ≃ Site d L × Fin d where
  toFun l := (l.base, l.dir)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [NeZero L] : Fintype (Link d L) := Fintype.ofEquiv _ linkEquivProd.symm

/-- A **gauge (link) configuration**: a group element on every oriented link — the link variables
`U`. An `abbrev` (not a `def`) so the function-space instances — `Fintype`, `MeasurableSpace`,
`TopologicalSpace` — transfer transparently to the configuration space. -/
abbrev Config (d L : ℕ) (G : Type*) : Type _ := Link d L → G

/-! ## §3  Plaquettes and the plaquette holonomy -/

/-- A **plaquette**: an elementary oriented square, based at `base`, spanning the `dir₁`-`dir₂`
plane with `dir₁ < dir₂` (so each geometric square is counted once). -/
structure Plaquette (d L : ℕ) where
  /-- The base corner of the plaquette. -/
  base : Site d L
  /-- The first (smaller) direction spanning the square. -/
  dir₁ : Fin d
  /-- The second (larger) direction spanning the square. -/
  dir₂ : Fin d
  /-- The directions are ordered, `dir₁ < dir₂`, counting each square once. -/
  lt : dir₁ < dir₂
deriving DecidableEq

/-- A plaquette is the same data as a base site plus an ordered pair of distinct directions. -/
@[simps] def plaquetteEquivSubtype :
    Plaquette d L ≃ {p : Site d L × Fin d × Fin d // p.2.1 < p.2.2} where
  toFun p := ⟨(p.base, p.dir₁, p.dir₂), p.lt⟩
  invFun q := ⟨q.1.1, q.1.2.1, q.1.2.2, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [NeZero L] : Fintype (Plaquette d L) := Fintype.ofEquiv _ plaquetteEquivSubtype.symm

/-- The **plaquette holonomy** `U_P`: the ordered product of the four link variables traversed
around the elementary square — up direction `dir₁`, then up `dir₂`, then back down `dir₁`, then back
down `dir₂` (the last two reversed, hence inverted). This is the elementary Wilson loop; the Wilson
action (Lane L2) is built from `Re tr (1 − U_P)`. -/
def plaquetteHolonomy {G : Type*} [Group G] (U : Config d L G) (p : Plaquette d L) : G :=
  U ⟨p.base, p.dir₁⟩ * U ⟨shift p.dir₁ p.base, p.dir₂⟩
    * (U ⟨shift p.dir₂ p.base, p.dir₁⟩)⁻¹ * (U ⟨p.base, p.dir₂⟩)⁻¹

/-- The trivial (all-identity) configuration has trivial holonomy on every plaquette. -/
@[simp] lemma plaquetteHolonomy_one {G : Type*} [Group G] (p : Plaquette d L) :
    plaquetteHolonomy (fun _ => (1 : G)) p = 1 := by
  simp [plaquetteHolonomy]

end Spectra.GaugeTheory.Lattice
