/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Data.EReal.Operations

/-!
# The Legendre–Fenchel conjugate on a real pairing

The convex-analytic substrate for Density Functional Theory's Lieb formulation (lane **FD1**), and a
piece of shared infrastructure that mathlib lacks entirely (there is no Fenchel/Legendre conjugate,
biconjugate, or subgradient anywhere in the library, in this version). Given a real bilinear-style
pairing `p : X → Y → ℝ` and an extended-real-valued function `f : X → EReal`, the **convex
conjugate** is
`fenchelConj p f y = ⨆ x, (p x y - f x)`.
For DFT the pairing is `p n v = ∫ v·n` on densities × potentials, and the conjugate of the (negated)
ground-state energy is the Lieb functional; the library here is kept abstract.

## Main definitions

* `Spectra.fenchelConj` — `⨆ x, (p x y - f x)`, valued in `EReal`.
* `Spectra.biconjugate` — `⨆ y, (p x y - fenchelConj p f y)`, the Fenchel **biconjugate** `f**`
  (lane **FD2**); the largest closed-convex minorant of `f`.

## Main results

* `Spectra.sub_le_fenchelConj` — each affine piece `p x y - f x` lies below the conjugate.
* `Spectra.le_fenchelConj_add` — the **Fenchel–Young inequality** `p x y ≤ f x + fenchelConj p f y`,
  in the pointwise form valid wherever `f x` is finite.
* `Spectra.fenchelConj_antitone` — the conjugate is antitone in `f`.
* `Spectra.biconjugate_le` — `f** ≤ f`, **unconditional** (the always-true half of Fenchel–Moreau).
* `Spectra.fenchelConj_biconjugate` — the triple-conjugate collapse `f*** = f*`, **unconditional**.
* `Spectra.biconjugate_biconjugate` — the biconjugate is **idempotent**, `f**** = f**`.
* `Spectra.biconjugate_eq_of_eq_iSup_affine` — **Fenchel–Moreau**, conditional form: if `f` is a
  pointwise supremum of pairing-affine functions `x ↦ p x y - c` then `f** = f`.

## Implementation notes

**The value type is `EReal`, and the `⊤ + ⊥ = ⊥` bot-absorption convention is load-bearing.** The
naive *unconditional* additive Young inequality `p x y ≤ f x + fenchelConj p f y` is **false** at
any `x` where `f x ∈ {⊤, ⊥}`: if `f ≡ ⊤` then `fenchelConj = ⊥` and `⊤ + ⊥ = ⊥`, so the claim
reads `p x y ≤ ⊥`. This is not a Lean artifact — it is the honest behaviour of the extended reals —
so `le_fenchelConj_add` is stated *pointwise*, guarded by `f x ≠ ⊤ ∧ f x ≠ ⊥`, which is exactly the
regime where Young is meaningful (a proper-`f`, everywhere-valid corollary is a later addition
once a `Proper` predicate is introduced). No boundedness side-conditions are needed for the supremum
itself, since `EReal` is a `CompleteLinearOrder`.

**The Fenchel–Moreau split (FD2).** The biconjugate `f**` obeys `f** ≤ f` and the collapses
`f*** = f*`, `f**** = f**` **unconditionally** — no convexity, no topology, no Hahn–Banach — because
these are pure order/`iSup` facts about the extended reals. The *reverse* inequality `f ≤ f**`
(equivalently `f** = f`, i.e. `f` equals its own closed-convex envelope) is the genuine content of
Fenchel–Moreau and is a **research wall** (`⛔FEN`): the unconditional statement for a *proper convex
l.s.c.* `f` needs a weak-\* Hahn–Banach separation on the dual pair to manufacture enough affine
minorants, which mathlib does not provide for a general pairing. Rather than axiomatize it, we carry
the regularity as an **explicit hypothesis**: `biconjugate_eq_of_eq_iSup_affine` proves `f** = f`
whenever `f` is *given* as a pointwise supremum of pairing-affine functions `x ↦ p x y - c`. This is
not circular — it is a real structural assumption, and it is essentially the form in which DFT's
Lieb functional `F_L[n] = ⨆_v (E[v] - ∫v·n)` arises (lane LB3): with the pairing `p n v = ∫v·n`,
index by `v`, take slope `g v = -v` (matching `∫(-v)·n = -∫v·n`) and *real* intercept `c v = -E[v]`
(finite on the admissible potential class where `E[v] ∈ ℝ`), so `F_L = F_L**` — the closedness of
`F_L` — follows. The Hahn–Banach-powered unconditional version is deferred.
-/

namespace Spectra

variable {X Y : Type*}

/-- The **Legendre–Fenchel (convex) conjugate** of `f : X → EReal` with respect to a real pairing
`p : X → Y → ℝ`: `fenchelConj p f y = ⨆ x, (p x y - f x)`. -/
noncomputable def fenchelConj (p : X → Y → ℝ) (f : X → EReal) (y : Y) : EReal :=
  ⨆ x, ((p x y : EReal) - f x)

lemma fenchelConj_apply (p : X → Y → ℝ) (f : X → EReal) (y : Y) :
    fenchelConj p f y = ⨆ x, ((p x y : EReal) - f x) := rfl

/-- Each affine piece `p x y - f x` lies below the conjugate value at `y`. -/
theorem sub_le_fenchelConj (p : X → Y → ℝ) (f : X → EReal) (x : X) (y : Y) :
    (p x y : EReal) - f x ≤ fenchelConj p f y :=
  le_iSup (fun x' => ((p x' y : EReal) - f x')) x

/-- **The Fenchel–Young inequality**, pointwise form: `p x y ≤ f x + fenchelConj p f y` wherever
`f x` is finite. (The unconditional form is false at improper points; see the module docstring.) -/
theorem le_fenchelConj_add (p : X → Y → ℝ) (f : X → EReal) {x : X} (y : Y)
    (htop : f x ≠ ⊤) (hbot : f x ≠ ⊥) :
    (p x y : EReal) ≤ f x + fenchelConj p f y := by
  rw [add_comm (f x)]
  exact (EReal.sub_le_iff_le_add (Or.inl hbot) (Or.inl htop)).1 (sub_le_fenchelConj p f x y)

/-- The conjugate is **antitone** in `f`: a larger function has a smaller conjugate. -/
theorem fenchelConj_antitone (p : X → Y → ℝ) {f g : X → EReal} (h : f ≤ g) (y : Y) :
    fenchelConj p g y ≤ fenchelConj p f y := by
  refine iSup_le (fun x => ?_)
  calc (p x y : EReal) - g x
      ≤ (p x y : EReal) - f x := EReal.sub_le_sub (le_refl _) (h x)
    _ ≤ fenchelConj p f y := sub_le_fenchelConj p f x y

/-! ## The concave conjugate

For a *concave* `g : X → EReal` — the shape of the DFT ground-state energy `E[v]`, concave in the
external potential — the **concave conjugate** `g^⋆(y) = ⨆ x, (g x - p x y)` is the object Lieb's
universal functional is built from: `F_Lieb[n] = ⨆ v, (E[v] - ∫ v·n)`. Because the *pairing* term
`p x y` is a genuine real (never `⊤`/`⊥`), the concave Young inequality holds **unconditionally** —
no finiteness guard on `g` is needed, in contrast to the convex case above. -/

/-- The **concave conjugate** of `g : X → EReal` with respect to a real pairing `p`:
`concaveConj p g y = ⨆ x, (g x - p x y)`. This is the shape of the Lieb functional. -/
noncomputable def concaveConj (p : X → Y → ℝ) (g : X → EReal) (y : Y) : EReal :=
  ⨆ x, (g x - (p x y : EReal))

lemma concaveConj_apply (p : X → Y → ℝ) (g : X → EReal) (y : Y) :
    concaveConj p g y = ⨆ x, (g x - (p x y : EReal)) := rfl

/-- Each affine piece `g x - p x y` lies below the concave conjugate. -/
theorem sub_le_concaveConj (p : X → Y → ℝ) (g : X → EReal) (x : X) (y : Y) :
    g x - (p x y : EReal) ≤ concaveConj p g y :=
  le_iSup (fun x' => (g x' - (p x' y : EReal))) x

/-- **The concave Fenchel–Young inequality**, holding unconditionally:
`g x ≤ concaveConj p g y + p x y`. Unlike the convex case, the subtracted term is the real pairing
(never `⊤`/`⊥`), so no finiteness guard on `g` is needed. -/
theorem le_concaveConj_add (p : X → Y → ℝ) (g : X → EReal) (x : X) (y : Y) :
    g x ≤ concaveConj p g y + (p x y : EReal) :=
  (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).1
    (sub_le_concaveConj p g x y)

/-- The concave conjugate is **monotone** in `g`: a larger function has a larger concave
conjugate. -/
theorem concaveConj_mono (p : X → Y → ℝ) {g h : X → EReal} (hgh : g ≤ h) (y : Y) :
    concaveConj p g y ≤ concaveConj p h y := by
  refine iSup_le (fun x => ?_)
  exact le_trans (EReal.sub_le_sub (hgh x) (le_refl _)) (sub_le_concaveConj p h x y)

/-! ## The subdifferential and the Fenchel–Young equality

Lane **FD3** of the Fenchel library: the subgradient (subdifferential) of an `EReal`-valued function
`f` with respect to the real pairing `p`, and the theorem that `y` is a subgradient of `f` at `x`
**exactly when** the Fenchel–Young inequality holds with equality. In DFT this is the object behind
`n ∈ ∂E(v) ↔ n` is a ground-state density of `H_v` (lane LB5), where the possible emptiness of the
subdifferential is precisely `v`-representability.

The subgradient is the set of "slopes" `y` whose supporting affine minorant through `(x, f x)` lies
below `f`. The increment `p x' y - p x y` is formed **in `ℝ`** and only then coerced, so the
definition never involves an `EReal` `∞ - ∞`; the finiteness guard on `f x` is needed only for the
equality characterization (exactly as for `le_fenchelConj_add`). -/

/-- The **subdifferential** `∂f(x)` of `f : X → EReal` at `x` with respect to the real pairing `p`:
the set of `y : Y` whose affine minorant of slope `y` through `(x, f x)` supports `f` from below,
`f x + (p x' y - p x y) ≤ f x'` for all `x'`. The increment is a real subtraction (then coerced), so
no `EReal` `∞ - ∞` arises; the set may be **empty** (the honest encoding of
non-differentiability). -/
def subgradient (p : X → Y → ℝ) (f : X → EReal) (x : X) : Set Y :=
  { y | ∀ x', f x + ((p x' y - p x y : ℝ) : EReal) ≤ f x' }

@[simp] lemma mem_subgradient_iff {p : X → Y → ℝ} {f : X → EReal} {x : X} {y : Y} :
    y ∈ subgradient p f x ↔ ∀ x', f x + ((p x' y - p x y : ℝ) : EReal) ≤ f x' := Iff.rfl

/-- Rearrangement in `EReal`: `r + (a - b) ≤ c ↔ a - c ≤ b - r`, **unconditional** in `c` (the three
cases `c = ⊥, ↑s, ⊤` all hold despite the `∞`-arithmetic). The engine of the Fenchel–Young
equivalence, letting the `∞`-valued `c = f x'` pass through cleanly. -/
private theorem coe_add_coe_sub_le_iff (r a b : ℝ) (c : EReal) :
    (r : EReal) + ((a - b : ℝ) : EReal) ≤ c ↔ (a : EReal) - c ≤ (b : EReal) - (r : EReal) := by
  rw [← EReal.coe_add, ← EReal.coe_sub]
  induction c using EReal.rec with
  | bot =>
      refine iff_of_false (fun h => EReal.coe_ne_bot _ (le_bot_iff.mp h)) (fun h => ?_)
      rw [sub_eq_add_neg, EReal.neg_bot, EReal.add_top_of_ne_bot (EReal.coe_ne_bot a)] at h
      exact EReal.coe_ne_top _ (top_le_iff.mp h)
  | coe s =>
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
      constructor <;> intro h <;> linarith
  | top => simp

/-- **The Fenchel–Young equality (FD3).** At a point where `f x` is finite, `y` is a subgradient of
`f` at `x` if and only if the Fenchel–Young inequality `p x y ≤ f x + fenchelConj p f y` holds with
**equality**: `f x + fenchelConj p f y = p x y`. This is the exact-recovery characterization of the
subdifferential; the finiteness guard is essential (as for `le_fenchelConj_add`). -/
theorem mem_subgradient_iff_fenchelConj_add_eq (p : X → Y → ℝ) (f : X → EReal) {x : X} {y : Y}
    (htop : f x ≠ ⊤) (hbot : f x ≠ ⊥) :
    y ∈ subgradient p f x ↔ f x + fenchelConj p f y = (p x y : EReal) := by
  have hfx : ((f x).toReal : EReal) = f x := EReal.coe_toReal htop hbot
  set r : ℝ := (f x).toReal with _hrdef
  rw [mem_subgradient_iff]
  have hge : (p x y : EReal) - (r : EReal) ≤ fenchelConj p f y := by
    have h := sub_le_fenchelConj p f x y
    rwa [← hfx] at h
  constructor
  · intro hy
    rw [← hfx]
    have hle : fenchelConj p f y ≤ (p x y : EReal) - (r : EReal) := by
      rw [fenchelConj_apply]
      refine iSup_le (fun x' => ?_)
      exact (coe_add_coe_sub_le_iff r (p x' y) (p x y) (f x')).mp (by rw [hfx]; exact hy x')
    rw [le_antisymm hle hge, add_comm, EReal.sub_add_cancel]
  · intro heq x'
    rw [← hfx] at heq ⊢
    have hfstar : fenchelConj p f y = (p x y : EReal) - (r : EReal) := by
      rw [← heq, EReal.add_sub_cancel_left]
    refine (coe_add_coe_sub_le_iff r (p x' y) (p x y) (f x')).mpr ?_
    rw [← hfstar]
    exact sub_le_fenchelConj p f x' y

/-! ## The biconjugate and Fenchel–Moreau (FD2)

Lane **FD2** of the Fenchel library: the **biconjugate** `f**`, obtained by conjugating `f*` back
across the pairing, `f**(x) = ⨆ y, (p x y - f*(y))`. It is the largest closed-convex minorant of
`f`.

The three *unconditional* pillars — `biconjugate_le` (`f** ≤ f`), `fenchelConj_biconjugate`
(`f*** = f*`) and `biconjugate_biconjugate` (`f**** = f**`) — hold for **any** `f : X → EReal` with
no convexity, topology, or Hahn–Banach input; they are pure order facts, the honest completable core
of Fenchel–Moreau. The reverse `f ≤ f**` is the `⛔FEN` wall and is delivered *conditionally* on `f`
being a pointwise supremum of pairing-affine functions (`biconjugate_eq_of_eq_iSup_affine`); see the
module docstring. -/

/-- Extended-real identity for the biconjugate casework: `s - (s - a) ≤ a` for a real `s`, valued in
`EReal` and **unconditional** in `a` (the cases `a = ⊥, ↑r, ⊤` all hold under the `∞`-arithmetic —
at `⊥` both sides are `⊥`, at `⊤` both are `⊤`, at `↑r` both are `↑r`). The engine that turns
Fenchel–Young into `f** ≤ f`. -/
private theorem coe_sub_coe_sub_le (s : ℝ) (a : EReal) :
    (s : EReal) - ((s : EReal) - a) ≤ a := by
  induction a using EReal.rec with
  | bot => exact le_of_eq (by rw [EReal.coe_sub_bot, EReal.sub_top])
  | coe r => exact le_of_eq (by rw [← EReal.coe_sub, ← EReal.coe_sub, sub_sub_cancel])
  | top => exact le_of_eq (by rw [EReal.sub_top, EReal.coe_sub_bot])

/-- The **Fenchel biconjugate** `f**` of `f : X → EReal` with respect to a real pairing `p`:
`biconjugate p f x = ⨆ y, (p x y - fenchelConj p f y)`. Conjugating `f*` back across the pairing;
the largest closed-convex minorant of `f`. -/
noncomputable def biconjugate (p : X → Y → ℝ) (f : X → EReal) (x : X) : EReal :=
  ⨆ y, ((p x y : EReal) - fenchelConj p f y)

lemma biconjugate_apply (p : X → Y → ℝ) (f : X → EReal) (x : X) :
    biconjugate p f x = ⨆ y, ((p x y : EReal) - fenchelConj p f y) := rfl

/-- **`f** ≤ f`, unconditionally** — the always-true half of Fenchel–Moreau. Each affine piece
`p x y - f*(y)` of the biconjugate lies below `f x` by Fenchel–Young, with no finiteness or
convexity hypothesis (the `∞`-arithmetic is absorbed by `coe_sub_coe_sub_le`). -/
theorem biconjugate_le (p : X → Y → ℝ) (f : X → EReal) (x : X) :
    biconjugate p f x ≤ f x := by
  rw [biconjugate_apply]
  refine iSup_le (fun y => ?_)
  exact (EReal.sub_le_sub (le_refl _) (sub_le_fenchelConj p f x y)).trans
    (coe_sub_coe_sub_le (p x y) (f x))

/-- The biconjugate is **monotone** in `f`: a larger function has a larger biconjugate (two
antitone conjugations compose to a monotone map). -/
theorem biconjugate_mono (p : X → Y → ℝ) {f g : X → EReal} (h : f ≤ g) (x : X) :
    biconjugate p f x ≤ biconjugate p g x := by
  refine iSup_mono (fun y => ?_)
  exact EReal.sub_le_sub (le_refl _) (fenchelConj_antitone p h y)

/-- **The triple-conjugate collapse `f*** = f*`, unconditionally.** Conjugating the biconjugate
returns the conjugate — a hallmark identity that needs no convexity or Hahn–Banach. The `≥` half is
`fenchelConj_antitone` applied to `biconjugate_le`; the `≤` half is another Fenchel–Young
estimate. -/
theorem fenchelConj_biconjugate (p : X → Y → ℝ) (f : X → EReal) (y : Y) :
    fenchelConj p (biconjugate p f) y = fenchelConj p f y := by
  refine le_antisymm ?_ (fenchelConj_antitone p (fun x => biconjugate_le p f x) y)
  rw [fenchelConj_apply]
  refine iSup_le (fun x => ?_)
  refine (EReal.sub_le_sub (le_refl _) ?_).trans (coe_sub_coe_sub_le (p x y) (fenchelConj p f y))
  exact le_iSup (fun y' => ((p x y' : EReal) - fenchelConj p f y')) y

/-- The biconjugate is **idempotent**, `f**** = f**` — immediate from `f*** = f*`. -/
theorem biconjugate_biconjugate (p : X → Y → ℝ) (f : X → EReal) (x : X) :
    biconjugate p (biconjugate p f) x = biconjugate p f x := by
  simp only [biconjugate_apply, fenchelConj_biconjugate]

/-- **Fenchel–Moreau, conditional form.** If `f` is *given* as a pointwise supremum of
pairing-affine functions `x ↦ p x (g i) - c i`, then `f ≤ f**` (hence, with `biconjugate_le`,
`f** = f`). This is the honest, Hahn–Banach-free content of Fenchel–Moreau: the affine minorants are
supplied by hypothesis, which is essentially how the Lieb functional `F_L[n] = ⨆_v (E[v] - ∫v·n)` is
built (lane LB3; the fit uses slope `g v = -v` and real intercept `-E[v]`, so it needs `E[v]`
finite). -/
theorem le_biconjugate_of_eq_iSup_affine (p : X → Y → ℝ) (f : X → EReal) {ι : Type*}
    (g : ι → Y) (c : ι → ℝ)
    (hf : ∀ x, f x = ⨆ i, ((p x (g i) : EReal) - (c i : EReal))) (x : X) :
    f x ≤ biconjugate p f x := by
  rw [hf x]
  refine iSup_le (fun i => ?_)
  -- the `g i`-slope affine minorant is below the biconjugate; it suffices that `f*(g i) ≤ c i`.
  have hstar : fenchelConj p f (g i) ≤ (c i : EReal) := by
    rw [fenchelConj_apply]
    refine iSup_le (fun x' => ?_)
    refine (EReal.sub_le_sub (le_refl _) ?_).trans (coe_sub_coe_sub_le (p x' (g i)) (c i))
    rw [hf x']
    exact le_iSup (fun j => ((p x' (g j) : EReal) - (c j : EReal))) i
  refine le_trans (EReal.sub_le_sub (le_refl _) hstar) ?_
  exact le_iSup (fun y => ((p x y : EReal) - fenchelConj p f y)) (g i)

/-- **Fenchel–Moreau equality**, conditional form: for `f` a pointwise supremum of pairing-affine
functions, the biconjugate recovers `f` on the nose, `f** = f`. -/
theorem biconjugate_eq_of_eq_iSup_affine (p : X → Y → ℝ) (f : X → EReal) {ι : Type*}
    (g : ι → Y) (c : ι → ℝ)
    (hf : ∀ x, f x = ⨆ i, ((p x (g i) : EReal) - (c i : EReal))) :
    biconjugate p f = f :=
  funext fun x => le_antisymm (biconjugate_le p f x) (le_biconjugate_of_eq_iSup_affine p f g c hf x)

end Spectra
