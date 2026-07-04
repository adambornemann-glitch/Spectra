# `Spectra/Operator/` — Unbounded Operators on Hilbert Space

**Status: sorry-free, axiom-clean, every headline result gated in [`AxiomCheck.lean`](../../AxiomCheck.lean).**
This is the base of the whole library. Every other tower — the spectral theorem, Stone's
theorem, functional calculus, Tomita–Takesaki modular theory, the Dirac operator, the hydrogen
atom's spectrum — is built on the self-adjointness and domain facts proved here. Nothing in this
directory is postulated: closability, the double adjoint, deficiency indices, and von Neumann's
self-adjoint extension theorem are all *proved*, not bundled.

> **Ground truth is `lake build`.** This README is a map. Names below are real as of writing but
> verify against source before citing them elsewhere.

Twenty-nine files, six layers:

```
Spectra/Operator/
├── Symmetric.lean, SelfAdjoint.lean, Bounded.lean,          -- the basic hierarchy: symmetric ⊂
│   BoundedFactorAdjoint.lean, Closable.lean,                -- self-adjoint, boundedness, closability,
│   AdjointClosure.lean                                      -- the double adjoint T** = T̄
├── EssentialSelfAdjointness.lean, CommonCoreSum.lean,        -- essential self-adjointness, sums on a
│   Composite.lean, CanonicalCommutation.lean,               -- common domain, Kato–Rellich, and why
│   KatoRellich.lean                                         -- unboundedness is unavoidable
├── DeficiencySubspace.lean, DeficiencyIndex.lean,            -- deficiency indices n±(A) and the
│   VonNeumannExtension.lean, VonNeumannExtensionSelfAdjoint.lean, -- extension A_V along a unitary
│   SelfAdjointExtension.lean, SelfAdjointExtensionClassification.lean, -- N₊ ≃ N₋
│   UniqueSelfAdjointExtension.lean
├── VonNeumannFormula.lean, SymmetricExtension.lean,          -- the first & second von Neumann
│   SymmetricExtensionClassification.lean,                   -- formulas; the full classification of
│   SymmetricExtensionSelfAdjointness.lean,                  -- ALL symmetric extensions, not just
│   SymmetricExtensionClosedness.lean                        -- self-adjoint ones
├── ConjugationCriterion.lean, WeylCriterion.lean,            -- a sufficient existence criterion, a
│   NumericalRange.lean                                      -- PVM-free spectral criterion, numerical range
└── Unitary/                                                 -- bounded unitary/normal-operator toolkit
    ├── Basic.lean, Bridge.lean, Powers.lean                 -- feeding CayleyTransform/ and PositiveDefinite/
```

---

## Layer 1 — the basic hierarchy: symmetric, self-adjoint, bounded, closable

| File | Content |
|---|---|
| `Symmetric.lean` | `SymmetricOperator` — a densely-defined `LinearPMap` with formal self-adjointness `⟪Aψ,φ⟫ = ⟪ψ,Aφ⟫` on the domain (no domain-equality requirement); commutator/anticommutator at a point, `expectation`, `variance` — the substrate for the Robertson/Schrödinger uncertainty inequalities. |
| `SelfAdjoint.lean` | `SelfAdjointOperator` — bundles a `LinearPMap` with a genuine `IsSelfAdjoint` proof (`A† = A`, including `D(A) = D(A†)`); density and formal symmetry are derived, not assumed; `toSymmetricOperator` gives free reuse of everything in `Symmetric.lean`. |
| `Bounded.lean` | `IsBounded` (domain = `⊤`); the **Hellinger–Toeplitz theorem** — an everywhere-defined symmetric operator on a complete space is automatically bounded (`boundedExtension`) — plus its converse `ofBounded`; separately, the general **bounded ⟺ closed** loop for any `LinearPMap` (`isClosed_of_bound_of_isClosed_domain`, `exists_bound_of_isClosed_of_domain_eq_top`, via Mathlib's closed graph theorem). |
| `BoundedFactorAdjoint.lean` | `(b∘A)⋆ = A⋆∘b⁻¹` for a unitary factor `b : F ≃ₗᵢ[ℂ] G` composed with a densely-defined `A` — the true, provable special case of the composite-adjoint law (the general unbounded-times-unbounded `(AB)⋆ = B⋆A⋆` is false). The Stage-1 substrate for the Tomita–Takesaki polar-uniqueness build (`S = W Δ^{½} ⟹ S⋆ = Δ^{½} W⁻¹`). |
| `Closable.lean` | Bridges Mathlib's generic closability (`LinearPMap.IsClosable`, `.closure`, `.HasCore`) with its Hilbert-adjoint theory: any operator with a densely-defined formal adjoint is closable (`isClosable_of_isFormalAdjoint`), closed operators equal their own closure, `closure ≤ adjoint` for symmetric operators, and `HasCore` = topological density of the restricted graph. |
| `AdjointClosure.lean` | `adjoint` depends only on the topological closure of the graph (`closure_adjoint_eq_adjoint`); the **double adjoint theorem** `T** = T̄` (Reed–Simon VIII.1(b)); upgrades `Closable.lean`'s sufficiency-only criterion to a full **iff**: `isClosable_iff_dense_adjoint_domain`. The submodule-level adjoint machinery this needs (order-reversal, closure commuting with equivalence) is, per its own docstring, not currently in Mathlib. |

## Layer 2 — essential self-adjointness, sums, and Kato–Rellich

| File | Content |
|---|---|
| `EssentialSelfAdjointness.lean` | `IsEssentiallySelfAdjoint` (closure is self-adjoint); the **dense-range von Neumann criterion** — symmetric + densely-defined + `ran(B±i)` merely *dense* (not onto) already forces `B.closure` self-adjoint. |
| `CommonCoreSum.lean` | `sumOp A B` (`A+B` on `A.domain ⊓ B.domain`); sum of symmetric operators is symmetric; the Kato–Rellich companion reduces essential self-adjointness of a sum to a directly-verified deficiency condition — deliberately *not* automatic (Nelson's counterexample). |
| `Composite.lean` | `compositeSymmetric` — the composite `∑ vᵢ Oᵢ` from a family of `SymmetricOperator`s on a common invariant domain, bundled as `QuantumRLDData` (the quantum analogue of a regular statistical model); covariance, commutator, and variance of the composite decompose bilinearly, giving a genuine Riemannian (Fisher) metric and a genuine symplectic form on tangent vectors. Deliberately stated at `SymmetricOperator`, not `SelfAdjointOperator`, generality — sums of self-adjoint operators can fail even essential self-adjointness. The one file here that reaches outward into `QuantumMechanics/` and `InformationGeometry/`. |
| `CanonicalCommutation.lean` | The **Wielandt–Wintner theorem**: no pair of *bounded* self-adjoint operators on a nontrivial Hilbert space can satisfy the canonical commutation relation `AB - BA = i·1` (`not_ccr_of_bounded`) — the structural reason quantum mechanics forces unbounded operators in the first place. |
| `KatoRellich.lean` | The **Kato–Rellich theorem** (`kato_rellich`): if `A` is self-adjoint and `V` is symmetric on `D(A)` with relative bound `a < 1`, then `A+V` is self-adjoint on the *same* domain — via von Neumann's surjectivity criterion at a tunable purely-imaginary height and a Neumann-series inversion of `1 + V(A-z)⁻¹`. Corollaries: bounded perturbations, relative-bound-zero (the hydrogen atom's entry point via Hardy's inequality), and a Stone-theorem corollary for the perturbed generator's unitary group. The largest file in the directory (670 lines). |

## Layer 3 — deficiency indices & von Neumann's extension theorem (N1–N4)

| File | Content |
|---|---|
| `DeficiencySubspace.lean` | The deficiency subspaces `N₊(A) = ker(A*-i)`, `N₋(A) = ker(A*+i)` of any densely-defined `A` (no symmetry needed), and their orthogonal characterizations `N₊(A) = ran(A+i)ᗮ`, `N₋(A) = ran(A-i)ᗮ`. |
| `DeficiencyIndex.lean` | Deficiency indices `n±(A) := Module.rank ℂ N±(A)`; vanish for self-adjoint `A`; the cross-lane equivalence `deficiencySubspacesBot_iff_denseRange_addSub` unifying this layer with Layer 2's dense-range criterion. |
| `VonNeumannExtension.lean` | The extension `A_V = A*│_{D(A) ⊔ ran(1-V)}` along a unitary deficiency identification `V : N₊(A) ≃ₗᵢ[ℂ] N₋(A)`: domain density, `A ≤ A_V`, and the explicit action formula `A_V(x+η-Vη) = Ax + iη + iVη`. |
| `VonNeumannExtensionSelfAdjoint.lean` | `A_V` is symmetric **unconditionally** (a boundary-form computation), self-adjoint when `A` is closed (**N3**, via surjectivity of `A_V ± i`), and essentially self-adjoint with **no** closedness hypothesis at all. |
| `SelfAdjointExtension.lean` | Von Neumann's extension theorem (**N4**): a symmetric densely-defined `A` admits a self-adjoint extension iff `N₊(A) ≃ₗᵢ N₋(A)` (`exists_le_isSelfAdjoint_iff_nonempty_deficiencyEquiv`), via the Cayley transform of the extension. |
| `SelfAdjointExtensionClassification.lean` | Von Neumann's **classification** (**N3d**): `V ↦ A_V` is a *bijection* between deficiency unitaries and self-adjoint extensions of a closed symmetric `A` — completeness (every extension is *some* `A_V`) plus injectivity, packaged as `selfAdjointExtensionEquiv`. |
| `UniqueSelfAdjointExtension.lean` | The classical characterization closing the loop: essential self-adjointness ⟺ **exactly one** self-adjoint extension (`isEssentiallySelfAdjoint_iff_existsUnique_le_isSelfAdjoint`), plus the trichotomy — non-essentially-self-adjoint but extendable operators have *at least two*. |

## Layer 4 — the von Neumann formulas & the full symmetric-extension classification

| File | Content |
|---|---|
| `VonNeumannFormula.lean` | The **first von Neumann formula**: for closed symmetric densely-defined `A`, `D(A*) = D(A) ⊔ N₊(A) ⊔ N₋(A)` — graph-orthogonal, unique (`∃!`), with `A*(ψ+η+ξ) = Aψ + iη - iξ`; general (non-closed) version via `A.closure`. |
| `SymmetricExtension.lean` | Generalizes the extension from a *unitary* deficiency map to a **partial isometry** `V` on a submodule `F ≤ N₊(A)`: `A_V = A*│_{D(A) ⊔ (1-V)F}`, symmetric via a boundary-form identity — no unitarity needed. |
| `SymmetricExtensionClassification.lean` | The **second von Neumann formula**: for closed symmetric `A`, *every* symmetric extension `B ≥ A` is exactly some partial `A_V` — `F` and `V` are read off `D(B)` and recovered uniquely (`exists_eq_vonNeumannExtensionOn`). |
| `SymmetricExtensionSelfAdjointness.lean` | Exactly which partial extensions `A_V` are self-adjoint: `IsSelfAdjoint A_V ↔ F = N₊(A) ∧ Surjective V` — a full deficiency unitary, and nothing less (`vonNeumannExtensionOn_isSelfAdjoint_iff`). |
| `SymmetricExtensionClosedness.lean` | Exactly which partial extensions are **closed**: `A_V.IsClosed ↔ IsClosed F`, via a graph-Pythagoras identity transferring Cauchy sequences across the defect decomposition (`vonNeumannExtensionOn_isClosed_iff`). |

Together, Layers 3–4 give the **complete textbook picture** (Reed–Simon X.1–X.2, Akhiezer–Glazman §80):
symmetric extensions ↔ partial isometries on subspaces of `N₊(A)` · self-adjoint ↔ full unitaries ·
closed ↔ closed `F`.

## Layer 5 — conjugation criterion, Weyl's criterion, numerical range

| File | Content |
|---|---|
| `ConjugationCriterion.lean` | **Von Neumann's conjugation criterion** (Reed–Simon X.3): a symmetric operator commuting with an antiunitary conjugation admits self-adjoint extensions — the conjugation swaps `N₊ ↔ N₋`, restricted to an antiunitary equivalence, then transported to a *unitary* one via the general Hilbert-basis-transport lemma `nonempty_linearIsometryEquiv_of_antiunitary`. Covers Schrödinger operators with real potentials. |
| `WeylCriterion.lean` | **Weyl's criterion** for the *full* spectrum: `λ ∈ spectrum A ⟺ ∃` an approximate eigensequence (`mem_spectrum_iff_exists_weylSequence`). PVM-free — built on the parametric bounded-below core in `Resolvent/BoundedBelow.lean` (closed range from a closed graph + lower bound, dense range at real `λ` for self-adjoint `A`), dropping the former `SpectralTheory.Essential` dependency entirely. |
| `NumericalRange.lean` | The numerical range `W(A) = {⟪ψ,Aψ⟫ : ‖ψ‖=1, ψ ∈ D(A)}`; real for symmetric `A`; the sharp bound `dist(z,W(A))·‖ψ‖ ≤ ‖(A-z)ψ‖`; injectivity plus closed and dense range of `A-z` whenever `z ∉ closure(W(A))` — feeds `Resolvent.spectrum_subset_closure_numericalRange`, the marquee "spectrum ⊆ closure(numerical range)" theorem. |

## `Unitary/` — bounded unitary & normal-operator toolkit

| File | Content |
|---|---|
| `Basic.lean` | A bespoke bounded-operator `Unitary` predicate (`U*U = UU* = 1`) and `IsNormal`; unitaries preserve inner products/norms and are bijective; normal + bounded-below ⟹ surjective/invertible; the approximate-eigenvalue criterion for non-invertibility of `U - w`. |
| `Bridge.lean` | Bridges the bespoke `Unitary` predicate to **Mathlib's** `unitary` submonoid membership in the C\*-algebra `H →L[ℂ] H`, unlocking Mathlib's continuous functional calculus (`cfc`) on Cayley transforms of self-adjoint operators. |
| `Powers.lean` | Integer powers `U^n : ℤ` (monoid power for `n ≥ 0`, adjoint powers for `n < 0`); the group law `U^(m+n) = U^m·U^n`; the inner-product shift `⟪U^m ψ, U^n ψ⟫ = ⟪ψ, U^(n-m) ψ⟫` for unitary `U` — feeds `PositiveDefinite/Unitary.lean`'s autocorrelation sequence (the Bochner/Herglotz route). |

---

## How the pieces connect

```
   SymmetricOperator / SelfAdjointOperator                    Symmetric.lean, SelfAdjoint.lean
                    │  closability, T** = T̄, closed ⟺ bounded
                    ▼
   IsEssentiallySelfAdjoint, sums, Kato–Rellich perturbation   Layer 2
                    │  deficiency subspaces N±(A)
                    ▼
   von Neumann extension A_V  (unitary V : N₊ ≃ₗᵢ N₋)          Layer 3
                    │  existence (N4) · classification (N3d) · essential-SA ⟺ unique extension
                    ▼
   first von Neumann formula  D(A*) = D(A) ⊔ N₊ ⊔ N₋           VonNeumannFormula.lean
                    │  generalize V to a partial isometry on F ≤ N₊
                    ▼
   second von Neumann formula: EVERY symmetric extension       SymmetricExtension* family
   is some A_V — plus which A_V are self-adjoint / closed      ◀── the textbook classification, complete
                    │
                    ├──▶ ConjugationCriterion / WeylCriterion / NumericalRange (Layer 5)
                    │        — existence shortcuts and spectrum-location tools consumed by
                    │          Schrödinger operators (hydrogen atom) and Resolvent/
                    │
                    └──▶ Unitary/ — the bounded-operator side, feeding the Cayley transform
                             (Spectra/CayleyTransform/) which reduces self-adjoint A to a unitary
                             V and reproves the spectral theorem via Riesz–Markov, entirely
                             independently of the Yosida–Hille route in Spectra/YosidaHille/
```

`Composite.lean` and `CanonicalCommutation.lean` are the two files that face outward toward
physics rather than downward toward the spectral theorem: the former builds the Fisher-metric /
symplectic-form structure consumed by `Spectra/InformationGeometry/`, the latter (Wielandt–Wintner)
explains *why* this whole directory has to exist — bounded self-adjoint operators cannot satisfy
the canonical commutation relation, so quantum mechanics forces the unbounded theory built here.

## What's deliberately out of scope here

- **The spectral theorem, Stone's theorem, and functional calculus** — `Spectra/Resolvent/`,
  `Spectra/YosidaHille/`, `Spectra/CayleyTransform/`, `Spectra/SpectralTheory/`. This directory
  supplies the self-adjointness and domain facts those consume; it does not itself construct a
  spectral measure.
- **The essential spectrum and Weyl's theorem on compact perturbations** —
  `Spectra/SpectralTheory/Essential/`. Distinct from the *pointwise* Weyl criterion in
  `WeylCriterion.lean` above (approximate eigensequences vs. compact-perturbation invariance of
  `σ_ess`), despite the shared name.
- **The Cayley transform itself** (`V = (A-i)(A+i)⁻¹`, its Möbius shadow, Riesz–Markov) —
  `Spectra/CayleyTransform/`. `Unitary/Bridge.lean` here is the plumbing that lets that transform's
  *output* participate in Mathlib's `cfc`, not the transform's construction.
- **Tomita–Takesaki's `Δ`, `J`, and the modular flow** — `Spectra/Modular/TomitaTakesaki/`.
  `BoundedFactorAdjoint.lean`'s composite-adjoint law is a substrate that project consumes, built
  here because it is a general operator-theory fact, not a modular-theory-specific one.

## Mathlib gaps this directory could upstream

1. **The full von Neumann self-adjoint extension theory** — deficiency indices, the extension
   theorem (N1–N4), the classification bijection `V ↦ A_V`, and both von Neumann formulas. Mathlib
   has `LinearPMap` adjoint/closability primitives but nothing past them; this is a textbook chapter
   (Reed–Simon X.1–X.3) with no Mathlib analogue at all.
2. **Submodule-level adjoint machinery** — order-reversal, closure-commutes-with-equivalence,
   orthogonal-complement-ignores-closure (`AdjointClosure.lean`'s own docstring calls this out).
3. **The Kato–Rellich perturbation theorem** and the bounded ⟺ closed graph loop for general
   `LinearPMap`s (`Bounded.lean`).
4. **The bounded-factor composite-adjoint law** `(b∘A)⋆ = A⋆∘b⁻¹` — per `BoundedFactorAdjoint.lean`'s
   own docstring, absent from both Mathlib and the rest of Spectra before this file.
5. **The Wielandt–Wintner theorem** (no bounded CCR pair) — a short, classical, and apparently
   unformalized result explaining why unbounded operator theory is unavoidable in quantum mechanics.
