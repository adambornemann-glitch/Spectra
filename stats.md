# Library Statistics: `Spectra`

**Root:** `/Users/augustusthwack/Documents/Spectra/Spectra`

**Files:** 43 `.lean` files

## Summary

| Metric | Count |
|--------|------:|
| Total raw lines | 8,409 |
| Lines of code (no block comments, no blanks, no `--`-only) | 6,297 |
| Blank lines | 931 |
| Comment-only lines (`--`) | 80 |
| Lines inside `/- -/` block comments | 1,411 |

## Declarations

| Kind | Count |
|------|------:|
| `theorem` | 56 |
| `lemma` | 168 |
| `def` | 48 |
| `structure` | 6 |
| `instance` | 5 |
| **Proofs (theorem + lemma)** | **224** |
| **Definitions (def + abbrev)** | **48** |
| **Axioms** | **0** |
| **Types (structure + class + inductive)** | **6** |

## File Listing

| # | File | Raw Lines | Code Lines | Thm+Lem | Def | Axiom |
|--:|------|----------:|----------:|--------:|----:|------:|
| 1 | `Basic.lean` | 1 | 1 | 0 | 1 | 0 |
| 2 | `Uncertainty.lean` | 11 | 4 | 0 | 0 | 0 |
| 3 | `Uncertainty/Heisenberg.lean` | 108 | 36 | 3 | 1 | 0 |
| 4 | `Uncertainty/SchrodingerRobertson.lean` | 323 | 219 | 13 | 1 | 0 |
| 5 | `Uncertainty/SymmetricOp.lean` | 293 | 147 | 14 | 15 | 0 |
| 6 | `Uncertainty/UnboundedOb.lean` | 128 | 37 | 4 | 2 | 0 |
| 7 | `UnitaryEvolution.lean` | 8 | 2 | 0 | 0 | 0 |
| 8 | `UnitaryEvolution/BochnerIntegration/Basic.lean` | 315 | 255 | 10 | 0 | 0 |
| 9 | `UnitaryEvolution/BochnerIntegration/Domain.lean` | 477 | 399 | 16 | 5 | 0 |
| 10 | `UnitaryEvolution/BochnerIntegration/Limits.lean` | 31 | 3 | 0 | 0 | 0 |
| 11 | `UnitaryEvolution/BochnerIntegration/Limits/Helpers.lean` | 222 | 187 | 4 | 0 | 0 |
| 12 | `UnitaryEvolution/BochnerIntegration/Limits/Minus.lean` | 555 | 522 | 3 | 0 | 0 |
| 13 | `UnitaryEvolution/BochnerIntegration/Limits/Plus.lean` | 343 | 310 | 3 | 0 | 0 |
| 14 | `UnitaryEvolution/BochnerIntegration/Resolvent.lean` | 146 | 87 | 8 | 2 | 0 |
| 15 | `UnitaryEvolution/Ehrenfest.lean` | 94 | 53 | 3 | 0 | 0 |
| 16 | `UnitaryEvolution/Generator.lean` | 252 | 160 | 9 | 1 | 0 |
| 17 | `UnitaryEvolution/Resolvent/Analytic.lean` | 148 | 107 | 1 | 0 | 0 |
| 18 | `UnitaryEvolution/Resolvent/Basic.lean` | 235 | 167 | 11 | 5 | 0 |
| 19 | `UnitaryEvolution/Resolvent/Core.lean` | 239 | 205 | 1 | 1 | 0 |
| 20 | `UnitaryEvolution/Resolvent/Identities.lean` | 169 | 131 | 2 | 1 | 0 |
| 21 | `UnitaryEvolution/Resolvent/LowerBound.lean` | 111 | 77 | 1 | 0 | 0 |
| 22 | `UnitaryEvolution/Resolvent/NormExpansion.lean` | 180 | 109 | 10 | 0 | 0 |
| 23 | `UnitaryEvolution/Resolvent/Range/ClosedRange.lean` | 239 | 202 | 3 | 0 | 0 |
| 24 | `UnitaryEvolution/Resolvent/Range/Orthogonal.lean` | 239 | 197 | 4 | 0 | 0 |
| 25 | `UnitaryEvolution/Resolvent/Range/Surjectivity.lean` | 149 | 100 | 3 | 1 | 0 |
| 26 | `UnitaryEvolution/Resolvent/SpecialCases.lean` | 325 | 263 | 11 | 2 | 0 |
| 27 | `UnitaryEvolution/Schrodinger.lean` | 108 | 72 | 3 | 0 | 0 |
| 28 | `UnitaryEvolution/Stone.lean` | 209 | 139 | 7 | 0 | 0 |
| 29 | `UnitaryEvolution/Yosida/Basic.lean` | 85 | 49 | 8 | 0 | 0 |
| 30 | `UnitaryEvolution/Yosida/Bounds.lean` | 108 | 81 | 3 | 0 | 0 |
| 31 | `UnitaryEvolution/Yosida/Convergence/Approximants.lean` | 232 | 188 | 7 | 0 | 0 |
| 32 | `UnitaryEvolution/Yosida/Convergence/JNegOperator.lean` | 171 | 139 | 3 | 0 | 0 |
| 33 | `UnitaryEvolution/Yosida/Convergence/JOperator.lean` | 162 | 122 | 3 | 0 | 0 |
| 34 | `UnitaryEvolution/Yosida/Defs.lean` | 95 | 42 | 1 | 7 | 0 |
| 35 | `UnitaryEvolution/Yosida/Duhamel/Commutation.lean` | 82 | 53 | 3 | 0 | 0 |
| 36 | `UnitaryEvolution/Yosida/Duhamel/Estimate.lean` | 227 | 189 | 4 | 0 | 0 |
| 37 | `UnitaryEvolution/Yosida/Duhamel/Formula.lean` | 274 | 230 | 5 | 1 | 0 |
| 38 | `UnitaryEvolution/Yosida/Duhamel/Helpers.lean` | 153 | 101 | 6 | 0 | 0 |
| 39 | `UnitaryEvolution/Yosida/ExpBounded/Adjoint.lean` | 166 | 125 | 6 | 0 | 0 |
| 40 | `UnitaryEvolution/Yosida/ExpBounded/Basic.lean` | 246 | 187 | 11 | 1 | 0 |
| 41 | `UnitaryEvolution/Yosida/ExpBounded/Unitary.lean` | 214 | 171 | 8 | 0 | 0 |
| 42 | `UnitaryEvolution/Yosida/Exponential.lean` | 436 | 367 | 7 | 1 | 0 |
| 43 | `UnitaryEvolution/Yosida/Symmetry.lean` | 100 | 62 | 2 | 0 | 0 |

## Top 20 Files by Code Lines

| # | File | Code Lines |
|--:|------|----------:|
| 1 | `UnitaryEvolution/BochnerIntegration/Limits/Minus.lean` | 522 |
| 2 | `UnitaryEvolution/BochnerIntegration/Domain.lean` | 399 |
| 3 | `UnitaryEvolution/Yosida/Exponential.lean` | 367 |
| 4 | `UnitaryEvolution/BochnerIntegration/Limits/Plus.lean` | 310 |
| 5 | `UnitaryEvolution/Resolvent/SpecialCases.lean` | 263 |
| 6 | `UnitaryEvolution/BochnerIntegration/Basic.lean` | 255 |
| 7 | `UnitaryEvolution/Yosida/Duhamel/Formula.lean` | 230 |
| 8 | `Uncertainty/SchrodingerRobertson.lean` | 219 |
| 9 | `UnitaryEvolution/Resolvent/Core.lean` | 205 |
| 10 | `UnitaryEvolution/Resolvent/Range/ClosedRange.lean` | 202 |
| 11 | `UnitaryEvolution/Resolvent/Range/Orthogonal.lean` | 197 |
| 12 | `UnitaryEvolution/Yosida/Duhamel/Estimate.lean` | 189 |
| 13 | `UnitaryEvolution/Yosida/Convergence/Approximants.lean` | 188 |
| 14 | `UnitaryEvolution/BochnerIntegration/Limits/Helpers.lean` | 187 |
| 15 | `UnitaryEvolution/Yosida/ExpBounded/Basic.lean` | 187 |
| 16 | `UnitaryEvolution/Yosida/ExpBounded/Unitary.lean` | 171 |
| 17 | `UnitaryEvolution/Resolvent/Basic.lean` | 167 |
| 18 | `UnitaryEvolution/Generator.lean` | 160 |
| 19 | `Uncertainty/SymmetricOp.lean` | 147 |
| 20 | `UnitaryEvolution/Stone.lean` | 139 |

## Top 20 Files by Proof Count (theorem + lemma)

| # | File | Proofs |
|--:|------|-------:|
| 1 | `UnitaryEvolution/BochnerIntegration/Domain.lean` | 16 |
| 2 | `Uncertainty/SymmetricOp.lean` | 14 |
| 3 | `Uncertainty/SchrodingerRobertson.lean` | 13 |
| 4 | `UnitaryEvolution/Resolvent/Basic.lean` | 11 |
| 5 | `UnitaryEvolution/Resolvent/SpecialCases.lean` | 11 |
| 6 | `UnitaryEvolution/Yosida/ExpBounded/Basic.lean` | 11 |
| 7 | `UnitaryEvolution/BochnerIntegration/Basic.lean` | 10 |
| 8 | `UnitaryEvolution/Resolvent/NormExpansion.lean` | 10 |
| 9 | `UnitaryEvolution/Generator.lean` | 9 |
| 10 | `UnitaryEvolution/BochnerIntegration/Resolvent.lean` | 8 |
| 11 | `UnitaryEvolution/Yosida/Basic.lean` | 8 |
| 12 | `UnitaryEvolution/Yosida/ExpBounded/Unitary.lean` | 8 |
| 13 | `UnitaryEvolution/Stone.lean` | 7 |
| 14 | `UnitaryEvolution/Yosida/Convergence/Approximants.lean` | 7 |
| 15 | `UnitaryEvolution/Yosida/Exponential.lean` | 7 |
| 16 | `UnitaryEvolution/Yosida/Duhamel/Helpers.lean` | 6 |
| 17 | `UnitaryEvolution/Yosida/ExpBounded/Adjoint.lean` | 6 |
| 18 | `UnitaryEvolution/Yosida/Duhamel/Formula.lean` | 5 |
| 19 | `Uncertainty/UnboundedOb.lean` | 4 |
| 20 | `UnitaryEvolution/BochnerIntegration/Limits/Helpers.lean` | 4 |
