"""Numeric checks for the M₂(M) matrix amplification (Spectra/Modular/Cocycle/).

`MatrixAmplification.lean` builds the 2×2 block algebra `M₂(M)` on `H ⊕ H`,
`blockOp a b c d = [[a,b],[c,d]]`, and proves the two centralizer identities
that make the amplification work:

  L1  `centralizer (M₂(M)) = M' ⊗ 1₂`   (scalar blocks with entry in M'),
  L2  `centralizer (M' ⊗ 1₂) = M₂(M')`.

L1 is the SUBTLE one: the commutant of `M₂(M)` is NOT `M₂(M')` — it is only the
*scalar* blocks `blockOp w 0 0 w`, `w ∈ M'`.  A formalization that mistakenly
claimed `M₂(M')` would be off by a factor of 4 in dimension.  We pin this down
on a genuinely proper von Neumann algebra.

Model.  `M = M_k(ℂ) ⊗ I_m` acting on `ℂ^n`, `n = k·m`.  Then `M' = I_k ⊗ M_m(ℂ)`,
`dim M = k²`, `dim M' = m²`.  With `k = m = 2` (n = 4):
  * `dim centralizer(M₂(M)) = m² = 4`   (scalar blocks M'⊗1₂),   NOT
  * `dim M₂(M') = 4·m² = 16`.
The commutant dimension is computed by solving `[X, g] = 0` over all generators
`g` (a null-space computation) — a route completely independent of the
closed-form `M'⊗1₂` description.
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nclib import linalg as la
from nclib.harness import check, check_le, finish

TOL = 1e-8


def blockOp(a, b, c, d):
    """[[a,b],[c,d]] as a 2n×2n matrix from four n×n blocks."""
    n = len(a)
    M = la.zeros(2 * n)
    for i in range(n):
        for j in range(n):
            M[i][j] = a[i][j]
            M[i][n + j] = b[i][j]
            M[n + i][j] = c[i][j]
            M[n + i][n + j] = d[i][j]
    return M


# --------------------------------------------------------------------------
# blockOp_comp:  composition is matrix multiplication
# --------------------------------------------------------------------------
n = 2
A = [la.hermitian_from_seed(n, 100 + i) for i in range(8)]
a, b, c, d, a2, b2, c2, d2 = A
# Route A: assemble the two 2n×2n block matrices and multiply them with the plain
# (block-formula-free) matmul — this does NOT use blockOp_comp.
lhs = la.matmul(blockOp(a, b, c, d), blockOp(a2, b2, c2, d2))
# Route B: the four block-product formulas asserted by blockOp_comp.
rhs = blockOp(la.add(la.matmul(a, a2), la.matmul(b, c2)),
              la.add(la.matmul(a, b2), la.matmul(b, d2)),
              la.add(la.matmul(c, a2), la.matmul(d, c2)),
              la.add(la.matmul(c, b2), la.matmul(d, d2)))
check("blockOp composition = matrix multiplication",
      "Cocycle/MatrixAmplification.lean:95 (blockOp_comp)",
      la.max_abs_diff(lhs, rhs), 0.0, abs_tol=TOL)

# blockOp_star: star(blockOp a b c d) = blockOp a⋆ c⋆ b⋆ d⋆ (conjugate transpose)
check("star(blockOp a b c d) = blockOp a⋆ c⋆ b⋆ d⋆",
      "Cocycle/MatrixAmplification.lean:137 (blockOp_star)",
      la.max_abs_diff(la.dagger(blockOp(a, b, c, d)),
                      blockOp(la.dagger(a), la.dagger(c), la.dagger(b), la.dagger(d))),
      0.0, abs_tol=TOL)

# matrix units:  e₁₂·e₂₁ = e₁₁,  e₁₁+e₂₂ = 1
z = la.zeros(n)
one = la.eye(n)
e11, e12, e21, e22 = blockOp(one, z, z, z), blockOp(z, one, z, z), blockOp(z, z, one, z), blockOp(z, z, z, one)
check("e₁₂·e₂₁ = e₁₁", "Cocycle/MatrixAmplification.lean:160 (e₁₂_mul_e₂₁)",
      la.max_abs_diff(la.matmul(e12, e21), e11), 0.0, abs_tol=TOL)
check("e₁₁+e₂₂ = 1", "Cocycle/MatrixAmplification.lean:174 (e₁₁_add_e₂₂)",
      la.max_abs_diff(la.add(e11, e22), la.eye(2 * n)), 0.0, abs_tol=TOL)

# --------------------------------------------------------------------------
# The proper algebra M = M_k ⊗ I_m  and its commutant M' = I_k ⊗ M_m
# --------------------------------------------------------------------------
k, m = 2, 2
N = k * m                                    # = n dimension of the base space (4)
I_k, I_m = la.eye(k), la.eye(m)


def unit(dim, i, j):
    E = la.zeros(dim)
    E[i][j] = 1.0
    return E


M_basis = [la.kron(unit(k, i, j), I_m) for i in range(k) for j in range(k)]      # M_k ⊗ I_m
Mp_basis = [la.kron(I_k, unit(m, i, j)) for i in range(m) for j in range(m)]     # I_k ⊗ M_m

# sanity: M and M' are each other's commutants at the base level
check("dim M' (I_k⊗M_m) via commutant of M = m²",
      "(toolkit sanity: model M'=I_k⊗M_m has dim m²)",
      la.commutant_dim(M_basis, N), m * m, abs_tol=0)

# --------------------------------------------------------------------------
# L1:  centralizer(M₂(M)) = scalar blocks M'⊗1₂   (dim m², NOT 4m²)
# --------------------------------------------------------------------------
z2 = la.zeros(N)
M2_gens = ([blockOp(g, z2, z2, z2) for g in M_basis] +
           [blockOp(z2, g, z2, z2) for g in M_basis] +
           [blockOp(z2, z2, g, z2) for g in M_basis] +
           [blockOp(z2, z2, z2, g) for g in M_basis])

dim_comm_M2 = la.commutant_dim(M2_gens, 2 * N)
check("L1: dim centralizer(M₂(M)) = dim(M'⊗1₂) = m²  (NOT 4m²)",
      "Cocycle/MatrixAmplification.lean:330 (centralizer_M2set = scalarBlockSet M')",
      dim_comm_M2, m * m, abs_tol=0)
check_le("L1: centralizer(M₂(M)) ≠ M₂(M') (m² < 4m²)",
         "Cocycle/MatrixAmplification.lean:330 (centralizer_M2set)",
         dim_comm_M2, 4 * m * m - 1, slack=0)   # asserts dim ≤ 4m²−1, i.e. strictly less

# ⊇ inclusion: every scalar block blockOp w 0 0 w (w∈M') commutes with all of M₂(M)
w = Mp_basis[1]                                  # a nonzero element of M'
scalar_block = blockOp(w, la.zeros(N), la.zeros(N), w)
max_comm = max(la.max_abs_diff(la.commutator(scalar_block, g), la.zeros(2 * N)) for g in M2_gens)
check("L1 ⊇: [blockOp w 0 0 w, M₂(M)] = 0 for w∈M'",
      "Cocycle/MatrixAmplification.lean:370 (centralizer_M2set, reverse)",
      max_comm, 0.0, abs_tol=TOL)
# non-scalar block from M₂(M') is NOT in the commutant (guards the m²-vs-4m² trap)
bad_block = blockOp(w, z2, z2, z2)                               # blockOp w 0 0 0, w∈M'
e12_N = blockOp(z2, la.eye(N), z2, z2)                          # e₁₂ ∈ M₂(M)
bad_comm = la.max_abs_diff(la.commutator(bad_block, e12_N), la.zeros(2 * N))
check_le("L1: blockOp w 0 0 0 (w∈M') does NOT commute with e₁₂ ⇒ ∉ centralizer",
         "Cocycle/MatrixAmplification.lean:330 (M₂(M') ⊄ centralizer)",
         -bad_comm, -1e-3, slack=0)   # asserts commutator norm > 1e-3

# --------------------------------------------------------------------------
# L2:  centralizer(M'⊗1₂) = M₂(M')     (dim 4m²)
# --------------------------------------------------------------------------
scalarBlock_gens = [blockOp(w, la.zeros(N), la.zeros(N), w) for w in M_basis]   # M ⊗ 1₂
dim_comm_scalar = la.commutant_dim(scalarBlock_gens, 2 * N)
check("L2: dim centralizer(M⊗1₂) = dim M₂(M') = 4·m²",
      "Cocycle/MatrixAmplification.lean:378 (centralizer_scalarBlockSet = M₂(M'))",
      dim_comm_scalar, 4 * m * m, abs_tol=0)

finish("M₂(M) matrix amplification numeric checks")
