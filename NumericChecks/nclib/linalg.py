"""Pure-stdlib dense complex linear algebra for the numeric checks.

No numpy. Matrices are lists of lists of `complex`; vectors are lists of
`complex`. Everything here is written to be *auditable* and *testable* against
textbook values (see `selftest.py`), because the operator-algebra checks
(modular theory, KMS, channels) rest entirely on it.

## The one trick that avoids a complex eigensolver

A complex Hermitian matrix `H = A + iB` (A real symmetric, B real
antisymmetric) embeds into the real symmetric `2n x 2n` matrix

        M = [[A, -B],
             [B,  A]]

whose real eigen-decomposition (via a plain real-symmetric **Jacobi**
eigensolver, which is bulletproof and easy to verify) carries the entire
spectral content of `H`.  For any *real-valued* function `f : R -> R`,

        f(H)  =  C + iD ,   where  f(M) = [[C, -D],[D, C]] ,

i.e. `f(H)` is read straight off the real matrix function `f(M)`.  That covers
`sqrt`, `log`, `exp`, arbitrary real powers, `cos`, `sin` of any Hermitian
matrix.  Complex-valued functional calculus is then assembled from real pieces:

        e^{iKt} = cos(Kt) + i sin(Kt)          (K Hermitian)
        rho^{it} = e^{it log rho}              (rho PSD, invertible)

So the whole modular flow / KMS machinery is built from ONE primitive — a real
symmetric eigensolver — never a complex one.  This is deliberate: the primitive
is independently cross-checked (functional calculus vs a truncated power series)
in the self-tests, so the operator-algebra checks inherit a trusted core.
"""

import cmath
import math

# --------------------------------------------------------------------------
# Construction and basic arithmetic
# --------------------------------------------------------------------------


def mat(rows):
    """Coerce a list of lists into a matrix of complex numbers."""
    return [[complex(z) for z in row] for row in rows]


def zeros(n, m=None):
    m = n if m is None else m
    return [[0j for _ in range(m)] for _ in range(n)]


def eye(n):
    return [[complex(1.0 if i == j else 0.0) for j in range(n)] for i in range(n)]


def diagm(entries):
    n = len(entries)
    D = zeros(n)
    for i in range(n):
        D[i][i] = complex(entries[i])
    return D


def nrows(A):
    return len(A)


def ncols(A):
    return len(A[0]) if A else 0


def add(A, B):
    return [[A[i][j] + B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def sub(A, B):
    return [[A[i][j] - B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def scale(c, A):
    c = complex(c)
    return [[c * A[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def matmul(A, B):
    n, k, m = len(A), len(B), len(B[0])
    assert len(A[0]) == k, "shape mismatch in matmul"
    C = zeros(n, m)
    for i in range(n):
        Ai = A[i]
        Ci = C[i]
        for t in range(k):
            a = Ai[t]
            if a == 0:
                continue
            Bt = B[t]
            for j in range(m):
                Ci[j] += a * Bt[j]
    return C


def matmul_chain(*mats):
    out = mats[0]
    for M in mats[1:]:
        out = matmul(out, M)
    return out


def transpose(A):
    return [[A[i][j] for i in range(len(A))] for j in range(len(A[0]))]


def conj(A):
    return [[A[i][j].conjugate() for j in range(len(A[0]))] for i in range(len(A))]


def dagger(A):
    """Conjugate transpose A^*."""
    return [[A[i][j].conjugate() for i in range(len(A))] for j in range(len(A[0]))]


def trace(A):
    return sum(A[i][i] for i in range(len(A)))


def matvec(A, v):
    return [sum(A[i][j] * v[j] for j in range(len(v))) for i in range(len(A))]


def commutator(A, B):
    return sub(matmul(A, B), matmul(B, A))


def anticommutator(A, B):
    return add(matmul(A, B), matmul(B, A))


def kron(A, B):
    """Kronecker product A (x) B."""
    na, ma = len(A), len(A[0])
    nb, mb = len(B), len(B[0])
    C = zeros(na * nb, ma * mb)
    for i in range(na):
        for j in range(ma):
            a = A[i][j]
            for p in range(nb):
                for q in range(mb):
                    C[i * nb + p][j * mb + q] = a * B[p][q]
    return C


def direct_sum(A, B):
    """Block-diagonal A (+) B."""
    na, ma = len(A), len(A[0])
    nb, mb = len(B), len(B[0])
    C = zeros(na + nb, ma + mb)
    for i in range(na):
        for j in range(ma):
            C[i][j] = A[i][j]
    for i in range(nb):
        for j in range(mb):
            C[na + i][ma + j] = B[i][j]
    return C


# --------------------------------------------------------------------------
# Norms and comparison
# --------------------------------------------------------------------------


def fro_norm(A):
    return math.sqrt(sum(abs(A[i][j]) ** 2 for i in range(len(A)) for j in range(len(A[0]))))


def max_abs_diff(A, B):
    return max(abs(A[i][j] - B[i][j]) for i in range(len(A)) for j in range(len(A[0])))


def is_hermitian(A, tol=1e-10):
    return max_abs_diff(A, dagger(A)) <= tol


def is_unitary(A, tol=1e-9):
    n = len(A)
    return max_abs_diff(matmul(dagger(A), A), eye(n)) <= tol


def is_identity(A, tol=1e-9):
    return max_abs_diff(A, eye(len(A))) <= tol


# --------------------------------------------------------------------------
# Linear solve / inverse (complex Gaussian elimination, partial pivoting)
# --------------------------------------------------------------------------


def inv(A):
    n = len(A)
    # Augment [A | I] and reduce.
    aug = [[A[i][j] for j in range(n)] + [complex(1.0 if i == j else 0.0) for j in range(n)]
           for i in range(n)]
    for col in range(n):
        piv = max(range(col, n), key=lambda r: abs(aug[r][col]))
        if abs(aug[piv][col]) < 1e-300:
            raise ZeroDivisionError("singular matrix in inv")
        aug[col], aug[piv] = aug[piv], aug[col]
        pivval = aug[col][col]
        aug[col] = [x / pivval for x in aug[col]]
        for r in range(n):
            if r != col:
                f = aug[r][col]
                if f != 0:
                    aug[r] = [aug[r][k] - f * aug[col][k] for k in range(2 * n)]
    return [row[n:] for row in aug]


def solve(A, b):
    Ainv = inv(A)
    return matvec(Ainv, b)


def det(A):
    """Determinant via LU with partial pivoting."""
    n = len(A)
    M = [row[:] for row in A]
    d = 1.0 + 0j
    for col in range(n):
        piv = max(range(col, n), key=lambda r: abs(M[r][col]))
        if abs(M[piv][col]) < 1e-300:
            return 0j
        if piv != col:
            M[col], M[piv] = M[piv], M[col]
            d = -d
        d *= M[col][col]
        for r in range(col + 1, n):
            f = M[r][col] / M[col][col]
            if f != 0:
                M[r] = [M[r][k] - f * M[col][k] for k in range(n)]
    return d


# --------------------------------------------------------------------------
# Real symmetric eigensolver (cyclic Jacobi) -- the trusted core
# --------------------------------------------------------------------------


def real_sym_eig(S, sweeps=100, tol=1e-14):
    """Eigen-decompose a REAL symmetric matrix by cyclic Jacobi rotations.

    Returns (eigvals, V) with eigvals a list of floats and V a real matrix
    (list of lists of float) whose COLUMNS are orthonormal eigenvectors:
    S = V diag(eigvals) V^T.  Robust for any symmetric input; converges
    quadratically once the off-diagonal is small.
    """
    n = len(S)
    A = [[float(S[i][j]) for j in range(n)] for i in range(n)]
    V = [[1.0 if i == j else 0.0 for j in range(n)] for i in range(n)]
    for _ in range(sweeps):
        off = math.sqrt(sum(A[i][j] ** 2 for i in range(n) for j in range(i + 1, n)))
        if off <= tol:
            break
        for p in range(n):
            for q in range(p + 1, n):
                apq = A[p][q]
                if abs(apq) < 1e-300:
                    continue
                app, aqq = A[p][p], A[q][q]
                # Jacobi rotation angle: zero out A[p][q].
                phi = (aqq - app) / (2.0 * apq)
                t = math.copysign(1.0, phi) / (abs(phi) + math.sqrt(phi * phi + 1.0)) \
                    if phi != 0.0 else 1.0
                c = 1.0 / math.sqrt(t * t + 1.0)
                s = t * c
                # Apply rotation to rows/cols p,q.
                for k in range(n):
                    akp, akq = A[k][p], A[k][q]
                    A[k][p] = c * akp - s * akq
                    A[k][q] = s * akp + c * akq
                for k in range(n):
                    apk, aqk = A[p][k], A[q][k]
                    A[p][k] = c * apk - s * aqk
                    A[q][k] = s * apk + c * aqk
                for k in range(n):
                    vkp, vkq = V[k][p], V[k][q]
                    V[k][p] = c * vkp - s * vkq
                    V[k][q] = s * vkp + c * vkq
    eigvals = [A[i][i] for i in range(n)]
    return eigvals, V


# --------------------------------------------------------------------------
# Complex Hermitian functional calculus via the real embedding
# --------------------------------------------------------------------------


def _embed(H):
    """Real 2n x 2n symmetric embedding [[Re, -Im],[Im, Re]] of Hermitian H."""
    n = len(H)
    M = [[0.0] * (2 * n) for _ in range(2 * n)]
    for i in range(n):
        for j in range(n):
            re = H[i][j].real
            im = H[i][j].imag
            M[i][j] = re
            M[n + i][n + j] = re
            M[n + i][j] = im
            M[i][n + j] = -im
    return M


def _unembed(M, n):
    """Inverse of `_embed`: read complex Hermitian from real block matrix."""
    return [[complex(M[i][j], M[n + i][j]) for j in range(n)] for i in range(n)]


def herm_func(H, f):
    """Apply real-valued function f to complex Hermitian H via the real embedding.

    f : float -> float.  Returns the complex Hermitian matrix f(H).
    """
    n = len(H)
    M = _embed(H)
    lam, V = real_sym_eig(M)
    fl = [f(l) for l in lam]
    # f(M) = V diag(fl) V^T  (real symmetric).
    two = 2 * n
    fM = [[0.0] * two for _ in range(two)]
    for i in range(two):
        Vi = V[i]
        for j in range(two):
            Vj = V[j]
            fM[i][j] = sum(Vi[k] * fl[k] * Vj[k] for k in range(two))
    return _unembed(fM, n)


def herm_eigvalues(H):
    """Sorted real eigenvalues of a complex Hermitian matrix (each once)."""
    n = len(H)
    lam, _ = real_sym_eig(_embed(H))
    lam.sort()
    # Embedding doubles every eigenvalue; take every other.
    return [lam[2 * i] for i in range(n)]


def herm_eig(H, tol=1e-9):
    """Eigenvalues (ascending) and orthonormal COMPLEX eigenvectors of Hermitian H.

    Returns ``(evals, vecs)`` with ``evals`` a list of ``n`` floats and ``vecs`` a
    list of ``n`` complex vectors (each a list of ``complex``), orthonormal, with
    ``H vecs[k] = evals[k] vecs[k]``.

    Mechanism: the real embedding ``M = [[Re,-Im],[Im,Re]]`` has, for every
    eigenpair ``(mu, w)`` with ``w = [a; b]`` (``a,b in R^n``), the property that
    the complex vector ``a + i b`` is an eigenvector of ``H`` for the same ``mu``
    (``H(a+ib) = (Aa-Bb) + i(Ba+Ab) = mu(a+ib)``).  Each eigenvalue of ``H``
    appears twice in ``M`` (real eigvecs ``[a;b]`` and ``[-b;a]``), so we
    Gram-Schmidt the complex candidates within each degenerate cluster and keep
    exactly ``n`` orthonormal vectors — robust under degeneracy, never needing a
    complex eigensolver.
    """
    n = len(H)
    lam, V = real_sym_eig(_embed(H))
    order = sorted(range(2 * n), key=lambda k: lam[k])
    evals = []
    vecs = []
    for k in order:
        mu = lam[k]
        c = [complex(V[i][k], V[n + i][k]) for i in range(n)]
        # Gram-Schmidt against already-kept vectors in the same eigen-cluster.
        for prev_mu, u in zip(evals, vecs):
            if abs(prev_mu - mu) < 1e-6:
                ip = sum(u[i].conjugate() * c[i] for i in range(n))
                c = [c[i] - ip * u[i] for i in range(n)]
        nrm = math.sqrt(sum(abs(c[i]) ** 2 for i in range(n)))
        if nrm < tol:
            continue
        vecs.append([c[i] / nrm for i in range(n)])
        evals.append(mu)
        if len(vecs) == n:
            break
    return evals, vecs


def herm_sqrt(H):
    # `max(0, ·)` clamps sub-epsilon negative eigenvalues (Jacobi roundoff on a PSD
    # operator) to 0 — the CFC √ of a positive operator is defined on its spectrum ⊆ [0,∞).
    return herm_func(H, lambda x: math.sqrt(x) if x > 0.0 else 0.0)


def herm_log(H):
    return herm_func(H, math.log)


def herm_exp(H):
    return herm_func(H, math.exp)


def herm_pow(H, p):
    """Real power H^p for PSD Hermitian H (p real)."""
    return herm_func(H, lambda x: x ** p if x > 0 else (0.0 if p > 0 else float("inf")))


def herm_unitary_exp(K, t=1.0):
    """e^{i t K} for Hermitian K, as cos(tK) + i sin(tK) (both real-valued calc)."""
    tK = scale(t, K)
    cospart = herm_func(tK, math.cos)
    sinpart = herm_func(tK, math.sin)
    return add(cospart, scale(1j, sinpart))


def herm_pow_imag(rho, t):
    """rho^{it} = e^{i t log rho} for PSD invertible Hermitian rho."""
    return herm_unitary_exp(herm_log(rho), t)


def expm_series(A, terms=60):
    """Matrix exponential by truncated Taylor series (INDEPENDENT route; for tests
    and for general non-Hermitian A).  Scaling-and-squaring for robustness."""
    n = len(A)
    # scale by 2^s so that ||A/2^s|| is small
    nrm = fro_norm(A)
    s = max(0, int(math.ceil(math.log2(nrm + 1e-300))) + 1) if nrm > 0.5 else 0
    B = scale(1.0 / (2 ** s), A)
    term = eye(n)
    total = eye(n)
    for k in range(1, terms):
        term = scale(1.0 / k, matmul(term, B))
        total = add(total, term)
    for _ in range(s):
        total = matmul(total, total)
    return total


# --------------------------------------------------------------------------
# Partial trace and vectorization (for channels / bipartite systems)
# --------------------------------------------------------------------------


def partial_trace(rho, dims, keep):
    """Partial trace of a bipartite operator on dims=(dA,dB), keeping subsystem
    `keep` in {0,1}.  rho is (dA*dB) x (dA*dB), row/col index = a*dB + b."""
    dA, dB = dims
    if keep == 0:
        out = zeros(dA)
        for a1 in range(dA):
            for a2 in range(dA):
                out[a1][a2] = sum(rho[a1 * dB + b][a2 * dB + b] for b in range(dB))
        return out
    else:
        out = zeros(dB)
        for b1 in range(dB):
            for b2 in range(dB):
                out[b1][b2] = sum(rho[a * dB + b1][a * dB + b2] for a in range(dA))
        return out


def vec(X):
    """Column-stacking vectorization: vec(X)[j*n + i] = X[i][j]."""
    n, m = len(X), len(X[0])
    out = [0j] * (n * m)
    for j in range(m):
        for i in range(n):
            out[j * n + i] = X[i][j]
    return out


def unvec(v, n):
    """Inverse of column-stacking vec for an n x n matrix."""
    X = zeros(n)
    for j in range(n):
        for i in range(n):
            X[i][j] = v[j * n + i]
    return X


# --------------------------------------------------------------------------
# Singular values (via Hermitian eigenvalues of A^* A) -- for trace/HS norms
# --------------------------------------------------------------------------


def rank(A, tol=1e-9):
    """Numerical rank of a complex matrix via Gaussian elimination with pivoting."""
    n = len(A)
    m = len(A[0])
    M = [row[:] for row in A]
    r = 0
    for col in range(m):
        # find pivot in column `col` at or below row r
        piv = max(range(r, n), key=lambda i: abs(M[i][col])) if r < n else None
        if piv is None or abs(M[piv][col]) < tol:
            continue
        M[r], M[piv] = M[piv], M[r]
        pv = M[r][col]
        M[r] = [x / pv for x in M[r]]
        for i in range(n):
            if i != r and abs(M[i][col]) > 0:
                f = M[i][col]
                M[i] = [M[i][k] - f * M[r][k] for k in range(m)]
        r += 1
        if r == n:
            break
    return r


def null_dim(A, tol=1e-9):
    """Dimension of the null space (kernel) of a complex matrix."""
    return len(A[0]) - rank(A, tol)


def commutant_dim(generators, d, tol=1e-8):
    """Dimension of the commutant {X in M_d : [X,g]=0 for all g in generators}.

    Builds the stacked linear map vec(X) |-> ([X,g_1];...;[X,g_k]) and returns
    the dimension of its kernel.  vec is column-stacking, so
    vec([X,g]) = ((g^T (x) I) - (I (x) g)) vec(X)."""
    I_d = eye(d)
    blocks = []
    for g in generators:
        Lg = kron(transpose(g), I_d)     # vec(X g) = (g^T (x) I) vec X
        Rg = kron(I_d, g)                # vec(g X) = (I (x) g) vec X
        blocks.append(sub(Lg, Rg))
    # stack vertically
    big = []
    for B in blocks:
        big.extend(B)
    return null_dim(big, tol)


def transpose_perm(n):
    """The n^2 x n^2 permutation P with vec(X^T) = P vec(X) (column-stacking vec).

    Together with complex conjugation this realizes the adjoint map X |-> X^*
    on the vectorized Hilbert-Schmidt space (X^* = conj . transpose)."""
    d = n * n
    P = [[0.0] * d for _ in range(d)]
    for i in range(n):
        for j in range(n):
            # vec(X)[j*n+i] = X[i][j];  vec(X^T)[i*n+j] = X[j][i] = vec(X)[j*n+i]
            P[i * n + j][j * n + i] = 1.0
    return P


def realify_linear(A):
    """Realify a COMPLEX-linear map (d x d) to the real 2d x 2d [[Re,-Im],[Im,Re]]."""
    return _embed(A)


def realify_antilinear(A):
    """Realify an ANTILINEAR map v |-> A conj(v) to real 2d x 2d [[ReA, ImA],[ImA, -ReA]].

    Antilinear T(x+iy) = A(x-iy) = (ReA x + ImA y) + i(ImA x - ReA y)."""
    d = len(A)
    M = [[0.0] * (2 * d) for _ in range(2 * d)]
    for i in range(d):
        for j in range(d):
            re, im = A[i][j].real, A[i][j].imag
            M[i][j] = re            # Re-out from Re-in
            M[i][d + j] = im        # Re-out from Im-in
            M[d + i][j] = im        # Im-out from Re-in
            M[d + i][d + j] = -re   # Im-out from Im-in
    return M


def unrealify_linear(M, d):
    """Inverse of `realify_linear`: read complex d x d from real [[C,-D],[D,C]]."""
    return _unembed(M, d)


def real_transpose(M):
    """Plain transpose of a real matrix (list of lists of float)."""
    n, m = len(M), len(M[0])
    return [[M[i][j] for i in range(n)] for j in range(m)]


def real_matmul(A, B):
    """Real matrix product (float entries)."""
    n, k, m = len(A), len(B), len(B[0])
    C = [[0.0] * m for _ in range(n)]
    for i in range(n):
        Ai = A[i]
        Ci = C[i]
        for t in range(k):
            a = Ai[t]
            if a == 0.0:
                continue
            Bt = B[t]
            for j in range(m):
                Ci[j] += a * Bt[j]
    return C


def singular_values(A):
    """Singular values of A (descending): sqrt of eigenvalues of A^* A."""
    AhA = matmul(dagger(A), A)
    ev = herm_eigvalues(AhA)
    sv = [math.sqrt(max(0.0, e)) for e in ev]
    sv.sort(reverse=True)
    return sv


def trace_norm(A):
    """Schatten-1 norm = sum of singular values = Tr|A|."""
    return sum(singular_values(A))


def hs_norm(A):
    """Hilbert-Schmidt (Schatten-2) norm = sqrt(Tr A^* A)."""
    return math.sqrt(trace(matmul(dagger(A), A)).real)


def op_norm(A):
    """Operator (Schatten-inf) norm = largest singular value."""
    return singular_values(A)[0]


def abs_op(A):
    """|A| = sqrt(A^* A), Hermitian PSD."""
    return herm_sqrt(matmul(dagger(A), A))


# --------------------------------------------------------------------------
# Random-ish deterministic Hermitian / density matrices (seed-free, for tests)
# --------------------------------------------------------------------------


def hermitian_from_seed(n, seed):
    """Deterministic Hermitian n x n matrix from an integer seed (no RNG).

    Uses a simple LCG-like integer recurrence so results are reproducible and
    RNG-free (the workflow/quadrature style forbids Math.random-type calls)."""
    x = (seed * 1103515245 + 12345) & 0x7FFFFFFF
    def nxt():
        nonlocal x
        x = (x * 1103515245 + 12345) & 0x7FFFFFFF
        return (x / 0x7FFFFFFF) * 2.0 - 1.0
    H = zeros(n)
    for i in range(n):
        H[i][i] = complex(nxt(), 0.0)
        for j in range(i + 1, n):
            z = complex(nxt(), nxt())
            H[i][j] = z
            H[j][i] = z.conjugate()
    return H


def density_from_seed(n, seed, floor=0.15):
    """Deterministic faithful (strictly positive, trace-1) density matrix."""
    H = hermitian_from_seed(n, seed)
    P = matmul(H, dagger(H))          # PSD
    # add a floor to guarantee strict positivity (faithfulness)
    for i in range(n):
        P[i][i] += floor
    tr = trace(P).real
    return scale(1.0 / tr, P)
