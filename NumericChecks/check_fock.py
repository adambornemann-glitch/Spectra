"""Numeric checks for the Fock-space keystones:

  Spectra/Spaces/Fock/{Exponential,Symmetrizer,BoseFermi,NumberOp,Total}.lean
  Spectra/Spaces/Tensor/Power.lean

Convention anchors (verified against the Lean source):

  * Inner product is CONJUGATE-LINEAR IN THE FIRST slot (mathlib/RCLike): ⟪u,v⟫ = Σ conj(uᵢ) vᵢ.
  * NO factorial rescaling on tensor powers (Parthasarathy): ⟪f^⊗n, g^⊗n⟫ = ⟪f,g⟫ⁿ.
  * Coherent coefficient `expCoeff n = (√n!)⁻¹` (the CORRECTED convention), so the two coefficients
    on ε(f), ε(g) multiply to 1/n! against ⟪f,g⟫ⁿ and Σ = exp⟪f,g⟫.  The pre-correction 1/n!
    coefficient would give Σ⟪f,g⟫ⁿ/(n!)² (a ₀F₁/Bessel value), NOT exp — the primary bug to catch.
  * symProj = (n!)⁻¹ Σ_σ U_σ,  altProj = (n!)⁻¹ Σ_σ sign(σ) U_σ  (AVERAGES over Sₙ).

The coherent-overlap and coherent-norm statements are genuine infinite-dimensional ℓ² facts; here
they are TRUNCATED at N sectors and confirmed to CONVERGE to the transcendental value (‖f‖,‖g‖ ≤ 1,
N ≈ 24).  The permutation representation U_σ and tensor powers are built in-file and sanity-checked;
every projector identity (idempotency, self-adjointness, rank/trace, Pauli, Slater norm) exercises
them by independent routes (matrix square vs single average; numeric eigenvalue-sum vs a closed-form
binomial; det-sign vs inversion-parity).
"""

import cmath
import math
import os
import sys
from itertools import permutations

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nclib import linalg as la
from nclib.harness import check, check_le, finish

TOL = 1e-9


def inner(u, v):
    """⟪u,v⟫ with conjugation on the FIRST slot."""
    return sum(u[i].conjugate() * v[i] for i in range(len(u)))


def kron_vec(u, v):
    return [u[i] * v[j] for i in range(len(u)) for j in range(len(v))]


def tensor_pow(f, n):
    """f^⊗n as a length-dⁿ vector (empty product = the 1-dim vacuum scalar [1])."""
    out = [1.0 + 0j]
    for _ in range(n):
        out = kron_vec(out, f)
    return out


def perm_matrix(sigma, d):
    """The dⁿ×dⁿ permutation U_σ acting on tensor legs: (U_σ)_{b,a}=1 when bₖ = a_{σ(k)}.
    A faithful unitary representation of Sₙ (σ a tuple perm of range n)."""
    n = len(sigma)
    dim = d ** n

    def digits(idx):
        t = []
        for _ in range(n):
            t.append(idx % d)
            idx //= d
        return t[::-1]

    def flat(t):
        idx = 0
        for x in t:
            idx = idx * d + x
        return idx

    M = la.zeros(dim)
    for a in range(dim):
        ta = digits(a)
        tb = [ta[sigma[k]] for k in range(n)]
        M[flat(tb)][a] = 1.0
    return M


def perm_sign(sigma):
    """(−1)^{#inversions} of the permutation tuple sigma."""
    n = len(sigma)
    inv = sum(1 for i in range(n) for j in range(i + 1, n) if sigma[i] > sigma[j])
    return -1.0 if inv % 2 else 1.0


def sym_proj(d, n):
    """symProj = (n!)⁻¹ Σ_σ U_σ."""
    dim = d ** n
    P = la.zeros(dim)
    for sigma in permutations(range(n)):
        P = la.add(P, perm_matrix(sigma, d))
    return la.scale(1.0 / math.factorial(n), P)


def alt_proj(d, n):
    """altProj = (n!)⁻¹ Σ_σ sign(σ) U_σ."""
    dim = d ** n
    Q = la.zeros(dim)
    for sigma in permutations(range(n)):
        Q = la.add(Q, la.scale(perm_sign(sigma), perm_matrix(sigma, d)))
    return la.scale(1.0 / math.factorial(n), Q)


# sanity: perm_matrix(identity) = I, and sign matches det of the n-permutation matrix
assert la.is_identity(perm_matrix(tuple(range(3)), 2)), "U_id must be I"
for sig in permutations(range(3)):
    detsign = la.det(la.mat([[1.0 if sig[i] == j else 0.0 for j in range(3)] for i in range(3)])).real
    assert abs(detsign - perm_sign(sig)) < 1e-9, "sign vs det mismatch"


# ==========================================================================
#  1.  tensor-power inner product  ⟪f^⊗n, g^⊗n⟫ = ⟪f,g⟫ⁿ   (Power.lean)
# ==========================================================================
f = [1.0, 1j]
g = [2.0, 3.0]
s_fg = inner(f, g)                                   # = 2 − 3j
assert abs(s_fg.imag) > 0.1, "want a complex overlap (phase matters)"
for nn in range(1, 5):
    lhs = inner(tensor_pow(f, nn), tensor_pow(g, nn))     # big Kronecker dot
    rhs = s_fg ** nn                                       # scalar power
    check(f"inner_tprod_tprod: ⟪f^⊗{nn}, g^⊗{nn}⟫ = ⟪f,g⟫^{nn}  (Kron dot vs scalar power)",
          "Spaces/Tensor/Power.lean:66 (inner_tprod_tprod)", abs(lhs - rhs), 0.0, abs_tol=1e-10)


# ==========================================================================
#  2.  expCoeff and the sector overlap  ⟪ε(f)ₙ, ε(g)ₙ⟫ = ⟪f,g⟫ⁿ / n!   (Exponential.lean)
# ==========================================================================
# expCoeff n = 1/√(n!), expCoeff n² = 1/n!  (two routes: sqrt-invert-square vs reciprocal factorial)
for nn in range(0, 7):
    c = 1.0 / math.sqrt(math.factorial(nn))
    check(f"expCoeff_sq: (1/√{nn}!)² = 1/{nn}!",
          "Spaces/Fock/Exponential.lean:69 (expCoeff/expCoeff_sq)",
          c ** 2, 1.0 / math.factorial(nn), rel_tol=1e-12)

# inner_expVecSector: ⟪ε(f)ₙ, ε(g)ₙ⟫ = ⟪f,g⟫ⁿ / n!  with ε(f)ₙ = (√n!)⁻¹ f^⊗n
for nn in range(0, 5):
    cn = 1.0 / math.sqrt(math.factorial(nn))
    u = [cn * z for z in tensor_pow(f, nn)]
    v = [cn * z for z in tensor_pow(g, nn)]
    lhs = inner(u, v)
    rhs = s_fg ** nn / math.factorial(nn)
    check(f"inner_expVecSector: ⟪ε(f)_{nn}, ε(g)_{nn}⟫ = ⟪f,g⟫^{nn}/{nn}!",
          "Spaces/Fock/Exponential.lean:125 (inner_expVecSector)", abs(lhs - rhs), 0.0, abs_tol=1e-11)


# ==========================================================================
#  3.  ★ coherent-state overlap  ⟪ε(f), ε(g)⟫ = exp⟪f,g⟫   (truncated)   (Exponential.lean:166)
# ==========================================================================
# small-norm complex vectors; ⟪f,g⟫ genuinely complex so exp has both parts
# moderate-norm vectors: ⟪f,g⟫ = 0.25 − 0.25j is genuinely complex (exp has both cos & sin parts)
# yet |⟪f,g⟫| ≈ 0.35 keeps the exp series converging fast — N=12 gives a ~1e-15 tail — AND makes
# the pre-correction 1/n! mutation (guard a) differ from exp by ~0.03, comfortably detectable.
# (The n-particle sector has dimension dⁿ, so N cannot be pushed high — but it needn't be.)
fc = [0.5, 0.5j]
gc = [0.5, 0.5]
s_c = inner(fc, gc)
N = 12


def coherent_vec(h, N):
    """The truncated exponential vector ε(h): concatenation of (√n!)⁻¹ h^⊗n, n=0..N."""
    blocks = []
    for nn in range(N + 1):
        cn = 1.0 / math.sqrt(math.factorial(nn))
        blocks.extend(cn * z for z in tensor_pow(h, nn))
    return blocks


Ef, Eg = coherent_vec(fc, N), coherent_vec(gc, N)
lhs_ov = inner(Ef, Eg)                               # Route A: tensor-algebra partial sum
rhs_ov = cmath.exp(s_c)                              # Route B: library complex exp of one scalar
check("★ inner_expVec_expVec: ⟪ε(f),ε(g)⟫ = exp⟪f,g⟫  (truncated tensor sum → complex exp)",
      "Spaces/Fock/Exponential.lean:166 (inner_expVec_expVec)", abs(lhs_ov - rhs_ov), 0.0, abs_tol=1e-10)

# norm_expVec_sq: ‖ε(f)‖² = Real.exp(‖f‖²)
nf_sq = inner(fc, fc).real                           # ‖f‖²
lhs_nm = inner(Ef, Ef).real                          # Σ ‖f‖^{2n}/n! (tensor route)
check("★ norm_expVec_sq: ‖ε(f)‖² = exp(‖f‖²)  (truncated → real exp)",
      "Spaces/Fock/Exponential.lean:175 (norm_expVec_sq)", lhs_nm, math.exp(nf_sq), rel_tol=1e-10)


# ==========================================================================
#  4.  bosonic / fermionic projectors  (Symmetrizer.lean, BoseFermi.lean)
# ==========================================================================
for (d, n) in [(2, 2), (2, 3), (3, 2)]:
    P = sym_proj(d, n)
    Q = alt_proj(d, n)
    dim = d ** n
    # idempotent (P²=P via double sum) & self-adjoint (P†=P)
    check(f"symProj idempotent P²=P  (d={d},n={n})",
          "Spaces/Fock/Symmetrizer.lean:291 (symProj_idem)",
          la.max_abs_diff(la.matmul(P, P), P), 0.0, abs_tol=1e-10)
    check(f"symProj self-adjoint P†=P  (d={d},n={n})",
          "Spaces/Fock/Symmetrizer.lean:334 (isSelfAdjoint_symProj)",
          la.max_abs_diff(la.dagger(P), P), 0.0, abs_tol=1e-12)
    check(f"altProj idempotent Q²=Q  (d={d},n={n})",
          "Spaces/Fock/Symmetrizer.lean:310 (altProj_idem)",
          la.max_abs_diff(la.matmul(Q, Q), Q), 0.0, abs_tol=1e-10)
    check(f"altProj self-adjoint Q†=Q  (d={d},n={n})",
          "Spaces/Fock/Symmetrizer.lean:356 (isSelfAdjoint_altProj)",
          la.max_abs_diff(la.dagger(Q), Q), 0.0, abs_tol=1e-12)
    # rank/trace vs closed-form binomials — a numeric consistency fact (Symmetrizer.lean states no
    # rank theorem): trace of the projector (numeric eigenvalue-sum) vs the combinatorial dimension.
    tr_sym = la.trace(P).real
    tr_alt = la.trace(Q).real
    check(f"dim symmetric sector = tr(symProj) = C(d+n−1,n) = {math.comb(d + n - 1, n)}  (d={d},n={n})",
          "Spaces/Fock/Symmetrizer.lean:192 (symProj — sector dim, numeric consistency)",
          tr_sym, float(math.comb(d + n - 1, n)), rel_tol=1e-9)
    check(f"dim antisymmetric sector = tr(altProj) = C(d,n) = {math.comb(d, n)}  (d={d},n={n})",
          "Spaces/Fock/Symmetrizer.lean:199 (altProj — sector dim, numeric consistency)",
          tr_alt, float(math.comb(d, n)), rel_tol=1e-9)
    # eigenvalues of a projector are in {0,1}
    check(f"symProj eigenvalues ⊆ {{0,1}}  (d={d},n={n})",
          "Spaces/Fock/Symmetrizer.lean:291 (symProj_idem ⇒ spectrum ⊆ {0,1})",
          max(abs(e * (e - 1)) for e in la.herm_eigvalues(P)), 0.0, abs_tol=1e-9)
    # mutually orthogonal sectors: symProj ∘ altProj = 0  (n ≥ 2)
    check(f"symProj ∘ altProj = 0  (orthogonal sectors, d={d},n={n})",
          "Spaces/Fock/Symmetrizer.lean:424 (symProj_comp_altProj)",
          la.fro_norm(la.matmul(P, Q)), 0.0, abs_tol=1e-10)

# Pauli exclusion (altProj_tprod_eq_zero): antisymmetrizing a REPEATED factor gives 0 — but NOT trivially
Q22 = alt_proj(2, 2)
v_rep = [1.0, 2.0]
w_repeated = tensor_pow(v_rep, 2)                    # v⊗v  (repeated factor)
w_distinct = kron_vec([1.0, 0.0], [0.0, 1.0])        # e₀⊗e₁ (distinct)
check("Pauli: altProj(v⊗v) = 0  (antisymmetrizing a repeated factor)",
      "Spaces/Fock/BoseFermi.lean:261 (altProj_tprod_eq_zero)",
      math.sqrt(sum(abs(z) ** 2 for z in la.matvec(Q22, w_repeated))), 0.0, abs_tol=1e-12)
check_le("Pauli non-triviality: altProj(e₀⊗e₁) ≠ 0  (altProj is not the zero map)",
         "Spaces/Fock/BoseFermi.lean:261 (non-vacuity)",
         -math.sqrt(sum(abs(z) ** 2 for z in la.matvec(Q22, w_distinct))), -0.1, slack=0)

# Slater normalization: ‖altProj(⊗ orthonormal)‖² = 1/n!
for (d, n) in [(2, 2), (3, 3)]:
    Q = alt_proj(d, n)
    basis = [[1.0 if i == k else 0.0 for i in range(d)] for k in range(n)]  # e₀,…,e_{n−1}
    tp = [1.0 + 0j]
    for k in range(n):
        tp = kron_vec(tp, basis[k])
    qv = la.matvec(Q, tp)
    nrm_sq = sum(abs(z) ** 2 for z in qv)
    check(f"Slater norm: ‖altProj(e₀⊗…⊗e_{n-1})‖² = 1/{n}! = {1/math.factorial(n):.4f}  (d={d},n={n})",
          "Spaces/Fock/BoseFermi.lean:353 (norm_sq_altProj_tprod)", nrm_sq, 1.0 / math.factorial(n), rel_tol=1e-9)


# ==========================================================================
#  5.  number operator N  (NumberOp.lean)  — truncated Fock, d=2, sectors 0..3
# ==========================================================================
d, K = 2, 3
dims = [d ** k for k in range(K + 1)]                 # 1,2,4,8
offs = [sum(dims[:k]) for k in range(K + 2)]
totdim = offs[-1]
Nop = la.zeros(totdim)
for k in range(K + 1):
    for i in range(offs[k], offs[k + 1]):
        Nop[i][i] = float(k)                          # block k = k·I
# ★ mean photon number: ⟪ε(f), N ε(f)⟫ = ‖f‖²·exp(‖f‖²).  N acting as the eigenvalue n on sector n
# is the operator's DEFINITION (no external ground truth for the eigenvalue at the truncated level),
# so the genuine two-route check pairs that action against a TRANSCENDENTAL closed form: apply N
# (multiply sector n by n) to the tensor-built coherent vector, vs the scalar ‖f‖²·exp(‖f‖²).  A wrong
# n²-law would give ‖f‖²(‖f‖²+1)exp(‖f‖²), a genuinely different number.
Kc = 12
Ecoh = coherent_vec(fc, Kc)                          # d=2 coherent vector ε(f)
sec = []
for nn in range(Kc + 1):
    sec.extend([nn] * (2 ** nn))                     # sector index n of each component (d=2)
meanN = sum(sec[i] * abs(Ecoh[i]) ** 2 for i in range(len(Ecoh)))   # ⟪ε(f), N ε(f)⟫ = Σ n‖f‖^{2n}/n!
nf2 = inner(fc, fc).real                             # ‖f‖²
check("★ numberOp mean number: ⟪ε(f),Nε(f)⟫ = ‖f‖²·exp(‖f‖²)  (block-N action vs closed form)",
      "Spaces/Fock/NumberOp.lean:165 (numberOp_fockSector)", meanN, nf2 * math.exp(nf2), rel_tol=1e-9)
# symmetric (formal-adjoint) form: ⟪Nξ,η⟫ = ⟪ξ,Nη⟫  — apply N to ξ vs to η (different vectors), equal
# only because the eigenvalues are real.  (This is the finite content; the genuine self-adjointness
# numberOp_isSelfAdjoint at :226 is a domain equality D(N†)=D(N) a finite truncation cannot witness.)
xi = [0j] * totdim
xi[offs[2] + 1] = 1.0 + 1j
xi[offs[3] + 4] = 0.5
eta = [complex(0.3 * i, -0.2 * i) for i in range(totdim)]
check("numberOp symmetric form: ⟪Nξ,η⟫ = ⟪ξ,Nη⟫  (N applied to ξ vs to η)",
      "Spaces/Fock/NumberOp.lean:185 (numberOp_isFormalAdjoint_self)",
      abs(inner(la.matvec(Nop, xi), eta) - inner(xi, la.matvec(Nop, eta))), 0.0, abs_tol=1e-12)
# positivity: 0 ≤ Re⟪ξ,Nξ⟫
check_le("numberOp positivity: 0 ≤ Re⟪ξ,Nξ⟫",
         "Spaces/Fock/NumberOp.lean:240 (re_inner_self_numberOp_nonneg)",
         -inner(xi, la.matvec(Nop, xi)).real, 0.0, slack=1e-12)


# ==========================================================================
#  6.  linear independence of coherent vectors via the exp-Gram  (Total.lean)
# ==========================================================================
fs = [[0.2, 0.0], [0.0, 0.2], [0.15, 0.15j]]
m = len(fs)
# Route A: Gram from truncated coherent block vectors; Route B: elementwise exp of the overlap matrix
Es = [coherent_vec(h, N) for h in fs]
GA = [[inner(Es[i], Es[j]) for j in range(m)] for i in range(m)]
GB = [[cmath.exp(inner(fs[i], fs[j])) for j in range(m)] for i in range(m)]
check("exp-Gram: Gᵢⱼ = ⟪ε(fᵢ),ε(fⱼ)⟫ = exp⟪fᵢ,fⱼ⟫  (tensor route vs elementwise exp)",
      "Spaces/Fock/Exponential.lean:166 (inner_expVec_expVec, applied to a family)",
      max(abs(GA[i][j] - GB[i][j]) for i in range(m) for j in range(m)), 0.0, abs_tol=1e-10)
gmin = min(la.herm_eigvalues(la.mat(GB)))
# the exp-Gram is PD ⇒ the ε(fᵢ) are linearly independent (a downstream corollary of the exp formula;
# linear independence itself is deferred in Lean — see Exponential.lean:51 — so this anchors to the
# proved overlap identity, not to a linear-independence theorem).
check_le("exp-Gram positive-definite (min eig > 0) ⇒ ε(f₁),ε(f₂),ε(f₃) linearly independent",
         "Spaces/Fock/Exponential.lean:166 (inner_expVec_expVec ⇒ lin. indep.; deferred in Lean)", -gmin, -1e-6, slack=0)


# ==========================================================================
#  7.  FALSIFICATION GUARDS
# ==========================================================================
# (a) the pre-correction coefficient 1/n! (instead of 1/√n!) would give Σ⟪f,g⟫ⁿ/(n!)² (₀F₁/Bessel), NOT exp.
def coherent_vec_wrong(h, N):
    blocks = []
    for nn in range(N + 1):
        cn = 1.0 / math.factorial(nn)                # WRONG: 1/n! instead of 1/√n!
        blocks.extend(cn * z for z in tensor_pow(h, nn))
    return blocks


wrong_ov = inner(coherent_vec_wrong(fc, N), coherent_vec_wrong(gc, N))
check_le("GUARD coeff 1/n!: ⟪ε_wrong(f),ε_wrong(g)⟫ = Σ⟪f,g⟫ⁿ/(n!)² ≠ exp⟪f,g⟫ (₀F₁, not exp)",
         "Spaces/Fock/Exponential.lean:69 (expCoeff, /√n! guard)",
         -abs(wrong_ov - rhs_ov), -1e-2, slack=0)
# (b) altProj with the sign dropped is symProj — on the repeated factor it returns v⊗v ≠ 0 (Pauli violated).
P22 = sym_proj(2, 2)
w_symrepeat = la.matvec(P22, w_repeated)             # sign-dropped "antisymmetrizer" on v⊗v
check_le("GUARD sign-drop: (symProj not altProj)(v⊗v) ≠ 0 — the sign is what enforces Pauli",
         "Spaces/Fock/BoseFermi.lean:261 (Pauli, sign guard)",
         -math.sqrt(sum(abs(z) ** 2 for z in w_symrepeat)), -0.1, slack=0)
# (c) number operator with the n² law: mean number would be ‖f‖²(‖f‖²+1)exp‖f‖² ≠ ‖f‖²exp‖f‖².
meanN_wrong = sum(sec[i] ** 2 * abs(Ecoh[i]) ** 2 for i in range(len(Ecoh)))   # Σ n²‖f‖^{2n}/n!
check_le("GUARD n² law: ⟪ε(f),Nε(f)⟫ under n² = ‖f‖²(‖f‖²+1)exp‖f‖² ≠ ‖f‖²exp‖f‖² (law pinned by closed form)",
         "Spaces/Fock/NumberOp.lean:165 (numberOp, eigenvalue guard)",
         -abs(meanN_wrong - nf2 * math.exp(nf2)), -1e-3, slack=0)

finish("Fock space / coherent states / symmetrizers / number operator numeric checks")
