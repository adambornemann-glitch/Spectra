"""Numeric checks for the trace-class / Schatten-norm keystones:

  Spectra/QuantumMechanics/Channels/TraceClass/{Fidelity,HilbertSchmidtNorm,Norm}.lean
  Spectra/QuantumMechanics/Channels/PolarDecomp.lean
  Spectra/InformationGeometry/Quantum/BKM.lean

These theorems are stated for (possibly infinite-dimensional) trace-class / Hilbert–Schmidt
operators; the `IsTraceClass`/`IsHilbertSchmidt` *predicates* are vacuously true for every finite
matrix, so only the QUANTITATIVE shadows are checked here — the trace/HS/operator norms
(`Σσᵢ`, `√Σσᵢ²`, `max σᵢ`), the Uhlmann fidelity, and the BKM kernel/metric.

Two independence disciplines the recon flagged as essential:

  * The symmetric-identity trap (x = x).  `traceNorm_adjoint` (‖A⋆‖₁ = ‖A‖₁) and `fidelity_comm`
    are equalities a self-comparison would fake.  The escape is that the two sides are computed
    from GENUINELY DIFFERENT matrices that merely share a spectrum: ‖A⋆‖₁ diagonalizes `A A⋆`
    while ‖A‖₁ diagonalizes `A⋆ A` (different matrices for non-normal `A`); the fidelity is checked
    against the standard textbook formula `tr √(√ρ σ √ρ)` — a different Hermitian matrix
    (`√ρ σ √ρ`) than the one behind `‖√ρ √σ‖₁` (`√σ ρ √σ`).  And the numeric VALUE (sum of
    singular values) is pinned, because dropping the √ (using Σ eigenvalues = ‖·‖₂²) is also
    adjoint-invariant and would pass a pure equality test while being the wrong quantity.

  * The BKM metric `∫₀^∞ tr(A(ρ+s)⁻¹B(ρ+s)⁻¹) ds` is validated by two disjoint routes: a
    double-exponential QUADRATURE of the resolvent integrand, versus the closed-form
    `Σ_{k,l} Ã_{kl} B̃_{lk} · c(pₖ,p_l)` in ρ's eigenbasis, where `c(a,b) = (log a − log b)/(a − b)`
    is the reciprocal logarithmic mean (Kubo–Mori tensor).  The quadrature never diagonalizes ρ;
    the closed form never integrates.
"""

import cmath
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nclib import linalg as la
from nclib.quadrature import exp_sinh
from nclib.harness import check, check_le, finish

TOL = 1e-8


def inner(u, v):
    return sum(u[i].conjugate() * v[i] for i in range(len(u)))


# ==========================================================================
#  FIDELITY  (Channels/TraceClass/Fidelity.lean)
# ==========================================================================
# Faithful states, NON-commuting so √ρ√σ ≠ √σ√ρ and F is a nontrivial number.
rho = la.density_from_seed(3, 7, floor=0.05)
sigma = la.density_from_seed(3, 23, floor=0.05)
assert la.max_abs_diff(la.commutator(rho, sigma), la.zeros(3)) > 0.1, "need [ρ,σ]≠0"
sqrt_rho, sqrt_sig = la.herm_sqrt(rho), la.herm_sqrt(sigma)


def fidelity_lean(P, Q):
    """The Lean definition F(P,Q) = ‖√P √Q‖₁ = Σ singular values of √P √Q."""
    return la.trace_norm(la.matmul(la.herm_sqrt(P), la.herm_sqrt(Q)))


def fidelity_textbook(P, Q):
    """Independent route: the standard Uhlmann formula F = tr √(√P Q √P) = Σ √eig(√P Q √P).
    A DIFFERENT Hermitian matrix (√P Q √P) than the one behind ‖√P √Q‖₁, with the same spectrum."""
    sP = la.herm_sqrt(P)
    M = la.matmul(la.matmul(sP, Q), sP)          # √P Q √P  (Hermitian PSD)
    return sum(math.sqrt(max(0.0, e)) for e in la.herm_eigvalues(M))


F_def = fidelity_lean(rho, sigma)
F_txt = fidelity_textbook(rho, sigma)
# fidelity : ‖√ρ√σ‖₁ equals the textbook Uhlmann fidelity tr√(√ρσ√ρ)  (two different Hermitian matrices)
check("fidelity F(ρ,σ) = ‖√ρ√σ‖₁ = tr√(√ρσ√ρ)  (Lean def vs Uhlmann formula, independent matrices)",
      "Fidelity.lean:139 (fidelity)", F_def, F_txt, rel_tol=1e-7)

# fidelity_self : F(ρ,ρ) = tr ρ  (use an UNNORMALIZED PSD ρ so tr ρ ≠ 1 — guards against a hidden √ or normalization)
Pun = la.mat([[2.0, 0.5j, 0.0], [-0.5j, 0.5, 0.0], [0.0, 0.0, 1.3]])   # Hermitian PSD, tr = 3.8
F_self = fidelity_lean(Pun, Pun)
check("fidelity_self: F(ρ,ρ) = tr ρ = 3.8  (unnormalized, value pinned ≠ 1)",
      "Fidelity.lean:151 (fidelity_self)", F_self, la.trace(Pun).real, rel_tol=1e-8)

# fidelity_comm : F(ρ,σ) = F(σ,ρ)  — the two SVDs are of DIFFERENT matrices √ρ√σ vs √σ√ρ
M_rs = la.matmul(sqrt_rho, sqrt_sig)
M_sr = la.matmul(sqrt_sig, sqrt_rho)
assert la.max_abs_diff(M_rs, M_sr) > 0.05, "need √ρ√σ ≠ √σ√ρ (else x=x)"
check("fidelity_comm: F(ρ,σ) = F(σ,ρ)  (SVDs of the two DIFFERENT matrices √ρ√σ, √σ√ρ)",
      "Fidelity.lean:157 (fidelity_comm)", la.trace_norm(M_rs), la.trace_norm(M_sr), rel_tol=1e-8)

# fidelity_le_sqrt_mul : F(ρ,σ) ≤ √(tr ρ · tr σ)  — test on UNNORMALIZED positives so the bound isn't just "≤1"
Q1 = la.mat([[1.5, 0.3 - 0.2j, 0.0], [0.3 + 0.2j, 0.8, 0.1], [0.0, 0.1, 0.6]])   # PSD
Q2 = la.mat([[0.9, 0.0, 0.4j], [0.0, 1.1, 0.0], [-0.4j, 0.0, 0.7]])              # PSD
assert min(la.herm_eigvalues(Q1)) > 1e-6 and min(la.herm_eigvalues(Q2)) > 1e-6, "need PSD"
check_le("fidelity_le_sqrt_mul: F(ρ,σ) ≤ √(tr ρ · tr σ)  (unnormalized positives)",
         "Fidelity.lean:166 (fidelity_le_sqrt_mul)",
         fidelity_lean(Q1, Q2), math.sqrt(la.trace(Q1).real * la.trace(Q2).real), slack=1e-9)

# fidelity_le_one : F ≤ 1 for normalized states, strict for ρ ≠ σ (report the gap)
check_le("fidelity_le_one: F(ρ,σ) ≤ 1  for states (strict since ρ ≠ σ)",
         "Fidelity.lean:179 (fidelity_le_one)", F_def, 1.0, slack=1e-9)
check_le("fidelity < 1 strictly for distinct states (bound has slack)",
         "Fidelity.lean:179 (fidelity_le_one, strictness)", -(1.0 - F_def), -1e-3, slack=0)

# EXTERNAL ANCHOR: for a pure state |ψ⟩⟨ψ|, F(|ψ⟩⟨ψ|, σ) = √⟨ψ|σ|ψ⟩ (validates the fidelity VALUE)
psi = [c / math.sqrt(sum(abs(z) ** 2 for z in [0.6, 0.8j, 0.5])) for c in [0.6, 0.8j, 0.5]]
Ppsi = [[psi[i] * psi[j].conjugate() for j in range(3)] for i in range(3)]
check("fidelity anchor: F(|ψ⟩⟨ψ|, σ) = √⟨ψ|σ|ψ⟩  (pure-state fidelity value)",
      "Fidelity.lean:139 (fidelity, pure-state anchor)",
      fidelity_lean(Ppsi, sigma), math.sqrt(inner(psi, la.matvec(sigma, psi)).real), rel_tol=1e-7)


# ==========================================================================
#  TRACE-NORM ADJOINT INVARIANCE  &  SCHATTEN–HÖLDER  (Fidelity.lean / HilbertSchmidtNorm.lean)
# ==========================================================================
# a genuinely NON-NORMAL matrix, so A A⋆ ≠ A⋆ A (different matrices, same spectrum)
A = la.mat([[1.0, 2.0 + 1j, 0.5], [0.0, 0.3, 1.5j], [0.2j, 0.0, -0.7]])
assert la.max_abs_diff(la.matmul(A, la.dagger(A)), la.matmul(la.dagger(A), A)) > 0.1, "need non-normal A"
# traceNorm_adjoint : ‖A⋆‖₁ = ‖A‖₁  — ‖A⋆‖₁ diagonalizes A A⋆, ‖A‖₁ diagonalizes A⋆ A (different matrices)
check("traceNorm_adjoint: ‖A⋆‖₁ = ‖A‖₁  (via singular values of A A⋆ vs A⋆ A — different matrices)",
      "Fidelity.lean:115 (traceNorm_adjoint)", la.trace_norm(la.dagger(A)), la.trace_norm(A), rel_tol=1e-8)
# The trace norm is Σσ, NOT Σσ² (= ‖A‖₂², also adjoint-invariant): so the adjoint check above does
# not by itself pin the right quantity.  Σσ ≠ Σσ² here (guard), and Tr|A| = ‖A‖₁ (= Σσ, not Σσ²) is
# pinned independently at the polar-decomposition block below (trace of the reconstructed |A|).
sv = la.singular_values(A)
check_le("Σσᵢ ≠ Σσᵢ²  (‖A‖₁ and ‖A‖₂² genuinely differ on this A — the value, not just adjoint-symmetry)",
         "HilbertSchmidtNorm.lean:83 (hsNorm)", -abs(sum(sv) - sum(s * s for s in sv)), -1e-2, slack=0)
# hsNorm_adjoint : ‖A⋆‖₂ = ‖A‖₂
check("hsNorm_adjoint: ‖A⋆‖₂ = ‖A‖₂",
      "HilbertSchmidtNorm.lean:102 (hsNorm_adjoint)", la.hs_norm(la.dagger(A)), la.hs_norm(A), rel_tol=1e-9)

# traceNorm_comp_le : ‖X Y‖₁ ≤ ‖X‖₂ ‖Y‖₂   (sharp Schatten–Hölder)
X = la.mat([[1.0, 0.5j, 0.0], [0.3, 0.0, 1.2], [0.0, -0.4j, 0.6]])
Y = la.mat([[0.0, 1.1, 0.2j], [0.7, 0.0, 0.0], [0.3j, 0.5, -0.9]])
lhs_sh = la.trace_norm(la.matmul(X, Y))
rhs_sh = la.hs_norm(X) * la.hs_norm(Y)
check_le("Schatten–Hölder: ‖XY‖₁ ≤ ‖X‖₂·‖Y‖₂  (SVD sum vs Frobenius product)",
         "HilbertSchmidtNorm.lean:143 (traceNorm_comp_le)", lhs_sh, rhs_sh, slack=1e-9)
check_le("Schatten–Hölder has slack here: ‖XY‖₁ < ‖X‖₂‖Y‖₂ (not vacuous)",
         "HilbertSchmidtNorm.lean:143 (traceNorm_comp_le, slack)", -(rhs_sh - lhs_sh), -1e-3, slack=0)
# sharp/tight case: X = Y = a rank-one |u⟩⟨v| saturates ‖XX‖₁ ... use X=|u⟩⟨v|, Y=|v⟩⟨w| ⇒ equality ‖XY‖₁=‖X‖₂‖Y‖₂
u = [1.0, 1j, 0.0]; vv = [0.0, 1.0, 1j]; w = [1.0, 0.0, 1.0]
R1 = [[u[i] * vv[j].conjugate() for j in range(3)] for i in range(3)]   # |u⟩⟨v|
R2 = [[vv[i] * w[j].conjugate() for j in range(3)] for i in range(3)]   # |v⟩⟨w|
check("Schatten–Hölder SHARP: ‖(|u⟩⟨v|)(|v⟩⟨w|)‖₁ = ‖·‖₂·‖·‖₂  (rank-one equality case)",
      "HilbertSchmidtNorm.lean:143 (traceNorm_comp_le, sharpness)",
      la.trace_norm(la.matmul(R1, R2)), la.hs_norm(R1) * la.hs_norm(R2), rel_tol=1e-7)

# hsNorm_sqrtOp_of_nonneg : ‖√ρ‖₂ = √(tr ρ)
check("hsNorm_sqrtOp: ‖√ρ‖₂ = √(tr ρ)  (Frobenius norm of √ρ vs √trace)",
      "Fidelity.lean:53 (hsNorm_sqrtOp_of_nonneg)",
      la.hs_norm(sqrt_rho), math.sqrt(la.trace(rho).real), rel_tol=1e-8)


# ==========================================================================
#  POLAR DECOMPOSITION  (PolarDecomp.lean)
# ==========================================================================
# A invertible non-normal ⇒ polar isometry U is unitary, A = U|A|, |A⋆| = U|A|U⋆.
absA = la.abs_op(A)                                   # |A| = √(A⋆A), Hermitian PSD
U = la.matmul(A, la.inv(absA))                        # U = A|A|⁻¹  (unitary since A invertible)
check("polar isometry U = A|A|⁻¹ is unitary (A invertible)",
      "PolarDecomp.lean:127 (polarIsometry)", 1.0 if la.is_unitary(U) else 0.0, 1.0, abs_tol=1e-9)
# polar_decomposition : U |A| = A
check("polar_decomposition: U·|A| = A",
      "PolarDecomp.lean:140 (polar_decomposition)", la.max_abs_diff(la.matmul(U, absA), A), 0.0, abs_tol=1e-8)
# absOp_adjoint_eq : |A⋆| = U |A| U⋆   (the identity behind traceNorm_adjoint)
lhs_pa = la.abs_op(la.dagger(A))
rhs_pa = la.matmul(la.matmul(U, absA), la.dagger(U))
check("|A⋆| = U|A|U⋆  (absOp_adjoint_eq, the polar identity behind ‖A⋆‖₁=‖A‖₁)",
      "Fidelity.lean:72 (absOp_adjoint_eq)", la.max_abs_diff(lhs_pa, rhs_pa), 0.0, abs_tol=1e-7)
# |A| and A share the same singular values (eig|A| = σ(A)); |A| Hermitian so its eigenvalues ARE its σ
check("Tr|A| = ‖A‖₁  (|A| = √(A⋆A) has eigenvalues = singular values of A)",
      "PolarDecomp.lean:51 (absOp)", la.trace(absA).real, la.trace_norm(A), rel_tol=1e-8)


# ==========================================================================
#  BKM METRIC  (InformationGeometry/Quantum/BKM.lean)
# ==========================================================================
# 2x2 for a fast, accurate resolvent quadrature.  τ = ρ_b + s I strictly positive for s>0.
rho_b = la.density_from_seed(2, 5, floor=0.08)        # faithful state
# self-adjoint (Hermitian) trace-class tangent operators A_b, B_b, NON-commuting with ρ_b
A_b = la.mat([[0.4, 0.6 + 0.3j], [0.6 - 0.3j, -0.4]])
B_b = la.mat([[0.1, -0.5j], [0.5j, 0.7]])
assert la.is_hermitian(A_b) and la.is_hermitian(B_b), "tangent ops must be self-adjoint"


def bkm_kernel(tau, A, B):
    """bkmKernel τ A B = tr(A τ⁻¹ B τ⁻¹)  (τ⁻¹ = Ring.inverse τ)."""
    Ti = la.inv(tau)
    return la.trace(la.matmul(la.matmul(la.matmul(A, Ti), B), Ti))


# bkmKernel_comm : K(A,B) = K(B,A)  — the two matrices AτBτ⁻¹ and BτAτ⁻¹ differ; equal traces by cyclicity
tau0 = la.add(rho_b, la.scale(0.37, la.eye(2)))
prodAB = la.matmul(la.matmul(la.matmul(A_b, la.inv(tau0)), B_b), la.inv(tau0))
prodBA = la.matmul(la.matmul(la.matmul(B_b, la.inv(tau0)), A_b), la.inv(tau0))
assert la.max_abs_diff(prodAB, prodBA) > 0.05, "need A τ⁻¹ B τ⁻¹ ≠ B τ⁻¹ A τ⁻¹ (else x=x)"
check("bkmKernel_comm: K_τ(A,B) = K_τ(B,A)  (cyclicity of trace on two DIFFERENT products)",
      "BKM.lean:96 (bkmKernel_comm)", abs(bkm_kernel(tau0, A_b, B_b) - bkm_kernel(tau0, B_b, A_b)),
      0.0, abs_tol=1e-9)
# bkmKernel_self_re_nonneg : 0 ≤ Re K_τ(A,A) for self-adjoint A.  Independent route: = ‖τ^{-1/2}Aτ^{-1/2}‖₂²
Tinv_half = la.herm_pow(la.inv(tau0), 0.5)            # τ^{-1/2}  (τ⁻¹ PSD)
C = la.matmul(la.matmul(Tinv_half, A_b), Tinv_half)  # C = τ^{-1/2} A τ^{-1/2}, Hermitian
check_le("bkmKernel_self_re_nonneg: 0 ≤ Re K_τ(A,A)",
         "BKM.lean:119 (bkmKernel_self_re_nonneg)", -bkm_kernel(tau0, A_b, A_b).real, 0.0, slack=1e-10)
check("Re K_τ(A,A) = ‖τ^{-1/2}Aτ^{-1/2}‖₂²  (kernel = HS-norm of the conjugated operator)",
      "BKM.lean:119 (bkmKernel_self_re_nonneg, C⋆C route)",
      bkm_kernel(tau0, A_b, A_b).real, la.hs_norm(C) ** 2, rel_tol=1e-8)
# bilinearity : K(A₁+A₂,B) = K(A₁,B)+K(A₂,B) and K(cA,B) = c·K(A,B)
A2 = la.mat([[0.2, 0.1j], [-0.1j, -0.3]])
check("bkmKernel_add_left: K(A₁+A₂,B) = K(A₁,B)+K(A₂,B)",
      "BKM.lean:76 (bkmKernel_add_left)",
      abs(bkm_kernel(tau0, la.add(A_b, A2), B_b) - (bkm_kernel(tau0, A_b, B_b) + bkm_kernel(tau0, A2, B_b))),
      0.0, abs_tol=1e-9)
c_scal = 1.7 - 0.4j
check("bkmKernel_smul_left: K(cA,B) = c·K(A,B)",
      "BKM.lean:82 (bkmKernel_smul_left)",
      abs(bkm_kernel(tau0, la.scale(c_scal, A_b), B_b) - c_scal * bkm_kernel(tau0, A_b, B_b)),
      0.0, abs_tol=1e-9)

# --- the BKM METRIC g^BKM_ρ(A,B) = ∫_{s>0} Re tr(A(ρ+s)⁻¹B(ρ+s)⁻¹) ds ---
# Route 1: double-exponential quadrature of the resolvent integrand.
def bkm_integrand(A, B):
    def f(s):
        tau = la.add(rho_b, la.scale(s, la.eye(2)))
        return bkm_kernel(tau, A, B).real
    return f


g_quad = exp_sinh(bkm_integrand(A_b, B_b))
# Route 2: eigenbasis closed form  Σ_{k,l} Ã_{kl} B̃_{lk} c(pₖ,p_l),  c(a,b)=(log a−log b)/(a−b).
p, ecols = la.herm_eig(rho_b)                        # eigenvalues pₖ, eigenvectors (columns)
Umat = [[ecols[k][i] for k in range(2)] for i in range(2)]   # U with columns = eigenvectors
Ud = la.dagger(Umat)
Atil = la.matmul(la.matmul(Ud, A_b), Umat)          # Ã = U⋆ A U
Btil = la.matmul(la.matmul(Ud, B_b), Umat)


def ckm(a, b):
    return 1.0 / a if abs(a - b) < 1e-9 else (math.log(a) - math.log(b)) / (a - b)


g_closed = sum(Atil[k][l] * Btil[l][k] * ckm(p[k], p[l]) for k in range(2) for l in range(2)).real
check("bkmMetric g(A,B) = ∫₀^∞ Re tr(A(ρ+s)⁻¹B(ρ+s)⁻¹) ds  (quadrature = Kubo–Mori closed form)",
      "BKM.lean:155 (bkmMetric)", g_quad, g_closed, rel_tol=1e-6)
# bkmMetric_comm : g(A,B) = g(B,A)
g_quad_BA = exp_sinh(bkm_integrand(B_b, A_b))
check("bkmMetric_comm: g(A,B) = g(B,A)  (quadrature, both orders)",
      "BKM.lean:165 (bkmMetric_comm)", g_quad, g_quad_BA, rel_tol=1e-6)
# bkmMetric_self_nonneg : 0 ≤ g(A,A)  (and strictly positive for A ≠ 0)
g_self = exp_sinh(bkm_integrand(A_b, A_b))
check_le("bkmMetric_self_nonneg: 0 ≤ g(A,A)  (strictly positive for A ≠ 0)",
         "BKM.lean:172 (bkmMetric_self_nonneg)", -g_self, -1e-3, slack=0)


# ==========================================================================
#  FALSIFICATION GUARDS
# ==========================================================================
# (a) fidelity WITHOUT the square roots: ‖ρσ‖₁ ≠ ‖√ρ√σ‖₁ (the roots are load-bearing).
F_noroot = la.trace_norm(la.matmul(rho, sigma))
check_le("GUARD no-sqrt: ‖ρσ‖₁ ≠ ‖√ρ√σ‖₁ (dropping √ is detected)",
         "Fidelity.lean:139 (fidelity, sqrt guard)", -abs(F_noroot - F_def), -1e-2, slack=0)
# (b) BKM with τ (not τ⁻¹): tr(A τ B τ) ≠ tr(A τ⁻¹ B τ⁻¹) (inverting the resolvent is load-bearing).
K_wrong = la.trace(la.matmul(la.matmul(la.matmul(A_b, tau0), B_b), tau0)).real
check_le("GUARD BKM τ vs τ⁻¹: tr(AτBτ) ≠ tr(Aτ⁻¹Bτ⁻¹) (the resolvent inverse is required)",
         "BKM.lean:66 (bkmKernel, inverse guard)",
         -abs(K_wrong - bkm_kernel(tau0, A_b, B_b).real), -1e-2, slack=0)
# (c) Schatten–Hölder with ‖X‖₂+‖Y‖₂ (AM instead of product) would be a DIFFERENT, weaker-looking bound.
check_le("GUARD Hölder product vs sum: ‖X‖₂·‖Y‖₂ ≠ ‖X‖₂+‖Y‖₂ (the product form is genuine)",
         "HilbertSchmidtNorm.lean:143 (traceNorm_comp_le, product guard)",
         -abs(rhs_sh - (la.hs_norm(X) + la.hs_norm(Y))), -1e-2, slack=0)

finish("Fidelity / Schatten norms / polar decomposition / BKM metric numeric checks")
