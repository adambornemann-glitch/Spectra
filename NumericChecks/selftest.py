"""Self-test of the nclib toolkit against textbook values.

Run: python3 selftest.py  (from NumericChecks/)
If this fails, no other check in this directory can be trusted.
"""

import math
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from nclib.quadrature import tanh_sinh, exp_sinh
from nclib.special import genlaguerre, kummer_1f1, assoc_legendre, sph_harm_real_theta
from nclib.harness import check, finish
from nclib import linalg as la

# --- quadrature ---
check("ts: int_0^1 4/(1+x^2) = pi", "(toolkit)",
      tanh_sinh(lambda x: 4.0 / (1.0 + x * x), 0.0, 1.0), math.pi)
check("ts: int_0^1 1/sqrt(x) = 2 (endpoint singularity)", "(toolkit)",
      tanh_sinh(lambda x: 1.0 / math.sqrt(x), 0.0, 1.0), 2.0)
check("es: int_0^inf e^{-x} = 1", "(toolkit)",
      exp_sinh(lambda x: math.exp(-x)), 1.0)
check("es: int_0^inf x^2 e^{-x} = 2", "(toolkit)",
      exp_sinh(lambda x: x * x * math.exp(-x)), 2.0)
check("es: int_0^inf e^{-x^2} = sqrt(pi)/2", "(toolkit)",
      exp_sinh(lambda x: math.exp(-x * x)), math.sqrt(math.pi) / 2.0)
check("es: int_0^inf e^{-x}/sqrt(x) = sqrt(pi)", "(toolkit)",
      exp_sinh(lambda x: math.exp(-x) / math.sqrt(x)), math.sqrt(math.pi))

# --- Laguerre: orthogonality int_0^inf x^a e^{-x} L_n^a L_m^a = G(n+a+1)/n! δnm ---
def lag_inner(n, m, a):
    return exp_sinh(lambda x: x**a * math.exp(-x) * genlaguerre(n, a, x) * genlaguerre(m, a, x))

check("Laguerre: <L_3^2, L_3^2>_w = Gamma(6)/3! = 20", "(toolkit)",
      lag_inner(3, 3, 2.0), math.gamma(6.0) / math.factorial(3))
check("Laguerre: <L_3^2, L_5^2>_w = 0", "(toolkit)",
      lag_inner(3, 5, 2.0), 0.0, abs_tol=1e-9)
check("Laguerre: L_2^1(x)=3-3x+x^2/2 at x=1.7", "(toolkit)",
      genlaguerre(2, 1.0, 1.7), 3 - 3 * 1.7 + 1.7**2 / 2)

# --- Kummer ---
check("1F1(a;a;x) = e^x", "(toolkit)", kummer_1f1(2.5, 2.5, 1.3), math.exp(1.3))
check("1F1(1;2;2x) = (e^{2x}-1)/(2x)", "(toolkit)",
      kummer_1f1(1.0, 2.0, 2 * 0.9), (math.exp(1.8) - 1) / 1.8)
# 1F1(-n; a+1; x) = n!/(a+1)_n * L_n^a(x)
poch = lambda a, n: math.gamma(a + n) / math.gamma(a)
check("1F1(-3;3;x) vs Laguerre L_3^2", "(toolkit)",
      kummer_1f1(-3.0, 3.0, 2.2),
      math.factorial(3) / poch(3.0, 3) * genlaguerre(3, 2.0, 2.2))

# --- Legendre / spherical harmonics ---
check("P_2^1(x) = -3x sqrt(1-x^2) at 0.4", "(toolkit)",
      assoc_legendre(2, 1, 0.4), -3 * 0.4 * math.sqrt(1 - 0.16))
# int_0^pi |Y_l^m|^2 * 2pi sin(theta) dtheta = 1
for l, m in [(0, 0), (1, 0), (2, 1), (3, 2)]:
    val = tanh_sinh(lambda th: sph_harm_real_theta(l, m, th) ** 2
                    * 2 * math.pi * math.sin(th), 0.0, math.pi)
    check(f"Y_{l}^{m} normalized on sphere", "(toolkit)", val, 1.0)

# --- linalg: complex linear algebra core (used by modular/kms/cocycle/spectral) ---
def md(A, B):
    return la.max_abs_diff(A, B)


# real symmetric eigensolver: eigenvalues of tridiag [2,-1;...] on 3 nodes
_S = [[2.0, -1.0, 0.0], [-1.0, 2.0, -1.0], [0.0, -1.0, 2.0]]
_lam, _ = la.real_sym_eig(_S)
check("linalg: real_sym_eig eigenvalues (2±√2, 2)", "(toolkit)",
      max(abs(a - b) for a, b in zip(sorted(_lam), sorted([2 - 2 ** .5, 2.0, 2 + 2 ** .5]))),
      0.0, abs_tol=1e-10)

# Hermitian [[2,i],[-i,3]] eigenvalues (5±√5)/2
_H = la.mat([[2.0, 1j], [-1j, 3.0]])
check("linalg: herm_eigvalues (5±√5)/2", "(toolkit)",
      max(abs(a - b) for a, b in zip(la.herm_eigvalues(_H),
          sorted([(5 - 5 ** .5) / 2, (5 + 5 ** .5) / 2]))), 0.0, abs_tol=1e-10)

# complex Hermitian eigenvectors: reconstruction, orthonormality, eigen-relation
_Heig = la.mat([[2.0, 1j, 0.0], [-1j, 3.0, 1.0], [0.0, 1.0, 1.5]])
_evs, _vcs = la.herm_eig(_Heig)
# ascending eigenvalues match the values-only routine
check("linalg: herm_eig eigenvalues match herm_eigvalues", "(toolkit)",
      max(abs(a - b) for a, b in zip(sorted(_evs), la.herm_eigvalues(_Heig))), 0.0, abs_tol=1e-9)
# orthonormality  ⟨u_i,u_j⟩ = δ_ij
_ortho = max(abs(sum(_vcs[i][k].conjugate() * _vcs[j][k] for k in range(3))
                   - (1.0 if i == j else 0.0)) for i in range(3) for j in range(3))
check("linalg: herm_eig vectors orthonormal", "(toolkit)", _ortho, 0.0, abs_tol=1e-9)
# eigen-relation  H u_k = λ_k u_k, and spectral reconstruction  H = Σ λ_k |u_k⟩⟨u_k|
_recon = la.zeros(3)
for _k in range(3):
    _Hu = la.matvec(_Heig, _vcs[_k])
    for _i in range(3):
        assert abs(_Hu[_i] - _evs[_k] * _vcs[_k][_i]) < 1e-8, "herm_eig eigen-relation"
        for _j in range(3):
            _recon[_i][_j] += _evs[_k] * _vcs[_k][_i] * _vcs[_k][_j].conjugate()
check("linalg: Σ λ_k |u_k⟩⟨u_k| = H (spectral reconstruction)", "(toolkit)",
      la.max_abs_diff(_recon, _Heig), 0.0, abs_tol=1e-8)
# degeneracy robustness: repeated eigenvalue (identity-like block) still yields an ON basis
_Hdeg = la.mat([[1.0, 0.0, 0.0], [0.0, 1.0, 0.0], [0.0, 0.0, 4.0]])
_edeg, _vdeg = la.herm_eig(_Hdeg)
_odeg = max(abs(sum(_vdeg[i][k].conjugate() * _vdeg[j][k] for k in range(3))
                - (1.0 if i == j else 0.0)) for i in range(3) for j in range(3))
check("linalg: herm_eig orthonormal under degeneracy", "(toolkit)", _odeg, 0.0, abs_tol=1e-9)

# functional calculus: sqrt squares back, exp∘log = id, and herm_exp vs power series
check("linalg: (√H)² = H", "(toolkit)", md(la.matmul(la.herm_sqrt(_H), la.herm_sqrt(_H)), _H),
      0.0, abs_tol=1e-9)
check("linalg: exp(log H) = H", "(toolkit)", md(la.herm_exp(la.herm_log(_H)), _H), 0.0, abs_tol=1e-9)
check("linalg: herm_exp = truncated power series (independent route)", "(toolkit)",
      md(la.herm_exp(_H), la.expm_series(_H)), 0.0, abs_tol=1e-8)

# unitary flow e^{iKt} vs independent series; ρ^{it} group law
_K = la.mat([[0.5, 0.3 - 0.2j], [0.3 + 0.2j, -0.7]])
check("linalg: e^{iKt} = e^{itK} series (independent route)", "(toolkit)",
      md(la.herm_unitary_exp(_K, 0.9), la.expm_series(la.scale(0.9j, _K))), 0.0, abs_tol=1e-8)
_rho = la.density_from_seed(3, 7)
check("linalg: ρ^{it} unitary", "(toolkit)",
      1.0 if la.is_unitary(la.herm_pow_imag(_rho, 1.3)) else 0.0, 1.0)
check("linalg: ρ^{it}ρ^{is} = ρ^{i(t+s)} (group law)", "(toolkit)",
      md(la.matmul(la.herm_pow_imag(_rho, 1.3), la.herm_pow_imag(_rho, 0.4)),
         la.herm_pow_imag(_rho, 1.7)), 0.0, abs_tol=1e-9)

# inverse / determinant
_Amat = la.mat([[1, 2j, 0], [0, 1, 1], [1j, 0, 3]])
check("linalg: A·A⁻¹ = I", "(toolkit)", md(la.matmul(_Amat, la.inv(_Amat)), la.eye(3)),
      0.0, abs_tol=1e-9)
check("linalg: det(A)·det(A⁻¹) = 1", "(toolkit)",
      abs(la.det(_Amat) * la.det(la.inv(_Amat)) - 1), 0.0, abs_tol=1e-9)

# kron / partial trace: Tr_B(X⊗Y) = X·Tr(Y)
_X, _Y = la.mat([[1, 2], [3, 4]]), la.mat([[5, 0], [0, 1]])
check("linalg: partial_trace(X⊗Y) = X·Tr(Y)", "(toolkit)",
      md(la.partial_trace(la.kron(_X, _Y), (2, 2), 0), la.scale(la.trace(_Y), _X)),
      0.0, abs_tol=1e-12)

# singular values / trace norm: diag(3,-4i) ⇒ σ={3,4}, ‖·‖₁=7, ‖·‖₂=5
_D = la.mat([[3, 0], [0, -4j]])
check("linalg: trace_norm(diag(3,-4i)) = 7", "(toolkit)", la.trace_norm(_D), 7.0, abs_tol=1e-9)
check("linalg: hs_norm(diag(3,-4i)) = 5", "(toolkit)", la.hs_norm(_D), 5.0, abs_tol=1e-9)

# realification adjoint identity underpinning the modular checks:
#   Δ = S⋆S built from the antilinear graph  ==  ρ(·)ρ⁻¹  (the KEY route independence)
_n = 2
_r = la.density_from_seed(_n, 4)
_rh, _rih, _rinv = la.herm_sqrt(_r), la.herm_pow(_r, -0.5), la.inv(_r)
_P = la.transpose_perm(_n)
_AS = la.matmul(la.kron(la.transpose(_rh), _rih), la.mat(_P))     # S ξ = ρ^{-½}ξ⋆ρ^{½}
_SR = la.realify_antilinear(_AS)
_Delta_abs = la.unrealify_linear(la.real_matmul(la.real_transpose(_SR), _SR), _n * _n)
_Delta_clo = la.matmul(la.kron(la.eye(_n), _r), la.kron(la.transpose(_rinv), la.eye(_n)))
check("linalg: S⋆S (realified antilinear graph) = ρ(·)ρ⁻¹", "(toolkit)",
      md(_Delta_abs, _Delta_clo), 0.0, abs_tol=1e-8)

# rank / commutant dimension: commutant of full M_2(ℂ) is the scalars (dim 1)
_full = [la.mat([[1, 0], [0, 0]]), la.mat([[0, 1], [0, 0]]),
         la.mat([[0, 0], [1, 0]]), la.mat([[0, 0], [0, 1]])]
check("linalg: commutant_dim(M₂(ℂ)) = 1 (scalars)", "(toolkit)",
      la.commutant_dim(_full, 2), 1, abs_tol=0)

finish("nclib self-test")
