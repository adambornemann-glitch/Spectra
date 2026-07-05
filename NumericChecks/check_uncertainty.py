"""Numeric checks for uncertainty, Pauli algebra, Ehrenfest, unitarity/first-law,
tensor cross-norm, and the quantum (RLD/SLD) Fisher structure.

Subsystems: Spectra/QuantumMechanics/Uncertainty/, PauliMatrices.lean,
Ehrenfest.lean, Unitarity/, InformationGeometry/CramerRao/Quantum.lean,
FisherModel.lean, Spaces/Tensor/Hilbert.lean.

The headline is the **Schrödinger-Robertson** inequality, which is strictly
stronger than Robertson:

    Var(A)·Var(B) ≥ ¼‖⟨ψ,[A,B]ψ⟩‖² + Cov(A,B)²        (Schrödinger)
    Var(A)·Var(B) ≥ ¼‖⟨ψ,[A,B]ψ⟩‖²                     (Robertson)

with  Cov(A,B) = ½Re⟨ψ,{A,B}ψ⟩ − ⟨A⟩⟨B⟩,  Var(A)=‖(A−⟨A⟩)ψ‖².  We use a state
where BOTH the commutator term and the covariance term are nonzero, so the two
bounds differ — the covariance term is genuine content, not decoration.  The
three RHS ingredients are computed by disjoint matrix paths (shifted-operator
norms; the commutator [A,B]ψ; the anticommutator {A,B}ψ).

The Pauli-algebra checks are *convention anchors*: they confirm the library's
stated relations (e.g. `[σ_x,σ_y]=2iσ_z`, not `−2i`) against the standard
representation `σ_x=[[0,1],[1,0]]` etc., rather than independent-route checks.
"""

import cmath
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nclib import linalg as la
from nclib.harness import check, check_le, finish

TOL = 1e-8
I = 1j

# Pauli matrices
sx = la.mat([[0, 1], [1, 0]])
sy = la.mat([[0, -1j], [1j, 0]])
sz = la.mat([[1, 0], [0, -1]])
I2 = la.eye(2)


def inner(u, v):
    """⟨u,v⟩ with conjugation on the FIRST slot (mathlib/physics convention)."""
    return sum(u[i].conjugate() * v[i] for i in range(len(u)))


def expect(Op, psi):
    return inner(psi, la.matvec(Op, psi)).real


def variance(Op, psi):
    """‖(Op−⟨Op⟩)ψ‖² via the shifted operator."""
    e = expect(Op, psi)
    shifted = la.sub(Op, la.scale(e, la.eye(len(psi))))
    v = la.matvec(shifted, psi)
    return sum(abs(c) ** 2 for c in v)


def covariance(A, B, psi):
    """½Re⟨ψ,{A,B}ψ⟩ − ⟨A⟩⟨B⟩."""
    anti = la.matvec(la.anticommutator(A, B), psi)
    return 0.5 * inner(psi, anti).real - expect(A, psi) * expect(B, psi)


# --------------------------------------------------------------------------
# Pauli algebra
# --------------------------------------------------------------------------
check("σ_x² = I", "PauliMatrices.lean:140 (pauliX_sq)",
      la.max_abs_diff(la.matmul(sx, sx), I2), 0.0, abs_tol=TOL)
check("σ_x⋆ = σ_x", "PauliMatrices.lean:101 (pauliX_hermitian)",
      la.max_abs_diff(la.dagger(sx), sx), 0.0, abs_tol=TOL)
check("[σ_x,σ_y] = 2i σ_z", "PauliMatrices.lean:194 (pauliXY_commutator)",
      la.max_abs_diff(la.commutator(sx, sy), la.scale(2 * I, sz)), 0.0, abs_tol=TOL)
check("{σ_x,σ_y} = 0", "PauliMatrices.lean:170 (pauliXY_anticommute)",
      la.max_abs_diff(la.anticommutator(sx, sy), la.zeros(2)), 0.0, abs_tol=TOL)

# --------------------------------------------------------------------------
# Schrödinger-Robertson uncertainty (the stronger bound) and Robertson
# --------------------------------------------------------------------------
# state with nonzero commutator AND covariance:  ψ = (cos a, e^{ib} sin a)
a_ang, b_ang = 0.7, 1.1
psi = [math.cos(a_ang), cmath.exp(I * b_ang) * math.sin(a_ang)]
# observables (Hermitian, not commuting, not anticommuting)
A = la.add(sx, la.scale(0.6, sz))
B = la.add(sy, la.scale(0.4, sx))

varA, varB = variance(A, psi), variance(B, psi)
comm_vec = la.matvec(la.commutator(A, B), psi)                 # [A,B]ψ  (Route: commutator)
comm_term = 0.25 * abs(inner(psi, comm_vec)) ** 2
cov = covariance(A, B, psi)                                    # (Route: anticommutator)

check_le("Robertson: Var(A)Var(B) ≥ ¼|⟨ψ,[A,B]ψ⟩|²",
         "Uncertainty/SchrodingerRobertson.lean:251 (robertson_uncertainty)",
         comm_term, varA * varB, slack=1e-12)
check_le("Schrödinger-Robertson: Var(A)Var(B) ≥ ¼|⟨[A,B]⟩|² + Cov²",
         "Uncertainty/SchrodingerRobertson.lean:194 (schrodinger_uncertainty)",
         comm_term + cov ** 2, varA * varB, slack=1e-12)
# SHARP: a pure qubit state SATURATES Schrödinger-Robertson (ΔAψ, ΔBψ both ⟂ ψ,
# hence colinear in ℂ²), so equality holds exactly — pinning the ¼ and Cov² coeffs.
check("Schrödinger-Robertson SATURATED at pure qubit: Var(A)Var(B) = ¼|⟨[A,B]⟩|²+Cov²",
      "Uncertainty/SchrodingerRobertson.lean:194 (schrodinger_uncertainty, sharpness)",
      varA * varB, comm_term + cov ** 2, rel_tol=1e-9)
# the covariance term is genuine: Schrödinger bound strictly exceeds Robertson bound
check_le("Cov² > 0  ⇒ Schrödinger bound strictly stronger than Robertson",
         "Uncertainty/SchrodingerRobertson.lean:119 (covariance nonzero)",
         -(cov ** 2), -1e-3, slack=0)
# variance cross-check: ‖(A−⟨A⟩)ψ‖² == ⟨A²⟩ − ⟨A⟩²
varA_alt = expect(la.matmul(A, A), psi) - expect(A, psi) ** 2
check("Var(A) = ⟨A²⟩ − ⟨A⟩²  (two routes)",
      "Uncertainty/SchrodingerRobertson.lean (variance)", varA, varA_alt, rel_tol=1e-9)

# --------------------------------------------------------------------------
# Ehrenfest:  d/dt⟨ψ(t),Bψ(t)⟩ = ⟨iAψ,Bψ⟩ + ⟨ψ,B(iAψ)⟩,  U(t)=e^{itA}
# --------------------------------------------------------------------------
Ah = la.hermitian_from_seed(2, 3)          # generator (Hermitian)
Bobs = la.hermitian_from_seed(2, 9)        # observable
psi0 = [1 / math.sqrt(2), 1j / math.sqrt(2)]
dt = 1e-6


def expectB_at(t):
    Ut = la.herm_unitary_exp(Ah, t)
    pt = la.matvec(Ut, psi0)
    return inner(pt, la.matvec(Bobs, pt))


lhs_ehr = (expectB_at(dt) - expectB_at(-dt)) / (2 * dt)         # FD derivative (real)
iApsi = la.matvec(la.scale(I, Ah), psi0)
rhs_ehr = inner(iApsi, la.matvec(Bobs, psi0)) + inner(psi0, la.matvec(Bobs, iApsi))
check("Ehrenfest d/dt⟨B⟩ = ⟨iAψ,Bψ⟩+⟨ψ,B iAψ⟩  (U=e^{itA})",
      "Ehrenfest.lean:49 (ehrenfest_theorem)", abs(lhs_ehr - rhs_ehr), 0.0, abs_tol=1e-6)

# --------------------------------------------------------------------------
# Unitarity / first law: energy expectation conserved; spectral measure invariant
# --------------------------------------------------------------------------
tt = 0.83
Utt = la.herm_unitary_exp(Ah, tt)
x = [0.6, 0.8j]
Ux = la.matvec(Utt, x)
lhs_en = inner(la.matvec(Ah, Ux), Ux)          # ⟪A(U(t)x), U(t)x⟫  (A in first slot, per Lean)
rhs_en = inner(la.matvec(Ah, x), x)            # ⟪Ax, x⟫
check("energy expectation conserved ⟨A U(t)x,U(t)x⟩ = ⟨Ax,x⟩",
      "Unitarity/FirstLawIff.lean:305 (energy_expectation_conserved)",
      abs(lhs_en - rhs_en), 0.0, abs_tol=1e-8)

# spectral measure invariance: ‖P(B)U(t)ψ‖² = ‖P(B)ψ‖²  (P = spectral projector of Ah)
# build spectral projector onto lowest eigenvalue via (Ah−λ_hi)/(λ_lo−λ_hi)
lams = la.herm_eigvalues(Ah)
lo, hi = min(lams), max(lams)
Pproj = la.scale(1.0 / (lo - hi), la.sub(Ah, la.scale(hi, I2)))    # = |lo⟩⟨lo|
Pproj = la.matmul(Pproj, Pproj)   # idempotent-ize (already a projector; harmless)
def normsq(v): return sum(abs(c) ** 2 for c in v)
lhs_sp = normsq(la.matvec(Pproj, la.matvec(Utt, psi0)))
rhs_sp = normsq(la.matvec(Pproj, psi0))
# NOTE: only invariant because P commutes with U(t)=f(Ah). Verify commutation too.
check("spectral projector commutes with U(t): [P,U]=0",
      "Unitarity/FirstLawIff.lean:162 (borelMeasure_unitary_invariant)",
      la.max_abs_diff(la.commutator(Pproj, Utt), la.zeros(2)), 0.0, abs_tol=1e-9)
check("‖P U(t)ψ‖² = ‖Pψ‖²  (diagonal spectral measure invariant)",
      "Unitarity/FirstLawIff.lean:162 (borelMeasure_unitary_invariant)",
      abs(lhs_sp - rhs_sp), 0.0, abs_tol=1e-9)

# --------------------------------------------------------------------------
# Hilbert tensor cross-norm:  ‖x⊗y‖=‖x‖‖y‖,  ⟨x⊗y,x'⊗y'⟩=⟨x,x'⟩⟨y,y'⟩
# --------------------------------------------------------------------------
x1 = [1 + 1j, 0.0]
y1 = [1.0, 1.0]
xp = [1j, 1.0]
yp = [1.0, -1j]


def kron_vec(u, v):
    return [u[i] * v[j] for i in range(len(u)) for j in range(len(v))]


nx = math.sqrt(normsq(x1)); ny = math.sqrt(normsq(y1))
check("‖x⊗y‖ = ‖x‖·‖y‖ (Hilbert cross-norm)",
      "Spaces/Tensor/Hilbert.lean:172 (norm_tmul)",
      math.sqrt(normsq(kron_vec(x1, y1))), nx * ny, rel_tol=1e-12)
lhs_t = inner(kron_vec(x1, y1), kron_vec(xp, yp))
rhs_t = inner(x1, xp) * inner(y1, yp)
check("⟨x⊗y,x'⊗y'⟩ = ⟨x,x'⟩·⟨y,y'⟩",
      "Spaces/Tensor/Hilbert.lean:167 (inner_tmul_tmul)",
      abs(lhs_t - rhs_t), 0.0, abs_tol=1e-12)

# --------------------------------------------------------------------------
# Quantum Fisher (SLD/RLD): quantumMetric = 4·Cov PSD; RLD Pythagorean; bilinear bound
# --------------------------------------------------------------------------
# pure-state qubit ψ, observables O_1,O_2,O_3 = σ_x,σ_y,σ_z
Os = [sx, sy, sz]
psq = [math.cos(0.5), cmath.exp(0.9j) * math.sin(0.5)]


def Kcplx(i, j):
    """Complex quantum covariance K_ij = ⟨ψ, ΔO_i ΔO_j ψ⟩."""
    ei, ej = expect(Os[i], psq), expect(Os[j], psq)
    dOi = la.sub(Os[i], la.scale(ei, I2))
    dOj = la.sub(Os[j], la.scale(ej, I2))
    return inner(psq, la.matvec(la.matmul(dOi, dOj), psq))


g = [[Kcplx(i, j).real for j in range(3)] for i in range(3)]   # symmetric (SLD) part
om = [[Kcplx(i, j).imag for j in range(3)] for i in range(3)]  # antisymmetric (symplectic) part

# quantumMetric G = 4·Cov  is symmetric PSD  (route A: eigenvalues; route B: 4·Var(O_v)≥0)
G = [[4.0 * g[i][j] for j in range(3)] for i in range(3)]
Gc = la.mat(G)
gmin = min(la.herm_eigvalues(Gc))
check_le("quantumMetric G=4Cov positive-semidefinite (min eig ≥ 0)",
         "FisherModel.lean:211 (quantumMetric_posSemidef)", -gmin, 0.0, slack=1e-9)
# route B: for a random real v, 4·Var(O_v) = v^T G v ≥ 0
v3 = [0.8, -0.3, 0.5]
Ov = la.add(la.add(la.scale(v3[0], sx), la.scale(v3[1], sy)), la.scale(v3[2], sz))
quad = sum(v3[i] * G[i][j] * v3[j] for i in range(3) for j in range(3))
check("v^T G v = 4·Var(O_v)  (quantum metric = variance form)",
      "FisherModel.lean:211 (quantumMetric_posSemidef)",
      quad, 4.0 * variance(Ov, psq), rel_tol=1e-9)

# G symmetric, ω antisymmetric  ⇒  G^RLD = g + iω is Hermitian
herm_dev = max(abs(g[i][j] - g[j][i]) + abs(om[i][j] + om[j][i]) for i in range(3) for j in range(3))
check("RLD matrix G^RLD=g+iω Hermitian (g symmetric, ω antisymmetric)",
      "CramerRao/Quantum.lean:266 (rldMatrix_hermitian)", herm_dev, 0.0, abs_tol=1e-12)

# RLD Pythagorean: |g(v,w)+iω(v,w)|² = g(v,w)² + ω(v,w)²
vv, ww = [0.8, -0.3, 0.5], [-0.1, 1.2, 0.4]
gvw = sum(vv[i] * g[i][j] * ww[j] for i in range(3) for j in range(3))
ovw = sum(vv[i] * om[i][j] * ww[j] for i in range(3) for j in range(3))
check("RLD Pythagorean |G^RLD(v,w)|² = g(v,w)²+ω(v,w)²",
      "CramerRao/Quantum.lean:314 (rld_pythagorean)",
      abs(complex(gvw, ovw)) ** 2, gvw ** 2 + ovw ** 2, rel_tol=1e-12)

# Schrödinger bilinear bound: g(v,v)g(w,w) ≥ g(v,w)² + ω(v,w)²
gvv = sum(vv[i] * g[i][j] * vv[j] for i in range(3) for j in range(3))
gww = sum(ww[i] * g[i][j] * ww[j] for i in range(3) for j in range(3))
check_le("Schrödinger bilinear bound g(v,v)g(w,w) ≥ g(v,w)²+ω(v,w)²",
         "CramerRao/Quantum.lean:339 (schrodinger_bilin_bound)",
         gvw ** 2 + ovw ** 2, gvv * gww, slack=1e-12)

# weldMatrix content: the (real, symmetric, PSD) quantum metric factors as Rᵀ R
# (route: independent Cholesky) — validates weldMatrix_spec's Rᵀ R = quantumMetric
def cholesky_real(Mreal):
    nn = len(Mreal)
    Lc = [[0.0] * nn for _ in range(nn)]
    for i in range(nn):
        for j in range(i + 1):
            s = sum(Lc[i][kk] * Lc[j][kk] for kk in range(j))
            if i == j:
                Lc[i][j] = math.sqrt(max(0.0, Mreal[i][i] - s))
            else:
                Lc[i][j] = (Mreal[i][j] - s) / Lc[j][j] if Lc[j][j] > 1e-14 else 0.0
    return Lc


# add a tiny ridge for the rank-deficient pure-state metric so Cholesky is defined
Gr = [[G[i][j] + (1e-9 if i == j else 0.0) for j in range(3)] for i in range(3)]
Lc = cholesky_real(Gr)                                   # G = Lc Lcᵀ ; take R = Lcᵀ
R = [[Lc[j][i] for j in range(3)] for i in range(3)]     # Rᵀ = Lc
RtR = [[sum(R[kk][i] * R[kk][j] for kk in range(3)) for j in range(3)] for i in range(3)]
check("weldMatrix: Rᵀ R = quantumMetric G  (Cholesky factorization exists)",
      "FisherModel.lean:247 (weldMatrix_spec)",
      max(abs(RtR[i][j] - Gr[i][j]) for i in range(3) for j in range(3)), 0.0, abs_tol=1e-7)

finish("Uncertainty / Pauli / Ehrenfest / tensor / quantum-Fisher numeric checks")
