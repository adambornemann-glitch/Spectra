"""Numeric checks for Cayley transform, resolvent, Weyl criterion, generator
(Spectra/CayleyTransform/, Spectra/Resolvent/, Spectra/Operator/, Spectra/SpectralTheory/).

These are the classic i-sign / inverse-ordering / Möbius-direction traps.  The
Lean statements fix specific conventions:

  cayleyTransform      C = I − 2i(A + iI)⁻¹                (= (A−iI)(A+iI)⁻¹)
  apply_resolvent      C(Aψ + iψ) = Aψ − iψ
  one_minus_cayley     (I−C)(Aψ+iψ) = 2iψ,  (I+C)(Aψ+iψ) = 2Aψ
  eigenvalue corr.     μ ∈ σ(A) ⇔ (μ−i)/(μ+i) ∈ σ(C)
  neg-one iff          −1 ∈ σ(C) ⇔ 0 ∈ σ(A)
  resolvent_identity   R(z) − R(w) = (z−w) R(z) R(w),   R(z) = (A − zI)⁻¹
  resolvent_adjoint    R(z)⋆ = R(z̄)
  generator            (U(t)ψ − ψ)/(it) → Aψ,   U(t) = e^{itA}
  Weyl criterion       λ ∈ σ(A) ⇔ ∃ unit ψₙ with ‖(A−λ)ψₙ‖ → 0

Model.  `A` a self-adjoint matrix (real spectrum).  Each side is computed by an
independent route: the literal Lean expression vs an eigen/Möbius/direct route.
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
I = 1j

# --------------------------------------------------------------------------
# Self-adjoint operator A
# --------------------------------------------------------------------------
nn = 4
A = la.hermitian_from_seed(nn, 42)
Id = la.eye(nn)
eigs_A = sorted(la.herm_eigvalues(A))


def resolvent(z):
    """R(z) = (A − zI)⁻¹."""
    return la.inv(la.sub(A, la.scale(z, Id)))


# --------------------------------------------------------------------------
# Cayley transform  C = I − 2i(A+iI)⁻¹   (Route A: literal;  Route B: (A−i)(A+i)⁻¹)
# --------------------------------------------------------------------------
ApiInv = la.inv(la.add(A, la.scale(I, Id)))
C = la.sub(Id, la.scale(2 * I, ApiInv))                       # literal Lean definition
C_prod = la.matmul(la.sub(A, la.scale(I, Id)), ApiInv)        # (A−iI)(A+iI)⁻¹
check("Cayley C = I−2i(A+iI)⁻¹ = (A−iI)(A+iI)⁻¹",
      "CayleyTransform/Defs.lean:32 (cayleyTransform)",
      la.max_abs_diff(C, C_prod), 0.0, abs_tol=TOL)

# C is unitary and an isometry
check("Cayley C unitary: C⋆C = I",
      "CayleyTransform/Defs.lean:72 (cayleyTransform_unitary)",
      la.max_abs_diff(la.matmul(la.dagger(C), C), Id), 0.0, abs_tol=TOL)
check("Cayley C isometry: singular values all = 1",
      "CayleyTransform/Defs.lean:48 (cayleyTransform_isometry)",
      max(abs(s - 1.0) for s in la.singular_values(C)), 0.0, abs_tol=1e-8)

# C(Aψ + iψ) = Aψ − iψ
psi = [complex((i * 5 % 7) - 3, (i * 2 % 5) - 2) for i in range(nn)]
Apsi = la.matvec(A, psi)
lhs = la.matvec(C, [Apsi[i] + I * psi[i] for i in range(nn)])
rhs = [Apsi[i] - I * psi[i] for i in range(nn)]
check("C(Aψ+iψ) = Aψ−iψ", "CayleyTransform/Defs.lean:38 (cayleyTransform_apply_resolvent)",
      max(abs(lhs[i] - rhs[i]) for i in range(nn)), 0.0, abs_tol=TOL)

# (I−C)(Aψ+iψ) = 2iψ  and  (I+C)(Aψ+iψ) = 2Aψ
phi = [Apsi[i] + I * psi[i] for i in range(nn)]
ImC = la.matvec(la.sub(Id, C), phi)
IpC = la.matvec(la.add(Id, C), phi)
check("(I−C)(Aψ+iψ) = 2iψ", "CayleyTransform/Inverse.lean:30 (one_minus_cayley_apply)",
      max(abs(ImC[i] - 2 * I * psi[i]) for i in range(nn)), 0.0, abs_tol=TOL)
check("(I+C)(Aψ+iψ) = 2Aψ", "CayleyTransform/Inverse.lean:41 (one_plus_cayley_apply)",
      max(abs(IpC[i] - 2 * Apsi[i]) for i in range(nn)), 0.0, abs_tol=TOL)


# --------------------------------------------------------------------------
# Eigenvalue correspondence  μ∈σ(A) ⇔ (μ−i)/(μ+i)∈σ(C)  (Möbius)
# --------------------------------------------------------------------------
def mobius(mu):
    return (mu - I) / (mu + I)


# each real eigenvalue of A maps to an eigenvalue of C  (det(C − w I) = 0)
dets = [abs(la.det(la.sub(C, la.scale(mobius(mu), Id)))) for mu in eigs_A]
check("μ∈σ(A) ⇒ det(C − Möbius(μ)·I) = 0",
      "CayleyTransform/Eigenvalue.lean:79 (cayley_eigenvalue_correspondence)",
      max(dets), 0.0, abs_tol=1e-7)
# a non-image point on the unit circle is NOT in σ(C)
w_off = mobius(max(eigs_A) + 0.37)              # image of a non-eigenvalue → still on circle but ∉ σ(C)
check_le("point off σ(A)-image: det(C − w·I) ≠ 0",
         "CayleyTransform/Eigenvalue.lean:79 (correspondence, converse)",
         -abs(la.det(la.sub(C, la.scale(w_off, Id)))), -1e-4, slack=0)
# |Möbius(μ)| = 1 for real μ  (spectrum on unit circle)
check("|Möbius(μ)| = 1 for real μ  ⇒ σ(C) ⊆ unit circle",
      "CayleyTransform/Defs.lean:113 (cayleyTransform_spectrum_subset_circle)",
      max(abs(abs(mobius(mu)) - 1.0) for mu in eigs_A), 0.0, abs_tol=1e-12)

# −1 ∈ σ(C) ⇔ 0 ∈ σ(A)
# case 1: our A is invertible (0 ∉ σ), so −1 ∉ σ(C):
check_le("0∉σ(A) ⇒ −1∉σ(C):  det(C+I) ≠ 0",
         "CayleyTransform/Eigenvalue.lean:30 (cayley_neg_one_eigenvalue_iff)",
         -abs(la.det(la.add(C, Id))), -1e-4, slack=0)
# case 2: a singular A0 (0 ∈ σ) gives −1 ∈ σ(C0):
A0 = la.hermitian_from_seed(nn, 42)
lam0 = eigs_A[1]
A0 = la.sub(A0, la.scale(lam0, Id))              # shift so 0 is an eigenvalue
C0 = la.matmul(la.sub(A0, la.scale(I, Id)), la.inv(la.add(A0, la.scale(I, Id))))
check("0∈σ(A) ⇒ −1∈σ(C):  det(C₀+I) = 0",
      "CayleyTransform/Eigenvalue.lean:30 (cayley_neg_one_eigenvalue_iff)",
      abs(la.det(la.add(C0, Id))), 0.0, abs_tol=1e-7)

# --------------------------------------------------------------------------
# Resolvent identities
# --------------------------------------------------------------------------
z, w = complex(0.3, 0.5), complex(-0.4, 0.9)
Rz, Rw = resolvent(z), resolvent(w)
# R(z) − R(w) = (z−w) R(z) R(w)
lhs_ri = la.sub(Rz, Rw)
rhs_ri = la.scale(z - w, la.matmul(Rz, Rw))
check("resolvent identity R(z)−R(w) = (z−w)R(z)R(w)",
      "Resolvent/Identities.lean:59 (resolvent_identity)",
      la.max_abs_diff(lhs_ri, rhs_ri), 0.0, abs_tol=1e-7)
# R(z)⋆ = R(z̄)
check("resolvent adjoint R(z)⋆ = R(z̄)",
      "Resolvent/Identities.lean:234 (resolvent_adjoint)",
      la.max_abs_diff(la.dagger(Rz), resolvent(z.conjugate())), 0.0, abs_tol=1e-8)
# resolvent tendsto bound  ‖R(zₙ)ξ − R(z)ξ‖ ≤ |zₙ−z|·(1/|Im zₙ|)·‖R(z)ξ‖  (via identity)
zn = z + 0.05 + 0.02j
xi = [complex(1, -1), complex(0, 2), complex(-1, 0), complex(0.5, 0.5)]
Rz_xi = la.matvec(resolvent(z), xi)
diff_xi = [la.matvec(resolvent(zn), xi)[i] - Rz_xi[i] for i in range(nn)]
lhs_norm = math.sqrt(sum(abs(v) ** 2 for v in diff_xi))
bound = abs(zn - z) * (1.0 / abs(zn.imag)) * math.sqrt(sum(abs(v) ** 2 for v in Rz_xi))
check_le("resolvent continuity bound ‖ΔRξ‖ ≤ |Δz|/|Im zₙ|·‖R(z)ξ‖",
         "Resolvent/Identities.lean:137 (resolvent_tendsto)", lhs_norm, bound, slack=1e-9)

# Neumann series  Σ_{k=0}^∞ Tᵏ = (I−T)⁻¹  for ‖T‖ < 1
T = la.scale(0.3, la.hermitian_from_seed(nn, 7))
T = la.scale(0.4 / la.op_norm(T), T)             # ensure ‖T‖ ≈ 0.4 < 1
partial = la.eye(nn)
term = la.eye(nn)
for _ in range(60):
    term = la.matmul(term, T)
    partial = la.add(partial, term)
check("Neumann series Σ Tᵏ = (I−T)⁻¹ (‖T‖<1)",
      "Resolvent/Defs.lean:82 (neumannSeries)",
      la.max_abs_diff(partial, la.inv(la.sub(Id, T))), 0.0, abs_tol=1e-7)

# --------------------------------------------------------------------------
# Stone generator:  (U(t)ψ − ψ)/(it) → Aψ,  U(t)=e^{itA};  and resolvent match
# --------------------------------------------------------------------------
tt = 1e-5
Ut = la.herm_unitary_exp(A, tt)
gen_fd = [(la.matvec(Ut, psi)[i] - psi[i]) / (I * tt) for i in range(nn)]
check("generator (U(t)ψ−ψ)/(it) → Aψ,  U=e^{itA}",
      "OneParameterUnitaryGroup/Basic.lean:137 (generator)",
      max(abs(gen_fd[i] - Apsi[i]) for i in range(nn)), 0.0, abs_tol=1e-4)
# Stone: the generator's resolvent equals the operator resolvent (A−z)⁻¹.
# Route A: the group Laplace transform  R(z) = −i ∫₀^∞ e^{−izt} U(t) dt  (Im z < 0),
#          U(t)=e^{itA} — a genuinely independent route through the unitary GROUP.
# Route B: the matrix inverse (A − zI)⁻¹.
zL = -1.5j                                        # Im z < 0 (fast enough decay to tame e^{itA})
_Ucache = {}
def U_of(t):
    if t not in _Ucache:
        _Ucache[t] = la.herm_unitary_exp(A, t)
    return _Ucache[t]
def laplace_entry(p, q):
    integ = exp_sinh(lambda t: cmath.exp(-1j * zL * t) * U_of(t)[p][q], level=10)
    return -1j * integ
R_laplace = [[laplace_entry(p, q) for q in range(nn)] for p in range(nn)]
check("Stone: R(z) = −i∫₀^∞e^{−izt}U(t)dt = (A−z)⁻¹  (group vs inverse)",
      "CayleyTransform/Generator/Stone.lean:48 (generator_resolvent_eq_selfAdjoint)",
      la.max_abs_diff(R_laplace, la.inv(la.sub(A, la.scale(zL, Id)))), 0.0, abs_tol=1e-8)

# --------------------------------------------------------------------------
# Weyl criterion:  λ∈σ(A) ⇔ ∃ unit ψₙ, ‖(A−λ)ψₙ‖→0
#   finite self-adjoint:  min over unit ψ of ‖(A−λ)ψ‖ = dist(λ, σ(A))
# --------------------------------------------------------------------------
# for an eigenvalue λ: the smallest singular value of A−λI is 0 (Weyl seq exact)
lam = eigs_A[2]
smin_eig = min(la.singular_values(la.sub(A, la.scale(lam, Id))))
check("λ∈σ(A): min‖(A−λ)ψ‖ = 0 (Weyl sequence exists)",
      "Operator/WeylCriterion.lean:93 (mem_spectrum_iff_exists_weylSequence)",
      smin_eig, 0.0, abs_tol=1e-7)
# for a non-spectral point: min‖(A−μ)ψ‖ = dist(μ,σ) > 0
mu_gap = (eigs_A[0] + eigs_A[1]) / 2             # midpoint between two eigenvalues
smin_gap = min(la.singular_values(la.sub(A, la.scale(mu_gap, Id))))
dist = min(abs(mu_gap - e) for e in eigs_A)
check("μ∉σ(A): min‖(A−μ)ψ‖ = dist(μ,σ(A)) > 0  (no Weyl sequence)",
      "Operator/WeylCriterion.lean:93 (mem_spectrum_iff_exists_weylSequence)",
      smin_gap, dist, rel_tol=1e-7)

finish("Cayley / resolvent / Weyl / generator numeric checks")
