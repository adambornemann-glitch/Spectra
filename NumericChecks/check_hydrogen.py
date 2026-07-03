"""Numeric checks for the hydrogen tower.

Every `lean_*` function below is a literal transcription of a Lean definition
(file:line cited next to it). The checks then verify, in double precision,
that the *statements* of the theorems hold numerically — guarding against
wrong constants / signs / normalizations that a correct proof of a wrong
statement would not catch.

Conventions under test (atomic units, Z = 1 where the eigenfunctions live):
  H = -1/2 Δ - 1/r,   E_n = -1/(2 n^2)
  R_{nl}(r) = N_{nl} (2r/n)^l e^{-r/n} L_{n-l-1}^{2l+1}(2r/n)
"""

import cmath
import math
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from nclib.quadrature import tanh_sinh, exp_sinh
from nclib.special import genlaguerre, genlaguerre_deriv
from nclib.harness import check, finish


# ----------------------------------------------------------------------------
# Literal transcriptions of the Lean definitions
# ----------------------------------------------------------------------------

def real_binom(alpha, k):
    """Laguerre/Orthogonality.lean:55  realBinom a k = (prod_{i<k} (a-i)) / k!"""
    prod = 1.0
    for i in range(k):
        prod *= (alpha - i)
    return prod / math.factorial(k)


def lean_laguerre(n, alpha, x):
    """Laguerre/Orthogonality.lean:74  L_n^a(x) = sum_k (-1)^k C(n+a, n-k) x^k/k!"""
    return sum(
        (-1.0) ** k * real_binom(n + alpha, n - k) * x ** k / math.factorial(k)
        for k in range(n + 1)
    )


def lean_laguerre_weight(alpha, x):
    """Laguerre/Orthogonality.lean:502  w(x) = x^a e^{-x} on (0,inf)"""
    return x ** alpha * math.exp(-x) if x > 0 else 0.0


def lean_radial_norm(n, l):
    """Equation/Eigenfunctions.lean:101
    N = sqrt((2/n)^3 * (n-l-1)! / (2n * (n+l)!))"""
    return math.sqrt(
        (2.0 / n) ** 3 * math.factorial(n - l - 1) / (2.0 * n * math.factorial(n + l))
    )


def lean_R(n, l, r):
    """Equation/Eigenfunctions.lean:115
    R_{nl}(r) = N * (2r/n)^l * e^{-r/n} * L_{n-l-1}^{2l+1}(2r/n)"""
    return (
        lean_radial_norm(n, l)
        * (2.0 * r / n) ** l
        * math.exp(-r / n)
        * lean_laguerre(n - l - 1, 2 * l + 1, 2.0 * r / n)
    )


def lean_eigenvalue(n):
    """Equation/Eigenfunctions.lean:52  E_n = -1/(2 n^2)"""
    return -1.0 / (2.0 * n ** 2)


def lean_eigenvalue_Z(Z, n):
    """Spectrum/Eigenvalue.lean:283  E_n = -Z^2/(2 n^2)"""
    return -(Z ** 2) / (2.0 * n ** 2)


# Analytic derivatives of R_{nl} (via dL_n^a/dx = -L_{n-1}^{a+1}, standard
# convention — validated against lean_laguerre in the first check block).
def R_derivs(n, l, r):
    """Return (R, R', R'') at r > 0."""
    N = lean_radial_norm(n, l)
    c = 2.0 / n
    u = c * r
    m = n - l - 1
    a = 2 * l + 1
    L0 = genlaguerre(m, a, u)
    L1 = -genlaguerre(m - 1, a + 1, u) if m >= 1 else 0.0
    L2 = genlaguerre(m - 2, a + 2, u) if m >= 2 else 0.0
    P0 = u ** l
    P1 = l * u ** (l - 1) if l >= 1 else 0.0
    P2 = l * (l - 1) * u ** (l - 2) if l >= 2 else 0.0
    E0 = math.exp(-u / 2.0)
    E1 = -0.5 * E0
    E2 = 0.25 * E0
    f0 = P0 * L0 * E0
    f1 = P1 * L0 * E0 + P0 * L1 * E0 + P0 * L0 * E1
    f2 = (P2 * L0 * E0 + P0 * L2 * E0 + P0 * L0 * E2
          + 2.0 * (P1 * L1 * E0 + P1 * L0 * E1 + P0 * L1 * E1))
    return N * f0, N * c * f1, N * c * c * f2


def radial_hamiltonian(n, l, r):
    """Equation/Eigenfunctions.lean:137
    (H_l R)(r) = -1/2 R'' - (1/r) R' + (l(l+1)/(2r^2)) R - (1/r) R"""
    R0, R1, R2 = R_derivs(n, l, r)
    return -0.5 * R2 - R1 / r + (l * (l + 1) / (2.0 * r * r)) * R0 - R0 / r


# ----------------------------------------------------------------------------
# 1. Laguerre convention: Lean's explicit sum == standard recurrence
# ----------------------------------------------------------------------------
for (n, a, x) in [(0, 1.0, 0.7), (1, 3.0, 2.1), (3, 5.0, 0.9), (5, 2.5, 4.2),
                  (4, 3.0, 11.0), (6, 7.0, 1.3)]:
    check(f"laguerrePolynomial {n} {a} at x={x} == standard L_n^a",
          "Laguerre/Orthogonality.lean:74 (laguerrePolynomial)",
          lean_laguerre(n, a, x), genlaguerre(n, a, x), rel_tol=1e-12)

# laguerre_one: L_1^a(x) = 1 + a - x   (Orthogonality.lean:83)
check("laguerre_one: L_1^a = 1 + a - x", "Laguerre/Orthogonality.lean:83",
      lean_laguerre(1, 2.7, 1.4), 1 + 2.7 - 1.4, rel_tol=1e-14)

# ----------------------------------------------------------------------------
# 2. laguerre_recurrence (Orthogonality.lean:177):
#    (n+1) L_{n+1} = (2n+a+1-x) L_n - (n+a) L_{n-1}
# ----------------------------------------------------------------------------
for (n, a, x) in [(1, 3.0, 2.2), (3, 1.0, 0.5), (5, 4.5, 7.7)]:
    lhs = (n + 1) * lean_laguerre(n + 1, a, x)
    rhs = (2 * n + a + 1 - x) * lean_laguerre(n, a, x) \
        - (n + a) * lean_laguerre(n - 1, a, x)
    check(f"laguerre_recurrence n={n} a={a} x={x}",
          "Laguerre/Orthogonality.lean:177", lhs, rhs, rel_tol=1e-12)

# ----------------------------------------------------------------------------
# 3. laguerre_differential_eq (Orthogonality.lean:383):
#    x L'' + (a+1-x) L' + n L = 0
# ----------------------------------------------------------------------------
for (n, a, x) in [(2, 3.0, 1.1), (4, 1.0, 3.3), (5, 2.0, 8.0)]:
    L0 = genlaguerre(n, a, x)
    L1 = -genlaguerre(n - 1, a + 1, x)
    L2 = genlaguerre(n - 2, a + 2, x) if n >= 2 else 0.0
    resid = x * L2 + (a + 1 - x) * L1 + n * L0
    check(f"laguerre ODE residual n={n} a={a} x={x}",
          "Laguerre/Orthogonality.lean:383", resid, 0.0, abs_tol=1e-10)

# ----------------------------------------------------------------------------
# 4. laguerre_orthogonality (Orthogonality.lean:728):
#    int_0^inf x^a e^{-x} L_n L_m = 0  (n != m); diagonal = Gamma(n+a+1)/n!
# ----------------------------------------------------------------------------
for (n, m, a) in [(1, 3, 2.0), (2, 4, 1.0), (0, 5, 3.0), (2, 3, 0.5)]:
    val = exp_sinh(lambda x: lean_laguerre_weight(a, x)
                   * lean_laguerre(n, a, x) * lean_laguerre(m, a, x))
    check(f"laguerre_orthogonality n={n} m={m} a={a}",
          "Laguerre/Orthogonality.lean:728", val, 0.0, abs_tol=1e-8)
for (n, a) in [(2, 2.0), (4, 1.0)]:
    val = exp_sinh(lambda x: lean_laguerre_weight(a, x)
                   * lean_laguerre(n, a, x) ** 2)
    check(f"laguerre diagonal norm n={n} a={a} = Gamma(n+a+1)/n!",
          "(convention check for Orthogonality.lean weight)",
          val, math.gamma(n + a + 1) / math.factorial(n), rel_tol=1e-9)

# ----------------------------------------------------------------------------
# 5. Radial normalization: int_0^inf R_{nl}^2 r^2 dr = 1
#    (diagonal of hydrogen_eigenfunction_orthonormal, Spectrum/Eigenvalue.lean:472)
# ----------------------------------------------------------------------------
for (n, l) in [(1, 0), (2, 0), (2, 1), (3, 1), (4, 2), (5, 0), (5, 4)]:
    val = exp_sinh(lambda r: lean_R(n, l, r) ** 2 * r * r, level=11)
    check(f"int R_{{{n}{l}}}^2 r^2 dr = 1",
          "Eigenfunctions.lean:101+115 / Spectrum/Eigenvalue.lean:472",
          val, 1.0, rel_tol=1e-9)

# ----------------------------------------------------------------------------
# 6. Radial orthogonality (Eigenfunctions.lean:771): n != n', same l
# ----------------------------------------------------------------------------
for (n, n2, l) in [(1, 2, 0), (2, 3, 0), (2, 3, 1), (3, 5, 2)]:
    val = exp_sinh(lambda r: lean_R(n, l, r) * lean_R(n2, l, r) * r * r, level=11)
    check(f"int R_{{{n}{l}}} R_{{{n2}{l}}} r^2 dr = 0",
          "Eigenfunctions.lean:771 (radial_wavefunction_orthonormal)",
          val, 0.0, abs_tol=1e-9)

# ----------------------------------------------------------------------------
# 7. Radial eigenvalue equation (Eigenfunctions.lean:393):
#    H_l R_{nl} = E_n R_{nl} pointwise, E_n = -1/(2n^2)
# ----------------------------------------------------------------------------
for (n, l) in [(1, 0), (2, 0), (2, 1), (3, 1), (4, 2), (5, 3)]:
    En = lean_eigenvalue(n)
    for r in [0.31, 1.0, 2.7, 6.5]:
        lhs = radial_hamiltonian(n, l, r)
        rhs = En * lean_R(n, l, r)
        scale = max(abs(lean_R(n, l, r)), 1e-3)  # avoid node zeros
        check(f"(H_{l} R_{{{n}{l}}})(r={r}) = E_{n} R (E={En})",
              "Eigenfunctions.lean:137+393 (radial_eigenvalue_eq)",
              lhs / scale, rhs / scale, rel_tol=1e-8, abs_tol=1e-9)

# ----------------------------------------------------------------------------
# 8. Energy by quadrature (independent of the ODE): with chi = r R,
#    <T> = 1/2 int (chi'^2 + l(l+1) chi^2/r^2) dr,  <V> = -int chi^2/r dr,
#    <T> + <V> = E_n  and virial  <T> = -E_n, <V> = 2 E_n.
# ----------------------------------------------------------------------------
for (n, l) in [(1, 0), (2, 1), (3, 0), (4, 3)]:
    def chi(r, n=n, l=l):
        return r * lean_R(n, l, r)

    def chi_p(r, n=n, l=l):
        R0, R1, _ = R_derivs(n, l, r)
        return R0 + r * R1

    T = 0.5 * exp_sinh(lambda r: chi_p(r) ** 2
                       + l * (l + 1) * chi(r) ** 2 / r ** 2, level=11)
    V = -exp_sinh(lambda r: chi(r) ** 2 / r, level=11)
    En = lean_eigenvalue(n)
    check(f"<T>+<V> for (n,l)=({n},{l}) = E_{n} = {En}",
          "Hamiltonian.lean:55 (H = -1/2 Lap - 1/r), Eigenfunctions.lean:52",
          T + V, En, rel_tol=1e-8)
    check(f"virial <T> = -E_{n} for (n,l)=({n},{l})",
          "(consequence of H = -1/2 Lap - 1/r)", T, -En, rel_tol=1e-8)

# ----------------------------------------------------------------------------
# 9. Ground state, explicitly: R_10 = 2 e^{-r}, E_1 = -1/2
# ----------------------------------------------------------------------------
check("R_10(r) = 2 e^{-r} at r=1.3", "Eigenfunctions.lean:115 (n=1,l=0)",
      lean_R(1, 0, 1.3), 2.0 * math.exp(-1.3), rel_tol=1e-13)
check("E_1 = -1/2 (ground state, -13.6 eV)", "Eigenfunctions.lean:52",
      lean_eigenvalue(1), -0.5)

# ----------------------------------------------------------------------------
# 10. Bohr formula (BohrFormula.lean:63): E_n - E_m = Z^2/2 (1/m^2 - 1/n^2)
#     Balmer (BohrFormula.lean:80): E_n - E_2 = 1/2 (1/4 - 1/n^2)
# ----------------------------------------------------------------------------
for (Z, n, m) in [(1.0, 3, 2), (2.0, 5, 1), (1.0, 7, 4)]:
    check(f"Bohr: E_{n}-E_{m} (Z={Z})", "BohrFormula.lean:63",
          lean_eigenvalue_Z(Z, n) - lean_eigenvalue_Z(Z, m),
          Z ** 2 / 2 * (1.0 / m ** 2 - 1.0 / n ** 2), rel_tol=1e-14)
check("Balmer n=3 (H-alpha): E_3-E_2 = 1/2(1/4-1/9)", "BohrFormula.lean:80",
      lean_eigenvalue(3) - lean_eigenvalue(2), 0.5 * (0.25 - 1.0 / 9.0),
      rel_tol=1e-14)

# ----------------------------------------------------------------------------
# 11. Boundary behavior (Eigenfunctions.lean:631):
#     chi_{nl}(r)/r^{l+1} -> N (2/n)^l L_{n-l-1}^{2l+1}(0) as r -> 0+
# ----------------------------------------------------------------------------
for (n, l) in [(2, 1), (3, 0), (4, 2)]:
    r = 1e-8
    got = (r * lean_R(n, l, r)) / r ** (l + 1)
    want = lean_radial_norm(n, l) * (2.0 / n) ** l \
        * lean_laguerre(n - l - 1, 2 * l + 1, 0.0)
    check(f"chi_{{{n}{l}}}/r^{l+1} -> N (2/n)^l L(0)",
          "Eigenfunctions.lean:631 (radial_boundary_r_zero)",
          got, want, rel_tol=1e-6)

# ----------------------------------------------------------------------------
# 12. Free Green's function G_z(x) = e^{-sqrt(-z)|x|}/(4 pi |x|)
#     (FreeGreens/Basic.lean:75)
# ----------------------------------------------------------------------------
kappa = 1.7
z = -kappa ** 2


def G(r):
    return math.exp(-kappa * r) / (4.0 * math.pi * r)


# (a) Helmholtz equation away from origin: -Lap G - z G = 0,
#     radial Lap = d^2/dr^2 + (2/r) d/dr; finite differences.
for r in [0.5, 1.0, 3.0]:
    h = 1e-4
    G2 = (G(r + h) - 2 * G(r) + G(r - h)) / h ** 2
    G1 = (G(r + h) - G(r - h)) / (2 * h)
    resid = -(G2 + 2.0 * G1 / r) - z * G(r)
    check(f"(-Lap - z) G_z = 0 at r={r} (z={z})",
          "FreeGreens/Basic.lean:75 (freeGreensFunction)",
          resid / G(r), 0.0, abs_tol=1e-6)

# (b) total mass: int_R3 G_z dx = int_0^inf r e^{-kr} dr = 1/k^2 = -1/z
check("int_R3 G_z dx = -1/z", "FreeGreens/Basic.lean:75",
      exp_sinh(lambda r: r * math.exp(-kappa * r)), -1.0 / z, rel_tol=1e-10)

# (c) Laplace integral (FreeGreens/Basic.lean:35):
#     int_0^inf e^{-w r} sin(a r) dr = a/(w^2+a^2), complex w with Re w > 0
w = complex(1.5, 0.8)
a = 2.3
val = exp_sinh(lambda r: cmath.exp(-w * r) * math.sin(a * r))
expect = a / (w * w + a * a)
check("Laplace sin integral, real part", "FreeGreens/Basic.lean:35",
      val.real, expect.real, rel_tol=1e-9)
check("Laplace sin integral, imag part", "FreeGreens/Basic.lean:35",
      val.imag, expect.imag, rel_tol=1e-9)

# ----------------------------------------------------------------------------
# 13. Independence pass: the ODE checks in sections 3 and 7 lean on textbook
#     derivative identities (dL/dx = -L_{n-1}^{a+1}). Repeat them with pure
#     finite differences applied to the LITERAL Lean transcriptions, so no
#     hand calculus is shared between the two sides.
# ----------------------------------------------------------------------------
for (n, a, x) in [(3, 2.0, 1.7), (5, 4.0, 6.2)]:
    h = 1e-3
    L = lambda t, n=n, a=a: lean_laguerre(n, a, t)
    L1 = (L(x + h) - L(x - h)) / (2 * h)
    L2 = (L(x + h) - 2 * L(x) + L(x - h)) / h ** 2
    resid = x * L2 + (a + 1 - x) * L1 + n * L(x)
    check(f"laguerre ODE by pure FD on the Lean sum (n={n}, a={a}, x={x})",
          "Laguerre/Orthogonality.lean:74+383",
          resid / max(abs(n * L(x)), 1.0), 0.0, abs_tol=1e-6)

for (n, l, r) in [(2, 0, 1.3), (3, 1, 2.1), (4, 2, 5.0)]:
    h = 1e-3
    Rf = lambda t, n=n, l=l: lean_R(n, l, t)
    R1 = (Rf(r + h) - Rf(r - h)) / (2 * h)
    R2 = (Rf(r + h) - 2 * Rf(r) + Rf(r - h)) / h ** 2
    lhs = -0.5 * R2 - R1 / r + (l * (l + 1) / (2 * r * r)) * Rf(r) - Rf(r) / r
    check(f"radial ODE by pure FD on lean_R (n={n}, l={l}, r={r})",
          "Eigenfunctions.lean:115+137+393 (identity-free route)",
          lhs, lean_eigenvalue(n) * Rf(r), rel_tol=1e-4, abs_tol=1e-7)

# ----------------------------------------------------------------------------
# 14. External identity anchor for the r -> 0 boundary value:
#     L_m^a(0) = Gamma(m+a+1) / (Gamma(a+1) m!)
# ----------------------------------------------------------------------------
for (m, a) in [(1, 3.0), (3, 5.0), (4, 2.0)]:
    check(f"L_{m}^{a}(0) = Gamma(m+a+1)/(Gamma(a+1) m!)",
          "Laguerre/Orthogonality.lean:74 (value at 0 vs Gamma identity)",
          lean_laguerre(m, a, 0.0),
          math.gamma(m + a + 1) / (math.gamma(a + 1) * math.factorial(m)),
          rel_tol=1e-12)

# ----------------------------------------------------------------------------
# 15. Reality anchor: the Bohr checks in section 10 mirror an algebraic
#     identity, so tie the eigenvalue scale to a measured quantity instead.
#     E_3 - E_2 in Hartree -> eV -> nm must reproduce the H-alpha line at
#     656.11 nm (Bohr model, infinite nuclear mass, vacuum).
# ----------------------------------------------------------------------------
HARTREE_EV = 27.211386245988        # CODATA 2018
HC_EV_NM = 1239.8419843320026       # h c in eV nm
E_ha_eV = (lean_eigenvalue(3) - lean_eigenvalue(2)) * HARTREE_EV
check("H-alpha: hc/(E_3 - E_2) = 656.11 nm",
      "Eigenfunctions.lean:52 + BohrFormula.lean:80 (units anchor)",
      HC_EV_NM / E_ha_eV, 656.112, rel_tol=5e-5)

finish("Hydrogen tower: eigenvalues, eigenfunctions, Laguerre, Green's function")
