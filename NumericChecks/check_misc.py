"""Numeric checks for the remaining closed-form constants across the library.

Lean statements under test:
  chsh_expectation_algebraic_bound (BellsTheorem/CHSH_Bounds/CHSH_Basic.lean:403):
      |a b' - a b + a' b + a' b'| <= 2 for |a|,|a'|,|b|,|b'| <= 1
  tsirelson_bound (Tsirelson/Basic.lean:259): |<CHSH>| <= 2 sqrt 2, attained
  dichotomic_expectation_bound (CHSH_Basic.lean:317): |Tr(A rho)| <= 1
  kummerM_ode (Kummer.lean:41): z M'' + (b - z) M' - a M = 0
  kummerM growth (Kummer.lean:43): |M(a,b,rho)| >= C e^{rho/2} eventually
  diracMomentumOp_sq / _hermitian / _factor (DiracEquation/Dispersion.lean):
      D(p,m)^2 = (|p|^2+m^2) I,  D = D^dagger,  (D+E)(D-E) = 0
  heisenberg_uncertainty (Uncertainty/Heisenberg.lean:89): sigma_x sigma_p >= 1/2
      (hbar = 1), equality for Gaussians
  poissonKernel_fourier (Kernel/Poisson/Basic.lean:30):
      int P_eps(x) e^{ixt} dx = e^{-eps|t|},  P_eps(x) = (1/pi) eps/(x^2+eps^2)
  sphericalHarmonic_eigenvalue (SphericalHarmonics/Basic.lean:214):
      -Lap_sphere Y_l^m = l(l+1) Y_l^m
  sphericalHarmonic_orthonormal (SphericalHarmonics/Basic.lean:346)
"""

import cmath
import math
import random
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from nclib.quadrature import tanh_sinh, exp_sinh
from nclib.special import kummer_1f1, assoc_legendre, sph_harm_real_theta
from nclib.harness import check, check_le, finish

random.seed(20260702)

# ----------------------------------------------------------------------------
# tiny complex matrix helpers (lists of lists)
# ----------------------------------------------------------------------------
def mat_mul(A, B):
    n, k, m = len(A), len(B), len(B[0])
    return [[sum(A[i][t] * B[t][j] for t in range(k)) for j in range(m)]
            for i in range(n)]


def mat_add(A, B):
    return [[A[i][j] + B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mat_scale(c, A):
    return [[c * A[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mat_dagger(A):
    return [[A[j][i].conjugate() for j in range(len(A))] for i in range(len(A[0]))]


def mat_trace(A):
    return sum(A[i][i] for i in range(len(A)))


def kron(A, B):
    na, nb = len(A), len(B)
    return [[A[i // nb][j // nb] * B[i % nb][j % nb]
             for j in range(na * nb)] for i in range(na * nb)]


def eye(n):
    return [[complex(1.0) if i == j else complex(0.0) for j in range(n)]
            for i in range(n)]


SX = [[0, 1], [1, 0]]
SY = [[0, -1j], [1j, 0]]
SZ = [[1, 0], [0, -1]]
SX = [[complex(v) for v in row] for row in SX]
SY = [[complex(v) for v in row] for row in SY]
SZ = [[complex(v) for v in row] for row in SZ]

# ----------------------------------------------------------------------------
# 1. CHSH classical bound: corners and random points of [-1,1]^4
# ----------------------------------------------------------------------------
def S_alg(a, ap, b, bp):
    return abs(a * bp - a * b + ap * b + ap * bp)


corner_max = max(S_alg(a, ap, b, bp)
                 for a in (-1, 1) for ap in (-1, 1)
                 for b in (-1, 1) for bp in (-1, 1))
check("CHSH classical: max over corners = 2", "CHSH_Basic.lean:403",
      corner_max, 2.0)
rand_max = max(S_alg(*(random.uniform(-1, 1) for _ in range(4)))
               for _ in range(20000))
check_le("CHSH classical: 20000 random points <= 2", "CHSH_Basic.lean:403",
         rand_max, 2.0)

# ----------------------------------------------------------------------------
# 2. Tsirelson: spin observables A(t) = cos t Z + sin t X on the Bell state
#    |Phi+> = (|00> + |11>)/sqrt(2); S = <A B'> - <A B> + <A' B> + <A' B'>.
#    Optimal angles reach exactly 2 sqrt 2; grid search stays below.
# ----------------------------------------------------------------------------
def spin(t):
    return mat_add(mat_scale(math.cos(t), SZ), mat_scale(math.sin(t), SX))


phi_plus = [1 / math.sqrt(2), 0.0, 0.0, 1 / math.sqrt(2)]
rho_bell = [[phi_plus[i] * phi_plus[j] for j in range(4)] for i in range(4)]


def E(ta, tb):
    O = kron(spin(ta), spin(tb))
    return mat_trace(mat_mul(O, rho_bell)).real


def S_quantum(ta, tap, tb, tbp):
    return E(ta, tbp) - E(ta, tb) + E(tap, tb) + E(tap, tbp)


# A(0), A'(pi/2), B(3pi/4), B'(pi/4) is the textbook optimum for this pattern
S_opt = S_quantum(0.0, math.pi / 2, 3 * math.pi / 4, math.pi / 4)
check("Tsirelson: optimal angles give exactly 2 sqrt 2",
      "Tsirelson/Basic.lean:259 + QuantumCHSH/Violation.lean", S_opt,
      2.0 * math.sqrt(2.0), rel_tol=1e-12)
grid = [i * math.pi / 12 for i in range(24)]
S_max = max(abs(S_quantum(a, ap, b, bp))
            for a in grid for ap in grid for b in grid for bp in grid)
check_le("Tsirelson: grid search of 24^4 angle tuples <= 2 sqrt 2",
         "Tsirelson/Basic.lean:259", S_max, 2.0 * math.sqrt(2.0) + 1e-12)
check("Tsirelson: grid search attains 2 sqrt 2 (violates classical 2)",
      "Tsirelson/Basic.lean:259", S_max, 2.0 * math.sqrt(2.0), rel_tol=1e-9)

# dichotomic bound: |Tr(A rho)| <= 1 for A^2 = 1 and random pure rho
for _ in range(50):
    v = [complex(random.gauss(0, 1), random.gauss(0, 1)) for _ in range(2)]
    nrm = math.sqrt(sum(abs(z) ** 2 for z in v))
    v = [z / nrm for z in v]
    rho = [[v[i] * v[j].conjugate() for j in range(2)] for i in range(2)]
    t = random.uniform(0, 2 * math.pi)
    A = spin(t)
    val = abs(mat_trace(mat_mul(A, rho)))
    if val > 1.0 + 1e-12:
        check_le("dichotomic bound violated!", "CHSH_Basic.lean:317", val, 1.0)
        break
else:
    check_le("dichotomic |Tr(A rho)| <= 1 over 50 random (A, rho)",
             "CHSH_Basic.lean:317", 0.0, 1.0)
# and A(t)^2 = 1
Asq = mat_mul(spin(0.7), spin(0.7))
check("spin observable squares to identity", "CHSH_Basic.lean:317 (hA_sq)",
      max(abs(Asq[i][j] - eye(2)[i][j]) for i in range(2) for j in range(2)),
      0.0, abs_tol=1e-14)

# ----------------------------------------------------------------------------
# 3. Kummer ODE (Kummer.lean:41): z M'' + (b-z) M' - a M = 0, using the
#    contiguous-derivative identities M' = (a/b) M(a+1,b+1,-), etc.
# ----------------------------------------------------------------------------
for (a, b, z) in [(0.7, 1.9, 2.4), (0.7, 1.9, -3.1), (-3.0, 2.5, 1.7),
                  (2.2, 0.8, 5.0)]:
    M0 = kummer_1f1(a, b, z)
    M1 = a / b * kummer_1f1(a + 1, b + 1, z)
    M2 = a * (a + 1) / (b * (b + 1)) * kummer_1f1(a + 2, b + 2, z)
    resid = z * M2 + (b - z) * M1 - a * M0
    check(f"Kummer ODE residual at (a,b,z)=({a},{b},{z})",
          "Kummer.lean:41 (kummerM_ode)", resid, 0.0, abs_tol=1e-10)

# the same ODE by pure finite differences on the series itself, so the check
# does not share the contiguous-derivative identities with the residual
for (a, b, z) in [(0.7, 1.9, 2.4), (-3.0, 2.5, 1.7)]:
    h = 1e-3
    M = lambda t, a=a, b=b: kummer_1f1(a, b, t)
    M1 = (M(z + h) - M(z - h)) / (2 * h)
    M2 = (M(z + h) - 2 * M(z) + M(z - h)) / h ** 2
    resid = z * M2 + (b - z) * M1 - a * M(z)
    check(f"Kummer ODE by pure FD at (a,b,z)=({a},{b},{z})",
          "Kummer.lean:41 (kummerM_ode, identity-free route)",
          resid / max(abs(a * M(z)), 1.0), 0.0, abs_tol=1e-6)

# growth: |M(a,b,rho)| e^{-rho/2} increases without bound (non-terminating a)
vals = [abs(kummer_1f1(0.7, 1.9, rho)) * math.exp(-rho / 2.0)
        for rho in (10.0, 20.0, 30.0, 40.0)]
ok = all(vals[i] < vals[i + 1] for i in range(3)) and vals[0] > 1.0
check("Kummer growth: |M| e^{-rho/2} increasing and > 1 for rho >= 10",
      "Kummer.lean:43 (kummerM_abs_exp_lower)", 1.0 if ok else 0.0, 1.0)

# ----------------------------------------------------------------------------
# 4. Dirac dispersion (Dispersion.lean): Dirac representation
#    alpha_i = offdiag(sigma_i), beta = diag(1,1,-1,-1); D = p.alpha + m beta.
# ----------------------------------------------------------------------------
def dirac_D(p, m):
    Z2 = [[complex(0)] * 2 for _ in range(2)]
    alphas = []
    for S in (SX, SY, SZ):
        top = [Z2[0] + S[0], Z2[1] + S[1]]
        bot = [S[0] + Z2[0], S[1] + Z2[1]]
        alphas.append(top + bot)
    beta = [[complex(1 if i == j and i < 2 else (-1 if i == j else 0))
             for j in range(4)] for i in range(4)]
    D = mat_scale(m, beta)
    for i in range(3):
        D = mat_add(D, mat_scale(p[i], alphas[i]))
    return D


for (p, m) in [((0.3, -1.2, 0.7), 1.5), ((2.0, 0.0, -0.4), 0.0),
               ((0.0, 0.0, 0.0), 2.5)]:
    D = dirac_D(p, m)
    E2 = p[0] ** 2 + p[1] ** 2 + p[2] ** 2 + m ** 2
    Dsq = mat_mul(D, D)
    err_sq = max(abs(Dsq[i][j] - E2 * eye(4)[i][j])
                 for i in range(4) for j in range(4))
    check(f"D(p,m)^2 = (|p|^2+m^2) I for p={p}, m={m}",
          "Dispersion.lean:70 (diracMomentumOp_sq)", err_sq, 0.0, abs_tol=1e-13)
    Dd = mat_dagger(D)
    err_h = max(abs(D[i][j] - Dd[i][j]) for i in range(4) for j in range(4))
    check(f"D(p,m) Hermitian for p={p}, m={m}",
          "Dispersion.lean:84 (diracMomentumOp_hermitian)", err_h, 0.0,
          abs_tol=1e-14)
    Eval = math.sqrt(E2)
    plus = mat_add(D, mat_scale(Eval, eye(4)))
    minus = mat_add(D, mat_scale(-Eval, eye(4)))
    prod = mat_mul(plus, minus)
    err_f = max(abs(prod[i][j]) for i in range(4) for j in range(4))
    check(f"(D+E)(D-E) = 0 (mass shell) for p={p}, m={m}",
          "Dispersion.lean:117 (diracMomentumOp_factor)", err_f, 0.0,
          abs_tol=1e-12)

# ----------------------------------------------------------------------------
# 5. Heisenberg (Heisenberg.lean:89, hbar = 1): sigma_x sigma_p >= 1/2 with
#    equality for Gaussians. Var(p) = int psi'^2 for real normalized psi
#    with <x> = <p> = 0.
# ----------------------------------------------------------------------------
def uncertainty_product(psi, psi_p, lo, hi):
    nrm = tanh_sinh(lambda x: psi(x) ** 2, lo, hi, level=12)
    var_x = tanh_sinh(lambda x: x * x * psi(x) ** 2, lo, hi, level=12) / nrm
    var_p = tanh_sinh(lambda x: psi_p(x) ** 2, lo, hi, level=12) / nrm
    return math.sqrt(var_x * var_p)


for aa in [0.5, 1.0, 3.0]:
    up = uncertainty_product(lambda x: math.exp(-aa * x * x),
                             lambda x: -2 * aa * x * math.exp(-aa * x * x),
                             -12, 12)
    check(f"Gaussian (a={aa}): sigma_x sigma_p = 1/2 exactly",
          "Heisenberg.lean:89 (heisenberg_uncertainty, equality case)",
          up, 0.5, rel_tol=1e-9)

up1 = uncertainty_product(lambda x: x * math.exp(-x * x / 2),
                          lambda x: (1 - x * x) * math.exp(-x * x / 2),
                          -12, 12)
check("first excited state: sigma_x sigma_p = 3/2 >= 1/2",
      "Heisenberg.lean:89", up1, 1.5, rel_tol=1e-9)
for _ in range(5):
    c = random.uniform(0.2, 2.0)
    d = random.uniform(0.5, 3.0)
    psi = lambda x, c=c, d=d: (1 + c * x) * math.exp(-d * x * x)
    psi_p = lambda x, c=c, d=d: (c - 2 * d * x * (1 + c * x)) * math.exp(-d * x * x)
    nrm = tanh_sinh(lambda x: psi(x) ** 2, -12, 12)
    mean_x = tanh_sinh(lambda x: x * psi(x) ** 2, -12, 12) / nrm
    var_x = tanh_sinh(lambda x: (x - mean_x) ** 2 * psi(x) ** 2, -12, 12) / nrm
    var_p = tanh_sinh(lambda x: psi_p(x) ** 2, -12, 12) / nrm  # <p> = 0, psi real
    check_le(f"random state (c={c:.2f}, d={d:.2f}): sigma_x sigma_p >= 1/2",
             "Heisenberg.lean:89 / Heisenberg.lean:99 (variance form)",
             0.5, math.sqrt(var_x * var_p))

# ----------------------------------------------------------------------------
# 6. Poisson kernel Fourier transform (Kernel/Poisson/Basic.lean:30):
#    int (1/pi) eps/(x^2+eps^2) e^{ixt} dx = e^{-eps |t|}
# ----------------------------------------------------------------------------
def poisson(eps, x):
    return eps / (math.pi * (x * x + eps * eps))


# t = 0: total mass 1 (integrate exactly via x = eps tan u)
eps = 0.5
mass = tanh_sinh(lambda u: poisson(eps, eps * math.tan(u))
                 * eps / math.cos(u) ** 2, -math.pi / 2, math.pi / 2)
check("Poisson kernel total mass = 1 (t = 0)", "Kernel/Poisson/Basic.lean:30",
      mass, 1.0, rel_tol=1e-9)

# t != 0: oscillatory; panel-sum int_{-L}^{L} P(x) cos(t x) dx, tail ~ 2 eps/(pi L)
t = 1.0
L = 3000.0
npan = 600
panel = 2 * L / npan
val = sum(tanh_sinh(lambda x: poisson(eps, x) * math.cos(t * x),
                    -L + k * panel, -L + (k + 1) * panel, level=7)
          for k in range(npan))
check("Poisson Fourier at eps=0.5, t=1: = e^{-1/2}",
      "Kernel/Poisson/Basic.lean:30 (poissonKernel_fourier)",
      val, math.exp(-eps * abs(t)), rel_tol=5e-4)

# ----------------------------------------------------------------------------
# 7. Spherical harmonics: -Lap_sphere Y = l(l+1) Y via the theta-ODE
#    -(T'' + cot(th) T') + m^2 T / sin^2 th = l(l+1) T for T = P_l^m(cos th),
#    plus cross-orthonormality.
# ----------------------------------------------------------------------------
for (l, m) in [(3, 2), (5, 1), (4, 0)]:
    T = lambda th, l=l, m=m: assoc_legendre(l, m, math.cos(th))
    for th in [0.7, 1.3, 2.2]:
        h = 1e-4
        T2 = (T(th + h) - 2 * T(th) + T(th - h)) / h ** 2
        T1 = (T(th + h) - T(th - h)) / (2 * h)
        lhs = -(T2 + T1 / math.tan(th)) + m * m * T(th) / math.sin(th) ** 2
        check(f"-Lap_sphere P_{l}^{m} = l(l+1) P at theta={th}",
              "SphericalHarmonics/Basic.lean:214 (sphericalHarmonic_eigenvalue)",
              lhs / max(abs(T(th)), 1e-3), l * (l + 1) * T(th) / max(abs(T(th)), 1e-3),
              rel_tol=1e-4)

# orthogonality across l (same m): int_0^pi Th_lm Th_l'm sin th dth = 0
for (l, l2, m) in [(2, 3, 1), (1, 3, 0), (4, 2, 2)]:
    v = tanh_sinh(lambda th: sph_harm_real_theta(l, m, th)
                  * sph_harm_real_theta(l2, m, th)
                  * 2 * math.pi * math.sin(th), 0.0, math.pi)
    check(f"<Y_{l}^{m}, Y_{l2}^{m}> = 0",
          "SphericalHarmonics/Basic.lean:346 (sphericalHarmonic_orthonormal)",
          v, 0.0, abs_tol=1e-10)

finish("Misc constants: CHSH/Tsirelson, Kummer, Dirac, Heisenberg, Poisson, Y_lm")
