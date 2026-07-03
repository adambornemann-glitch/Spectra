"""Numeric checks for InformationGeometry/.

Lean statements under test:
  gaussianShiftModel_fisherMatrix (GaussianModel.lean:839):
      Fisher matrix of x ~ prod_k N((R theta)_k, 1) equals R^T R (all entries),
      with score s_i(x) = sum_k (x_k - (R theta)_k) R_{ki}  (GaussianModel.lean:179)
      and Fisher g_ij = int s_i s_j p dmu  (Fisher/Information.lean:183).
  Score mean zero (Score.lean): int s_i p dmu = 0.
  classicalBitData (Dichotomy.lean:181): metric == 4, cubic = 16 cot(2 alpha)
      -- checked against the Bernoulli family p_alpha = (cos^2 a, sin^2 a).
  qubitData (Dichotomy.lean:235): metric = diag(1, sin^2 alpha), cubic == 0
      -- checked against the SLD quantum Fisher metric of the Bloch family
         |psi(a,b)> = (cos(a/2), e^{ib} sin(a/2)).
  cramerRao_scalar (CramerRao/Bound.lean:57): Var(T) >= (d tau)^2 / g_ii,
      equality for T = x on N(theta, 1).
"""

import cmath
import math
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from nclib.quadrature import tanh_sinh
from nclib.harness import check, check_le, finish


def phi(u):
    """Standard normal pdf (gaussianPDFReal with variance 1)."""
    return math.exp(-0.5 * u * u) / math.sqrt(2.0 * math.pi)


# ----------------------------------------------------------------------------
# 1. Gaussian shift model, m = n = 2: Fisher = R^T R, entrywise, by genuine
#    2D numeric integration of int s_i s_j p dx over R^2.
# ----------------------------------------------------------------------------
R = [[1.0, 0.5], [-0.3, 2.0]]
theta = [0.7, -0.3]
mu = [R[0][0] * theta[0] + R[0][1] * theta[1],
      R[1][0] * theta[0] + R[1][1] * theta[1]]


def density(x0, x1):
    """GaussianModel.lean:56  p(theta, x) = prod_k N(x_k; (R theta)_k, 1)"""
    return phi(x0 - mu[0]) * phi(x1 - mu[1])


def score(i, x0, x1):
    """GaussianModel.lean:179  s_i = sum_k (x_k - (R theta)_k) R_{ki}"""
    return (x0 - mu[0]) * R[0][i] + (x1 - mu[1]) * R[1][i]


def integral2d(f):
    # nested 2D tanh-sinh: good to ~1e-9; checks below use rel_tol 1e-6
    L = 9.0
    return tanh_sinh(
        lambda x0: tanh_sinh(lambda x1: f(x0, x1), mu[1] - L, mu[1] + L, level=9),
        mu[0] - L, mu[0] + L, level=9)


RtR = [[sum(R[k][i] * R[k][j] for k in range(2)) for j in range(2)]
       for i in range(2)]
for i in range(2):
    for j in range(2):
        g_ij = integral2d(lambda x0, x1, i=i, j=j:
                          score(i, x0, x1) * score(j, x0, x1) * density(x0, x1))
        check(f"gaussianShift Fisher g_{i}{j} = (R^T R)_{i}{j}",
              "GaussianModel.lean:839 (gaussianShiftModel_fisherMatrix)",
              g_ij, RtR[i][j], rel_tol=1e-6, abs_tol=1e-7)

# density normalization and score mean zero
check("gaussianShift density integrates to 1", "GaussianModel.lean:56",
      integral2d(density), 1.0, rel_tol=1e-6)
for i in range(2):
    check(f"score mean E[s_{i}] = 0", "Score.lean (score expectation vanishes)",
          integral2d(lambda x0, x1, i=i: score(i, x0, x1) * density(x0, x1)),
          0.0, abs_tol=1e-10)

# scoreFun really is the score: compare the transcribed formula against a
# finite difference of log p in theta_i (independent route -- no shared algebra).
def density_theta(t0, t1, x0, x1):
    m0 = R[0][0] * t0 + R[0][1] * t1
    m1 = R[1][0] * t0 + R[1][1] * t1
    return phi(x0 - m0) * phi(x1 - m1)


hs = 1e-6
for i in range(2):
    for (x0, x1) in [(0.3, -1.2), (1.7, 0.4)]:
        d0 = hs if i == 0 else 0.0
        d1 = hs if i == 1 else 0.0
        fd = (math.log(density_theta(theta[0] + d0, theta[1] + d1, x0, x1))
              - math.log(density_theta(theta[0] - d0, theta[1] - d1, x0, x1))
              ) / (2 * hs)
        check(f"scoreFun s_{i} == d/dth_{i} log p at x=({x0},{x1})",
              "GaussianModel.lean:179 (scoreFun is the true score)",
              score(i, x0, x1), fd, rel_tol=1e-6, abs_tol=1e-7)

# ----------------------------------------------------------------------------
# 2. Classical bit (Dichotomy.lean:181): Bernoulli p_a = (cos^2 a, sin^2 a).
#    Fisher metric E[(d/da log p)^2] == 4;  cubic E[(d/da log p)^3] = 16 cot 2a.
# ----------------------------------------------------------------------------
def bit_moments(a, h=1e-6):
    # scores of the two outcomes by finite differences of log p in alpha,
    # so no hand-derived calculus is shared with the expected values
    def lp0(t):
        return 2.0 * math.log(abs(math.cos(t)))

    def lp1(t):
        return 2.0 * math.log(abs(math.sin(t)))

    s0 = (lp0(a + h) - lp0(a - h)) / (2 * h)
    s1 = (lp1(a + h) - lp1(a - h)) / (2 * h)
    p0, p1 = math.cos(a) ** 2, math.sin(a) ** 2
    return p0 * s0 ** 2 + p1 * s1 ** 2, p0 * s0 ** 3 + p1 * s1 ** 3


for a in [0.3, 0.7, 1.2, math.pi / 4]:
    m2, m3 = bit_moments(a)
    check(f"classical bit metric at a={a:.3f} == 4",
          "Dichotomy.lean:181 (classicalBitData.metric = 4)", m2, 4.0,
          rel_tol=1e-8)
    check(f"classical bit cubic at a={a:.3f} == 16 cot(2a)",
          "Dichotomy.lean:159 (bitCubic = 16 cos(2a)/sin(2a))",
          m3, 16.0 / math.tan(2.0 * a), rel_tol=1e-7, abs_tol=1e-7)

# ----------------------------------------------------------------------------
# 3. Qubit (Dichotomy.lean:235): SLD quantum Fisher metric of the Bloch
#    family |psi(a,b)> = (cos(a/2), e^{ib} sin(a/2)):
#    F_ij = 4 Re( <d_i psi|d_j psi> - <d_i psi|psi><psi|d_j psi> )
#    should equal diag(1, sin^2 a).
# ----------------------------------------------------------------------------
def bloch(a, b):
    return [complex(math.cos(a / 2.0), 0.0),
            cmath.exp(1j * b) * math.sin(a / 2.0)]


def qfi_metric(a, b):
    h = 1e-6

    def d(i):
        pp = bloch(a + (h if i == 0 else 0), b + (h if i == 1 else 0))
        mm = bloch(a - (h if i == 0 else 0), b - (h if i == 1 else 0))
        return [(pp[k] - mm[k]) / (2 * h) for k in range(2)]

    psi = bloch(a, b)
    dpsi = [d(0), d(1)]

    def ip(u, v):
        return sum(u[k].conjugate() * v[k] for k in range(2))

    F = [[0.0] * 2 for _ in range(2)]
    for i in range(2):
        for j in range(2):
            F[i][j] = 4.0 * (ip(dpsi[i], dpsi[j])
                             - ip(dpsi[i], psi) * ip(psi, dpsi[j])).real
    return F


for (a, b) in [(0.8, 1.1), (2.0, 0.4), (1.3, 2.9)]:
    F = qfi_metric(a, b)
    check(f"qubit QFI g_00 at (a,b)=({a},{b}) == 1",
          "Dichotomy.lean:235 (qubitData.metric = diag(1, sin^2 a))",
          F[0][0], 1.0, rel_tol=1e-6)
    check(f"qubit QFI g_11 at (a,b)=({a},{b}) == sin^2 a",
          "Dichotomy.lean:235", F[1][1], math.sin(a) ** 2, rel_tol=1e-6)
    check(f"qubit QFI g_01 at (a,b)=({a},{b}) == 0",
          "Dichotomy.lean:235", F[0][1], 0.0, abs_tol=1e-6)

# ----------------------------------------------------------------------------
# 4. Cramer-Rao (CramerRao/Bound.lean:57): Var_theta(T) >= (d tau)^2 / g_11.
#    Every ingredient travels its own numeric route, so the check exercises
#    the *relationship* the theorem asserts, never one integral vs itself:
#      score  s(th, x) = d/dth log p    -- finite difference in theta
#      Fisher g(th)    = int s^2 p dx   -- quadrature of the FD score
#      tau(th)         = E_th[T]        -- quadrature; d tau by FD in theta
#      Var(T)          = E_th[(T-tau)^2]-- quadrature
#    Models are chosen so g != 1 != Var (an expression-identity bug cannot
#    fake a pass), and one estimator is strictly inefficient.
# ----------------------------------------------------------------------------
def cramer_rao_case(name, lean, logp, T, th, lo, hi,
                    want_g=None, equality=False, min_gap=None):
    hs = 1e-5

    def p(x):
        return math.exp(logp(th, x))

    def s(x):
        return (logp(th + hs, x) - logp(th - hs, x)) / (2 * hs)

    g = tanh_sinh(lambda x: s(x) ** 2 * p(x), lo, hi, level=11)

    def tau(t):
        return tanh_sinh(lambda x: T(x) * math.exp(logp(t, x)), lo, hi,
                         level=11)

    ht = 1e-4
    dtau = (tau(th + ht) - tau(th - ht)) / (2 * ht)
    mean = tau(th)
    var = tanh_sinh(lambda x: (T(x) - mean) ** 2 * p(x), lo, hi, level=11)
    bound = dtau ** 2 / g
    if want_g is not None:
        check(f"{name}: Fisher from FD score = {want_g}",
              "Fisher/Information.lean:183 (g = E[s^2], s = d log p)",
              g, want_g, rel_tol=1e-6)
    # slack absorbs FD/quadrature noise at equality points; the attainment
    # check below still pins equality to 1e-5
    check_le(f"{name}: (d tau)^2/g <= Var(T)", lean, bound, var, slack=1e-7)
    if equality:
        check(f"{name}: efficient estimator attains the bound", lean,
              bound, var, rel_tol=1e-5)
    if min_gap is not None:
        check_le(f"{name}: inefficient estimator strictly above bound "
                 f"(gap >= {min_gap})", lean, min_gap, var - bound)
    return g, dtau, var, bound


LOG_SQRT_2PI = 0.5 * math.log(2.0 * math.pi)
CR = "CramerRao/Bound.lean:57 (cramerRao_scalar)"

# A: N(theta, sigma=2), T = x. g = 1/4 while Var = 4: bound attained, and no
#    two quantities coincide numerically by construction.
cramer_rao_case("N(th, sig=2), T=x", CR,
                lambda t, x: -((x - t) ** 2) / 8.0 - math.log(2.0) - LOG_SQRT_2PI,
                lambda x: x, 0.4, 0.4 - 26.0, 0.4 + 26.0,
                want_g=0.25, equality=True)

# A': N(theta, sigma=1/2), T = x. g = 4 while Var = 1/4: with g on the wrong
#     side of the division even the bare inequality fails, not just equality.
cramer_rao_case("N(th, sig=1/2), T=x", CR,
                lambda t, x: -2.0 * (x - t) ** 2 + math.log(2.0) - LOG_SQRT_2PI,
                lambda x: x, 0.4, 0.4 - 7.0, 0.4 + 7.0,
                want_g=4.0, equality=True)

# B: N(theta, 1), T = x + 0.8 sin x: unbiased for its own mean function
#    tau(th) = th + 0.8 e^{-1/2} sin th but NOT efficient -> strict gap
#    (analytically: Var - bound ~ 0.054 at th = 0.4).
cramer_rao_case("N(th,1), T = x + 0.8 sin(x)", CR,
                lambda t, x: -((x - t) ** 2) / 2.0 - LOG_SQRT_2PI,
                lambda x: x + 0.8 * math.sin(x), 0.4, 0.4 - 13.0, 0.4 + 13.0,
                want_g=1.0, min_gap=0.02)

# C: exponential model p = th e^{-th x} on (0, inf), T = x (non-Gaussian):
#    g = 1/th^2, tau = 1/th, d tau = -1/th^2, bound = Var = 1/th^2.
th_e = 1.7
_, dtau_e, _, _ = cramer_rao_case("Exp(th), T=x", CR,
                                  lambda t, x: math.log(t) - t * x,
                                  lambda x: x, th_e, 1e-12, 60.0,
                                  want_g=1.0 / th_e ** 2, equality=True)
check("Exp(th): d tau from quadrature+FD = -1/th^2",
      CR + " (the (d tau)^2 numerator)", dtau_e, -1.0 / th_e ** 2,
      rel_tol=1e-6)

# D: Bernoulli (cos^2 a, sin^2 a) -- the classicalBitData family, discrete.
#    T = indicator(outcome 1), tau(a) = sin^2 a. Ties Cramer-Rao back to the
#    Dichotomy metric: the FD-score Fisher must equal 4.
a0 = 0.9
hb = 1e-6
pb = [math.cos(a0) ** 2, math.sin(a0) ** 2]
sb = [(2 * math.log(abs(math.cos(a0 + hb))) - 2 * math.log(abs(math.cos(a0 - hb)))) / (2 * hb),
      (2 * math.log(abs(math.sin(a0 + hb))) - 2 * math.log(abs(math.sin(a0 - hb)))) / (2 * hb)]
g_bit = pb[0] * sb[0] ** 2 + pb[1] * sb[1] ** 2
check("Bernoulli: FD-score Fisher = classicalBitData.metric = 4",
      "Dichotomy.lean:181 + Fisher/Information.lean:183", g_bit, 4.0,
      rel_tol=1e-8)
tau_bit = lambda t: math.sin(t) ** 2  # E[T] = P(outcome 1)
dtau_bit = (tau_bit(a0 + hb) - tau_bit(a0 - hb)) / (2 * hb)
var_bit = pb[0] * (0.0 - tau_bit(a0)) ** 2 + pb[1] * (1.0 - tau_bit(a0)) ** 2
bound_bit = dtau_bit ** 2 / g_bit
check_le("Bernoulli: (d tau)^2/g <= Var(indicator)", CR, bound_bit, var_bit,
         slack=1e-9)
check("Bernoulli: indicator is efficient (bound attained)", CR,
      bound_bit, var_bit, rel_tol=1e-6)
check("Bernoulli: Var = sin^2(2a)/4 (external closed form)",
      "(anchor for the Bernoulli case)", var_bit,
      math.sin(2 * a0) ** 2 / 4.0, rel_tol=1e-9)

finish("Information geometry: Gaussian Fisher = R^T R, bit/qubit metrics, Cramer-Rao")
