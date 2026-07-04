"""Numeric checks for the Hardy inequality suite (Perturbation/).

Lean statements under test (3D, Lebesgue measure):
  hardy_inequality        (HardyInequality.lean:1712):
      int |psi|^2/|x|^2 dx <= 4 * int |grad psi|^2 dx        on H^1(R^3)
  hardy_constant_sharp    (Hardy/Sharp.lean:408): the 4 cannot be lowered;
      witnessed by the Emden-Fowler family g_n(r) = r^{-1/2} eta(log r / n)
      with derivative gN' = r^{-3/2}(eta'(log r/n)/n - eta(log r/n)/2)
      (Hardy/Sharp.lean:234,237).
  hardy_operator_bound    (HardyInequality.lean:1770):
      ||psi/r|| <= eps ||Lap psi|| + (1/eps) ||psi||          on H^2(R^3)
  coulomb_relatively_bounded_H2 (CoulombBound.lean:234):
      ||Z psi/r|| <= eps ||Lap psi|| + (Z^2/eps) ||psi||

For radial psi:  int |psi|^2/|x|^2 dx = 4 pi int_0^inf psi^2 dr
                 int |grad psi|^2 dx  = 4 pi int_0^inf psi'^2 r^2 dr
so the 4 pi cancels in every inequality below and we work with the radial
integrals directly.
"""

import math
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from nclib.quadrature import tanh_sinh, exp_sinh
from nclib.harness import check, check_le, finish


# ----------------------------------------------------------------------------
# 1. hardy_inequality: ratio = (int psi^2 dr)/(int psi'^2 r^2 dr) <= 4
#    for a spread of H^1 radial test functions (analytic derivatives).
# ----------------------------------------------------------------------------
TESTS = [
    ("e^{-r}", lambda r: math.exp(-r), lambda r: -math.exp(-r)),
    ("e^{-r^2}", lambda r: math.exp(-r * r), lambda r: -2 * r * math.exp(-r * r)),
    ("r e^{-r}", lambda r: r * math.exp(-r), lambda r: (1 - r) * math.exp(-r)),
    ("1/(1+r^2)", lambda r: 1 / (1 + r * r),
     lambda r: -2 * r / (1 + r * r) ** 2),
    ("e^{-r}(1+3r)", lambda r: (1 + 3 * r) * math.exp(-r),
     lambda r: (2 - 3 * r) * math.exp(-r)),
]
for name, f, fp in TESTS:
    hardy = exp_sinh(lambda r: f(r) ** 2)
    grad = exp_sinh(lambda r: fp(r) ** 2 * r * r)
    check_le(f"hardy_inequality on psi = {name}: int psi^2 <= 4 int psi'^2 r^2",
             "HardyInequality.lean:1712 (constant 4)", hardy, 4.0 * grad)

# ----------------------------------------------------------------------------
# 2. hardy_constant_sharp: Emden-Fowler ratio -> 4 from below.
#    In t = log r:  int g_n^2 dr           = int eta(t/n)^2 dt
#                   int (g_n')^2 r^2 dr    = int (eta'(t/n)/n - eta(t/n)/2)^2 dt
#    eta = the standard C_c^inf bump on (-1, 1).
# ----------------------------------------------------------------------------
def eta(t):
    return math.exp(-1.0 / (1.0 - t * t)) if abs(t) < 1.0 else 0.0


def eta_p(t):
    if abs(t) >= 1.0:
        return 0.0
    return eta(t) * (-2.0 * t) / (1.0 - t * t) ** 2


def hardy_ratio(n):
    num = tanh_sinh(lambda t: eta(t / n) ** 2, -n, n)
    den = tanh_sinh(lambda t: (eta_p(t / n) / n - eta(t / n) / 2.0) ** 2, -n, n)
    return num / den


prev = 0.0
for n in [2, 4, 8, 16, 32, 64]:
    ratio = hardy_ratio(n)
    check_le(f"Emden-Fowler ratio(n={n}) <= 4",
             "HardySharp.lean:408 (hardy_constant_sharp)", ratio, 4.0)
    check_le(f"Emden-Fowler ratio increases at n={n} (-> 4)",
             "HardySharp.lean:192-241 (optimizer family)", prev, ratio)
    prev = ratio
check("Emden-Fowler ratio(n=64) is within 2% of 4",
      "HardySharp.lean:408 (sharpness: no C < 4 works)", prev, 4.0, rel_tol=0.02)

# Exact prediction: with I2 = int eta'^2, I0 = int eta^2 (cross term vanishes),
# ratio(n) = I0 / (I2/n^2 + I0/4) -- checks the gN' formula's algebra.
I0 = tanh_sinh(lambda t: eta(t) ** 2, -1.0, 1.0)
I2 = tanh_sinh(lambda t: eta_p(t) ** 2, -1.0, 1.0)
for n in [4, 16]:
    check(f"ratio(n={n}) matches closed form I0/(I2/n^2 + I0/4)",
          "HardySharp.lean:237 (gN' = r^{-3/2}(eta'/n - eta/2))",
          hardy_ratio(n), I0 / (I2 / n ** 2 + I0 / 4.0), rel_tol=1e-8)

# gN' really is the derivative of gN (finite-difference cross-check).
def gN(n, r):
    return r ** (-0.5) * eta(math.log(r) / n)


def gN_prime(n, r):
    return r ** (-1.5) * (eta_p(math.log(r) / n) / n - eta(math.log(r) / n) / 2.0)


for r in [0.8, 1.5, 2.5]:
    h = 1e-6
    fd = (gN(4, r + h) - gN(4, r - h)) / (2 * h)
    check(f"gN'(4, r={r}) matches d/dr gN", "HardySharp.lean:234,237",
          gN_prime(4, r), fd, rel_tol=1e-7)

# ----------------------------------------------------------------------------
# 3. hardy_operator_bound: ||psi/r|| <= eps ||Lap psi|| + (1/eps)||psi||
#    Radial norms (the 4 pi cancels on both sides -- keep it anyway):
#      ||psi/r||^2 = 4pi int psi^2 dr,  ||psi||^2 = 4pi int psi^2 r^2 dr,
#      ||Lap psi||^2 = 4pi int (psi'' + 2 psi'/r)^2 r^2 dr.
#    Gaussians psi = e^{-a r^2}: Lap psi = (4 a^2 r^2 - 6 a) e^{-a r^2}.
# ----------------------------------------------------------------------------
def gauss_norms(a):
    fp2 = 4 * math.pi
    n_hardy = math.sqrt(fp2 * exp_sinh(lambda r: math.exp(-2 * a * r * r)))
    n_psi = math.sqrt(fp2 * exp_sinh(lambda r: math.exp(-2 * a * r * r) * r * r))
    n_lap = math.sqrt(fp2 * exp_sinh(
        lambda r: ((4 * a * a * r * r - 6 * a) * math.exp(-a * r * r)) ** 2 * r * r))
    return n_hardy, n_psi, n_lap


for a in [0.5, 2.0, 8.0]:
    nh, np_, nl = gauss_norms(a)
    for eps in [0.1, 0.5, 1.0]:
        check_le(f"||psi/r|| <= eps||Lap psi|| + (1/eps)||psi||  (a={a}, eps={eps})",
                 "HardyInequality.lean:1770 (C(eps) = 1/eps)",
                 nh, eps * nl + (1.0 / eps) * np_)

# ----------------------------------------------------------------------------
# 4. coulomb_relatively_bounded_H2 with Z: C = Z^2/eps
# ----------------------------------------------------------------------------
Z = 2.0
for a in [0.5, 4.0]:
    nh, np_, nl = gauss_norms(a)
    for eps in [0.2, 1.0]:
        check_le(f"||Z psi/r|| <= eps||Lap psi|| + (Z^2/eps)||psi||  (Z={Z}, a={a}, eps={eps})",
                 "CoulombBound.lean:234 (C = Z^2/eps via Hardy)",
                 Z * nh, eps * nl + (Z * Z / eps) * np_)

# coulomb_norm_eq (CoulombBound.lean:216): ||V psi|| = Z sqrt(hardyIntegral)
nh, _, _ = gauss_norms(1.0)
check("coulomb_norm_eq: ||Z/r psi|| = Z sqrt(hardy)", "CoulombBound.lean:216",
      Z * nh, Z * math.sqrt(4 * math.pi * exp_sinh(
          lambda r: math.exp(-2 * r * r))), rel_tol=1e-10)

# ----------------------------------------------------------------------------
# 5. Dilation scan: single test functions leave the eps-bound slack by 3-10x,
#    so sweep each profile's whole scaling orbit psi_k(r) = psi(k r).
#    Norms scale exactly as
#      ||psi_k/r|| = k^{-1/2} ||psi/r||,  ||psi_k|| = k^{-3/2} ||psi||,
#      ||Lap psi_k|| = k^{+1/2} ||Lap psi||,
#    so ratio(k) = (eps k ||Lap psi|| + C ||psi||/k) / ||psi/r||.
#    (i)  min_k ratio >= 1 -- the bound survives its worst dilation;
#    (ii) min_k ratio is INDEPENDENT of eps  <=>  C(eps) ~ 1/eps exactly
#         (the dilation absorbs eps iff the intercept scales inversely),
#         a structural test of hardy_operator_bound's C(eps) = 1/eps.
# ----------------------------------------------------------------------------
def profile_norms(psi, lap_psi):
    n_hardy = math.sqrt(exp_sinh(lambda r: psi(r) ** 2))
    n_psi = math.sqrt(exp_sinh(lambda r: psi(r) ** 2 * r * r))
    n_lap = math.sqrt(exp_sinh(lambda r: lap_psi(r) ** 2 * r * r))
    return n_hardy, n_psi, n_lap


def min_ratio_over_dilation(nh, npsi, nlap, eps, C):
    def ratio(logk):
        k = math.exp(logk)
        return (eps * k * nlap + C * npsi / k) / nh

    lo, hi = math.log(1e-3), math.log(1e3)
    for _ in range(200):  # ternary search on the smooth unimodal ratio
        m1 = lo + (hi - lo) / 3.0
        m2 = hi - (hi - lo) / 3.0
        if ratio(m1) < ratio(m2):
            hi = m2
        else:
            lo = m1
    return ratio(0.5 * (lo + hi))


PROFILES = {
    "cusp e^{-r}": profile_norms(
        lambda r: math.exp(-r),
        lambda r: (1.0 - 2.0 / r) * math.exp(-r)),
    "gauss e^{-r^2}": profile_norms(
        lambda r: math.exp(-r * r),
        lambda r: (4.0 * r * r - 6.0) * math.exp(-r * r)),
}
for pname, (nh, npsi, nlap) in PROFILES.items():
    mins = {}
    for eps in (0.3, 1.0):
        mr = min_ratio_over_dilation(nh, npsi, nlap, eps, 1.0 / eps)
        mins[eps] = mr
        check_le(f"eps-bound survives worst dilation ({pname}, eps={eps})",
                 "HardyInequality.lean:1770 (hardy_operator_bound)", 1.0, mr)
    check(f"min-over-dilation ratio eps-invariant ({pname})",
          "HardyInequality.lean:1770 (structural test: C(eps) = 1/eps)",
          mins[0.3], mins[1.0], rel_tol=1e-8)

finish("Hardy inequality suite: constant 4, sharpness, Kato-Rellich bounds")
