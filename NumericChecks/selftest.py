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

finish("nclib self-test")
