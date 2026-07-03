"""Pure-stdlib special functions used by the numeric checks.

Conventions are the standard ones (Abramowitz & Stegun / DLMF):
  - generalized Laguerre L_n^{(a)}(x) with L_0=1, L_1 = 1+a-x,
    (n+1) L_{n+1} = (2n+1+a-x) L_n - (n+a) L_{n-1}
  - Kummer 1F1(a; b; x) = sum_k (a)_k / (b)_k x^k / k!
  - associated Legendre P_l^m with Condon-Shortley phase
"""

import math


def genlaguerre(n, a, x):
    """Generalized Laguerre polynomial L_n^{(a)}(x), standard convention."""
    if n == 0:
        return 1.0
    lm1 = 1.0
    l = 1.0 + a - x
    for k in range(1, n):
        lm1, l = l, ((2 * k + 1 + a - x) * l - (k + a) * lm1) / (k + 1)
    return l


def genlaguerre_deriv(n, a, x):
    """d/dx L_n^{(a)}(x) = -L_{n-1}^{(a+1)}(x)."""
    if n == 0:
        return 0.0
    return -genlaguerre(n - 1, a + 1, x)


def kummer_1f1(a, b, x, tol=1e-17, max_terms=10000):
    """Kummer confluent hypergeometric 1F1(a; b; x) by direct series."""
    term = 1.0
    total = 1.0
    for k in range(max_terms):
        term *= (a + k) / (b + k) * x / (k + 1)
        total += term
        if abs(term) < tol * abs(total) and k > 3:
            break
    return total


def assoc_legendre(l, m, x):
    """Associated Legendre P_l^m(x), Condon-Shortley phase, m >= 0."""
    if m < 0 or m > l:
        raise ValueError("need 0 <= m <= l")
    # P_m^m
    pmm = 1.0
    if m > 0:
        somx2 = math.sqrt((1.0 - x) * (1.0 + x))
        fact = 1.0
        for _ in range(m):
            pmm *= -fact * somx2
            fact += 2.0
    if l == m:
        return pmm
    pmmp1 = x * (2 * m + 1) * pmm
    if l == m + 1:
        return pmmp1
    pll = 0.0
    for ll in range(m + 2, l + 1):
        pll = ((2 * ll - 1) * x * pmmp1 - (ll + m - 1) * pmm) / (ll - m)
        pmm, pmmp1 = pmmp1, pll
    return pll


def sph_harm_real_theta(l, m, theta):
    """|Y_l^m(theta, phi)| angular factor: the theta-dependent part
    sqrt((2l+1)/(4pi) * (l-m)!/(l+m)!) * P_l^m(cos theta), m >= 0."""
    norm = math.sqrt(
        (2 * l + 1) / (4 * math.pi) * math.factorial(l - m) / math.factorial(l + m)
    )
    return norm * assoc_legendre(l, m, math.cos(theta))


def factorial(n):
    return math.factorial(n)
