"""Pure-stdlib quadrature: tanh-sinh (finite) and exp-sinh (half-infinite).

Double-exponential rules give near machine precision for analytic integrands,
including ones with endpoint singularities (e.g. 1/sqrt(x) at 0).
No numpy required.
"""

import math


def tanh_sinh(f, a, b, level=10):
    """Integrate f over the finite interval [a, b] by tanh-sinh quadrature.

    Node positions near the endpoints are computed via their distance to the
    endpoint (eps = 1 - |x| = 2/(1+e^{2u})), so integrable endpoint
    singularities are handled at full double precision.
    """
    c = 0.5 * (b - a)
    d = 0.5 * (b + a)
    h = 2.0 ** (-(level - 4))
    total = _eval_or_zero(f, d) * _ts_weight(0.0)
    k = 1
    while True:
        t = k * h
        w = _ts_weight(t)
        if w < 1e-300:
            break
        u = 0.5 * math.pi * math.sinh(t)
        if u > 350.0:
            break
        eps = 2.0 / (1.0 + math.exp(2.0 * u))  # = 1 - tanh(u), stable
        xp = b - c * eps  # node near b
        xm = a + c * eps  # node near a
        total += w * (_eval_or_zero(f, xp) + _eval_or_zero(f, xm))
        k += 1
        if k > 100000:
            break
    return total * c * h


def _eval_or_zero(f, x):
    try:
        v = f(x)
    except (OverflowError, ValueError, ZeroDivisionError):
        return 0.0
    if isinstance(v, complex):
        if not (math.isfinite(v.real) and math.isfinite(v.imag)):
            return 0.0
        return v
    if not math.isfinite(v):
        return 0.0
    return v


def _ts_weight(t):
    ch = math.cosh(t)
    sh = math.sinh(t)
    den = math.cosh(0.5 * math.pi * sh)
    return 0.5 * math.pi * ch / (den * den)


def exp_sinh(f, level=10):
    """Integrate f over (0, infinity) by exp-sinh quadrature.

    Handles integrable singularities at 0 and exponential decay at infinity.
    """
    h = 2.0 ** (-(level - 4))
    total = 0.0
    # |u| = (pi/2)|sinh t| <= 700  <=>  |t| <= asinh(1400/pi) ~ 6.8
    t_max = math.asinh(700.0 / (0.5 * math.pi))
    n_max = int(t_max / h)
    for k in range(-n_max, n_max + 1):
        t = k * h
        u = 0.5 * math.pi * math.sinh(t)
        x = math.exp(u)
        w = x * 0.5 * math.pi * math.cosh(t)
        if w == 0.0 or not math.isfinite(w):
            continue
        try:
            v = f(x)
        except (OverflowError, ValueError, ZeroDivisionError):
            continue
        if isinstance(v, complex):
            if not (math.isfinite(v.real) and math.isfinite(v.imag)):
                continue
        elif not math.isfinite(v):
            continue
        total += w * v
    return total * h


def integrate_0_inf(f, level=10):
    """Alias with a self-describing name."""
    return exp_sinh(f, level=level)
