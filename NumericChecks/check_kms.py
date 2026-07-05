"""Numeric checks for the KMS condition (Spectra/Modular/KMS/).

The library states the KMS condition (Bratteli-Robinson form) for a state `ω`,
dynamics `α`, inverse temperature `β`:  for each `a,b` there is `F` holomorphic
on the strip `0 < Im z < β` with boundary values

    F(t)      = ω(a · α_t(b))          (lower, Im = 0)
    F(t + iβ) = ω(α_t(b) · a)          (upper, Im = β)

A wrong β-sign (`-iβ`), a swapped operator order on the upper boundary, or a
`β` vs `1/β` confusion would all be provable and pass AxiomCheck.  We validate
the convention on the canonical concrete model.

Model.  `A = M_n(ℂ)`, a Hermitian Hamiltonian `H`, the Gibbs state
`ρ_β = e^{-βH}/Z`, `ω(x) = Tr(ρ_β x)`, and Heisenberg dynamics
`α_t(b) = e^{itH} b e^{-itH}`, complexified to `σ_z(b) = e^{izH} b e^{-izH}`.
The two-point function is `F(z) = Tr(ρ_β a σ_z(b))`.

Independence.  The KMS boundary identity `F(t+iβ) = ω(α_t(b) a)` is checked by
computing the LEFT side as an analytic continuation
`Tr(ρ_β a e^{itH}e^{-βH} b e^{-itH}e^{βH})` and the RIGHT side as the plain
product `Tr(ρ_β e^{itH} b e^{-itH} a)` — completely different matrix
expressions, which coincide only because the β-convention is right.  All
observables are non-commuting (H, a=σ-like, b=σ-like don't share eigenbases),
so ordering/sign errors change the numbers.
"""

import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nclib import linalg as la
from nclib.harness import check, check_le, finish

TOL = 1e-8

# --------------------------------------------------------------------------
# Model
# --------------------------------------------------------------------------
n = 3
H = la.hermitian_from_seed(n, 3)               # Hamiltonian
a = la.hermitian_from_seed(n, 8)               # observable a
b = la.hermitian_from_seed(n, 14)              # observable b
beta = 0.8


def gibbs(bet):
    e = la.herm_exp(la.scale(-bet, H))
    return la.scale(1.0 / la.trace(e).real, e)


rho_b = gibbs(beta)


def expizH(z):
    """e^{izH} for complex z = x+iy:  e^{ixH} e^{-yH}  (both functions of H, commute)."""
    x, y = z.real, z.imag
    return la.matmul(la.herm_unitary_exp(H, x), la.herm_exp(la.scale(-y, H)))


def sigma(z, op):
    """σ_z(op) = e^{izH} op e^{-izH}."""
    return la.matmul_chain(expizH(z), op, expizH(-z))


def omega(op):
    return la.trace(la.matmul(rho_b, op))


def F(z):
    """Two-point function F(z) = ω(a · σ_z(b)) = Tr(ρ_β a σ_z(b))."""
    return omega(la.matmul(a, sigma(z, b)))


def sc(name, decl, lhs, rhs, tol=TOL):
    return check(name, decl, la.max_abs_diff([[lhs]], [[rhs]]), 0.0, abs_tol=tol)


# --------------------------------------------------------------------------
# KMS lower boundary  F(t) = ω(a · α_t(b))   (and ordering is not symmetric)
# --------------------------------------------------------------------------
t = 0.5
sc("KMS lower boundary F(t) = ω(a·α_t(b))",
   "KMS/Condition.lean:338 (KMSFunction.lower_boundary)",
   F(complex(t, 0.0)), omega(la.matmul(a, sigma(complex(t, 0), b))))
# non-triviality: the reversed order ω(α_t(b)·a) is genuinely different
diff_order = abs(omega(la.matmul(a, sigma(complex(t, 0), b)))
                 - omega(la.matmul(sigma(complex(t, 0), b), a)))
check_le("ordering matters: |ω(a·α_t b) − ω(α_t b·a)| > 0 (noncommutative)",
         "KMS/Condition.lean:338/340 (boundary ordering)",
         -diff_order, -1e-3, slack=0.0)  # asserts diff_order > 1e-3

# --------------------------------------------------------------------------
# KMS upper boundary  F(t + iβ) = ω(α_t(b) · a)     [the β-convention check]
# --------------------------------------------------------------------------
# Route A: analytic continuation F(t+iβ)
lhs_upper = F(complex(t, beta))
# Route B: plain product ω(α_t(b) a) with real-time α_t(b)
rhs_upper = omega(la.matmul(sigma(complex(t, 0), b), a))
sc("KMS upper boundary F(t+iβ) = ω(α_t(b)·a)   [β sign & order]",
   "KMS/Condition.lean:340 (KMSFunction.upper_boundary)", lhs_upper, rhs_upper)

# the wrong sign F(t−iβ) does NOT equal ω(α_t(b)·a) (guards against −iβ bug)
wrong = abs(F(complex(t, -beta)) - rhs_upper)
check_le("wrong sign F(t−iβ) ≠ ω(α_t b·a)  (guards −iβ)",
         "KMS/Condition.lean:340 (upper_boundary β-sign)", -wrong, -1e-3, slack=0.0)

# --------------------------------------------------------------------------
# KMS function is holomorphic on the strip:  ∂F/∂z̄ = 0  (Cauchy-Riemann)
# --------------------------------------------------------------------------
z0 = complex(0.3, 0.4 * beta)
h = 1e-5
dFdx = (F(z0 + h) - F(z0 - h)) / (2 * h)
dFdy = (F(z0 + 1j * h) - F(z0 - 1j * h)) / (2 * h)
dbar = 0.5 * (dFdx + 1j * dFdy)                # ∂/∂z̄ = ½(∂x + i∂y)
check("F holomorphic on strip: ∂F/∂z̄ = 0",
      "KMS/Condition.lean:332 (KMSFunction.holomorphic)", abs(dbar), 0.0, abs_tol=1e-6)

# --------------------------------------------------------------------------
# Imaginary-time KMS:  ω(a · σ_{iβ}(b)) = ω(b · a)
# --------------------------------------------------------------------------
# σ_{iβ}(b) = e^{-βH} b e^{βH}   (Route A);  Route B is the plain product ω(ba).
lhs_it = omega(la.matmul(a, sigma(complex(0, beta), b)))
rhs_it = omega(la.matmul(b, a))
sc("imaginary-time KMS: ω(a·σ_{iβ}(b)) = ω(b·a)",
   "KMS/ImaginaryTime.lean:80 (IsKMSState.imaginaryTime)", lhs_it, rhs_it)

# --------------------------------------------------------------------------
# KMS ⇒ time invariance:  ω(α_t(a)) = ω(a)
# --------------------------------------------------------------------------
inv_dev = max(abs(omega(sigma(complex(tt, 0), a)) - omega(a)) for tt in (0.2, 1.3, -2.1))
check("KMS invariance ω(α_t(a)) = ω(a)",
      "KMS/Condition.lean:793 (IsKMSState.isInvariant)", inv_dev, 0.0, abs_tol=1e-9)

# --------------------------------------------------------------------------
# Generator  δ(a) = i[H,a]  (FD vs commutator)  and  ω(δ(a)) = 0
# --------------------------------------------------------------------------
eps = 1e-6
delta_fd = la.scale(1.0 / (2 * eps), la.sub(sigma(complex(eps, 0), a), sigma(complex(-eps, 0), a)))
delta_formula = la.scale(1j, la.commutator(H, a))          # i[H,a]
check("generator δ(a) = i[H,a]  (FD vs commutator)",
      "KMS/Generator.lean:47 (Dynamics.generator)",
      la.max_abs_diff(delta_fd, delta_formula), 0.0, abs_tol=1e-5)
sc("invariant state kills generator: ω(δ(a)) = 0",
   "KMS/Generator.lean:133 (IsInvariant.generator_apply)", omega(delta_formula), 0.0)

# --------------------------------------------------------------------------
# Temperature rescaling:  ω KMS at β for α  ⇒  ω KMS at β₂ for α.rescale(β/β₂)
#   rescale(c)_t = α_{ct}.  We verify the rescaled KMS upper boundary at β₂.
# --------------------------------------------------------------------------
beta2 = 1.5
c = beta / beta2                                    # rescale factor = β₁/β₂
# rescaled dynamics α'_t(b) = α_{ct}(b) = σ_{ct}(b); the α'-two-point function is
# F'(z) = ω(a σ_{cz}(b)); its upper boundary at Im=β₂ must give ω(α'_t(b)·a).
lhs_resc = omega(la.matmul(a, sigma(c * complex(t, beta2), b)))   # F'(t+iβ₂), Route A
rhs_resc = omega(la.matmul(sigma(complex(c * t, 0), b), a))       # ω(α'_t(b)·a), Route B
sc("rescaled KMS at β₂: F'(t+iβ₂)=ω(α'_t(b)·a), α'=α∘(·×β/β₂)",
   "KMS/Modular.lean:339 (IsKMSState.rescale) / Modular.lean:196 (Dynamics.rescale)",
   lhs_resc, rhs_resc)

finish("KMS (Gibbs-state) numeric checks")
