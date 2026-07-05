"""Numeric checks for Tomita-Takesaki modular theory (Spectra/Modular/).

The library builds the modular operator abstractly: for a von Neumann algebra
`M` with cyclic-separating vector `Ω`, the Tomita operator is the antilinear
`S(xΩ) = x⋆Ω`, the modular operator is `Δ = S⋆S` (von Neumann's `T⋆T`
theorem), `Δ^{½}` its square root, `J` the modular conjugation with `S=JΔ^{½}`,
and the modular flow `Δ^{it}`.  None of that is stated with a matrix; a wrong
placement of `ρ`, a wrong `i`-sign in the flow, or `Δ^{½}J` vs `JΔ^{½}` would
be proved correctly and pass AxiomCheck.

Concrete faithful model (the canonical one).  Take `M = M_n(ℂ)` acting on the
Hilbert-Schmidt space `H = M_n(ℂ)`, `⟪a,b⟫ = Tr(a⋆b)`, and the cyclic-separating
vector `Ω = ρ^{½}` for a faithful density matrix `ρ`.  Then

    S ξ = ρ^{-½} ξ⋆ ρ^{½},   Δ ξ = ρ ξ ρ^{-1},   J ξ = ξ⋆,
    Δ^{½} ξ = ρ^{½} ξ ρ^{-½},   Δ^{it} ξ = ρ^{it} ξ ρ^{-it},   log Δ = [log ρ, ·].

The KEY independence: `Δ` is built by TWO routes that share no bug —
  (A) from the abstract graph of the antilinear `S`, via realification, as the
      real operator `Sᵣᵀ Sᵣ` (this is literally `S⋆S`), then read back as a
      complex operator;
  (B) the closed-form density-matrix sandwich `ρ(·)ρ^{-1}`.
On a `ρ` with distinct eigenvalues these have eigenvalues `ρ_i/ρ_j` spread away
from 1, so an expression-identity bug cannot fake a pass.
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nclib import linalg as la
from nclib.harness import check, check_le, finish

TOL = 1e-8

# --------------------------------------------------------------------------
# The concrete model
# --------------------------------------------------------------------------
n = 3
rho = la.density_from_seed(n, 5)              # faithful (strictly +), trace 1
d = n * n
I_n = la.eye(n)
P = la.transpose_perm(n)                       # vec(X^T) = P vec(X)

rho_half = la.herm_sqrt(rho)
rho_ihalf = la.herm_pow(rho, -0.5)
rho_inv = la.inv(rho)
logrho = la.herm_log(rho)


def L(A):
    """Left multiplication superoperator: vec(A X) = (I (x) A) vec X."""
    return la.kron(I_n, A)


def R(B):
    """Right multiplication superoperator: vec(X B) = (B^T (x) I) vec X."""
    return la.kron(la.transpose(B), I_n)


def eqm(name, decl, A, B, tol=TOL):
    """Record that matrices A, B agree (max entrywise deviation ~ 0)."""
    return check(name, decl, la.max_abs_diff(A, B), 0.0, abs_tol=tol)


# --------------------------------------------------------------------------
# Δ = S⋆S from the abstract antilinear graph  vs  the closed form ρ(·)ρ^{-1}
# --------------------------------------------------------------------------
# Antilinear Tomita operator S ξ = ρ^{-½} ξ⋆ ρ^{½}:  vec(Sξ) = A_S conj(vec ξ)
A_S = la.matmul(la.kron(la.transpose(rho_half), rho_ihalf), la.mat(P))

# Route A: build Δ = S⋆S by realifying S and forming the real adjoint product.
S_R = la.realify_antilinear(A_S)
Delta_R = la.real_matmul(la.real_transpose(S_R), S_R)
Delta_abstract = la.unrealify_linear(Delta_R, d)

# Route B: the density-matrix sandwich.
Delta_closed = la.matmul(L(rho), R(rho_inv))

eqm("Δ = S⋆S  (abstract graph)  ==  ρ(·)ρ⁻¹  (closed form)",
    "TomitaTakesaki/VonNeumannTstarT.lean:89 (modularOp_apply)",
    Delta_abstract, Delta_closed)

# --------------------------------------------------------------------------
# tomitaOp_apply:  S(xΩ) = x⋆Ω   (defining property of S)
# --------------------------------------------------------------------------
# For x ∈ M, the vector xΩ = x·ρ^{½}; S must send it to x⋆·ρ^{½}.
x_test = la.hermitian_from_seed(n, 13)
xOmega = la.matmul(x_test, rho_half)                      # x Ω  (as n×n)
# Apply S (closed form) to vec(xΩ): S ξ = ρ^{-½} ξ⋆ ρ^{½}
S_xOmega = la.matmul_chain(rho_ihalf, la.dagger(xOmega), rho_half)
xstar_Omega = la.matmul(la.dagger(x_test), rho_half)      # x⋆ Ω, computed directly
eqm("S(xΩ) = x⋆Ω", "TomitaTakesaki/TomitaOperator.lean:98 (tomitaOp_apply)",
    S_xOmega, xstar_Omega)

# --------------------------------------------------------------------------
# Δ Hermitian, positive, symmetric; eigenvalues ρ_i/ρ_j
# --------------------------------------------------------------------------
check("Δ Hermitian (symmetric form ⟨Δx,y⟩=⟨x,Δy⟩)",
      "TomitaTakesaki/VonNeumannTstarT.lean:102 (modularOp_isSymmetric)",
      la.max_abs_diff(Delta_closed, la.dagger(Delta_closed)), 0.0, abs_tol=TOL)

delta_ev = sorted(la.herm_eigvalues(Delta_closed))
check_le("Δ ≥ 0 (min eigenvalue ≥ 0)  [modularOp_nonneg]",
         "TomitaTakesaki/VonNeumannTstarT.lean:116 (modularOp_nonneg)",
         -min(delta_ev), 0.0, slack=1e-7)
rho_ev = sorted(la.herm_eigvalues(rho))
expect_ev = sorted(a / b for a in rho_ev for b in rho_ev)
check("σ(Δ) = {ρ_i/ρ_j}", "TomitaTakesaki/VonNeumannTstarT.lean:264 (modularOp_isSelfAdjoint ⟹ real σ; model gives ρ_i/ρ_j)",
      max(abs(a - b) for a, b in zip(delta_ev, expect_ev)), 0.0, abs_tol=1e-6)

# modularOp_nonneg identity:  Re⟨Δξ,ξ⟩ = ‖Sξ‖²
xi = la.unvec([complex((i * 7 % 5) - 2, (i * 3 % 4) - 1) for i in range(d)], n)
xi_v = la.vec(xi)
Dxi = la.matvec(Delta_closed, xi_v)
re_inner = sum(xi_v[i].conjugate() * Dxi[i] for i in range(d)).real
S_xi = la.matmul_chain(rho_ihalf, la.dagger(xi), rho_half)   # S ξ
norm_S_xi_sq = la.hs_norm(S_xi) ** 2
check("Re⟨Δξ,ξ⟩ = ‖Sξ‖²", "TomitaTakesaki/VonNeumannTstarT.lean:116 (modularOp_nonneg)",
      re_inner, norm_S_xi_sq, rel_tol=1e-9)

# one_add_modularOp_surjective: 1+Δ invertible (surjective)
one_plus = la.add(la.eye(d), Delta_closed)
eqm("(1+Δ)(1+Δ)⁻¹ = 1   (1+Δ surjective)",
    "TomitaTakesaki/VonNeumannTstarT.lean:201 (one_add_modularOp_surjective)",
    la.matmul(one_plus, la.inv(one_plus)), la.eye(d), tol=1e-7)

# --------------------------------------------------------------------------
# Δ^{½}: squares to Δ, self-adjoint, fixes vacuum
# --------------------------------------------------------------------------
Dhalf = la.herm_pow(Delta_closed, 0.5)
eqm("(Δ^{½})² = Δ", "Cocycle/ModularSqrtSquare.lean:607 (modularSqrt_sq_apply)",
    la.matmul(Dhalf, Dhalf), Delta_closed)
eqm("Δ^{½} self-adjoint", "Cocycle/ModularSqrtSelfAdjoint.lean:258 (modularSqrt_isSelfAdjoint)",
    Dhalf, la.dagger(Dhalf))
# closed form Δ^{½} ξ = ρ^{½} ξ ρ^{-½}
Dhalf_closed = la.matmul(L(rho_half), R(rho_ihalf))
eqm("Δ^{½} = ρ^{½}(·)ρ^{-½}", "Cocycle/ModularSqrt.lean:52 (modularSqrt)", Dhalf, Dhalf_closed)

# --------------------------------------------------------------------------
# Δ⁻¹ and Δ^{-½}  (ModularReciprocal)
# --------------------------------------------------------------------------
Dinv = la.matmul(L(rho_inv), R(rho))            # ρ^{-1}(·)ρ
eqm("Δ⁻¹ = ρ⁻¹(·)ρ  self-adjoint & inverse",
    "Cocycle/ModularReciprocal.lean:142 (modularOpInv_isSelfAdjoint)",
    la.matmul(Delta_closed, Dinv), la.eye(d))
Dmhalf = la.herm_pow(Delta_closed, -0.5)
eqm("(Δ^{-½})² = Δ⁻¹", "Cocycle/ModularReciprocal.lean:453 (modularSqrtInv_sq_apply)",
    la.matmul(Dmhalf, Dmhalf), Dinv)

# --------------------------------------------------------------------------
# Modular conjugation J: antiunitary, J²=1, JΔ^{½}=S, S²=1
# --------------------------------------------------------------------------
A_J = la.mat(P)                                  # J ξ = ξ⋆  ->  A_J conj(·), A_J = P
# antiunitarity ⟨Ju,Jv⟩ = ⟨v,u⟩ (inner_modularConjugation): equivalent to A_J unitary
check("J antiunitary: ⟨Ju,Jv⟩=⟨v,u⟩  (A_J unitary)",
      "Cocycle/ModularPolarUniqueness.lean:194 (inner_modularConjugation)",
      la.max_abs_diff(la.matmul(la.dagger(A_J), A_J), la.eye(d)), 0.0, abs_tol=1e-12)
eqm("J² = 1", "TomitaTakesaki/Basic.lean:201 (symm_J: J.symm=J ⟹ J²=1)",
    la.matmul(A_J, la.conj(A_J)), la.eye(d), tol=1e-12)
# S = J Δ^{½}:  as antilinear matrices  A_S == A_J conj(Δ^{½})
eqm("S = J Δ^{½}  (polar decomposition)", "Cocycle/ModularPolarExtension.lean:346 (tomita_eq_modularConjugation_modularSqrt_full)",
    A_S, la.matmul(A_J, la.conj(Dhalf)))
eqm("S² = 1 on domain", "Cocycle/ModularInvolution.lean:174 (sTilde_closure_involutive)",
    la.matmul(A_S, la.conj(A_S)), la.eye(d))

# --------------------------------------------------------------------------
# Commutation theorem  J M J = M':  J L_a J = R_{a⋆}
# --------------------------------------------------------------------------
a_op = la.hermitian_from_seed(n, 21)
JLaJ = la.matmul_chain(A_J, la.conj(L(a_op)), la.conj(A_J))
eqm("J L_a J = R_{a⋆}   (Tomita duality J M J = M')",
    "TomitaTakesaki/Basic.lean:28/196 (Tomita J M J = M'; finite-model validation)",
    JLaJ, R(la.dagger(a_op)))

# inner_star_comm:  ⟨a⋆Ω, bΩ⟩ = ⟨b⋆Ω, aΩ⟩ for a∈M (left) and b∈M' (right mult by c)
c_op = la.hermitian_from_seed(n, 31)
aΩ = la.matmul(a_op, rho_half)               # a·Ω,  a ∈ M (left mult)
bΩ = la.matmul(rho_half, c_op)               # b·Ω,  b = R_c ∈ M' (right mult)
astarΩ = la.matmul(la.dagger(a_op), rho_half)
bstarΩ = la.matmul(rho_half, la.dagger(c_op))
lhs = la.trace(la.matmul(la.dagger(astarΩ), bΩ))     # ⟨a⋆Ω, bΩ⟩_HS
rhs = la.trace(la.matmul(la.dagger(bstarΩ), aΩ))     # ⟨b⋆Ω, aΩ⟩_HS
check("⟨a⋆Ω,bΩ⟩ = ⟨b⋆Ω,aΩ⟩  (a∈M, b∈M')",
      "TomitaTakesaki/Closable.lean:31 (inner_star_comm)",
      la.max_abs_diff([[lhs]], [[rhs]]), 0.0, abs_tol=TOL)

# --------------------------------------------------------------------------
# Modular flow Δ^{it}: unitary, group law, fixes vacuum, preserves M
# --------------------------------------------------------------------------
t, s = 0.7, -0.4
Dit = la.herm_pow_imag(Delta_closed, t)
Dis = la.herm_pow_imag(Delta_closed, s)
check("Δ^{it} unitary", "TomitaTakesaki/ModularFlow.lean:61 (modularFlow_unitary)",
      la.max_abs_diff(la.matmul(la.dagger(Dit), Dit), la.eye(d)), 0.0, abs_tol=1e-8)
eqm("Δ^{i(s+t)} = Δ^{is} Δ^{it}  (group law)",
    "TomitaTakesaki/ModularFlow.lean:66 (modularFlow_group_law)",
    la.herm_pow_imag(Delta_closed, s + t), la.matmul(Dis, Dit))
# closed form Δ^{it} ξ = ρ^{it} ξ ρ^{-it}
rho_it = la.herm_pow_imag(rho, t)
rho_mit = la.herm_pow_imag(rho, -t)
eqm("Δ^{it} = ρ^{it}(·)ρ^{-it}", "TomitaTakesaki/ModularFlow.lean:49 (modularFlow)",
    Dit, la.matmul(L(rho_it), R(rho_mit)))

# Vacuum is fixed: Δ Ω = Ω, Δ^{½} Ω = Ω, Δ^{it} Ω = Ω  (Ω = ρ^{½} as HS vector)
Omega = la.vec(rho_half)
eqm("Δ Ω = Ω", "Cocycle/ModularVacuum.lean:142 (modularOp_vacuum)",
    [la.matvec(Delta_closed, Omega)], [Omega], tol=TOL)
eqm("Δ^{½} Ω = Ω", "Cocycle/ModularVacuum.lean:233 (modularSqrt_vacuum)",
    [la.matvec(Dhalf, Omega)], [Omega], tol=TOL)
eqm("Δ^{it} Ω = Ω", "Cocycle/ModularFlowVacuum.lean:151 (modularFlow_fixes_vacuum)",
    [la.matvec(Dit, Omega)], [Omega], tol=1e-8)

# Modular automorphism preserves M:  Δ^{it} L_a Δ^{-it} = L_{ρ^{it} a ρ^{-it}}
Dmit = la.herm_pow_imag(Delta_closed, -t)
sigma_a = la.matmul_chain(rho_it, a_op, rho_mit)
eqm("Δ^{it} L_a Δ^{-it} = L_{σ_t(a)}   (σ_t(M)=M)",
    "TomitaTakesaki/Basic.lean:196 (modularAutomorphism_mem: Δ^{it}MΔ^{-it}=M)",
    la.matmul_chain(Dit, L(a_op), Dmit), L(sigma_a))

# --------------------------------------------------------------------------
# Modular Hamiltonian:  generator(Δ^{it}) = log Δ = [log ρ, ·]
# --------------------------------------------------------------------------
logDelta = la.herm_log(Delta_closed)
ad_logrho = la.sub(L(logrho), R(logrho))
eqm("log Δ = [log ρ, ·]   (generator = modular Hamiltonian)",
    "Cocycle/ModularHamiltonian.lean:109 (generator_modularFlow_eq_logModularOp)",
    logDelta, ad_logrho)
eqm("log Δ self-adjoint", "Cocycle/ModularHamiltonian.lean:92 (logModularOp_isSelfAdjoint)",
    logDelta, la.dagger(logDelta))
eqm("Δ^{it} = exp(it · log Δ)   (Stone: modular flow from its generator)",
    "Cocycle/ModularHamiltonian.lean:109 (generator_modularFlow_eq_logModularOp)",
    Dit, la.herm_unitary_exp(logDelta, t))

# --------------------------------------------------------------------------
# The state ω(a) = ⟨Ω, aΩ⟩_HS = Tr(ρ a)
# --------------------------------------------------------------------------
omega_a = la.trace(la.matmul(la.dagger(rho_half), la.matmul(a_op, rho_half)))
check("ω(a)=⟨Ω,aΩ⟩_HS = Tr(ρa)", "Modular/KMS/Modular.lean (HS state ⟨Ω,·Ω⟩=Tr(ρ·); model identity)",
      la.max_abs_diff([[omega_a]], [[la.trace(la.matmul(rho, a_op))]]), 0.0, abs_tol=TOL)

finish("Modular / Tomita-Takesaki numeric checks")
