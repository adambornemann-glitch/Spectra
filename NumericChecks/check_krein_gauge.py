"""Numeric checks for the Krein-space and lattice-gauge / Yang-Mills keystones:

  Spectra/Spaces/Krein/{Basic,Fock}.lean
  Spectra/GaugeTheory/Lattice/{Basic,WilsonAction,GibbsMeasure,ReflectionPositivity}.lean
  Spectra/GaugeTheory/UnitaryGroup/{Topology,Haar}.lean
  Spectra/QuantumFieldTheory/Wightman/RelativisticSpectralData.lean

Two honesty notes carried over from the recon:

  * Many gauge statements are PURELY MEASURE-THEORETIC (Haar existence/uniqueness, measurability,
    compactness, the partition-function integral over an infinite compact group).  Those are not
    dense-linear-algebra identities.  Here they are exercised only through FINITE surrogates —
    a uniform average over a finite subgroup (Z_k ⊂ U(1) or the quaternion group Q₈ ⊂ SU(2)) —
    which is explicitly labelled; the inequalities 0<Z≤1 and reflection-positivity ≥0 transfer
    verbatim to the finite average because they follow only from 0 ≤ S ≤ M and factorization.

  * Krein subspaces (posPart/negPart/ranges) are compared as orthogonal PROJECTOR matrices
    (basis-independent), using a NON-diagonal involution (σx / σy) so a mutation that silently
    assumes the eigenspaces are coordinate axes is caught.  The Krein form is checked by its two
    equivalent slot forms ⟪Jx,y⟫ and ⟪x,Jy⟫ (different products, equal iff J is Hermitian).
"""

import cmath
import math
import os
import sys
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nclib import linalg as la
from nclib.harness import check, check_le, finish

TOL = 1e-9
I = 1j

# Pauli / involutions
sx = la.mat([[0, 1], [1, 0]])
sy = la.mat([[0, -1j], [1j, 0]])
sz = la.mat([[1, 0], [0, -1]])
I2 = la.eye(2)


def inner(u, v):
    return sum(u[i].conjugate() * v[i] for i in range(len(u)))


def normsq(v):
    return sum(abs(c) ** 2 for c in v)


def spectral_proj(J, target):
    """Orthogonal projector onto the `target`-eigenspace of Hermitian J (Σ |u⟩⟨u|)."""
    evs, vecs = la.herm_eig(J)
    n = len(J)
    P = la.zeros(n)
    for lam, u in zip(evs, vecs):
        if abs(lam - target) < 1e-6:
            for i in range(n):
                for j in range(n):
                    P[i][j] += u[i] * u[j].conjugate()
    return P


# ##########################################################################
#  PART A — KREIN SPACES  (Spaces/Krein/Basic.lean, Fock.lean)
# ##########################################################################

# FundamentalSymmetry: J† = J and J∘J = 1 (self-adjoint unitary involution); the form is indefinite.
J3 = la.diagm([1, 1, -1])
check("FundamentalSymmetry: J† = J (self-adjoint)",
      "Spaces/Krein/Basic.lean:70 (isSelfAdjoint')", la.max_abs_diff(la.dagger(J3), J3), 0.0, abs_tol=TOL)
check("FundamentalSymmetry: J∘J = 1 (involution)  (J@J vs an independent I)",
      "Spaces/Krein/Basic.lean:70 (comp_self)", la.max_abs_diff(la.matmul(J3, J3), la.eye(3)), 0.0, abs_tol=TOL)
# indefinite: the Krein self-form takes BOTH signs
e0 = [1, 0, 0]; e2 = [0, 0, 1]
kf0 = inner(la.matvec(J3, e0), e0).real
kf2 = inner(la.matvec(J3, e2), e2).real
check("Krein form indefinite: [e0,e0]=+1 and [e2,e2]=−1 (both signs occur)",
      "Spaces/Krein/Basic.lean:70 (indefinite)", kf0 - kf2, 2.0, rel_tol=TOL)

# kreinInner x y = ⟪Jx,y⟫ = ⟪x,Jy⟫ (J Hermitian): two slot forms are DIFFERENT products, equal iff J†=J.
Jc = sy                                  # complex Hermitian involution σy
x = [1.0, 2j]; y = [3.0, -1j]
left = inner(la.matvec(Jc, x), y)        # ⟪Jx,y⟫
right = inner(x, la.matvec(Jc, y))       # ⟪x,Jy⟫
check("kreinInner: ⟪Jx,y⟫ = ⟪x,Jy⟫  (left/right slot forms, J=σy Hermitian)",
      "Spaces/Krein/Basic.lean:161,166 (kreinInner / _eq_inner_right)", abs(left - right), 0.0, abs_tol=TOL)
# conjugate-linear in the FIRST slot: [c•x,y] = conj(c)·[x,y]
c = 1.0 + 2j
check("kreinInner conjugate-linear first slot: [c•x,y] = conj(c)·[x,y]",
      "Spaces/Krein/Basic.lean:185 (kreinInner_smul_left)",
      abs(inner(la.matvec(Jc, [c * xi for xi in x]), y) - c.conjugate() * left), 0.0, abs_tol=TOL)

# posProj = (I+J)/2, negProj = (I−J)/2: self-adjoint idempotents summing to 1; range(posProj)=+1 eigenspace.
J = sx                                   # NON-diagonal involution (eigenvectors (1,±1)/√2)
Ppos = la.scale(0.5, la.add(I2, J))
Pneg = la.scale(0.5, la.sub(I2, J))
check("posProj idempotent (I+J)²/4 = (I+J)/2",
      "Spaces/Krein/Basic.lean:211 (posProj)", la.max_abs_diff(la.matmul(Ppos, Ppos), Ppos), 0.0, abs_tol=TOL)
check("posProj self-adjoint",
      "Spaces/Krein/Basic.lean:211 (posProj)", la.max_abs_diff(la.dagger(Ppos), Ppos), 0.0, abs_tol=TOL)
check("posProj + negProj = 1",
      "Spaces/Krein/Basic.lean:249 (posProj_add_negProj)", la.max_abs_diff(la.add(Ppos, Pneg), I2), 0.0, abs_tol=TOL)
# range(posProj) = (+1)-eigenspace: compare projector (I+J)/2 to the spectral projector (independent route)
check("range(posProj) = (+1)-eigenspace of J  ((I+J)/2 vs spectral projector)",
      "Spaces/Krein/Basic.lean:334 (range_posProj)",
      la.max_abs_diff(Ppos, spectral_proj(J, +1.0)), 0.0, abs_tol=1e-8)
# negPart_eq_orthogonal: negPart = posPart^⊥, i.e. Q_neg = I − Q_pos (two disjoint eigen-computations)
Qpos = spectral_proj(J, +1.0)
Qneg = spectral_proj(J, -1.0)
check("negPart_eq_orthogonal: Q(−1-eigenspace) = I − Q(+1-eigenspace)",
      "Spaces/Krein/Basic.lean:388 (negPart_eq_orthogonal)",
      la.max_abs_diff(Qneg, la.sub(I2, Qpos)), 0.0, abs_tol=1e-8)

# kreinInner definite on the two parts: [x,x]=+‖x‖² on H₊, −‖x‖² on H₋
xpos = [1.0, 1.0]                        # J xpos = xpos  (∈ H₊)
xneg = [1.0, -1.0]                       # J xneg = −xneg (∈ H₋)
check("kreinInner_self on H₊: [x,x] = ‖x‖²  (positive-definite)",
      "Spaces/Krein/Basic.lean:405 (kreinInner_self_of_mem_posPart)",
      inner(la.matvec(J, xpos), xpos).real, normsq(xpos), rel_tol=TOL)
check("kreinInner_self on H₋: [x,x] = −‖x‖²  (negative-definite)",
      "Spaces/Krein/Basic.lean:411 (kreinInner_self_of_mem_negPart)",
      inner(la.matvec(J, xneg), xneg).real, -normsq(xneg), rel_tol=TOL)

# kreinAdjoint A⁺ = J A† J and the Krein-adjoint property [Ax,y] = [x,A⁺y]
Jd = la.diagm([1, -1])
Anh = la.mat([[1.0, 1j], [0.0, 2.0]])    # non-Hermitian
Aplus = la.matmul(la.matmul(Jd, la.dagger(Anh)), Jd)
xk = [1.0, 1j]; yk = [2.0, -1.0]
# [Ax,y] = ⟪J(Ax),y⟫  vs  [x,A⁺y] = ⟪Jx,A⁺y⟫  (A⁺ built independently; different products)
lhs_ka = inner(la.matvec(Jd, la.matvec(Anh, xk)), yk)
rhs_ka = inner(la.matvec(Jd, xk), la.matvec(Aplus, yk))
check("kreinAdjoint property: [Ax,y] = [x,A⁺y]  with A⁺ = J A† J",
      "Spaces/Krein/Basic.lean:437 (kreinInner_map_left)", abs(lhs_ka - rhs_ka), 0.0, abs_tol=TOL)
# involutive: A⁺⁺ = A
Aplusplus = la.matmul(la.matmul(Jd, la.dagger(Aplus)), Jd)
check("kreinAdjoint involutive: A⁺⁺ = A  (non-normal A, so A⁺ ≠ A)",
      "Spaces/Krein/Basic.lean:450 (kreinAdjoint_kreinAdjoint)", la.max_abs_diff(Aplusplus, Anh), 0.0, abs_tol=TOL)
# isKreinSelfAdjoint A ⟺ IsSelfAdjoint(JA): TRUE model (A=J·M, M Hermitian) and FALSE model (A=σx)
M = la.mat([[2.0, 1j], [-1j, 3.0]])      # Hermitian
Atrue = la.matmul(Jd, M)
b1_true = la.max_abs_diff(la.matmul(la.matmul(Jd, la.dagger(Atrue)), Jd), Atrue) < 1e-9
b2_true = la.max_abs_diff(la.dagger(la.matmul(Jd, Atrue)), la.matmul(Jd, Atrue)) < 1e-9
check("isKreinSelfAdjoint_iff (TRUE model A=JM): (A⁺=A) ⟺ ((JA)†=JA), both true",
      "Spaces/Krein/Basic.lean:462 (isKreinSelfAdjoint_iff_isSelfAdjoint_comp)",
      1.0 if (b1_true and b2_true) else 0.0, 1.0, abs_tol=0)
b1_false = la.max_abs_diff(la.matmul(la.matmul(Jd, la.dagger(sx)), Jd), sx) < 1e-9
b2_false = la.max_abs_diff(la.dagger(la.matmul(Jd, sx)), la.matmul(Jd, sx)) < 1e-9
check("isKreinSelfAdjoint_iff (FALSE model A=σx): (A⁺=A) ⟺ ((JA)†=JA), both FALSE (Hermitian≠Krein-s.a.)",
      "Spaces/Krein/Basic.lean:462 (isKreinSelfAdjoint_iff, false branch)",
      1.0 if (b1_false == b2_false) else 0.0, 1.0, abs_tol=0)

# fockSymmetry Krein form: [ξ,η] = Σ_n ⟪Γ_n(J)ξ_n, η_n⟫ with Γ_n(J)=J^⊗n, Γ_0=1 (vacuum unsigned).
# Truncate to sectors 0 (ℂ), 1 (ℂ²), 2 (ℂ⁴). J=diag(1,-1).
Jf = la.diagm([1, -1])
JxJ = la.kron(Jf, Jf)
Gamma = la.direct_sum(la.direct_sum(la.mat([[1]]), Jf), JxJ)   # blockdiag(1, J, J⊗J) on ℂ⁷
xiF = [1.0 + 0.5j, 0.3, -0.2j, 0.4, 1j, 0.1, -0.5]
etaF = [0.7, 0.2 + 1j, 0.5, -0.3j, 0.6, 0.8, 0.1j]
lhs_fock = inner(la.matvec(Gamma, xiF), etaF)                  # Route A: full block operator (kron J⊗J)
# Route B: Γₙ(diag(1,−1)) is diagonal with sign (−1)^{#ones in the multi-index}, computed by BIT-PARITY
# — an encoding INDEPENDENT of the Kronecker product used to build Gamma in Route A, so a wrong
# Kronecker or a signed vacuum (Γ₀ should be +1) would make the two routes disagree.
xs = [xiF[0:1], xiF[1:3], xiF[3:7]]
es = [etaF[0:1], etaF[1:3], etaF[3:7]]
def parity_sign(j):
    return -1.0 if bin(j).count("1") % 2 else 1.0             # (−1)^{popcount}; parity_sign(0)=+1 (vacuum)
rhs_fock = sum(parity_sign(j) * xs[nn][j].conjugate() * es[nn][j]
               for nn in range(3) for j in range(len(xs[nn])))
check("kreinInner_fockSymmetry: [ξ,η] = Σₙ⟪Γₙ(J)ξₙ,ηₙ⟫, Γₙ=J^⊗n  (kron block operator vs bit-parity)",
      "Spaces/Krein/Fock.lean:187 (kreinInner_fockSymmetry)", abs(lhs_fock - rhs_fock), 0.0, abs_tol=1e-10)


# ##########################################################################
#  PART B — LATTICE GAUGE / WILSON ACTION  (algebraic, directly checkable)
# ##########################################################################
n_dim = 2                                # SU(2)/U(2) matrices are 2×2, so Fintype.card = 2


def hadamard():
    return la.scale(1 / math.sqrt(2), la.mat([[1, 1], [1, -1]]))


# plaquetteHolonomy = A·B·C⁻¹·D⁻¹ (ordered product; inverses on the two return legs)
A = hadamard()
B = la.diagm([cmath.exp(1j * math.pi / 3), cmath.exp(-1j * math.pi / 3)])
C = la.mat([[0, -1], [1, 0]])
D = la.scale(1 / math.sqrt(2), la.mat([[1, 1j], [1j, 1]]))
holo_inv = la.matmul(la.matmul(la.matmul(A, B), la.inv(C)), la.inv(D))       # via dense inverse
holo_dag = la.matmul(la.matmul(la.matmul(A, B), la.dagger(C)), la.dagger(D)) # via conj-transpose (unitary)
check("plaquetteHolonomy = A·B·C⁻¹·D⁻¹  (dense inverse vs conj-transpose, unitary links)",
      "GaugeTheory/Lattice/Basic.lean:128 (plaquetteHolonomy)",
      la.max_abs_diff(holo_inv, holo_dag), 0.0, abs_tol=1e-9)
check("plaquette holonomy is unitary",
      "GaugeTheory/Lattice/Basic.lean:128", 1.0 if la.is_unitary(holo_inv) else 0.0, 1.0, abs_tol=1e-9)
# all-identity links → holonomy = I  (plaquetteHolonomy_one)
holo_one = la.matmul(la.matmul(la.matmul(I2, I2), la.inv(I2)), la.inv(I2))
check("plaquetteHolonomy(all I) = I  (vacuum holonomy)",
      "GaugeTheory/Lattice/Basic.lean (plaquetteHolonomy_one)", la.max_abs_diff(holo_one, I2), 0.0, abs_tol=TOL)


def re_tr(Umat):
    return la.trace(Umat).real


# re_trace_le_card / neg_card_le_re_trace: −n ≤ Re tr U ≤ n  for every unitary
for label, Umat in [("Hadamard", A), ("diag rot", B), ("holonomy", holo_inv), ("−I", la.scale(-1, I2)), ("I", I2)]:
    check_le(f"re_trace_le_card: Re tr({label}) ≤ 2", "WilsonAction.lean:55 (re_trace_le_card)",
             re_tr(Umat), 2.0, slack=1e-9)
    check_le(f"neg_card_le_re_trace: −2 ≤ Re tr({label})", "WilsonAction.lean:116 (neg_card_le_re_trace)",
             -2.0, re_tr(Umat), slack=1e-9)
# tightness anchors
check("re_trace tight at I: Re tr I = 2 = card", "WilsonAction.lean:55 (tight)", re_tr(I2), 2.0, rel_tol=TOL)
check("re_trace tight at −I: Re tr(−I) = −2 = −card", "WilsonAction.lean:116 (tight)",
      re_tr(la.scale(-1, I2)), -2.0, rel_tol=TOL)

# plaquetteAction_eq: Re tr(1 − U_P) = n − Re tr(U_P)   (form I−U then trace, vs n − tr U)
UP = B
routeA = la.trace(la.sub(I2, UP)).real
routeB = 2.0 - re_tr(UP)
check("plaquetteAction_eq: Re tr(1−U_P) = card − Re tr U_P  (two routes)",
      "WilsonAction.lean:80 (plaquetteAction_eq)", routeA, routeB, rel_tol=1e-9)
# plaquetteAction_nonneg: 0 ≤ n − Re tr U_P;  plaquetteAction_le: ≤ 2n, tight at −I
for label, Umat in [("Hadamard", A), ("diag rot", B), ("holonomy", holo_inv), ("−I", la.scale(-1, I2))]:
    dens = 2.0 - re_tr(Umat)
    check_le(f"plaquetteAction_nonneg: 0 ≤ {label} density", "WilsonAction.lean:86 (plaquetteAction_nonneg)",
             -dens, 0.0, slack=1e-9)
    check_le(f"plaquetteAction_le: {label} density ≤ 2·card = 4", "WilsonAction.lean:129 (plaquetteAction_le)",
             dens, 4.0, slack=1e-9)
check("plaquetteAction_le tight at −I: density = 4 = 2·card",
      "WilsonAction.lean:129 (tight)", 2.0 - re_tr(la.scale(-1, I2)), 4.0, rel_tol=TOL)
check("plaquetteAction_one: vacuum (U_P=I) density = 0",
      "WilsonAction.lean:93 (plaquetteAction_one)", 2.0 - re_tr(I2), 0.0, abs_tol=TOL)

# wilsonAction = β·Σ_p density; nonneg (β≥0); wilsonAction_le ≤ β·#plaq·2n
plaq_holos = [A, B, D, holo_inv]         # 4 plaquettes
beta = 1.7
S = beta * sum(2.0 - re_tr(U) for U in plaq_holos)
S_route2 = beta * (len(plaq_holos) * 2.0 - sum(re_tr(U) for U in plaq_holos))    # factor out identity contribution
check("wilsonAction = β·Σ_p(card − Re tr U_P)  (per-plaquette vs factored routes)",
      "WilsonAction.lean:74 (wilsonAction)", S, S_route2, rel_tol=1e-9)
check_le("wilsonAction_nonneg: 0 ≤ S (β ≥ 0)", "WilsonAction.lean:98 (wilsonAction_nonneg)", -S, 0.0, slack=1e-9)
check_le("wilsonAction_le: S ≤ β·#plaq·2·card", "WilsonAction.lean:137 (wilsonAction_le)",
         S, beta * len(plaq_holos) * (2 * 2.0), slack=1e-9)
check("wilsonAction_one: all-identity config ⇒ S = 0",
      "WilsonAction.lean:104 (wilsonAction_one)", beta * sum(2.0 - re_tr(I2) for _ in plaq_holos), 0.0, abs_tol=TOL)

# norm_entry_le_one: |A_ij| ≤ 1 for a unitary  (entrywise modulus vs column-norm identity Σ_k|A_kj|²=1)
for label, Umat in [("Hadamard", A), ("holonomy", holo_inv)]:
    max_entry = max(abs(Umat[i][j]) for i in range(2) for j in range(2))
    check_le(f"norm_entry_le_one: max|{label}_ij| ≤ 1", "Topology.lean:112 (norm_entry_le_one)",
             max_entry, 1.0, slack=1e-9)
    # column-norm identity (the reason): Σ_k |A_kj|² = 1
    for j in range(2):
        check_le(f"unitary column {j} of {label} is a unit vector: Σ_k|A_kj|² = 1",
                 "Topology.lean:112 (column-norm)", abs(sum(abs(Umat[k][j]) ** 2 for k in range(2)) - 1.0), 1e-9, slack=0)


# ##########################################################################
#  PART C — MEASURE SURROGATES (finite subgroup; clearly labelled)
# ##########################################################################
# Q₈ = {±I, ±iσx, ±iσy, ±iσz} ⊂ SU(2)
Q8 = []
for M0 in [I2, la.scale(1j, sx), la.scale(1j, sy), la.scale(1j, sz)]:
    Q8.append(M0)
    Q8.append(la.scale(-1, M0))


def haar_avg(func, group):
    return sum(func(g) for g in group) / len(group)


# haarUnitary is a PROBABILITY measure (surrogate: uniform average of 1 over Q₈ = 1)
check("haarUnitary probability (surrogate): (1/|Q₈|)Σ 1 = 1",
      "Haar.lean:80 (isProbabilityMeasure_haarUnitary)", haar_avg(lambda g: 1.0, Q8).real, 1.0, rel_tol=TOL)
# LEFT-INVARIANCE (surrogate): (1/|G|)Σ f(h·g) = (1/|G|)Σ f(g) for a NON-constant f  (two routes)
f_obs = lambda g: g[0][0].real           # Re(g₀₀): values {±1,0,…} over Q₈, non-constant
h_shift = la.scale(1j, sx)
avg_shift = haar_avg(lambda g: f_obs(la.matmul(h_shift, g)), Q8)
avg_plain = haar_avg(f_obs, Q8)
check("haarUnitary left-invariance (surrogate): ⟨f(h·)⟩ = ⟨f⟩ over Q₈  (non-constant f)",
      "Haar.lean:88 (IsHaarMeasure / left-invariance)", abs(avg_shift - avg_plain), 0.0, abs_tol=1e-12)

# partitionFunction 0 < Z ≤ 1 (surrogate): Z = uniform average of exp(−S) over a finite config ensemble.
# links valued in Z₄ ⊂ U(1) (n=1, plaquette = phase e^{iθ}); S = β·Σ_p(1 − cos θ_p) ≥ 0.
Z4 = [cmath.exp(2j * math.pi * k / 4) for k in range(4)]     # {1,i,−1,−i}
beta_g = 0.8
P_plaq = 3                                # 3 independent plaquette phases
configs = list(product(Z4, repeat=P_plaq))
def action(cfg):
    return beta_g * sum(1.0 - z.real for z in cfg)            # n=1: card − Re tr = 1 − cos θ
Z = sum(math.exp(-action(cfg)) for cfg in configs) / len(configs)
check_le("partitionFunction Z ≤ 1 (surrogate): mean exp(−S) ≤ 1 since S ≥ 0",
         "GibbsMeasure.lean:111 (partitionFunction_ne_top)", Z, 1.0, slack=1e-12)
check_le("partitionFunction Z > 0 (surrogate): Z ≥ exp(−M), M = β·#plaq·2·card",
         "GibbsMeasure.lean:124 (partitionFunction_pos)", math.exp(-beta_g * P_plaq * 2 * 1), Z, slack=0)
check_le("partitionFunction Z < 1 strictly (surrogate): some config has S>0 for β>0",
         "GibbsMeasure.lean:111 (Z<1)", -(1.0 - Z), -1e-3, slack=0)


# ##########################################################################
#  PART D — RELATIVISTIC SPECTRAL DATA  (Wightman/RelativisticSpectralData.lean)
# ##########################################################################
# rankOneProjection v = |v⟩⟨v|, a star projection for a UNIT vector (P†=P, P²=P, tr P=1).
w = [1.0, 1j]                                                # NON-unit witness (‖w‖² = 2)
wn2 = inner(w, w).real                                       # = 2  (genuinely ≠ 1)
v = [c / math.sqrt(wn2) for c in w]                          # unit vector v = w/‖w‖
Pv = [[v[i] * v[j].conjugate() for j in range(2)] for i in range(2)]      # rankOne |v⟩⟨v| (v normalized)
# independent route: the least-squares projector w(w†w)⁻¹w† = w w†/‖w‖² from the UN-normalized w,
# so the Gram factor is genuinely 1/2 — not the degenerate 1/1 of a unit vector.
Pv2 = [[w[i] * w[j].conjugate() / wn2 for j in range(2)] for i in range(2)]
check("rankOneProjection = |v⟩⟨v|  (v=w/‖w‖ outer vs w(w†w)⁻¹w† from un-normalized w, factor 1/2)",
      "RelativisticSpectralData.lean:173 (rankOneProjection)", la.max_abs_diff(Pv, Pv2), 0.0, abs_tol=TOL)
check("rankOneProjection self-adjoint P† = P",
      "RelativisticSpectralData.lean:177 (isStarProjection)", la.max_abs_diff(la.dagger(Pv), Pv), 0.0, abs_tol=TOL)
check("rankOneProjection idempotent P² = P (unit v)",
      "RelativisticSpectralData.lean:177 (isStarProjection)", la.max_abs_diff(la.matmul(Pv, Pv), Pv), 0.0, abs_tol=TOL)
check("rankOneProjection trace = 1 (rank one)",
      "RelativisticSpectralData.lean:177", la.trace(Pv).real, 1.0, rel_tol=TOL)

# Reflection positivity (surrogate, β=0 free case): ∫ conj(f(ΘU))·f(U) = |∫ f|² over the product measure.
# Z₂ = {+1,−1}, two links (one +, one −) paired by Θ; f a function of the positive link only.
Z2 = [1.0, -1.0]
for fdesc, fpos in [("f=1+u", lambda u: 1.0 + u), ("f=u", lambda u: u), ("f=u+2", lambda u: u + 2.0)]:
    # LHS: average over U=(u₊,u₋) of conj(f(u₋))·f(u₊)   [Θ swaps the two links]
    lhs_rp = sum(fpos(um).conjugate() * fpos(up) for up in Z2 for um in Z2) / (len(Z2) ** 2)
    # RHS: |⟨f⟩|²  over the positive-link measure
    mean_f = sum(fpos(up) for up in Z2) / len(Z2)
    rhs_rp = (mean_f.conjugate() * mean_f) if isinstance(mean_f, complex) else mean_f ** 2
    check(f"reflection positivity (surrogate, {fdesc}): ∫ conj(f(ΘU))f(U) = |⟨f⟩|² ≥ 0",
          "ReflectionPositivity.lean:170 (reflectionPositive_configReflection)",
          abs(complex(lhs_rp) - complex(rhs_rp)), 0.0, abs_tol=1e-12)
    check_le(f"reflection positivity ≥ 0 ({fdesc})", "ReflectionPositivity.lean:170 (≥0)",
             -complex(lhs_rp).real, 0.0, slack=1e-12)


# ##########################################################################
#  FALSIFICATION GUARDS
# ##########################################################################
# (a) Krein form with the WRONG (non-Hermitian) J: ⟪Jx,y⟫ ≠ ⟪x,Jy⟫ (Hermiticity of J is load-bearing).
Jbad = la.mat([[0, 1], [0, 0]])          # not Hermitian, not an involution
check_le("GUARD non-Hermitian J: ⟪Jx,y⟫ ≠ ⟪x,Jy⟫ (fundamental symmetry needs J†=J)",
         "Spaces/Krein/Basic.lean:161 (kreinInner, Hermiticity guard)",
         -abs(inner(la.matvec(Jbad, x), y) - inner(x, la.matvec(Jbad, y))), -1e-2, slack=0)
# (b) plaquette action with '1+U_P' instead of '1−U_P': at the vacuum gives 2·card = 4, not 0.
wrong_vacuum = la.trace(la.add(I2, I2)).real           # Re tr(1+I) = 4  (true vacuum action is 0)
check_le("GUARD sign 1+U vs 1−U: Re tr(1+I) = 4 ≠ 0 (vacuum action) — the minus sign is pinned",
         "WilsonAction.lean:80 (plaquetteAction, sign guard)", -wrong_vacuum, -3.9, slack=0)
# (c) Boltzmann sign: exp(+S) gives Z ≥ 1, violating Z ≤ 1.
Z_wrong = sum(math.exp(+action(cfg)) for cfg in configs) / len(configs)
check_le("GUARD Boltzmann exp(+S): Z_wrong ≥ 1 (violates Z ≤ 1) — the minus in exp(−S) is pinned",
         "GibbsMeasure.lean:111 (gibbsDensity, sign guard)", -(Z_wrong - 1.0), -1e-3, slack=0)
# (d) left-invariance over a NON-subgroup subset (Q₈ minus the identity, whose f-value ≠ 0): the two
#     averages differ (⟨f⟩ = −1/7 vs ⟨f(h·)⟩ = 0), so reindexing is not measure-preserving.
Q7 = Q8[1:]                              # drop I (f(I)=1); Q₈∖{I} is not a subgroup
check_le("GUARD non-subgroup: ⟨f(h·)⟩ ≠ ⟨f⟩ over Q₈∖{g} (invariance requires a genuine subgroup)",
         "Haar.lean:88 (left-invariance, subgroup guard)",
         -abs(haar_avg(lambda g: f_obs(la.matmul(h_shift, g)), Q7) - haar_avg(f_obs, Q7)), -1e-3, slack=0)

finish("Krein spaces / lattice gauge / Wilson action / Haar / reflection-positivity numeric checks")
