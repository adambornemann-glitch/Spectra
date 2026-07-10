"""Numeric checks for the quantum-entropy keystones:

  Spectra/InformationGeometry/Quantum/Entropy/{VonNeumann,Spectral,Diagonal,Gibbs,CrossEntropy}.lean
  Spectra/InformationGeometry/Quantum/KleinScalar.lean

The Lean development is written to be correct in **infinite** dimensions (the
entropy is valued in ``ℝ≥0∞`` and may be ``+∞``; ``log σ`` is unbounded and is
never formed — the cross entropy is read off ``σ``'s scalar spectral measure).
These checks pin the *content* of those statements on finite-dimensional faithful
states, where every quantity is a finite real number and each side of every
theorem can be computed by a genuinely independent route.

Independent-route discipline (the cardinal rule of this suite):

  * von Neumann entropy  S(ρ) = tr(-ρ log ρ)  is computed THREE ways —
      (A) eigenvalue sum   Σ negMulLog λᵢ         (herm eigenvalues + scalar negMulLog)
      (B) operator cfc     Re tr(cfc negMulLog ρ) (matrix negMulLog(ρ) via functional calc)
      (C) literal product  Re tr(-ρ · log ρ)      (matrix log then matmul)
    — validating `vonNeumannEntropy_eq_tsum` (A≡B) *and* that the operator
    definition really is tr(-ρ log ρ) (B≡C).

  * cross entropy  −Tr(ρ log σ)  is computed TWO ways —
      (A) spectral-measure form  Σᵢ λᵢ Σⱼ |⟨eᵢ,fⱼ⟩|² (−log sⱼ)  — the LITERAL Lean
          `crossEntropy` definition: ρ's eigenpairs (λᵢ,eᵢ), σ's eigenpairs (sⱼ,fⱼ),
          integrating −log t against σ's scalar spectral measure at eᵢ;
      (B) operator form  −Re tr(ρ · log σ)  — matrix log σ then matmul.
    The two routes never share an intermediate object; agreement validates the
    nontrivial claim that the spectral-integral form equals −Tr(ρ log σ).

The models are chosen NON-commuting and ρ≠σ so that S(ρ), the measured cross
entropy, and the cross entropy are three DIFFERENT numbers and the relative
entropy D(ρ‖σ) is strictly positive — an expression-identity bug cannot fake a
pass, and the ordering S(ρ) ≤ measuredCrossEntropy ≤ crossEntropy has genuine
slack.  A closing block of executable FALSIFICATION GUARDS recomputes each
headline with a documented mutation (sign flip, ρ↔σ swap, diagonal→eigenvalue)
and asserts the mutation is detected — the permanent, runnable form of the
mutation table in the README.
"""

import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nclib import linalg as la
from nclib.harness import check, check_le, finish

TOL = 1e-8


def inner(u, v):
    """⟨u,v⟩ with conjugation on the FIRST slot (mathlib/physics convention)."""
    return sum(u[i].conjugate() * v[i] for i in range(len(u)))


def neg_mul_log(x):
    """Real.negMulLog x = -x * log x  (with the mathlib convention log 0 = 0, so 0 ↦ 0)."""
    return -x * math.log(x) if x > 1e-300 else 0.0


# --------------------------------------------------------------------------
# Models: faithful (strictly positive), trace-1, NON-commuting, ρ ≠ σ.
# --------------------------------------------------------------------------
# A smaller `floor` than the default keeps them strictly positive (faithful) while
# spreading the eigenvalues and making [ρ,σ] genuinely nonzero — so S(ρ), the measured
# cross entropy, and the cross entropy are three distinct numbers.
rho = la.density_from_seed(3, 7, floor=0.05)
sigma = la.density_from_seed(3, 23, floor=0.05)
n = 3
assert la.max_abs_diff(la.commutator(rho, sigma), la.zeros(n)) > 0.1, "need [ρ,σ]≠0"
assert min(la.herm_eigvalues(rho)) > 1e-3 and min(la.herm_eigvalues(sigma)) > 1e-3, "need faithful"

lam_rho, ev_rho = la.herm_eig(rho)      # ρ eigenpairs (λᵢ, eᵢ)
s_sig, ev_sig = la.herm_eig(sigma)      # σ eigenpairs (sⱼ, fⱼ)


# --------------------------------------------------------------------------
# 1.  ρ's eigenvalues are a probability distribution  (Spectral.lean)
# --------------------------------------------------------------------------
# eigenvalue_nonneg / eigenvalue_le_one : 0 ≤ λᵢ ≤ 1
check_le("QState eigenvalues ≥ 0 (min eigenvalue nonneg)",
         "Entropy/Spectral.lean:79 (eigenvalue_nonneg)", -min(lam_rho), 0.0, slack=1e-12)
check_le("QState eigenvalues ≤ 1 (max eigenvalue ≤ 1)",
         "Entropy/Spectral.lean:139 (eigenvalue_le_one)", max(lam_rho), 1.0, slack=1e-12)
# hasSum_eigenvalue : Σ λᵢ = 1  (independent routes: eigenvalue sum vs direct trace)
check("Σ λᵢ = 1 = Tr ρ  (eigenvalue sum vs direct trace, two routes)",
      "Entropy/Spectral.lean:109 (hasSum_eigenvalue)",
      sum(lam_rho), la.trace(rho).real, rel_tol=1e-9)


# --------------------------------------------------------------------------
# 2.  von Neumann entropy S(ρ) = tr(-ρ log ρ) = Σ negMulLog λᵢ  (three routes)
# --------------------------------------------------------------------------
S_A = sum(neg_mul_log(l) for l in lam_rho)                       # (A) eigenvalue sum
S_B = la.trace(la.herm_func(rho, neg_mul_log)).real             # (B) cfc negMulLog
S_C = la.trace(la.scale(-1.0, la.matmul(rho, la.herm_log(rho)))).real  # (C) -ρ·log ρ

# vonNeumannEntropy_eq_tsum : the operator definition equals the eigenvalue-sum (Shannon) form
check("S(ρ) : Σ negMulLog λᵢ = Re tr(cfc negMulLog ρ)  (spectral form = operator form)",
      "Entropy/Spectral.lean:150 (vonNeumannEntropy_eq_tsum)", S_A, S_B, rel_tol=1e-8)
# the operator `entropyOp ρ = cfc negMulLog ρ` really is the literal `-ρ log ρ`
check("S(ρ) : Re tr(cfc negMulLog ρ) = Re tr(-ρ log ρ)  (cfc form = literal product)",
      "Entropy/VonNeumann.lean:94 (entropyOp = cfc Real.negMulLog ρ)", S_B, S_C, rel_tol=1e-8)
# nonnegativity (entropyOp_nonneg / vonNeumannEntropy_nonneg): a MIXED state has S > 0
check_le("S(ρ) ≥ 0  and strictly positive for a mixed state",
         "Entropy/VonNeumann.lean:120 (vonNeumannEntropy_nonneg)", -S_A, -1e-3, slack=0)

# entropyOp_nonneg literally: -ρ log ρ ⪰ 0  (all eigenvalues ≥ 0)
entropyOp = la.herm_func(rho, neg_mul_log)
check_le("entropyOp ρ = -ρ log ρ is positive-semidefinite (min eig ≥ 0)",
         "Entropy/VonNeumann.lean:99 (entropyOp_nonneg)",
         -min(la.herm_eigvalues(entropyOp)), 0.0, slack=1e-9)


# --------------------------------------------------------------------------
# 3.  Pure states have zero entropy  (VonNeumann.lean)
# --------------------------------------------------------------------------
psi = [c / math.sqrt(sum(abs(z) ** 2 for z in [0.6, 0.8j, 0.5]))
       for c in [0.6, 0.8j, 0.5]]
Ppure = [[psi[i] * psi[j].conjugate() for j in range(n)] for i in range(n)]  # |ψ⟩⟨ψ|
check("Tr|ψ⟩⟨ψ| = 1 (pureState is a genuine state)",
      "Entropy/VonNeumann.lean:125 (pureState)", la.trace(Ppure).real, 1.0, rel_tol=1e-12)
# entropyOp_pure : -|ψ⟩⟨ψ| log|ψ⟩⟨ψ| = 0
check("entropyOp of a pure state is the zero operator",
      "Entropy/VonNeumann.lean:137 (entropyOp_pure)",
      la.fro_norm(la.herm_func(Ppure, neg_mul_log)), 0.0, abs_tol=1e-8)
# vonNeumannEntropy_pure : S(|ψ⟩⟨ψ|) = 0
check("S(|ψ⟩⟨ψ|) = 0  (pure state has zero entropy)",
      "Entropy/VonNeumann.lean:152 (vonNeumannEntropy_pure)",
      sum(neg_mul_log(l) for l in la.herm_eigvalues(Ppure)), 0.0, abs_tol=1e-8)


# --------------------------------------------------------------------------
# 4.  EXTERNAL ANCHOR: S(I/d) = log d  (pins the sign and the log base)
#     Not a Lean theorem, but the maximally-mixed state's entropy is the one
#     value that a wrong sign (→ -log d < 0) or wrong base could not fake.
# --------------------------------------------------------------------------
maxmix = la.scale(1.0 / n, la.eye(n))
check("S(I/d) = log d  (max entropy anchor: sign + natural-log base)",
      "Entropy/VonNeumann.lean:108 (vonNeumannEntropy, external anchor)",
      la.trace(la.herm_func(maxmix, neg_mul_log)).real, math.log(n), rel_tol=1e-9)


# --------------------------------------------------------------------------
# 5.  σ's diagonal in ρ's eigenbasis  (Diagonal.lean)
# --------------------------------------------------------------------------
# diagSigma ρ σ i = re⟨eᵢ, σ eᵢ⟩
diagS = [inner(ev_rho[i], la.matvec(sigma, ev_rho[i])).real for i in range(n)]
check_le("diagSigma sᵢ ≥ 0  (σ positive)",
         "Entropy/Diagonal.lean:38 (diagSigma_nonneg)", -min(diagS), 0.0, slack=1e-12)
check_le("diagSigma sᵢ ≤ 1",
         "Entropy/Diagonal.lean:42 (diagSigma_le_one)", max(diagS), 1.0, slack=1e-12)
# hasSum_diagSigma : Σ sᵢ = Tr σ = 1  (diagonal-in-ρ-basis vs direct trace of σ)
check("Σ sᵢ = 1 = Tr σ  (σ diagonal in ρ's basis vs direct trace, two routes)",
      "Entropy/Diagonal.lean:54 (hasSum_diagSigma)", sum(diagS), la.trace(sigma).real, rel_tol=1e-9)
# the diagonal is genuinely NOT σ's eigenvalues (ρ,σ don't commute) — the distinction is real content
diag_vs_eig = max(abs(a - b) for a, b in zip(sorted(diagS), sorted(s_sig)))
check_le("σ's ρ-diagonal ≠ σ's eigenvalues (non-commuting: diagonal is genuine content)",
         "Entropy/Diagonal.lean:34 (diagSigma)", -diag_vs_eig, -1e-2, slack=0)


# --------------------------------------------------------------------------
# 6.  measured cross entropy and the Gibbs (commuting-case Klein) inequality
# --------------------------------------------------------------------------
# measuredCrossEntropy ρ σ = Σᵢ -λᵢ log sᵢ
measured = sum(-lam_rho[i] * math.log(diagS[i]) for i in range(n))
# vonNeumannEntropy_le_measuredCrossEntropy : S(ρ) ≤ Σ -λᵢ log sᵢ   (Gibbs, faithful σ)
check_le("Gibbs: S(ρ) ≤ Σ -λᵢ log sᵢ  (measured cross entropy, non-commuting σ)",
         "Entropy/Gibbs.lean:56 (vonNeumannEntropy_le_measuredCrossEntropy)",
         S_A, measured, slack=1e-9)
# the bound has genuine slack here (S(ρ) strictly below the measured cross entropy)
check_le("Gibbs bound has slack: S(ρ) < Σ -λᵢ log sᵢ (not a vacuous equality)",
         "Entropy/Gibbs.lean:56 (Gibbs slack)", -(measured - S_A), -1e-3, slack=0)


# --------------------------------------------------------------------------
# 7.  the cross entropy −Tr(ρ log σ), two independent routes, and Klein
# --------------------------------------------------------------------------
# (A) spectral-measure form: the LITERAL Lean `crossEntropy` definition
cross_A = 0.0
for i in range(n):
    for j in range(n):
        overlap = abs(inner(ev_rho[i], ev_sig[j])) ** 2      # |⟨eᵢ, fⱼ⟩|²  = μ_{eᵢ}({sⱼ})
        cross_A += lam_rho[i] * overlap * (-math.log(s_sig[j]))
# (B) operator form −Re tr(ρ log σ)
cross_B = -la.trace(la.matmul(rho, la.herm_log(sigma))).real
check("crossEntropy(ρ,σ) : spectral-measure form = −Re tr(ρ log σ)  (two independent routes)",
      "Entropy/CrossEntropy.lean:240 (crossEntropy)", cross_A, cross_B, rel_tol=1e-8)

# measuredCrossEntropy_le_crossEntropy : the Jensen bridge  (dephased ≤ genuine)
check_le("Jensen bridge: measuredCrossEntropy ≤ crossEntropy",
         "Entropy/CrossEntropy.lean:291 (measuredCrossEntropy_le_crossEntropy)",
         measured, cross_A, slack=1e-9)

# vonNeumannEntropy_le_crossEntropy : the FULL Klein inequality  S(ρ) ≤ −Tr(ρ log σ)
check_le("Klein: S(ρ) ≤ crossEntropy(ρ,σ) = −Tr(ρ log σ)  (full Umegaki form)",
         "Entropy/CrossEntropy.lean:300 (vonNeumannEntropy_le_crossEntropy)",
         S_A, cross_A, slack=1e-9)
# relative entropy D(ρ‖σ) = crossEntropy − S(ρ) is STRICTLY positive for ρ≠σ (Klein sharp only at ρ=σ)
D_rho_sig = cross_A - S_A
check_le("D(ρ‖σ) = crossEntropy − S(ρ) > 0  strictly (ρ ≠ σ)",
         "Entropy/CrossEntropy.lean:300 (relative entropy positivity, strict)",
         -D_rho_sig, -1e-3, slack=0)

# crossEntropy_self : crossEntropy(ρ,ρ) = S(ρ), i.e. D(ρ‖ρ) = 0  (non-vacuity + equality case).
# Computed by the SAME spectral-measure route as cross_A but with σ := ρ; the overlaps
# |⟨eᵢ,eⱼ⟩|² collapse to δ_{ij} (orthonormal eigenbasis), so it should recover S(ρ).
cross_self = 0.0
for i in range(n):
    for j in range(n):
        overlap = abs(inner(ev_rho[i], ev_rho[j])) ** 2       # = δ_{ij}
        cross_self += lam_rho[i] * overlap * (-math.log(lam_rho[j]))
check("crossEntropy(ρ,ρ) = S(ρ)  (non-vacuity; D(ρ‖ρ)=0 = Klein equality case)",
      "Entropy/CrossEntropy.lean:348 (crossEntropy_self)", cross_self, S_A, rel_tol=1e-8)


# --------------------------------------------------------------------------
# 8.  the scalar Klein inequality  λ − μ ≤ λ·log(λ/μ)   (KleinScalar.lean)
# --------------------------------------------------------------------------
# checked where the two sides genuinely differ, including λ<μ (LHS negative) and λ>μ
for (lam, mu) in [(0.7, 0.2), (0.2, 0.7), (0.5, 0.5), (0.9, 0.05), (0.0, 0.3)]:
    lhs = lam - mu
    rhs = lam * math.log(lam / mu) if lam > 0 else 0.0    # 0·log(0/μ) = 0 branch of Real.negMulLog
    check_le(f"scalar Klein: λ−μ ≤ λ log(λ/μ)  (λ={lam}, μ={mu})",
             "KleinScalar.lean:38 (Real.klein_scalar)", lhs, rhs, slack=1e-12)
# rearranged form mul_log_sub_mul_log_ge : λ−μ ≤ λ log λ − λ log μ  (λ,μ>0)
lam, mu = 0.7, 0.2
check_le("scalar Klein rearranged: λ−μ ≤ λ log λ − λ log μ",
         "KleinScalar.lean:51 (mul_log_sub_mul_log_ge)",
         lam - mu, lam * math.log(lam) - lam * math.log(mu), slack=1e-12)


# --------------------------------------------------------------------------
# 9.  FALSIFICATION GUARDS — executable mutation testing.
#     Each recomputes a headline with a documented WRONG transcription and
#     asserts the mutation is DETECTED (the guard PASSES iff the mutant fails
#     the theorem).  This is the permanent form of the README mutation table.
# --------------------------------------------------------------------------
# (a) Klein with the sign flipped: mis-signed relative entropy D_mut = +Tr(ρ log σ) − S(ρ).
#     The correct cross term is −Tr(ρ log σ); flipping it makes D_mut = −cross_A − S_A < 0,
#     so the mis-signed "Klein" S(ρ) ≤ +Tr(ρ log σ) is violated.
D_mut = la.trace(la.matmul(rho, la.herm_log(sigma))).real - S_A
check_le("GUARD sign-flip: mis-signed D = +Tr(ρ log σ) − S(ρ) is NEGATIVE (mutation detected)",
         "Entropy/CrossEntropy.lean:300 (Klein, sign guard)", D_mut, -1e-3, slack=0)

# (b) argument-order swap: crossEntropy(σ,ρ) ≠ crossEntropy(ρ,σ) — the order is genuine content.
cross_swapped = -la.trace(la.matmul(sigma, la.herm_log(rho))).real
check_le("GUARD ρ↔σ swap: crossEntropy(σ,ρ) ≠ crossEntropy(ρ,σ) (argument order matters)",
         "Entropy/CrossEntropy.lean:240 (crossEntropy, order guard)",
         -abs(cross_swapped - cross_A), -1e-2, slack=0)

# (c) Gibbs with σ's EIGENVALUES (sorted-matched) instead of the ρ-diagonal: a different number,
#     so the "use the diagonal" content is not vacuous.  (min-matched to give the mutant its best shot.)
measured_eig = sum(-a * math.log(b) for a, b in zip(sorted(lam_rho, reverse=True),
                                                    sorted(s_sig, reverse=True)))
check_le("GUARD diagonal→eigenvalue: Σ-λᵢlog(σ-eig) ≠ Σ-λᵢlog(sᵢ) (diagonal is required)",
         "Entropy/Gibbs.lean:51 (measuredCrossEntropy, diagonal guard)",
         -abs(measured_eig - measured), -1e-3, slack=0)

# (d) wrong entropy sign  S'(ρ) = +Σ λᵢ log λᵢ = −S(ρ) < 0 for a mixed state ⇒ "S≥0" violated.
S_wrong = sum(l * math.log(l) for l in lam_rho if l > 1e-300)
check_le("GUARD entropy sign: S' = +Σ λᵢ log λᵢ is NEGATIVE for a mixed state (mutation detected)",
         "Entropy/VonNeumann.lean:120 (nonneg, sign guard)", S_wrong, -1e-3, slack=0)


finish("Quantum entropy / Klein / Gibbs / cross-entropy numeric checks")
