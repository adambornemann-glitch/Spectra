/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Channels.TraceClass.Triangle

/-!
# Stage F — the trace-class operators as a normed space (toward Banach)

The trace-class operators form a `ℂ`-submodule of `H →L[ℂ] H` (`traceClassSubmodule`), and the
trace norm `‖·‖₁` dominates the operator norm: `‖T‖ ≤ ‖T‖₁`.  The latter is the key comparison
making `‖·‖₁`-Cauchy sequences operator-norm Cauchy, the first step toward Banach completeness.

## Main results

* `isTraceClass_smul`, `traceNorm_neg` — scalar/negation stability of the trace class and its norm.
* `traceClassSubmodule` — the trace-class operators as a `Submodule ℂ (H →L[ℂ] H)`.
* `norm_le_traceNorm` — **`‖T‖ ≤ ‖T‖₁`** (operator norm dominated by trace norm)
  for trace-class `T`.
* `TraceClass H` — the trace-class operators as a **type** (a non-reducible synonym of the
  submodule, to avoid the operator-norm/trace-norm instance diamond), with the trace norm `‖·‖₁`.
* `TraceClass.instNormedAddCommGroup`, `TraceClass.instNormedSpace` — **`TraceClass H` is a
  `ℂ`-normed space** in the trace norm (F2), built from a `NormedSpace.Core`.
* `isTraceClass_and_traceNorm_le_of_tendsto` — **Fatou / lower semicontinuity** of the trace norm:
  the operator-norm limit of a trace-norm-bounded sequence is trace-class with the limiting bound.
* `TraceClass.instCompleteSpace` — **`TraceClass H` is complete** (a `ℂ`-Banach space) (F3).

## Context

Sixth brick of the trace-class / von Neumann predual development (the discharge-first route to the
Tomita–Takesaki fundamental theorem), building on the triangle inequality (`Triangle.lean`).
-/

open ContinuousLinearMap RCLike
open scoped InnerProductSpace InnerProduct ENNReal NNReal

namespace Spectra.QuantumMechanics.Channels

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Scalar and negation stability -/

/-- The trace class is closed under scalar multiplication. -/
theorem isTraceClass_smul (c : ℂ) {T : H →L[ℂ] H} (hT : IsTraceClass T) : IsTraceClass (c • T) := by
  change posTrace (stdHilbertBasis H) (absOp (c • T)) ≠ ⊤
  rw [posTrace_absOp_smul]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT

/-- `‖-T‖₁ = ‖T‖₁`. -/
@[simp] theorem traceNorm_neg (T : H →L[ℂ] H) : traceNorm (-T) = traceNorm T := by
  rw [← neg_one_smul ℂ T, traceNorm_smul]
  simp

/-! ## The trace-class submodule -/

variable (H) in
/-- The **trace-class operators** as a `ℂ`-submodule of `H →L[ℂ] H`. -/
def traceClassSubmodule : Submodule ℂ (H →L[ℂ] H) where
  carrier := {T | IsTraceClass T}
  add_mem' hS hT := isTraceClass_add hS hT
  zero_mem' := isTraceClass_zero
  smul_mem' c _ hT := isTraceClass_smul c hT

@[simp] lemma mem_traceClassSubmodule {T : H →L[ℂ] H} :
    T ∈ traceClassSubmodule H ↔ IsTraceClass T := Iff.rfl

/-! ## The operator norm is dominated by the trace norm -/

/-- **`‖T‖ ≤ ‖T‖₁`** for trace-class `T`.  Writing `T = |T|^{1/2} · (|T|^{1/2} U⋆ ·)` is not needed:
via Parseval and Cauchy–Schwarz, `‖|T|^{1/2} y‖² ≤ ‖T‖₁ · ‖y‖²`, so
`‖T x‖ = ‖|T|^{1/2} (|T|^{1/2} x)‖ ≤ ‖T‖₁ · ‖x‖`. -/
theorem norm_le_traceNorm {T : H →L[ℂ] H} (hT : IsTraceClass T) : ‖T‖ ≤ traceNorm T := by
  have hRsa : (sqrtOp (absOp T))† = sqrtOp (absOp T) := by
    rw [← star_eq_adjoint]; exact (sqrtOp_isSelfAdjoint (absOp T)).star_eq
  -- Parseval + Cauchy–Schwarz: ‖|T|^{1/2} y‖² ≤ ‖T‖₁ · ‖y‖²
  have hRsq : ∀ y, ‖sqrtOp (absOp T) y‖ ^ 2 ≤ traceNorm T * ‖y‖ ^ 2 := by
    intro y
    have hterm : ∀ j, ‖⟪stdHilbertBasis H j, sqrtOp (absOp T) y⟫_ℂ‖ ^ 2
        ≤ ‖sqrtOp (absOp T) (stdHilbertBasis H j)‖ ^ 2 * ‖y‖ ^ 2 := by
      intro j
      have hswap : ⟪stdHilbertBasis H j, sqrtOp (absOp T) y⟫_ℂ
          = ⟪sqrtOp (absOp T) (stdHilbertBasis H j), y⟫_ℂ := by
        have h := adjoint_inner_left (sqrtOp (absOp T)) y (stdHilbertBasis H j)
        rw [hRsa] at h; exact h.symm
      rw [hswap]
      calc ‖⟪sqrtOp (absOp T) (stdHilbertBasis H j), y⟫_ℂ‖ ^ 2
          ≤ (‖sqrtOp (absOp T) (stdHilbertBasis H j)‖ * ‖y‖) ^ 2 := by
            gcongr; exact norm_inner_le_norm _ _
        _ = ‖sqrtOp (absOp T) (stdHilbertBasis H j)‖ ^ 2 * ‖y‖ ^ 2 := by rw [mul_pow]
    calc ‖sqrtOp (absOp T) y‖ ^ 2
        = ∑' j, ‖⟪stdHilbertBasis H j, sqrtOp (absOp T) y⟫_ℂ‖ ^ 2 :=
          (hasSum_norm_inner_sq (stdHilbertBasis H) (sqrtOp (absOp T) y)).tsum_eq.symm
      _ ≤ ∑' j, ‖sqrtOp (absOp T) (stdHilbertBasis H j)‖ ^ 2 * ‖y‖ ^ 2 :=
          Summable.tsum_le_tsum hterm
            (hasSum_norm_inner_sq (stdHilbertBasis H) (sqrtOp (absOp T) y)).summable
            ((summable_sqrtOp_absOp_sq hT).mul_right (‖y‖ ^ 2))
      _ = (∑' j, ‖sqrtOp (absOp T) (stdHilbertBasis H j)‖ ^ 2) * ‖y‖ ^ 2 := tsum_mul_right
      _ = traceNorm T * ‖y‖ ^ 2 := by rw [tsum_sqrtOp_absOp_sq]
  refine ContinuousLinearMap.opNorm_le_bound _ (traceNorm_nonneg T) fun x => ?_
  have hTx : ‖T x‖ ^ 2 ≤ (traceNorm T * ‖x‖) ^ 2 := by
    have hx : ‖T x‖ = ‖sqrtOp (absOp T) (sqrtOp (absOp T) x)‖ := by
      rw [← norm_absOp_apply T x, ← ContinuousLinearMap.mul_apply,
        sqrtOp_mul_self (absOp T) (absOp_nonneg T)]
    rw [hx]
    calc ‖sqrtOp (absOp T) (sqrtOp (absOp T) x)‖ ^ 2
        ≤ traceNorm T * ‖sqrtOp (absOp T) x‖ ^ 2 := hRsq _
      _ ≤ traceNorm T * (traceNorm T * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hRsq x) (traceNorm_nonneg T)
      _ = (traceNorm T * ‖x‖) ^ 2 := by ring
  have hnn : 0 ≤ traceNorm T * ‖x‖ := mul_nonneg (traceNorm_nonneg T) (norm_nonneg x)
  have h := Real.sqrt_le_sqrt hTx
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hnn] at h

/-! ## F2 — the trace-class operators as a normed space `TraceClass H`

The trace-class operators are packaged as a **non-reducible type synonym** `TraceClass H` of the
submodule `↥(traceClassSubmodule H)`, carrying the trace norm `‖·‖₁`.  We must NOT put a
`NormedAddCommGroup` on the submodule directly: a submodule of `B(H)` already inherits the
*operator* norm, and adding the trace norm would create an instance diamond.  Using a fresh
(non-reducible) synonym severs that inheritance, so the trace norm is the only norm in scope. -/

/-- The trace class is closed under subtraction (it is a submodule of `B(H)`). -/
theorem isTraceClass_sub {S T : H →L[ℂ] H} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    IsTraceClass (S - T) :=
  (mem_traceClassSubmodule).1
    ((traceClassSubmodule H).sub_mem ((mem_traceClassSubmodule).2 hS)
      ((mem_traceClassSubmodule).2 hT))

variable (H) in
/-- The **trace-class operators** as a type, a non-reducible synonym of `↥(traceClassSubmodule H)`.
Carries the trace norm `‖·‖₁` (`TraceClass.instNorm`), making it a `ℂ`-Banach space (F2 gives the
normed-space structure, F3 completeness). -/
def TraceClass : Type _ := ↥(traceClassSubmodule H)

namespace TraceClass

instance : AddCommGroup (TraceClass H) := inferInstanceAs (AddCommGroup ↥(traceClassSubmodule H))
instance : Module ℂ (TraceClass H) := inferInstanceAs (Module ℂ ↥(traceClassSubmodule H))

/-- The underlying bounded operator of a trace-class element. -/
def toOp (T : TraceClass H) : H →L[ℂ] H := (T : ↥(traceClassSubmodule H)).1

/-- The underlying operator is trace-class. -/
theorem isTraceClass (T : TraceClass H) : IsTraceClass T.toOp :=
  (mem_traceClassSubmodule).1 (T : ↥(traceClassSubmodule H)).2

@[simp] theorem toOp_zero : (0 : TraceClass H).toOp = 0 := rfl

@[simp] theorem toOp_add (S T : TraceClass H) : (S + T).toOp = S.toOp + T.toOp := rfl

@[simp] theorem toOp_smul (c : ℂ) (T : TraceClass H) : (c • T).toOp = c • T.toOp := rfl

@[simp] theorem toOp_neg (T : TraceClass H) : (-T).toOp = -T.toOp := rfl

@[simp] theorem toOp_sub (S T : TraceClass H) : (S - T).toOp = S.toOp - T.toOp := rfl

@[simp] theorem toOp_mk (A : H →L[ℂ] H) (hA : A ∈ traceClassSubmodule H) :
    (show TraceClass H from ⟨A, hA⟩).toOp = A := rfl

/-- Trace-class elements are equal iff their underlying operators agree. -/
@[ext] theorem ext {S T : TraceClass H} (h : S.toOp = T.toOp) : S = T :=
  show (S : ↥(traceClassSubmodule H)) = (T : ↥(traceClassSubmodule H)) from Subtype.ext h

/-- The trace norm on `TraceClass H`. -/
noncomputable instance instNorm : Norm (TraceClass H) := ⟨fun T => traceNorm T.toOp⟩

@[simp] theorem norm_def (T : TraceClass H) : ‖T‖ = traceNorm T.toOp := rfl

/-- The `NormedSpace.Core` for the trace norm: nonnegativity, absolute homogeneity, the triangle
inequality, and definiteness (definiteness uses `norm_le_traceNorm`: `‖T‖ = 0 ⟹ ‖T.toOp‖ ≤ 0`). -/
theorem core : NormedSpace.Core ℂ (TraceClass H) where
  norm_nonneg T := traceNorm_nonneg T.toOp
  norm_smul c T := by
    change traceNorm (c • T).toOp = ‖c‖ * traceNorm T.toOp
    rw [toOp_smul, traceNorm_smul]
  norm_triangle S T := by
    change traceNorm (S + T).toOp ≤ traceNorm S.toOp + traceNorm T.toOp
    rw [toOp_add]
    exact traceNorm_add_le S.isTraceClass T.isTraceClass
  norm_eq_zero_iff T := by
    change traceNorm T.toOp = 0 ↔ T = 0
    constructor
    · intro h
      have hop : ‖T.toOp‖ ≤ 0 := (norm_le_traceNorm T.isTraceClass).trans h.le
      exact TraceClass.ext (norm_le_zero_iff.1 hop |>.trans toOp_zero.symm)
    · intro h
      rw [h, toOp_zero, traceNorm_zero]

noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (TraceClass H) :=
  NormedAddCommGroup.ofCore core

noncomputable instance instNormedSpace : NormedSpace ℂ (TraceClass H) :=
  NormedSpace.ofCore core

/-- **The operator norm is dominated by the trace norm** on `TraceClass H`: `‖T.toOp‖ ≤ ‖T‖`.
This is `norm_le_traceNorm` restated through the `TraceClass` synonym (`‖T‖ = ‖T.toOp‖₁`);
it makes the `toOp` map `1`-Lipschitz, hence `‖·‖₁`-Cauchy sequences operator-norm Cauchy —
the completeness input. -/
theorem norm_toOp_le (T : TraceClass H) : ‖T.toOp‖ ≤ ‖T‖ :=
  norm_le_traceNorm T.isTraceClass

end TraceClass

/-! ## F3 — completeness of the trace norm (`TraceClass H` is a Banach space)

The key ingredient is a **lower-semicontinuity / Fatou** estimate: if `Xₙ → A` in operator norm and
`tr |Xₙ| ≤ C` uniformly, then `tr |A| ≤ C` (so `A` is trace-class with `‖A‖₁ ≤ C`).  Each finite
diagonal partial sum `∑_{i∈F} ⟪eᵢ, |X| eᵢ⟫` is operator-norm continuous in `X` (via
`CFC.continuous_abs` and continuity of evaluation / inner product), so passes to the limit `A` and
stays `≤ C`; taking the supremum over finite `F` (`ENNReal.tsum_eq_iSup_sum`) gives `tr |A| ≤ C`.

Applying this to `Xₙ = Tₙ - Tₘ` for a `‖·‖₁`-Cauchy sequence `Tₙ` (which is operator-norm Cauchy by
`norm_le_traceNorm`, hence operator-norm convergent to some `A`, `[CompleteSpace H]`) shows both
that `A` is trace-class and that `Tₘ → A` in trace norm — completeness. -/

/-- Each diagonal entry `re ⟪e, |X| e⟫ = ‖|X|^{1/2} e‖² ≥ 0` is nonnegative. -/
theorem re_inner_absOp_nonneg (X : H →L[ℂ] H) (e : H) : 0 ≤ re ⟪e, absOp X e⟫_ℂ := by
  rw [← norm_sqrtOp_sq (absOp X) (absOp_nonneg X) e]; positivity

/-- If `Xₙ → A` in operator norm, then the diagonal `re ⟪e, |Xₙ| e⟫ → re ⟪e, |A| e⟫`.  Uses that the
modulus `X ↦ |X|` is operator-norm continuous (`CFC.continuous_abs`), evaluation at `e` is
continuous, inner product is continuous, and `RCLike.re` is continuous. -/
theorem tendsto_re_inner_absOp_of_tendsto {ι : Type*} {l : Filter ι} {X : ι → H →L[ℂ] H}
    {A : H →L[ℂ] H} (hX : Filter.Tendsto X l (nhds A)) (e : H) :
    Filter.Tendsto (fun n => re ⟪e, absOp (X n) e⟫_ℂ) l (nhds (re ⟪e, absOp A e⟫_ℂ)) := by
  have habs : Filter.Tendsto (fun n => absOp (X n)) l (nhds (absOp A)) :=
    ((CFC.continuous_abs (A := H →L[ℂ] H)).tendsto A).comp hX
  have hcont : Continuous fun Y : H →L[ℂ] H => re ⟪e, Y e⟫_ℂ :=
    (RCLike.continuous_re.comp
      ((continuous_const.inner ((ContinuousLinearMap.apply ℂ H e).continuous))))
  exact (hcont.tendsto (absOp A)).comp habs

/-- **Fatou / lower semicontinuity of the trace norm.** If `Xₙ → A` in operator norm and every `Xₙ`
is trace-class with `‖Xₙ‖₁ ≤ C` (`0 ≤ C`), then `A` is trace-class with `‖A‖₁ ≤ C`.  Each finite
diagonal partial sum is operator-norm continuous, so `≤ C` passes to the limit `A`; the sup over
finite sets gives `tr |A| ≤ ofReal C < ∞`. -/
theorem isTraceClass_and_traceNorm_le_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {X : ι → H →L[ℂ] H} {A : H →L[ℂ] H} (hX : Filter.Tendsto X l (nhds A))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᶠ n in l, IsTraceClass (X n) ∧ traceNorm (X n) ≤ C) :
    IsTraceClass A ∧ traceNorm A ≤ C := by
  set e := stdHilbertBasis H with _he
  -- Each finite partial sum of the diagonal of |A| is ≤ C.
  have hpartial : ∀ F : Finset _,
      ∑ i ∈ F, ENNReal.ofReal (re ⟪e i, absOp A (e i)⟫_ℂ) ≤ ENNReal.ofReal C := by
    intro F
    -- Real partial sum for A is the limit of the real partial sums for Xₙ.
    have htend : Filter.Tendsto (fun n => ∑ i ∈ F, re ⟪e i, absOp (X n) (e i)⟫_ℂ) l
        (nhds (∑ i ∈ F, re ⟪e i, absOp A (e i)⟫_ℂ)) :=
      tendsto_finsetSum F fun i _ => tendsto_re_inner_absOp_of_tendsto hX (e i)
    -- Each partial sum for Xₙ is ≤ C, eventually.
    have hle : ∀ᶠ n in l, ∑ i ∈ F, re ⟪e i, absOp (X n) (e i)⟫_ℂ ≤ C := by
      filter_upwards [hbound] with n hn
      have hsum : ∑ i ∈ F, ENNReal.ofReal (re ⟪e i, absOp (X n) (e i)⟫_ℂ)
          ≤ posTrace e (absOp (X n)) := by
        rw [posTrace_eq_tsum_ofReal e (absOp_nonneg (X n))]
        exact ENNReal.sum_le_tsum F
      have hfin : ∑ i ∈ F, ENNReal.ofReal (re ⟪e i, absOp (X n) (e i)⟫_ℂ) ≤ ENNReal.ofReal C := by
        refine hsum.trans ?_
        rw [← ENNReal.ofReal_toReal hn.1]
        exact ENNReal.ofReal_le_ofReal hn.2
      rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => re_inner_absOp_nonneg (X n) (e i)] at hfin
      exact (ENNReal.ofReal_le_ofReal_iff hC).1 hfin
    -- Pass the ℝ-inequality to the limit, then to ℝ≥0∞.
    have hAle : ∑ i ∈ F, re ⟪e i, absOp A (e i)⟫_ℂ ≤ C := le_of_tendsto htend hle
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => re_inner_absOp_nonneg A (e i)]
    exact ENNReal.ofReal_le_ofReal hAle
  -- Sup over finite F gives tr |A| ≤ ofReal C.
  have htr : posTrace e (absOp A) ≤ ENNReal.ofReal C := by
    rw [posTrace_eq_tsum_ofReal e (absOp_nonneg A), ENNReal.tsum_eq_iSup_sum]
    exact iSup_le hpartial
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top htr, ?_⟩
  calc traceNorm A = (posTrace e (absOp A)).toReal := rfl
    _ ≤ (ENNReal.ofReal C).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top htr
    _ = C := ENNReal.toReal_ofReal hC

namespace TraceClass

/-- **`TraceClass H` is complete** — the trace-class operators are a Banach space in `‖·‖₁`.

Given a `‖·‖₁`-Cauchy sequence `Tₙ`, the underlying operators `(Tₙ).toOp` are
operator-norm Cauchy (`norm_toOp_le`), hence operator-norm convergent to some `A`
(`[CompleteSpace H]`).  The Fatou estimate
`isTraceClass_and_traceNorm_le_of_tendsto` applied to `k ↦ (Tₖ).toOp - (Tₘ).toOp → A - (Tₘ).toOp`
shows `A - (Tₘ).toOp` is trace-class (so `A` is, taking one `m`) and `‖A - (Tₘ).toOp‖₁ ≤ ε` for
`m ≥ N`; therefore `Tₘ → ⟨A, _⟩` in trace norm. -/
noncomputable instance instCompleteSpace : CompleteSpace (TraceClass H) := by
  refine Metric.complete_of_cauchySeq_tendsto fun T hT => ?_
  -- The trace-norm Cauchy criterion in ε–N form.
  have hcauchy : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      traceNorm ((T m).toOp - (T n).toOp) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hT ε hε
    exact ⟨N, fun m hm n hn => by
      have := hN m hm n hn
      rwa [dist_eq_norm, norm_def, toOp_sub] at this⟩
  -- (Tₙ).toOp is operator-norm Cauchy, hence convergent to some A.
  have hopCauchy : CauchySeq fun n => (T n).toOp := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    calc ‖(T m).toOp - (T n).toOp‖
        ≤ traceNorm ((T m).toOp - (T n).toOp) :=
          norm_le_traceNorm (isTraceClass_sub (T m).isTraceClass (T n).isTraceClass)
      _ < ε := hN m hm n hn
  obtain ⟨A, hA⟩ := cauchySeq_tendsto_of_complete hopCauchy
  -- For each fixed m ≥ N: A - (Tₘ).toOp is trace-class and ‖A - (Tₘ).toOp‖₁ ≤ ε.
  have hkey : ∀ ε > 0, ∃ N, ∀ m ≥ N,
      IsTraceClass (A - (T m).toOp) ∧ traceNorm (A - (T m).toOp) ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy ε hε
    refine ⟨N, fun m hm => ?_⟩
    -- k ↦ (Tₖ).toOp - (Tₘ).toOp → A - (Tₘ).toOp in operator norm.
    have htendk : Filter.Tendsto (fun k => (T k).toOp - (T m).toOp) Filter.atTop
        (nhds (A - (T m).toOp)) := hA.sub tendsto_const_nhds
    -- and each such term is trace-class with trace norm ≤ ε (eventually, for k ≥ N).
    have hbnd : ∀ᶠ k in Filter.atTop,
        IsTraceClass ((T k).toOp - (T m).toOp) ∧ traceNorm ((T k).toOp - (T m).toOp) ≤ ε := by
      filter_upwards [Filter.eventually_ge_atTop N] with k hk
      exact ⟨isTraceClass_sub (T k).isTraceClass (T m).isTraceClass, (hN k hk m hm).le⟩
    exact isTraceClass_and_traceNorm_le_of_tendsto htendk hε.le hbnd
  -- A is trace-class (apply hkey with ε = 1).
  have hAtc : IsTraceClass A := by
    obtain ⟨N, hN⟩ := hkey 1 one_pos
    have hdiff : IsTraceClass (A - (T N).toOp) := (hN N le_rfl).1
    have : A = (A - (T N).toOp) + (T N).toOp := by abel
    rw [this]; exact isTraceClass_add hdiff (T N).isTraceClass
  refine ⟨⟨A, (mem_traceClassSubmodule).2 hAtc⟩, ?_⟩
  -- Tₘ → ⟨A, _⟩ in trace norm.
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hkey (ε / 2) (by positivity)
  refine ⟨N, fun m hm => ?_⟩
  rw [dist_eq_norm, norm_def, toOp_sub, toOp_mk, ← traceNorm_neg, neg_sub]
  exact lt_of_le_of_lt (hN m hm).2 (by linarith)

end TraceClass

end Spectra.QuantumMechanics.Channels
