import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionInvariantNormalizations

/-!
# Weighted differential expressions for the actual Weierstrass function

The expression family records the weights of X, Y, g₂ and g₃. Its formal
z-derivative is bound to ordinary derivatives of the actual Mathlib WP
and WP′. Scalar constants exist only in degree zero, and every expression
has an actual same-level modular-form realization in the Good product span.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open Complex Filter Set ModularForm
open scoped Topology Real UpperHalfPlane Modular MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.WeierstrassDifferentialExpressions

open ZInQ.Contrib.HeckePrimeRationality
open TorsionInvariantForms TorsionWeightThree

/-- Homogeneous expressions; a scalar constant has weight zero only. -/
inductive Expr : ℕ → Type
  | zero (k : ℕ) : Expr k
  | scalar (c : ℂ) : Expr 0
  | X : Expr 2
  | Y : Expr 3
  | G2 : Expr 4
  | G3 : Expr 6
  | add {k : ℕ} (e f : Expr k) : Expr k
  | smul {k : ℕ} (c : ℂ) (e : Expr k) : Expr k
  | mul {k l : ℕ} (e : Expr k) (f : Expr l) : Expr (k + l)
  | cast {k l : ℕ} (h : k = l) (e : Expr k) : Expr l

/-- Evaluate at the actual Mathlib Weierstrass objects, keeping the invariants constant in z. -/
def Expr.eval {k : ℕ} (e : Expr k) (L : _root_.PeriodPair) (z : ℂ) : ℂ :=
  match e with
  | .zero _ => 0
  | .scalar c => c
  | .X => L.weierstrassP z
  | .Y => L.derivWeierstrassP z
  | .G2 => L.g₂
  | .G3 => L.g₃
  | .add e f => e.eval L z + f.eval L z
  | .smul c e => c * e.eval L z
  | .mul e f => e.eval L z * f.eval L z
  | .cast _ e => e.eval L z

/-- Formal z-differentiation using DX=Y, DY=6X²−g₂/2 and invariant constants. -/
def Expr.differentiate {k : ℕ} (e : Expr k) : Expr (k + 1) :=
  match e with
  | .zero k => .zero (k + 1)
  | .scalar _ => .zero 1
  | .X => .Y
  | .Y => .add (.smul 6 (Expr.mul (k := 2) (l := 2) .X .X)) (.smul (-(1/2 : ℂ)) .G2)
  | .G2 => .zero 5
  | .G3 => .zero 7
  | .add e f => .add e.differentiate f.differentiate
  | .smul c e => .smul c e.differentiate
  | .mul e f => .add (.cast (by omega) (.mul e.differentiate f))
      (.cast (by omega) (.mul e f.differentiate))
  | .cast h e => .cast (by omega) e.differentiate

/-- Every formal derivative is the ordinary derivative of the actual analytic evaluation off the lattice. -/
theorem Expr.hasDerivAt_eval {k : ℕ} (e : Expr k) (L : _root_.PeriodPair) {z : ℂ}
    (hz : z ∉ L.lattice) : HasDerivAt (fun w : ℂ => e.eval L w) (e.differentiate.eval L z) z := by
  induction e with
  | zero k => exact hasDerivAt_const z 0
  | scalar c => exact hasDerivAt_const z c
  | X =>
    simpa only [Expr.eval, Expr.differentiate, ← L.deriv_weierstrassP] using!
      (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
  | Y =>
    have h := (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.hasDerivAt
    apply h.congr_deriv
    simp only [Expr.eval, Expr.differentiate]
    rw [TorsionInvariants.wp_second_eq L hz]
    ring
  | G2 => exact hasDerivAt_const z L.g₂
  | G3 => exact hasDerivAt_const z L.g₃
  | add e f he hf => exact he.add hf
  | smul c e he => exact he.const_mul c
  | mul e f he hf => exact he.mul hf
  | cast h e he => exact he

/-- The r-th actual WP derivative is represented by a weighted expression of degree r+2. -/
def wpJet : (r : ℕ) → Expr (r + 2)
  | 0 => .X
  | r + 1 => .cast (by omega) (wpJet r).differentiate

/-- The expression recurrence equals actual ordinary iterated derivatives everywhere off the lattice. -/
theorem wpJet_eval (L : _root_.PeriodPair) (r : ℕ) {z : ℂ} (hz : z ∉ L.lattice) :
    (wpJet r).eval L z = iteratedDeriv r L.weierstrassP z := by
  induction r generalizing z with
  | zero => rfl
  | succ r ih =>
    have hg : (fun w : ℂ => (wpJet r).eval L w) =ᶠ[𝓝 z] iteratedDeriv r L.weierstrassP := by
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
      exact ih hw
    have hd := (Expr.hasDerivAt_eval (wpJet r) L hz).deriv
    have hc := hg.deriv_eq
    simpa only [wpJet, Expr.eval, iteratedDeriv_succ] using hd.symm.trans hc

/-- Realize every weighted expression as a genuine modular form from actual x/y/g₂/g₃ bundles. -/
def Expr.toForm {k : ℕ} (e : Expr k) (N : ℕ) (h3 : 3 ≤ N) (a b : ℤ) : Weight N (k : ℤ) :=
  match e with
  | .zero _ => 0
  | .scalar c => c • AllLevelProducts.productForm N (by omega) 0 Fin.elim0 (by intro i; exact Fin.elim0 i)
  | .X => WeierstrassForms.xForm N (by omega) a b
  | .Y => TorsionWeightThree.yForm N (by omega) a b
  | .G2 => TorsionInvariantForms.g2Form N (by omega)
  | .G3 => TorsionInvariantForms.g3Form N (by omega)
  | .add e f => e.toForm N h3 a b + f.toForm N h3 a b
  | .smul c e => c • e.toForm N h3 a b
  | .mul e f => TorsionInvariantForms.productMul N _ _ (e.toForm N h3 a b) (f.toForm N h3 a b)
  | .cast h e => ModularForm.mcast (congrArg (fun n : ℕ => (n : ℤ)) h) (e.toForm N h3 a b)

/-- The actual expression values at a Good torsion point agree with the genuine form realization. -/
theorem Expr.toForm_apply {k : ℕ} (e : Expr k) (N : ℕ) (h3 : 3 ≤ N) (a b : ℤ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) (τ : ℍ) :
    e.toForm N h3 a b τ = e.eval (ThetaWeierstrass.periodPair τ) (CompletedTheta.torsionPoint N a b τ) := by
  induction e with
  | zero => rfl
  | scalar c =>
    simp only [Expr.toForm, Expr.eval, _root_.smul_apply, smul_eq_mul]
    rw [AllLevelProducts.productForm_apply (by omega)]
    simp
  | X => rw [Expr.toForm, WeierstrassForms.xForm_apply, TorsionWeierstrassData.xValue_of_good N a b τ hg]; rfl
  | Y => rw [Expr.toForm, TorsionWeightThree.yForm_apply, TorsionWeightThree.yValue_of_good N a b τ hg]; rfl
  | G2 => exact TorsionInvariantForms.g2Form_apply_actual N (by omega) τ
  | G3 => exact TorsionInvariantForms.g3Form_apply_actual N (by omega) τ
  | add e f he hf => simp only [Expr.toForm, Expr.eval, _root_.add_apply, he, hf]
  | smul c e he => simp only [Expr.toForm, Expr.eval, _root_.smul_apply, smul_eq_mul, he]
  | mul e f he hf => simp only [Expr.toForm, Expr.eval, TorsionInvariantForms.productMul_apply, he, hf]
  | cast h e he => simp only [Expr.toForm, Expr.eval, ModularForm.mcast_apply, he]

/-- Every actual expression form is in the same-level Good homogeneous product span. -/
theorem Expr.toForm_mem {k : ℕ} (e : Expr k) (N : ℕ) (h3 : 3 ≤ N) (a b : ℤ) :
    e.toForm N h3 a b ∈ TorsionInvariantForms.homogeneousProductSpan N (by omega) k := by
  induction e with
  | zero k => exact Submodule.zero_mem _
  | scalar c =>
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨Fin.elim0, (by intro i; exact Fin.elim0 i), rfl⟩
  | X => exact TorsionInvariantForms.xForm_mem_homogeneous N (by omega) h3 a b
  | Y => exact TorsionInvariantForms.yForm_mem_homogeneous N (by omega) h3 a b
  | G2 => exact TorsionInvariantForms.g2Form_mem_degreeFour N h3
  | G3 => exact TorsionInvariantForms.g3Form_mem_degreeSix N h3
  | add e f he hf => exact Submodule.add_mem _ he hf
  | smul c e he => exact Submodule.smul_mem _ c he
  | mul e f he hf => exact TorsionInvariantForms.productMul_mem N (by omega) _ _ _ _ he hf
  | cast h e he => subst h; exact he

end ZInQ.Contrib.HeckePrimeRationality.WeierstrassDifferentialExpressions
