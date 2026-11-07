import ZInQKernel.Syntax.Language.Build
import ZInQKernel.Syntax.Language.PointRef

/-!
# Quadratic-field pairs and point-code formulas

A pair `u = (u₀, u₁)` of polynomials stands for `u₀ + u₁ s ∈ K₀ = ℚ(s)`, `s² = 2`. A point code
is a five-tuple `p = (p₀, …, p₄)` with `x(p) = (p₁, p₂)` and `y(p) = (p₃, p₄)`. This file
transcribes the shared pair and point formulas of the specification (the methods of
`EllipticCore` in `construction/rational-elliptic-core.js`), with the fresh variables allocated
in the order of the specification, and proves that pair arithmetic represents `K₀ =
QuadraticAlgebra ℚ 2 0` faithfully (`Pair.val`).
-/

namespace ZInQ.Syntax

open MvPolynomial

/-- A pair `(u₀, u₁)` of polynomials, standing for `u₀ + u₁ s`. -/
abbrev Pair : Type := Poly × Poly

namespace Pair

/-- `u + u'`. -/
noncomputable def add (u v : Pair) : Pair := (u.1 + v.1, u.2 + v.2)

/-- `-u`. -/
noncomputable def neg (u : Pair) : Pair := (-u.1, -u.2)

/-- `u - u' = u + (-u')`. -/
noncomputable def sub (u v : Pair) : Pair := add u (neg v)

/-- `k u` for a polynomial (in particular an integer) `k`. -/
noncomputable def smul (k : Poly) (u : Pair) : Pair := (k * u.1, k * u.2)

/-- `u · u' = (u₀u₀' + 2u₁u₁', u₀u₁' + u₁u₀')`. -/
noncomputable def mul (u v : Pair) : Pair := (u.1 * v.1 + 2 * (u.2 * v.2), u.1 * v.2 + u.2 * v.1)

/-- `u² = u · u`. -/
noncomputable def sq (u : Pair) : Pair := mul u u

/-- The integer pair `(a, b)`. -/
noncomputable def ofInt (a b : ℤ) : Pair := (C a, C b)

/-- `1 = (1, 0)`. -/
noncomputable def one : Pair := ofInt 1 0

/-- `0 = (0, 0)`. -/
noncomputable def zero : Pair := ofInt 0 0

/-- The conjugate `ū = (u₀, -u₁)`. -/
noncomputable def conj (u : Pair) : Pair := (u.1, -u.2)

/-- The norm `N(u) = u₀² - 2u₁²`. -/
noncomputable def norm (u : Pair) : Poly := u.1 ^ 2 - 2 * u.2 ^ 2

/-- The repeated-squaring loop of the specification: with accumulator `r` and square `q`,
multiply `r` by `q` when the exponent is odd, halve the exponent, and square `q` if the
exponent is still positive. -/
noncomputable def powAux (n : ℕ) (r q : Pair) : Pair :=
  if h : n = 0 then r else
    let r' := if n % 2 = 1 then mul r q else r
    if n / 2 = 0 then r' else powAux (n / 2) r' (sq q)
termination_by n
decreasing_by omega

/-- `u^n` by repeated squaring. -/
noncomputable def pow (u : Pair) (n : ℕ) : Pair := powAux n one u

/-- The curve coefficient `A = (-11243, 7950) = -d²`, `d = 75 - 53 s`. -/
noncomputable def A : Pair := ofInt (-11243) 7950

/-- `δ = (11243, -7950) = d²`. -/
noncomputable def delta : Pair := ofInt 11243 (-7950)

end Pair

/-! ### Pair and point formulas -/

/-- `u ≐ u'`: `⋀(u₀ ≐ u₀', u₁ ≐ u₁')`. -/
noncomputable def feq (u v : Pair) : Formula := .and [.eq u.1 v.1, .eq u.2 v.2]

/-- `NZ_K(u) = NZ(N(u))` (one fresh variable). -/
noncomputable def Build.fnz (u : Pair) : Build Formula := Build.nz u.norm

/-- The formula of `Div(n, d)` with quotient pair `q` and inverse-norm variable `X_k`. -/
noncomputable def divFormula (n d q : Pair) (k : ℕ) : Formula :=
  .and [nzFormula d.norm k, feq (d.mul q) n]

/-- `Div(n, d)`: a fresh pair `q`, then `⋀(NZ_K(d), d · q ≐ n)`; its value is `q`. -/
noncomputable def Build.fdiv (n d : Pair) : Build (Pair × Formula) := do
  let q0 ← Build.fresh
  let q1 ← Build.fresh
  let f ← Build.fnz d
  pure ((q0, q1), .and [f, feq (d.mul (q0, q1)) n])

/-- A point code. -/
abbrev Code : Type := Fin 5 → Poly

/-- The code `O = (1, 0, 0, 0, 0)`. -/
noncomputable def Code.O : Code := ![1, 0, 0, 0, 0]

/-- `neg(p) = (p₀, p₁, p₂, -p₃, -p₄)`. -/
noncomputable def Code.neg (p : Code) : Code := ![p 0, p 1, p 2, -p 3, -p 4]

/-- `x(p) = (p₁, p₂)`. -/
def Code.x (p : Code) : Pair := (p 1, p 2)

/-- `y(p) = (p₃, p₄)`. -/
def Code.y (p : Code) : Pair := (p 3, p 4)

/-- `eq(p, p') = ⋀_{i=0}^4 (p_i ≐ p_i')`. -/
noncomputable def peq (p p' : Code) : Formula := .and (List.ofFn fun i => .eq (p i) (p' i))

/-- `isO(p) = eq(p, O)`. -/
noncomputable def isO (p : Code) : Formula := peq p Code.O

/-- `fin(p)`: the atom `p₀ ≐ 0`. -/
noncomputable def fin (p : Code) : Formula := .eq (p 0) 0

/-- The curve atom pair `Y² ≐ X² · X + A · X`. -/
noncomputable def curve (X Y : Pair) : Formula :=
  feq Y.sq ((X.sq.mul X).add (Pair.A.mul X))

/-- A fresh point: five fresh variables. -/
noncomputable def Build.freshPoint : Build Code := do
  let a ← Build.fresh
  let b ← Build.fresh
  let c ← Build.fresh
  let d ← Build.fresh
  let e ← Build.fresh
  pure ![a, b, c, d, e]

/-- The generator point `G = (0, c₁, -145, c₂, c₃)` of a template, with the rational constants
`1641/8`, `-15465/4`, `87483/32` requested in this order. -/
noncomputable def Build.gen : Build Code := do
  let c1 ← Build.rational 1641 8
  let c2 ← Build.rational (-15465) 4
  let c3 ← Build.rational 87483 32
  pure ![0, c1, -145, c2, c3]

/-- The formula of `Z(p, ζ)` with inverse-norm variable `X_k`. -/
noncomputable def zFormula (p : Code) (ζ : Pair) (k : ℕ) : Formula :=
  .or [.and [isO p, feq ζ Pair.zero], .and [fin p, nzFormula p.y.norm k, feq (p.y.mul ζ) p.x.neg]]

/-- `Z(p, ζ)` (one fresh variable): `ζ = z(p) = -x/y`, with `z(O) = 0`. -/
noncomputable def Build.zGadget (p : Code) (ζ : Pair) : Build Formula := do
  let f ← Build.fnz p.y
  pure (.or [.and [isO p, feq ζ Pair.zero], .and [fin p, f, feq (p.y.mul ζ) p.x.neg]])

/-- `IX(p, v)`: `v = 1/x`, with value `0` at the identity. -/
noncomputable def ixFormula (p : Code) (v : Pair) : Formula :=
  .or [.and [isO p, feq v Pair.zero], .and [fin p, feq (p.x.mul v) Pair.one]]

@[simp] theorem Build.fnz_apply (u : Pair) (s : BuildState) :
    Build.fnz u s = (nzFormula u.norm s.next, { s with next := s.next + 1 }) := rfl

@[simp] theorem Build.fdiv_apply (n d : Pair) (s : BuildState) :
    Build.fdiv n d s = (((X s.next, X (s.next + 1)),
      divFormula n d (X s.next, X (s.next + 1)) (s.next + 2)), { s with next := s.next + 3 }) :=
  rfl

@[simp] theorem Build.zGadget_apply (p : Code) (ζ : Pair) (s : BuildState) :
    Build.zGadget p ζ s = (zFormula p ζ s.next, { s with next := s.next + 1 }) := rfl

@[simp] theorem Build.freshPoint_apply (s : BuildState) :
    Build.freshPoint s =
      ((fun i => X (s.next + (i : ℕ)) : Code), { s with next := s.next + 5 }) := by
  simp only [Build.freshPoint, Build.bind_apply, Build.fresh_apply, Build.pure_apply,
    Prod.mk.injEq, and_true]
  funext i
  fin_cases i <;> simp [add_assoc]

/-! ### Pair arithmetic represents the quadratic field -/

namespace Pair

/-- The element `[u] = u₀(x) + u₁(x) s` of `K₀`. -/
noncomputable def val (x : ℕ → ℚ) (u : Pair) : K0 := ⟨ev x u.1, ev x u.2⟩

variable (x : ℕ → ℚ)

@[simp] theorem re_val (u : Pair) : (val x u).re = ev x u.1 := rfl

@[simp] theorem im_val (u : Pair) : (val x u).im = ev x u.2 := rfl

theorem val_add (u v : Pair) : val x (add u v) = val x u + val x v := by
  ext <;> simp [add]

theorem val_neg (u : Pair) : val x (neg u) = -val x u := by
  ext <;> simp [neg]

theorem val_sub (u v : Pair) : val x (sub u v) = val x u - val x v := by
  ext <;> simp [sub, add, neg, sub_eq_add_neg]

theorem val_smul (k : Poly) (u : Pair) :
    val x (smul k u) = QuadraticAlgebra.C (ev x k) * val x u := by
  ext <;> simp [smul]

theorem val_mul (u v : Pair) : val x (mul u v) = val x u * val x v := by
  ext <;> simp [mul]
  ring

theorem val_sq (u : Pair) : val x (sq u) = val x u ^ 2 := by
  rw [sq, val_mul, pow_two]

@[simp] theorem val_ofInt (a b : ℤ) : val x (ofInt a b) = ⟨a, b⟩ := by
  ext <;> simp [ofInt]

theorem val_one : val x one = 1 := by
  ext <;> simp [one, ofInt] <;> rfl

theorem val_zero : val x zero = 0 := by
  ext <;> simp [zero, ofInt]

/-- The conjugate represents `σ : s ↦ -s` (`star` on `QuadraticAlgebra ℚ 2 0`). -/
theorem val_conj (u : Pair) : val x (conj u) = star (val x u) := by
  ext <;> simp [conj, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]

/-- `N(u) = [u] σ[u]`. -/
theorem C_ev_norm (u : Pair) :
    QuadraticAlgebra.C (ev x (norm u)) = val x u * star (val x u) := by
  ext
  · simp only [QuadraticAlgebra.re_C, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_star,
      QuadraticAlgebra.im_star, re_val, im_val, norm, map_sub, map_mul, map_pow, ev_ofNat]
    ring
  · simp only [QuadraticAlgebra.im_C, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star,
      QuadraticAlgebra.im_star, re_val, im_val]
    ring

theorem ev_norm (u : Pair) : ev x (norm u) = (ev x u.1) ^ 2 - 2 * (ev x u.2) ^ 2 := by
  simp [norm]

theorem val_powAux (n : ℕ) (r q : Pair) : val x (powAux n r q) = val x r * val x q ^ n := by
  induction n using Nat.strong_induction_on generalizing r q with
  | _ n ih =>
    rw [powAux]
    split_ifs with h0 h1 h2 h2
    · subst h0; simp
    · rw [val_mul]
      have : n = 1 := by omega
      subst this; simp
    · rw [ih (n / 2) (by omega), val_mul, val_sq, ← pow_mul, mul_assoc, ← pow_succ']
      congr 2
      omega
    · have : n = 0 := by omega
      exact absurd this h0
    · rw [ih (n / 2) (by omega), val_sq, ← pow_mul]
      congr 2
      omega

theorem val_pow (u : Pair) (n : ℕ) : val x (pow u n) = val x u ^ n := by
  rw [pow, val_powAux, val_one, one_mul]

theorem val_A : val x A = -genD ^ 2 := by
  ext <;> simp [A, genD, pow_two] <;> norm_num

theorem val_delta : val x delta = genD ^ 2 := by
  ext <;> simp [delta, genD, pow_two] <;> norm_num

end Pair

/-- **Pair equality.** `u ≐ u'` holds exactly when `[u] = [u']`. -/
theorem holds_feq (x : ℕ → ℚ) (u v : Pair) : (feq u v).Holds x ↔ Pair.val x u = Pair.val x v := by
  simp [feq, QuadraticAlgebra.ext_iff]

theorem lift_feq (y : ℕ → ℚ) (u v : Pair) : (feq u v).Lift y ↔ Pair.val y u = Pair.val y v := by
  simp [feq, QuadraticAlgebra.ext_iff]

/-- The pair norm vanishes only at `0`. -/
theorem ev_norm_ne_zero_iff (x : ℕ → ℚ) (u : Pair) : ev x u.norm ≠ 0 ↔ Pair.val x u ≠ 0 := by
  rw [Pair.ev_norm, ← K0_ne_zero_iff_pairNorm]
  rfl

theorem VarsIn.norm {u : Pair} {P : ℕ → Prop} (h1 : VarsIn u.1 P) (h2 : VarsIn u.2 P) :
    VarsIn u.norm P :=
  (h1.pow 2).sub ((VarsIn.ofNat 2 P).mul (h2.pow 2))

theorem VarsIn.pairMul {u v : Pair} {P : ℕ → Prop} (hu1 : VarsIn u.1 P) (hu2 : VarsIn u.2 P)
    (hv1 : VarsIn v.1 P) (hv2 : VarsIn v.2 P) :
    VarsIn (u.mul v).1 P ∧ VarsIn (u.mul v).2 P :=
  ⟨(hu1.mul hv1).add ((VarsIn.ofNat 2 P).mul (hu2.mul hv2)), (hu1.mul hv2).add (hu2.mul hv1)⟩

theorem ev_update_of_varsIn {f : Poly} {k : ℕ} (h : VarsIn f (· ≠ k)) (x : ℕ → ℚ) (t : ℚ) :
    ev (Function.update x k t) f = ev x f :=
  ev_congr fun i hi => Function.update_of_ne (h i hi) _ _

theorem val_update_of_varsIn {u : Pair} {k : ℕ} (h1 : VarsIn u.1 (· ≠ k))
    (h2 : VarsIn u.2 (· ≠ k)) (x : ℕ → ℚ) (t : ℚ) :
    Pair.val (Function.update x k t) u = Pair.val x u := by
  ext
  · exact ev_update_of_varsIn h1 x t
  · exact ev_update_of_varsIn h2 x t

/-- **Nonzero pairs.** `NZ_K(u)` is satisfiable by its fresh variable exactly when `[u] ≠ 0`. -/
theorem exists_update_fnz_iff (x : ℕ → ℚ) {u : Pair} {k : ℕ} (h1 : VarsIn u.1 (· ≠ k))
    (h2 : VarsIn u.2 (· ≠ k)) :
    (∃ t : ℚ, (nzFormula u.norm k).Holds (Function.update x k t)) ↔ Pair.val x u ≠ 0 := by
  rw [exists_update_nzFormula_iff x u.norm fun h => VarsIn.norm h1 h2 k h rfl,
    ev_norm_ne_zero_iff]

/-- **Division.** `Div(n, d)` holds for some value of its inverse-norm variable, with value
`q`, exactly when `[d] ≠ 0` and `[q] = [n]/[d]`. -/
theorem exists_update_divFormula_iff (x : ℕ → ℚ) {n d q : Pair} {k : ℕ}
    (hn1 : VarsIn n.1 (· ≠ k)) (hn2 : VarsIn n.2 (· ≠ k)) (hd1 : VarsIn d.1 (· ≠ k))
    (hd2 : VarsIn d.2 (· ≠ k)) (hq1 : VarsIn q.1 (· ≠ k)) (hq2 : VarsIn q.2 (· ≠ k)) :
    (∃ t : ℚ, (divFormula n d q k).Holds (Function.update x k t)) ↔
      Pair.val x d ≠ 0 ∧ Pair.val x q = Pair.val x n / Pair.val x d := by
  have hm := VarsIn.pairMul hd1 hd2 hq1 hq2
  simp only [divFormula, Formula.holds_and, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, holds_feq, val_update_of_varsIn hm.1 hm.2,
    val_update_of_varsIn hn1 hn2]
  rw [exists_and_right, exists_update_fnz_iff x hd1 hd2, Pair.val_mul]
  refine and_congr_right fun hd => ?_
  rw [eq_div_iff hd, mul_comm]

/-- The values of a code. -/
theorem holds_peq (x : ℕ → ℚ) (p p' : Code) :
    (peq p p').Holds x ↔ evCode x p = evCode x p' := by
  simp only [peq, Formula.holds_and, List.forall_mem_ofFn_iff, Formula.holds_eq]
  exact ⟨fun h => funext h, fun h i => congrFun h i⟩

theorem evCode_O (x : ℕ → ℚ) : evCode x Code.O = ![1, 0, 0, 0, 0] := by
  funext i
  fin_cases i <;> simp [evCode, Code.O]

theorem holds_isO (x : ℕ → ℚ) (p : Code) : (isO p).Holds x ↔ evCode x p = ![1, 0, 0, 0, 0] := by
  rw [isO, holds_peq, evCode_O]

theorem holds_fin (x : ℕ → ℚ) (p : Code) : (fin p).Holds x ↔ ev x (p 0) = 0 := by
  simp [fin]

theorem lift_fin (y : ℕ → ℚ) (p : Code) : (fin p).Lift y ↔ ev y (p 0) = 0 := by
  simp [fin]

/-- The curve atom pair says `[Y]² = [X]³ - d² [X]`. -/
theorem holds_curve (x : ℕ → ℚ) (X Y : Pair) :
    (curve X Y).Holds x ↔ Pair.val x Y ^ 2 = Pair.val x X ^ 3 + -genD ^ 2 * Pair.val x X := by
  rw [curve, holds_feq, Pair.val_sq, Pair.val_add, Pair.val_mul, Pair.val_mul, Pair.val_sq,
    Pair.val_A, pow_succ _ 2]

theorem VarsIn.code {p : Code} {P : ℕ → Prop} (h : ∀ i, VarsIn (p i) P) :
    VarsIn p.x.1 P ∧ VarsIn p.x.2 P ∧ VarsIn p.y.1 P ∧ VarsIn p.y.2 P :=
  ⟨h 1, h 2, h 3, h 4⟩

theorem holds_update_isO (x : ℕ → ℚ) {p : Code} {k : ℕ} (hp : ∀ i, VarsIn (p i) (· ≠ k))
    (t : ℚ) : (isO p).Holds (Function.update x k t) ↔ (isO p).Holds x := by
  rw [holds_isO, holds_isO]
  have : evCode (Function.update x k t) p = evCode x p :=
    funext fun i => ev_update_of_varsIn (hp i) x t
  rw [this]

theorem holds_zFormula (x : ℕ → ℚ) (p : Code) (ζ : Pair) (k : ℕ) :
    (zFormula p ζ k).Holds x ↔
      ((isO p).Holds x ∧ Pair.val x ζ = 0) ∨
        (ev x (p 0) = 0 ∧ (nzFormula p.y.norm k).Holds x ∧
          Pair.val x p.y * Pair.val x ζ = -Pair.val x p.x) := by
  simp only [zFormula, Formula.holds_or, Formula.holds_and, List.mem_cons, List.not_mem_nil,
    or_false, exists_eq_or_imp, exists_eq_left, forall_eq_or_imp, forall_eq, holds_feq,
    holds_fin, Pair.val_zero, Pair.val_mul, Pair.val_neg]

/-- **The local parameter.** `Z(p, ζ)` holds for some value of its fresh variable exactly when
either `p = O` and `[ζ] = 0`, or `p₀ = 0`, `[y(p)] ≠ 0` and `[ζ] = -[x(p)]/[y(p)]`. -/
theorem exists_update_zFormula_iff (x : ℕ → ℚ) {p : Code} {ζ : Pair} {k : ℕ}
    (hp : ∀ i, VarsIn (p i) (· ≠ k)) (hζ1 : VarsIn ζ.1 (· ≠ k)) (hζ2 : VarsIn ζ.2 (· ≠ k)) :
    (∃ t : ℚ, (zFormula p ζ k).Holds (Function.update x k t)) ↔
      (evCode x p = ![1, 0, 0, 0, 0] ∧ Pair.val x ζ = 0) ∨
        (ev x (p 0) = 0 ∧ Pair.val x p.y ≠ 0 ∧
          Pair.val x ζ = -Pair.val x p.x / Pair.val x p.y) := by
  obtain ⟨hx1, hx2, hy1, hy2⟩ := VarsIn.code hp
  simp only [holds_zFormula, holds_update_isO x hp, val_update_of_varsIn hζ1 hζ2,
    val_update_of_varsIn hy1 hy2, val_update_of_varsIn hx1 hx2, ev_update_of_varsIn (hp 0)]
  rw [exists_or, exists_const, exists_and_left, exists_and_right,
    exists_update_fnz_iff x hy1 hy2, holds_isO]
  refine or_congr Iff.rfl (and_congr_right fun _ => and_congr_right fun hy => ?_)
  rw [eq_div_iff hy, mul_comm]

/-- **The inverse abscissa.** `IX(p, v)` holds exactly when either `p = O` and `[v] = 0`, or
`p₀ = 0` and `[x(p)] [v] = 1`. -/
theorem holds_ixFormula (x : ℕ → ℚ) (p : Code) (v : Pair) :
    (ixFormula p v).Holds x ↔
      (evCode x p = ![1, 0, 0, 0, 0] ∧ Pair.val x v = 0) ∨
        (ev x (p 0) = 0 ∧ Pair.val x p.x * Pair.val x v = 1) := by
  simp only [ixFormula, Formula.holds_or, Formula.holds_and, List.mem_cons, List.not_mem_nil,
    or_false, exists_eq_or_imp, exists_eq_left, forall_eq_or_imp, forall_eq, holds_feq,
    holds_isO, holds_fin, Pair.val_zero, Pair.val_mul, Pair.val_one]

/-- The two branches of `Z` and `IX` are exclusive: `p₀ = 1` in the first, `p₀ = 0` in the
second. -/
theorem not_isO_and_fin (x : ℕ → ℚ) (p : Code) :
    ¬ (evCode x p = ![1, 0, 0, 0, 0] ∧ ev x (p 0) = 0) := by
  rintro ⟨h, h0⟩
  have := congrFun h 0
  simp [evCode, h0] at this

end ZInQ.Syntax
