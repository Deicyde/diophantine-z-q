import Mathlib
import ZInQKernel.Hypotheses.Height

/-!
# hdec-elementary: the leaves of Theorem 4.1 (draft, scratch only)

Companion of `docs/research/hdec-elementary.md`. Numbering (L1-L12, F-a ... F-e, G1-G23) is the
note's. Compile with `lake env lean scratch/hdec-elementary/Leaves.lean`.

The file has three layers.

1. **Concrete definitions (cheap, genuine).** The Igusa–Clebsch invariants of a binary sextic from
   its roots (Mestre's `A', B', C', D'`), the QM-locus point `[96(j+1) : 576j : 4608j(5j+4) :
   4096j³]`, the Thomae point (fourth powers of the ten even theta constants, up to a common
   factor and signs, by Thomae's formula), and the absolute logarithmic Weil height of a point of
   `Pⁿ` over a number field. Two pieces of glue are proved here (F1 as algebra); one leaf is
   stated with these genuine definitions only (`Igusa1960`, used by the alternative route for
   A7).
2. **A placeholder signature `Objects`** for what Mathlib lacks: abelian varieties over number
   fields, isogenies with degrees, products, the Jacobian of a sextic, `J₁(N)`, and the stable
   Faltings height. The leaves L8-L12 (Arakelov half) are stated over it. **Over an arbitrary
   model of `Objects` these Props are not faithful**: as wk-h §4.3 shows for its signature, a
   fake model turns them, together with `ModularityOutput`, into a `j`-height bound. They
   become faithful leaves only when every field of `Objects` is replaced by a genuine definition
   (note §5). The pins to concrete data (`jac a r` is the Jacobian of the explicit sextic whose
   Thomae point and Igusa–Clebsch invariants are the concrete ones) limit, but do not remove,
   this freedom.
3. **The top-level glue** `sixContactMinAt_of_leaves`: the Arakelov leaves L8-L12 and the output
   of the modularity half (`ModularityOutput`, which the note derives from L1-L7 and the glue
   G1-G17) imply `SixContactMinAt S`. The step to `JHeightBoundAt S` is `sorry` (glue G18-G23:
   E's and F's arithmetic; wk-h's `transfer_numerics` already proves E's part); the last step is
   the repository's proved `JHeight.sixContactMin_of_jHeightBound`, re-proved here for an arbitrary
   `S` from a verbatim copy of `JHeight.lean`'s F4 section (this file cannot import it).

Imports. `ZInQKernel/Hypotheses/JHeight.lean` imports `HeightMin.lean`, which needs the upstream
package `lean/` (not built in this worktree), so this file imports only
`ZInQKernel.Hypotheses.Height` (Mathlib-only), as wk-h's drafts do. `Jmap`, F4 and
`JHeightBoundAt` below are verbatim copies from `JHeight.lean`, and `SixContactMinAt S`
is the body of `SixContactMin` with `Mult.S_mul` abstracted to `S`; at `S = Mult.S_mul` all three
agree with the repository's definitions by `rfl`.

L1-L7 (Shimura curve, Shimura reciprocity, Grothendieck monodromy, Faltings 1983,
Khare–Wintenberger + Ribet, Carayol) need Tate modules, Galois representations of local and
global fields, abelian varieties over `ℚ` with endomorphism algebras, Weil restriction, `J₁(N)`
over `ℚ`, conductors and the moduli of QM surfaces; they are stated in the note (§3) and not
here.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace HDec

/-! ## 1. Concrete definitions -/

section Concrete

variable {k : Type*} [Field k]

/-- `(rᵢ - rⱼ)²`. -/
def dsq (r : Fin 6 → k) (i j : Fin 6) : k := (r i - r j) ^ 2

/-- Igusa–Clebsch `I₂` (Mestre's `A'`) of the sextic `a ∏ (X - rᵢ)`:
`a² Σ (12)²(34)²(56)²` over the 15 pairings, written as a sum over `S₆` divided by 48. -/
def IC2 (a : k) (r : Fin 6 → k) : k :=
  a ^ 2 * (∑ σ : Equiv.Perm (Fin 6),
    dsq r (σ 0) (σ 1) * dsq r (σ 2) (σ 3) * dsq r (σ 4) (σ 5)) / 48

/-- Igusa–Clebsch `I₄` (Mestre's `B'`): `a⁴ Σ (12)²(23)²(31)²(45)²(56)²(64)²` over the 10
splittings into two triples (sum over `S₆` divided by 72). -/
def IC4 (a : k) (r : Fin 6 → k) : k :=
  a ^ 4 * (∑ σ : Equiv.Perm (Fin 6),
    dsq r (σ 0) (σ 1) * dsq r (σ 1) (σ 2) * dsq r (σ 2) (σ 0) *
    dsq r (σ 3) (σ 4) * dsq r (σ 4) (σ 5) * dsq r (σ 5) (σ 3)) / 72

/-- Igusa–Clebsch `I₆` (Mestre's `C'`): `a⁶ Σ (12)²(23)²(31)²(45)²(56)²(64)²(14)²(25)²(36)²`
over 60 terms (sum over `S₆` divided by 12). -/
def IC6 (a : k) (r : Fin 6 → k) : k :=
  a ^ 6 * (∑ σ : Equiv.Perm (Fin 6),
    dsq r (σ 0) (σ 1) * dsq r (σ 1) (σ 2) * dsq r (σ 2) (σ 0) *
    dsq r (σ 3) (σ 4) * dsq r (σ 4) (σ 5) * dsq r (σ 5) (σ 3) *
    dsq r (σ 0) (σ 3) * dsq r (σ 1) (σ 4) * dsq r (σ 2) (σ 5)) / 12

/-- Igusa–Clebsch `I₁₀` (Mestre's `D'`): the discriminant `a¹⁰ ∏_{i<j} (rᵢ - rⱼ)²`. -/
def IC10 (a : k) (r : Fin 6 → k) : k :=
  a ^ 10 * ∏ i : Fin 6, ∏ j : Fin 6, if i < j then dsq r i j else 1

/-- The sextic `a ∏ (X - rᵢ)` defines a genus-2 curve `y² = a ∏ (X - rᵢ)`: `a ≠ 0` and distinct
roots. -/
def IsGenus2 (a : k) (r : Fin 6 → k) : Prop := a ≠ 0 ∧ Function.Injective r

/-- **The QM locus in Igusa–Clebsch coordinates.** The weighted-projective point
`[I₂ : I₄ : I₆ : I₁₀]` of `a ∏ (X - rᵢ)` is
`[96(j+1) : 576j : 4608j(5j+4) : 4096j³]`, the image of Lin–Yang's Igusa vector
`[J₂ : J₄ : J₆ : J₁₀] = [12(j+1) : 6(j²+j+1) : 4(j³-2j²+1) : j³]` under `I₂ = 8J₂`,
`I₄ = 4J₂² - 96J₄`, `I₆ = 8J₂³ - 160J₂J₄ - 576J₆`, `I₁₀ = 4096J₁₀`
(`scratch/hdec-elementary/igusa_thomae_check.py`). -/
def OnQMLocus (a : k) (r : Fin 6 → k) (j : k) : Prop :=
  ∃ c : k, c ≠ 0 ∧ IC2 a r = c ^ 2 * (96 * (j + 1)) ∧ IC4 a r = c ^ 4 * (576 * j) ∧
    IC6 a r = c ^ 6 * (4608 * j * (5 * j + 4)) ∧ IC10 a r = c ^ 10 * (4096 * j ^ 3)

/-- **Glue G21 (F1 as algebra).** On the QM locus, the Hauptmodul is the weight-zero Igusa
invariant `j = 3779136 · I₁₀² / I₄⁵` (N5's theta formula, after Thomae). -/
theorem j_eq_of_onQMLocus [CharZero k] {a : k} {r : Fin 6 → k} {j : k} (hj : j ≠ 0)
    (h : OnQMLocus a r j) : j = 3779136 * IC10 a r ^ 2 / IC4 a r ^ 5 := by
  obtain ⟨c, hc, -, h4, -, h10⟩ := h
  rw [h4, h10]
  field_simp
  ring

/-- The ten splittings `{0, a, b} | complement` of `{0, …, 5}` into two triples. -/
def thomaeTriple : Fin 10 → Finset (Fin 6) :=
  ![{0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 1, 5}, {0, 2, 3}, {0, 2, 4}, {0, 2, 5}, {0, 3, 4},
    {0, 3, 5}, {0, 4, 5}]

/-- **The Thomae point** `T_S = Δ(S) Δ(Sᶜ)`, `Δ(S) = ∏_{i<j ∈ S} (rᵢ - rⱼ)`. By Thomae's formula
the fourth powers of the ten even theta constants of `Jac(y² = a ∏ (X - rᵢ))` are
`κ · ε_S · T_S` with one common factor `κ` and signs `ε_S`, so `[T_S]` and `[θ_S⁴]` have the same
Weil height. `Σ T_S² = I₄/a⁴` and `∏ T_S² = (I₁₀/a¹⁰)⁴` (script, 30 random root sets). -/
def thomae (r : Fin 6 → k) (s : Fin 10) : k :=
  ∏ i : Fin 6, ∏ j : Fin 6,
    if i < j ∧ (i ∈ thomaeTriple s ↔ j ∈ thomaeTriple s) then r i - r j else 1

/-- The action of `M = (α β; γ δ)` and `e` on a sextic, `e² (γX + δ)⁶ f((αX + β)/(γX + δ))`,
written on coefficients. -/
def actSextic (M : Matrix (Fin 2) (Fin 2) k) (e : k) (f : Polynomial k) : Polynomial k :=
  Polynomial.C (e ^ 2) * ∑ i ∈ range 7, Polynomial.C (f.coeff i) *
    (Polynomial.C (M 0 0) * Polynomial.X + Polynomial.C (M 0 1)) ^ i *
    (Polynomial.C (M 1 0) * Polynomial.X + Polynomial.C (M 1 1)) ^ (6 - i)

/-- The split sextic `a ∏ (X - rᵢ)`. -/
def sextic (a : k) (r : Fin 6 → k) : Polynomial k :=
  Polynomial.C a * ∏ i : Fin 6, (Polynomial.X - Polynomial.C (r i))

end Concrete

/-- **Foundation leaf (Igusa 1960; Mestre 1991 §1), statable now.** Over an algebraically closed
field of characteristic zero, two genus-2 sextics with all six roots finite are isomorphic as
curves (by `(x, y) ↦ ((αx+β)/(γx+δ), e y/(γx+δ)³)`) exactly when their Igusa–Clebsch invariants
agree in weighted projective space. Used only by the alternative proof of A7 (note §4, G5). -/
def Igusa1960 : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (a a' : k) (r r' : Fin 6 → k),
    IsGenus2 a r → IsGenus2 a' r' →
    ((∃ M : Matrix (Fin 2) (Fin 2) k, M.det ≠ 0 ∧ ∃ e : k, e ≠ 0 ∧
        actSextic M e (sextic a r) = sextic a' r') ↔
      ∃ c : k, c ≠ 0 ∧ IC2 a' r' = c ^ 2 * IC2 a r ∧ IC4 a' r' = c ^ 4 * IC4 a r ∧
        IC6 a' r' = c ^ 6 * IC6 a r ∧ IC10 a' r' = c ^ 10 * IC10 a r)

/-- The absolute logarithmic Weil height of `x : ι → L` as a point of `P(ι)`, `L` a number field:
Mathlib's relative `Height.logHeight` divided by `[L : ℚ]`. -/
def absLogHeight {L : Type*} [Field L] [NumberField L] {ι : Type*} [Finite ι] (x : ι → L) : ℝ :=
  Height.logHeight x / (Module.finrank ℚ L : ℝ)

/-! ## 2. Placeholder signature and the Arakelov leaves L8-L12 -/

/-- A bundled number field. -/
structure NF where
  carrier : Type
  [fld : Field carrier]
  [nf : NumberField carrier]

attribute [instance] NF.fld NF.nf

instance : CoeSort NF Type := ⟨NF.carrier⟩

/-- **PLACEHOLDER** for the definitions Mathlib lacks (note §5: D5 abelian varieties over number
fields, D6 isogenies, D7 Jacobians of genus-2 curves, D9 `J₁(N)`, D12 the stable Faltings height
in Faltings' original normalization). Not a definition of anything: every field must be replaced
by the genuine object before the leaves below are faithful. -/
structure Objects where
  /-- abelian varieties over the number field `K` -/
  AV : NF → Type
  /-- dimension -/
  dim : {K : NF} → AV K → ℕ
  /-- product -/
  prod : {K : NF} → AV K → AV K → AV K
  /-- the `K`-isogenies `A → B` -/
  Isog : {K : NF} → AV K → AV K → Type
  /-- the degree of an isogeny -/
  deg : {K : NF} → {A B : AV K} → Isog A B → ℕ
  /-- the stable Faltings height, original normalization -/
  hF : {K : NF} → AV K → ℝ
  /-- the Jacobian of `y² = a ∏ (X - rᵢ)` over `K`, with its canonical principal polarization -/
  jac : {K : NF} → K → (Fin 6 → K) → AV K
  /-- `J₁(N)` base-changed from `ℚ` to `K` -/
  J1 : (K : NF) → ℕ → AV K

variable (O : Objects)

/-- **L8 (Javanpeykar 2014, Thm 1.1.1, at `X₁(N)`, with `g, deg_B ≤ [SL₂(ℤ) : Γ₁(N)] ≤ N²`).** -/
def Javanpeykar : Prop :=
  ∀ (K : NF) (N : ℕ), 1 ≤ N →
    O.hF (O.J1 K N) ≤ 13000000 * (N : ℝ) ^ 12 ∧ O.dim (O.J1 K N) ≤ N ^ 2

/-- **L9 (Gaudron–Rémond 2014, Duke, Thm 1.4)**, in N5's logarithmic form: if `A` and `B` are
`K`-isogenous, there is an isogeny `A → B` with `log deg φ ≤ 1024g³(64g² log 14g + log d +
2 log max(h_F(A), log d, 1))`, `g = dim A`, `d = [K : ℚ]`. -/
def GaudronRemond : Prop :=
  ∀ (K : NF) (A B : O.AV K), Nonempty (O.Isog A B) →
    ∃ φ : O.Isog A B,
      Real.log (O.deg φ) ≤ 1024 * (O.dim A : ℝ) ^ 3 *
        (64 * (O.dim A : ℝ) ^ 2 * Real.log (14 * O.dim A) + Real.log (Module.finrank ℚ K) +
          2 * Real.log (max (O.hF A) (max (Real.log (Module.finrank ℚ K)) 1)))

/-- **L10 (Faltings 1983, Lemma 5 and §2; Raynaud 1985, Exp. VII):** height variation under
isogeny, additivity, and dimension of products. -/
def FaltingsHeightVariation : Prop :=
  (∀ (K : NF) (A B : O.AV K) (φ : O.Isog A B), 0 < O.deg φ ∧
      |O.hF A - O.hF B| ≤ Real.log (O.deg φ) / 2) ∧
    (∀ (K : NF) (A B : O.AV K), O.hF (O.prod A B) = O.hF A + O.hF B ∧
      O.dim (O.prod A B) = O.dim A + O.dim B)

/-- **L11 (Bost's lower bound, as recorded in Gaudron–Rémond 2014 §9 / CMH 2014 §2.3).** -/
def BostLower : Prop :=
  ∀ (K : NF) (A : O.AV K), -(3 / 2 : ℝ) * O.dim A ≤ O.hF A

/-- **L12 (Pazuki 2012, Cor. 1.3(2), `g = 2`, `r = 2`, Deligne metric; with Thomae's formula).**
For a genus-2 curve `y² = a ∏ (X - rᵢ)` over `K`, the Thomae point has absolute log height at
most `4(½X_D + C₂ log(X_D + 2))`, `X_D = max(1, h_F(Jac) + log π)`, `C₂ = 1000·2⁴(log 2⁴)⁵`.
(Pazuki's Euclidean height dominates the sup-norm Weil height; `h([θ⁴]) = 4h([θ])`.) -/
def PazukiThomae : Prop :=
  ∀ (K : NF) (a : K) (r : Fin 6 → K), IsGenus2 a r →
    let XD := max 1 (O.hF (O.jac a r) + Real.log Real.pi)
    absLogHeight (thomae r) ≤
      4 * (XD / 2 + 1000 * 2 ^ 4 * Real.log (2 ^ 4) ^ 5 * Real.log (XD + 2))

/-- The Arakelov leaves L8-L12. -/
def ArakelovLeaves : Prop :=
  Javanpeykar O ∧ GaudronRemond O ∧ FaltingsHeightVariation O ∧ BostLower O ∧ PazukiThomae O

/-! ## 3. The output of the modularity half, and the top-level glue -/

open ZInQ

/-! ### Verbatim copy of `ZInQKernel/Hypotheses/JHeight.lean` lines 31-232 (proved there; F4)

Copied so that the last step `JHeightBoundAt S → SixContactMinAt S` is proved here too. -/

theorem contactSupport_pos (S : Finset ℕ) (u : ℚ) : 0 < contactSupport S u := by
  unfold contactSupport
  exact Finset.prod_pos fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

def Fh (a b : ℤ) : ℤ := a * (a + 15 * b) * (a + 20 * b) * (a + 24 * b) * (a + 30 * b) * (a + 60 * b)

/-- The binary quadratic `G_h(a,b) = 7a² + 300ab + 3600b²` (discriminant `−10800 < 0`). -/
def Gh (a b : ℤ) : ℤ := 7 * a ^ 2 + 300 * a * b + 3600 * b ^ 2

/-- The Hauptmodul value `J(u) = −57600 F(u)² / G(u)⁶` (h-b1 M7). -/
def Jmap (u : ℚ) : ℚ :=
  -57600 * (u * (u + 15) * (u + 20) * (u + 24) * (u + 30) * (u + 60)) ^ 2 /
    (7 * u ^ 2 + 300 * u + 3600) ^ 6

/-- Nullstellensatz certificate for `x⁷` (`scratch/wk-h/f4_cert.py`). -/
theorem cert_x (a b : ℤ) :
    3 * a ^ 7 = (-200 * a - 4800 * b) * Fh a b +
      (29 * a ^ 5 + 3700 * a ^ 4 * b + 164400 * a ^ 3 * b ^ 2 + 2880000 * a ^ 2 * b ^ 3 +
        17280000 * a * b ^ 4) * Gh a b := by
  unfold Fh Gh; ring

/-- Nullstellensatz certificate for `y⁷` (`scratch/wk-h/f4_cert.py`). -/
theorem cert_y (a b : ℤ) :
    104976000000 * b ^ 7 = (-1001 * a - 37650 * b) * Fh a b +
      (143 * a ^ 5 + 20557 * a ^ 4 * b + 1026600 * a ^ 3 * b ^ 2 + 20691900 * a ^ 2 * b ^ 3 +
        133110000 * a * b ^ 4 + 29160000 * b ^ 5) * Gh a b := by
  unfold Fh Gh; ring

/-- `G` has no rational zero (negative discriminant). -/
theorem G_ne_zero (u : ℚ) : 7 * u ^ 2 + 300 * u + 3600 ≠ 0 := by
  nlinarith [sq_nonneg (7 * u + 150)]

/-- `C₀ = 57600²·3⁷·(2¹⁰3⁸5⁶)⁷`, the bound for the cancellation in `J(u)`. -/
def C0 : ℤ := (57600 * 3 ^ 7) * (57600 * 104976000000 ^ 7)

/-- **Cancellation bound.** For coprime `a, b`, a common divisor of `57600F_h²` and `G_h⁶` divides
`C₀` (from `cert_x`, `cert_y` raised to the 7th power). -/
theorem dvd_C0 {a b c : ℤ} (hab : IsCoprime a b) (hP : c ∣ 57600 * Fh a b ^ 2)
    (hQ : c ∣ Gh a b ^ 6) : c ∣ C0 := by
  have key : ∀ x y : ℤ, 57600 * (x + y) ^ 7 =
      57600 * x ^ 2 * (x ^ 5 + 7 * x ^ 4 * y + 21 * x ^ 3 * y ^ 2 + 35 * x ^ 2 * y ^ 3 +
        35 * x * y ^ 4 + 21 * y ^ 5) + y ^ 6 * (57600 * (7 * x + y)) := by intros; ring
  have hsplit : ∀ (A B : ℤ), c ∣ 57600 * (A * Fh a b + B * Gh a b) ^ 7 := by
    intro A B
    rw [key]
    refine dvd_add ?_ ?_
    · have : 57600 * (A * Fh a b) ^ 2 = (57600 * Fh a b ^ 2) * A ^ 2 := by ring
      rw [this, mul_assoc]; exact dvd_mul_of_dvd_left hP _
    · have : (B * Gh a b) ^ 6 = Gh a b ^ 6 * B ^ 6 := by ring
      rw [this, mul_assoc]; exact dvd_mul_of_dvd_left hQ _
  have hx : c ∣ 57600 * 3 ^ 7 * a ^ 49 := by
    have e : 57600 * 3 ^ 7 * a ^ 49 = 57600 * (3 * a ^ 7) ^ 7 := by ring
    rw [e, cert_x]; exact hsplit _ _
  have hy : c ∣ 57600 * 104976000000 ^ 7 * b ^ 49 := by
    have e : 57600 * 104976000000 ^ 7 * b ^ 49 = 57600 * (104976000000 * b ^ 7) ^ 7 := by ring
    rw [e, cert_y]; exact hsplit _ _
  obtain ⟨s, t, hst⟩ := hab.pow (m := 49) (n := 49)
  have e : C0 = (57600 * 104976000000 ^ 7 * s) * (57600 * 3 ^ 7 * a ^ 49) +
      (57600 * 3 ^ 7 * t) * (57600 * 104976000000 ^ 7 * b ^ 49) := by
    have : C0 = C0 * (s * a ^ 49 + t * b ^ 49) := by rw [hst, mul_one]
    rw [this, C0]; ring
  rw [e]
  exact dvd_add (dvd_mul_of_dvd_right hx _) (dvd_mul_of_dvd_right hy _)

theorem abs_monomial_le {a b m : ℤ} (ha : |a| ≤ m) (hb : |b| ≤ m) (i j : ℕ) :
    |a ^ i * b ^ j| ≤ m ^ (i + j) := by
  have hm : 0 ≤ m := (abs_nonneg a).trans ha
  rw [abs_mul, abs_pow, abs_pow, pow_add]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) ha _) (pow_le_pow_left₀ (abs_nonneg _) hb _)
    (by positivity) (by positivity)

/-- **Lower bound.** With `m = max(|a|, |b|) > 0`: `m¹² ≤ 10⁴⁸ max(57600F_h², G_h⁶)`. -/
theorem lower_bound {a b m : ℤ} (ha : |a| ≤ m) (hb : |b| ≤ m) (hm : 0 < m)
    (hmax : m = |a| ∨ m = |b|) :
    m ^ 12 ≤ 10 ^ 48 * max (57600 * Fh a b ^ 2) (Gh a b ^ 6) := by
  by_contra hlt
  push Not at hlt
  have hP := le_max_left (57600 * Fh a b ^ 2) (Gh a b ^ 6)
  have hQ := le_max_right (57600 * Fh a b ^ 2) (Gh a b ^ 6)
  have hF : 240 * 10 ^ 24 * |Fh a b| < m ^ 6 := by
    have h2 : (240 * 10 ^ 24 * |Fh a b|) ^ 2 < (m ^ 6) ^ 2 := by
      rw [mul_pow, sq_abs]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h2
  have hG : 10 ^ 8 * |Gh a b| < m ^ 2 := by
    have h6 : (10 ^ 8 * |Gh a b|) ^ 6 < (m ^ 2) ^ 6 := by
      rw [mul_pow, pow_abs, abs_of_nonneg (by positivity : (0:ℤ) ≤ Gh a b ^ 6)]
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 6 (by positivity) h6
  have hX : 240 * 10 ^ 24 * (m * |Fh a b|) < m ^ 7 := by nlinarith
  have hY : 10 ^ 8 * (m ^ 5 * |Gh a b|) < m ^ 7 := by
    have : (0 : ℤ) < m ^ 5 := by positivity
    nlinarith
  have m10 : -m ≤ a ∧ a ≤ m := abs_le.mp ha
  have m01 : -m ≤ b ∧ b ≤ m := abs_le.mp hb
  have mono : ∀ i j : ℕ, i + j = 5 → -m ^ 5 ≤ a ^ i * b ^ j ∧ a ^ i * b ^ j ≤ m ^ 5 := by
    intro i j hij
    have := abs_monomial_le ha hb i j
    rw [hij] at this
    exact abs_le.mp this
  have m50 := mono 5 0 rfl
  have m41 := mono 4 1 rfl
  have m32 := mono 3 2 rfl
  have m23 := mono 2 3 rfl
  have m14 := mono 1 4 rfl
  have m05 := mono 0 5 rfl
  simp only [pow_one, pow_zero, mul_one, one_mul] at m50 m41 m32 m23 m14 m05
  have hm7 : (0 : ℤ) < m ^ 7 := by positivity
  have tri : ∀ A B : ℤ, |A * Fh a b + B * Gh a b| ≤ |A| * |Fh a b| + |B| * |Gh a b| := by
    intro A B; rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
  rcases hmax with h | h
  · have hA : |-200 * a - 4800 * b| ≤ 5000 * m := by
      rw [abs_le]; constructor <;> linarith
    have hB : |29 * a ^ 5 + 3700 * a ^ 4 * b + 164400 * a ^ 3 * b ^ 2 + 2880000 * a ^ 2 * b ^ 3 +
        17280000 * a * b ^ 4| ≤ 20328129 * m ^ 5 := by
      rw [abs_le]; constructor <;> linarith
    have e := tri (-200 * a - 4800 * b) (29 * a ^ 5 + 3700 * a ^ 4 * b + 164400 * a ^ 3 * b ^ 2 +
      2880000 * a ^ 2 * b ^ 3 + 17280000 * a * b ^ 4)
    rw [← cert_x, abs_mul, abs_pow, ← h, show |(3 : ℤ)| = 3 by norm_num] at e
    have e1 := mul_le_mul_of_nonneg_right hA (abs_nonneg (Fh a b))
    have e2 := mul_le_mul_of_nonneg_right hB (abs_nonneg (Gh a b))
    linarith
  · have hA : |-1001 * a - 37650 * b| ≤ 38651 * m := by
      rw [abs_le]; constructor <;> linarith
    have hB : |143 * a ^ 5 + 20557 * a ^ 4 * b + 1026600 * a ^ 3 * b ^ 2 +
        20691900 * a ^ 2 * b ^ 3 + 133110000 * a * b ^ 4 + 29160000 * b ^ 5| ≤
        184009200 * m ^ 5 := by
      rw [abs_le]; constructor <;> linarith
    have e := tri (-1001 * a - 37650 * b) (143 * a ^ 5 + 20557 * a ^ 4 * b +
      1026600 * a ^ 3 * b ^ 2 + 20691900 * a ^ 2 * b ^ 3 + 133110000 * a * b ^ 4 + 29160000 * b ^ 5)
    rw [← cert_y, abs_mul, abs_pow, ← h, show |(104976000000 : ℤ)| = 104976000000 by norm_num] at e
    have e1 := mul_le_mul_of_nonneg_right hA (abs_nonneg (Fh a b))
    have e2 := mul_le_mul_of_nonneg_right hB (abs_nonneg (Gh a b))
    linarith

/-- **F4, strengthened.** `12 h(u) ≤ h(J(u)) + 450` for `u ∉ 𝒞` (N5: `h(u) < h(J(u)) + 74`). -/
theorem twelve_mul_ratHeight_le (u : ℚ) (_hu : u ∉ contactSet) :
    12 * ratHeight u ≤ ratHeight (Jmap u) + 450 := by
  set a : ℤ := u.num with ha_def
  set b : ℤ := (u.den : ℤ) with hb_def
  have hb : 0 < b := by rw [hb_def]; exact_mod_cast u.den_pos
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hcop : IsCoprime a b := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact u.reduced
  have hu_eq : u = (a : ℚ) / (b : ℚ) := by
    rw [ha_def, hb_def]; push_cast; exact (Rat.num_div_den u).symm
  have hFq : u * (u + 15) * (u + 20) * (u + 24) * (u + 30) * (u + 60) =
      (Fh a b : ℚ) / (b : ℚ) ^ 6 := by
    rw [hu_eq]; unfold Fh; push_cast; field_simp
  have hGq : 7 * u ^ 2 + 300 * u + 3600 = (Gh a b : ℚ) / (b : ℚ) ^ 2 := by
    rw [hu_eq]; unfold Gh; push_cast; field_simp
  have hG0 : 0 < Gh a b := by unfold Gh; nlinarith [sq_nonneg (7 * a + 150 * b), mul_pos hb hb]
  set n : ℤ := -(57600 * Fh a b ^ 2) with hn_def
  set d : ℤ := Gh a b ^ 6 with hd_def
  have hdpos : 0 < d := by positivity
  have hJ : Jmap u = (n : ℚ) / (d : ℚ) := by
    have hGq0 : (Gh a b : ℚ) ≠ 0 := by exact_mod_cast hG0.ne'
    unfold Jmap; rw [hFq, hGq, hn_def, hd_def]; push_cast; field_simp
  obtain ⟨c, hn, hd⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den n hdpos.ne'
  rw [← hJ] at hn hd
  set J := Jmap u with hJdef
  have hden : (0 : ℤ) < (J.den : ℤ) := by exact_mod_cast J.den_pos
  have hcpos : 0 < c := by
    by_contra h; push Not at h; rw [hd] at hdpos; nlinarith
  have hcdvd : c ∣ C0 := dvd_C0 hcop (dvd_neg.mp (Dvd.intro _ hn.symm)) (Dvd.intro _ hd.symm)
  have hcle : c ≤ C0 := Int.le_of_dvd (by norm_num [C0]) hcdvd
  have hmaxeq : max (57600 * Fh a b ^ 2) d = c * max |J.num| (J.den : ℤ) := by
    have h1 : 57600 * Fh a b ^ 2 = |n| := by
      rw [hn_def, abs_neg, abs_of_nonneg (by positivity)]
    rw [h1, hn, hd, abs_mul, abs_of_pos hcpos, mul_max_of_nonneg _ _ hcpos.le]
  set m := max |a| b with hm_def
  have hm : 0 < m := lt_of_lt_of_le hb (le_max_right _ _)
  have hlow := lower_bound (a := a) (b := b) (le_max_left |a| b)
    (by rw [abs_of_pos hb]; exact le_max_right _ _) hm
    (by rcases max_choice |a| b with h | h
        · left; exact h
        · right; rw [abs_of_pos hb]; exact h)
  rw [hmaxeq] at hlow
  set H := max |J.num| (J.den : ℤ) with hH_def
  have hH : 1 ≤ H := le_max_of_le_right (by exact_mod_cast J.den_pos)
  have hlow2 : m ^ 12 ≤ 10 ^ 139 * H := by
    have hC : 10 ^ 48 * C0 ≤ 10 ^ 139 := by norm_num [C0]
    calc m ^ 12 ≤ 10 ^ 48 * (c * H) := hlow
      _ ≤ 10 ^ 48 * (C0 * H) := by gcongr
      _ = (10 ^ 48 * C0) * H := by ring
      _ ≤ 10 ^ 139 * H := by gcongr
  have hu_h : ratHeight u = Real.log (m : ℝ) := by
    unfold ratHeight; rw [hm_def]; push_cast [ha_def, hb_def]; rfl
  have hJ_h : ratHeight J = Real.log (H : ℝ) := by
    unfold ratHeight; rw [hH_def]; push_cast; rfl
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hlowR : (m : ℝ) ^ 12 ≤ 10 ^ 139 * (H : ℝ) := by exact_mod_cast hlow2
  have hlog10 : Real.log 10 < 3 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h1 := Real.exp_one_gt_d9
    have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have h2 : (2.7 : ℝ) ^ 3 < Real.exp 1 ^ 3 :=
      pow_lt_pow_left₀ (by linarith) (by norm_num) (by norm_num)
    rw [this]; norm_num at h2 ⊢; linarith
  have key : 12 * Real.log (m : ℝ) ≤ 139 * Real.log 10 + Real.log (H : ℝ) := by
    have := Real.log_le_log (by positivity) hlowR
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow] at this
    push_cast at this
    linarith
  rw [hu_h, hJ_h]
  linarith

/-- Verbatim copy of `ZInQ.JHeight.heightX`: `max(1, C_cm, Q_R¹⁷)`. -/
def heightX (R : ℝ) : ℝ := max 1 (max (heightCcm : ℝ) (heightQ R ^ 17))

/-- Verbatim copy of `ZInQ.JHeight.JHeightBound S`. -/
def JHeightBoundAt (S : Finset ℕ) : Prop :=
  ∀ u : ℚ, u ∉ contactSet →
    ratHeight (Jmap u) ≤
      (40 * 10000 * 2 ^ 24 + 22 : ℝ) * heightX heightD * (contactSupport S u : ℝ) ^ 24

/-- The body of `ZInQ.SixContactMin` with `Mult.S_mul` abstracted to `S`
(`SixContactMinAt Mult.S_mul` is `SixContactMin` by `rfl`). -/
def SixContactMinAt (S : Finset ℕ) : Prop :=
  ∀ u : ℚ, u ∉ contactSet →
    ratHeight u ≤ heightH6 (heightD : ℝ) * (contactSupport S u : ℝ) ^ 24

/-- `Q = D^{D E₀}`, the constant `Q_R` at `R = D`. -/
def Qc : ℝ := heightQ (heightD : ℝ)

/-- **What L1-L7 and the glue G1-G17 deliver** (N5 L405-867 on route K; note §4): for
`u ∈ ℚ \ 𝒞` there are a number field `K` with `[K:ℚ] ≤ Q·M` (N5's `L'`), a genus-2 sextic over
`K` on the QM locus over `J(u)`, and a `K`-isogeny `J₁(N) → Jac(C) × Z` with `N ≤ Q·M²`,
`M = M_S(u)` (used at `S = Mult.S_mul`). The CM alternative of N5 is excluded by NoCM (glue G8).
It is a lemma of the decomposition, not a leaf. -/
def ModularityOutput (S : Finset ℕ) : Prop :=
  ∀ u : ℚ, u ∉ contactSet →
    ∃ (K : NF) (a : K) (r : Fin 6 → K), IsGenus2 a r ∧
      OnQMLocus a r ((Jmap u : ℚ) : K) ∧
      (Module.finrank ℚ K : ℝ) ≤ Qc * contactSupport S u ∧
      ∃ N : ℕ, 1 ≤ N ∧ (N : ℝ) ≤ Qc * (contactSupport S u : ℝ) ^ 2 ∧
        ∃ Z : O.AV K, Nonempty (O.Isog (O.J1 K N) (O.prod (O.jac a r) Z))

/-- **Glue G18-G23 (E2-E4, F1-F3 with Thomae).** From the Arakelov leaves and the output of the
modularity half, the `j`-form of H. To be proved: E's arithmetic is wk-h's `transfer_numerics`
(`scratch/wk-h/Arakelov.lean`, proved); F1 is `j_eq_of_onQMLocus`; F2 is a degree-10 height
estimate for `[3779136 ∏ T_S : (Σ T_S²)⁵]` (Mathlib's `Height.logHeight_eval_le`), plus the
invariance of the absolute height of a rational number under extension of `K`. -/
theorem jHeightBoundAt_of_leaves (S : Finset ℕ) (hA : ArakelovLeaves O)
    (hM : ModularityOutput O S) : JHeightBoundAt S := by
  sorry

/-- The repository's `ZInQ.JHeight.sixContactMin_of_jHeightBound` (proved in
`ZInQKernel/Hypotheses/JHeight.lean`, standard axioms), restated for an arbitrary `S`; its proof
there does not use any property of `S`; proved here from the verbatim copy of F4 above. -/
theorem sixContactMinAt_of_jHeightBoundAt (S : Finset ℕ) (hJ : JHeightBoundAt S) :
    SixContactMinAt S := by
  intro u hu
  have h12 := twelve_mul_ratHeight_le u hu
  have hj := hJ u hu
  have hX : 1 ≤ heightX heightD := le_max_left _ _
  have hM : (1 : ℝ) ≤ (contactSupport S u : ℝ) ^ 24 :=
    one_le_pow₀ (by exact_mod_cast contactSupport_pos _ _)
  have hXM : 1 ≤ heightX heightD * (contactSupport S u : ℝ) ^ 24 :=
    one_le_mul_of_one_le_of_one_le hX hM
  have e : heightH6 (heightD : ℝ) = 2 * 10 ^ 13 * heightX heightD := rfl
  rw [e]
  nlinarith

/-- **Top-level glue.** The Arakelov leaves L8-L12 and the output of the modularity half imply
`SixContactMin` (at `S = Mult.S_mul`). -/
theorem sixContactMinAt_of_leaves (S : Finset ℕ) (hA : ArakelovLeaves O)
    (hM : ModularityOutput O S) : SixContactMinAt S :=
  sixContactMinAt_of_jHeightBoundAt S (jHeightBoundAt_of_leaves O S hA hM)

end HDec

#print axioms HDec.j_eq_of_onQMLocus
#print axioms HDec.sixContactMinAt_of_jHeightBoundAt
#print axioms HDec.sixContactMinAt_of_leaves
