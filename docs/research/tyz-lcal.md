# tyz-lcal: the three L-leaves of the TYZ decomposition

Task tyz-lcal, 2026-11-13/14. Lean: `scratch/tyz-lcal/TYZLcal.lean` (one file, about 930 lines, imports
`ZInQKernel.Contrib.TYZDecomp.Leaves`, `ZInQKernel.Contrib.HeckeAll.Continuation`,
`ZInQKernel.Contrib.GaussFE.FunctionalEquation5`, `Mathlib.NumberTheory.NumberField.Cyclotomic.PID`;
namespace `ZInQ.Contrib.TYZLcal`). It compiles with `lake env lean` with no errors, no warnings, no `sorry` and
no `axiom`. Results log: `scratch/tyz-lcal/log.md`. Numerics: `scratch/tyz-lcal/lcal_check.py` with output
`out_lcal_check.txt`. No existing file was edited.

Marks: **VERIFIED** means read in a source named here, computed, or compiled. **STANDARD** means a published
theorem with its reference. **SPECULATIVE** means an assessment. **UNVERIFIED** means a locator or theorem number
that was not read here. TYZ is Tian–Yuan–Zhang, arXiv:1411.4728v1 (Asian J. Math. 21 (2017)). Their source
`Period7.tex` is not on this host (`~/tyz-src` does not exist), so every TYZ line number below is quoted from
`nt-tyz.md`, `rv-nt-tyz.md`, `rv-pn-encoding.md` or `tyz-decomp.md`.

## 0. Main result

**`TYZLcalOne` is not an independent leaf. It is a theorem of the fork given the other two L-leaves**
(VERIFIED, compiled; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`):

```lean
theorem tyzLcalOne_of_leaves (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) : TYZLcalOne
```

Consequences:

```lean
theorem tyzThm35ReadingA_of_three_leaves (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hG : TYZGenusPackage) : ZInQ.Literature.TYZThm35ReadingA
theorem genusPackage_iff_readingA_of_two (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) :
    TYZGenusPackage ↔ ZInQ.Literature.TYZThm35ReadingA
```

So the TYZ side of the decomposition goes from four leaves to three: `TYZThm11Integral`, `TYZLemma29Mod2` and
`TYZGenusPackage`. The leaf that is removed was the weakest-sourced one. TYZ only assert it ("Since
`𝓛(1) = 1`", L1082), and its earlier citation went through tables (Cremona) or Tunnell at `n = 1`.

The proof has three parts:

1. **Arithmetic.**
   * `TYZThm11Integral` at `m = 1` gives `lcalSq 1 = a²` with `a ∈ ℤ`.
   * `TYZLemma29Mod2` at `m = 3` gives `𝓛(3)𝓛(1) ≡ g(3) (mod 2)`.
   * `g(3) = #2Cl(ℚ(√−3)) = 1` is proved in Lean (`gCl_three`): `ℚ(√−3)` is `ℚ(ζ₃)`, and Mathlib proves that
     `𝓞` of it is a PID (`IsCyclotomicExtension.Rat.three_pid`).
   * So `a` is odd, and either `a² = 1` or `a² ≥ 9`.
2. **Analysis (glue, proved).** `‖L(C₁, 1)‖ ≤ 3.35` and `∫₁^∞ dx/√(x³ − x) ≥ 2`. Since
   `lcalSq 1 = 4 L(C₁,1) / ∫₁^∞ dx/√(x³−x)`, the case `a² ≥ 9` would force `‖L(C₁,1)‖ ≥ (9/4)·2 = 4.5`, which
   the bound excludes. The true value is `L(C₁,1) = 0.6555…`.
3. **The continuation used** is the explicit Hecke theta integral of `Contrib/HeckeFE`, which the fork already
   uses to prove `HeckeContinuation`. By uniqueness of continuations it is the function behind `lValOne`.

The two remaining L-leaves are genuinely TYZ-specific, faithful, and not stronger than TYZ. §2 checks this
statement by statement. A sign-independence lemma, `lemma29Mod2_iff`, shows that the universally quantified
sign choice in `TYZLemma29Mod2` is harmless.

## 1. The Lean declarations (exact types; all compiled)

Namespace `ZInQ.Contrib.TYZLcal`, with `open ZInQ.Literature ZInQ.PropN ZInQ.RouteK.Rank5b
ZInQ.Contrib.TYZDecomp`. The leaves `TYZThm11Integral`, `TYZLcalOne`, `TYZLemma29Mod2` and the definitions
`lcalSq`, `lValOne`, `omegaInt`, `omegaTYZ`, `curveC` are those of `ZInQKernel/Contrib/TYZDecomp/Leaves.lean`.
They are imported, not copied, so these theorems are about exactly those Props.

**Arithmetic part (§1–§2 of the file).**

```lean
def zeta3 : QNeg 3 := ⟨-1 / 2, 1 / 2⟩
theorem zeta3_isPrimitiveRoot : IsPrimitiveRoot zeta3 3
instance isCyclotomicExtension_three : IsCyclotomicExtension {3} ℚ (QNeg 3)
theorem gCl_three : gCl 3 = 1
theorem gNat_three : gNat 3 = 1
theorem lcalSq_one : lcalSq 1 = lValOne 1 / ((omegaInt : ℂ) / 4)
def ellOf (h11 : TYZThm11Integral) : ℕ → ℤ         -- a sign choice of 𝓛 on classes 1, 3
theorem ell_one_odd (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) {a : ℤ}
    (ha : (a : ℂ) ^ 2 = lcalSq 1) : Odd a
def LValOneBound : Prop := ‖lValOne 1‖ < 9 / 4 * omegaInt
theorem lcalOne_of_leaves (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) (hB : LValOneBound) :
    TYZLcalOne
```

**Analytic part (§1–§7 of the second half of the file, `open Complex Real Set MeasureTheory HurwitzZeta
ZInQ.Contrib.HeckeFE`).**

```lean
theorem gaussLambda_one_eq (a b : UnitAddCircle) :
    gaussLambda a b 1 = (∫ x in Ioi 1, gaussTheta a b x) + ∫ x in Ioi 1, gaussThetaDual a b x
theorem norm_integral_Ioi_one_le {f : ℝ → ℂ} {C c : ℝ} (hc : 0 < c)
    (hf : ∀ x : ℝ, 1 < x → ‖f x‖ ≤ C * Real.exp (-c * (x - 1))) :
    ‖∫ x in Ioi (1 : ℝ), f x‖ ≤ C / c
def Fexp (M : ℕ) (c : ZMod M × ZMod M → ℂ) (s : ℂ) : ℂ      -- HeckeFE's continuation, explicitly
def cU (x : ZMod 4 × ZMod 4) : ℂ := (1 / 4) * unitOf x
theorem isLContinuation_Fone : IsLContinuation (curveC 1) (Fexp 4 cU)
theorem lValOne_one_eq : lValOne 1 =
    ∑ j : Fin 4 × Fin 4, cU (((j.1 : ℤ) : ZMod 4), ((j.2 : ℤ) : ZMod 4)) * (1 / 4) *
      ((π : ℂ) * gaussLambda (((j.1 : ℝ) / 4 : ℝ) : UnitAddCircle)
        (((j.2 : ℝ) / 4 : ℝ) : UnitAddCircle) 1)
theorem abs_oddKernel_quarter_le {x : ℝ} (hx : 1 ≤ x) :
    |oddKernel ((1 / 4 : ℝ) : UnitAddCircle) x| ≤ 0.37 * Real.exp (-(π / 16) * (x - 1))
theorem abs_evenKernel_zero_le {x : ℝ} (hx : 1 ≤ x) : |evenKernel ((0 : ℝ) : UnitAddCircle) x| ≤ 1.11
theorem abs_evenKernel_half_le {x : ℝ} (hx : 1 ≤ x) :
    |evenKernel ((1 / 2 : ℝ) : UnitAddCircle) x| ≤ 1.11
theorem abs_cosKernel_le (b : ℝ) {x : ℝ} (hx : 1 ≤ x) : |cosKernel (b : UnitAddCircle) x| ≤ 1.11
theorem abs_sinKernel_le (a : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    |sinKernel (a : UnitAddCircle) x| ≤ 0.112 * Real.exp (-π * (x - 1))
theorem norm_gaussLambda_le_A {a b : ℝ} (ha : a = 1 / 4 ∨ a = 3 / 4) (hb : b = 0 ∨ b = 1 / 2) :
    ‖gaussLambda (a : UnitAddCircle) (b : UnitAddCircle) 1‖ ≤ 6.7 / π
theorem norm_gaussLambda_le_B {a b : ℝ} (ha : a = 0 ∨ a = 1 / 2) (hb : b = 1 / 4 ∨ b = 3 / 4) :
    ‖gaussLambda (a : UnitAddCircle) (b : UnitAddCircle) 1‖ ≤ 6.7 / π
theorem norm_lValOne_one_le : ‖lValOne 1‖ ≤ 3.35
theorem omegaInt_ge_two : 2 ≤ omegaInt
theorem lValOneBound : LValOneBound
```

**Final results and sign independence (§8, §9).**

```lean
theorem tyzLcalOne_of_leaves (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) : TYZLcalOne
theorem tyzLcalOne_of_leaves' (h11 : TYZThm11Integral) (h11b : TYZThm11Mod2) : TYZLcalOne
theorem tyzThm35ReadingA_of_three_leaves (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hG : TYZGenusPackage) : ZInQ.Literature.TYZThm35ReadingA
theorem genusPackage_iff_readingA_of_two (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) :
    TYZGenusPackage ↔ ZInQ.Literature.TYZThm35ReadingA
theorem lemmaTwoEight_congr {ℓ ℓ' : ℕ → ℤ}
    (h : ∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((ℓ m : ℤ) : ZMod 2) = ℓ' m)
    (hℓ : LemmaTwoEight ℓ) : LemmaTwoEight ℓ'
theorem lemma29Mod2_iff (h11 : TYZThm11Integral) : TYZLemma29Mod2 ↔ LemmaTwoEight (ellOf h11)
```

`#print axioms` (VERIFIED, 2026-11-13 23:15) gives `[propext, Classical.choice, Quot.sound]` for each of:
`gCl_three`, `ell_one_odd`, `lcalOne_of_leaves`, `isLContinuation_Fone`, `norm_lValOne_one_le`,
`omegaInt_ge_two`, `lValOneBound`, `tyzLcalOne_of_leaves`, `tyzThm35ReadingA_of_three_leaves`,
`genusPackage_iff_readingA_of_two`, `lemma29Mod2_iff`, `tyzLcalOne_of_leaves'`.

### 1.1 The analytic bound, step by step

* The coefficient `c(α) = ¼·unitOf(α mod 4)` is `ψ₁(α)/α` for the Hecke character of `y² = x³ − x`.
  `DeuringCd 1` (from the fork's `GaussFE.gaussPointCount`) and `LSeries_cd_eq` identify Mathlib's `L(C₁, s)`
  with `Σ_α c(α) α N(α)^{−s}` for `Re s > 3/2`.
* `Fexp 4 cU s = Σ_j c_j · 4·16^{−s} · π^s Γ(s)^{−1} Λ_{j/4}(s)`, where `Λ_{a,b} = mellin θ_{a,b}`, is
  entire. `isLContinuation_Fone` proves that it continues Mathlib's `L(C₁, s)`. At `s = 1`, `Γ(1) = 1`,
  which gives `lValOne_one_eq`.
* `Λ_{a,b}(1) = ∫₁^∞ θ_{a,b} + ∫₁^∞ θ^dual_{a,b}`. This follows by splitting the Mellin integral at `1` and
  substituting `x ↦ 1/x` on `(0, 1)` (`mellin_comp_inv`, with the weight-two law `θ(1/x) = x² θ^dual(x)`).
* Only the eight classes `j` with `unitOf j ≠ 0` contribute. These are the `(a, b)` with exactly one
  coordinate in `{1/4, 3/4}` and the other in `{0, 1/2}`. The other coordinate is fixed by `b ↦ −b`, so
  `oddKernel b = sinKernel b = 0`, and
  * `θ_{a,b} = oddKernel(a)·evenKernel(b)`,
  * `θ^dual_{a,b} = sinKernel(a)·cosKernel(b)`
  (or the same with `a` and `b` swapped).
* On `x ≥ 1`, Mathlib's Hurwitz kernels are bounded by explicit geometric majorants over `ℤ = ℕ ⊔ (−ℕ−1)`:
  * `|oddKernel(1/4)| ≤ 0.37 e^{−π(x−1)/16}`;
  * `|evenKernel(0)|, |evenKernel(1/2)|, |cosKernel| ≤ 1.11`;
  * `|sinKernel| ≤ 0.112 e^{−π(x−1)}`.

  The exponential constants come from `exp 1 > 2.718` and `exp y ≥ 1 + y + y²/2`.
* Hence `‖Λ_j(1)‖ ≤ (0.37·1.11)/(π/16) + (0.112·1.11)/π ≤ 6.7/π`, and
  `‖L(C₁,1)‖ ≤ 8 · ¼ · ¼ · π · 6.7/π = 3.35`.
* `∫₁^∞ dx/√(x³ − x) ≥ ∫₁^∞ x^{−3/2} dx = 2`.

## 2. The three statements: what they say, and faithfulness

### 2.1 `TYZThm11Integral` (remains a leaf; genuinely TYZ)

```lean
def TYZThm11Integral : Prop :=
  ∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ∃ ℓ : ℤ, (ℓ : ℂ) ^ 2 = lcalSq m
-- lcalSq m = L(C_m,1) / (2^{2k(m)−3} · (2/√m) ∫₁^∞ dx/√(x³−x)),  k(m) = #prime factors of m
```

**What it says.** For odd squarefree `m ≡ 1, 3 (mod 8)`, `m = 1` included, the number
`L(C_m, 1)/(2^{2k−3}Ω_m)` is the square of an integer.

**Faithfulness.**

* *Source.* It is TYZ Theorem 1.1, first assertion (L371–380, quoted in nt-tyz §1.2: "Let `n ≡ 1, 2, 3 (mod 8)`
  be positive and squarefree. Then `𝓛(n)` is an integer"). The Lean statement restricted to odd `n ≡ 1, 3`. The
  case `n = 1` is covered, since Theorem 1.1's congruence explicitly sets its right side to `1` at `n = 1`.
* *Normalisation.* The definition `𝓛(n)² = L(E_n,1)/(2^{2k−2−a}Ω_{n,∞})`, with `a(n) = 1` for odd `n` and
  `Ω_n = (2/√n)∫₁^∞`, is TYZ L338–353 as transcribed by rv-tyz-inputs (`tyzcalc.py`). It is not re-read here
  (needs a human check against the source).
* *Numerical check of the normalisation* (VERIFIED, computed, `out_lcal_check.txt`, the first 30 squarefree
  `m ≡ 1, 3 (mod 8)`, `m ≤ 155`). `lcalSq(m)` is an integer square to within `4·10⁻¹⁵` in every case:
  * value `1` for most `m`;
  * `4` at 17, 73, 89, 97, 155;
  * `9` at 43, 107, 131;
  * `16` at 113;
  * `0` at 41, 65, 137, 145.

  A factor-2 error in `2^{2k−3}` or in `Ω` would give non-squares. Independently, `|𝓛(m)| = |a_T(m)|/2^k` on all
  30 values, where `a_T` are the coefficients of Tunnell's form `η(8z)η(16z)θ(2z)`. This agrees with
  rv-pn-encoding's check `𝓛(n) = ±(A_n − 2B_n)/2^{k+1}`.
* *The L-function.* Mathlib's `L(C_m, s)` is the true `L(E_m, s)`. The model `y² = x³ − m²x` is minimal at
  every place, with additive reduction exactly at `p ∣ 2m` (`HeckeAll/LocalCd.lean`: `isMinimal_cdLocal'`,
  `localPolynomial_cdLocal_eq'`, `LSeries_cd_eq'`). `E_m : my² = x³ − x` is `ℚ`-isomorphic to `C_m`.
  `lValOne` is the value of the unique continuation (`lValOne_eq`).
* *Strength.* The Lean statement only asserts that an integer square root exists, which is what "`𝓛(n)` is an
  integer" says. It is not stronger.

**Not reducible here.** The integrality of `𝓛` is the Waldspurger/Gross-point content of TYZ §2. Nothing in
`Contrib/PSide` (`a_p` values, Hasse's bound, convergence) bears on `L(C_m, 1)`. *Remark* (SPECULATIVE):

* Tunnell's formula (Invent. Math. 72 (1983); statement from memory, UNVERIFIED) is
  `L(C_m,1) = ∫₁^∞dx/√(x³−x) · a_T(m)²/(4√m)`.
* Given it, `TYZThm11Integral` becomes the combinatorial statement `2^{k(m)} ∣ a_T(m)` for `m ≡ 1, 3 (mod 8)`
  (numerically VERIFIED on the 30 values).
* It is not known here whether that divisibility has an elementary proof. If it has, `TYZThm11Integral` could
  be replaced by Tunnell's theorem, which is older and more widely checked.

### 2.2 `TYZLcalOne` (no longer a leaf)

```lean
def TYZLcalOne : Prop := lcalSq 1 = 1      -- ⇔ L(C₁,1) = ¼ ∫₁^∞ dx/√(x³−x)   (lcalSq_one)
```

**What it says.** `L(y² = x³ − x, 1) = ¼∫₁^∞ dx/√(x³ − x)`, i.e. `L(E,1)/Ω = 1/8` for 32a2.

**Status.** It is true (numerically VERIFIED: `L(C₁,1) = 0.6555143886`, `omegaInt = 2.622057554292 =
π/AGM(1,√2)`, so the ratio is `1/4`). It is now **proved from the other two L-leaves**
(`tyzLcalOne_of_leaves`).

**One point for a human check.** The derivation uses `TYZLemma29Mod2` at `m = 3`. That is exactly where
rv-nt-tyz B1 found that the printed Lemma 2.9 and Theorem 2.1 differ by the factor `w_K = 3`. The *mod-2* leaf
holds under either version, because 3 is odd. Numerically `𝓛(3)𝓛(1) = ±1` and `g(3) = 1`. So the derivation is
valid whichever statement is the misprint.

Logically, TYZ's own proof of Theorem 1.1 uses "`𝓛(1) = 1`" (L1082). Deriving it back from Lemma 2.9 is not
circular as a leaf decomposition, since leaves are published statements, not proofs. But it does mean that the
correctness of the two remaining leaves now carries this fact. This is SPECULATIVE as to whether TYZ's proof of
Lemma 2.9 itself uses L1082; it should be checked by a human with the source. The ordering in the source
suggests that Lemma 2.9 (L1062) precedes the use at L1082.

### 2.3 `TYZLemma29Mod2` (remains a leaf; genuinely TYZ)

```lean
def TYZLemma29Mod2 : Prop :=
  ∀ ℓ : ℕ → ℤ, (∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((ℓ m : ℂ)) ^ 2 = lcalSq m) →
    LemmaTwoEight ℓ
```

`LemmaTwoEight ℓ` says, for squarefree `m`:

* `m ≡ 1`, `m > 1`: `Σ_{d ∣ m, d ≡ 1, d² < m} ℓ(d)ℓ(m/d) ≡ g(m) (mod 2)`;
* `m ≡ 3`: `Σ_{d ∣ m, d ≡ 1} ℓ(m/d)ℓ(d) ≡ g(m) (mod 2)`;

where `g(m) = #2Cl(ℚ(√−m))`.

**What it says.** The parity of TYZ's convolution `Σ ε(d₁,d₂)𝓛(d₁)𝓛(d₂)` over non-ordered decompositions
`m = d₁d₂` with `d₂ ≡ 1` is the parity of `g(m)`.

**Faithfulness.**

* *Source.* It is TYZ Lemma 2.9 (L1062–1066) together with Proposition 2.3 (`Q(m) ≡ g(m)`, L580–586), read
  mod 2. The signs `ε` and the odd factor `w_K` vanish mod 2.
* *Prior reviews.* rv-pn-encoding re-derived the restriction `1 < m` for `m ≡ 1` and the one-member-per-pair
  filter (lemma28-L). It also showed that with the 2-primary part instead of `#2Cl` the statement would be
  false at `m = 33`, and the Lean statement uses `#2Cl`.
* *Numerical check here* (VERIFIED, computed): the congruence holds for all 29 values `m ≤ 155`, `m > 1` of the
  sample, with `ℓ = √lcalSq` and `g = h/2^{t−1}` (class numbers by reduced forms).
* *Universal quantifier.* The `∀ ℓ` over sign choices is harmless. `lemma29Mod2_iff` proves
  `TYZLemma29Mod2 ↔ LemmaTwoEight (ellOf h11)` under integrality, because `LemmaTwoEight` reads `ℓ` only mod 2,
  on squarefree classes 1 and 3.
* *Strength and vacuity.* It is a consequence of TYZ, not stronger. It is not vacuous given
  `TYZThm11Integral`, since then a sign choice exists (`ellOf_sq`).

**Not reducible here.** The statement relates central `L`-values mod 2 to class numbers. That is TYZ's
Waldspurger-formula content (TYZ Theorem 2.1, from Yuan–Zhang–Zhang), and it does not follow from the
definitions or from `Contrib/PSide`'s coefficient results, which concern `a_p` only. One small part is
reducible, and it is proved: the value `g(3) = 1` that the `m = 3` instance needs (`gCl_three`).

## 3. What remains, and integration

* **The TYZ L-leaves are now two**, `TYZThm11Integral` and `TYZLemma29Mod2` (or the alternative
  `TYZThm11Mod2`, via `lemma29Mod2_of_thm11Mod2`). Both are published, refereed, over genuine definitions, and
  numerically confirmed on 30 inputs. The decomposition of `TYZThm35ReadingA` is:
  `TYZThm11Integral`, `TYZLemma29Mod2`, `TYZGenusPackage` (`tyzThm35ReadingA_of_three_leaves`).
* **Human checks** (source text needed):
  1. TYZ L338–353, the normalisation `2^{2k−2−a}` and `Ω_{n,∞}` (pinned numerically here, but not read);
  2. TYZ L371–380, that Theorem 1.1 includes `n = 1`;
  3. TYZ L1062–1066 at `m = 3`, the `w_K` factor (harmless mod 2);
  4. whether TYZ's proof of Lemma 2.9 uses L1082 (immaterial for the decomposition, §2.2).
* **Integration.** `scratch/tyz-lcal/TYZLcal.lean` can be copied verbatim to a new module, e.g.
  `ZInQKernel/Contrib/TYZLcal/Basic.lean`, dropping the trailing `#print axioms` lines. It adds no new
  hypotheses and edits no pinned file. It only needs the import of
  `Mathlib.NumberTheory.NumberField.Cyclotomic.PID`.
* **Not done.** The Tunnell alternative for `TYZThm11Integral` (§2.1 remark) was not pursued. Neither was any
  Lean statement of Tunnell's formula.
