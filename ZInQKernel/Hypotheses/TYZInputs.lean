import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import ZInQKernel.Hypotheses.CR3Literature

/-!
# The Tian–Yuan–Zhang inputs of Proposition N

`TYZInputs` is the hypothesis from which `RouteK/PropN.lean` proves `Literature.TYZRow5b`
(Proposition N of `docs/research/nt-tyz.md` §4). It encodes the results I1–I5 and I7 of
Tian–Yuan–Zhang that Proposition N uses (nt-tyz §4.2), as printed in arXiv:1411.4728v1 (cited as
TYZ; line numbers `Lnnnn` refer to its source `Period7.tex`). The journal version (Asian J. Math. 21
(2017)) was not compared here; the locator audit `docs/research/locators.md` (AI agents, 2026-11-12)
read it and reports the convolution as Lemma 2.9 there too, and arXiv Theorem 1.2 (not used here)
as journal Theorem 1.4. It is a conjunction of consequences of statements printed in TYZ,
together with two standard facts that TYZ use without printing: Hecke's continuation of
`L(C_n, s)` (CM; the I7 conjunct) and F4, that `[i]` is defined over `ℚ(i)` (used only to justify
the type of `GenusData.β`). The parts are:

* an integer function `L` (TYZ's `𝓛`, §1, L338–345) with `L 1 = 1` (L1082) and Lemma 2.9 with
  Proposition 2.3 modulo 2 (L1062–1066, L580–586): `LemmaTwoEight L` (I2; the name is historical:
  earlier notes miscounted the lemma as 2.8, corrected 2026-11-12, see `LemmaTwoEight`);
* the defining property of `𝓛` for `n ≡ 5 (mod 8)` (L338–345), with Hecke's continuation of
  `L(C_n, s)` (CM; TYZ assume it when they write `ord_{s=1}` and do not prove it):
  `L n ≠ 0 → ∃ F, IsLContinuation … F ∧ analyticOrderAt F 1 ≤ 1` (I7);
* for each squarefree `n ≡ 5 (mod 8)`, the genus-point data `GenusData L n` over a `ℤ[i]`-module
  `M`, in the intended model the `ℤ[i]`-span in `A(ℍ'_n)` of `A[(1+i)³]` and the genus points
  `Z(e)` (`e ∣ n`, `e ≡ 5, 7 (mod 8)`): the recursion I1 (§3.1, L1325–1329) with the `ε`-classes of
  Theorem 3.3 (L1299–1309), the torsion statements I3 (Theorem 3.5, L1353–1354) and I4 (τ,
  L1384–1402; Lemmas 3.16, 3.18, L2182–2232), the action `β` of a lifting of `β₁` and I5
  (Lemma 3.21, L2504–2517; "β acts on ℚ(i) trivially", L2581).

Each field is a consequence of a printed TYZ statement (`docs/research/pn-design.md` §2). Two
points are not literally printed, and both are settled:

* the typing of `β : M →+ M`. Since `M` is existential, it is taken to be the span above, and
  `β` is the restriction to `M` of one lifting `β' ∈ Gal(ℚ̄/ℚ)` of `β₁`. That `β'` maps this `M`
  into itself follows from printed statements and F4 (`rv-pn-encoding` F2): `β'` fixes
  `A(ℚ(i)) = A[(1+i)³]` (L2581, L2184), Lemma 3.21(1),(4) gives `β' Z(e) ∈ −Z(e) + A[(1+i)³]` for
  any lifting (L2500), and `β'` commutes with `[i]` because `[i]` is defined over `ℚ(i)` (F4). So
  F5, that `ℍ'_n/ℚ` is Galois, is not needed. (F5 is the alternative route: it would make `β'`
  act on all of `A(ℍ'_n)`. TYZ use it without printing it (L2594–2595); it follows from TYZ
  Proposition 3.2(1) (L1255–1256) together with Cox, *Primes of the form x² + ny²*, Lemma 9.3
  (ring class fields are generalized dihedral over `ℚ`).) Neither F4 nor F5 is a Lean field;
* T1: the constant `P_χ = ε 2^{h₂(n)} 𝓛(d₁) 𝒫(d₀)` of TYZ Theorem 3.3 (used by `eps_53`,
  `eps_pm1` and `recursion`, through I3) is asserted after "computations similar to" those of
  Theorem 2.1, which TYZ do not print (L2014–2015). `docs/research/tyz-t1.md` closes this:
  Theorem 3.3 holds as printed. I3 needs the constant not to depend on `d₁` for fixed `d₀`; this
  is written out from TYZ's Theorem A.9 (L3062–3077; no local factor depends on `χ`, `d₀` or `d₁`
  except through the two L-values), and checked exactly on 30 values of `n ≡ 5 (mod 8)`, 73
  contributing pairs `(d₀, d₁)`, from Heegner points on `X₀(32)`. What remains external is
  Theorem A.9 itself: the Yuan–Zhang–Zhang Gross–Zagier formula, made explicit by TYZ, who omit
  the deduction (L3079).

Reviews: `docs/research/rv-tyz-inputs.md` re-derived TYZ's proofs of I1–I7 and found that they
hold, with T1 as the one residual doubt, since closed by `docs/research/tyz-t1.md`;
`docs/research/pn-design.md` (§1, §2, §5) compares each field with the source;
`docs/research/rv-pn-encoding.md` reviewed the Lean encoding (no blocker; its should-fix items
are applied here). `Witness.genusData_nonempty` (`RouteK/PropN.lean`) shows that the fields of
`GenusData` are jointly satisfiable when `L n ≠ 0`, and `Witness.genusData_nonempty_iff_parities`
that for `L n = 0` they are satisfiable exactly when the conclusion of Proposition N's final step
holds.
-/

noncomputable section

namespace ZInQ.PropN

open ZInQ.Literature ZInQ.RouteK.Rank5b

/-! ### TYZ's `g` on natural numbers, and `i` -/

/-- TYZ's genus class number `g(e) = #(2 Cl(ℚ(√−e)))` (L363) as a function on `ℕ` (`gCl` needs
`e ≠ 0`; the value at `0` is never used). -/
def gNat (e : ℕ) : ℕ := if h : e = 0 then 0 else haveI : NeZero e := ⟨h⟩; gCl e

/-- The Gaussian integer `i`. -/
def gi : GaussianInt := ⟨0, 1⟩

/-- `(1 + i)³ = 2i(1 + i) = −2 + 2i`; its associate `2 + 2i = −i(1+i)³` generates the kernel of
`y ↦ τ(y/2)`. -/
def twoTwoI : GaussianInt := ⟨2, 2⟩

/-! ### The inputs -/

/-- **Lemma 2.9 with Proposition 2.3, modulo 2** (TYZ L1062–1066, L580–586; §2 assumes `n ≡ 1, 2, 3`
positive squarefree, L499). The name `LemmaTwoEight` is historical: this encodes TYZ's convolution
**Lemma 2.9** (numbered so in arXiv v1, by the shared §2 counter of `Period7.tex`, and in the journal
text per the locator audit `docs/research/locators.md`); TYZ's Lemma 2.8 (label `lem2.6`, L1009) is
the symmetry lemma `P(d₁, d₂) = P(d₂, d₁)`. Corrected 2026-11-12 (loc-adopt); the statement is
unchanged. The encoded content: `Σ ε(d₁, d₂) 𝓛(d₁)𝓛(d₂) ≡ Q(m) ≡ g(m) (mod 2)` over the non-ordered
decompositions `m = d₁d₂` with `d₂ ≡ 1 (mod 8)`. (At `m = 3`, Lemma 2.9 and Theorem 2.1 differ by
the odd factor `w_K = 3` (`rv-nt-tyz` B1); the congruence holds under either, and `𝓛(3) = ±1` by
direct computation.)

* `m ≡ 1`: both factors are `≡ 1`; each unordered pair `{d, m/d}` (`d ≠ m/d` as `m > 1` is
  squarefree) is counted once, through its member with `d² < m`.
* `m ≡ 3`: `d₂ ≡ 1` and `d₁ ≡ 3` are distinguished by their classes; the sum is over `d₂ = d`.

The signs `ε = ±1` vanish modulo 2. Restricted to `m > 1` (for `m = 3` automatic). -/
def LemmaTwoEight (L : ℕ → ℤ) : Prop :=
  (∀ m : ℕ, Squarefree m → 1 < m → m % 8 = 1 →
    (((∑ d ∈ m.divisors.filter (fun d => d % 8 = 1 ∧ d * d < m), L d * L (m / d) : ℤ) :
      ZMod 2) = (gNat m : ZMod 2))) ∧
  (∀ m : ℕ, Squarefree m → m % 8 = 3 →
    (((∑ d ∈ m.divisors.filter (fun d => d % 8 = 1), L (m / d) * L d : ℤ) : ZMod 2) =
      (gNat m : ZMod 2)))

/-- **The genus-point data of TYZ §3 for one squarefree `n ≡ 5 (mod 8)`.** In the intended model
`M` is the `ℤ[i]`-span, inside the `ℤ[i]`-module `A(ℍ'_n)` (L1324), of `A[(1+i)³]` and the genus
points `Z(e)` for `e ∣ n`, `e ≡ 5, 7 (mod 8)`; `Z e` is the genus point `Z(e)` and `P e` the point
`P(e)` (L1318–1329). These lie in `A(ℍ'_n)`: for `e ≡ 5`, `H'_e` is a factor of `ℍ'_n` (L1321); for
`e ≡ 7`, `Z(e)` is defined over `L_e ⊂ L_n(i) ⊂ ℍ'_n` (L2558). `τ y` is `τ(y/2)` (L1384–1402), and
`β` is the restriction to `M` of one lifting `β' ∈ Gal(ℚ̄/ℚ)` of `β₁ = r_∞(−1) r₂(−2)`
(L2496–2500), which maps `M` into itself (see the field `β`). -/
structure GenusData (L : ℕ → ℤ) (n : ℕ) where
  /-- The `ℤ[i]`-span in `A(ℍ'_n)` of `A[(1+i)³]` and the `Z(e)`, `e ∣ n`, `e ≡ 5, 7`; it contains
  every `P(d)` by the recursion, since the coefficients `ε 𝓛` lie in `ℤ[i]`. -/
  M : Type
  [addCommGroup : AddCommGroup M]
  [module : Module GaussianInt M]
  /-- `Z(e)`, the genus point (L1318). -/
  Z : ℕ → M
  /-- `P(e)` (L1325–1329). -/
  P : ℕ → M
  /-- `ε(d₀, d₁) ∈ μ₄` of Theorem 3.3 (L1308). -/
  ε : ℕ → ℕ → GaussianInt
  /-- Theorem 3.3: `ε(d₀, d₁) = ±i` if `(d₀, d₁) ≡ (5, 3) (mod 8)` (L1308; TYZ also prove the
  class, Lemma `multiples1`, L1919–1921, and use the same uniformity in the proof of
  Proposition 3.4, L2105–2108). `lemmaN2` needs this field: if the `(5, 3)` values did not lie in
  one class modulo `2ℤ[i]`, Lemma N2 would fail. -/
  eps_53 : ∀ d₀ d₁ : ℕ, d₀ * d₁ ∣ n → d₀ % 8 = 5 → d₁ % 8 = 3 → ε d₀ d₁ = gi ∨ ε d₀ d₁ = -gi
  /-- Theorem 3.3: `ε(d₀, d₁) = ±1` otherwise (the odd classes `(5,1)`, `(7,1)`, `(7,3)`). -/
  eps_pm1 : ∀ d₀ d₁ : ℕ, d₀ * d₁ ∣ n →
    (d₀ % 8 = 5 ∧ d₁ % 8 = 1 ∨ d₀ % 8 = 7 ∧ d₁ % 8 = 1 ∨ d₀ % 8 = 7 ∧ d₁ % 8 = 3) →
    ε d₀ d₁ = 1 ∨ ε d₀ d₁ = -1
  /-- **I1**, the recursion defining `P` (L1325–1329; `ε` as in Theorem 3.3, L1328; `𝓛(d₁) ∈ ℤ`,
  L1329), for every `d ∣ n` with `d ≡ 5, 7 (mod 8)`:
  `P(d) = Z(d) − Σ_{d = d₀d₁, d₁ ≡ 1, 3, d₁ > 1} ε(d₀, d₁) 𝓛(d₁) P(d₀)` (for odd `d ≡ 5, 7`, the
  classes `d₁ ≡ 1, 3` force `d₀ ≡ 5, 7`). -/
  recursion : ∀ d ∈ n.divisors, (d % 8 = 5 ∨ d % 8 = 7) →
    P d = Z d - ∑ d₁ ∈ d.divisors.filter (fun d₁ => 1 < d₁ ∧ (d₁ % 8 = 1 ∨ d₁ % 8 = 3)),
      (ε (d / d₁) d₁ * (L d₁ : GaussianInt)) • P (d / d₁)
  /-- **I3**, Theorem 3.5 (first assertion, L1354) with `𝒫(n) = 0` if `𝓛(n) = 0` (L1295):
  `P(n)` then vanishes in `A(ℍ'_n) ⊗ ℚ`, i.e. is torsion. -/
  torsion_of_zero : L n = 0 → IsOfFinAddOrder (P n)
  /-- `y ↦ τ(y/2)`, `ℤ[i] → A[(1+i)³] = A(ℚ(i)) ⊂ A(ℍ'_n)` (L1386–1399). -/
  τ : GaussianInt →+ M
  /-- `τ` is an isomorphism `ℂ/(1+i)ℤ[i] → A(ℂ)` (L1386): `τ(y/2) = 0 ↔ y ∈ 2(1+i)ℤ[i]`. -/
  τ_eq_zero : ∀ y, τ y = 0 ↔ twoTwoI ∣ y
  /-- **I4**, Lemma 3.18 (L2230–2232, `n` odd): `A(ℍ'_n)_tors = A[(1+i)³] = τ(½ℤ[i])`; hence
  `M_tors ⊂ A(ℍ'_n)_tors = A[(1+i)³]`, which `M` contains. -/
  tors_mem_range : ∀ x : M, IsOfFinAddOrder x → ∃ y, τ y = x
  /-- One lifting `β'` of `β₁`, restricted to `M` (additive, since `A` is defined over `ℚ`, L1391).
  It preserves `M`: `β'` fixes `A(ℚ(i)) = A[(1+i)³]` (L2581, L2184), Lemma 3.21(1),(4) (for any
  lifting, L2500) gives `β' Z(e) ∈ −Z(e) + A[(1+i)³]`, and `β'` commutes with `[i]` (F4: `[i]` is
  defined over `ℚ(i)`; standard, not printed in TYZ). F5 (`ℍ'_n/ℚ` Galois, which TYZ use at
  L2594–2595 without printing it, and which follows from Proposition 3.2(1), L1255–1256, with Cox,
  Lemma 9.3) would give the same typing on all of `A(ℍ'_n)` but is not needed. -/
  β : M →+ M
  /-- `β'` fixes `A[(1+i)³] = A(ℚ(i))` (Lemma 3.16, L2182–2185), since `β` acts trivially on
  `ℚ(i)` (L2581). -/
  β_τ : ∀ y, β (τ y) = τ y
  /-- **I5**, Lemma 3.21(1) (L2506–2507): `Z(e)^{β'+1} ∈ g(e) τ((1−i)/2) + ℤ τ(1)` for `e ≡ 5`. -/
  beta_five : ∀ e ∈ n.divisors, e % 8 = 5 →
    ∃ k : ℤ, β (Z e) + Z e = (gNat e : ℤ) • τ ⟨1, -1⟩ + k • τ 2
  /-- **I5**, Lemma 3.21(4) (L2514–2515): `Z(e)^{β'+1} = g(e) τ(1/2)` for `e ≡ 7`. Exact as TYZ
  print it, in their normalization of `τ` (L1398–1401); since `τ 1 = τ(1/2)` has order 4, this
  needs `gNat e` to be the integer `#2Cl`, not its parity. `finalStep` uses it only modulo
  `ℤ τ 2`. -/
  beta_seven : ∀ e ∈ n.divisors, e % 8 = 7 → β (Z e) + Z e = (gNat e : ℤ) • τ 1

attribute [instance] GenusData.addCommGroup GenusData.module

/-- **The TYZ inputs of Proposition N.** There is an integer function `L` (TYZ's `𝓛`, with a
choice of the sign of each value, L361; integer-valued on classes 1 and 3 by Theorem 1.1, L371–380,
L1329; on class 5 only whether `𝓛(n) = 0` matters, so a model may take values in `{0, 1}` there)
such that `L 1 = 1` (L1082), Lemma 2.9 with Proposition 2.3 holds modulo 2, `L n ≠ 0` gives
analytic rank at most one for `n ≡ 5 (mod 8)` (the definition of `𝓛`, L338–345, `𝓛(n) = 0` if
`ord_{s=1} > 1`, together with Hecke's continuation of `L(C_n, s)` (CM; assumed, not proved, in
TYZ); `E_n ≅ C_n` over `ℚ`), and every squarefree `n ≡ 5 (mod 8)` carries the genus-point data of
TYZ §3 (its field `β : M →+ M` uses F4, which TYZ do not print; see `GenusData.β`). -/
def TYZInputs : Prop :=
  ∃ L : ℕ → ℤ, L 1 = 1 ∧ LemmaTwoEight L ∧
    (∀ n : ℕ, n % 8 = 5 → Squarefree n → L n ≠ 0 →
      ∃ F : ℂ → ℂ, IsLContinuation (shortCurve (-(n : ℚ) ^ 2)) F ∧ analyticOrderAt F 1 ≤ 1) ∧
    (∀ n : ℕ, n % 8 = 5 → Squarefree n → Nonempty (GenusData L n))
end ZInQ.PropN
