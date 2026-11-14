# gz-statements: statement review of `FHNonvanishing` and `GrossZagierHeegner`

Status: research note (task gz-statements, 2026-11-13), branch `wip/gz-statements` (base fork main
83651ea9). New Lean files: `ZInQKernel/Contrib/GZStatements/{Weak,Level,Compat,Hensel}.lean`. Axiom
check: `scratch/gz-statements/Check.lean`, output `scratch/gz-statements/out_check_axioms.txt`.
Log: `scratch/gz-statements/log.md`. No existing file of the project was edited.

Marks: **VERIFIED** means read in a named source, computed, or compiled. **STANDARD** means a
published theorem with its reference. **SPECULATIVE** means an assessment. This host has no
network access and no copy of any paper cited here. **Every theorem number and every quotation
of the literature in this note is UNVERIFIED**: it is written from memory and must be checked
(§6).

---

## 0. Main result

**Neither leaf is stronger than the published theorem it cites, and neither is vacuous.** Each
is a consequence of its source, with the textbook facts that are folded in and named below. For
`FHNonvanishing` this holds provided Friedberg–Hoffstein's theorem has the generality listed in
§6 H1: every level, dihedral `π` allowed, arbitrary local data on a finite `S`. That generality
is recalled but UNVERIFIED. The restricted form needs it only for one CM newform of level `32 d²`
per `d`. Both
are stated over genuine definitions: Tau Ceti's `Newform`, the root number pinned by Tau Ceti's
proved functional equation, and Mathlib's `WeierstrassCurve.LFunction`, `Affine.Point` and
`jacobiSym`. No statement needs a repair. The gaps found are of two kinds:

- scope wider than the use: all levels, all newforms, every bound `B`, every elliptic curve;
- docstring precision: unverified theorem labels, and the meaning of `HeegnerHyp` for `D = 0`.

**Both leaves can be weakened to what the glue uses**, and the weakened forms still give
Theorem 1.1 (VERIFIED, compiled). The restricted Gross–Zagier leaf is also implied by
`GrossZagierCd`, and hence by the original premise `Literature.GrossZagier` (VERIFIED, compiled).
So it is never stronger than the premise it replaces.

### 0.1 Declarations proved

All in namespace `ZInQ.GZStatements`. `#print axioms` gives `[propext, Classical.choice,
Quot.sound]` for each of the 22 declarations below (VERIFIED, `out_check_axioms.txt`).

**The restricted leaves** (`Weak.lean`):

```lean
def FHNonvanishingCd : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d →
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2) (hχ : f.χ = 1),
    (∀ n : ℕ, n ≠ 0 → coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ)) →
    rootNumber f hχ = -1 →
    ∃ D : ℤ, D < -4 ∧ IsOddImagFundDisc D ∧ HeegnerHyp N D ∧
      ∀ G : ℂ → ℂ, IsEntireCont (twistCoeff f D) 2 G → G 1 ≠ 0

def GrossZagierHeegnerCd : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d →
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ)) →
    ∀ D : ℤ, IsOddImagFundDisc D → D < -4 → HeegnerHyp N D →
    ∀ F G : ℂ → ℂ, IsEntireCont (coeff f) 2 F → IsEntireCont (twistCoeff f D) 2 G →
      analyticOrderAt F 1 = 1 → G 1 ≠ 0 →
    ∀ (K : Type) [Field K] [DecidableEq K] [Algebra ℚ K], Module.finrank ℚ K = 2 →
      (∃ δ : K, δ ^ 2 = algebraMap ℚ K D) →
      ∃ y : ((shortCurve (-(d : ℚ) ^ 2))⁄K).Point, ¬IsOfFinAddOrder y ∧
        ∀ σ : K ≃ₐ[ℚ] K, IsOfFinAddOrder (Affine.Point.map σ.toAlgHom y - y)

def GrossZagierRankCd : Prop :=        -- the weakest form that closes the chain
  ∀ d : ℕ, d % 8 = 5 → Squarefree d →
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ)) →
    ∀ D : ℤ, IsOddImagFundDisc D → D < -4 → HeegnerHyp N D →
    ∀ F G : ℂ → ℂ, IsEntireCont (coeff f) 2 F → IsEntireCont (twistCoeff f D) 2 G →
      analyticOrderAt F 1 = 1 → G 1 ≠ 0 →
      ∃ P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point, ¬IsOfFinAddOrder P
```

**Weaker than the originals; still sufficient; no stronger than the premise** (`Weak.lean`):

```lean
theorem fhNonvanishingCd_of_fhNonvanishing : ZInQ.GZDecomp.FHNonvanishing → FHNonvanishingCd
theorem grossZagierHeegnerCd_of_grossZagierHeegner :
    ZInQ.GZDecomp.GrossZagierHeegner → GrossZagierHeegnerCd
theorem grossZagierRankCd_of_grossZagierHeegnerCd : GrossZagierHeegnerCd → GrossZagierRankCd
theorem grossZagierCd_of_fhNonvanishingCd_grossZagierRankCd :
    FHNonvanishingCd → GrossZagierRankCd → ZInQ.GZDecomp.GrossZagierCd
theorem grossZagierCd_of_fhNonvanishingCd_grossZagierHeegnerCd :
    FHNonvanishingCd → GrossZagierHeegnerCd → ZInQ.GZDecomp.GrossZagierCd
theorem frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd :
    ZInQ.SixContactMin → ZInQ.Literature.TYZThm35ReadingA → FHNonvanishingCd →
      GrossZagierHeegnerCd → ZInQ.FrozenTarget
theorem frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierRankCd :
    ZInQ.SixContactMin → ZInQ.Literature.TYZThm35ReadingA → FHNonvanishingCd →
      GrossZagierRankCd → ZInQ.FrozenTarget
theorem grossZagierRankCd_of_grossZagierCd : ZInQ.GZDecomp.GrossZagierCd → GrossZagierRankCd
theorem grossZagierHeegnerCd_of_grossZagierCd :
    ZInQ.GZDecomp.GrossZagierCd → GrossZagierHeegnerCd
theorem grossZagierHeegnerCd_of_grossZagier : ZInQ.Literature.GrossZagier → GrossZagierHeegnerCd
```

**The level and the Heegner hypothesis made explicit** (`Level.lean`):

```lean
theorem level_eq_of_coeff_cd {d : ℕ} (hd4 : d % 4 = 1) (hsq : Squarefree d) {N : ℕ} [NeZero N]
    (f : Newform N 2) (hχ : f.χ = 1)
    (hf : ∀ n : ℕ, n ≠ 0 → coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ)) :
    N = 32 * d ^ 2
theorem heegnerHyp_iff_of_coeff_cd … (D : ℤ) : HeegnerHyp N D ↔ HeegnerHyp (32 * d ^ 2) D
theorem heegnerHyp_32_iff {d : ℕ} (hd : d ≠ 0) (D : ℤ) :
    HeegnerHyp (32 * d ^ 2) D ↔
      jacobiSym 2 D.natAbs = 1 ∧ ∀ p : ℕ, p.Prime → p ∣ d → jacobiSym (p : ℤ) D.natAbs = 1
```

`Level.lean` also contains the helpers `LFunction_cd_eq_heckeCoeff` and
`exists_newform_level32`. The 22 declarations of the axiom check are the ones listed in §0.1.

**The definitions `HeegnerHyp` and `chiD`, and the root-number compatibility** (`Compat.lean`):

```lean
theorem jacobiSym_neg_level {N : ℕ} (hN : N ≠ 0) {D : ℤ} (hD : IsOddImagFundDisc D)
    (hH : HeegnerHyp N D) : jacobiSym (-(N : ℤ)) D.natAbs = -1
theorem coprime_of_heegnerHyp {N : ℕ} {D : ℤ} (hD0 : D ≠ 0) (hH : HeegnerHyp N D) :
    Nat.Coprime D.natAbs N
theorem jacobiSym_two_eq_one_iff {D : ℤ} (hD : IsOddImagFundDisc D) :
    jacobiSym 2 D.natAbs = 1 ↔ D % 8 = 1
theorem jacobiSym_prime_eq_legendreSym {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {D : ℤ}
    (hD : IsOddImagFundDisc D) : jacobiSym (p : ℤ) D.natAbs = legendreSym p D
theorem heegnerHyp_iff_split {N : ℕ} {D : ℤ} (hD : IsOddImagFundDisc D) :
    HeegnerHyp N D ↔ (2 ∣ N → D % 8 = 1) ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ N → (D : ZMod p) ≠ 0 ∧ IsSquare (D : ZMod p)
theorem chiD_mul (D : ℤ) (m n : ℕ) : chiD D (m * n) = chiD D m * chiD D n
theorem chiD_prime {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {D : ℤ} (hD : IsOddImagFundDisc D) :
    chiD D p = (legendreSym p D : ℂ)
theorem chiD_two {D : ℤ} (hD : IsOddImagFundDisc D) :
    chiD D 2 = if D % 8 = 1 then 1 else -1
```

**The Heegner hypothesis in Gross–Zagier's form** (`Hensel.lean`: Hensel lifting at odd `p` and
at 2, then CRT):

```lean
theorem exists_sq_mod_four_mul_of_heegnerHyp {N : ℕ} (hN : N ≠ 0) {D : ℤ}
    (hD : IsOddImagFundDisc D) (hH : HeegnerHyp N D) : ∃ β : ℤ, (4 * N : ℤ) ∣ D - β ^ 2
```

`#print axioms` (VERIFIED). The output of `scratch/gz-statements/Check.lean` gives, for each of
the 22 names above:

```
'ZInQ.GZStatements.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry` or error (VERIFIED: `grep -ci "sorry\|error"` returns 0).

### 0.2 Verdict table

| Leaf | Published source (UNVERIFIED locators) | Stronger than the source? | Vacuous? | Weakest form that closes the chain |
| --- | --- | --- | --- | --- |
| `FHNonvanishing` | Friedberg–Hoffstein, Ann. of Math. 142 (1995) 385-423, central-value theorem (gz-decomp cites "Thm B") | no, if FH's theorem allows every level, dihedral `π` and arbitrary local data at a finite `S` (§6 H1) | no | `FHNonvanishingCd` (one family; `D < −4` in place of `∀ B`) |
| `GrossZagierHeegner` | Gross–Zagier, Invent. Math. 84 (1986) 225-320, Thm I.6.3 and Ch. V; Gross 1984 for the conjugation relation | no; folded in: modular parametrization (Shimura 1971, plus Faltings 1983 for general `E`), nondegeneracy of `ĥ` | no | `GrossZagierRankCd`; recommended: `GrossZagierHeegnerCd` |

**Proposal to the owner** (a statement change; not applied). In the headline, replace the
premises `GZDecomp.FHNonvanishing` and `GZDecomp.GrossZagierHeegner` by `FHNonvanishingCd` and
`GrossZagierHeegnerCd`. The theorem
`frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd` already
compiles. The human check of the literature then shrinks to a single level, `N = 32 d²`, and a
single CM newform per `d`.

---

## 1. How the glue uses the two leaves

Traced in `ZInQKernel/Contrib/GZDecomp/Decomp.lean` (VERIFIED by reading).
`grossZagierCd_of_leaves` is the only consumer of the leaves.
`grossZagierCd_of_leaves'`, `frozenTarget_of_…_gzLeaves` and atkin-li's
`frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner` only pass the
leaves on to it. Each leaf is applied exactly once.

| Leaf | Call | Arguments actually supplied |
| --- | --- | --- |
| `FHNonvanishing` | `hL2 N f hχ hw 4` | `f` is the newform of `C_d` from `modular_cd` (`d ≡ 5 mod 8` squarefree); `hw` comes from G3; `B = 4` |
| `GrossZagierHeegner` | `hL3 _ N f hχ hf D … K hK2 ⟨δ, _⟩` | `E = C_d`; the same `N, f`; `D` from L2; `F` = the continuation of `L(C_d, s)`; `G` from G6; `K = AdjoinRoot (X² − D)` |

What the chain uses from each conclusion:

- From L2: `D < −4` (passed to L3), `IsOddImagFundDisc D` (L3, and `D ≠ 0` for G5, G6),
  `HeegnerHyp N D` (L3), and `G 1 ≠ 0` for one `G`.
- From L3: a `y` of infinite order with `σy − y` torsion, which G4 turns into a rational point.
  So the weakest L3 that closes the chain asks only for that rational point: `GrossZagierRankCd`.

`FHNonvanishingCd` is therefore the weakest L2 compatible with L3's hypotheses. One could also
replace its hypothesis `rootNumber f hχ = −1` by "`L(f, s)` has a simple zero at 1", which is
stronger by G3, so that version of the leaf is weaker. That form is not the shape of FH's
theorem, so it is not proposed.

The level is pinned (`level_eq_of_coeff_cd`, VERIFIED). Any newform of weight 2 and trivial
character with `aₙ(f) = aₙ(C_d)` has level `N = 32 d²`. The proof uses atkin-li's strong
multiplicity one across levels and the level-`32 d²` newform of gz-theta and atkin-li. So in the
restricted leaves, `HeegnerHyp N D` means:

- `D ≡ 1 (mod 8)` (`heegnerHyp_32_iff`, `jacobiSym_two_eq_one_iff`);
- `D` is a nonzero square modulo every prime `p ∣ d` (`heegnerHyp_iff_split`).

---

## 2. `FHNonvanishing` against Friedberg–Hoffstein 1995

### 2.1 The Lean statement (verbatim, `Contrib/GZDecomp/Decomp.lean`)

```lean
def FHNonvanishing : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2) (hχ : f.χ = 1), rootNumber f hχ = -1 →
    ∀ B : ℕ, ∃ D : ℤ, D < -(B : ℤ) ∧ IsOddImagFundDisc D ∧ HeegnerHyp N D ∧
      ∀ G : ℂ → ℂ, IsEntireCont (twistCoeff f D) 2 G → G 1 ≠ 0
```

### 2.2 The published statement (from memory; UNVERIFIED in every detail)

S. Friedberg, J. Hoffstein, *Nonvanishing theorems for automorphic L-functions on GL(2)*, Ann. of
Math. (2) 142 (1995), no. 2, 385-423. As I recall it, the paper has two main theorems, labelled A
and B: one for central values `L(½, π ⊗ χ)` and one for central derivatives `L′(½, π ⊗ χ)`. I do
not reliably remember which label is which. gz-decomp cites "Theorem B" for the central-value
statement, which may be the wrong label. The central-value statement, in the form needed:

> *Let `π` be a cuspidal automorphic representation of `GL₂(𝔸_F)`, `F` a number field. Let `S` be
> a finite set of places containing the archimedean places and those where `π` ramifies [possibly
> also the places above 2], and for each `v ∈ S` let `χ_v` be a quadratic or trivial character of
> `F_v^×`. Suppose there is a quadratic idele class character `χ₀` with `(χ₀)_v = χ_v` for
> `v ∈ S` and `ε(½, π ⊗ χ₀) = 1`. Then there are infinitely many quadratic idele class characters
> `χ` with `χ_v` as prescribed at every `v ∈ S` such that `L(½, π ⊗ χ) ≠ 0`.*

Whether FH assume a trivial central character is not remembered. The Lean leaf only applies to
trivial nebentypus, so either form suffices. Earlier results with possible restrictions on the
level: Bump–Friedberg–Hoffstein, Invent. Math. 102 (1990) 543-618 (values and derivatives);
Waldspurger, J. Math. Pures Appl. 60 (1981) and Compositio Math. 54 (1985) (UNVERIFIED). Murty–Murty,
Ann. of Math. 133 (1991), is the derivative case and does not supply L2 (agreeing with
rv-cr3-trust §2.2). The leaf does not rely on S. Zhang or Yuan–Zhang–Zhang.

### 2.3 Clause-by-clause comparison

Take `F = ℚ`, `π = π_f`, `S = {∞, 2} ∪ {p ∣ N}`, `χ_∞ = sgn`, and `χ_v = 1` for `v ∣ 2N`.

| Lean clause | FH counterpart | Match |
| --- | --- | --- |
| `∀ N [NeZero N] (f : Newform N 2)` | `π` cuspidal on `GL₂(𝔸_ℚ)` | `π_f` is cuspidal (STANDARD). `Newform` is genuine: eigen for all `T_n` with `(n, N) = 1`, nonzero, Petersson-new, `a₁ = 1` (VERIFIED, TC `Newforms/Newform.lean:85-111`). **Range**: every level `N`, every newform, CM ones included; FH's range must contain this (§6 H1(a), (b)). |
| `hχ : f.χ = 1` | central character of `π` | trivial; a sub-case |
| `rootNumber f hχ = −1` | compatibility hypothesis `ε(½, π ⊗ χ₀) = 1` | `rootNumber = i²·frickeSign` is the sign of TC's proved `Λ_N(2 − s) = rootNumber · Λ_N(s)` with `Λ_N = N^{s/2}(2π)^{−s}Γ(s)L(f, s)` (VERIFIED, `LFunction/Sign.lean:186`). Since `Λ_N ≢ 0` it is the classical `ε(f) = ε(½, π_f)`, whatever the normalization of the Fricke operator. For `(D, N) = 1`, `ε(f ⊗ χ_D) = ε(f) χ_D(−N)` (STANDARD: Atkin–Li 1978; Iwaniec–Kowalski Prop. 14.20, UNVERIFIED number). Under the leaf's hypotheses `χ_D(−N) = −1` (VERIFIED: `jacobiSym_neg_level`) and `(D, N) = 1` (VERIFIED: `coprime_of_heegnerHyp`), so `ε(f ⊗ χ_D) = +1` for every admissible `D`. This is FH's hypothesis, for every `χ₀` with the prescribed data. |
| `∀ B, ∃ D, D < −B` | "infinitely many `χ`" | Quadratic characters of `ℚ` correspond bijectively to fundamental discriminants. `χ_∞ = sgn` gives `D < 0`, and infinitely many negative `D` are unbounded below. **Stronger than needed**: the glue uses `B = 4`. |
| `IsOddImagFundDisc D` (`D < 0`, `D % 4 = 1`, squarefree) | `χ_∞ = sgn`; `χ_2` unramified | `χ_2 = 1` makes `χ` unramified at 2, so `D` is odd, hence `≡ 1 (mod 4)` and squarefree. `%` is `Int.emod` (gz-decomp §5 item 9, VERIFIED there). Needs `2 ∈ S` even when `2 ∤ N`; FH allow any finite `S` (§6 H1(c)). |
| `HeegnerHyp N D` | `χ_p = 1` for `p ∣ N` | VERIFIED equivalent to the splitting conditions (`heegnerHyp_iff_split`): `D ≡ 1 (mod 8)` if `2 ∣ N`, and `D` a nonzero square mod each odd `p ∣ N`. These are exactly the conditions for `χ_{D,p}` to be trivial (STANDARD). |
| `∀ G, IsEntireCont (twistCoeff f D) 2 G → G 1 ≠ 0` | `L(½, π ⊗ χ_D) ≠ 0` | `twistCoeff f D n = aₙ(f) chiD D n`. `chiD D` is the Kronecker character of `ℚ(√D)`: completely multiplicative (`chiD_mul`), equal to `(D/p)` at odd `p` (`chiD_prime`) and to `±1` at 2 according to `D mod 8` (`chiD_two`) (all VERIFIED). For `(D, N) = 1` the Dirichlet series is the full finite `L(f ⊗ χ_D, s) = L(s − ½, π_f ⊗ χ_D)`: the factor at `p ∣ D` is `1 = L_p(π_p ⊗ χ_p)`; at `p ∣ N` it is `L_p(π_p)`, since `χ_p = 1` (STANDARD). Centre: `s = 1` ↔ `½`. `G` exists (G6, proved) and is unique (`IsEntireCont.eq`), so `∀ G` is not vacuous. If FH state the partial `L^S`, the missing Euler factors are finite and nonzero at the centre (roots of absolute value `√p` or `1`), so `L^S(½) ≠ 0 ⇔ L(½) ≠ 0`. |

**Conclusion.** `FHNonvanishing` is FH's central-value theorem applied to `π_f` with the data
above, together with the textbook twisted root number. It is not stronger, **provided FH's
theorem has no restriction excluding the level, dihedral `π`, or this choice of local data**
(§6 H1). It is not vacuous: its hypotheses are met by the newform of `C_5` (level 800; root
number `−1`, since `C_5` has analytic rank 1, rv-cr3-trust §2.1).

### 2.4 Gaps and proposed fixes (not applied)

**FH-1. Scope wider than the use.**
- *Gap.* The leaf covers every level and every newform with root number `−1`. Its truth then
  rests on the full generality of FH's theorem. The glue needs one CM newform of level `32 d²`
  per `d ≡ 5 (mod 8)`.
- *Fix.* Use `ZInQ.GZStatements.FHNonvanishingCd` (text in §0.1) in its place. It is implied by
  the leaf (`fhNonvanishingCd_of_fhNonvanishing`) and suffices (§0.1).

**FH-2. `∀ B` is not used.**
- *Gap.* Only `B = 4` is used, to exclude `D = −3`.
- *Fix.* Included in FH-1: the restricted leaf asks for `D < −4`, which only needs one `D ≠ −3`
  among FH's infinitely many.

**FH-3. Docstring precision.** The docstring of `FHNonvanishing` says "Theorem B (UNVERIFIED
number)". Proposed new docstring (for the restricted leaf, or for the original if it is kept):

```
/-- **(L2) Friedberg–Hoffstein: nonvanishing of central twisted values with prescribed local
components.** Let `f` be a newform of weight 2, level `N`, trivial nebentypus and root number
`−1` [restricted form: the newform of `C_d`, `d ≡ 5 mod 8` squarefree; its level is `32 d²`,
`level_eq_of_coeff_cd`]. Then there is an odd imaginary fundamental discriminant `D < −4` such
that every prime `p ∣ N` splits in `ℚ(√D)` and `L(f ⊗ χ_D, 1) ≠ 0`, where
`L(f ⊗ χ_D, s) = ∑ aₙ(f) χ_D(n) n^{−s}` is continued to `ℂ`.

Source: S. Friedberg, J. Hoffstein, Ann. of Math. 142 (1995), 385-423, the main theorem on
central values `L(½, π ⊗ χ)` (label A or B: UNVERIFIED), applied with `π = π_f`,
`S = {∞, 2} ∪ {p ∣ N}`, `χ_∞ = sgn`, `χ_v = 1` for `v ∣ 2N`. Folded in (textbook):
`ε(f ⊗ χ_D) = ε(f) χ_D(−N)` for `(D, N) = 1` (Atkin–Li, Invent. Math. 48 (1978)); here
`χ_D(−N) = −1` (`GZStatements.jacobiSym_neg_level`), so the twists have root number `+1`, which is
FH's compatibility hypothesis. The `π_f` used is dihedral (CM by `ℚ(i)`); FH's theorem is
believed to cover dihedral `π` (UNVERIFIED). -/
```

**FH-4. `HeegnerHyp` alone does not mean "split" when `D = 0`.**
- *Gap.* `jacobiSym p 0 = 1`, so `HeegnerHyp N 0` holds. The leaf always pairs it with
  `IsOddImagFundDisc D`, which excludes this, so there is **no defect in the leaf**.
- *Fix* (docstring only). Proposed new docstring for `GZDecomp.HeegnerHyp`:

```
/-- **Heegner hypothesis**: `(p / |D|) = 1` for every prime `p ∣ N`. For an odd imaginary
fundamental discriminant `D` this is "every `p ∣ N` splits in `ℚ(√D)`"
(`GZStatements.heegnerHyp_iff_split`: `D ≡ 1 mod 8` if `2 ∣ N`, `D` a nonzero square mod each odd
`p ∣ N`). For `D = 0` it holds trivially (`jacobiSym p 0 = 1`); use it only together with
`IsOddImagFundDisc D`. -/
```

---

## 3. `GrossZagierHeegner` against Gross–Zagier 1986

### 3.1 The Lean statement (verbatim)

```lean
def GrossZagierHeegner : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) →
    ∀ D : ℤ, IsOddImagFundDisc D → D < -4 → HeegnerHyp N D →
    ∀ F G : ℂ → ℂ, IsEntireCont (coeff f) 2 F → IsEntireCont (twistCoeff f D) 2 G →
      analyticOrderAt F 1 = 1 → G 1 ≠ 0 →
    ∀ (K : Type) [Field K] [DecidableEq K] [Algebra ℚ K], Module.finrank ℚ K = 2 →
      (∃ δ : K, δ ^ 2 = algebraMap ℚ K D) →
      ∃ y : (E⁄K).Point, ¬IsOfFinAddOrder y ∧
        ∀ σ : K ≃ₐ[ℚ] K, IsOfFinAddOrder (Affine.Point.map σ.toAlgHom y - y)
```

### 3.2 The published statements (from memory; UNVERIFIED in every detail)

B. Gross, D. Zagier, *Heegner points and derivatives of L-series*, Invent. Math. 84 (1986),
225-320.

- **Standing hypotheses** (Introduction / Ch. I; UNVERIFIED). `N ≥ 1`, and `D < 0` a fundamental
  discriminant with `D ≡ β² (mod 4N)`. I do not remember whether the paper also assumes `D` odd,
  `(D, 2N) = 1`, or `D ≠ −3, −4` (`u = #𝒪_K^×/2 = 1`). The Lean hypotheses imply each of these
  (§3.3). I believe `N` is not assumed squarefree.
- **Thm I.6.3** (UNVERIFIED number). For a newform `f ∈ S₂(Γ₀(N))` and a class-group character
  `χ` of `K = ℚ(√D)`:
  `L′(f, χ, 1) = (8π²(f, f) / (h u² √|D|)) · ĥ(c_{χ,f})`.
  For `χ = 1`, `L(f, 1, s) = L(f, s) L(f ⊗ χ_D, s)`.
- **Ch. V, Thm 2.1 and corollaries** (UNVERIFIED numbers). For `E/ℚ` with a modular
  parametrization `φ : X₀(N) → E` and `y_K = Tr_{H/K} φ(x₁) ∈ E(K)`,
  `L′(E/K, 1) = c · ĥ(y_K)` with an explicit `c ≠ 0`. Hence `y_K` has infinite order iff
  `L′(E/K, 1) ≠ 0`.
- **Conjugation.** `ȳ_K = −ε · y_K` modulo torsion, where `ε` is the sign of the functional
  equation of `L(E, s)`. Source: Gross, *Heegner points on X₀(N)*, in *Modular forms* (Durham
  1983), Ellis Horwood 1984, §5 (UNVERIFIED), restated in GZ Ch. V. Consequently, if `ε = −1`
  then `y_K + ȳ_K ≡ 2y_K` lies in `E(ℚ)` and `rank E(ℚ) ≥ 1`.

The leaf does not rely on S. Zhang (Ann. of Math. 153 (2001)) or Yuan–Zhang–Zhang (Ann. of Math.
Studies 184, 2013). Those generalize GZ to weaker Heegner conditions and totally real fields.
L2 supplies a `D` satisfying the full classical Heegner hypothesis, so GZ 1986 suffices.

### 3.3 Clause-by-clause comparison

| Lean clause | GZ counterpart | Match |
| --- | --- | --- |
| `∀ E [IsElliptic] N f, f.χ = 1, ∀ n ≠ 0, aₙ(f) = aₙ(E)` | `E/ℚ` with `φ : X₀(N) → E`, `f` its newform | `E.LFunction` is Mathlib's Euler product over all primes, with local factors from the **minimal** model (good, split or nonsplit multiplicative, additive) (VERIFIED, `Mathlib/AlgebraicGeometry/EllipticCurve/LFunction.lean:41-81`), so `aₙ(E)` is genuine. Folded in: `φ` exists. `E ∼ E_f` by Faltings' isogeny theorem (Invent. Math. 73 (1983), Korollar 2), and `E_f` is a quotient of `J₀(N)` (Shimura 1971, Thm 7.14-7.15). Both UNVERIFIED numbers, STANDARD content. For `C_d`, which has CM by `ℤ[i]`, Shimura's result that CM curves over `ℚ` are quotients of `J₀(N)` (Nagoya Math. J. 43 (1971), UNVERIFIED) avoids Faltings. **Range**: every `E`; the use is `C_d` only. |
| `IsOddImagFundDisc D`, `D < −4` | `D < 0` fundamental; possibly `D` odd, `D ≠ −3, −4` | `D` is odd, `≤ −7` and fundamental: this implies every candidate standing hypothesis |
| `HeegnerHyp N D` | `D ≡ β² (mod 4N)` | `HeegnerHyp` is the splitting condition (VERIFIED, `heegnerHyp_iff_split`). For odd `D` it implies GZ's form `D ≡ β² (mod 4N)` (VERIFIED, compiled: `exists_sq_mod_four_mul_of_heegnerHyp`, by Hensel at odd `p^k ∥ N` and at `2` with `D ≡ 1 mod 8`, then CRT). Numerically also 30 pairs `(N, D)`, 0 failures (VERIFIED, `out_check_heegner.txt`). It also gives `(D, N) = 1` (VERIFIED, `coprime_of_heegnerHyp`). |
| `IsEntireCont (coeff f) 2 F`, `analyticOrderAt F 1 = 1` | `ord_{s=1} L(E, s) = 1` | `F` is the unique entire continuation of `L(f, s) = L(E, s)`. `analyticOrderAt` (Mathlib, `ℕ∞`) equal to 1 means a simple zero. The root number is then `−1` (G3, proved: `signOfSimpleZero`). |
| `IsEntireCont (twistCoeff f D) 2 G`, `G 1 ≠ 0` | `L(E^D, 1) ≠ 0` | For `(D, N) = 1`, `∑ aₙ χ_D(n) n^{−s} = L(f ⊗ χ_D, s) = L(E^D, s)` (STANDARD; `chiD` = Kronecker, VERIFIED §2.3). Then `L(E/K, s) = L(E, s) L(E^D, s)` (STANDARD), so `L′(E/K, 1) = L′(E, 1) L(E^D, 1) ≠ 0`. |
| `∀ K, finrank ℚ K = 2, ∃ δ, δ² = D` | `K = ℚ(√D)` | Any such `K` is `≅ ℚ(√D)`; transport. Any two `Algebra ℚ K` and any two `DecidableEq K` instances agree. |
| `∃ y, ¬IsOfFinAddOrder y` | `y_K` of infinite order | GZ: `ĥ(y_K) = L′(E/K, 1)/c ≠ 0`. Nondegeneracy of `ĥ` (Néron–Tate; Tau Ceti `canonicalHeight_eq_zero_iff_isOfFinAddOrder`) then gives infinite order. |
| `∀ σ, σy − y` torsion | `ȳ_K = −ε y_K` mod torsion, `ε = −1` | `σ = 1` is trivial; for `σ` = conjugation, `ȳ_K − y_K` is torsion. **Cross-check independent of the printed sign convention**: by Kolyvagin (Math. USSR Izv. 32 (1989)), `L(E^D, 1) ≠ 0` gives `E^D(ℚ)` finite. The `(−1)`-eigenspace of conjugation on `E(K) ⊗ ℚ` is `E^D(ℚ) ⊗ ℚ = 0`, so `ȳ_K − y_K` is torsion for either sign. So the conclusion holds even if the printed relation used the opposite convention. |

**Conclusion.** `GrossZagierHeegner` is a consequence of GZ 1986 (formula and Ch. V) together
with Gross 1984 (or Kolyvagin 1989) and the folded-in parametrization. It is not stronger than
these sources and not vacuous: `C_5`, its newform and a Heegner `D` with `L(C_5^D, 1) ≠ 0` meet
every hypothesis (rv-cr3-trust §2.1 numerics).

**Strength remark** (VERIFIED, compiled). L3's conclusion is satisfied by the base change of
**any** rational point of infinite order (`exists_fixed_point_of_rat_point`). Hence:

- `GrossZagierCd → GrossZagierHeegnerCd` (`grossZagierHeegnerCd_of_grossZagierCd`);
- `FHNonvanishingCd → (GrossZagierHeegnerCd → GrossZagierCd)` (§0.1).

Given L2, the restricted L3 is therefore *equivalent* to `GrossZagierCd`. The decomposition does
not make the Gross–Zagier input logically smaller. What it buys is that L3's hypotheses,
including the auxiliary `K`, are those of GZ's published corollary. That is the point of the
split, and it is not a defect.

### 3.4 Gaps and proposed fixes (not applied)

**GZ-1. Scope wider than the use; Faltings folded in.**
- *Gap.* The leaf covers every elliptic curve with a matching newform, so it folds in Faltings'
  isogeny theorem to obtain `φ : X₀(N) → E`. The use is `E = C_d`, for which Shimura 1971 gives
  `φ` directly.
- *Fix.* Use `ZInQ.GZStatements.GrossZagierHeegnerCd` (text in §0.1). It is implied by the leaf
  (`grossZagierHeegnerCd_of_grossZagierHeegner`), and also by `Literature.GrossZagier`
  (`grossZagierHeegnerCd_of_grossZagier`). Or use the weakest form `GrossZagierRankCd`, which is
  GZ's rank corollary.

**GZ-2. Docstring precision.** Proposed new docstring:

```
/-- **(L3) Gross–Zagier with Gross's conjugation relation** [restricted form: for `C_d`,
`d ≡ 5 mod 8` squarefree, level `32 d²` by `level_eq_of_coeff_cd`]. Let `E/ℚ` have the L-series
of a weight-2 newform `f` of level `N` and trivial nebentypus. Let `D < −4` be an odd fundamental
discriminant with every `p ∣ N` split in `ℚ(√D)` (so `D ≡ β² mod 4N` and `(D, 2N) = 1`). Suppose
`L(f, s)` has a simple zero at `s = 1` and `L(f ⊗ χ_D, 1) ≠ 0`, so that
`L′(E/K, 1) = L′(f, 1) L(f ⊗ χ_D, 1) ≠ 0`. Then for every `K ≅ ℚ(√D)`, `E(K)` has a point `y` of
infinite order (the Heegner point `y_K`) with `σ y − y` torsion for all `σ ∈ Aut(K/ℚ)`.

Sources: B. Gross, D. Zagier, Invent. Math. 84 (1986), 225-320, Thm I.6.3 and Ch. V (UNVERIFIED
numbers): `L′(E/K, 1) = c ĥ(y_K)`, `c ≠ 0`. The relation `ȳ_K = −ε y_K` mod torsion: B. Gross,
*Heegner points on X₀(N)* (1984), or GZ Ch. V (UNVERIFIED). Alternatively Kolyvagin (1989):
`E^D(ℚ)` is finite since `L(E^D, 1) ≠ 0`. Folded in: the parametrization `X₀(N) → E`
(Shimura 1971 Thm 7.14 with Faltings 1983, or for CM curves Shimura, Nagoya Math. J. 43 (1971))
and nondegeneracy of `ĥ`. The conclusion is implied by "`E(ℚ)` has a point of infinite order"
(`GZStatements.exists_fixed_point_of_rat_point`). -/
```

**GZ-3. None of substance.** No hypothesis of L3 is weaker than GZ's. No conclusion goes beyond
`y_K`. The sign convention cannot make L3 false (Kolyvagin cross-check, §3.3).

---

## 4. Definitions the leaves use (adversarial pass)

| Definition | Genuine? | Evidence |
| --- | --- | --- |
| `HeckeRing.GL2.Newform N 2` (TC) | yes | eigen at all `T_n`, `(n, N) = 1`; `ne_zero`; `isNew : ∈ TauCeti.cuspFormsNew` (Petersson complement of old forms); `isNorm : a₁ = 1` (VERIFIED read). A wrong or empty `Newform` type would contradict the proved `HeckeThetaNewform` (atkin-li), which constructs newforms with prescribed coefficients. |
| `rootNumber f hχ = I^2 * frickeSign` | yes | `frickeSign` = the `ε ∈ {±1}` with `𝒲_N f = ε f` (`Newforms/Fricke.lean:221-233`); it appears as the sign in the proved functional equation `frickeCompletedL_sub_eq` (VERIFIED read), so it is the classical root number |
| `coeff f n` | yes | `(qExpansion 1 f.toCuspForm).coeff n`; the width of `Γ₁(N)` at `∞` is 1 |
| `chiD D n = jacobiSym n |D|` | yes, for odd `D` | Kronecker character of `ℚ(√D)` at every prime, completely multiplicative (VERIFIED: `chiD_prime`, `chiD_two`, `chiD_mul`; gz-decomp's numerical check, 6000 pairs) |
| `IsOddImagFundDisc D` | yes | `D < 0 ∧ D % 4 = 1 ∧ Squarefree D`: the odd negative fundamental discriminants (`Int.emod`) |
| `HeegnerHyp N D` | yes, with `IsOddImagFundDisc` | VERIFIED `heegnerHyp_iff_split`; for `D = 0` see FH-4 |
| `IsEntireCont a 2 G` | yes | entire, and equal to `LSeries a` on `Re s > 2`. Unique (`IsEntireCont.eq`). Existence for the twists is proved (G6), so `∀ G` is not vacuous. |
| `WeierstrassCurve.LFunction` (Mathlib) | yes | Euler product of local factors of the minimal model at every prime (VERIFIED read) |
| `Affine.Point`, `Affine.Point.map`, `IsOfFinAddOrder` (Mathlib) | yes | the group `E(K)` and the Galois action |

No free predicate appears in either leaf. Every symbol is a Mathlib or Tau Ceti definition, or a
project definition checked above.

---

## 5. Weakened leaves: proofs (all VERIFIED, compiled)

- `fhNonvanishingCd_of_fhNonvanishing`: instantiate `B = 4`.
- `grossZagierHeegnerCd_of_grossZagierHeegner`: instantiate `E = C_d`, using
  `shortCurve_cd_isElliptic`.
- `grossZagierRankCd_of_grossZagierHeegnerCd`: G5 (`exists_quadratic_field`) then G4
  (`exists_rat_point_of_heegner`).
- `grossZagierCd_of_fhNonvanishingCd_grossZagierRankCd`: the gz-decomp route, with steps:
  - `modular_cd` applied to `GZTheta.heckeThetaNewform`;
  - G2 (`isEntireCont_of_isLContinuation`);
  - G3 (`signOfSimpleZero`);
  - the restricted L2;
  - G6 (`exists_isEntireCont_twist`);
  - the rank form of L3.
- `isLContinuation_of_isEntireCont`: Hecke's continuation `ZInQ.Contrib.heckeContinuation`
  (proved), together with uniqueness of entire continuations, turns `IsEntireCont (coeff f) 2 F`
  into `IsLContinuation C_d F`.
- `exists_fixed_point_of_rat_point`: `y = baseChange ℚ K P`. `map` is injective
  (`Affine.Point.map_injective`), so `y` has infinite order. `map σ y = y` by
  `Affine.Point.map_baseChange`.
- `level_eq_of_coeff_cd`: build `g` of level `32 d²` (gz-theta `cmForm32`, atkin-li `newCM`). At
  primes `p ∤ 32 d² N`, `aₚ(f) = aₚ(C_d) = heckeCoeff d p = aₚ(g)` (Deuring, proved), and
  `aₚ = λₚ` for normalized eigenforms. Then apply `GZTheta.newformUniqueAcrossLevels` at the
  common level `N · 32 d²`.

---

## 6. What a human must check against the papers

Each item gives the exact text to compare. "Lean says" is the English reading of the restricted
leaf, which is what the proposed headline uses.

**H1. Friedberg–Hoffstein 1995, central-value theorem.** Lean says: *for `f` the newform of
`C_d` (`d ≡ 5 mod 8` squarefree; level `32 d²`; CM by `ℚ(i)`; root number `−1`) there is an odd
fundamental `D < −4` with `D ≡ 1 (mod 8)`, `D` a nonzero square mod every `p ∣ d`, and
`L(f ⊗ χ_D, 1) ≠ 0`.* Check in the printed theorem:

- (a) no restriction on the conductor of `π`. The level here is `32 d²`: even, divisible by
  `2⁵`, not squarefree.
- (b) dihedral `π` (CM forms) are not excluded.
- (c) the local data may be prescribed at an arbitrary finite `S ∋ ∞, 2`, with `χ_v` trivial
  at finite `v ∈ S` and `χ_∞ = sgn`.
- (d) the form of the root-number hypothesis. Expected: "some `χ₀` with these local components
  has `ε(½, π ⊗ χ₀) = 1`", or a condition on `∏_{v∈S} ε_v(π_v ⊗ χ_v) χ_v(−1)`.
- (e) the conclusion is "infinitely many `χ`" (or at least one `χ ≠ χ_{−3}`) with
  `L(½, π ⊗ χ) ≠ 0`, and whether `L` is complete, finite or partial (all equivalent here, §2.3).
- (f) the label (A or B) of this theorem, and the page.

If (a) or (b) fails, cite instead the special case for this family:
- Bump–Friedberg–Hoffstein 1990; check its level hypotheses;
- Waldspurger 1981/1985 with a nonvanishing result for the relevant half-integral weight
  coefficients.

**H2. Twisted root number.** Text to find (Atkin–Li 1978, Thm 3.1 or its corollary; or
Iwaniec–Kowalski Prop. 14.20; or Shimura 1971). Expected: *if `f ∈ S₂(Γ₀(N))` is a newform and `χ`
is a primitive character mod `r` with `(r, N) = 1`, then `f ⊗ χ` is a newform of level `N r²`,
and its Fricke eigenvalue is `w(f ⊗ χ) = χ(N) τ(χ)² r⁻¹ w(f)`* (equivalently, the same relation
for root numbers `ε = −w` in weight 2). For quadratic `χ_D`, `τ(χ_D)² = χ_D(−1)|D|`, so
`ε(f ⊗ χ_D) = χ_D(−N) ε(f)`. Lean proves `χ_D(−N) = −1` (`jacobiSym_neg_level`). Hence
`ε(f ⊗ χ_D) = +1` when `ε(f) = −1`. Check the printed relation, including the factor `χ(N)`
versus `χ(−N)` or `χ̄(N)`. For real `χ` all these readings coincide once `τ(χ)²` is evaluated.

**H3. Gross–Zagier 1986, standing hypotheses.** Find the hypotheses on `(N, D)` in Ch. I. Lean
supplies: `D` odd, `D ≤ −7`, fundamental, every `p ∣ N` split, and `N = 32 d²`. These imply
`D ≡ β² mod 4N` (proved in Lean: `exists_sq_mod_four_mul_of_heegnerHyp`) and `(D, 2N) = 1`
(proved: `coprime_of_heegnerHyp`, and `D` odd). Check that:
- every printed hypothesis is among these;
- in particular, `N` is not required to be squarefree or odd.

**H4. Gross–Zagier 1986, Ch. V.** Text to find: *`L′(E/K, 1) = c · ĥ(y_K)` with `c ≠ 0`* and
*`y_K` has infinite order iff `L′(E/K, 1) ≠ 0`*, for `E` with a parametrization from `X₀(N)`, `N`
the conductor. Check also `L(E/K, s) = L(E, s) L(E^D, s)`.

**H5. Conjugation relation.** Text to find in Gross 1984 §5 or GZ Ch. V: *`ȳ_K = −ε y_K`
(mod `E(K)_tors`), `ε` the sign in `Λ(E, 2 − s) = ε Λ(E, s)`*. Possible alternatives: the sign
written via the `w_N`-eigenvalue `w = −ε`, as `ȳ_K = w y_K`; or `ε` defined as the
functional-equation sign of `L(E/K, s)`. In every reading, for analytic rank 1 the point
`y_K + ȳ_K` must be `2y_K` mod torsion. The Kolyvagin cross-check (§3.3) makes L3 true whatever
the printed convention.

**H6. Modular parametrization of `C_d`.** Text to find in Shimura, Nagoya Math. J. 43 (1971):
*an elliptic curve over `ℚ` with complex multiplication is a quotient of `J₀(N)` over `ℚ`, `N` its
conductor*. Or in Shimura's 1971 book, Thm 7.14-7.15 (`E_f` exists), plus Faltings 1983 Korollar 2
(isogeny). For `C_d` the conductor is `32 d²`, consistent with `level_eq_of_coeff_cd`
(VERIFIED).

---

## 7. Reproduction

```
lake build ZInQKernel.Contrib.GZStatements.Weak ZInQKernel.Contrib.GZStatements.Level \
  ZInQKernel.Contrib.GZStatements.Compat ZInQKernel.Contrib.GZStatements.Hensel
lake env lean scratch/gz-statements/Check.lean        # types and #print axioms
~/bin/uv run --offline --no-project --with sympy python -I scratch/gz-statements/check_heegner.py
```
