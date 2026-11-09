# The CM branch of the six-contact estimate is empty for rational u

Status labels. **VERIFIED**: checked against the manuscript `diophantine_zq.tex` (line numbers
refer to the frozen 11/5 source), against the Lean development, or by a computation whose
script is in `scratch/h-cm/` (outputs saved beside the scripts as `*.output.txt`).
**STANDARD**: a published theorem, with reference. **SPECULATIVE**: an idea or expectation
that is not proved.

Notation. `𝒞 = {0,-15,-20,-24,-30,-60}`, `F(u) = ∏_{c∈𝒞}(u-c)`, `G(u) = 7u²+300u+3600`,
`H(u) = (u²-60u-1800)(13u²+480u+3600)(11u²+600u+7200)`, `J(u) = -57600F²/G⁶`
(manuscript lines 377-386, 510-516). `B` is the quaternion algebra over `ℚ` of discriminant 6,
`O` a maximal order, `X = X⁶` the Shimura curve over `ℚ` (coarse moduli of principally
polarized abelian surfaces with an `O`-action, in the polarization convention of line 409ff),
`W = {1, w₂, w₃, w₆}` its Atkin–Lehner group, `X* = X/W ≅ P¹_ℚ`. For a point `x ∈ X(ℚ̄)` write
`(A_x, ι)` for the corresponding surface; `x` is a **CM point** if `End_O(A_x) = 𝔬` is an order
in an imaginary quadratic field `K`, and then `CM(𝔬)` denotes the set of all such points.

## Summary

- **The CM branch never occurs for rational `u`** (VERIFIED proof, Section 4.1, from three
  STANDARD inputs). For `u ∈ ℚ \ 𝒞` every fibre surface `A` of the manuscript's
  construction has `End⁰(A_ℚ̄) = B`. Hence the paragraph "CM fibers" (lines 581-631), the
  constants `B_cm`, `C_cm`, and the audit applications A003 (Fowler at `k = D`), A004 (CM
  Faltings height formula), A005 (Gaudron–Rémond for `E² → A`) and the height-section use of
  A065 drop out of the proof of H.
- **The key fact.** In Elkies' coordinate `t` on `X*` (`t = 1, ∞, 0` at discriminants
  `-4, -3, -24`) the manuscript's map is `t(u) = 1 + 27J(u)/16 = H(u)²/G(u)⁶`, with
  `t(u) - 1 = -3(180F(u)/G(u)³)²`. The cover `X → X*` has function field
  `ℚ(t)(√(-t), √(3(t-1)))` (Elkies 1998, §3). So the four points of `X` over `t(u)` have
  coordinates `(±iH/G³, ±540iF/G³)`. They are defined over `ℚ(i)`, and complex conjugation acts
  on them as `w₃`. Shimura's reciprocity law (`K·ℚ(x) = K(f)`) together with the
  Jordan–González–Rotger theorem (`W' × Pic(𝔬)` acts simply transitively on `CM(𝔬)`) admits no
  CM point with such a fibre.
- **No class-number classification is used.** The proof does not use Elkies' list of rational
  CM points. As an independent check, all 27 points of that list were converted to the
  manuscript's coordinate, and none of the 24 non-elliptic values has a rational preimage under
  `J`. Each degree-12 equation `J(u) = j_Δ` factors over `ℚ` into irreducible factors of degree
  2, 4 or 12 (Section 4.2). Completeness of that list would need the class-number 1, 2 and 4
  classifications (Heegner–Baker–Stark, Baker–Stark, Arno or Watkins, which use
  Goldfeld–Gross–Zagier). That is not needed.
- **The numerical constant is unchanged.** `C_cm < Q_R^17` for every admissible `R`, so
  `H₆(S;R) = 2·10¹³·Q_R^17` with or without the CM term. `SixContactEstimate` in Lean needs no
  change, and neither do the precision program (`eB`, `eC` in `Compiler/Precision/CappedTest.lean`)
  or the size chapter.
- **Trade.** Four audit applications (two theorems used only here, Fowler and the CM height
  formula) are replaced by Shimura's reciprocity law for CM points on Shimura curves (1967),
  the Jordan/González–Rotger description of `CM(𝔬)`, Elkies' explicit model of `X⁶ → X*(6)`,
  and standard class field theory. All of these are older and structurally simpler than the
  effective-analytic inputs they replace. Elkies' model is the only computed input. Its two
  twist constants were rederived here from his algebraically proved CM values and checked
  against all 24 entries of his table.

## 1. The statement and every use

### 1.1 In the manuscript (VERIFIED by reading)

The proof of Theorem 4.1 (`thm:height`, lines 404-408) splits the fibre surface `A/L` by its
geometric endomorphism algebra (lines 564-580). It is either `B` or `M₂(k)`. "We treat these two
cases separately" (line 578). The CM case (`End⁰(A_ℚ̄) = M₂(k)`) is the paragraph "CM fibers",
lines 581-631. It concludes `h_F(A) ≤ C_cm`. The two cases are merged at lines 901-905:
`max(1,h_F(A)) ≤ max(1, C_cm, Q_R^17)·M_S(u)^24`. The CM constants are defined at lines 393-394
(`B_cm = D²3^{21000D²} + 1`, `C_cm = 2B_cm + 4096(1028 + 5D + 84000D²)`) and announced at line
401 ("a separate effective CM argument"). Nothing after line 905 refers to the case
distinction. The theta-height step (lines 908-963) uses only `max(1,h_F(A))`.

### 1.2 In Lean (VERIFIED by grep under `ZInQKernel/`)

H enters the main theorem as the hypothesis `ZInQ.SixContactEstimate`
(`Hypotheses/Height.lean`). No Lean statement depends on the CM branch as mathematics. The CM
constants appear only as numerals inside the constant `H₆`:

- `ZInQ.heightBcm`, `ZInQ.heightCcm`, and `ZInQ.heightH6 R = 2·10¹³·max 1 (max C_cm (Q_R^17))`
  (`Hypotheses/Height.lean`).
- `bcmFn`, `ccmFn`, `heightBcm_eq`, `heightCcm_eq`, and
  `A0 = 2·10¹³·max 1 (max heightCcm (Q0^17))` (`Compiler/Precision/HeightConstant.lean`).
- `eval_eB`, `eval_eC` (`Compiler/Precision/CappedTest.lean`): the precision machine computes
  `C_cm` as part of `A0`.

H itself is consumed at exactly two leaves, `Compiler.Precision.sixContact_at_heightPrimes` and
`Mult.sixContact_at_Smul`, in both cases for an adversarial `u ∈ ℚ \ 𝒞`
(`docs/research/rs-height.md`, §1.2-1.4).

### 1.3 What the CM branch has to deliver

Since `u` is adversarial, the CM branch has to cover every `u ∈ ℚ \ 𝒞` whose fibre surface is
CM. For those `u` it must give `max(1, h_F(A)) ≤ max(1, C_cm, Q_R^17)·M_S(u)^24`.

## 2. The weakest form needed, and the slack

**The CM term is numerically invisible (VERIFIED).** `C_cm ≤ 3B_cm ≤ 6D²·3^{21000D²}`, so
`log C_cm < 30000 D²`. On the other hand `log Q_R^17 = 17·R·E₀·log R ≥ 170·G₀²·D³·log D` for
`R ≥ D`. Hence `max(1, C_cm, Q_R^17) = Q_R^17` for every admissible `R`. The CM branch could
deliver any bound up to `Q_R^17·M^24`, a factor of roughly `exp(10G₀²D³ log D)` above what it
proves. Deleting `C_cm` from `H₆` changes neither the theorem nor any Lean numeral's role.
`SixContactEstimate` with `C_cm` is implied by the version without it.

**The weakest form is vacuity.** The branch is needed only for those rational `u` whose fibre is
CM. The statement

> **(NoCM)** For every `u ∈ ℚ \ 𝒞` and every point `x ∈ X(ℚ̄)` over `t(u)`, `x` is not a CM point,

makes it vacuous. That is the strongest possible conclusion, and it is what Section 4.1 proves.
Weaker fallbacks would also suffice: a finite explicit list of exceptional `u`, each with
`h(u) ≤ H₆` (trivially true for any explicit `u`), or any bound on `|Δ|` polynomial in `M`.

## 3. The manuscript's proof of the CM branch and its trust leaves

Structure of lines 581-631 (VERIFIED by reading):

1. Matrix units in `End⁰_L(A) = M₂(k)` give a CM elliptic curve `E/L` and an `L`-isogeny
   `E² → A`.
2. `Δ` is the discriminant of `End(E_ℚ̄)`. Since `j(E) ∈ L` and `[ℚ(j(E)):ℚ] = h(Δ)`, we get
   `h(Δ) ≤ [L:ℚ] = d ≤ D`.
3. Fowler's effective bound at `k = D` gives `√|Δ| ≤ 2D²e^{21000D²}`.
4. The CM Faltings height is read off the discriminant formula for a reduced period
   `τ = x + iy` with `y ≤ √|Δ|/2`, giving `h_F(E) ≤ π√|Δ|/12 + 1 ≤ B_cm`.
5. The Gaudron–Rémond isogeny estimate over `L` with source `E²`, plus Faltings' height
   variation and additivity, give `h_F(A) ≤ C_cm`.

| Step | Imported theorem | Lines | Audit | Used elsewhere? |
| --- | --- | --- | --- | --- |
| 1 | Matrix units, isogeny `E² → A` over the Hom field (Milne, Poincaré reducibility) | 583-586 | (A061/A079 context) | yes (non-CM branch) |
| 2 | Singular moduli are algebraic integers of degree `h(Δ)` (class polynomial) | 586-588 | A065 | yes: lines 1009-1012, 1759-1765 (non-integral `j = 35152/9` excludes CM) |
| 3 | Fowler, Prop. 2.7: `h(Δ) ≤ k ⇒ √|Δ| ≤ 2k²exp(21000k²)` | 588-593 | A003 | **no** |
| 4 | Barquero-Sanchez et al., CM Faltings height, discriminant formula (6.2) | 594-613 | A004 | **no** |
| 5 | Gaudron–Rémond, Theorem 1.4, source `E²` | 614-631 | A005 | the theorem yes (A015, lines 878-895); this application no |
| 5 | Faltings, height variation and additivity | 619-630 | A006 | yes (lines 894-903) |

Fowler's bound at `k = D` is the most expensive leaf of the branch: it is an effective
class-number lower bound with no exceptional-field exclusion, applied at a class number of size
`D > 2^(2^8008)`. `cmheight` (A004) is cited only here (line 605). `fowler` is cited only at
line 588 (and in the bibliography line 6808). VERIFIED by grep.

## 4. Candidate cheaper routes

### 4.1 Route C1 (carried out): the fibre over a rational point is defined over ℚ(i)

**4.1.1 Coordinates (VERIFIED, `cm_table.py` Part A).** Elkies normalizes a rational coordinate
`t` on `X*(6)` by `t = 0, 1, ∞` at the elliptic points of orders `2, 4, 6`, i.e. at the CM
discriminants `-24, -4, -3` (Elkies, *Shimura curve computations*, ANTS-III, LNCS 1423 (1998),
§3.1). The manuscript's `j` takes the values `-16/27, 0, ∞` there (line 908; branch data at
lines 421-422). Both are `ℚ`-rational coordinates on the same curve `X* = X⁶/W`, so
`t = 1 + 27j/16`. Then:

- `G⁶ - 97200F² = H²` (line 515), so `t(u) = 1 + 27J(u)/16 = H(u)²/G(u)⁶` and
  `t(u) - 1 = -97200F²/G⁶ = -3·(180F/G³)²`.
- For `u ∈ ℚ \ 𝒞`: `F(u) ≠ 0`; `G(u) ≠ 0` (`disc G = -10800`); `H(u) ≠ 0` (its quadratic
  factors have non-square discriminants `10800, 43200, 43200`, line 541 and rs-height §3.3).
  So `t(u)` is a nonzero rational square, `t(u) - 1 ∈ -3·ℚ^{×2}`, and `0 < t(u) < 1`.

**4.1.2 The model of `X → X*` (STANDARD, with VERIFIED consistency checks).** Elkies (§3.1,
statement; §3.3, determination of the constants) proves that the function field of `X⁶` is
`ℚ(t)(√(c₀t), √(c₁(t-1)))` with `c₀ = -1`, `c₁ = 3`. The resulting conic `X² + Y² + 3Z² = 0`
agrees with Ihara's equation reported by Kurihara. Elkies fixes the constants by matching the
conductors `30, 42, 78` of the genus-one curves `X₀⁶(l)`, `l = 5, 7, 13`. Write
`y₁ = √(-t)`, `y₂ = √(3(t-1))`. The stabilizers of the points of `X` over `t = 1, ∞, 0` are
`⟨w₂⟩, ⟨w₃⟩, ⟨w₆⟩`, the fixed groups of the elliptic points of discriminants `-4, -3, -24`.
The quotient `X/⟨w_m⟩ → X*` is the double cover branched over the two elliptic values not
under fixed points of `w_m`. Therefore `w₂ : (y₁,y₂) ↦ (y₁,-y₂)`, `w₆ : (y₁,y₂) ↦ (-y₁,y₂)`,
`w₃ : (y₁,y₂) ↦ (-y₁,-y₂)`. VERIFIED as a derivation from the branch data.

The constants were checked independently in four ways (VERIFIED, scripts in `scratch/h-cm/`):

- *Rederivation.* For a class-number-one discriminant `Δ`, Shimura's theorem (S) below gives
  `ℚ(x) ⊆ K = ℚ(√Δ)`. So `c₀t_Δ` and `c₁(t_Δ - 1)` lie in `{1, Δ}` modulo squares. Elkies'
  values for `Δ = -19, -43, -67, -163` force `c₀ = -1` and `c₁ = 3` (`cm_table.py` Part D).
  The first two of these values are among those Elkies proved algebraically.
- *Algebraic recomputation of the values.* Elkies' covers `X₀*(l) → X*(6)` (`l = 5, 7, 13`) and
  involutions `w_l` were rechecked: degree, cycle structure over `0, 1, ∞`, and `w_l² = 1`. The
  rational values of `t` at the solutions of `t(x) = t(w_l(x))` were recomputed. This reproduces
  exactly the 15 table values with `-Δ ∈ {4, 19, 24, 40, 43, 51, 75, 84, 88, 100, 120, 132,
  147, 168, 312}`, including `t(-19) = 3211/1024` and `t(-43) = 21250987/16000000`
  (`isogeny_check.py`).
- *Fibre fields.* For all 24 non-elliptic entries of Elkies' Table 1, the fibre field
  `ℚ(√(-t), √(3(t-1)))` lies in the genus field of `Δ`, as it must since it lies in the ring
  class field. Complex conjugation acts on each fibre by a nontrivial element of `W`, as it must
  since `X⁶(ℝ) = ∅` (`cm_table.py` Part C).
- *Reciprocity at ramified primes.* For every entry and every `p ∈ {2,3}` ramified in `K`, the
  Frobenius of the prime above `p`, computed by genus characters, acts on the fibre exactly as
  `w_p`. This is the rule `σ_𝔭(x) = w_p(x)` of Jordan's thesis (Part C). Also `2^b·h(Δ) = 4` for
  every entry, as the count (JGR) below requires for a rational point of `X*` (Part E).

**4.1.3 Inputs from the theory of CM points.**

- **(S) Shimura's reciprocity law** (STANDARD: G. Shimura, *Construction of class fields and
  zeta functions of algebraic curves*, Ann. of Math. 85 (1967), Main Theorem I; in the form used
  here, Saia, arXiv:2212.12635, Thm. "Shimura" and §2). If `x ∈ X⁶` is a CM point with
  `End_O(A_x) = 𝔬`, `𝔬` the order of conductor `f` in `K`, then `K·ℚ(x) = K(f)`, the ring
  class field. For `σ ∈ Gal(ℚ̄/K)`, `σ(x) = [𝔞]⋆x`, where `[𝔞] ∈ Pic(𝔬)` corresponds to
  `σ|_{K(f)}` under the Artin map and `⋆` is the action of `Pic(𝔬)` on `CM(𝔬)`.
- **(JGR) The structure of `CM(𝔬)`** (STANDARD: B. Jordan, *On the Diophantine arithmetic of
  Shimura curves*, Harvard thesis 1981, §3, for `f = 1`; J. González and V. Rotger,
  *Non-elliptic Shimura curves of genus one*, J. Math. Soc. Japan 58 (2006), §5 and Prop. 5.6,
  for general `f`; restated in Saia, op. cit., Prop. "number of CM points" and the paragraph
  after Thm. "fake elliptic curves"). `W` permutes `CM(𝔬)`. Let `b` be the number of primes
  `p | 6` inert in `K` and `W' = ⟨w_p : p | 6 inert in K⟩`. Then `|CM(𝔬)| = 2^b·h(𝔬)`, and
  `W' × Pic(𝔬)` acts simply transitively on `CM(𝔬)`.
- **(Emb) Local embedding condition** (STANDARD: Vignéras, *Arithmétique des algèbres de
  quaternions*, LNM 800, Ch. II §1 and Ch. III §5). At `p | 6`, `O_p` is the unique maximal
  order `{x : N(x) ∈ ℤ_p}` of the division algebra `B_p`. An optimal embedding of `𝔬` therefore
  forces `𝔬_p = O_{K,p}` and `K_p` a field: `p ∤ f`, and `p` is not split in `K`.
- **(RCF) Ramification of ring class fields** (STANDARD: Cox, *Primes of the form x²+ny²*,
  §9). `K(f)/K` is unramified at every prime not dividing `f`.

**4.1.4 Theorem (NoCM).** *Let `u ∈ ℚ \ 𝒞` and let `x ∈ X(ℚ̄)` lie over `t(u)`. Then `x` is not
a CM point. Consequently every fibre surface `A` in the proof of Theorem 4.1 has
`End⁰(A_ℚ̄) = B`.*

*Proof.* (VERIFIED as an argument from (S), (JGR), (Emb), (RCF) and 4.1.1-4.1.2.)

*Step 1: the fibre.* Put `t₀ = t(u)`, `r₁ = H(u)/G(u)³`, `r₂ = 540F(u)/G(u)³`. By 4.1.1,
`r₁, r₂ ∈ ℚ^×`, `-t₀ = (ir₁)²` and `3(t₀ - 1) = (ir₂)²` (`cm_table.py` Part D). The affine
curve `y₁² = -t`, `y₂² = 3(t-1)` is the smooth conic `y₂² + 3y₁² + 3 = 0`. So the fibre of
`X → X*` over `t₀` consists of the four points `(ε₁ir₁, ε₂ir₂)`, `ε_i = ±1`, and the residue
field of each is `ℚ(i)`. `W` acts on the fibre simply transitively by sign changes. An element
`σ ∈ Gal(ℚ̄/ℚ)` acts trivially if `σ(i) = i` and as `w₃` otherwise. In particular
`ℚ(x) = ℚ(i)` and `σx ∈ {x, w₃x}` for all `σ`.

*Step 2: reductions.* Suppose `x ∈ CM(𝔬)`, `𝔬 ⊂ K` of conductor `f`. By (Emb), `2` and `3`
are not split in `K` and `(f, 6) = 1`. By (JGR), the four points `W·x` lie in `CM(𝔬)`, so
`|CM(𝔬)| ≥ 4`. By (S), `K(f) = K·ℚ(x) = K(i)`, hence `h(𝔬) = [K(f):K] ≤ 2`.

*Case A: `2` inert in `K`.* Then `2` is unramified in `K`, and in `K(f)/K` by (RCF) because
`2 ∤ f`. So `K(f)/ℚ` is unramified at 2. But `ℚ(i) = ℚ(x) ⊆ K(x) = K(f)`, and 2 ramifies in
`ℚ(i)`. Contradiction.

*Case B: `2` and `3` ramified in `K`.* Then `b = 0` and `|CM(𝔬)| = h(𝔬) ≤ 2 < 4`.
Contradiction.

*Case C: `2` ramified, `3` inert in `K`.* Then `b = 1` and `W' = {1, w₃}`. For
`σ ∈ Gal(ℚ̄/K)`, Step 1 gives `σx = w·x` with `w ∈ {1, w₃} = W'`, and (S) gives
`σx = [𝔞_σ]⋆x`. Simple transitivity of `W' × Pic(𝔬)` forces `w = 1` and `[𝔞_σ] = 1`. Since
the Artin map is onto `Pic(𝔬)`, `h(𝔬) = 1` and `|CM(𝔬)| = 2 < 4`. Contradiction.

These cases are exhaustive. For the manuscript's `A`: its image under `Y₃ → X⁶` is a point over
`j = J(u)`, i.e. over `t(u)`, and `End⁰(A_ℚ̄) = M₂(k)` holds exactly when that point is CM. ∎

Remarks. (a) The argument uses one property of `J`: for rational `u`, `Gal(ℚ̄/ℚ)` acts on the
fibre of `X⁶` through a group of order 2, by `w₃`, with fixed field `ℚ(i)`. Equivalently, the
quotient `P¹_u/C₃` (`C₃` the rotation subgroup of the dihedral group of rs-height §3.3) is the
twist of `X⁶` by the cocycle with values `(-1, -1)` on `(y₁, y₂)`, and it is isomorphic to
`X⁶` over `ℚ(i)`. (b) Elkies' table has six points with `t ∈ (0,1)`. For `-Δ = 52, 88, 148`
(`2` ramified, `3` inert, as in Case C), Frobenius at the prime above 2 acts as `w₂ ∉ W'`. For
`-Δ = 132, 312, 708` (as in Case B, `h = 4`), `Pic` acts simply transitively on the fibre. In
both situations the fibre field has degree 4, not `ℚ(i)`, and the square-class test of 4.2
fails. (c) `K = ℚ(i)` falls under Case C
with `𝔬 = ℤ[i]`, the elliptic point `t = 1`, which `u ∉ 𝒞` already excludes.

**4.1.5 The rewritten CM part of the proof of H.** In the proof of Theorem 4.1, keep lines
564-580 up to "Hence the geometric endomorphism algebra is either `B` or `M₂(k)`". Then replace
lines 578-631 by:

> *The algebra `M₂(k)` does not occur.* Let `t = 1 + 27j/16` be the coordinate on
> `P¹_j = X⁶/W` with values `0, 1, ∞` at the CM points of discriminants `-24, -4, -3`. By
> [Elkies, §3], `X⁶ → P¹_j` has function field `ℚ(t)(√(-t), √(3(t-1)))`, and `w₂, w₆, w₃`
> change the sign of `√(3(t-1))`, of `√(-t)`, and of both. Since `t(u) = H²/G⁶` and
> `t(u) - 1 = -3(180F/G³)²`, the four points over `t(u)` are `(±iH/G³, ±540iF/G³)`. Each is
> defined over `ℚ(i)`, and complex conjugation acts as `w₃`. If the moduli point `x` of `A` on
> `X⁶` had CM by an order `𝔬` of conductor `f` in `K`, then `2, 3 ∤ f` and neither `2` nor `3`
> splits in `K`. Shimura's reciprocity law gives `K(f) = K·ℚ(x) = K(i)`, and `W'×Pic(𝔬)` acts
> simply transitively on the `2^b h(𝔬)` points of `CM(𝔬)` [Jordan; González–Rotger, Prop.
> 5.6]. Cases A-C above give a contradiction. Hence `End⁰(A_ℚ̄) = B`. Put `M = M_S(u)`,
> `d = [L:ℚ] ≤ D` and `Q = Q_R`.

The heading "Non-CM fibers and scalar descent" then becomes the only case. Line 901 reads "This
proves the estimate needed below: `max(1,h_F(A)) ≤ Q_R^17 M_S(u)^24`". In the definition of `H₆`
(lines 393-397), `B_cm` and `C_cm` may be deleted (`H₆ = 2·10¹³ max(1, Q_R^17) = 2·10¹³Q_R^17`)
or kept: by Section 2 the value is the same. Keeping them avoids touching the Lean numerals. The
sentence at line 401 loses "and a separate effective CM argument".

**4.1.6 Which inputs remain for H.** From the table in rs-height §3.2, the following leave the
proof of H:

- A003 (Fowler, Prop. 2.7) and A004 (CM height formula): these were used nowhere else, so
  `fowler` and `cmheight` leave the trust base.
- A005: only this application of Gaudron–Rémond Theorem 1.4 goes. The theorem stays through
  A015.
- A065: the use at lines 580-595 goes. A065 stays for the non-CM test of `E_ℓ` at lines
  1009-1012 and 1759-1765, which needs only that singular moduli are algebraic integers.

The following enter: (S) Shimura 1967, (JGR) Jordan 1981 / González–Rotger 2006, (E) Elkies
1998 §3.1-3.3 (the model `c₀ = -1`, `c₁ = 3`), and the standard facts (Emb) and (RCF). Every
other leaf is unchanged: A001, A002, A078 (Shimura curve and integral model), A061, A079,
A006, A016, A062, A007, A008, A063, A009, A010, A011 (Pan), A064, A012, A013, A071, A014, A015,
A017, A018.

Comparison. Shimura reciprocity for CM points underlies the canonical model of `X⁶` over
`ℚ`, which the manuscript already uses implicitly when it treats `P¹_j` and `J(u)` as rational.
(JGR) is a counting statement about optimal embeddings combined with (S). Elkies' constants are
the result of a finite computation, now cross-checked several ways. By contrast, Fowler's
proposition is an effective analytic class-number bound, and its application at `k = D` was the
only place where a bound of size `exp(D²)` on a CM discriminant entered.

### 4.2 Route C2 (carried out as a check): Elkies' table and the degree-12 equations

**Conversion (VERIFIED, `cm_table.py`, `md_table.py`).** Elkies' Table 1 lists `(A : B) = t`.
One misprint was found and corrected: for `-Δ = 40`, Table 1 prints `B = 25`, while Table 2
gives `B = 5³`. Only `B = 125` satisfies `A - B = 3⁷` as Table 2 states. All 24 non-elliptic
rows satisfy the `|A - B|` factorizations of Table 2. In the manuscript's coordinate
`j = 16(t-1)/27`:

| -Δ | t = A/B | j = 16(t-1)/27 | 0<t<1 | t mod ℚ^{×2} | t-1 mod ℚ^{×2} |
|---|---|---|---|---|---|
| 3 | ∞ | ∞ | no | – | – |
| 4 | 1 | 0 | no | – | – |
| 24 | 0 | -16/27 | no | – | – |
| 84 | -169/27 | -3136/729 | no | -3 | -3 |
| 40 | 2312/125 | 1296/125 | no | 10 | 15 |
| 51 | -1377/1024 | -2401/1728 | no | -17 | -1 |
| 19 | 3211/1024 | 81/64 | no | 19 | 3 |
| 120 | 5776/3375 | 38416/91125 | no | 15 | 15 |
| 52 | 6877/15625 | -5184/15625 | yes | 13 | -3 |
| 132 | 13689/15625 | -30976/421875 | yes | 1 | -1 |
| 75 | 152881/138240 | 14641/233280 | no | 15 | 15 |
| 168 | -701784/15625 | -11478544/421875 | no | -6 | -1 |
| 43 | 21250987/16000000 | 194481/1000000 | no | 43 | 3 |
| 228 | 66863329/11390625 | 887563264/307546875 | no | 1 | 1 |
| 88 | 15545888/20796875 | -3111696/20796875 | yes | 22 | -33 |
| 123 | -296900721/16000000 | -312900721/27000000 | no | -41 | -1 |
| 100 | 421850521/1771561 | 248935680/1771561 | no | 1 | 15 |
| 147 | -1073152081/3024000000 | -4097152081/5103000000 | no | -21 | -21 |
| 312 | 27008742384/27680640625 | -10750371856/747377296875 | yes | 39 | -1 |
| 67 | 77903700667/1024000000 | 2847396321/64000000 | no | 67 | 3 |
| 148 | 69630712957/377149515625 | -182233364544/377149515625 | yes | 37 | -3 |
| 372 | -455413074649/747377296875 | -19244645944384/20179187015625 | no | -3 | -3 |
| 408 | -32408609436736/55962140625 | -519433145237776/1510977796875 | no | -17 | -17 |
| 267 | -5766681714488721/1814078464000000 | -7580760178488721/3061257408000000 | no | -89 | -1 |
| 232 | 66432278483452232/56413239012828125 | 5937208575184656/56413239012828125 | no | 58 | 87 |
| 708 | 71475755554842930369/224337327397603890625 | -2445785149484175364096/6057107839735305046875 | yes | 1 | -1 |
| 163 | 699690239451360705067/684178814003344000000 | 574497238815433521/42761175875209000000 | no | 163 | 3 |

**Rational roots (VERIFIED).** A rational preimage needs `t ∈ ℚ^{×2}` and `t - 1 ∈ -3ℚ^{×2}`
(4.1.1). No row passes. The nearest misses are `-Δ = 132` and `708`, where `t` is a square but
`t - 1 ∈ -ℚ^{×2}`. Independently, the polynomial `B·H(X)² - A·G(X)⁶` (equivalently
`-57600bF(X)² - aG(X)⁶` for `j = a/b`, line 950) was factored over `ℚ` for each row. The
factorization patterns are `2⁶`, `4³` or `12`, and there is no linear factor. The three elliptic
values give `H = 0`, `F = 0`, `G = 0`, which have no root in `ℚ \ 𝒞`. **There is no rational
root, so there is no height to report.**

**What completeness of the list would need (task question, answered for the record).** A CM
point of `X*` is rational if and only if `CM(𝔬)` is a single `W`-orbit, i.e.
`2^b·h(𝔬) = 4` by (JGR) (VERIFIED for every row, `cm_table.py` Part E). With
`(f, 6) = 1` and `2, 3` non-split, this means:

- `h(𝔬) = 1` with `2, 3` both inert (`b = 2`): the class-number-one problem
  (Heegner–Baker–Stark). This gives `-19, -43, -67, -163`.
- `h(𝔬) = 2` with exactly one of `2, 3` inert (`b = 1`): the class-number-two problem
  (Baker, Stark, Montgomery–Weinberger), plus the elementary class-number formula for orders,
  which gives `-75, -100, -147`.
- `h(𝔬) = 4` with `6 | Δ` (`b = 0`), with `Pic(𝔬)` generated by the classes above 2 and 3 and
  hence `≅ (ℤ/2)²`. This needs the class-number-four classification (Arno, Acta Arith. 60
  (1992), using the Goldfeld–Gross–Zagier lower bound), or Watkins (Math. Comp. 73 (2004),
  `h ≤ 100`). The restriction to exponent-2 class groups does not help: the idoneal problem
  is not effectively solved without the bound on `h`. So no Baker-type input suffices for `b = 0`.

In addition, 10 of the 27 values are only numerical in Elkies' paper (`-Δ = 228, 123,
67, 148, 372, 408, 267, 232, 708, 163`). The algebraic recomputation above covers 15 values;
`-Δ = 52` is proved in Elkies' paper but was not recomputed here. Route C2 is therefore strictly heavier than C1, and C1 makes it
unnecessary. It remains a useful independent check: C1 predicts that no row passes the
square-class test, and none does.

### 4.3 Route C3 (SPECULATIVE): models over ℚ(i) for the non-CM branch

- *Idea.* Step 1 of 4.1.4 shows `ℚ(x) = ℚ(i)` for every `u ∈ ℚ \ 𝒞`. Since `ℚ(i)` splits `B`
  (`2` ramified, `3` inert) and the point is not elliptic, Jordan's descent theorem (thesis
  Thm. 2.1.3; STANDARD) gives a model of `(A, ι)` over `ℚ(i)`, unique up to quadratic twist.
  All of `End(A_ℚ̄) = O` is then defined over `ℚ(i)`.
- *What it would replace.* It would replace the Hom field `L` of degree `≤ D` (lines 564-580),
  the construction of `K` from the level-3 cover (lines 510-531), and possibly the
  Skolem–Noether/Brauer descent (A062, A007), since `A` is already a `B`-surface over a
  quadratic field with field of moduli `ℚ` on `X*`. Conductor exponents at `p ∤ 6` are tame:
  inertia acts through `Aut(A_x̄, ι) ⊆ μ₄` or `μ₆`. So the conductor would be
  `≤ 2^a 3^b ∏_{p | M'} p²`, with `a, b` bounded by the local bounds for 2-dimensional
  representations. Here `M'` would also count primes of `S` with odd contact valuation. This
  could replace `Q_R = R^{RE₀}` by roughly `exp(O(R))` and remove the hypothesis
  `S ⊇ {p ≤ 324}`.
- *Why it might work.* The parity mechanism of lines 510-522 is local at the elliptic points of
  order 2 (the contacts lie over `t = 1`, and `y₂ = 540iF/G³` is the local parameter of `X⁶`
  there). Good reduction after a quadratic twist should be readable from `v_p(y₂)`.
- *Main obstacle.* Controlling the reduction of the `ℚ(i)`-model at `p ∉ S` still needs an
  integral model of the moduli problem near the elliptic points, which is the job of Buzzard's
  models and the level-3 cover (A002, A078). Without it the twist ambiguity can introduce bad
  primes. The modularity step (Pan, A011, or Ribet–Pyle plus Khare–Wintenberger, rs-height R5.4)
  is unchanged. So this route simplifies constants and some descent steps; it removes no deep
  leaf. The constants already have enormous slack (rs-height §2.3), so the payoff is in
  readability and audit size, not in the target.
- *First test.* For about ten small rational `u` (for example `u = 1, 2, 5, -1500/61` from the
  `M_S(u) = 1` list in rs-height §3.3), build the genus-2 curve with Igusa–Clebsch invariants
  `[12(j+1), 6(j²+j+1), 4(j³-2j²+1), j³]` (line 538) by Mestre's algorithm over `ℚ(i)`, choose
  the twist minimizing the conductor, and compare its bad primes with
  `{2,3} ∪ supp M_{{2,3}}(u)`. Success: equality in every case. This needs a computer algebra
  system with genus-2 conductor routines.

### 4.4 Route C4: reach the same conclusion through the ramified Atkin–Lehner rule

Instead of the counting in (JGR), one can use Jordan's rule `σ_𝔭(x) = w_p(x)` for `p | 6`
ramified in `K` (thesis, §3; STANDARD; checked numerically on Elkies' table in 4.1.2). In
Case B or C, `σ_{𝔭₂}` acts on the fibre as `w₂`, but every Galois element acts as `1` or `w₃`.
Since `W` acts freely on the fibre, this is a contradiction. In Case A, (RCF) applies as before.
This route has the same depth as C1. It is listed as a cross-check, so that the proof does not
depend on one normalization of the `Pic`-action.

### 4.5 Route C5: change the construction

Not needed for the CM branch. But a redesign of the contact set or of `J` (rs-height R7) must
recheck the analogue of Step 1: the image of `ℚ`-points must land in a twist of `X⁶` whose
fibres are defined over a field that excludes CM by an argument like Cases A-C. For a general
twist field `ℚ(√a, √b)` the case analysis changes. It goes through as above when the field is a
single imaginary quadratic field ramified at 2 and the twisting element is `w₃` (SPECULATIVE
beyond the present `J`).

## 5. Ranking and recommendation

| Route | Payoff | Status / chance | Reason |
| --- | --- | --- | --- |
| C1 (fibre over `ℚ(i)` + Shimura + JGR) | removes A003, A004 and two applications (A005, A065 here) | **done**; high that it survives audit | short proof; every input is a classical published theorem; the conventions were checked against 24 CM points |
| C4 (ramified Atkin–Lehner rule) | backup proof of the same step | done as a check | same depth as C1 |
| C2 (Elkies' list) | check only | done; completeness would need Arno/Watkins | heavier than C1; 10 values only numerical in the source |
| C3 (`ℚ(i)`-models) | smaller constants, fewer descent steps | speculative; low-medium | integral control at elliptic points still needed; no deep leaf removed |
| C5 (redesign) | none for this branch | n/a | the current `J` already makes the branch empty |

**Recommendation.** Adopt Theorem (NoCM) as a lemma in the proof of H and delete the CM
paragraph, as in 4.1.5. The single next step is an audit of the three new citations to the
standard of `docs/theorem-application-audit/`:

- (S): Shimura 1967, Main Theorem I, in the form `K·ℚ(x) = K(f)` with Galois acting through
  `Pic(𝔬)`.
- (JGR): González–Rotger 2006, Prop. 5.6, and Jordan 1981, §3: the count `2^b h(𝔬)`, simple
  transitivity of `W' × Pic(𝔬)`, and stability of `CM(𝔬)` under `W`. The conventions should be
  checked for the maximal-order curve `X⁶`, which is the case `N = 1` where all conventions agree.
- (E): Elkies 1998, §3.1 and §3.3, `c₀ = -1`, `c₁ = 3`.

Success criterion: three audit records accepted with no unresolved convention issue, and the
manuscript's proof of Theorem 4.1 reading as in 4.1.5. Chance: **high**. The argument is a few
lines once the inputs are granted. Each input is a well-known published theorem. The one
computed input (E) was rederived from Elkies' algebraically proved CM values and is consistent
with all 24 table entries, including a direct check of the reciprocity rule at ramified primes.
The Lean development needs no change, because `C_cm` is dominated by `Q_R^17` (Section 2).
