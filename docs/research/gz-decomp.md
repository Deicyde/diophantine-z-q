# gz-decomp: the Gross–Zagier premise as three literature leaves plus proved glue

Status: research note (task gz-decomp, 2026-11-13). Branch `wip/gz-decomp` (base `wip/tc-port`
443ece10 merged with `origin/main`). Lean: `ZInQKernel/Contrib/GZDecomp/Scope.lean`,
`ZInQKernel/Contrib/GZDecomp/Decomp.lean` (new files), the axiom check
`scratch/gz-decomp/Check.lean` (output `scratch/gz-decomp/out_check_axioms.txt`), and 243 Tau Ceti
modules newly vendored under `ZInQKernel/Contrib/TauCeti/` (list `scratch/gz-decomp/tc-modules.txt`).
Results log: `scratch/gz-decomp/log.md`. No existing file of the project was edited (the two
port fixes are in files this task vendored).

Marks. **VERIFIED**: read in a source named here, computed, or compiled. **STANDARD**: a published
theorem with its reference. **SPECULATIVE**: an assessment. This host has no network and no copy
of any of the papers below: **every theorem number of the literature in this note is
UNVERIFIED**.

---

## 0. Main result

**`Literature.GrossZagier` is decomposed into three leaves, and all of the glue is proved in
Lean.** Every declaration below compiles. `#print axioms` gives exactly
`[propext, Classical.choice, Quot.sound]` for each one (VERIFIED, `out_check_axioms.txt`):

```lean
-- Contrib/GZDecomp/Scope.lean
theorem ZInQ.GZDecomp.grossZagierCd_of_grossZagier :
    ZInQ.Literature.GrossZagier → ZInQ.GZDecomp.GrossZagierCd
theorem ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagierCd :
    ZInQ.SixContactMin → ZInQ.Literature.TYZThm35ReadingA → ZInQ.GZDecomp.GrossZagierCd →
      ZInQ.FrozenTarget
theorem ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzInputs_grossZagierCd :
    ZInQ.SixContactMin → ZInQ.PropN.TYZInputs → ZInQ.GZDecomp.GrossZagierCd → ZInQ.FrozenTarget
-- Contrib/GZDecomp/Decomp.lean
theorem ZInQ.GZDecomp.grossZagierCd_of_leaves' :
    ZInQ.GZDecomp.HeckeThetaNewform → ZInQ.GZDecomp.FHNonvanishing →
      ZInQ.GZDecomp.GrossZagierHeegner → ZInQ.GZDecomp.GrossZagierCd
theorem ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves :
    ZInQ.SixContactMin → ZInQ.Literature.TYZThm35ReadingA → ZInQ.GZDecomp.HeckeThetaNewform →
      ZInQ.GZDecomp.FHNonvanishing → ZInQ.GZDecomp.GrossZagierHeegner → ZInQ.FrozenTarget
theorem ZInQ.GZDecomp.signOfSimpleZero : ZInQ.GZDecomp.SignOfSimpleZero
```

The glue lemmas `modular_cd`, `isEntireCont_of_isLContinuation`, `exists_isEntireCont_twist`,
`exists_rat_point_of_heegner`, `exists_quadratic_field` and `grossZagierCd_of_leaves` have the
same axioms.

So, on the headline's route, Theorem 1.1 follows from `SixContactMin`, TYZ reading A, and these
three leaves (`frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves`).

### 0.1 Leaf table

| Leaf | Lean (`ZInQ.GZDecomp.`) | Published source (all locators UNVERIFIED) | Tier | Status |
| --- | --- | --- | --- | --- |
| L1 | `HeckeThetaNewform` | Hecke (1936-37); Shimura, *Introduction to the arithmetic theory of automorphic functions* (1971); Miyake, *Modular forms* (1989) Thm 4.8.2; Iwaniec, *Topics in classical automorphic forms* Thm 12.5. Deuring's identity, the other half of modularity of `C_d`, is proved in Lean | textbook | stated over genuine definitions, compiles |
| L2 | `FHNonvanishing` | Friedberg–Hoffstein, Ann. of Math. 142 (1995) 385-423, Thm B; Bump–Friedberg–Hoffstein, Invent. Math. 102 (1990) 543-618; Waldspurger (1985, 1991). Folded in: the root number of a twist, `ε(f⊗χ_D) = ε(f)χ_D(−N)` (Shimura; Atkin–Li 1978) | research | stated, compiles |
| L3 | `GrossZagierHeegner` | Gross–Zagier, Invent. Math. 84 (1986) 225-320, Thm I.6.3 and Ch. V; Gross, *Heegner points on X₀(N)* (Durham 1983, publ. 1984) for `ȳ_K = −ε y_K`. Folded in, because `X₀(N)` cannot be stated in Lean: Eichler–Shimura/Shimura 1971 Thm 7.14-7.15 with Faltings 1983 Kor. 2 (or Shimura, Nagoya Math. J. 43 (1971) for CM curves), and nondegeneracy of `ĥ` (a Tau Ceti theorem) | research | stated, compiles; finest form that can be stated today |

### 0.2 Glue table

| Step | Content | Lean | Status |
| --- | --- | --- | --- |
| S1 | `GrossZagier ⇒ GrossZagierCd`; the headline chain with `GrossZagierCd` | `grossZagierCd_of_grossZagier`, `frozenTarget_of_…_grossZagierCd` (2 forms) | **proved** |
| G1 | modularity of `C_d` in L-series form: L1 plus Deuring `cdCoeff d = heckeCoeff d` | `modular_cd` | **proved** (uses `HeckeFE.deuringCd_of_gaussPointCount`, `GaussFE.gaussPointCount`, `HeckeAll.LFunction_cd_apply'`) |
| G2 | a continuation of `L(C_d, s)` is a continuation of `L(f, s)` | `isEntireCont_of_isLContinuation` | **proved** |
| G3 | simple zero at `s = 1` ⇒ root number `−1` | `signOfSimpleZero` | **proved** (Tau Ceti functional equation, `Newform.frickeCompletedL_sub_eq`) |
| G4 | descent: `y ∈ E(K)` of infinite order, `σy − y` torsion ⇒ a rational point of infinite order | `exists_rat_point_of_heegner` | **proved** (Tau Ceti `Affine.Point.exists_baseChange_eq_of_map_eq`) |
| G5 | existence of `K = ℚ(√D)` | `exists_quadratic_field` | **proved** (`AdjoinRoot (X² − D)`) |
| G6 | `∑ aₙ(f)χ_D(n)n^{−s}` has an entire continuation | `exists_isEntireCont_twist` | **proved** (Tau Ceti `CuspForm.twist`, `qExpansion_twist_coeff`) |
| G0 | assembly | `grossZagierCd_of_leaves`, `grossZagierCd_of_leaves'` | **proved** |

There is no open glue.

### 0.3 Answer on scope

**`Literature.GrossZagier` is used only at `C_d : y² = x³ − d²x` with `d ≡ 5 (mod 8)` squarefree.**
VERIFIED by reading every Lean use (`git grep -n GrossZagier`): `CR3Literature.lean:110`
(`certifiedRankTYZClRk_of_literature` applies it to `shortCurve (-(d:ℚ)^2)` only); the other uses
(`MainLiterature.lean`, `Contrib/GaussFE/Headline.lean`, `Contrib/HeckeFE/Basic.lean:2186, 2760`,
scratch copies) only pass it on to that theorem. The case
`ZInQ.GZDecomp.GrossZagierCd` suffices: the headline chain goes through with it
(`frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagierCd`, and the TYZ-inputs variant), and
`GrossZagier` implies it (`grossZagierCd_of_grossZagier`). The family form
`GrossZagierCongruent` (all squarefree `d`, closed under the twists `C_d ↦ C_{|dD|}`) sits in
between.

**Proposal to the owner** (a statement change, not made here). Replace the premise
`Literature.GrossZagier` by `GZDecomp.GrossZagierCd`, which it implies (`grossZagierCd_of_grossZagier`) and which is all the proof
uses. Or replace it by the three leaves L1-L3, which give `GrossZagierCd` in Lean.

### 0.4 Relation to cr3-trust Part D

| cr3-trust step | Here |
| --- | --- |
| D1 modularity of `C_d` (Deuring; Shimura 1971) | L1, with Deuring's identity proved (G1); the map `X₀(N) → C_d` is needed only inside L3 |
| D2 auxiliary `K` with `L(C_d^K, 1) ≠ 0` (BFH / FH / Waldspurger) | L2, with the sign (G3) and the continuation (G6) proved |
| D3 Gross–Zagier and `ȳ_K = −ε y_K` (GZ 1986, Gross 1984) | L3, with the descent to `C_d(ℚ)` (G4) and `K` itself (G5) proved |
| D4 (Kolyvagin, Kriz) | not used |

---

## 1. Scope (step 1)

```lean
def ZInQ.GZDecomp.GrossZagierCd : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ∀ F : ℂ → ℂ,
    IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F → analyticOrderAt F 1 = 1 →
      ∃ P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point, ¬IsOfFinAddOrder P
```

`IsLContinuation` and `analyticOrderAt` are as in `Literature.GrossZagier`. Proofs:

- `certifiedRankTYZClRk_of_readingA_grossZagierCd`: `analyticOrder_eq_one` applied to
  `tyzRow5b_of_readingA hA ZInQ.Contrib.heckeContinuation` and
  `rootNumberVanishing_of_functionalEquation ZInQ.Contrib.functionalEquation5`, then `hG`. This is
  the proof of `certifiedRankTYZClRk_of_literature` with `GrossZagierCd` in place of
  `GrossZagier`.
- `frozenTarget_of_…_grossZagierCd` then applies
  `exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk`.

The two proved CR₃ Props (`HeckeContinuation`, `FunctionalEquation5`) are discharged, so the new
headline has three premises: `SixContactMin`, `TYZThm35ReadingA`, `GrossZagierCd`.

---

## 2. The decomposition (step 2)

### 2.1 Route

For `d ≡ 5 (mod 8)` squarefree and `F` an entire continuation of `L(C_d, s)` with a simple zero at
`1`:

1. (L1 + G1) There is a newform `f` of weight 2, trivial nebentypus and some level `N` with
   `aₙ(f) = aₙ(C_d)` for all `n ≥ 1`.
2. (G2) `F` continues `L(f, s)`.
3. (G3) Hence the root number of `f` is `−1`.
4. (L2 + G6) Hence there is an odd fundamental `D < −4`, with every `p | N` split in `ℚ(√D)`,
   such that `L(f ⊗ χ_D, 1) ≠ 0`.
5. (G5, L3) Let `K = ℚ(√D)`. There is `y ∈ C_d(K)` of infinite order with `σy − y` torsion for
   every `σ ∈ Aut(K/ℚ)`: the Heegner point.
6. (G4) Then `y + σy ∈ C_d(ℚ)` has infinite order.

### 2.2 Objects (all genuine definitions)

- `HeckeRing.GL2.Newform N k` (Tau Ceti, `Newforms/Newform.lean`). A cusp form on `Γ₁(N)` with
  nebentypus `χ`, an eigenvector of the Hecke operators `T_n` with `(n, N) = 1`, in the new
  subspace, normalized by `a₁ = 1`. The new subspace `TauCeti.cuspFormsNew` is the Petersson
  orthogonal complement of the span of the level raises `V_d` from proper divisor levels
  (VERIFIED by reading `Newforms/Basic.lean:105, 202`). This is Miyake's primitive form.
- `coeff f n = (qExpansion 1 f.toCuspForm).coeff n` (Mathlib's q-expansion; the width of `Γ₁(N)`
  at `∞` is 1).
- `rootNumber f hχ = i² · f.frickeSign hχ`. This is the sign in Tau Ceti's proved functional
  equation `Λ_N(2 − s, f) = rootNumber · Λ_N(s, f)`, with `Λ_N(s) = N^{s/2}(2π)^{−s}Γ(s)L(f, s)`
  (`frickeCompletedL_sub_eq`, `frickeCompletedL_eq_cpow_mul_Λ`). It is therefore the classical
  root number, whatever the normalization of the Fricke involution, because `Λ_N ≢ 0`.
- `chiD D n = (n / |D|)` (Mathlib `jacobiSym`). For `D ≡ 1 (mod 4)` a fundamental discriminant this
  is the Kronecker character `χ_D` of `ℚ(√D)` (STANDARD, by quadratic reciprocity). It was also
  checked on 6000 pairs `(D, n)`, with 0 mismatches (VERIFIED, `check_chiD.py`).
- `IsOddImagFundDisc D`: `D < 0 ∧ D % 4 = 1 ∧ Squarefree D`.
- `HeegnerHyp N D`: `∀ p prime, p ∣ N → jacobiSym p |D| = 1`, i.e. `χ_D(p) = 1`, i.e. `p` splits
  in `ℚ(√D)`. At `p = 2` this is `D ≡ 1 (mod 8)` (VERIFIED on the same sample). For odd `D` it is
  equivalent to Gross–Zagier's condition "`D ≡ β² (mod 4N)`": Hensel at odd `p`, `D ≡ 1 (8)` at 2
  (STANDARD; rv-cr3-trust §2.1).
- `IsEntireCont a σ G`: `G` is entire and `G s = LSeries a s` for `Re s > σ`. Such a `G` is unique
  (`IsEntireCont.eq`), so no leaf depends on the choice of continuation.

### 2.3 L1 — Hecke–Shimura: the theta series of `ψ_d` is a newform

```lean
def HeckeThetaNewform : Prop :=
  ∀ d : ℕ, d % 4 = 1 → Squarefree d →
    ∃ (N : ℕ) (_ : NeZero N) (f : Newform N 2), f.χ = 1 ∧
      ∀ n : ℕ, n ≠ 0 → coeff f n = ZInQ.Contrib.HeckeFE.heckeCoeff d n
```

`heckeCoeff d n = ¼ ∑_{α ∈ ℤ[i], N(α) = n} (N(α)/d) u(α) α` is the n-th coefficient of the Hecke
L-series of the Grössencharacter `ψ_d` of `ℚ(i)` attached to `C_d` (`Contrib/HeckeFE/Basic.lean:473`).

- *Published statement* (UNVERIFIED locator; STANDARD content). Let `ψ` be a primitive Hecke
  character of an imaginary quadratic field `K`, of conductor `𝔪` and infinity type `α ↦ α^{k−1}`.
  Then `f_ψ = ∑_𝔞 ψ(𝔞) q^{N𝔞}` is a primitive form (newform) in `S_k(Γ₀(|d_K| N𝔪), χ_K ω_ψ)`
  (Miyake, Thm 4.8.2; Iwaniec, *Topics*, Thm 12.5; Hecke; Shimura 1971). For `ψ_d`: `k = 2`,
  `|d_K| N𝔪 = 32 d²`, and the character `χ_{−4} ω_{ψ_d}` is trivial, since `ψ_d((m)) = χ_{−4}(m) m`
  for `m ∈ ℤ` prime to `2d`.
- *Not stronger than the source.* L1 asks less: some level `N` (the source gives `32d²`), trivial
  nebentypus (a consequence), and coefficient equality only for `n ≥ 1`. Deuring's identity
  `cdCoeff d n = heckeCoeff d n` is proved in Lean (`DeuringCd`), so L1 is equivalent to "`C_d` is
  modular, in L-series form, with a newform of trivial character". That is true by Shimura (and by
  BCDT).
- *Pins its object.* `f` is determined by its coefficients. Its level is then forced by strong
  multiplicity one, and L2 and L3 receive the same `N` and `f` from the glue.
- *Non-vacuous.* The hypotheses hold at `d = 5`; the conclusion is existential, so it is not
  vacuously true.

**Is modularity glue? No: it is a textbook leaf.** Why:

- (i) The modular transformation law of the weight-2 theta series `∑ ψ_d(α) α q^{N α}` (a rank-2
  lattice with the harmonic polynomial `α` and a congruence character) is in neither Mathlib nor
  Tau Ceti. tc-main has lattice theta series `Θ_L`, `θ_{γ+L}` of weight `rank/2`, their nebentypus
  and cusp behaviour (`ModularForms/ThetaSeries/`), but no harmonic-polynomial or
  Grössencharacter-weighted theta series. Size: large.
- (ii) Eigen-ness for `T_n`, `(n, N) = 1`, would be glue: multiplicativity of `heckeCoeff`
  (`HeckeFE.heckeMult`, `heckePrimePowSplit`, proved) together with Tau Ceti's criterion
  `heckeTNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul`. Size: medium.
- (iii) Newness is not in Tau Ceti in a form that applies: one needs primitivity of `ψ_d` ⇒ new
  (Miyake §4.8) or strong multiplicity one across levels. Size: medium to large.

With (i) as a smaller leaf ("`f_{ψ_d} ∈ S_2(Γ₀(32d²))`"), (ii) and (iii) would make L1 glue. A
geometric parametrization `X₀(N) → C_d` is not needed by any Lean statement here (see L3).

### 2.4 L2 — nonvanishing of central twisted values (Friedberg–Hoffstein)

```lean
def FHNonvanishing : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2) (hχ : f.χ = 1), rootNumber f hχ = -1 →
    ∀ B : ℕ, ∃ D : ℤ, D < -(B : ℤ) ∧ IsOddImagFundDisc D ∧ HeegnerHyp N D ∧
      ∀ G : ℂ → ℂ, IsEntireCont (twistCoeff f D) 2 G → G 1 ≠ 0
```

`twistCoeff f D n = aₙ(f) χ_D(n)`. The continuation `G` exists (G6, proved).

- *Published statement* (UNVERIFIED; from memory, SPECULATIVE in its exact form). Friedberg–Hoffstein
  (Ann. of Math. 142 (1995), Thm B). Let `π` be a cuspidal automorphic representation of
  `GL₂(𝔸_F)`, `S` a finite set of places, and `χ_v` (`v ∈ S`) prescribed quadratic local characters.
  If the twists with these local components have root number `+1`, then infinitely many quadratic
  characters `χ` with these local components have `L(½, π ⊗ χ) ≠ 0`. Earlier: Bump–Friedberg–Hoffstein
  (Invent. Math. 102 (1990)) and Waldspurger (Compositio Math. 54 (1985); Forum Math. 3 (1991)).
- *How L2 follows from it.* Take `π = π_f` and `S = {∞, 2} ∪ {p | N}`. Prescribe `χ_∞ = sign`
  (`D < 0`), `χ_p = 1` for `p | N` (`p` splits), and `χ_2` unramified if `2 ∤ N` (`D` odd). A
  quadratic `χ` is `χ_D` for a fundamental `D`; the local conditions make `D` odd, hence
  `D ≡ 1 (mod 4)` squarefree. For `(D, N) = 1`, `ε(f ⊗ χ_D) = ε(f) χ_D(−N) = (−1)(−1)(1) = +1`
  (STANDARD: Shimura; Atkin–Li, Invent. Math. 48 (1978); folded in). Infinitely many `D` give
  `D < −B` for every `B`. For `(D, N) = 1` the series `∑ aₙ(f)χ_D(n)n^{−s}` is exactly
  `L(f ⊗ χ_D, s)` of the primitive twist, whose value at the centre `s = 1` is `L(½, π ⊗ χ_D)`.
- *Not stronger than the source.* The hypothesis is the root-number condition, and the conclusion
  is FH's conclusion restricted to the stated local conditions.
- *Non-vacuous.* `rootNumber = −1` holds for the newform of `C_5` (analytic rank 1, so G3 applies).
  For 16 values of `d`, a `D` with these conditions and `L(C_d^D, 1) ≠ 0` was found numerically
  with `|D| ≤ 455` (rv-cr3-trust §2.1, `out_indep_check.txt`).
- *Open question* (cr3-trust §2.4 item 3, rv-cr3-trust §2.2). Does the cited theorem allow the
  level `N = 32d²` (even, not squarefree)? FH 1995 is stated for general `π` (SPECULATIVE); BFH
  1990 may restrict the level. A human must check the printed theorem.

### 2.5 L3 — Gross–Zagier with Gross's conjugation relation

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

- *Published statements* (UNVERIFIED locators).
  - Gross–Zagier (Invent. Math. 84 (1986), Thm I.6.3; elliptic-curve form in Ch. V). For `E` with
    a modular parametrization `φ : X₀(N) → E` and `K` with the Heegner hypothesis,
    `L'(E/K, 1) = c · ĥ(y_K)` with `c ≠ 0`, where `y_K = Tr_{H/K} φ(x₁) ∈ E(K)` and
    `L(E/K, s) = L(f, s)L(f ⊗ χ_D, s)`.
  - Gross (1984, §5) and GZ. Complex conjugation acts by `ȳ_K = −ε y_K` modulo torsion, where `ε`
    is the root number of `E`.
- *How L3 follows* (all STANDARD).
  - The hypotheses give `L(f, 1) = 0`, so `L'(E/K, 1) = L'(f, 1) L(f ⊗ χ_D, 1) ≠ 0`.
  - Then `ĥ(y_K) ≠ 0`, so `y_K` has infinite order. This uses nondegeneracy of `ĥ`, which is
    proved in Tau Ceti (`Affine.Point.canonicalHeight_eq_zero_iff_isOfFinAddOrder`, given a
    Northcott instance).
  - `ε = −1` by G3 (proved), so `σ y_K − y_K` is torsion.
  - `E` has a parametrization of level `N`. The strong Weil curve `E_f` has one (Eichler–Shimura,
    Shimura 1971 Thm 7.14-7.15). `aₙ(E) = aₙ(f)` for all `n` gives `E ∼ E_f` (Faltings 1983,
    Kor. 2; for CM curves also Shimura, Nagoya Math. J. 43 (1971)). Composing with the isogeny
    gives a parametrization of `E`.
  - The statement for an abstract `K` with `[K:ℚ] = 2` and `δ² = D` follows by transport along
    `K ≅ ℚ(√D)`.
- *Why these pieces are folded into one leaf.* The Heegner point `y_K` cannot be named in Lean
  today (§4). Splitting the GZ formula and the conjugation relation into two leaves would have to
  quantify `y` existentially in each. Then nothing ties the `y` of one leaf to the `y` of the
  other, and the glue becomes unprovable (the defect rv-g0pieces found). Worse, "`∃ c ≠ 0, ∃ y,
  L'(E/K,1) = c ĥ(y)`" is equivalent to "`L' ≠ 0 → ∃ y` of infinite order", so it says nothing
  about the Heegner point. One leaf with one existential `y` is the finest faithful statement.
  This is the precedent of h-decomposition, which folded Lemma P because polarizations cannot be
  stated.
- *Not stronger than the source.* The hypotheses imply GZ's: Heegner, `(D, N) = 1`, `D` odd,
  `D ≠ −3, −4`, `L'(E/K,1) ≠ 0`. The conclusion is satisfied by `y_K`.
- *Non-vacuous.* Take `E = C_5`, `f` its newform (L1), and a Heegner `D` with `L(C_5^D, 1) ≠ 0`
  (rv-cr3-trust §2.1 numerics).

---

## 3. Glue (step 3): all proved

All glue is in `Contrib/GZDecomp/Decomp.lean`.

- **G1 `modular_cd`** (12 lines). `HeckeThetaNewform → d % 4 = 1 → Squarefree d → ∃ N f, f.χ = 1 ∧
  ∀ n ≠ 0, coeff f n = (C_d).LFunction n`. Proof: L1, then `deuringCd_of_gaussPointCount` and
  `LFunction_cd_apply'`.
- **G2 `isEntireCont_of_isLContinuation`**. `IsLContinuation E F` (from `Re s > 3/2`) together
  with matching coefficients gives `IsEntireCont (coeff f) 2 F`. Proof: `LSeries_congr`.
- **G3 `signOfSimpleZero`** (≈90 lines). Tau Ceti: `Λ_N(2 − s) = w Λ_N(s)` with `w = ±1`. If
  `w = 1`, write `F = w̃ · Λ_N` with `w̃(s) = 2Γ_ℂ(s)⁻¹N^{−s/2}` entire and `w̃(1) = 2πN^{−1/2} ≠ 0`.
  Then `F(s)w̃(2 − s) = w̃(s)F(2 − s)`. Write `F = (s − 1)g` near 1 with `g(1) ≠ 0`. This gives
  `(s − 1)(g(s)w̃(2 − s) + w̃(s)g(2 − s)) = 0` near 1, so `2g(1)w̃(1) = 0` by continuity, a
  contradiction. Uses `CuspForm.eq_strictWidthInfty_cpow_mul_L` to identify `F` with Mathlib's
  `ModularForm.L`.
- **G4 `exists_rat_point_of_heegner`**. With `σ ≠ 1` (`IsQuadraticExtension.exists_algEquiv_ne_one`),
  `z = y + σy` is `σ`-fixed (`σ² = 1`), so `z` is a base change of a point of `E(ℚ)`
  (`exists_baseChange_eq_of_map_eq`, Tau Ceti). Also `2y = z − (σy − y)`, so `z` has infinite
  order.
- **G5 `exists_quadratic_field`**. `AdjoinRoot (X² − C D)`, which is irreducible because `D < 0`,
  has `finrank 2` and contains `√D`.
- **G6 `exists_isEntireCont_twist`**. `CuspForm.twist (chiDMod D)` at level `N|D|²` has
  coefficients `χ_D(n)aₙ(f)` (`CuspForm.qExpansion_twist_coeff`), and its L-function
  `ModularForm.L` is entire.
- **G0 `grossZagierCd_of_leaves`, `grossZagierCd_of_leaves'`**. The route of §2.1.

---

## 4. What Mathlib and Tau Ceti provide, and what is missing

**Used (vendored or Mathlib):**

| Need | Supplier | Used in |
| --- | --- | --- |
| newforms, q-expansion | TC `HeckeRing.GL2.Newform`; Mathlib `qExpansion` | L1-L3 |
| entire `L(f, s)`, `Λ(f, s)` | Mathlib `ModularForm.L`, `Λ`; TC `CuspForm.differentiable_L`, `LSeries_qExpansion_coeff_eq`, `eq_strictWidthInfty_cpow_mul_L` | G3, G6 |
| functional equation with sign `±1` | TC `Newform.frickeCompletedL_sub_eq`, `I_zpow_mul_frickeSign_eq_one_or_neg_one` | G3; `rootNumber` |
| twist of a cusp form | TC `CuspForm.twist`, `qExpansion_twist_coeff` | G6 |
| quadratic-extension Galois facts, point descent | TC `Algebra.IsQuadraticExtension.*`, `Affine.Point.exists_baseChange_eq_of_map_eq` | G4 |
| `L(C_d, s)` as the Hecke series of `ψ_d`, Deuring | project `HeckeFE`, `HeckeAll`, `GaussFE` | G1 |
| Néron–Tate height, nondegeneracy | TC `Affine.Point.canonicalHeight`, `canonicalHeight_eq_zero_iff_isOfFinAddOrder` (vendored, `CanonicalHeight/Basic.lean`) | inside L3 (cannot be split off, §2.5) |

**Missing definitions for a finer L3 and for a geometric L1** (h-decomposition's tiers):

| Missing | Needed for | Status in Mathlib / Tau Ceti | Size |
| --- | --- | --- | --- |
| coarse moduli `Y₀(N)` and its compactification `X₀(N)` over `ℚ` | the parametrization, Heegner points | tc-main has the Katz–Mazur moduli problem `[Γ₀(N)]` (`ModularCurve/Gamma/Zero.lean`) and `Y₁(N)` for `N ≥ 4`; no coarse quotient, no compactification | very large |
| `J₀(N)`, the Eichler–Shimura quotient, morphisms `X₀(N) → E` over `ℚ` | splitting off Eichler–Shimura / Shimura 1971 and Faltings | missing (no Jacobians of curves) | very large |
| CM points on `X₀(N)` and the main theorem of CM (`x₁ ∈ X₀(N)(H)`) | defining `y_K` | Hilbert class field and Artin map in TC CFT (prereq-survey row B3); main theorem of CM not found | large |
| the theta series of a Grössencharacter as a modular form | making L1 glue | tc-main: lattice theta series only | large |
| isogeny theorem (Faltings) as a Lean statement | splitting off Faltings | TC has isogenies of elliptic curves (`EllipticCurve/Isogeny/`), so the statement is possible; not needed by the present L3 | small to state |

Once `X₀(N)`, `φ` and `x₁` exist, L3 splits into: GZ's formula
`L'(E/K,1) = c·ĥ_K(y_K)` (over Mathlib's `WeierstrassCurve.LFunction` for the number field `K`),
Gross's `ȳ_K = −ε y_K`, the factorization `L(E/K) = L(E)L(E^D)`, and the existence of `φ`, with
nondegeneracy of `ĥ` and G4 as glue.

---

## 5. Review pass (step 4): each leaf against its source, adversarially

**Do the clauses pin their objects?**

- L1: `f` is pinned by all of its coefficients; `N` and `χ = 1` follow.
- L2: `D` is existential, but the glue passes it to L3 unchanged, so nothing needs to agree
  across leaves except `N` and `f`. Both are explicit arguments.
- L3: `y` is existential and is consumed only inside L3's own conclusion, by G4. This is the
  rv-g0pieces lesson applied: the GZ formula and the conjugation relation are in one leaf
  (§2.5).
- `K` is universally quantified in L3. The glue supplies a concrete field (G5). Any field with
  `[K:ℚ] = 2` and `δ² = D` is `ℚ(√D)`, so the clause pins `K` up to isomorphism.

**Could a leaf be vacuous?**

- L1: no; its hypotheses hold at `d = 5`.
- L2: no; its hypothesis `rootNumber = −1` holds for the newform of `C_5` (G3 with
  `ord_{s=1} L(C_5, s) = 1`, cr3-trust A6/rv-cr3-trust numerics).
- L3: no; every hypothesis is met by `C_5`, its newform and a Heegner `D` from the numerical
  search. `D < −4` excludes only `D = −3`, which L2 never has to supply: `B = 4` in the glue.

**Could a leaf be stronger than its source?**

1. *L1, the nebentypus.* L1 asserts `f.χ = 1`. Miyake's character is `χ_{−4}·ω_ψ`. For `ψ_d`,
   `ψ_d((m)) = χ_{−4}(m)·m` for `m` prime to `2d`. So `ω = χ_{−4}` and the product is trivial
   (checked by hand from the definitions, `HeckeFE/Basic.lean:443-475`:
   `unitOf(α mod 4)·α` is the primary associate of `α`, `≡ 1 (mod 2+2i)`, so for odd `m ∈ ℤ` it is
   `χ_{−4}(m)·m`, and `(m²/d) = 1` for `m` prime to `d`). In any case L1 is equivalent, by the proved Deuring identity, to
   modularity of `C_d` with a trivial-character newform. That is true, because an elliptic curve
   over `ℚ` corresponds to a newform on `Γ₀(N)`. **No defect.**
2. *L1, newness in Tau Ceti's sense.* Newness is Petersson-orthogonality to all level raises from
   proper divisor levels (Diamond–Shurman §5.6). This is the classical notion. **No defect.**
3. *L2, the level.* FH 1995 is believed to cover every level; BFH 1990 may not. The leaf cites FH
   first. **Open: a human must check the printed hypotheses of FH Thm B** (cr3-trust §2.4 item 3).
4. *L2, the root-number hypothesis.* `rootNumber` is defined through Tau Ceti's functional
   equation, so it is the classical `ε(f)` (§2.2). The compatibility `ε(f⊗χ_D) = +1` needs
   `(D, N) = 1`, which `HeegnerHyp` implies (`χ_D(p) = 1 ≠ 0`). **No defect.**
5. *L2 and L3, the twisted series.* For `(D, N) = 1` the twist is primitive at level `ND²`, so
   `∑ aₙχ_D(n)n^{−s}` is the full L-function with no missing Euler factors. **No defect.**
6. *L3 for every `E` with matching coefficients.* This needs Faltings' isogeny theorem, folded in
   and cited. Restricting L3 to the curves `C_d` would let Shimura 1971 replace Faltings. The
   restriction is possible but was not made, because both are published. **No defect.**
7. *L3, the sign convention.* `σy − y` torsion corresponds to `ȳ_K = −ε y_K` with `ε = −1`. With
   the opposite convention (`ȳ_K = ε y_K`) the conclusion would be `σy + y` torsion. With
   `ε = −1`, analytic rank odd and `y_K` lying in the `E(ℚ)`-part of `E(K) ⊗ ℚ`, the stated form
   is the one consistent with BSD parity and with GZ's corollary that `rank E(ℚ) ≥ 1` (STANDARD).
   The opposite reading would put `y_K` in `E^D(ℚ)`, whose L-value at 1 is nonzero. **No
   defect.** The exact printed formula is UNVERIFIED.
8. *`chiD` and `HeegnerHyp` are the intended characters.* STANDARD and checked numerically (§2.2).
   **No defect.**

**Review outcome.** No statement needed a repair. One open check is recorded: the level
hypothesis of FH/BFH (item 3).

---

## 6. Vendoring

243 oct16 modules were added with `tcport.py ~/tc-oct16` (commit 5a01f5fe3621): the closure of
`ModularForms.LFunction.Sign`, `ModularForms.Twist.Basic`, `EllipticCurve.CanonicalHeight.Basic`,
`EllipticCurve.MordellWeil.NaiveHeight` and `EllipticCurve.GaloisDescent`, minus 14 already
vendored. The list is in `scratch/gz-decomp/tc-modules.txt`. Two port fixes, each marked in the
file:

- `NumberTheory/ModularForms/Basic.lean`: explicit `UpperHalfPlane ℂ` outParams of `IsSMulApply`
  (as tc-port 312eaee4). The file is taken byte-identical from `wip/t25-newform`, which vendored
  it with the same fix, so a merge adds identical content. The other 242 files that both
  branches add are identical too (checked with `git diff`).
- `NumberTheory/ModularForms/LFunction/Sign.lean`: `ModularForm.L_apply_of_ne_zero` does not exist
  in Mathlib 56a00585; `ModularForm.L` is unfolded instead.

The build succeeded with no `sorry` warning (VERIFIED). The axioms of the vendored constants used
are covered by `#print axioms` of the GZDecomp theorems.

## 7. Reproduction

```
lake build ZInQKernel.Contrib.GZDecomp.Decomp
lake env lean scratch/gz-decomp/Check.lean      # types and #print axioms
python3 -I scratch/gz-decomp/check_chiD.py       # chiD = Kronecker, 6000 pairs
```

PARI checks of conductors, root numbers and twists could not be rerun: `~/pyenv` is missing on
this host, `cypari2` is not cached, and there is no network. The earlier numerics of
rv-cr3-trust §2.1 are cited instead.
