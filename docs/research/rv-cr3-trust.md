# rv-cr3-trust: adversarial review of the CR₃ trust statement (`cr3-trust.md`)

Status: review note (task rv-cr3-trust, 2026-11-11). Reviewed: `docs/research/cr3-trust.md` (written at
base `14b28b23`), against the Lean files at `8b71bfdf` (branch `wip/rv-cr3-trust`), `KERNEL_PLAN.md`,
the notes it cites, and `docs/research/rv-prop-n.md` (which cr3-trust could not use). Log and scripts:
`scratch/rv-cr3-trust/`. No file under `ZInQKernel/`, `blueprint/` or other notes was edited.

Marks: **VERIFIED** (checked here: Lean source, a Lean run, or a script under `scratch/rv-cr3-trust/`),
**STANDARD** (published mathematics, locator given or named as missing), **SPECULATIVE** (assessment),
**UNVERIFIED** (a locator no one here could read; there is no network).

## Verdict

**Adopt after the listed repairs (§6).** The mathematical route of cr3-trust §1 (TYZ inputs →
Proposition N → analytic rank one → Gross–Zagier with an auxiliary field → point of infinite order) is
complete, and I found no gap in it. The Lean side is as claimed, except for one false statement about
the implication graph. The repairs:

1. **Wrong implication claim (§0.2, Summary 1, §3 docstring for `CertifiedRankTYZClRk`).**
   cr3-trust says `CertifiedRankTYZClRk` does not imply `CertifiedRankTYZ`, `CertifiedRankTYZCl`,
   `CertifiedRank5b` "because of the extra premise `#Sel₂ = 8`". That is false. The premise is a premise
   of the *target* forms, so it only makes them weaker. Lean proves all three from
   `CertifiedRankTYZClRk` by composing existing theorems (VERIFIED, `scratch/rv-cr3-trust/Check.lean`,
   §1.1). So `CertifiedRankTYZClRk` implies **every** form. The draft docstring clause "It implies
   every other form of CR₃ except the three …" must be replaced.
2. **§0.3 is out of date.** Both variants that cr3-trust calls missing now exist:
   `…_sixContactMin_certifiedRank5b` (`RouteK/Rank5bSec3.lean:51`, without 22P) and
   `…_sixContactMin_certifiedRankDLAdmRk` (`RouteK/RankDL.lean:232`). So there are now 14 forms with
   main-theorem variants, not 13. Some line numbers have moved.
3. **D2 supplier.** For analytic rank one, the auxiliary field needs a *nonvanishing central value*
   `L(C_d^K, 1) ≠ 0`. Murty–Murty 1991 is the theorem for *derivatives*, which serves the analytic-rank-0
   case of Gross–Zagier–Kolyvagin. Cite Bump–Friedberg–Hoffstein (or Waldspurger, or
   Friedberg–Hoffstein 1995). Also add the level condition `N = 32d²` (even, not squarefree) to the
   locator check (§2.2).
4. **Statuses after rv-prop-n.** C1–C3 go to [M2] (rv-nt-tyz, rv-prop-n; no human review), and
   rv-prop-n's three corrections are applied in B5, B8 and C3. A1 has two reviews and A2 has three.
5. **Small completeness and honesty repairs:**
   - locators for the complex-conjugation sign relation in D3 and for Shimura 1971 in D1;
   - a sentence on Mathlib's group law in A5;
   - in A6, `ellrank`'s lower bound `1` is not certified on the 6 curves with no point;
   - rv-cr3-rank (the supplier of A5 and E3) is still unmerged;
   - KERNEL_PLAN.md and three Lean docstrings still lead with Kriz or "Gross–Zagier–Kolyvagin".

None of these changes the route or the residual list in substance. Repair 1 makes the trust
statement *stronger*, not weaker.

## 1. Completeness (question 1)

### 1.1 The Lean implication graph (VERIFIED)

Every arrow of cr3-trust §0.2 exists under the stated name, with no hypotheses beyond the source form
(checked by reading at `8b71bfdf`). The one false claim is the paragraph after the diagram. The
following compositions are Lean theorems (`scratch/rv-cr3-trust/Check.lean`, §1.4):

```
TYZClRk ─Redei.certifiedRankTYZRk_of_certifiedRankTYZClRk─▶ TYZRk ─certifiedRankTYZ_of_certifiedRankTYZRk'─▶ TYZ
TYZ ─certifiedRank5b_of_certifiedRankTYZ─▶ 5b
TYZClRk ─certifiedRankTYZCl_of_certifiedRankTYZClRk'─▶ TYZCl
TYZClRk ─▶ TYZRk ─certifiedRankDLRk_of_certifiedRankTYZRk─▶ DLRk ─certifiedRankDLAdmRk_of_certifiedRankDLRk─▶ DLAdmRk
```

So `CertifiedRankTYZClRk` implies all 14 forms. cr3-trust's own remark that the three `#Sel₂ = 8`
forms are "logically stronger than `CertifiedRankSel`" is correct, and it does not conflict with this.

### 1.2 The outline against the published argument

I checked the chain from TYZ to the Lean statement step by step.

- **Statement match (A1–A3).** `gCl`, `T5bCl`, `Admissible5bNat` and the premises were reread here
  (`RedeiStatement.lean:33-57`, `Sec3/Defs.lean:85-88`). The sum runs over `Finpartition univ` of the
  primes, so each set partition is counted once with nonempty blocks. There is exactly one block
  `≡ 7`, exactly one `≡ 3`, and all blocks lie in `{1, 3, 7} (mod 8)`. `gCl` is `#Cl²` of the full ring
  of integers of `ℚ(√−n)`; `QNeg n` is a field for `n ≠ 0` and `dProd B ≠ 0` (`neZero_dProd`). This is
  Proposition N's `T_5b(n)` (VERIFIED by reading; agrees with rv-redei §1, rv-cr5b-sec3 §1,
  rv-prop-n §1).
- **The curve (A4).** `E_n : ny² = x³ − x` goes to `C_n : y² = x³ − n²x` under `(x, y) ↦ (nx, n²y)`: with
  `X = nx`, `Y = n²y` one gets `Y² = n³(x³ − x) = X³ − n²X` (VERIFIED by hand). Lean's curve is
  `shortCurve (−(d:ℚ)²)` in every form (VERIFIED by reading).
- **"Point of infinite order" (A5).** The conclusion is `∃ P, ¬IsOfFinAddOrder P` in Mathlib's
  `WeierstrassCurve.Affine.Point` group (rv-cr3-rank checked that the instance is Mathlib's
  `Point.instAddCommGroup`). cr3-trust does not say why Gross–Zagier's point, which has infinite order
  for the classical group law, has infinite order in Lean. The reason is that Mathlib's addition is the
  chord-tangent law, with the formulas of Silverman III.2.3 (STANDARD). The `Inf` forms make this
  question moot: `InfinitelyManyPoints d` (`RankInf.lean:32`) is `Set.Infinite {p : ℚ × ℚ | p.2² =
  p.1³ − d² p.1}`, which uses no group law, and Lean proves `XInf ↔ XRk`
  (`RankInf.lean:148-164`, through `fg_points`). *Repair:* add one sentence to A5.
- **The Selmer premise in the non-`Rk` forms.** It is a premise. The derivation of these forms from
  `CertifiedRankTYZClRk` is Lean-proved (RK9 with `fg_points`) relative to Lean's own `Sel2`. So whether
  `Sel2` is the textbook Selmer group affects only how those forms read, not whether
  `CertifiedRankTYZClRk` justifies them. The textbook match is rv-cr3-rank §1 and descent-alt
  (Proposition 0, Lean-proved).
- **TYZ → Proposition N → analytic rank one (B, C).** No step is skipped relative to nt-tyz §4 as
  reviewed by rv-nt-tyz and rv-prop-n. Two details from rv-prop-n are missing in cr3-trust:
  - the inclusion `ℍ'_{d₀} ⊂ ℍ'_n` in B5 is a quoted TYZ fact, not part of a definition;
  - one lift `β'` is used for all `Z(e)` at once (B8).
- **Analytic rank one → point (D).** Complete apart from the locators in §2.
- **The `Inf` and `DL` forms.** Covered by Lean equivalences and implications. `DLAdmRk` now has a
  variant (repair 2).

### 1.3 Kolyvagin on the route (STANDARD, by reading)

TYZ's definition of `𝓛(n)` uses, when `ord = 1`, the regulator of a generator of `E_n(ℚ)/tors`. TYZ
cite Coates–Wiles, Rubin, Gross–Zagier and Kolyvagin for this (B9; rv-cr5b-sec3 §2.2). The proof of
Theorem 3.3 uses Kolyvagin too (B4). So Kolyvagin's *published* papers are on the route, inside TYZ.
cr3-trust says so in D3 and in its drafts ("enter only inside TYZ"). That is honest. Any shortened
wording must not become "Kolyvagin is not needed".

Note that, given B9, TYZ's framework already presupposes `rank = 1` when `ord = 1`. So D is
logically redundant. It is still worth keeping, because it makes the final step independent of
Kolyvagin and of the definition of `𝓛(n)`.

### 1.4 Lean run (VERIFIED)

The modules `RouteK.RankDL`, `RankVariants`, `Rank5bSec3` and `RankInf` were built with `lake build`
(9843 jobs, success). `lake env lean scratch/rv-cr3-trust/Check.lean` then elaborates four
compositions without error (output: `out_check_lean.txt`):

- `CertifiedRankTYZClRk → CertifiedRankTYZ`
- `CertifiedRankTYZClRk → CertifiedRankTYZCl`
- `CertifiedRankTYZClRk → CertifiedRank5b`
- `CertifiedRankTYZClRk → CertifiedRankDLAdmRk`

`#print axioms` gives exactly `[propext, Classical.choice, Quot.sound]` for those four, for the two
new variants (`…_sixContactMin_certifiedRank5b`, `…_sixContactMin_certifiedRankDLAdmRk`), for the
`…TYZClRk` variant and for `certifiedRankTYZClInf_iff_certifiedRankTYZClRk`.

## 2. The analytic-to-algebraic step (question 2)

**Claim:** `ord_{s=1} L(C_d, s) = 1` gives a point of infinite order on `C_d(ℚ)` from:
- modularity of `C_d` (CM);
- an imaginary quadratic `K` with the Heegner hypothesis for `N = 32d²` and `L(C_d^K, 1) ≠ 0`;
- Gross–Zagier;
- the action of complex conjugation on the Heegner point.

Verdict: **correct**, with these remarks.

### 2.1 What was checked

- **Modularity (D1).** The step needs a nonconstant map `X_0(N) → C_d`, not only `L(C_d, s) = L(f, s)`.
  Shimura proved this for CM curves (G. Shimura, *On elliptic curves with complex multiplication as
  factors of the Jacobians of modular function fields*, Nagoya Math. J. 43 (1971), 199–208;
  UNVERIFIED locator, STANDARD content). BCDT is not needed. Alternatively, `C_1` is `X_0(32)` and
  `C_d` is its quadratic twist by `χ_d`. *Repair:* give the Shimura locator in D1.
- **Conductor.** `N(C_d) = 32d²` for the 30 sample values (VERIFIED, `ellglobalred`). It is STANDARD
  for odd squarefree `d`.
- **Heegner hypothesis for every `d` in the forms.** For `p | d`, `p² ‖ N`; "`p` splits" is enough for an
  ideal `𝔫` with `𝒪/𝔫 ≅ ℤ/N`. At 2, `D` must be a square mod `4N = 128·d²`. For odd `D` this holds at 2
  exactly when `D ≡ 1 (mod 8)`. Fundamental `D < 0` with these splitting conditions exist for every
  `d` by CRT and Dirichlet (STANDARD).
- **Root number of the twist.** For `(D, N) = 1`, `ε(C_d^D) = ε(C_d) χ_D(−N) = (−1)·(χ_D(−1) χ_D(N)) =
  (−1)(−1)(1) = +1`. So asking for `L(C_d^D, 1) ≠ 0` is consistent with the sign (STANDARD). The root
  number `ε(C_d) = −1` was VERIFIED on the 30 sample values.
- **Non-vacuity, numerically.** For the first 16 sample values (§4.2), a `D` with these conditions and
  analytic rank 0 for `C_d^D` exists, with `|D| ≤ 455` (VERIFIED numerically,
  `out_indep_check.txt`).
- **Gross–Zagier and the trace (D3).**
  - `L'(C_d/K, 1) = L'(C_d, 1) L(C_d^K, 1) ≠ 0`, so the Heegner point `y_K ∈ C_d(K)` has infinite
    order.
  - Complex conjugation acts by `ȳ_K = −ε(C_d) y_K^σ` up to torsion (Gross–Zagier 1986; B. Gross,
    *Heegner points on X_0(N)*, in *Modular forms* (Durham 1983), 1984; UNVERIFIED locators).
    Because `y_K` is the trace from the Hilbert class field and `ε = −1`, `y_K + ȳ_K = 2y_K + (torsion)`
    has infinite order.
  - cr3-trust states the conclusion but gives no locator for the sign relation. *Repair:* add one.
- **Kolyvagin, BCDT, Kriz are not needed for D** (STANDARD). Only `rank ≥ 1` is used, and RK9 does
  the rest without finiteness of `Ш`.

### 2.2 The D2 supplier (repair 3)

- **Murty–Murty does not fit.** M. R. Murty, V. K. Murty, *Mean values of derivatives of modular
  L-series*, Ann. of Math. 133 (1991), 447–475, is, by its title and its usual role, the theorem that
  produces twists with `L'(E^D, 1) ≠ 0`. That is the input for curves of analytic rank 0. D2 needs
  `L(C_d^K, 1) ≠ 0`.
  - Status: STANDARD that the two cases need different theorems. The text of MM's theorem is
    UNVERIFIED, so it is possible that MM also contains a value version. Until someone checks, MM
    should not be the cited supplier.
- **Suppliers that fit:**
  - Bump–Friedberg–Hoffstein 1990 (values and derivatives);
  - Waldspurger;
  - S. Friedberg, J. Hoffstein, *Nonvanishing theorems for automorphic L-functions on GL(2)*, Ann. of
    Math. 142 (1995), 385–423. From memory, this is stated for general cuspidal representations with
    prescribed local behaviour at finitely many places (SPECULATIVE, UNVERIFIED).
- **Level check.** cr3-trust §2.4 item 3 asks to check "the non-vanishing theorem with prescribed local
  conditions". It should also ask whether level `32d²` (even, not squarefree) is allowed. Some early
  nonvanishing results restrict the level (SPECULATIVE).

### 2.3 The forms whose conclusion is every Selmer class (VERIFIED)

`CertifiedRank`, `CertifiedRankSel`, `CertifiedRankTYZ` and `CertifiedRankTYZCl` come from the `Rk`
forms by these theorems:

| Form | Lean theorem | File |
| --- | --- | --- |
| `CertifiedRank` | `certifiedRank_of_certifiedRankRk'` | `RankVariants.lean` |
| `CertifiedRankSel` | `certifiedRankSel_of_certifiedRankRk'` | `RankVariants.lean` |
| `CertifiedRankTYZ` | `certifiedRankTYZ_of_certifiedRankTYZRk'` | `RankVariants.lean` |
| `CertifiedRankTYZCl` | `certifiedRankTYZCl_of_certifiedRankTYZClRk'` | `RankVariants.lean` |

Each applies `loc_of_mem_sel2_of_infinite_order` with `fg_points_all` (RK9 and Mordell–Weil). The
unprimed versions are in `Rank/Statements.lean` and take `hfg`. `CertifiedRank5b` comes from
`CertifiedRankTYZ` (`certifiedRank5b_of_certifiedRankTYZ`). No Kolyvagin, Cassels–Tate or finiteness
of `Ш` enters. cr3-trust's claim holds; the only correction is §1.1.

## 3. Suppliers and statuses (question 3)

| Step | cr3-trust status | Assessment |
| --- | --- | --- |
| A1 | [M1] + read | **[M2]**: rv-prop-n §1 also checks `gCl` = TYZ's `g` |
| A2 | [M2] + read | [M3] (rv-redei, rv-cr5b-sec3, rv-prop-n) + reread here |
| A3 | [M2] | fine; reread here |
| A4 | VERIFIED | fine (rechecked) |
| A5 | [M1] + read; `Inf` [L] | fine. The [M1] supplier rv-cr3-rank is on an unmerged branch (`origin/wip/rv-cr3-rank`, `aec3b570`, still not an ancestor of HEAD): merge it or cite it with its commit. Add the group-law sentence |
| A6 | [S] | fine. Reproduced independently (§4). On the 6 curves with no point, `ellrank`'s `[1, 1]` lower bound is not certified (it lists no point) |
| B1–B9 | [R] under the journal assumption | honest. The journal assumption is stated (§2.3). ARXIV-READ is a model reading, and the text says so |
| B5 | "a definition, not a theorem" | the inclusion `ℍ'_{d₀} ⊂ ℍ'_n` is a quoted TYZ fact (rv-prop-n §6): say so |
| B8 | "any lift `β'`" | "one lift `β'`, the same for all `Z(e)`" (rv-prop-n §6) |
| C1–C3 | [M1] | **[M2]**: rv-nt-tyz and rv-prop-n, both "holds"; no human review. C3: "F4 is not used" is already said; add rv-prop-n's list of the `ε`-classes used (`(5,1)`, `(7,1)`, `(7,3)`, as B4 already says) |
| C4 | [R] | fine |
| D1 | [R], locator UNVERIFIED | fine. Add the Shimura 1971 locator |
| D2 | [R], numbers UNVERIFIED | the supplier list is wrong in part: Murty–Murty (§2.2) |
| D3 | [R] | fine. Add the locator for the conjugation sign |
| E1–E3 | [L] | fine; axioms rerun here (log step 6) |

The marks are used consistently. No step is marked better than its weakest supplier, apart from the
small upgrades and downgrades above.

## 4. Definitional match and cr3-trust's own checks (question 4)

### 4.1 Coverage of each definition

- `T5b`: rv-cr5b-sec3 §1.4.
- `T5bCl` and `gCl`: rv-redei §1, rv-prop-n §1, and this review by reading.
- `Admissible5bNat`: read here.
- `Sel2` and `Loc`: rv-cr3-rank §1, plus Lean's Proposition 0.
- The curves: Lean, plus A4.
- `InfinitelyManyPoints`: read here and in cr3-trust. The equivalence with the `Rk` forms is [L].
- `Inputs`, `Slots`, `betaOf`, `thetaOf`, `Admissible`: rv-cr3-dl, and d2-check. `DLAdmRk` itself was
  read in cr3-trust only, and is read here again. It is implied by `DLRk` in Lean and implies pole
  completeness in Lean, so its own faithfulness matters only for reading it.

Every part is covered by a model review or a Lean theorem.

### 4.2 Independent recheck of A6 (VERIFIED, `scratch/rv-cr3-trust/indep_check.py`)

- **Method.**
  - `T5bCl` is computed from its Lean definition, with exact class numbers obtained by counting
    reduced forms (no PARI), and `#Cl² = h/2^{t−1}` by genus theory.
  - `dim Sel₂` comes from PARI `ell2cover`. That is independent of `mirror.py`, which cr3-trust used.
    It was calibrated on `d = 1, 5, 34, 1254`, which give `2, 3, 4, 5`.
- **Count.** The squarefree `d ≡ 5 (mod 8)` below 30000 with 3 to 5 primes and `T5bCl d = 1` number
  **386**. That matches cr3-trust's count of `T5b d = 1`, as `T5bCl_eq_T5b'` requires.
- **Sample.** 30 values, `L[6::13]`, disjoint from cr3-trust's sample:
  - `dim Sel₂ = 3` (`#Sel₂ = 8`) on all 30;
  - root number `−1` on all 30;
  - conductor `32d²` on all 30;
  - a Heegner field with `L(C_d^D, 1) ≠ 0` (numerical) on the first 16 (the run was split by the
    10-minute cap: `out_indep_check.txt` and `out_indep_check_part2.txt`).
  - Failures: 0.
- **Soundness of cr3-trust's A6.**
  - Its arithmetic claims are reproduced.
  - Its analytic rank is numerical, and the text says so.
  - Its claim "`ellrank` gives `[1, 1]`" is literal output. On the 6 curves without a point, the lower
    bound `1` is not witnessed (checked on `d = 10293`: output `[1, 1, 0, []]`). It rests on a parity
    step that is not a proof of positive rank. *Repair:* say so.
  - "Whether `T5b = 1` forces `#Sel₂ = 8` in general" is rightly marked SPECULATIVE. Nothing depends
    on it.

## 5. Residual list and draft docstrings (question 5)

### 5.1 The residual list (§2)

The list is right in substance. Changes:

- (i) Proposition N: **two** model reviews (rv-nt-tyz, rv-prop-n), not one.
- (ii) Single-review items: A1 now has two reviews. A5 still has one, on an unmerged branch.
- (iv) Locators:
  - item 3: drop Murty–Murty, or demote it to the derivative case, and add the level condition;
  - add Shimura 1971 for D1;
  - add the conjugation-sign locator for D3.
- §2.2 lists "Bump–Friedberg–Hoffstein 1990 or Murty–Murty 1991". Change it to "BFH 1990 (or
  Waldspurger; Friedberg–Hoffstein 1995)".

### 5.2 The drafts (§3)

- **`ZInQ.CertifiedRank`.**
  - Replace "(Bump–Friedberg–Hoffstein; Murty–Murty)" by "(Bump–Friedberg–Hoffstein)".
  - After "model review `docs/research/rv-nt-tyz.md`", add "and `docs/research/rv-prop-n.md`".
  - "Its proof is published mathematics plus one short repository argument" should add "and the match
    of the Lean definitions with TYZ's quantities (model reviews)". As written, it hides residual (ii).
  - The rest agrees with the outline and with Lean (names checked: `redeiFormula`, `det_M5b_eq_T5b`,
    `det_M5b_eq_one`, `prop0Statement`, `fg_points`, `loc_of_mem_sel2_of_infinite_order`,
    `certifiedRank_of_certifiedRankRk'`, `certifiedRankRk_of_certifiedRankTYZRk`,
    `Redei.certifiedRankTYZRk_of_certifiedRankTYZClRk`).
- **`CertifiedRankTYZClRk`.**
  - Replace "It implies every other form of CR₃ except the three with the premise `#Sel₂ = 8` … (those
    follow from their own `Rk` forms)" by "Lean derives every other form of CR₃ from it (the forms with
    the premise `#Sel₂ = 8` through RK9 and Mordell–Weil, `certifiedRankTYZ_of_certifiedRankTYZRk'`,
    `certifiedRankTYZCl_of_certifiedRankTYZClRk'`)".
  - Same Murty–Murty and rv-prop-n changes as above.
- **`CertifiedRankRk`.** Correct as drafted. Optionally add rv-prop-n.

### 5.3 Agreement with KERNEL_PLAN.md and the current docstrings

- KERNEL_PLAN.md:
  - lines 21 and 67–70 lead with Kriz, then "Tian–Yuan–Zhang with Gross–Zagier–Kolyvagin (only
    Gross–Zagier needed)";
  - it does not mention the two new variants;
  - lines 153–176 agree with Lean.
- `Hypotheses/CertifiedRank.lean` (Kriz first, "Gross–Zagier–Kolyvagin gives rank one"),
  `CertifiedRankRk` (Kriz first), and `CertifiedRank5b` ("Gross–Zagier and Kolyvagin (manuscript
  Lemma 5.5)") disagree with the drafts.

cr3-trust §4 lists the docstring alignment as a next step. When the drafts are adopted, KERNEL_PLAN
should be aligned too, and should list the new variants.

The docstrings of the two new variants are accurate:
- the 5b one says it goes through Corollary 4.4 and the Sel variant, and that the older variant takes
  22P;
- the DLAdmRk one says pole completeness comes from `poleCompleteness_of_certifiedRankDLAdmRk`.

The `CertifiedRankDLAdmRk` docstring has no trust paragraph of its own. It points to `DLRk`, which is
acceptable.

## 6. Repairs, by section of cr3-trust

- **Summary.**
  - Item 1: `TYZClRk` implies every form (delete "except …").
  - Count 14 forms.
  - Item 2: C1–C3 have two model reviews.
  - Item 3(a): "reviewed twice by a model".
  - Item 4: note that `ellrank`'s lower bound is uncertified on the 6 curves.
- **§0.1.** Table row `CertifiedRankDLAdmRk`: add its variant.
- **§0.2.** Replace the paragraph after the diagram with the compositions of §1.1. Update the locations
  (`Rank5bSec3.lean` lines 51, 64, 77).
- **§0.3.** Add `…_sixContactMin_certifiedRank5b` (`Rank5bSec3.lean:51`) and
  `…_sixContactMin_certifiedRankDLAdmRk` (`RankDL.lean:232`). Delete the recommendation that is now
  done.
- **§1 A1, A2.** Add rv-prop-n §1 as a review.
- **§1 A5.** Add the group-law sentence (§1.2). Merge or pin rv-cr3-rank.
- **§1 A6.** On the 6 curves, `ellrank`'s `r = 1` is not certified.
- **§1 B5.** The inclusion `ℍ'_{d₀} ⊂ ℍ'_n` is a quoted TYZ fact.
- **§1 B8.** One lift `β'` serves all `Z(e)`.
- **§1 C1–C3.** Status [M2] (rv-nt-tyz, rv-prop-n).
- **§1 D1.** Add the locator Shimura, Nagoya Math. J. 43 (1971).
- **§1 D2.** Drop Murty–Murty as the supplier (it is the derivative case). Add Friedberg–Hoffstein 1995
  as an option. Ask whether level `32d²` is allowed.
- **§1 D3.** Add a locator for `ȳ_K = −ε y_K^σ` mod torsion.
- **§2.1, §2.2, §2.4 item 3, §2.6.** Same changes as above.
- **§3.** The docstring edits of §5.2.
- **§4.** Mark the 5b variant as done. Add: align KERNEL_PLAN.md (lead with TYZ, list the new
  variants).
