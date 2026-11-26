# Adversarial AI readings: Cassels (1962), Theorem 1.1, for `hCT` (2026-11-26)

**Result.** The row `ZInQ.Manuscript.SelmerTwoPower.CasselsIVThm11Elliptic`
(`ZInQKernel/Contrib/OneProof/CasselsIV/Row.lean`, #217) matches its printed source, and every lens passed it. It
is Cassels's Theorem 1.1 at `k = ℚ`, for every elliptic curve over `ℚ`: a direct instance of the print, with one
weakening ("naturally-defined" is dropped). No reader found a clause stronger than the print, a missing hypothesis,
a quantifier or slot error, or a definition that differs from the printed notion beyond the identifications recorded
below.

The field `hCT` of `ZInQ.OneProof.frozenTarget` is not this row but the weaker form printed by Poonen–Stoll,
`PoleS12.CasselsTatePairingCurvesPS`, which Lean proves from it (§5).

No person has read these pages. Under the maintainer's ruling of 2026-11-26 (STATEMENT-CHECKS.md, "Adversarial AI
readings"), with no human reader available, this adversarial AI reading stands in for the human reading. The
evidence stays AI-READ.

The row was read at `a068c9136` (the head of #217 when it was read). Its statement is unchanged on main at
`8e353c213`. The only later edits to `CasselsIV/Row.lean` are docstrings, made in answer to two readers: the
Weil–Châtelet correspondence is now cited from §1, p. 98 (with footnote 12) as well as p. 108, and the docstring of
the per-curve helper `CasselsIVThm11` now says that it is not the row (see §3).

## 1. Method

Three independent AI readings of the row. Each worked from page images rendered from the PDF at 150 dpi, not from a
text layer (the scan has none). Each gives verbatim quotes and printed page numbers. The three readers ran on three
different model families (Claude, GPT, Gemini), so that they would not share blind spots. Each wrote its report
independently.

| Lens | Task |
| --- | --- |
| Fidelity | Unfold the Lean statement and every definition it uses into atomic clauses, and map each clause to the printed text: MATCH, MATCH AFTER A PROVED IDENTIFICATION, DIRECT INSTANCE, WEAKER or STRONGER THAN THE PRINT, MISMATCH. |
| Skeptic | Try to break the match: hidden standing hypotheses, what Ш means and how its group law is defined, the target group, the slots and quantifiers of the duality clause, vacuity, and what the relied-on Lean lemmas actually state. |
| Red team | Read the source cold, before any Lean, and state what it asserts in plain words. Then list every difference with the Lean and classify it. |

Source (legal copy; SHA-256):

| Source | Copy | SHA-256 |
| --- | --- | --- |
| J. W. S. Cassels, *Arithmetic on curves of genus 1. IV. Proof of the Hauptvermutung*, J. reine angew. Math. 211 (1962), 95-112 | GDZ scan PPN243919689_0211, LOG_0012 | `660a9e4fd00cd6447108464d47600d667330ff1d1e1128985e3bec215b0f31fc` |

Pages read: pp. 95-98, 101-105 and 108 by every lens. The fidelity lens read pp. 95-98, 101-105 and 108; the
skeptic pp. 95-105 and 108; the red team pp. 95-105, 108 and 112. Crelle's Journal is refereed.

The Lean dictionary was checked by every lens. `sha E` (`Contrib/OneProof/SelmerTwoPower.lean`) is
`E.shafarevichTateGroup embFin ⊓ E.shafarevichTateGroup embInf`, an additive subgroup of
`H1 (AbsoluteGaloisGroup ℚ) E.PointCoeff`; `embFin p` runs over every `p : Nat.Primes` (completion `ℚ_[p]`) and
`embInf ()` is the real place (`RealCompletion`, `ℝ`). `WeierstrassCurve.mem_shafarevichTateGroup_iff` says
`c ∈ W.shafarevichTateGroup τ ↔ ∀ i, W.pointRes (τ i) c = 0`, and `pointRes` is the cohomological pullback along
the local-to-global map of Galois groups and the global-to-local map of points (`pointRes_eq_explicitMap1`).
`E.PointCoeff` is Mathlib's points (zero and the nonsingular affine points) over `SeparableClosure ℚ`, with the
discrete topology and Galois acting on coordinates (`PointCoeff.instContinuousSMul`). `H1` is continuous
1-cocycles modulo coboundaries `σ ↦ σ • P − P`, with the Krull topology on the Galois group. `QZ` is
`ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)`. `E.IsElliptic` is `IsUnit E.Δ`. The choice of embedding does not matter
(`shafarevichTateGroup_eq_shafarevichTateGroup`, `pointRes_eq_pointRes`).

## 2. The row

| Lens | Verdict |
| --- | --- |
| Fidelity | PASS: every clause matches the print or is a direct instance of it (`k = ℚ`); the only weakening is dropping "naturally-defined"; nothing stronger, no mismatch, nothing blocking. |
| Skeptic | PASS (YES for the statement check): the `k = ℚ` Weierstrass instance of the printed theorem, with naturality dropped; no blocking mismatch, no required fix. |
| Red team | PASS on `CasselsIVThm11Elliptic`, no blocking item. FAIL on the unguarded helper `CasselsIVThm11` taken as a standalone row (§3). |

The print, p. 95:

> Theorem 1.1. Let k be an algebraic numberfield, C an abelian variety of dimension 1 and Ш the corresponding
> Tate-Šafarevič group of classes of principal homogeneous spaces for C defined over k which are everywhere
> locally trivial. Then there exists a naturally-defined skew-symmetric form l(ξ, η) defined for ξ, η ∈ Ш and
> taking values in the group Q/Z of the rationals modulo 1 which has the following property:
> Let m be a natural number and suppose that l(ξ, η) = 0 for all ξ ∈ Ш such that mξ = 0; then η = mH for some
> H ∈ Ш.

and §3 (viii), p. 104:

> (viii). l(ξ, η) is skewsymmetric, i.e. l(ξ, ξ) = 0 for all ξ.

The Lean:

```lean
def CasselsIVThm11 (E : WeierstrassCurve ℚ) : Prop :=
  ∃ l : sha E →+ sha E →+ QZ, (∀ ξ, l ξ ξ = 0) ∧
    ∀ m : ℕ, 0 < m → ∀ η : sha E, (∀ ξ : sha E, m • ξ = 0 → l ξ η = 0) →
      ∃ H : sha E, η = m • H

def CasselsIVThm11Elliptic : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → CasselsIVThm11 E
```

The clauses, as the readers mapped them:

* **Base field.** "Let k be an algebraic numberfield" (p. 95). The row fixes `k = ℚ`. DIRECT INSTANCE (all three).
* **The curve.** "C an abelian variety of dimension 1" (p. 95); p. 97: "An abelian variety C defined over a field k
  is a curve of genus 1 together with a distinguished point o on C defined over k. The rule of addition on C is
  that a + b = c … when the divisor consisting of the two points a, b with multiplicity +1 is linearly equivalent
  to the divisor consisting of the points c, o with multiplicity +1." The row quantifies over every
  `E : WeierstrassCurve ℚ` with `E.IsElliptic`. MATCH after the standard identification (fidelity), harmless
  (red team): every such `(C, o)` over `ℚ` has a nonsingular Weierstrass model with `o` at infinity, every `E` with
  `Δ` a unit is such a curve, and Mathlib's `toClass_injective` gives the group law in divisor-class form. The
  quantifier over all elliptic `E` covers every `C` up to `ℚ`-isomorphism. Weierstrass models of genus-one curves
  are not formalised; this is a reading step. The guard is not vacuous: `y² = x³ − x` (discriminant 64) is in the
  class (skeptic).
* **Points and coefficients.** p. 98: "𝔊̄ is the group of points of C defined over the algebraic closure k̄ of k and
  Γ is the galois group of k̄/k". `E.PointCoeff` is the points over `ℚˢ`, which in characteristic 0 is an algebraic
  closure. MATCH.
* **Continuous `H¹`.** p. 98: "the continuous group H¹(Γ, 𝔊̄)", with footnote 12: "i.e. arising from continuous
  cocycles when Γ has the Krull topology and 𝔊̄ the discrete topology". The cocycle `σ ↦ σ𝔄 − 𝔄` (p. 98) satisfies
  `a_{στ} = a_σ + σ a_τ`, the Lean `d1` convention. MATCH (fidelity).
* **The group Ш and its law.** p. 98: "It turns out (cf. Lang-Tate (6) or the discussion in Paper III) that this
  gives a 1—1 correspondence between WC and H¹(Γ, 𝔊̄). We give WC the group structure of H¹(Γ, 𝔊̄), so WC becomes
  a commutative torsion group. The map (1.1) preserves the group structure: in particular Ш is a subgroup of WC."
  pp. 101 and 108 write `WC = H¹(Γ, 𝔊̄)`. The print *defines* the group on WC, and hence on Ш, by transport from
  `H¹`, and builds the pairing on that side (p. 101: "a continuous cocycle … for η"). MATCH (fidelity); same
  additive group, no new geometric comparison assumption (skeptic); harmless (red team). The homogeneous-space to
  `H¹` bijection itself is not formalised; it is the print's own identification, not a Lean step the row needs.
* **"Everywhere locally trivial", and the real place.** p. 98: "Ш is just the intersection of the kernels of the
  maps WC(k) → WC(k_𝔭), where k_𝔭 runs through all the local completions of k". p. 105, (5.1): "We say that an
  element of H^u(Γ, 𝔐) is everywhere locally trivial if it is in the kernel of j_𝔭 for every 𝔭", with 𝔐_𝔭 "the
  group of points on C defined over k̄_𝔭" when 𝔐 = 𝔊̄, and j_𝔭 "independent of the particular embedding". p. 108:
  "a finite extension of a p-adic field (or the reals)". `pointRes τ` is exactly `j_𝔭`, and `sha E` is the kernel
  of every `j_𝔭` over the primes and `ℝ`. For `ℚ` these are all the places (Ostrowski, not formalised). MATCH.
* **Values.** "taking values in the group Q/Z of the rationals modulo 1" (p. 95). `QZ = ℚ ⧸ ℤ`. MATCH.
* **Bilinearity.** p. 101: "We shall show that l(ξ, η) is bilinear in ξ, η and that l(ξ, ξ) = 0 for all ξ"; p. 104,
  §4: "We have completed the construction of the bilinear form l(ξ, η) (ξ, η ∈ Ш)". `l : sha E →+ sha E →+ QZ`.
  MATCH.
* **Skew-symmetry.** "skew-symmetric" (p. 95), glossed by the print itself in (viii), p. 104: "l(ξ, ξ) = 0 for all
  ξ". The row's `∀ ξ, l ξ ξ = 0` is alternation, exactly (viii), and it is not inferred from `l(ξ, η) = −l(η, ξ)`,
  which alone would allow nonzero diagonal values of order 2 (skeptic). MATCH.
* **Naturality.** "there exists a naturally-defined skew-symmetric form" (p. 95). The row asks only for existence.
  WEAKER THAN THE PRINT, implied by it (all three). Not vacuous: `l = 0` satisfies the row for a curve exactly when
  its Ш is divisible; on the abstract group `ℤ/2` any alternating form is zero and `m = 2` fails at a generator
  (skeptic); for finite Ш, `m = #Ш` forces non-degeneracy (fidelity).
* **The multiplier.** "Let m be a natural number" (p. 95). The row has `0 < m`. MATCH: in 1962 a natural number is
  a positive integer, and `m = 0` would assert that Ч = 0, which is open Problem (a) on the same page ("Can Ч
  contain elements of Ш other than 0?"). Read with `m = 0` allowed, dropping it would only weaken the row.
* **The duality clause.** "suppose that l(ξ, η) = 0 for all ξ ∈ Ш such that mξ = 0; then η = mH for some H ∈ Ш"
  (p. 95). The row has `η` in the second slot, as printed, `ξ` over `sha E`, and `H` in the same `sha E` (compare
  Problem (b), p. 95). One `l` precedes every `m` and `η`, as in the print. MATCH. The proof's Lemma 4.1 (p. 104)
  has the divisible element in the first slot; by alternation the slot does not matter.
* **Dropped:** "naturally-defined", and the prose gloss after the theorem ("In other words, l sets Ш/Ч in complete
  duality with itself, where Ч is the group of infinitely divisible elements of Ш"), which is not part of the
  italicized statement. Both WEAKER THAN THE PRINT.

**Recorded non-blocking points**, with the reading the row follows:

1. **The Weil–Châtelet identification is the print's own.** Cassels identifies WC with `H¹(Γ, 𝔊̄)` in §1, p. 98,
   and gives WC the group law of `H¹`. The tree has no theorem identifying classes of homogeneous spaces with `H¹`,
   and none is claimed: the row is stated on the cohomological side, where the print builds the pairing. The
   verified lemmas are more limited: `pointRes_eq_explicitMap1` (the restriction is the cohomological pullback),
   `pointRes_eq_pointRes` and `shafarevichTateGroup_eq_shafarevichTateGroup` (independence of the embeddings).
2. **"Naturally-defined" is dropped.** A weakening: the row is an existence statement.
3. **The Weierstrass model.** "Abelian variety of dimension 1" is read as a nonsingular Weierstrass cubic with its
   point at infinity; standard, not formalised end to end.
4. **Locators.** Two readers asked that p. 98 (with footnote 12) be cited for the correspondence and its topology,
   not only p. 108. The docstrings on main now do (see the note above §1). The skeptic also notes that the italic lead of §3 (vii),
   p. 103, says "linear in η" while its displayed computation varies ξ; §3 (v) proves linearity in η, and pp. 101
   and 104 state bilinearity. Neither point changes the statement.

## 3. The unguarded helper `CasselsIVThm11`

The red team rated the helper `CasselsIVThm11 (E : WeierstrassCurve ℚ) : Prop` on its own and failed it: it has no
`E.IsElliptic` guard, `sha E` and `E.PointCoeff` are defined for every Weierstrass curve, and at a singular cubic
(for example `y² = x³`) it asserts something Theorem 1.1 does not. The fidelity lens and the skeptic note the same
point and call it harmless, since only the guarded wrapper is the row. The red team's own fix allows either a guard
or restricting the rating to `CasselsIVThm11Elliptic`. The fold takes the second: the read row is
`CasselsIVThm11Elliptic`, which applies the helper only at elliptic `E`, and the glue to `hCT` starts from it. The
helper's docstring on main says so: "The row is `CasselsIVThm11Elliptic`, which carries the guard `E.IsElliptic`; applied to a singular cubic,
this unguarded helper says more than Cassels does."

## 4. What the readings do not establish

* **The evidence stays AI-READ.** No person has read these pages, and OPEN.md's count of human readings does not
  change.
* **The proof imports Paper III.** §4 reduces Theorem 1.1 to Lemma 4.1 (p. 104), and §6 proves it through Lemma 6.2,
  which is Theorem 7.1 of Paper III (Cassels, Proc. London Math. Soc. (3) 12 (1962)); p. 105 also uses that Ш/qШ
  is finite (footnote 26). These are inputs to the proof, not to the statement. The readings check the statement
  only; Paper III and Lang–Tate were not read.
* **Comparison with the old row.** The old `hCT` (`PoleS12.CasselsTatePairingCurves`, Poonen–Stoll's restatement
  at the curves `E_ℓ`) and the read row are not shown to imply each other in the tree: from Theorem 1.1 to "kernel ⊆
  `divisiblePart`" needs Ш[q] or Ш/qШ finite. Both imply the Poonen–Stoll form
  `PoleS12.CasselsTatePairingCurvesPS`, which is all the consumer `poleCompleteness_of_rankOne_PS` reads
  (`casselsTatePairingCurvesPS_of_casselsIV`, `CasselsIV/Glue.lean`; `casselsTatePairingCurvesPS_of_current`,
  `CasselsTatePS/Basic.lean`). That form is the new `hCT` (§5).
* **Not formalised:** the Weil–Châtelet identification, Weierstrass models of genus-one curves, and Ostrowski's
  classification of the places of `ℚ`.

## 5. The field `hCT`: the Poonen–Stoll form, rated through the proved implication

The field `hCT` is `PoleS12.CasselsTatePairingCurvesPS` (`Contrib/OneProof/CasselsTatePS/Basic.lean`, #207): at
each curve `E_ℓ` of Theorem 5.3, an alternating pairing on `sha E_ℓ` with values in `ℚ/ℤ` that kills the maximal
divisible subgroup and whose kernel elements are infinitely divisible. It is not itself the statement the lenses read.
It is rated through two Lean theorems:

* `casselsTatePairingCurvesPS_of_casselsIV : CasselsIVThm11Elliptic → CasselsTatePairingCurvesPS`
  (`CasselsIV/Glue.lean`, #217). Each `E_ℓ` is elliptic (`PoleRC.curve_isElliptic`), and the glue keeps Cassels's
  pairing: alternation is (viii); the maximal divisible subgroup is killed because every class of `sha E` has finite
  order; kernel elements are infinitely divisible by Theorem 1.1 at every `m > 0`, after alternation moves the
  kernel element into the second slot. No finiteness of Ш/qШ is used. So `hCT` is a Lean-proved weakening of the
  direct instance read here, and it is rated as that print is: LEAF, with kind consequence, since the step from the
  print is an argument (proved), not a specialization.
* `casselsTatePairingCurvesPS_of_current : CasselsTatePairingCurves → CasselsTatePairingCurvesPS`
  (`CasselsTatePS/Basic.lean`, #207). The previous statement of `hCT` implies the new one, so the restatement is a
  weakening: a proof of the previous statement, such as a route through Fisher's work on #158, still closes `hCT`.

The consumer `poleCompleteness_of_rankOne_PS` reads exactly this form, so `frozenTarget` takes it with no glue in
between.

## 6. Effect on the board

`hCT`, the root hypothesis of `ZInQ.OneProof.frozenTarget`, is restated from `PoleS12.CasselsTatePairingCurves` to
`PoleS12.CasselsTatePairingCurvesPS`, fed to `poleCompleteness_of_rankOne_PS` as in
`CasselsTatePS.frozenTarget_with_hCTps` (`CasselsTatePS/FoldCheck.lean`). It is rated LEAF (strict and strictest),
kind consequence, with a flag recording the proved implication from the read row, the reading and the points above.
The earlier reading of the Poonen–Stoll introduction moves to `reviews-retired.tsv`. The count of open statements
stays at 22, and the strict count of the H part stays at 8/11. With the three root hypotheses, the strict count goes
from 8/14 to 9/13.
