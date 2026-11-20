# Gross–Zagier's rational point in the pole argument

**Verdict: conditional reduction; stop before a fold.** Gross–Zagier (7.3)(1)
supplies the infinite-order point used by `HKConsumed`, once the matching
newform is at the geometric conductor. The reduction proves the analytic-rank
dictionary and checks that the tree's newform has level `CST.newformLevel E`.
The equality of that least cusp-form level with the geometric conductor is
one new named GLUE. The prescribed newform route already uses two GLUE
readings, so this is not a standalone reduction with at most one total GLUE
before Theorem 5.3. With those readings shared by Theorem 5.3, the pole route
adds only the conductor GLUE and the new print draft, but still gives no
favorable fold. `GZ73Print` stays a draft pending the two-lens source check.

The manuscript's citation at L1784 has a known gap: the cited Milne theorem
and remark provide modularity and a parametrization at the conductor, but
the citation as given does not supply newness or the Hecke equivariance at
L1788. This is a locator and application gap; no mathematical error was
found in the checked pole steps. The Kolyvagin source cited at L1093 is an
unrefereed preprint, and its modularity premise is stronger than
`PoleS12.IsModular`. The existing audit explains both issues in
`docs/research/audit-pole-hypotheses.md` and the docstring of
`RC/PrintsAnalytic/Newform.lean` under `ZInQKernel/Contrib/OneProof/`.

## What the reduction proves

All four theorems are in namespace `ZInQ.Manuscript.HKGZ73`,
in `ZInQKernel/Contrib/OneProof/HKGZ73/Reduction.lean`.

- `level_eq_newformLevel_of_isNewformOf` identifies the level of a matching
  newform with `CST.newformLevel`. Apply the existing divisor-level
  extraction behind `modularNewform_of_printed` to the form at the least
  matching level. The extracted newform gives a matching cusp form at its
  own level by the trivial-character equivalence. Its level divides the
  least level and is at least the least level, hence they are equal. Li's
  strong multiplicity one identifies that level with the level of the
  newform from `modularNewform_of_printed`.
- `analyticRankOne_iff_exists_value_deriv` discharges the analytic
  dictionary in both directions. An entire continuation has analytic order
  one at 1 exactly when its value is zero and its derivative is nonzero:
  Mathlib's iterated derivative criterion at order one reads off the
  zeroth and first derivatives. Both sides use the same witness.
- `analyticRankOne_iff_value_deriv` gives the same equivalence for any
  supplied continuation. The identity theorem
  (`PrintsAnalytic.isLContinuation_eq`) makes the witness unique as a
  function; `PrintsAnalytic.eq_L_of_isLContinuation` also identifies it
  with `ModularForm.L` of the matching newform. No extra convergence,
  continuation, or normalization assumption is introduced.
- `hkConsumed_of_gz73` takes `BCDTThmAPrinted` through
  `bcdtThmA_of_printed` and `modularNewform_of_printed`, applies the two
  dictionaries and the conductor comparison, and obtains the point from
  `GZ73Print`. This is the entire arithmetic output consumed at L1111–1115.
  The existing `poleCompleteness_of_hkConsumed` uses it and the eight
  Selmer classes to get the required Kummer representatives.

**VERIFIED (Lean).** The reduction and `scratch/hk-gz73/Check.lean` pass
`lake env lean` after building their imports. The scratch file checks the
substitution into pole completeness and the implication from
`Prints.kolyvagin` to the old `hK` type. All four new theorems have only
`propext`, `Classical.choice`, and `Quot.sound`; see
`scratch/hk-gz73/axioms.txt`.

The two new assumptions split different parts of the target. `GZ73Print`
is the conditional implication from the reading desk's **AI-READ** locator:
Gross–Zagier, Invent. Math. 84 (1986), Thm (7.3)(1), p. 231. It supplies
only a point in the finite-order negation form, under a matching newform
at the conductor and the two central conditions (L1086–1093, L1111–1113).
Its extra standing premises prevent applying it directly to an
`HKConsumed` call; it promises neither modularity nor conductor data,
and is strictly less than the forward-rank assertion it replaces on the
pole branch, which also gives a rank upper bound and finiteness of Sha.
It is not the legacy unqualified positive-rank Prop.

`PoleNewformLevelIsConductor` supplies only a level comparison for
positive squarefree `ℓ ≡ 11 (mod 12)` on the modular pole curves
(L1779–1784). It mentions neither analytic rank nor rational points and
makes none of the arithmetic assertions of `HKConsumed`. Its target
`IsGeometricConductorLevel E N` is a definition: `N > 0` and for each
prime `p` the `p`-exponent of `N` equals the Artin conductor of the
actual cohomological Tate representation at `p`, for each auxiliary
Tate prime different from `p`. This is the existing
`associatedGeometricConductorExponent` from the Carayol formalization.
There is no abstract choice of a conductor map. The existing Carayol and
Faltings readings in `RCLeaves` compare Euler factors and do not assert
this equality of conductors. The formalization does not add a new
printed leaf for it.

## Remaining inputs and fold arithmetic

| Input | Scope and TeX lines | Owner |
| --- | --- | --- |
| Height bundles `r`, `t`, `l` | Unchanged H part, L377–972 and L10936–11007. | Existing height suppliers |
| `hRC` | Unchanged Theorem 5.3, L1005–1011, invoked at L1111; supplies analytic rank one. | Restricted-converse work |
| `hCT` | Unchanged Cassels–Tate pairing, L1072–1084; gives corank one at the eight-class calls. | Existing pairing supplier |
| `hB` | Existing BCDT printed input and adapter, L1092, L1779–1780, L11150–11154. | Modularity supplier |
| `shimuraConjugates`, `liMultiplicityOne` | Existing Shimura 1973 and Li 1975 prints behind the newform step, L1779–1784; bibliography L11050–11057. | `RCLeaves` suppliers |
| `carayolEulerFactors`, `faltingsRigidity` | Existing GLUE readings in the newform step, L1779–1784; bibliography L11084–11086 and L11205–11208. | `RCLeaves` suppliers |
| `GZ73Print` | Proposed published replacement for the pole use at L1086–1093 and L1111–1113; Gross–Zagier bibliography L11161–11162. | Reading desk and reviewer |
| `PoleNewformLevelIsConductor` | Open geometric conductor comparison, L1779–1784. | Project conductor work, unassigned |

Counts below are distinct open rows, with the two existing Shimura/Li
prints counted as prints and the draft counted as GLUE until cleared.

- **Before folding Theorem 5.3:** only `hK` leaves. `hRC`, `hCT`,
  `hB`, and the H rows remain. The four newform rows listed above enter,
  plus `GZ73Print` and `PoleNewformLevelIsConductor`. The base has
  31 rows (9 LEAF / 22 GLUE, including `hCT` and `hB` as LEAF).
  The trial would have **36** rows (11 / 25 now; 12 / 24 if the draft
  clears). Net **+5** rows.
- **After wiring Theorem 5.3 through the existing assembly:** `hRC`
  is independently replaced by its Theorem 5.3 suppliers
  (`restrictedConverseGenuine_of_leaves`); `Prints.bcdt` can share
  `hB` via the adapter. Against that assembly with a separate `hK`,
  the Gross–Zagier change removes just `hK` and adds just the print draft
  and conductor GLUE. No duplicate Shimura, Li, Carayol or Faltings row
  enters. The marginal change is **+1** row (0 LEAF / +1 GLUE now;
  +1 LEAF / 0 GLUE if the draft clears). If the shared suppliers are
  themselves proved, they can be reused without new rows. In particular,
  with Theorem 5.3 and those suppliers all closed, the base after removing
  `hRC` is 30 rows, and the replacement would take it to **31**
  (9 / 22 now; 10 / 21 if the draft clears).
- **Deduplication in that same assembly:** `Prints.kolyvagin` remains a
  separate Theorem 5.3 dependency, including at rank zero (L2616–2626,
  L7625–7627, L7780–7781). Where its current `r ≤ 1` statement is
  retained, its `r = 1` instance already implies `hK`. Compared with
  reusing that field to drop `hK`, the Gross–Zagier proposal adds **two**
  rows, and it cannot remove `Prints.kolyvagin`. This preprint input is
  GLUE under the project rule.

No assembly or registry was edited.

## Known issues and skeptic checks

- **Source lens:** the desk reading and the locator audit
  (`docs/research/locators.md`) agree on the modular elliptic curve,
  the zero central value, the nonzero derivative, and the infinite-order
  point over ℚ. The scan was not independently examined here. A skeptical
  page read must check the standing hypothesis, in particular whether
  merely having that newform suffices in the printed setup, and whether
  any restriction on the curve was omitted. The locator is AI-READ, not
  independent confirmation.
- **Lean lens:** `IsNewformOf` uses the genuine normalized weight-two
  newform space, trivial nebentypus and all positive-index coefficients,
  not just matching good Euler factors. Those coefficients are rational
  since they are the curve's integer coefficients. The central derivative
  is for the arithmetic L-series of the minimal model after entire
  continuation. The print requires a geometric conductor level explicitly.
  An independent review should check the interpretation of the printed
  conductor against this Tate-module definition, including the bad primes.
  A least modular level or an arbitrary witness of `ModularNewform` alone
  does not discharge that interpretation or its application.
- The manuscript bibliography already lists Gross–Zagier at L11161–11162.
  Its pole proof cites the stronger forward theorem at L1093. This
  replacement is confined to the point needed at L1111–1115; it supplies
  neither the stronger lemma as printed in the manuscript nor the
  downstream finiteness assertions elsewhere in the manuscript.

## Manuscript check

All locations are in `diophantine_zq.tex`.

| TeX lines | Step | Verdict |
| --- | --- | --- |
| L1001–1011, L1771–1775 | Pole completeness uses the restricted converse to obtain an order-one zero. | **OK** — Theorem 5.3 remains an input. |
| L1033–1069 | The simultaneous construction supplies both admitted parameters and eight Selmer classes. | **OK** — existing Kummer identification and construction supply the calls. |
| L1072–1084 | The pairing yields corank one from the eight classes. | **OK** — the existing proof takes `hCT`. |
| L1086–1089, L1111–1113 | Interpret order one as the zero and nonzero-derivative pair. | **OK** — the exact dictionary is proved. |
| L1092, L1779–1784, L11150–11154 | Obtain modularity and the matching weight-two newform. | **OK** — the specified adapter and printed newform route give the newform and its least level. |
| L1780–1788 | Pin the modular level to the geometric conductor; the text also asserts a geometric realization. | **unverified** — the level comparison remains GLUE; the given Milne locator is insufficient for the full claim. |
| L1093–1097, L11161–11167 | Replace the forward theorem's pole use by Gross–Zagier (7.3)(1). | **unverified** — the proposed print is AI-READ and awaits the two-lens check. |
| L1111–1115 | Get rational Kummer representatives. | **gap filled** — the Lean substitution needs only the point plus the eight-class count. |
| L1116–1121 | Rescale the two witnesses and conclude pole completeness. | **OK** — the existing pole completeness proof is reused. |
| L2616–2626, L4020–4021, L7625–7627, L7780–7781 | Theorem 5.3 also has uses of the forward rank and finiteness result. | **OK** — the replacement does not touch these suppliers. |
