# `hCT` as a single-print row: Cassels (1962), Theorem 1.1

Additive evidence for the root hypothesis `hCT` of `ZInQ.OneProof.frozenTarget`
(`ZInQ.Manuscript.PoleS12.CasselsTatePairingCurves`). Nothing here changes an existing statement.

Print: J. W. S. Cassels, *Arithmetic on curves of genus 1. IV. Proof of the Hauptvermutung*,
J. reine angew. Math. 211 (1962), 95–112, Theorem 1.1, p. 95, with §3 (viii), p. 104. A legal copy
is on GDZ (PPN243919689_0211, LOG_0012); the file read has SHA-256
`660a9e4fd00cd6447108464d47600d667330ff1d1e1128985e3bec215b0f31fc`. Quotations were taken from
page images rendered at 150 dpi.

## Files

- `Row.lean`
  - `SelmerTwoPower.CasselsIVThm11 E`: Theorem 1.1 at `k = ℚ` for one curve, over the tree's
    `sha E` and `QZ`.
  - `SelmerTwoPower.CasselsIVThm11Elliptic`: the same for every elliptic curve over `ℚ`, the most
    faithful instance of the print at `k = ℚ`.
- `Glue.lean`
  - `SelmerTwoPower.casselsTatePairingPS_of_casselsIV : CasselsIVThm11 E → CasselsTatePairingPS E`.
  - `PoleS12.casselsTatePairingCurvesPS_of_casselsIV : CasselsIVThm11Elliptic →
    CasselsTatePairingCurvesPS`.
  - `PoleS12.SilvermanRank.poleCompleteness_of_rankOne_casselsIV`: the consumer
    `poleCompleteness_of_rankOne_PS` fed by it.
- `FoldCheck.lean`: `ZInQ.OneProof.CasselsIV.frozenTarget_with_casselsIV`, the body of
  `frozenTarget` at its base (`TailZ106`, bundle `OpenResearchLeaves78`, top
  `sixContactMin_of_open99`) with `hCT : CasselsIVThm11Elliptic`. It imports `Main`'s import list
  at that base, not `Main`.

Every declaration has a `#print axioms` line. Expected axioms: `propext`, `Classical.choice`,
`Quot.sound`.

## The statement

Theorem 1.1, p. 95, verbatim: "Let k be an algebraic numberfield, C an abelian variety of
dimension 1 and Ш the corresponding Tate-Šafarevič group of classes of principal homogeneous
spaces for C defined over k which are everywhere locally trivial. Then there exists a
naturally-defined skew-symmetric form l(ξ, η) defined for ξ, η ∈ Ш and taking values in the group
Q/Z of the rationals modulo 1 which has the following property: Let m be a natural number and
suppose that l(ξ, η) = 0 for all ξ ∈ Ш such that mξ = 0; then η = mH for some H ∈ Ш."

§3 (viii), p. 104: "l(ξ, η) is skewsymmetric, i.e. l(ξ, ξ) = 0 for all ξ." So "skew-symmetric"
is the alternating property, and the row states it as `∀ ξ, l ξ ξ = 0`.

## Dictionary: Cassels's Ш and the tree's `sha`

- Cassels's Ш is the group of classes of everywhere locally trivial principal homogeneous spaces.
  He works with it cohomologically: a "1—1 correspondence between WC and H¹(Γ, 𝔊̄)" (§1, p. 98),
  with 𝔊̄ the points of C over the algebraic closure k̄ and continuous cocycles (p. 98,
  footnote 12); p. 108 repeats "WC = H¹(Γ, 𝔊̄)". On p. 98, Ш "is just the intersection of the
  kernels of the maps WC(k) → WC(k_𝔭), where k_𝔭 runs through all the local completions of k".
- "Everywhere locally trivial" is triviality under the restriction `j_𝔭` for every valuation `𝔭`
  of `k` (p. 105, (5.1)). The archimedean places are included: p. 108 treats "a finite extension
  of a p-adic field (or the reals)".
- The tree's `SelmerTwoPower.sha E` (`Contrib/OneProof/SelmerTwoPower.lean`) is
  `E.shafarevichTateGroup embFin ⊓ E.shafarevichTateGroup embInf`: the classes of
  `H¹(G_ℚ, E(ℚˢ))` whose restriction vanishes at every `ℚ_p` and at `ℝ` (`RealCompletion`).
  **The real place is included.** Over `ℚ` the separable closure is the algebraic closure.
- Not formalised: the Weil–Châtelet identification of classes of homogeneous spaces with `H¹`. The
  row is stated on the `H¹` side, which is where Cassels builds the pairing (§3).
- Not formalised: "naturally-defined". The row is an existence statement and is weaker than the
  print there.

## Glue

- Alternating: (viii), directly.
- Kills the maximal divisible subgroup: every class of `sha E` has finite order
  (`exists_nsmul_eq_zero_H1`). If `x = N • g` with `N • y = 0`, then `l x y = l g (N • y) = 0`.
- Kernel elements are infinitely divisible: alternation gives skew-symmetry. So if `l x · = 0`,
  then `l · x = 0`, the hypothesis of Theorem 1.1 holds for `η = x` at every `m > 0`, and
  `x = m • H`.
- No finiteness of `Ш/qШ` is used, because the Poonen–Stoll form asks only for element-wise
  divisibility. Getting the current row's clause "kernel ⊆ `divisiblePart`" from Theorem 1.1 would
  need `Ш[q]` or `Ш/qШ` finite; this file does not attempt it.

## Fold plan

- Restate the root binder `hCT` of `ZInQ.OneProof.frozenTarget` from
  `PoleS12.CasselsTatePairingCurves` to `SelmerTwoPower.CasselsIVThm11Elliptic`.
- Route it through `casselsTatePairingCurvesPS_of_casselsIV` and `poleCompleteness_of_rankOne_PS`,
  exactly as `frozenTarget_with_casselsIV` does.
- One hypothesis replaces one, so the count is unchanged.
- The new row is a direct instance of one refereed print. It quantifies over all elliptic curves
  over `ℚ`, as the print does, not only over the curves `E_ℓ`.
- Neither row is shown to imply the other in the tree (from Theorem 1.1 to "kernel ⊆
  `divisiblePart`" needs `Ш[q]` or `Ш/qШ` finite). Both imply the Poonen–Stoll form, which is all
  the consumer reads.
- Of the two restatements, the Poonen–Stoll form is the weaker hypothesis
  (`casselsTatePairingCurvesPS_of_casselsIV` shows this row implies it at `E_ℓ`); this row is the
  more direct single-print instance.

**Holder.** `hCT` is held by an outside contributor. The request on #158 asks them to agree to
restating it to the Poonen–Stoll form `PoleS12.CasselsTatePairingCurvesPS` (#207); it does not
name `CasselsIVThm11Elliptic`. Restating `hCT` to this row needs the holder's agreement to this
row specifically, and the fold waits for it. Folding into `Main.lean` is integrator work and is not
done here.

## Reading notes

- **Lemma 6.2 imports Paper III.** §4 reduces Theorem 1.1 to Lemma 4.1 (p. 104), and §6 proves
  Lemma 4.1 through Lemma 6.2, which is "Theorem 7.1 of Paper III" (Cassels, Proc. London Math.
  Soc. (3) 12 (1962)). Of its sufficiency half, p. 108 says: it "follows from an elaborate
  computation of group indexes … which is given in Paper III and not reproduced here".
  Footnote 33 likewise cites "Lemma 3.1 of Paper III, already proved by Tate and by Šafarevič".
  These are inputs to the proof, not to the statement; Theorem 1.1 is stated and proved in this
  paper on that basis.
- **"Ш/qШ finite".** The proof of Theorem 1.1 (p. 105) uses "As is well-known, the quotient group
  Ш/qШ is finite", with footnote 26: "This is essentially a step in the proof of the Mordell-Weil
  finite basis theorem: see e.g. Lang-Tate". This, too, is a proof input. The row does not need
  it, and the glue does not use it.
