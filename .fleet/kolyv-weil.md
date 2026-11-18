# kolyv-weil

**VERIFIED.** On fork PR #90's head (`a04588b4f`), the two cited inputs to
Lemma 5.5 now have conductor-level printed forms in
`ZInQKernel/Contrib/OneProof/KolyvWeil/`. BCDT Theorem A, Introduction
condition (6), supplies the nonconstant ℚ-map from $X_0(N_E)$ required by
Kolyvagin. Kolyvagin's cited MPIM preprint is stated for both $r=0,1$,
with the full finite Sha conclusion. In `lem:forward-rank`, tex L1092
supplies the parametrization for L1093. The task's quoted CST reference
belongs elsewhere in the manuscript.

All three new Lean modules and the scratch checks compiled. The
`#discharges` fixture uses the exact four pole binders and recognizes
old `hK` from the two new leaves. The replacement pole proof consumes
only their rank-one implication, so it drops old `hB` without deriving
the old cusp form statement. The pole proof and the splice into the
frozen-target interface use only `propext`, `Classical.choice`, and
`Quot.sound`. The pole check includes a transitive no-`TYZGenus` check.

Integration remains: replace `hB,hK` and their sole pole call as specified
in `scratch/kolyv-weil/autofold.json` and shown by `preview_fold.py`.
Stock autofold only handles H bundle fields. `Main.lean` and `PoleS12/`
are unchanged. The full H import chain was not rebuilt; the splice was
checked against the unchanged assembly interface. The literature inputs
remain hypotheses, with Kolyvagin identified as a cited preprint, not a
refereed publication. See [the report](../docs/research/kolyv-weil.md).
