#!/usr/bin/env python3
"""fold-b116 item 1: inbox 83's amendment to ss-faltings (faltingsSemistableHeightBC), reproducible.

Run from the repository root of a head that has ss-faltings folded (kinds row faltingsSemistableHeightBC, the leaf in
Contrib/OneProof/SSFaltings.lean, the field in the current TailZ bundle).

    python3 scratch/fold-b116/item1_ssf_amend.py [TailZ files with the field docstring ...]   (default TailZ84)

Edits (text only; no Lean statement changes):
* kinds.tsv row faltingsSemistableHeightBC: kind consequence, strict/strictest GLUE, the reading desk's flag
  (inbox 83, verbatim), flag_class note, source locator section 3, p. 354 (was section 1, UNVERIFIED);
* the leaf docstring (SSFaltings.lean): locator section 3 p. 354, the claim that Faltings "gives SGA 7 IX 3.3 as the
  reason" removed (not on the page), the Neron-model step (SGA 7 IX Cor. 3.3 / BLR 7.4/3) named inside the leaf;
* the field docstring in the TailZ bundle and Main's fold paragraph: section 1 -> section 3 p. 354.
"""
import sys

FIELD = 'faltingsSemistableHeightBC'
FLAG = ("Faltings 1983 §3 p. 354 (invariance of h of a semiabelian scheme under extension of the base field; AI page "
        "read 11-17; also p. 351 Bem. b), p. 350 Lemma 1); deciding step: the leaf is stated for the Neron model, which "
        "needs N'^0 = (N^0)_{R'} under semistability (SGA 7 IX Cor. 3.3 / BLR 7.4/3; neither cited in the manuscript); "
        "height normalization matches GroupModel.height up to definitional steps (metric (i/2)^g, p. 351)")
SOURCE = ("Faltings, Invent. Math. 73 (1983), 349-366, §3, p. 354 (bibliography faltings1983, diophantine_zq.tex "
          "L11084-11086; the manuscript cites the paper at L621 and L733, and uses this statement uncited at L596-598); "
          "ZInQ.SSFaltings.FaltingsSemistableHeightBC; ss-faltings")
RATED = 'ss-faltings; the reading desk 11-17 (page read)'


def die(m):
    sys.exit('item1_ssf_amend: ' + m)


def sub1(text, a, b, what):
    if text.count(a) != 1:
        die(f'{what}: expected one occurrence of {a[:60]!r}, found {text.count(a)}')
    return text.replace(a, b)


# kinds.tsv
kp = 'docs/one-proof/kinds.tsv'
lines = open(kp).read().split('\n')
hdr = lines[0].split('\t')
ix = {c: i for i, c in enumerate(hdr)}
hits = [i for i, l in enumerate(lines) if l.split('\t')[1:2] == [FIELD]]
if len(hits) != 1:
    die('kinds.tsv: expected one row ' + FIELD)
row = lines[hits[0]].split('\t')
row[ix['kind']] = 'consequence'
row[ix['flag']] = FLAG
row[ix['strict']] = 'GLUE'
row[ix['strictest']] = 'GLUE'
row[ix['source']] = SOURCE
row[ix['rated_by']] = RATED
row[ix['flag_class']] = 'note'
lines[hits[0]] = '\t'.join(row)
open(kp, 'w').write('\n'.join(lines))

# the leaf docstring
lp = 'ZInQKernel/Contrib/OneProof/SSFaltings.lean'
t = open(lp).read()
t = sub1(t, "extension**, which is Faltings' statement (Faltings 1983 §1; the manuscript uses it uncited at\n"
            "  diophantine_zq.tex L596-598): the leaf `FaltingsSemistableHeightBC` (§1), weaker than SS2\n",
         "extension**, which is Faltings' statement for semiabelian schemes (Faltings 1983 §3, p. 354; the manuscript\n"
         "  uses it uncited at diophantine_zq.tex L596-598) read for Néron models: the leaf\n"
         "  `FaltingsSemistableHeightBC` (§1 of this file), weaker than SS2\n", 'module doc')
t = sub1(t, "/-- **Leaf (Faltings 1983 §1; locator UNVERIFIED, pending reading).** If `A_L` has semistable reduction everywhere\n",
         "/-- **Leaf (Faltings 1983 §3, p. 354; page read 11-17 by the reading desk).** If `A_L` has semistable reduction\n"
         "everywhere\n", 'leaf header')
t = sub1(t, "`⋀^g ω`, metric `(i/2)^g ∫ η ∧ η̄`, degree normalized by `[L:ℚ]`, Faltings' normalization). Faltings states that\n"
            "the height of a semistable abelian variety does not change under finite extension of the ground field (the reason he\n"
            "gives is SGA 7 IX 3.3; the statement, not its proof, is the leaf). The manuscript uses it uncited at\n",
         "`⋀^g ω`, metric `(i/2)^g ∫ η ∧ η̄`, degree normalized by `[L:ℚ]`, Faltings' normalization, p. 351). Faltings\n"
         "prints, for a semiabelian scheme over the ring of integers, that its height is invariant under extension of the\n"
         "base field (§3, p. 354, without a citation; see also p. 351 Bem. b) and p. 350 Lemma 1). The leaf is stated for\n"
         "the Néron models `𝒩`, `𝒩'`, assuming semistability only of `𝒩`; linking it to the print needs\n"
         "`𝒩'^0 ≅ (𝒩^0)_{𝓞_{L'}}` under semistability, which is SGA 7 IX Cor. 3.3 (or BLR 7.4/3), cited neither by\n"
         "Faltings there nor by the manuscript: that content is part of this leaf (consequence, GLUE).\n"
         "The manuscript uses it uncited at\n", 'leaf body')
open(lp, 'w').write(t)

# the field docstring in the TailZ bundle(s)
for tz in (sys.argv[1:] or ['ZInQKernel/OneProof/H/TailZ84.lean']):
    t = open(tz).read()
    t = sub1(t, "diophantine_zq.tex L11084-11086), section 1 (locator UNVERIFIED, pending reading): the height of an abelian "
                "variety with semistable reduction everywhere does not change under finite extension of the ground field.",
             "diophantine_zq.tex L11084-11086), §3, p. 354 (page read 11-17): the height of a semiabelian scheme does not "
             "change under extension of the base field; read for Neron models, which needs N'^0 = (N^0)_{R'} under "
             "semistability (SGA 7 IX Cor. 3.3 / BLR 7.4/3, cited neither there nor in the manuscript; that content is "
             "part of this leaf).", tz)
    open(tz, 'w').write(t)

# Main's fold paragraph
mp = 'ZInQKernel/OneProof/Main.lean'
t = open(mp).read()
t = sub1(t, "by `faltingsSemistableHeightBC` (Faltings 1983 section 1, invariance of the height of a\n"
            "semistable abelian variety under finite extension;",
         "by `faltingsSemistableHeightBC` (Faltings 1983 §3, p. 354, invariance of the height of a\n"
         "semiabelian scheme under extension of the base field, read for Néron models: SGA 7 IX Cor. 3.3's content is\n"
         "named inside this leaf;", 'Main')
open(mp, 'w').write(t)
print('item 1: kinds row, leaf docstring, field docstring, Main paragraph edited')
