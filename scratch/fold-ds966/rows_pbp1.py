"""fold-ds966, fold 2 (pb-p1): the table edits that go with gen_pbp1.py. Run from the repository root after it:
    python3 scratch/fold-ds966/rows_pbp1.py
* kinds.tsv: the rows of panPrintedP and bergerPrintedVT removed; rows of panPrintedF and bergerSurveyF added (kind
  published, flag beginning "pending review; unread", hence GLUE in both columns; bundle/packet/label/tier/area_issue of
  the replaced rows), from pb-p1's scratch/pb-p1/kinds-rows-proposed.tsv with the flag prefixed.
* claims.tsv: rows of the two removed fields dropped (none on the fold head).
* reviews.tsv: rows of the two removed fields moved to reviews-retired.tsv (the readings were of the old statements).
Asserts every edit. Every new row passes render_open.py's row checks."""
import csv, io, os, sys
sys.path.insert(0, 'scripts/one_proof')
import render_open  # noqa: E402

D = 'docs/one-proof/'
OLD = ['panPrintedP', 'bergerPrintedVT']


def read(fn):
    rows = list(csv.DictReader(open(fn), delimiter='\t'))
    return rows, list(csv.DictReader(open(fn), delimiter='\t').fieldnames)


def write(fn, rows, cols):
    with open(fn, 'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=cols, delimiter='\t', lineterminator='\n')
        w.writeheader()
        w.writerows(rows)


rows, cols = read(D + 'kinds.tsv')
old = {r['field']: r for r in rows if r['field'] in OLD}
assert set(old) == set(OLD), old.keys()
PAN_FLAG = ("pending review; unread: new printed leaf (pb-p1, folded by fold-ds966; GLUE until a reviewer rates it; "
            "source: cited print, Pan arXiv:1901.07166v2 Thm 1.0.4 = JAMS 35 (2022) Thm 1.0.4, cited by "
            "diophantine_zq.tex; the statement is not in diophantine_zq.tex); Pan arXiv:1901.07166v2 Conj. 1.0.1 p. 2 and "
            "Thm 1.0.4 p. 5 read (JAMS numbering UNVERIFIED); 'potentially semi-stable in the sense of Fontaine' over "
            "Fontaine's B_st = B_cris[log p~] as Berger prints it (arXiv:math/0210184v1 II.3.1, II.3.3; a_n -> 0 read "
            "p-adically, as for A_max), basis form of admissibility (stronger hypothesis than the dimension form: "
            "isAdmissible_of_pstF, B_st G-stable bstF_stable); other readings as pb-fix3's panPrintedP (eigenform in its "
            "weakest sense, rho_g pinned by geometric-Frobenius traces)")
BER_FLAG = ("pending review; unread: new printed leaf (pb-p1, folded by fold-ds966; GLUE until a reviewer rates it; "
            "source: cited print, Berger's survey arXiv:math/0210184v1 IV.5.1; cited-drift: diophantine_zq.tex L739 cites "
            "Berger 2002 Invent. Math. 148 (Thm 0.7, the same theorem), not the survey; the statement is not in "
            "diophantine_zq.tex); Berger 2004 survey read on arXiv:math/0210184v1 (pages are the arXiv pages; de Gruyter "
            "pagination UNVERIFIED); readings: a_n -> 0 in B~^+ read p-adically with coefficients in A_inf and B_cris^+ "
            "the Q_p-algebra they generate (as bst-construct reads A_max); admissibility in its basis form, which the "
            "survey prints as equivalent to the dimension form (I.2.3, p. 6); Berger 2002 Thm 0.7 is the same theorem, "
            "its section 1.2 (p. 11) printing that Berger's B_st gives Fontaine's D_st")
new = []
for name, rep, flag, src in [
        ('panPrintedF', 'panPrintedP', PAN_FLAG,
         "Pan, The Fontaine-Mazur conjecture in the residually reducible case, J. Amer. Math. Soc. 35 (2022), 1031-1169, "
         "Thm 1.0.4 (= arXiv:1901.07166v2 Thm 1.0.4 with Conj. 1.0.1); Fontaine's B_st as BstFOf, pst as LocalIsPstF in "
         "Contrib/OneProof/PanBergerFontaine.lean"),
        ('bergerSurveyF', 'bergerPrintedVT', BER_FLAG,
         "Berger, An introduction to the theory of p-adic representations (2004), arXiv:math/0210184v1, IV.5.1 and "
         "IV.5.3, with II.2.3, II.3.1, II.3.3, II.5.2, I.2.3; = Berger, Invent. Math. 148 (2002), Theoreme 0.7; B_st "
         "(Fontaine) as BstFOf, admissibility (basis form) as IsAdmissibleT in Contrib/OneProof/PanBergerFontaine.lean and "
         "PanBergerPst.lean; de Rham as pb-fix2's IsDeRhamU")]:
    o = old[rep]
    r = dict(o)
    r.update(field=name, kind='published', flag=flag, strict='GLUE', strictest='GLUE', source=src,
             rated_by='pb-p1 (unreviewed); fold-ds966; pending review',
             flag_class='pending-review,unverified-locator')
    new.append(r)
out = []
for r in rows:
    if r['field'] == 'panPrintedP':
        out.append(new[0])
    elif r['field'] == 'bergerPrintedVT':
        out.append(new[1])
    else:
        out.append(r)
write(D + 'kinds.tsv', out, cols)

crow, ccols = read(D + 'claims.tsv')
write(D + 'claims.tsv', [r for r in crow if r['field'] not in OLD], ccols)
rv, rvcols = read(D + 'reviews.tsv')
ret, retcols = read(D + 'reviews-retired.tsv')
assert rvcols == retcols
moved = [r for r in rv if r['field'] in OLD]
write(D + 'reviews.tsv', [r for r in rv if r['field'] not in OLD], rvcols)
write(D + 'reviews-retired.tsv', ret + moved, retcols)
print(f'kinds: {len(old)} rows replaced; claims: {len(crow) - len([r for r in crow if r["field"] not in OLD])} dropped; '
      f'reviews: {len(moved)} moved to reviews-retired.tsv')
