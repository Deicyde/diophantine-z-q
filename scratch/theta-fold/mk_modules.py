"""theta-fold: the contributor modules ZInQKernel/Contrib/OneProof/LinYang{Kron,Split,Glue,Printed}.lean, cut from
linyang-printed's scratch/linyang-printed/LinYangPrintedFull.lean (copy in scratch/theta-fold/src/) by line ranges.
Dropped: theta-split §0 (the verbatim-copy check) and §1 (moved into TailK by plumb.py), linyang-printed §5-§9
(QMHauptmodul from the leaves, the J-tuple cross-check, Eisenstein modularity and IgusaPsi4/IgusaChi10, the 31-field
research bundle: not needed, igusaPsi4/igusaChi10 are already gt-theta's theorems), the `#print`s and `example`s.
Run from the repository root."""
SRC = 'scratch/theta-fold/src/LinYangPrintedFull.lean'
L = open(SRC).read().split('\n')
def R(a, b):  # 1-based inclusive
    return '\n'.join(L[a - 1:b])
def find(prefix, start=1):
    for i in range(start - 1, len(L)):
        if L[i].startswith(prefix): return i + 1
    raise KeyError(prefix)
OUT = 'ZInQKernel/Contrib/OneProof/'
kron_end = find('end IgusaAlgEval')
split_ns = find('namespace HDec.HSyn.G0Split.ThetaPt.ThetaSplit')
split_s2 = find('/-! ## 2. Reduction to symmetric functions')
split_end = find('end HDec.HSyn.G0Split.ThetaPt.ThetaSplit')
glue_start = split_end + 1
while not L[glue_start - 1].startswith('noncomputable section'): glue_start += 1
glue_end = find('end HDec.HSyn.G0Split.ThetaPt.IgusaAlgFinal')
pr_start = find('noncomputable section', find('/-! # linyang-printed, combined file'))
pr_s5 = find('/-! ## 5. `PkgI1.QMHauptmodul` from the same two leaves')
assert L[split_ns - 1 + 2].startswith('open CategoryTheory')

HDR = 'set_option linter.all false\n\n'
kron = ('import ZInQKernel.OneProof.H.TailZ19\n\n'
 '/-! # theta-fold (1/4): igusa-alg\'s Kronecker evaluation engine\n\n'
 'igusa-alg\'s `IgusaAlgEval` (scratch/igusa-alg/IgusaAlg.lean, verbatim through linyang-printed\'s\n'
 'LinYangPrintedFull.lean): a homogeneous integer polynomial identity holds over every commutative ring once the\n'
 'kernel checks one value at a Kronecker point and a coefficient bound (`Data.gen_eq_zero`; `decide +kernel`, no\n'
 '`native_decide`). Used by `LinYangGlue` for the identities `IgusaAlg 3..9`. docs/research/theta-fold.md. -/\n\n'
 + R(find('/-! # igusa-alg: polynomial identities by one Kronecker evaluation'), kron_end) + '\n')
split = ('import ZInQKernel.OneProof.H.TailZ19\n\n'
 '/-! # theta-fold (2/4): theta-split\'s reduction of `ThetaRatiosAtQM` to symmetric functions of `θ⁸`\n\n'
 'theta-split\'s scratch/theta-split/ThetaUse.lean §2-§7 (verbatim through igusa-alg and linyang-printed). Its §1\n'
 '(`ThetaRatiosAtQM`, `thetaPointOfFibre_of_qm_atQM`) is in `ZInQKernel/OneProof/H/TailK.lean`, where the chain\'s\n'
 'consumer `gluePieces_of_open4` uses it. docs/research/theta-fold.md. -/\n\n'
 'noncomputable section\n\n' + R(split_ns, split_ns + 6) + '\n\n' + R(split_s2, split_end) + '\n')
glue = ('import ZInQKernel.Contrib.OneProof.LinYangKron\nimport ZInQKernel.Contrib.OneProof.LinYangSplit\n\n'
 '/-! # theta-fold (3/4): theta-glue\'s Igusa theta expressions and igusa-alg\'s `ThetaRatiosAtQM` from\n'
 '`LinYangThetaCurve`\n\n'
 'theta-glue\'s scratch/theta-glue/ThetaGlue.lean (the duplication formula, `ThetaEightSquare`, Igusa\'s theta\n'
 'expressions `psi4Th`, `psi6Th`, `chi10Th`, `chi12Th`, theta-glue\'s composite `LinYangThetaCurve`, the reduction to\n'
 '`IgusaAlg k`) with igusa-alg\'s Kronecker proofs of `IgusaAlg 3..9`, and igusa-alg\'s final theorems\n'
 '(`thetaRatiosAtQM_of_linYang`, `thetaPointOfFibre_of_linYang`); verbatim through linyang-printed\'s\n'
 'LinYangPrintedFull.lean. docs/research/theta-fold.md. -/\n\n' + R(glue_start, glue_end) + '\n')
final = '''
/-! ## Route 1 from the two printed leaves (linyang-printed §10, theta-fold) -/

namespace HDec.HSyn.G0Split.ThetaPt.IgusaAlgFinal

open ThetaGlue ThetaSplit

/-- **The use form of `thetaRatiosAlgebraic` from Igusa's theta expressions and Lin–Yang's Example 29 (proved).** -/
theorem thetaRatiosAtQM_of_printed (hI : LinYangPrinted.IgusaThetaExpressions) (hL : LinYangPrinted.LinYangEx29) :
    ThetaRatiosAtQM :=
  thetaRatiosAtQM_of_linYang (LinYangPrinted.linYangThetaCurve_of_printed hI hL)

/-- **The use form from the strict printed leaves and `QMHauptmodul` (proved; theta-fold).** This is the hypothesis
`hθ` that `HDec.HSyn.gluePieces_of_open4` takes (as a function of `QMHauptmodul`), supplied at the top of the chain
(`sixContactMin_of_open29`) from the added-leaf fields `igusaThetaExpressions` and `linYangEx29All`. -/
theorem thetaRatiosAtQM_of_printedAll (hI : LinYangPrinted.IgusaThetaExpressions)
    (hA : LinYangPrinted.LinYangEx29All) (hH : PkgI1.QMHauptmodul) : ThetaRatiosAtQM :=
  thetaRatiosAtQM_of_printed hI (LinYangPrinted.linYangEx29_of_all hA hH)

/-- **`ThetaPointOfFibre` from `FibreQMPeriod` and the two printed leaves (proved).** Drop-in replacement for
`ThetaPt.thetaPointOfFibre_of_qm_ratios hQM hAlg`. -/
theorem thetaPointOfFibre_of_printed (hQM : FibreQMPeriod) (hI : LinYangPrinted.IgusaThetaExpressions)
    (hL : LinYangPrinted.LinYangEx29) : ThetaPointOfFibre :=
  thetaPointOfFibre_of_linYang hQM (LinYangPrinted.linYangThetaCurve_of_printed hI hL)

/-- **`ThetaPointOfFibre` from `FibreQMPeriod`, `QMHauptmodul` and the strict printed leaves (proved).** -/
theorem thetaPointOfFibre_of_printedAll (hQM : FibreQMPeriod) (hH : PkgI1.QMHauptmodul)
    (hI : LinYangPrinted.IgusaThetaExpressions) (hA : LinYangPrinted.LinYangEx29All) : ThetaPointOfFibre :=
  thetaPointOfFibre_of_linYang hQM (LinYangPrinted.linYangThetaCurve_of_printedAll hI hA hH)

end HDec.HSyn.G0Split.ThetaPt.IgusaAlgFinal
'''
printed = ('import ZInQKernel.Contrib.OneProof.LinYangGlue\n\n'
 '/-! # theta-fold (4/4): the printed leaves `IgusaThetaExpressions`, `LinYangEx29All` and Route 1 from them\n\n'
 'linyang-printed\'s scratch/linyang-printed/LinYangPrintedFull.lean §1-§4 and §10: the genuine Siegel Eisenstein\n'
 'series `siegelEis k` (a sum over `Γ_∞\\Sp₄(ℤ)`), Igusa\'s `χ₁₀`, `χ₁₂` (1962 combinations), Lin–Yang\'s `s_k`; the\n'
 'two LEAVES `IgusaThetaExpressions` (Igusa 1964/1967) and `LinYangEx29All` (Lin–Yang 2020, Example 29, the\n'
 'relations only); `LinYangThetaCurve` from them (eliminating `j₆`, density off one countable `Γ*`-orbit); and\n'
 '`thetaRatiosAtQM_of_printedAll`, which the chain\'s top `HDec.HSyn.sixContactMin_of_open29` uses in place of the\n'
 'field `thetaRatiosAlgebraic`. Locators of both leaves UNVERIFIED (see the docstrings).\n'
 'docs/research/theta-fold.md, docs/research/linyang-printed.md. -/\n\n'
 + R(pr_start, pr_s5 - 1).rstrip() + '\n\nend HDec.HSyn.G0Split.ThetaPt.LinYangPrinted\n' + final)
for name, body in [('LinYangKron', kron), ('LinYangSplit', split), ('LinYangGlue', glue), ('LinYangPrinted', printed)]:
    assert 'sorry' not in body and '#print' not in body
    open(OUT + name + '.lean', 'w').write(body)
    print(name, len(body.encode()))
