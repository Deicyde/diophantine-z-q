#!/usr/bin/env python3
"""Assemble ZInQKernel/Contrib/OneProof/RayClassShimura.lean (gt-rayclass).

Sources (all verbatim apart from the deletions and the renames listed here):
* scratch/shimura-cft/ShimuraCFT.lean: Part A2 (shimura-split's holomorphic family), Part B (definitions and the
  leaf), Part C2 (`exists_artinCondC`) and Part D (non-vacuity). Dropped: Part A1 and A3 (in the chain,
  TailZ16/TailZ17), c-to-printed's `CToPrinted.Shimura` block, Part C1 (t5-glue copies, in the chain module
  ZInQKernel/Contrib/OneProof/RingClassLattice.lean under the same names), the `R1fpProps`/rigidity variants of B5,
  and `mainThmIY3_of_mainThmI`.
* scratch/rayclass-cft/RayProof1..5, RayGlueO/I/A/B: dropped RayDefs (chain TailZ21), the t5-glue copies
  `exists_aut_extend`/`exists_ringEquiv_extend` (RingClassLattice's `T5Glue.exists_ringEquiv_extend` used), and the
  `RayClassCM` (QMFamily form) theorems; `obj_at` now takes `R1fpPropsAb` (it only reads the naturality clause,
  which the two clause lists share).
* scratch/gt-rayclass/NewCNO.lean (ClassNumberOneB proved) and NewFinal.lean (the two fields).
Run from the repository root: python3 scratch/gt-rayclass/mk.py
"""
import re

ROOT = '.'
SC = open('scratch/shimura-cft/ShimuraCFT.lean').read().split('\n')
RC = 'scratch/rayclass-cft/'
OUT = 'ZInQKernel/Contrib/OneProof/RayClassShimura.lean'

TOP = re.compile(r'^(theorem|def|lemma|/-|end|namespace|section|#|@\[|instance|abbrev|noncomputable|open|variable|'
                 r'private|example|attribute|set_option|$)')


def lines(a, b):
    """1-indexed inclusive range of ShimuraCFT.lean."""
    return SC[a - 1:b]


def drop_decl(L, name):
    pat = re.compile(r'^(private )?(noncomputable )?(theorem|def|lemma|abbrev|instance) ' + re.escape(name) + r'(\s|$)')
    for i, l in enumerate(L):
        if pat.match(l):
            j = i
            # preceding docstring / `open ... in` lines
            while j > 0 and L[j - 1].strip() != '' and not L[j - 1].startswith('end'):
                j -= 1
            k = i + 1
            while k < len(L) and not (L[k] != '' and TOP.match(L[k]) and not L[k].startswith(' ')):
                k += 1
            while k < len(L) and L[k].strip() == '':
                k += 1
            return L[:j] + L[k:]
    raise SystemExit(f'drop_decl: {name} not found')


def clean(L):
    """Drop `#print`, `example` blocks, `import` lines."""
    out, skip = [], False
    for l in L:
        if skip:
            if l.startswith(' ') or l.strip() == '':
                continue
            skip = False
        if l.startswith('#print') or l.startswith('import '):
            continue
        if l.startswith('example'):
            skip = True
            continue
        out.append(l)
    return out


def relabel_cno(L):
    """`ClassNumberOneB` is now GLUE, proved in NewCNO.lean (`classNumberOneB_proof`): replace its docstring."""
    i = next(k for k, l in enumerate(L) if l.startswith('def ClassNumberOneB'))
    j = i
    while not L[j - 1].startswith('/--'):
        j -= 1
    j -= 1
    doc = ['/-- **GLUE `ClassNumberOneB` (Eichler\'s class number one, adelic form), proved below**',
           '(`classNumberOneB_proof`, from the chain\'s norm-Euclidean `HDec.QMSplit.CNO.principal_of_lattice`, the',
           'computation behind `qmClassNumberOne_proof`): `(B ⊗ 𝔸_f)^× = B^× · 𝒪̂^×` for the maximal order',
           '`𝒪 = ℤ⟨1, i, (1+j)/2, (i+k)/2⟩` of `B = (2, −3 | ℚ)`. The statement is rayclass-cft\'s, unchanged. -/']
    return L[:j] + doc + L[i:]


parts = []

# --- shimura-cft Part A2 (shimura-split's holomorphic family), lines 585-858
a2 = clean(lines(585, 858))
parts.append(('scratch/shimura-cft/ShimuraCFT.lean Part A2 (lines 585-858)', a2))

# --- Part B (936-1382)
b = clean(lines(936, 1382))
for n in ['dcRel_one_iff', 'shimuraFamily_of_mainThmI', 'mainThmI_iff_ab', 'shimuraFamily_of_mainThmIAb', 'mainThmIY3_of_mainThmI',
          'ShimuraMainThmIDeligneY3']:
    b = drop_decl(b, n)
parts.append(('scratch/shimura-cft/ShimuraCFT.lean Part B (lines 936-1382)', b))

# --- Part C2 and D: from the `namespace ShimuraCFT` after C1's last `end T5Glue` to the end
ex = next(i for i in range(1387, len(SC)) if SC[i].startswith('theorem exists_tau'))
c_start = max(i for i in range(1387, ex) if SC[i].startswith('end T5Glue')) + 1
cd = clean(SC[c_start:])
parts.append((f'scratch/shimura-cft/ShimuraCFT.lean Part C2 and D (lines {c_start + 1}-{len(SC)})',
              ['noncomputable section', ''] + cd))

# --- `s6_sq` (RayDefs.lean lines 109-129; trimmed from the chain's copy in TailZ21)
RD = open(RC + 'RayDefs.lean').read().split('\n')
i0 = next(i for i, l in enumerate(RD) if l.startswith('theorem s6_sq'))
i1 = next(i for i in range(i0, len(RD)) if RD[i].strip() == '')
parts.append((RC + f'RayDefs.lean lines {i0 + 1}-{i1} (`s6_sq`, not in the chain)',
              ['noncomputable section', '', 'namespace ShimuraGlue.Ray', ''] + RD[i0:i1] + ['', 'end ShimuraGlue.Ray', '']))

# --- rayclass-cft parts
for f in ['RayProof1', 'RayProof2', 'RayProof3', 'RayProof4', 'RayProof5', 'RayGlueO', 'RayGlueI', 'RayGlueA',
          'RayGlueB']:
    L = clean(open(RC + f + '.lean').read().split('\n'))
    if f == 'RayProof2':
        L = drop_decl(L, 'exists_aut_extend')
        L = drop_decl(L, 'exists_ringEquiv_extend')
        L = relabel_cno(L)
        L = [l for l in L if not l.startswith('/-! ## P2a.')]
    if f == 'RayProof3':
        L = [l.replace(':= exists_ringEquiv_extend', ':= T5Glue.exists_ringEquiv_extend') for l in L]
    if f == 'RayProof5':
        L = drop_decl(L, 'rayClassCM_of')
        L = [l.replace('(hR1 : R1fpProps Y Φ)', '(hR1 : LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ)') for l in L]
        L = [l.replace('(`R1fpProps` naturality', '(`R1fpPropsAb` naturality') for l in L]
    if f == 'RayGlueO':
        L = drop_decl(L, 'rayClassCM_of2')
    if f == 'RayGlueI':
        L = drop_decl(L, 'rayClassCM_of3')
    if f == 'RayGlueA':
        L = drop_decl(L, 'rayClassCM_of4')
    if f == 'RayGlueB':
        L = drop_decl(L, 'rayClassCM_of_leaves')
    parts.append((RC + f + '.lean', L))

for f in ['NewCNO', 'NewFinal']:
    parts.append(('scratch/gt-rayclass/' + f + '.lean', clean(open('scratch/gt-rayclass/' + f + '.lean').read().split('\n'))))


hdr = open('scratch/gt-rayclass/Header.lean').read()
body = []
for src, L in parts:
    body.append(f'\n/-! ===== from {src} ===== -/\n')
    body.append('\n'.join(L))
txt = hdr + '\n'.join(body) + '\n'
txt = re.sub(r'\n{4,}', '\n\n\n', txt)
open(OUT, 'w').write(txt)
print('wrote', OUT, len(txt), 'bytes', txt.count('\n'), 'lines')
