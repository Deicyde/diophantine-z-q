# Generate the hdec-adopt2 modules of ZInQKernel/HDecomp/ from the scratch drafts (run from the
# worktree root). Verbatim copies of existing HDecomp modules become imports.
import re, os, subprocess
S = 'scratch/'; D = 'ZInQKernel/HDecomp/'; H = 'ZInQKernel.HDecomp.'
DOC = ('/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt2 from\n'
       '`scratch/{src}`.\n'
       'The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/\n')
made = []
def emit(dst, src, lines, imports):
    body = [l for l in lines if not l.startswith('import ')]
    body = [l for l in body if not re.match(r'#(print|check|eval|exit)', l)]
    seen = []; [seen.append(i) for i in imports if i not in seen]
    out = ['import ' + i + '\n' for i in seen] + ['\n', DOC.format(src=src), '\n'] + body
    os.makedirs(os.path.dirname(D + dst), exist_ok=True)
    open(D + dst, 'w').write(''.join(out)); made.append(D + dst)
def rd(p): return open(S + p).read().splitlines(keepends=True)
def imps(lines):
    return [l.split()[1] for l in lines if l.startswith('import ')]
def idx(L, pred, start=0):
    return next(i for i in range(start, len(L)) if pred(L[i]))
def plain(dst, src, extra=()):
    L = rd(src); emit(dst, src, L, imps(L) + list(extra))
OBJ = H + 'Objects'
NOTE_I3 = ("/-! pkg-I3's object layer and leaves (§1-§4 of the draft, a verbatim copy of\n"
           "`scratch/pkg-I3/I3.lean`) are imported from `ZInQKernel.HDecomp.Objects` (§A), whose\n"
           "QM leaf is `PkgI3.QMDichotomyYu`. -/\n\n")

# I3 linear algebra: glue-ssbc's C2.lean (= glue-I3-linalg's C2.lean + SSBC). The draft's
# lines 3-16 (pkg-I3's header) and §1-§4 (the pkg-I3 copy) are replaced by an import of Objects.
L = rd('glue-ssbc/C2.lean')
a = idx(L, lambda l: l.startswith('/-! ## 1. The `ℓ`-adic Tate module'))
b = idx(L, lambda l: l.startswith('/-! ## 5. C2 in the object layer'))
h0 = idx(L, lambda l: l.startswith('/-'), 1); h1 = idx(L, lambda l: l.startswith('-/'), h0)
emit('I3Linalg/C2.lean', 'glue-ssbc/C2.lean', L[:h0] + L[h1 + 1:a] + [NOTE_I3] + L[b:],
     imps(L) + [OBJ])
# TateBC: §1 (copy of pkg-I3's Tate module) from Objects.
L = rd('glue-I3-linalg/TateBC.lean')
a = idx(L, lambda l: l.startswith('/-! ## 1.'))
b = idx(L, lambda l: l.startswith('/-! ## 2.'))
emit('I3Linalg/TateBC.lean', 'glue-I3-linalg/TateBC.lean',
     L[:a] + ["/-! §1 (pkg-I3's Tate module, copied verbatim in the draft) is imported from\n",
              '`ZInQKernel.HDecomp.Objects`. -/\n\n'] + L[b:], imps(L) + [OBJ])
# RhoCont: §1-§2 and the leaf `TateModuleFree` (copies of pkg-I3) from Objects.
L = rd('glue-rho-cont/RhoCont.lean')
a = idx(L, lambda l: l.startswith('/-! ## 1.'))
b = idx(L, lambda l: l.startswith('/-! ## 3.'))
c = idx(L, lambda l: l.startswith('/-- Copied verbatim from scratch/pkg-I3/I3.lean (leaf I3.M0'))
d = idx(L, lambda l: not l.strip(), c)
emit('I3Linalg/RhoCont.lean', 'glue-rho-cont/RhoCont.lean',
     L[:a] + [NOTE_I3] + L[b:c] + ['/-! `TateModuleFree` (leaf I3.M0) is `PkgI3.TateModuleFree` of `Objects`. -/\n']
     + L[d:], imps(L) + [OBJ])

# WP3: glue-descent's files (byte-identical copies) and pkg-I6's cochain leaves from the project.
L = rd('glue-wp3/WP3.lean')
a = idx(L, lambda l: l.startswith('namespace PkgI6'))
b = idx(L, lambda l: l.startswith('end PkgI6'))
L = L[:a] + ['/-! The `PkgI6` cochain definitions and leaves are imported from\n',
             '`ZInQKernel.HDecomp.Conductor.I6Base`. -/\n'] + L[b + 1:]
emit('Descent/WP3.lean', 'glue-wp3/WP3.lean', L,
     [H + 'Descent.B3Assembly', H + 'Conductor.I6Base'])

# B3 (v): glue-b3b's B3b.lean (contains glue-b3-unram's Unram, glue-conj's Conj, T32(a), T32(b)).
plain('B3Unram/B3b.lean', 'glue-b3b/B3b.lean')
# C10 trace link (already imports HDecomp modules).
plain('C10/Link.lean', 'glue-c10-link/Link.lean')
# Vigneras.
plain('Vigneras/Local.lean', 'glue-vigneras/Local.lean')
L = rd('glue-vigneras/Global.lean')
# a long `first | …` line, broken by hand before the last alternative (wrap.py would break
# inside a parenthesized tactic sequence)
F = '        first | (left; rfl) | (right; rfl) | (exfalso; revert h2; decide) | (exfalso; revert h3; decide)\n'
assert F in L
L = [l if l != F else F[:F.rindex(' |')] + '\n          | (exfalso; revert h3; decide)\n' for l in L]
emit('Vigneras/Global.lean', 'glue-vigneras/Global.lean', L, imps(L))
# Square-root criterion: SqrtLocal (its copy of `exists_half_iff` becomes a call to
# `GlueI6Rest.exists_half_iff`); Disj (its copy of SqrtLocal's lines 84-242 and of
# `PkgI6.LocalKroneckerWeber` become imports).
L = rd('glue-sqrt-local/SqrtLocal.lean')
a = idx(L, lambda l: l.startswith('theorem exists_half_iff'))
b = idx(L, lambda l: l.rstrip().endswith(':= by'), a)
c = idx(L, lambda l: l.strip() and not l.startswith(' '), b + 1)
while not L[c - 1].strip(): c -= 1
L = L[:b] + [L[b].rstrip()[:-len(':= by')] + ':=\n', '  GlueI6Rest.exists_half_iff χ\n'] + L[c:]
L = [l.replace('/-! Copied verbatim from `scratch/glue-I6-rest/SqrtChar.lean` (glue-I6-rest). -/',
               '/-! Proved by `GlueI6Rest.exists_half_iff` (`Conductor/SqrtChar.lean`). -/') for l in L]
emit('Sqrt/SqrtLocal.lean', 'glue-sqrt-local/SqrtLocal.lean', L, imps(L) + [H + 'Conductor.SqrtChar'])
L = rd('glue-sqrt-disj/Disj.lean')
a = idx(L, lambda l: l.startswith('/-! Copied from `scratch/glue-sqrt-local/SqrtLocal.lean`')) - 2
b = idx(L, lambda l: l.startswith('end GlueSqrtLocal'), a)
c = idx(L, lambda l: l.startswith('namespace PkgI6'))
d = idx(L, lambda l: l.startswith('end PkgI6'), c)
assert L[a].startswith('namespace GlueSqrtLocal')
L = (L[:a] + ['/-! `GlueSqrtLocal.exists_half_iff`, `redU`, `redU_sq_eq_one` and their helpers\n',
              '(copied in the draft) are imported from `ZInQKernel.HDecomp.Sqrt.SqrtLocal`. -/\n']
     + L[b + 1:c] + ['/-! `PkgI6.LocalKroneckerWeber` is imported from `Conductor/I6Base.lean`. -/\n']
     + L[d + 1:])
emit('Sqrt/Disj.lean', 'glue-sqrt-disj/Disj.lean', L,
     imps(L) + [H + 'Sqrt.SqrtLocal', H + 'Conductor.I6Base'])
# The ℓ-adic conductor exponent.
plain('Conductor/LadicCond.lean', 'def-ladic-cond/LadicCond.lean')
# The remaining glue-assembly drafts.
for f in 'C8 E1Lin E2Index F3Glue'.split():
    plain(f'Assembly/{f}.lean', f'glue-assembly/{f}.lean')
subprocess.run(['python3', '-I', 'scratch/hdec-adopt/wrap.py'] + made)
print('\n'.join(made))
