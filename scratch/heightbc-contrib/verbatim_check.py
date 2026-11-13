#!/usr/bin/env python3
"""Mechanical statement check for ZInQKernel/Contrib/HeightBC/ (task heightbc-contrib).

Run from the repository root.
(a) Scratch-only Props: the def block (docstring + `def` up to the next blank line) in the
    Contrib module equals, character for character, the block in the owner file.
(b) Copies of kernel Props: the def body (from `def NAME` to the next blank line), with
    whitespace normalised, equals the kernel's; Lean also checks `kernel ↔ copy` by `Iff.rfl`
    (`ZInQKernel/Contrib/HeightBC/Main.lean`, Part 5).
Prints one line per check and `ALL OK` at the end, or exits with status 1."""
import re, sys

C = 'ZInQKernel/Contrib/HeightBC/'


def block(path, name, ns=None, doc=True):
    """The block of `def name` in path (docstring included if doc). If ns is given, only an
    occurrence inside `namespace ns` is accepted (the first one)."""
    ls = open(path).read().split('\n')
    cur = []
    for i, l in enumerate(ls):
        m = re.match(r'^namespace (\S+)', l)
        if m:
            cur.append(m.group(1))
        elif re.match(r'^end (\S+)\s*$', l) and cur and l.split()[1] == cur[-1]:
            cur.pop()
        if re.match(r'^def ' + re.escape(name) + r'\b', l) and (ns is None or ns in cur):
            j = i
            while ls[j:j + 1] and ls[j] != '':
                j += 1
            s = i
            if doc:
                while s > 0 and ls[s - 1] != '' and not ls[s - 1].startswith('-- '):
                    s -= 1
            return '\n'.join(ls[s:j])
    raise SystemExit(f'NOT FOUND: {name} in {path} (ns={ns})')


bad = 0


def check(desc, a, b):
    global bad
    ok = a == b
    bad += not ok
    print(('OK   ' if ok else 'FAIL ') + desc)


FIN = 'scratch/height-bc/Final.lean'
# (a) scratch-only Props, exact text against the owners
for name, mod in [('HodgeBCInjective', 'GlueC'), ('OmegaBaseChange', 'Natural'),
                  ('CotangentSpanBC', 'GlueC'), ('UniformizationLiftAnalytic', 'GlueC'),
                  ('HodgeLineBaseChange', 'Copies'), ('ModelHeightBaseChange', 'Copies'),
                  ('IsBaseChangeOf', 'Copies')]:
    check(f'ZInQ.HeightBC.{name} ({mod}) = {FIN}', block(C + mod + '.lean', name),
          block(FIN, name))
check('ZInQ.HeightBC.OmegaLocalization (OmegaBC) = scratch/hodge-bc2/omega_proof.lean.part',
      block(C + 'OmegaBC.lean', 'OmegaLocalization'),
      block('scratch/hodge-bc2/omega_proof.lean.part', 'OmegaLocalization'))
for owner in ['scratch/g0-split/Split.lean', 'scratch/g0-stablebc/Main.part']:
    check(f'G0StableBC.StableHeightBaseChange (G0StableBC) = {owner}',
          block(C + 'G0StableBC.lean', 'StableHeightBaseChange'),
          block(owner, 'StableHeightBaseChange'))
check('G0StableBC.HodgeLineBaseChange (G0StableBC) = scratch/g0-stablebc/Main.part',
      block(C + 'G0StableBC.lean', 'HodgeLineBaseChange'),
      block('scratch/g0-stablebc/Main.part', 'HodgeLineBaseChange'))
check('ZInQ.HeightBC.HodgeLineBaseChange body = G0StableBC.HodgeLineBaseChange body',
      block(C + 'Copies.lean', 'HodgeLineBaseChange', doc=False),
      block(C + 'G0StableBC.lean', 'HodgeLineBaseChange', doc=False))
check('G0Split.StableHeightBaseChange body (scratch/h-decomposition/Leaves.lean) = G0StableBC body',
      block('scratch/h-decomposition/Leaves.lean', 'StableHeightBaseChange', ns='G0Split',
            doc=False),
      block(C + 'G0StableBC.lean', 'StableHeightBaseChange', doc=False))

# (b) copies of kernel Props: body text up to whitespace
KER = 'ZInQKernel/HDecomp/Faltings/H5Neron.lean'


def norm(s):
    return ' '.join(s.split())


for name in ['NeronModelExists', 'SemistableNeronIdentityComponent', 'ModelHeightBaseChange',
             'OpenSubgroupHeight', 'GroupModelBaseChangeExists', 'IsOpenSubgroupModel',
             'IsBaseChangeOf']:
    k = norm(block(KER, name, doc=False).split(':=', 1)[1])
    try:
        b = block(C + 'H5GlueReduction.lean', name, doc=False)
    except SystemExit:
        b = None
    if b is not None:
        check(f'ZInQ.H5Glue.{name} body = kernel ZInQ.H5Neron.{name} body (whitespace)',
              norm(b.split(':=', 1)[1]), k)
for mod, ns, name in [('Copies', 'ZInQ.HeightBC', 'ModelHeightBaseChange'),
                      ('Copies', 'ZInQ.HeightBC', 'IsBaseChangeOf'),
                      ('G0StableBC', 'G0StableBC', 'ModelHeightBaseChange'),
                      ('G0StableBC', 'G0StableBC', 'IsBaseChangeOf')]:
    check(f'{ns}.{name} body = kernel ZInQ.H5Neron.{name} body (whitespace)',
          norm(block(C + mod + '.lean', name, doc=False).split(':=', 1)[1]),
          norm(block(KER, name, doc=False).split(':=', 1)[1]))
print('ALL OK' if bad == 0 else f'{bad} FAILED')
sys.exit(1 if bad else 0)
