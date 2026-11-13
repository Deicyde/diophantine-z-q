#!/usr/bin/env python3
"""leaf-fold3: the new parts (partsF/, compiled in module TailF after leaf-fold2's TailE) and the new
root-namespace module LF3Cot.lean.src. Every part is a verbatim copy of its source (line ranges named in
its header) with only these edits, each recorded in the header:
  * leaf-fold's HDec name-resolution edits (as mk_parts.py): `_root_.PkgI4` -> `_root_.HDec.PkgI4`, and in
    `open` lines a bare `ZInQ` also opens the kernel's root `ZInQ`;
  * `#print`, `#check`, `import` lines dropped;
  * lines `open PkgI3 (AbVar)` dropped (as leaf-fold2 and g0-assemble2 did for the height-bc parts:
    inside `HDec` the def-faltings alias `ZInQ.DefFaltings.AbVar` is meant).
Run from scratch/leaf-fold3."""
import re, os
R = '../'
def hdec(s):
    s = s.replace('_root_.PkgI4', '_root_.HDec.PkgI4')
    out = []
    for l in s.split('\n'):
        if l.startswith('#print') or l.startswith('#check') or l.startswith('import '):
            continue
        if l.startswith('open ') and re.search(r'(?<![\w.])ZInQ(?=\s|$)', l):
            l = re.sub(r'(?<![\w.])ZInQ(?=\s|$)', '_root_.ZInQ ZInQ', l, count=1)
        out.append(l)
    return '\n'.join(out)
def lines(fn, a=1, b=None):
    L = open(R + fn).read().split('\n')
    return '\n'.join(L[a-1:(b if b else len(L))])
def part(name, hdr, body, drop_open_abvar=False):
    if drop_open_abvar:
        body = '\n'.join(l for l in body.split('\n') if l.strip() != 'open PkgI3 (AbVar)')
    open('partsF/' + name, 'w').write('-- (leaf-fold3) ' + hdr + '\n' + hdec(body) + '\n')

def main():
    # c10: Burnside's theorem proved from Mathlib (rv-gluepieces2, as g0-assemble3's part d10)
    part('c10_burnside.lean', 'scratch/g0-assemble3/parts/d10_burnside.lean verbatim (rv-gluepieces2 checks/c11_burnside.lean)',
         lines('g0-assemble3/parts/d10_burnside.lean'))
    # c20: CPtsTransport proved (cpts-transport)
    part('c20_cpts.lean', 'scratch/cpts-transport/CPtsTransport.lean lines 7-end (after its import and #check lines)',
         lines('cpts-transport/CPtsTransport.lean', 7))
    # c40: kf-glue's points bookkeeping and levels 1-3 (as g0-assemble3's d20 lines 1-15 and 431-end; its lines
    #      16-430 duplicate part a75, which leaf-fold2 updated to kernel-field's current New.lean)
    part('c40_kfglue.lean', 'scratch/g0-assemble3/parts/d20_kfglue.lean lines 1-15 and 431-1391 (lines 16-430 duplicate part a75)',
         lines('g0-assemble3/parts/d20_kfglue.lean', 1, 15) + '\n' + lines('g0-assemble3/parts/d20_kfglue.lean', 431))
    # c50: twist-descent's parts (TwistDescent proved; ConjIsogMaps from MulIsogeny)
    part('c50_twistdescent.lean', 'scratch/twist-descent/Part{XC,HFD,Main,GDM,Final}.lean verbatim',
         '\n\n'.join(lines('twist-descent/Part%s.lean' % p) for p in ['XC', 'HFD', 'Main', 'GDM', 'Final']))
    # c60: hodge-bc2's two proofs (HodgeBCInjective, OmegaBaseChange)
    part('c60_hodgebc2.lean', 'scratch/hodge-bc2/hbc_proof.lean.part and omega_proof.lean.part verbatim',
         lines('hodge-bc2/hbc_proof.lean.part') + '\n\n' + lines('hodge-bc2/omega_proof.lean.part'), drop_open_abvar=True)
    # c70: linked-tate's parts 95-98 (G3 on the model from NOS + GoodRedTorsion), as g0-assemble3's parts c10-c15
    #      (which already carry the G7Data edits; c16 = linked-tate's own bundle is not needed)
    part('c70_linkedtate.lean', 'scratch/g0-assemble3/parts/c10-c15 verbatim (linked-tate parts 95, 97, 98b, 98c, 98d, 98)',
         '\n\n'.join(lines('g0-assemble3/parts/%s.lean' % p) for p in
           ['c10_lt95_linked', 'c11_lt97_linkeddata', 'c12_lt98b_ram', 'c13_lt98c_inertia', 'c14_lt98d_upperabs', 'c15_lt98_g3tate']))
    # c75: lt-goodred's proofs (GoodRedTorsion proved; QMEndRank from T6, T27), its integration file
    part('c75_ltgoodred.lean', 'scratch/lt-goodred/integ/99d_proofs.lean verbatim (made by its make_proofs.py from its parts 10, 20, 40, 50)',
         lines('lt-goodred/integ/99d_proofs.lean'))
    # LF3Cot: infra-stalks' CotangentBaseChange.lean lines 523-end (its lines 1-522 are in LF2Stalks), root namespace
    open('LF3Cot.lean.src', 'w').write('import LF2Stalks\n\n/-! leaf-fold3: scratch/infra-stalks/CotangentBaseChange.lean lines 523-end verbatim (its lines 1-522 are module LF2Stalks); `#print` lines dropped. -/\n\nuniverse u\n'
        + '\n'.join(l for l in lines('infra-stalks/CotangentBaseChange.lean', 523).split('\n') if not l.startswith('#print')) + '\n')

if __name__ == "__main__":
    main()
    print("ok", sorted(os.listdir("partsF")))
