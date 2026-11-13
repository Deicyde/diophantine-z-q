#!/usr/bin/env python3
"""unif-dims (P2: `ProductMetrizationOfProductUnif` from T35 and `TangentDimAtOrigin`) and infra-smooth-dim
(`TangentDimAtOrigin` proved), over this file's objects. Mirrors scratch/unif-dims/build_combined.py:
* parts/b09_unifdims.lean (inside HDec): WithProductHeight.lean from line 1578 (its lines 11-977 are part a25,
  980-1577 part b08), metrization2's Kernel.lean as build_combined takes it but without its G0Dim section
  (part 10 is g0-dim), Torsion.lean, part_main, DetProd, part_phl, part_final, part_combined, part_pc from its
  line 75, part_pcfinal, part_final2, part_combined2. `open PkgI3 (AbVar)` lines and `#print` lines deleted.
* LF2UnifRoot.lean.src (root namespace, imports LF2Stalks): CotangentProduct_infra.lean and part_pc lines 1-74
  (namespaces `AlgebraicGeometry`, `IsLocalRing`; inside `HDec` they would shadow Mathlib's namespaces).
  StalkPullback_infra.lean is LF2Stalks's first 525 lines (diff), so it is not repeated.
* LF2SmoothDim.lean.src (root): infra-smooth-dim's SmoothDimProps.lean without its `LeafQM.AV.Pin` section
  (image-plane has that copy), with the namespaces `InfraSmoothDim` -> `LF2.InfraSmoothDim` and
  `ZInQ.DefFaltings.HodgeLattice` -> `LF2.HodgeLattice` (to avoid clashes with image-plane's copy; the
  statement is transferred by unfolding, so the namespace does not matter)."""
d = '../unif-dims/'
def body(path):
    return '\n'.join(l for l in open(path).read().splitlines()
                     if not l.startswith('#print') and not l.startswith('import '))
def upto_print(path):
    return open(path).read().split('#print axioms')[0]
wph = open('../product-unif/WithProductHeight.lean').read().splitlines()
wph_tail = '\n'.join(l for l in wph[1577:] if not l.startswith('#print'))
kl = open(d + 'base/Kernel_metrization2.lean').read().splitlines()
i_jdd = next(i for i, l in enumerate(kl) if l.startswith('/-- **Glue (the Jacobian descends'))
i_m2 = next(i for i, l in enumerate(kl) if l.startswith('/-! ## metrization2: `JacDetNondegenerate` from'))
i_g0e = next(i for i, l in enumerate(kl) if l.startswith('end G0DimSec'))
kernel = '\n'.join(kl[i_g0e+1:i_jdd]) + '\nend ZInQ.Metrization\n\n' + \
    '\n'.join(l for l in kl[i_m2:] if not l.startswith('#print'))
pc = open(d + 'part_pc.lean').read().splitlines()
i_ud = next(i for i, l in enumerate(pc) if l.startswith('namespace ZInQ.UnifDims'))
out = ('/-! ## leaf-fold2: unif-dims and product-unif §3b-§5 over this file\'s objects (see mk_unifdims.py) -/\n\n'
       + wph_tail + '\n\n' + kernel + '\n\n' + body(d + 'Torsion.lean') + '\n\n'
       + upto_print(d + 'part_main.lean') + '\n\n' + body(d + 'DetProd.lean') + '\n\n'
       + upto_print(d + 'part_phl.lean') + '\n\n' + upto_print(d + 'part_final.lean') + '\n\n'
       + upto_print(d + 'part_combined.lean') + '\n\nopen CategoryTheory Limits\n\n'
       + '\n'.join(pc[i_ud:]) + '\n\n'
       + upto_print(d + 'part_pcfinal.lean') + '\n\n' + upto_print(d + 'part_final2.lean') + '\n\n'
       + upto_print(d + 'part_combined2.lean'))
out = '\n'.join(l for l in out.splitlines() if l.strip() != 'open PkgI3 (AbVar)' and not l.startswith('#print'))
# Leaves.lean's `ZInQ.LeafPush2` repeats most of `ZInQ.DefFaltings` (the kernel's does not): open only the
# LeafPush2 names this section uses, as g0-assemble2 did in parts 80, a30, a80.
assert out.count('open NumberField ZInQ.DefFaltings ZInQ.LeafPush2\n') == 1
out = out.replace('open NumberField ZInQ.DefFaltings ZInQ.LeafPush2\n', 'open NumberField ZInQ.DefFaltings\n'
                  'open ZInQ.LeafPush2 (CPts cptObj cDom cEvalAt IsUniformization UniformizationExists)\n')
# Leaves.lean has two abelian-variety structures (`ZInQ.DefFaltings.AbVar`, `PkgI3.AbVar`; the kernel has one,
# `open PkgI3 (AbVar)`): in this section a field-by-field coercion (= `LeafAdopt.abVarEquiv`) is inserted.
anchor = 'open ZInQ.LeafPush2 (CPts cptObj cDom cEvalAt IsUniformization UniformizationExists)\n'
out = out.replace(anchor, anchor + 'open scoped Obj\n\n/-- (leaf-fold2) the two abelian-variety structures of '
                  'Leaves.lean, field by field (`LeafAdopt.abVarEquiv`). -/\n'
                  'local instance lf2AbVarCoe {K : Type} [Field K] : Coe (AbVar K) (PkgI3.AbVar K) := ⟨fun A => ⟨A.X⟩⟩\n', 1)
open('parts/b09_unifdims.lean', 'w').write(out + '\n')
root = ('import LF2Stalks\n\n/-! leaf-fold2: unif-dims\' root-namespace lemmas (see mk_unifdims.py) -/\n\n'
        + body(d + 'base/CotangentProduct_infra.lean') + '\n\n' + '\n'.join(pc[:i_ud]) + '\n')
open('LF2UnifRoot.lean.src', 'w').write(root)
sd = open('../infra-smooth-dim/SmoothDimProps.lean').read().splitlines()
a = next(i for i, l in enumerate(sd) if l == 'namespace LeafQM')
b = next(i for i, l in enumerate(sd) if l == 'end LeafQM' and i > a)
sd = sd[:a] + ['-- (leaf-fold2) section LeafQM.AV.Pin omitted (image-plane has it)'] + sd[b+1:]
s = '\n'.join(l for l in sd if not l.startswith('#print'))
s = s.replace('ZInQ.DefFaltings.HodgeLattice', 'LF2.HodgeLattice').replace('InfraSmoothDim', 'LF2.InfraSmoothDim')
open('LF2SmoothDim.lean.src', 'w').write(s + '\n')
print('ok', out.count('\n'))
