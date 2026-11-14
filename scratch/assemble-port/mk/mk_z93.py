"""assemble-port: parts/z93_linkedfrob.lean = linked-frob's AFR block and its part 10 (scratch/linked-frob/assemble.sh), i.e.
  the two file-level `open` lines of g0-mod-field's ModField.lean, frob-trace's part_bridge_src.lean and part_frob.lean,
  [mul-rigidity's Rigidity.lean is omitted: part a15 already contains it], alg-frob-red's
  part_red.lean, afr-absfrob's AbsFrobDef.lean minus its import and its copy of `def AbsFrob`, afr-absfrob's part_fext.lean,
  frob-pieces' part_{good,neron,final,full}.lean, then scratch/linked-frob/parts/10_linkedfrob.lean and 20_bundle4.lean L1-37
  (its theorems through `linkedFrob_of_neron_nmp`; not its bundle); the same two sed-deletions as linked-frob's assemble.sh; then mk/open_zinq.py. Needs the kernel module
  ZInQKernel.Contrib.FrobPieces.SmoothGeomConnIntegral (imports_tailD.txt). Run from scratch/assemble-port."""
import re, subprocess, sys
R = '../'
def rd(p): return open(R + p).read()
def sed_del(txt, start_re, end_re):
    L = txt.split('\n'); out = []; i = 0; n = 0
    while i < len(L):
        if re.search(start_re, L[i]):
            j = i
            while not re.search(end_re, L[j]): j += 1
            i = j + 1; n += 1; continue
        out.append(L[i]); i += 1
    assert n == 1, (start_re, n)
    return '\n'.join(out)
rig = '\n'.join(rd('mul-rigidity/Rigidity.lean').split('\n')[4:])
rig = sed_del(rig, r'^/-- \*\*Textbook leaf \(rigidity;', r'η\[A\.X\] ≫ h = η\[B\.X\] → IsMonHom h$')
afd = '\n'.join(rd('afr-absfrob/AbsFrobDef.lean').split('\n')[1:])
afd = sed_del(afd, r'^/-- \*\*`AbsFrob` \(GLUE', r'≫ g = g ≫ Fr$')
parts = ['open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj',
         'open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q', '',
         rd('frob-trace/part_bridge_src.lean'), rd('frob-trace/part_frob.lean'), rd('alg-frob-red/part_red.lean'),
         afd, rd('afr-absfrob/part_fext.lean')] + [rd('frob-pieces/part_%s.lean' % f) + '\n' for f in ['good', 'neron', 'final', 'full']] + \
        [rd('linked-frob/parts/10_linkedfrob.lean')]
# linked-frob's 20_bundle4.lean L1-37 (its LinkedFrob theorems up to `linkedFrob_of_neron_nmp`; `linkedFrob_of_textbook` uses
# the deleted fields `TextbookLeaves.t3/t4` and its `GluePieces4` bundle is not copied), closed as the file closes them.
b4 = rd('linked-frob/parts/20_bundle4.lean').split('\n')
assert b4[31].startswith('theorem linkedFrob_of_neron_nmp') and b4[37].startswith('/-- **`LinkedFrob` from the textbook bundle'), (b4[31], b4[37])
parts.append('\n'.join(b4[:37]) + '\n\nend LinkedFrobRed\n\nend\n\nend LinkedFrobBundleSec\n')
hdr = '/-! ## assemble-port: linked-frob (LinkedFrob from N1-g1, ProperSmoothGenConnected, I2-Red, I2-NMP); see mk/mk_z93.py -/\n\n'
txt = hdr + '\n'.join(parts)
txt = '\n'.join(l for l in txt.split('\n') if not l.startswith('#print'))
k = len(re.findall(r'^noncomputable section\s*$', txt, re.M)) - len(re.findall(r'^end\s*$', txt, re.M))
txt += '\n' + '\nend  -- assemble-port: closes an unclosed `noncomputable section` of the copied files\n' * k
open('parts/z93_linkedfrob.lean', 'w').write(txt + '\n')
subprocess.run([sys.executable, '-I', 'mk/open_zinq.py', 'parts/z93_linkedfrob.lean'], check=True)
print('ok')
