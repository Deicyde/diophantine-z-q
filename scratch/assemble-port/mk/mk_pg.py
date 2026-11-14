"""assemble-port: period-glue and twist-descent parts, verbatim minus `import` and `#print` lines, then mk/open_zinq.py
(and an `end` per unclosed `noncomputable section`; e23 gets leaf-push2's `open ZInQ.LeafPush2 (CPts …)`, as parts
a30, d30, e20 have):
  parts/e21_s8.lean      = scratch/period-glue/S8.lean      (`PeriodGlue.s8Nonzero_proof : S8Nonzero`, Mathlib only)
  parts/e22_w8.lean      = scratch/period-glue/W8.lean      (`s8WeightExact_of : ThetaModularity → GammaStarGen → …`)
  parts/e23_qmtwist.lean = scratch/period-glue/QMTwist.lean (`qmTwistLattice_of' : T11aRiemannHom → LeafSkolemNoether → …`)
  parts/d25_twistdescent.lean = twist-descent's Mathlib-only module ZInQKernel/Contrib/TwistDescent/GaloisDescent.lean
     (merged from origin/wip/twist-descent; copied, not imported) + scratch/twist-descent/Part{XC,HFD,Main,Final}.lean
     (`KernelField.twistDescent`; PartGDM, kf-glue's unused `GaloisDescentMor`, is omitted: g0-assemble3's part d20 does not
     contain that def)
Run from scratch/assemble-port."""
import re, subprocess, sys
def clean(path):
    L = [l for l in open(path).read().split('\n') if not l.startswith('import ') and not l.startswith('#print')]
    t = '\n'.join(L)
    opens = len(re.findall(r'^noncomputable section\s*$', t, re.M)) + len(re.findall(r'^section\s*$', t, re.M))
    ends = len(re.findall(r'^end\s*$', t, re.M))
    return t.rstrip() + '\n' + ('\nend  -- assemble-port: closes the file\'s `noncomputable section`\n' * max(0, opens - ends))
out = {'e21_s8': ['../period-glue/S8.lean'], 'e22_w8': ['../period-glue/W8.lean'],
       'e23_qmtwist': ['../period-glue/QMTwist.lean'],
       'd25_twistdescent': ['../../ZInQKernel/Contrib/TwistDescent/GaloisDescent.lean'] + ['../twist-descent/Part%s.lean' % p for p in ['XC', 'HFD', 'Main', 'Final']]}
for name, srcs in out.items():
    hdr = '/-! ## assemble-port: %s, verbatim minus `import`/`#print` lines (mk/mk_pg.py) -/\n\n' % ', '.join('`scratch/' + s[3:] + '`' for s in srcs)
    body = '\n\n'.join(clean(s) for s in srcs)
    if name == 'e23_qmtwist':  # leaf-push2's names, opened at file level in period-glue's base (as parts a30, d30, e20 do)
        o = 'open HSyn.G0Split.FibreQM HSyn.G0Split.FibreQM.PeriodMapH\n'; assert body.count(o) == 1
        body = body.replace(o, o + 'open ZInQ.LeafPush2 (CPts cptObj IsUniformization cDom cEvalAt)\n')
    open('parts/%s.lean' % name, 'w').write(hdr + body)
    subprocess.run([sys.executable, '-I', 'mk/open_zinq.py', 'parts/%s.lean' % name], check=True)
print('ok')
