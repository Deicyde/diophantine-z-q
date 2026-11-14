"""Manual fixes for LPrefix.lean after del_decls.py + add_opens.py (op-dedupe). Each edit asserts its anchor."""
import sys
F = 'ZInQKernel/OneProof/H/LPrefix.lean'
s = open(F).read()
def rep(old, new, count=1):
    global s
    assert s.count(old) == count, (old, s.count(old))
    s = s.replace(old, new)
def cut(start_anchor, end_anchor, new, include_end=False):
    """replace the text from the line starting with start_anchor up to (not incl.) the line starting with end_anchor"""
    global s
    a = s.index('\n' + start_anchor) + 1
    b = s.index('\n' + end_anchor, a) + 1
    if include_end: b = s.index('\n', b) + 1
    s = s[:a] + new + s[b:]
# dot notation on the kernel's `PkgI4.GaloisRep` for HDec-defined predicates
rep('  ∃ a b : ℤ, a ≠ b ∧ ρ.HasHTWeightsAtSelf p {a, b}', '  ∃ a b : ℤ, a ≠ b ∧ GaloisRep.HasHTWeightsAtSelf (ρ := ρ) p {a, b}')
rep('    ρ.HasHTWeightsAtSelf ℓ {0, 1 - k}', '    GaloisRep.HasHTWeightsAtSelf (ρ := ρ) ℓ {0, 1 - k}')
rep('    ρ.DistinctHTWeights p →', '    GaloisRep.DistinctHTWeights (ρ := ρ) p →')
# def-faltings' copy of AbVar: the kernel's DefFaltings works over PkgI3.AbVar
cut('/-- (copied from `ZInQKernel/HDecomp/Objects.lean`) An abelian variety over a field `K`: a group',
    'noncomputable def AbVar.dim {K : Type}',
    '/-! op-dedupe: the copies `AbVar`, `AbVar.baseChange`, `AbVar.dim` of `ZInQKernel/HDecomp/Objects.lean` are\n'
    'removed: `AbVar` is the kernel\'s alias `ZInQ.DefFaltings.AbVar := PkgI3.AbVar`\n'
    '(`ZInQKernel/Contrib/HeightBC/G0StableBC.lean`). -/\n', include_end=True)
cut('/-- (leaf-adopt3 fold) The zero abelian variety', 'section ZeroAV',
    '-- op-dedupe: the copy `ZInQ.H5Neron.AbVar.zero` (for the copy `ZInQ.DefFaltings.AbVar`) is removed; as in the\n'
    '-- kernel, `AbVar.zero` is `PkgI3.AbVar.zero`.\n\n')
open(F, 'w').write(s)
print('LPrefix fixes applied')
# the kernel's alias `ZInQ.DefFaltings.AbVar := PkgI3.AbVar` (Contrib/HeightBC/G0StableBC.lean) replaces the copy
s = open(F).read()
rep('import ZInQKernel.HDecomp.Objects\n', 'import ZInQKernel.HDecomp.Objects\nimport ZInQKernel.Contrib.HeightBC.G0StableBC\n')
open(F, 'w').write(s)
# `#hdec_same HDec.X` compared the copy with the kernel's X; the copies below are removed (they are the kernel's X now)
s = open(F).read()
for x in ['PkgI6.LocalH2CardC', 'PkgI6.LocalKroneckerWeber', 'TSkolemKW.KW.KroneckerWeberCyclic', 'PkgI6.ChebotarevExists',
          'GlueConductor.HilbertDifferentFormula', 'GlueConductor.SerreDifferentBound', 'PkgI4.NewformOfEigenform',
          'GlueDescent.B2Q.LeafSqrtCrit', 'GlueDescent.B2Q.LeafUnramified', 'PkgI6.BrauerHasse2C',
          'PkgI6.BrauerReciprocity2C', 'PkgI2.AbhyankarDVR']:
    rep(f'#hdec_same HDec.{x}\n', f'-- op-dedupe: `HDec.{x}` removed; the bundle field is the kernel\'s `{x}` itself\n')
open(F, 'w').write(s)
