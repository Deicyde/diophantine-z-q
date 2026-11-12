import re
p='scratch/h-decomposition/Leaves.lean'; L=open(p).read()
def drop(name):
    global L
    m = re.search(r'\n/-- \*\*[^\n]*\n(?:(?!/--)[^\n]*\n)*?opaque ' + name + r' : Prop\n', L)
    assert m, name; L = L[:m.start()] + '\n' + L[m.end():]
for n in ['R08_SemistableReduction','T09_WeilPairing','T23_FontaineClosure','T29_LocalNormalizers','T32_TameQuadratic']:
    drop(n)
note = '''
/-! hsyn-fold: R8, T9, T23, T29 and T32 are no longer placeholders. Their concrete statements
(task leaf-push) are `PkgI2.GrothendieckMonodromy` (= `LeafPush.R08_GrothendieckMonodromy`,
consequence form), `LeafPush.T09_WeilPairing` (consequence, polarization hidden),
`PkgI4.T23_FontaineClosure` (exact, matrix form, `ℚ_p` coefficients),
`LeafPush.T29a_DivisionNormalizer` and `LeafPush.T29b_SplitNormalizer` (exact),
`LeafPush.T32a_TameQuadratic` and `LeafPush.T32b_QuadraticRamification` (consequences). -/

/-! ## §3. Glue -/'''
assert L.count('\n/-! ## §3. Glue -/') == 1
L = L.replace('\n/-! ## §3. Glue -/', note, 1)
for a, b in [('  r8 : R08_SemistableReduction\n', '  r8 : PkgI2.GrothendieckMonodromy.{0}\n'),
             ('  t9 : T09_WeilPairing\n', '  t9 : LeafPush.T09_WeilPairing.{0}\n'),
             ('  t23 : T23_FontaineClosure\n', '  t23 : ∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p\n'),
             ('  t29 : T29_LocalNormalizers\n', '  t29a : ∀ (p : ℕ) [Fact p.Prime], LeafPush.T29a_DivisionNormalizer p\n  t29b : ∀ (p : ℕ) [Fact p.Prime], LeafPush.T29b_SplitNormalizer p\n'),
             ('  t32 : T32_TameQuadratic\n', '  t32a : LeafPush.T32a_TameQuadratic\n  t32b : LeafPush.T32b_QuadraticRamification\n')]:
    assert L.count(a) == 1, a; L = L.replace(a, b)
open(p,'w').write(L); print(L.count('\nopaque '))
