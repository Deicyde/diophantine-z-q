# Print the block of `#print axioms` lines that hdec-adopt5b appends to scripts/print_axioms.lean
# (run from the worktree root). Every name must be a declaration of one adopted module.
import sys, glob
sys.path.insert(0, 'scratch/hdec-adopt2')
from decls import decls
full = {}
for p in sorted(glob.glob('ZInQKernel/HDecomp/Textbook/**/*.lean', recursive=True)):
    for n, _, _ in decls(p): full[n] = p
names = '''
PkgI6.hilbertDifferentFormula PkgI6.differentBound PkgI6.herbrandQuotient
PkgI6.herbrandTransitivity PkgI6.hilbertDifferentFormula_of_dvr PkgI6.monogenicDVR
PkgI6.traceContainsRamificationIdx TDifferent.exists_adjoin_eq_top
TSkolemKW.skolemNoether TSkolemKW.hsynSkolemNoether TSkolemKW.leafSkolemNoether
TSkolemKW.brauerNesbitt_module TSkolemKW.brauerNesbittChar0 TSkolemKW.hsynBrauerNesbitt
TSkolemKW.HS.frobeniusDense_of_frobDense TSkolemKW.HS.frobeniusDense_of_chebotarev
TSkolemKW.KW.ker_ge_of_kroneckerWeber TSkolemKW.KW.kroneckerWeberCyclic_of_kroneckerWeber
TSkolemKW.KW.ker_ge_of_kroneckerWeberCyclic TSkolemKW.KW.eq_of_agree_on_roots
TSkolemKW.KW.eq_of_agree_on_roots_cyclic TSkolemKW.KW.cycChar_surjective
TSkolemKW.KW.dirichletCharacter_of_kroneckerWeberCyclic TSkolemKW.KW.isOpen_ker_of_continuous
TSkolemKW.ChebCyc.chebotarevAt_cyclotomic TSkolemKW.C10.c10_of_chebotarev
T30.leafSqrtCrit_of_localKroneckerWeber T30.leafSqrtCrit_of_t16a
G1Adelic.relIndex_eq_four G1Adelic.mem_sup_iff_forall G1Adelic.normalizer_component
G1Adelic.gamma_count G1Adelic.gamma_order G1Adelic.gamma_count_Zint G1Count.index_count_of_central
T10Etale.H0Equiv T10Etale.T10_groupIso_of_linIso T10Etale.T10_linIso_zero T10Etale.transport_smul
T10Etale.galIso T10Etale.transport_bijective T10Etale.transport_H0
T10Etale.T10_linIso_of_tateDuality
PkgI1.igusa_forward PkgI1.igusaClebschSeparation_iff T28SO3.so3 PkgI1.mestre_abstract
PkgI1.separation_generic PkgI1.igusaClebschSeparation_of PkgI1.spot_J PkgI1.m3_G11 PkgI1.m3_G12
PkgI1.m3_G13 PkgI1.m3_G22 PkgI1.m3_a111
'''.split()
extra = sys.argv[1:]  # names from modules adopted later (e.g. Igusa/M3b)
names += extra
for n in names: assert n in full, n
print('\n-- hdec-adopt5b: t-different, t-skolem-kw, t30-adelic, t10-etale, t28-igusa')
print('-- (`HDecomp.Textbook`).')
for n in names: print('#print axioms ' + n)
