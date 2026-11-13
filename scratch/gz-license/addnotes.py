import re, sys
root = 'ZInQKernel/Contrib/TauCeti/'
imp = "extra imports of Backport/ modules (commit-97a5b235 declarations absent from the oct16 modules vendored here)"
notes = {
 'GroupTheory/GroupAction/Norm.lean': "`groupNorm`, `groupNormHom` and their lemmas omitted (taken from the imported oct16 `GroupCohomology.Cocycle`); extra imports of that module and a Backport/ module",
 'GroupTheory/SpecificGroups/Cyclic/PowMonoidHom.lean': imp,
 'NumberTheory/ClassFieldTheory/ClassFields/KroneckerWeber.lean': imp,
 'NumberTheory/ClassFieldTheory/ClassFields/RaySubgroup.lean': imp,
 'NumberTheory/ClassFieldTheory/Global/AdmissibleModulus/Basic.lean': imp,
 'NumberTheory/ClassFieldTheory/Global/AdmissibleModulus/Ramification.lean': imp,
 'NumberTheory/ClassFieldTheory/Global/AdmissibleModulus/Reciprocity.lean': imp,
 'NumberTheory/ClassFieldTheory/Global/ClassFormation.lean': "imports of Backport/ modules added, and the private import of `Global.PrescribedInvariant` replaced by its Backport/ version",
 'NumberTheory/ClassFieldTheory/Global/CorestrictionLocalization.lean': imp,
 'NumberTheory/ClassFieldTheory/Global/Kummer/Index.lean': "the import of `Global.Kummer.Norm` replaced by its Backport/ version, plus three further Backport/ imports",
 'NumberTheory/ClassFieldTheory/Global/LocalArtin/Compatibility.lean': imp,
 'NumberTheory/ClassFieldTheory/Global/LocalArtin/Frobenius.lean': imp,
 'NumberTheory/ClassFieldTheory/Global/Reciprocity.lean': imp,
 'NumberTheory/ClassFieldTheory/GlobalExistence/NormLimitation.lean': imp,
 'NumberTheory/ModularForms/LFunction/Sign.lean': "one proof unfolds `ModularForm.L` (no `ModularForm.L_apply_of_ne_zero` in the pinned Mathlib)",
 'NumberTheory/NumberField/InfinitePlace/Completion/Real.lean': "`exists_completionNormalizedAbsValue_eq` omitted (provided by the imported oct16 `InfinitePlace.Completion.Basic`)",
 'RepresentationTheory/Cyclic/Norm.lean': imp,
 'RepresentationTheory/Homological/ContCohomology/Corestriction/Mackey/Pullback.lean': imp,
 'RingTheory/Polynomial/Cyclotomic/PrimePow.lean': imp,
 'Topology/Algebra/Star/Completion.lean': "explicit continuity proofs instead of `fun_prop` (which times out at our pins)",
}
prov = re.compile(r'^(-- Vendored from Tau Ceti \(.*\), Apache-2\.0\.\n)', re.M)
for rel, n in notes.items():
    p = root + rel
    t = open(p, encoding='utf-8').read()
    assert '-- Modified for the Z-in-Q kernel:' not in t, rel
    t2, k = prov.subn(lambda m: m.group(1) + f"-- Modified for the Z-in-Q kernel: {n}.\n", t, count=1)
    assert k == 1, rel
    open(p, 'w', encoding='utf-8').write(t2)
    print(rel)
