"""Check that the Props of this task are textually identical (docstring included) to their sources.
Usage (repo root): python3 -I scratch/image-plane/py/verbatim.py"""
import re

def decl(text, name):
    m = re.search(r'(?m)^(?:noncomputable )?(?:def|abbrev|theorem) ' + re.escape(name) + r'\b', text)
    if not m:
        return None
    start = m.start()
    pre = text[:start]
    k = pre.rfind('/--')
    if k != -1 and re.fullmatch(r'(?s)/--.*?-/\s*(open .* in\s*)?', pre[k:]):
        start = k
    # also include a preceding `open ... in` line before the docstring
    pre2 = text[:start]
    m2 = re.search(r'(?m)^open [^\n]* in\n$', pre2)
    if m2:
        start = m2.start()
    end = text.find('\n\n', m.end())
    return text[start:end if end != -1 else len(text)]

CG = 'scratch/curve-glue/'
IP = 'scratch/image-plane/'
checks = [
    # (my file, source file, names)
    (IP + 'ImageClosed.lean', CG + 'AlgDep.lean.part', ['ImageClosed']),
    (IP + 'ImageClosed.lean', CG + 'C2K.lean',
     ['ptOf', 'ev', 'ev_res', 'ev_eq_zero_iff', 'ev_top', 'cst', 'ev_cst', 'res', 'res_res',
      'exists_point_of_isLocallyClosed', 'isUnit_of_ev_ne_zero', 'val_of_mem', 'val_of_not_mem',
      'ev_f_mul_g', 'ev_g_eq_zero', 'mem_V_of_not_mem_U', 'res_cst', 'ev_eq_of_nilpotent']),
    (IP + 'ImageClosed.lean', CG + 'C3K.lean', ['evalXY']),
    (IP + 'AlgDepProof.lean', CG + 'AlgDep.lean.part', ['ImageClosed', 'AlgDep']),
    (IP + 'AlgDepProof.lean', CG + 'C2K.lean', ['ConstOrOntoAlgClosed']),
    (IP + 'AlgDepProof.lean', CG + 'ClauseC.lean.part', ['ComponentIrreducible']),
    (IP + 'AlgDepProof.lean', 'scratch/infra-smooth-dim/SmoothDimProps.lean', ['SmoothStalkDimOne']),
    (IP + 'ImagePlaneFinal.lean', CG + 'C3K.lean', ['ImagePlaneCurveClosed', 'ImagePlaneCurve',
      'RatFactorAlgClosed', 'ConstOrOntoAlgClosed']),
    (IP + 'ImagePlaneFinal.lean', CG + 'ClauseC.lean.part', ['ImagePlaneCurveIrr', 'ComponentIrreducible']),
    (IP + 'ImagePlaneFinal.lean', CG + 'AlgDep.lean.part', ['AlgDep', 'ImageClosed']),
]
ok = True
for mine, src, names in checks:
    a, b = open(mine).read(), open(src).read()
    for n in names:
        x, y = decl(a, n), decl(b, n)
        same = x is not None and x == y
        ok &= same
        print(('IDENTICAL ' if same else 'DIFFERENT ') + f'{n:34s} {mine} vs {src}')
# each name defined once in the composite
fin = open(IP + 'ImagePlaneFinal.lean').read()
for n in ['ImagePlaneCurveClosed', 'ImageClosed', 'AlgDep', 'ConstOrOntoAlgClosed', 'ComponentIrreducible',
          'SmoothStalkDimOne', 'ImagePlaneCurveIrr']:
    c = len(re.findall(r'(?m)^def ' + n + r'\b', fin)); ok &= (c == 1)
    print(f'{"ONCE     " if c == 1 else "COUNT=" + str(c)} def {n} in ImagePlaneFinal.lean')
# composite = MobiusFinal verbatim prefix
mf = open(CG + 'MobiusFinal.lean').read()
pre = mf[:mf.index('\nend\n\n#print axioms') + len('\nend\n')]
s = fin.startswith(pre); ok &= s
print(('IDENTICAL ' if s else 'DIFFERENT ') + 'ImagePlaneFinal.lean starts with MobiusFinal.lean (minus #print lines) verbatim')
print('ALL OK' if ok else 'MISMATCH')
