"""curves-g: check that the statements of the group-G fields (and the definitions they use) in
leaf-fold3's flat file scratch/leaf-fold3/Leaves3.lean are verbatim the kernel owners' texts.
Run from the repository root: python3 scratch/curves-g/py/verbatim_check.py"""
import re, sys
flat = open('scratch/leaf-fold3/Leaves3.lean').read()
own = {
  'ZInQKernel/HDecomp/ModCurves/Defs.lean': ['IsCurve', 'SpecQ', 'IsX1Model', 'RatPt', 'IsJacobian',
      'JacobianExists', 'IsJ1', 'fieldX1', 'xCoord', 'EjBar', 'Ej', 'Qj', 'Kbar'],
  'ZInQKernel/HDecomp/ModCurves/Leaves.lean': ['DimJ1Genus', 'dim_J1_le'],
  'ZInQKernel/HDecomp/ModCurves/Genus.lean': ['genus', 'belyiDeg', 'nu2', 'nu3', 'nuInf', 'pmSubgroup'],
  'ZInQKernel/HDecomp/ModCurves/X1Belyi.lean': ['CurveOfFunctionFieldQ', 'ConstantFieldIsQ',
      'HasRationalPlace', 'ratHom', 'X1RationalCusp'],
}
bad = 0
for f, names in own.items():
    src = open(f).read()
    for n in names:
        # the declaration with its docstring (statement = code part), up to the next blank line
        m = re.search(r"(/--(?:(?!-/).)*-/\n)?[^\n]*\b(?:def|abbrev|class|structure|theorem)\s+" + re.escape(n)
                      + r"\b.*?(?=\n\n)", src, re.S)
        if m is None:
            print(f"{n}: NOT FOUND in {f}"); bad += 1; continue
        blk = m.group(0)
        code = blk[len(m.group(1)):] if m.group(1) else blk   # the declaration without its docstring
        k = flat.count(code)
        kd = flat.count(blk)
        print(f"{n} ({f.split('/')[-1]}): code {len(code.splitlines())} lines, verbatim copies in Leaves3.lean: {k}"
              + ("" if kd else "  [docstring differs]"))
        if k == 0: bad += 1
print("ALL VERBATIM" if bad == 0 else f"{bad} NOT VERBATIM")
sys.exit(1 if bad else 0)
