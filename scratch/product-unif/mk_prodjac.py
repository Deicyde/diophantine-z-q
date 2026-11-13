import re
m='scratch/metrization/'
def rd(f): return open(m+f).read()
def cut(s, end_marker):
    return s[:s.index(end_marker)]
J=open('scratch/product-unif/JacDet.lean').read()
J=J[:J.index("#print axioms")]
parts=[]
parts.append(cut(rd('part_prodgeo.lean'),"/-- **Glue (pure Mathlib): product lattices.**")+"end ZInQ.Metrization\n")
pl=rd('part_prodlat.lean')
parts.append(pl[:pl.index("/-- `ℂ^{g₁+g₂} ≃ ℂ^{g₁} × ℂ^{g₂}` over `ℝ`. -/")]+"end Proof\n\nend ZInQ.Metrization\n")
parts.append(cut(rd('part_produnif.lean'),"/-- **`ProductUniformization` from")+"end ZInQ.Metrization\n")
parts.append(cut(rd('part_prodsplit.lean'),"/-- **`ProductHodgeCompat` from")+"end ZInQ.Metrization\n")
parts.append(cut(rd('part_prodjac.lean'),"/-- **`ProductMetrizationGeo` from `ProductUniformizationAnalytic` and")+"end ZInQ.Metrization\n")
parts.append(cut(rd('part_produnif2.lean'),"/-- **`ProductMetrizationGeo` from `ProductLocalStructure`")+"end ZInQ.Metrization\n")
body="\n".join(parts)
body=re.sub(r"^(open NumberField DefFaltings.*)$", r"\1\nopen PkgI3 (AbVar)", body, flags=re.M)
hdr = J.replace("# product-unif: metrization's proof of `JacDetDescends`, on the kernel's types",
 "# product-unif: metrization's `JacDetDescends`, `productJacobian`, `productUniformizationAnalytic_of`, on the kernel's types")
note = """
/-! Further verbatim copies from `scratch/metrization/` (only `open PkgI3 (AbVar)` added, the
declarations after the cut points dropped): `part_prodgeo.lean` up to `ProductLatticeFacts`
(exclusive), `part_prodlat.lean` up to `blockLinearEquiv` (exclusive), `part_produnif.lean` up to
`productUniformization_of` (exclusive), `part_prodsplit.lean` up to `productHodgeCompat_of`
(exclusive), `part_prodjac.lean` up to `productMetrizationGeo_of'''` (exclusive),
`part_produnif2.lean` up to `productMetrizationGeo_of_local` (exclusive). -/

"""
out=hdr+note+body+"\n#print axioms ZInQ.Metrization.jacDetDescends\n#print axioms ZInQ.Metrization.productJacobian\n#print axioms ZInQ.Metrization.productUniformizationAnalytic_of\n"
open('scratch/product-unif/ProdJac.lean','w').write(out)
