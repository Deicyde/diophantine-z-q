"""Generate parts/e10_propts.lean from scratch/prop-ts-glue/PropTSGlue.lean (repo root, python3 -I)."""
L=open('scratch/prop-ts-glue/PropTSGlue.lean').read().split('\n')
k=next(i for i,l in enumerate(L) if l.startswith('namespace PropTSRed'))
keep=L[24:29]+['']+L[k:]
txt='\n'.join(l for l in keep if not l.startswith('#print'))
hdr='''/-! ## g0-assemble3: prop-ts and prop-ts-glue (scratch/prop-ts-glue/PropTSGlue.lean = prop-ts's PropTS.lean + t-purity3's
PurityDim2.lean + prop-ts-glue's appendix), verbatim: lines 25-29 (opens, `noncomputable section`) and %d-end; its lines
1-24 (imports, header) and 30-%d (`namespace G0ModField` with fibre-cover's `PropTS`, `PropTSAll`, = part a70) are not
repeated. `#print` lines dropped. -/
''' % (k+1, k)
open('scratch/g0-assemble3/parts/e10_propts.lean','w').write(hdr+txt+'\n')
