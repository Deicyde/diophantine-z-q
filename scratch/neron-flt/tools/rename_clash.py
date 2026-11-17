"""Rename the 24 FLT declarations whose names clash with Tau Ceti (task flt-cqj2).
Token-based: the last name component t becomes t_aflt in every new vendored file
(new_files.txt).  A wrong rename cannot change meaning silently: the new names are
fresh, so a token that referred to something else fails to elaborate."""
import re
toks="XYIdeal_isMaximal XYIdeal_ne_bot genericPoint genericX genericY infinite_point Coeff addXYZ_smulEval cusp dblXYZ_smulEval invar map_invar map_specialize map_ψc preΨ₄_add_Ψ₂Sq_sq preΨ₄_add_ψ₂_pow_four smulEval specialize φ_mul_ψ ψc ψc_neg normEDS_mul_complEDS normEDS_mul_complEDS_div universalNormEDS_ne_zero".split()
IC=r"[\w'!?₀-₉ₐ-ₜᵢ-ᵪⱼ]"
rx=re.compile(r"(?<!"+IC+")("+"|".join(sorted(map(re.escape,toks),key=len,reverse=True))+r")(?!"+IC+")")
files=[l.strip() for l in open('scratch/flt-cqj2/new_files.txt') if l.strip()]
changed=0
for f in files:
    s=open(f).read()
    head,sep,body=s.partition('\n-/\n')   # keep the vendoring header comment intact
    if not sep: raise SystemExit('no header '+f)
    found=sorted(set(rx.findall(body)))
    if not found: continue
    body=rx.sub(lambda m:m.group(1)+'_aflt',body)
    head+='\n[port] Tau Ceti name clash: renamed '+', '.join(f'`{t}` → `{t}_aflt`' for t in found)+'.'
    open(f,'w').write(head+sep+body); changed+=1
print('files changed',changed)
