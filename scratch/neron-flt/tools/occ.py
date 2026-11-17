import re,sys,collections
V='ZInQKernel/Contrib/CloudB2X0Transitive/Vendor/AnthropicFLT/'
files=[l.strip() for l in open('scratch/flt-cqj2/new_files.txt') if l.strip()]
toks="XYIdeal_isMaximal XYIdeal_ne_bot genericPoint genericX genericY infinite_point Coeff addXYZ_smulEval cusp dblXYZ_smulEval invar map_invar map_specialize map_ψc preΨ₄_add_Ψ₂Sq_sq preΨ₄_add_ψ₂_pow_four smulEval specialize φ_mul_ψ ψc ψc_neg normEDS_mul_complEDS normEDS_mul_complEDS_div universalNormEDS_ne_zero".split()
IC=r"[\w'!?₀-₉ₐ-ₜᵢ-ᵪⱼ]"
for t in toks:
    rx=re.compile(r"(?<!"+IC+")"+re.escape(t)+r"(?!"+IC+")")
    c=collections.Counter()
    for f in files:
        s=open(f).read()
        n=len(rx.findall(s))
        if n: c[f.split('AnthropicFLT/')[1]]=n
    print(t, sum(c.values()), len(c))
    if len(sys.argv)>1 and t in sys.argv[1:]:
        for k,v in c.items(): print('   ',v,k)
