import cypari2
pari = cypari2.Pari()
pari.default("realprecision", 60)
print(pari('mf=mfinit([13,2,Mod(4,13)],0); L=mfeigenbasis(mf); [#L, mfdim(mf)]'))
print(pari('f=L[1]; mfparams(f)'))
print(pari('mffields(mf)'))
print(pari('E=mfembed(f, mfcoefs(f,5)); E'))
print(pari('mfatkineigenvalues(mf,13)'))
