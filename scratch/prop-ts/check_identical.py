import re,sys
def block(src,name):
    s=open(src).read()
    # docstring + def up to the next blank line
    i=s.index("def "+name+" ")
    j=s.rfind("/--",0,i)
    k=s.index("\n\n",i)
    return s[j:k]
for n in ["PropTS","PropTSAll"]:
    a=block("scratch/fibre-cover/FibreCover.lean",n); b=block("scratch/prop-ts/PropTS.lean",n)
    print(n, "IDENTICAL" if a==b else "DIFFERENT", len(a))
