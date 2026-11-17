import itertools
rows=[tuple(int(x) for x in l.split()[:4]) for l in open('lev32b_out.txt')]
def test(fa, fc, mod):
    d={}
    for a,c,s,t in rows:
        key=(a%fa, c%fc)
        v=(s%mod,t%mod)
        if key in d and d[key]!=v: return False
        d[key]=v
    return True
for mod in [2]:
  for fa in [8,16,32,64,128,256,3*64,5*64]:
    for fc in [32,64,128,256,512,3*32*8]:
        print(mod,fa,fc,test(fa,fc,mod))
def test2(fa, fc, fn):
    d={}
    for a,c,s,t in rows:
        key=(a%fa, c%fc); v=fn(s,t)
        if key in d and d[key]!=v: return False
        d[key]=v
    return True
for name,fn in [('s',lambda s,t:s%2),('t',lambda s,t:t%2),('s+t',lambda s,t:(s+t)%2)]:
  for fa in [32,64,128,256]:
    for fc in [64,128,256,512]:
      if test2(fa,fc,fn): print(name,fa,fc)
