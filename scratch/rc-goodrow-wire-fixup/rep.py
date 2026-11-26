import sys,json
# usage: rep.py file  (reads pairs JSON from stdin)
f=sys.argv[1]; s=open(f).read()
for old,new in json.load(sys.stdin):
    n=s.count(old)
    if n!=1: sys.exit(f"{f}: count {n} for {old[:60]!r}")
    s=s.replace(old,new)
open(f,'w').write(s)
