# For each N5 line block, find matching blocks in an upstream version (whitespace/CRLF-insensitive).
import sys, difflib
a=[l.rstrip() for l in open(sys.argv[1],encoding='utf8')]
b=[l.rstrip() for l in open(sys.argv[2],encoding='utf8')]
sm=difflib.SequenceMatcher(None,a,b,autojunk=False)
ops=sm.get_opcodes()
same=sum(i2-i1 for t,i1,i2,j1,j2 in ops if t=='equal')
print("N5 lines",len(a),"matched",same)
for t,i1,i2,j1,j2 in ops:
    if t!='equal' and (i2-i1)>0:
        print(t,"N5 %d-%d"%(i1+1,i2),"V %d-%d"%(j1+1,j2))
