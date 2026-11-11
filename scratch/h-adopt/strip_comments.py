import sys, re
def strip(s):
    out=[];i=0;depth=0
    while i<len(s):
        if s.startswith('/-',i): depth+=1;i+=2;continue
        if depth and s.startswith('-/',i): depth-=1;i+=2;continue
        if not depth and s.startswith('--',i):
            j=s.find('\n',i); i=len(s) if j<0 else j; continue
        if not depth: out.append(s[i])
        i+=1
    return re.sub(r'\s+',' ',''.join(out)).strip()
a=open(sys.argv[1]).read(); b=open(sys.argv[2]).read()
print(sys.argv[2], "code identical:", strip(a)==strip(b))
