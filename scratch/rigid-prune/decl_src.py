import sys,re,subprocess
# usage: decl_src.py file name -> prints declaration body (until next top-level decl)
f,name=sys.argv[1],sys.argv[2]
short=name.split('.')[-1]
lines=open(f).read().split('\n')
start=None
for i,l in enumerate(lines):
    if re.match(r'^(private )?(noncomputable )?(theorem|def|lemma|abbrev|structure) '+re.escape(short)+r'\b',l):
        start=i;break
if start is None: print("NOTFOUND",name); sys.exit()
end=start+1
while end<len(lines) and not re.match(r'^(/--|@\[|(private )?(noncomputable )?(theorem|def|lemma|abbrev|structure|end|namespace|section|open|#)|/-!)',lines[end]): end+=1
print(f"== {name} {f}:{start+1}-{end}")
print('\n'.join(lines[start:end]))
