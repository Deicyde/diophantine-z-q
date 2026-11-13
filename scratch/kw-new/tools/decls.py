import os,re,sys
KW=r'(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)'
decl=re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped|local)\s+)*'+KW+r'\s+([^\s:({\[]+)')
def decls(path):
    out=[]; stack=[]
    if not os.path.exists(path): return out
    txt=open(path,encoding='utf-8').read()
    # strip block comments
    txt=re.sub(r'/-.*?-/','',txt,flags=re.S)
    for line in txt.split('\n'):
        m=re.match(r'^\s*namespace\s+(\S+)',line)
        if m: stack.append(('ns',m.group(1))); continue
        m=re.match(r'^\s*(?:noncomputable\s+)?section\b\s*(\S*)',line)
        if m: stack.append(('sec',m.group(1))); continue
        m=re.match(r'^\s*end\b\s*(\S*)',line)
        if m and stack: stack.pop(); continue
        m=decl.match(line)
        if m:
            n=m.group(1)
            if n.startswith('_root_.'): full=n[7:]
            else:
                ns='.'.join(x for k,x in stack if k=='ns')
                full=(ns+'.'+n) if ns else n
            out.append(full)
    return out
def p(root,m): return os.path.join(root,*m.split('.'))+'.lean'
