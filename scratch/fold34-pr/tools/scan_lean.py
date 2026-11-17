#!/usr/bin/env python3
"""Strip Lean comments (nested /- -/ and --) and string literals, then report forbidden tokens.
Usage: scan_lean.py FILE...   (prints file:line:token for each hit)"""
import re, sys
BAD = re.compile(r'(?<![\w.])(sorry|admit|native_decide|axiom|opaque|unsafe|implemented_by|extern|run_cmd|run_tac|run_elab|addDecl|skipKernelTC|reduceBool|ofReduceBool|csimp|macro|macro_rules|elab|elab_rules|syntax|initialize|builtin_initialize)(?![\w])|#eval|debug\.')
def strip(src):
    out=[]; i=0; n=len(src); depth=0
    while i<n:
        if depth==0 and src.startswith('--',i):
            j=src.find('\n',i); j=n if j<0 else j; i=j; continue
        if src.startswith('/-',i):
            depth+=1; i+=2; continue
        if depth>0 and src.startswith('-/',i):
            depth-=1; i+=2; continue
        if depth>0:
            out.append('\n' if src[i]=='\n' else ' '); i+=1; continue
        if src[i]=='"':
            j=i+1
            while j<n and src[j]!='"':
                j+= 2 if src[j]=='\\' else 1
            out.append('""'); i=j+1; continue
        out.append(src[i]); i+=1
    return ''.join(out)
hits=0
for f in sys.argv[1:]:
    s=strip(open(f,encoding='utf-8').read())
    for ln,line in enumerate(s.split('\n'),1):
        for m in BAD.finditer(line):
            print(f"{f}:{ln}:{m.group(0)}: {line.strip()[:120]}"); hits+=1
print(f"# {len(sys.argv)-1} files, {hits} hits", file=sys.stderr)
