"""Rename the vendored FLT declarations whose names clash with declarations already in the kernel's closure
(task neron-flt; adapted from flt-cqj2's rename_clash.py). Token-based: each listed last name component t becomes
t_nflt in every vendored file under ZInQKernel/Contrib/OneProof/NeronFLT/Vendor (import lines untouched). A wrong
rename cannot change meaning silently: the new names are fresh, so a token that referred to something else fails
to elaborate.  usage: python3 -I rename_clash.py TOKENS_FILE"""
import re, sys, glob
toks = [l.strip() for l in open(sys.argv[1]) if l.strip()]
IC = r"[\w'!?₀-₉ₐ-ₜᵢ-ᵪⱼ]"
rx = re.compile(r"(?<!" + IC + ")(" + "|".join(sorted(map(re.escape, toks), key=len, reverse=True)) + r")(?!" + IC + ")")
files = glob.glob('ZInQKernel/Contrib/OneProof/NeronFLT/Vendor/**/*.lean', recursive=True)
changed = 0
for f in files:
    s = open(f, encoding='utf-8').read()
    head, sep, body = s.partition('\n-/\n')
    if not sep: raise SystemExit('no header ' + f)
    lines = body.split('\n'); found = set(); out = []
    for l in lines:
        if l.startswith('import '): out.append(l); continue
        fs = rx.findall(l)
        if fs: found |= set(fs); l = rx.sub(lambda m: m.group(1) + '_nflt', l)
        out.append(l)
    if not found: continue
    head += '\n[port] name clash with declarations already in the kernel: renamed ' + ', '.join(
        f'`{t}` → `{t}_nflt`' for t in sorted(found)) + '.'
    open(f, 'w', encoding='utf-8').write(head + sep + '\n'.join(out)); changed += 1
print('files changed', changed)
