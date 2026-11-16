import re, sys, os
SRC = os.path.expanduser('~/flt-src')
DST = 'ZInQKernel/Contrib/CloudB3W12Tame/Vendor/AnthropicFLT'
MODP = 'ZInQKernel.Contrib.CloudB3W12Tame.Vendor.AnthropicFLT'
NS = 'ZInQ.Contrib.CloudW03NeronSurj.FLT'
# module name -> explicit argument list for the direct term in the Thm file
MODS = {
 'Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_isSeparable_residueField': 'K₀ 𝒪 u hu0 hu',
 'Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_perfectField': 'K 𝒪 u hu0 hu',
}
OPTS={'Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_isSeparable_residueField':'set_option backward.isDefEq.respectTransparency false'}
def header(path, changes):
    return f"""/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : {path}
  Retrieved      : 2026-11-16 (local clone at revision above, byte-for-byte before modification)
  Licence        : Apache License, Version 2.0 (see LICENSE and NOTICE in
                   ZInQKernel/Contrib/CloudB3W12Tame/Vendor/AnthropicFLT/)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original.
The changes are mechanical only; no statement, hypothesis, definition or proof term was
altered, weakened or omitted:
""" + ''.join(f"  * {c}\n" for c in changes) + "-/\n\n"
def retarget(lines):
    out=[]; n=0; dropped=0
    for l in lines:
        if l.strip()=='import P2M.Util': dropped+=1; continue
        m=re.match(r'import (Theorems|P2M\.Sol)\.(\S+)$', l.strip())
        if m: out.append(f'import {MODP}.{m.group(1)}.{m.group(2)}'); n+=1; continue
        out.append(l)
    return out,n,dropped
for mod,args in MODS.items():
    # Sol
    p=f'P2M/Sol/S_{mod}.lean'; src=open(f'{SRC}/{p}').read().rstrip('\n').split('\n')
    lines,n,d=retarget(src)
    i=max(k for k,l in enumerate(lines) if l.startswith('import'))
    nsline=[k for k,l in enumerate(lines) if l.startswith('namespace P2MW.')]
    assert len(nsline)==1 and not any(l.startswith('end P2MW.') for l in lines)
    inner=lines[nsline[0]].split()[1]
    opt=OPTS.get(mod)
    if opt:
        t=[k for k,l in enumerate(lines) if l.startswith('theorem solution')]; assert len(t)==1
        lines.insert(t[0], opt+' in')
    body=lines[:i+1]+['',f'namespace {NS}','']+lines[i+1:]+['',f'end {inner}','',f'end {NS}','']
    ch=[(f"compatibility option `{opt}` added in front of `theorem solution` (the source targets Lean 4.33.1; under Lean v4.35.0 / Mathlib 56a005855 the instance `Algebra.IsSeparable (Q.under K₀[X]).ResidueField Q.ResidueField` otherwise times out). It changes elaboration only, not the statement or the proof script." if opt else None),f"{n} internal `import`(s) retargeted to `{MODP}.*`." if n else None,
        f"{d} `import P2M.Util` removed (the file uses no `p2m_*` command).",
        f"1 scope the source leaves open at EOF closed explicitly (`end {inner}`) so the port namespace can be closed; Lean closes it implicitly at EOF in the original, so this is a no-op.",
        f"whole file wrapped in `namespace {NS} … end {NS}`."]
    os.makedirs(f'{DST}/P2M/Sol',exist_ok=True)
    open(f'{DST}/{p}','w').write(header(p,[c for c in ch if c])+'\n'.join(body))
    # Thm
    p=f'Theorems/Thm_{mod}.lean'; src=open(f'{SRC}/{p}').read().rstrip('\n').split('\n')
    lines,n,d=retarget(src)
    j=[k for k,l in enumerate(lines) if 'p2m_exact_reverting' in l]; assert len(j)==1
    l=lines[j[0]]
    m=re.search(r':= by p2m_exact_reverting @_root_\.(P2MW\.\S+\.solution)$', l); assert m
    lines[j[0]]=l[:m.start()]+f':=\n  {m.group(1)} {args}'
    i=max(k for k,l in enumerate(lines) if l.startswith('import'))
    body=lines[:i+1]+['',f'namespace {NS}','']+lines[i+1:]+['',f'end {NS}','']
    ch=[f"{n} internal `import`(s) retargeted to `{MODP}.*`.",
        f"{d} `import P2M.Util` removed.",
        f"`by p2m_exact_reverting @_root_.{m.group(1)}` (a custom tactic that reverts the context and applies the term) replaced by the direct term `{m.group(1)} {args}` (resolved inside the port namespace).",
        f"whole file wrapped in `namespace {NS} … end {NS}`."]
    os.makedirs(f'{DST}/Theorems',exist_ok=True)
    open(f'{DST}/{p}','w').write(header(p,ch)+'\n'.join(body))
print('ok')
