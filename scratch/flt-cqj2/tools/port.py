"""Copy FLT (anthropics/fermats-last-theorem @ 6e837e75) modules into the CloudB2 vendor tree.
usage: python3 -I port.py FLT_SRC DEST_VENDOR_DIR MODULE...   (only modules whose dest file is absent)
Only changes: header comment, import paths relocated, FLT lakefile options as set_option lines."""
import sys, os, re, hashlib
src, dest, mods = sys.argv[1], sys.argv[2], sys.argv[3:]
PFX = 'ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.'
UTIL = 'ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util'
HDR = """/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: {mod}
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
"""
OPTS = """set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
"""
def reloc(m):
    if m == 'P2M.Util': return UTIL
    if m.startswith(('Definitions.', 'Theorems.', 'P2M.Sol.')): return PFX + m
    return m
for mod in mods:
    rel = mod.replace('.', '/') + '.lean'
    out = os.path.join(dest, rel)
    if os.path.exists(out): continue
    lines = open(os.path.join(src, rel), encoding='utf-8').read().split('\n')
    i = 0; imps = []; pre = []; incom = False
    while i < len(lines):
        l = lines[i]
        if incom:
            pre.append(l); incom = '-/' not in l
        elif l.startswith('/-'):
            pre.append(l); incom = '-/' not in l[2:]
        elif l.startswith('--'): pre.append(l)
        elif l.startswith('import '): imps.append('import ' + reloc(l.split()[1]))
        elif l.strip() != '': break
        i += 1
    body = '\n'.join(pre + [''] + lines[i:]) if pre else '\n'.join(lines[i:])
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with open(out, 'w', encoding='utf-8') as f:
        f.write(HDR.format(mod=mod) + '\n'.join(imps) + '\n\n' + OPTS + '\n' + body)
    print('ported', mod)
