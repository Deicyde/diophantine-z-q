"""Audit (adapted from flt-cqj2): every line of each vendored file that differs from upstream (~/flt-src) is
classified as import, set_option, clash rename (equal to upstream after deleting `_nflt`), or [port]-marked (the
line or a line within 3 above/below carries `[port]`). The nine modules whose bodies are CloudW03NeronSurj's port
(first body line `-- [port] Lean 4.35 repairs: this body is CloudW03...`) are listed separately. Prints any other
difference."""
import difflib, glob, re
cnt = {'rename': 0, 'port': 0, 'import': 0, 'setopt': 0, 'other': 0, 'cloudw03_body_files': 0}
for f in sorted(glob.glob('ZInQKernel/Contrib/OneProof/NeronFLT/Vendor/AnthropicFLT/**/*.lean', recursive=True)):
    rel = f.split('AnthropicFLT/')[1]
    up = open('/home/jackmccarthy/flt-src/' + rel).read().split('\n')
    loc = open(f).read().split('\n-/\n', 1)[1]
    if 'this body is CloudW03NeronSurj' in loc: cnt['cloudw03_body_files'] += 1; print('CLOUDW03-BODY', rel); continue
    loc = loc.split('\n')
    sm = difflib.SequenceMatcher(None, up, loc, autojunk=False)
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == 'equal': continue
        for j in range(j1, j2):
            l = loc[j]
            if l.startswith('import '): cnt['import'] += 1; continue
            if l.startswith('set_option ') and j < 40: cnt['setopt'] += 1; continue
            if l.replace('_nflt', '') in up[max(0, i1 - 2):i2 + 2]: cnt['rename'] += 1; continue
            if any('[port]' in loc[k] for k in range(max(0, j - 3), min(len(loc), j + 4))): cnt['port'] += 1; continue
            if l.strip() == '': continue
            cnt['other'] += 1; print('OTHER', rel, j + 1, l[:150])
        if tag in ('delete', 'replace') and j2 == j1:
            for i in range(i1, i2):
                if up[i].startswith('import '): cnt['import'] += 1
                elif any('[port]' in loc[k] for k in range(max(0, j1 - 3), min(len(loc), j1 + 4))): cnt['port'] += 1
                else: cnt['other'] += 1; print('DELETED', rel, i + 1, up[i][:150])
print(cnt)
