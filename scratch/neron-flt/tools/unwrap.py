"""Replace a ported module by CloudW03NeronSurj's Lean-4.35 port of the same FLT file, with its namespace wrapper removed.
usage: python3 -I unwrap.py MODULE...  (run from the repo root)"""
import sys, re, os
W03 = 'ZInQKernel/Contrib/CloudW03NeronSurj/Vendor/'
DST = 'ZInQKernel/Contrib/OneProof/NeronFLT/Vendor/AnthropicFLT/'
PFX = 'ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.'
UTIL = 'ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util'
NS = 'ZInQ.Contrib.CloudW03NeronSurj.FLT'
FLT = os.path.expanduser('~/flt-src/')
for mod in sys.argv[1:]:
    rel = mod.replace('.', '/') + '.lean'
    src = open(W03 + rel, encoding='utf-8').read()
    orig = open(FLT + rel, encoding='utf-8').read()
    dst = open(DST + rel, encoding='utf-8').read()
    hdr = dst[:dst.index('-/\n') + 3]  # our vendoring header
    opts = re.findall(r'^set_option (?:maxHeartbeats|synthInstance.maxHeartbeats|backward.isDefEq.respectTransparency.types|autoImplicit) .*$', dst, re.M)[:4]
    # drop CloudW03 header comment
    body = src[src.index('-/\n') + 3:] if src.startswith('/-') else src
    lines = body.split('\n'); out = []; imps = []
    keep_open = 'p2m_open' in orig
    for l in lines:
        if l.startswith('import '):
            m = l.split()[1]
            if m == 'ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil': m = UTIL
            m = m.replace('ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.', PFX)
            imps.append('import ' + m); continue
        if l.strip() in ('namespace ' + NS, 'end ' + NS): continue
        if l.startswith('w03_open "') and not keep_open and not l.rstrip().endswith(' in'): continue
        l = l.replace('_root_.' + NS + '.', '_root_.').replace(NS + '.', '').replace('w03_', 'p2m_')
        out.append(l)
    note = ('-- [port] Lean 4.35 repairs: this body is CloudW03NeronSurj\'s port of the same upstream file\n'
            '-- (ZInQKernel/Contrib/CloudW03NeronSurj/Vendor/' + rel + ') with its namespace wrapper removed.\n')
    text = hdr + '\n'.join(imps) + '\n\n' + '\n'.join(opts) + '\n\n' + note + '\n'.join(out)
    open(DST + rel, 'w', encoding='utf-8').write(text)
    print('unwrapped', mod)
