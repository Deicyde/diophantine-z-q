"""Generate ZInQKernel/Contrib/OneProof/PanBergerSanity.lean from scratch/pb-sanity/Sanity1.lean:
expand the two local notations (O, ξ) outside comments (the contribution scan rejects `notation`),
and replace the header."""
import re, sys
src, dst, header = sys.argv[1], sys.argv[2], sys.argv[3]
text = open(src).read()
lines = text.split('\n')
# drop the local notation lines
lines = [l for l in lines if not l.startswith('local notation')]
out = []
in_block = 0
XI_RE = re.compile(r"(?<![\w'])ξ(?![\w'])")
O_RE = re.compile(r"(?<![\w.'])O(?![\w'♭])")
for l in lines:
    res = ''
    i = 0
    while i < len(l):
        if in_block:
            j = l.find('-/', i)
            k = l.find('/-', i)
            if k != -1 and (j == -1 or k < j):
                in_block += 1; res += l[i:k+2]; i = k + 2; continue
            if j == -1:
                res += l[i:]; i = len(l); continue
            in_block -= 1; res += l[i:j+2]; i = j + 2; continue
        k = l.find('/-', i)
        c = l.find('--', i)
        stops = [x for x in (k, c) if x != -1]
        stop = min(stops) if stops else len(l)
        code = l[i:stop]
        code = XI_RE.sub('(ZInQ.Contrib.G9.BdrKer.Cp.xi p)', code)
        code = O_RE.sub('𝓞_ℂ_[p]', code)
        res += code
        if stop == len(l):
            i = len(l)
        elif stop == c and (k == -1 or c < k):
            res += l[c:]; i = len(l)
        else:
            in_block += 1; res += '/-'; i = k + 2
    out.append(res)
body = '\n'.join(out)
# replace everything before 'noncomputable section' by the header
idx = body.index('noncomputable section')
imports = '\n'.join(x for x in body[:idx].split('\n') if x.startswith('import'))
open(dst, 'w').write(imports + '\n\n' + open(header).read().rstrip('\n') + '\n\n' + body[idx:])
