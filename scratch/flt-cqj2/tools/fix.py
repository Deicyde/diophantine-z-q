"""Apply mechanical Mathlib-v4.35 renames to ported files; each changed line gets a `-- [port]` comment above it.
usage: python3 -I fix.py FILE..."""
import sys, re
RULES = [
  (r'Ideal\.isMaximal_of_isIntegral_of_isMaximal_comap \(R := ', 'Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := ',
   'Mathlib v4.35: the algebra form of `isMaximal_of_isIntegral_of_isMaximal_comap` is `..._under`'),
]
for p in sys.argv[1:]:
    lines = open(p, encoding='utf-8').read().split('\n'); out = []; n = 0
    for l in lines:
        new = l; why = []
        for pat, rep, msg in RULES:
            if re.search(pat, new): new = re.sub(pat, rep, new); why.append(msg)
        if new != l:
            ind = re.match(r'\s*', l).group(0); out.append(ind + '-- [port] ' + '; '.join(why)); n += 1
        out.append(new)
    if n:
        open(p, 'w', encoding='utf-8').write('\n'.join(out)); print(p.split('/')[-1], n)
