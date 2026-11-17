"""[port] Mathlib v4.35: `List.TFAE.out` is 1-indexed; shift `.out i j` by one on the given FILE:LINE entries."""
import sys, re
for arg in sys.argv[1:]:
    p, n = arg.rsplit(':', 1); n = int(n)
    L = open(p, encoding='utf-8').read().split('\n')
    l = L[n - 1]
    new = re.sub(r'\.out (\d+) (\d+)', lambda m: '.out %d %d' % (int(m.group(1)) + 1, int(m.group(2)) + 1), l, count=1)
    assert new != l, arg
    ind = re.match(r'\s*', l).group(0)
    L[n - 1] = ind + '-- [port] Mathlib v4.35: `List.TFAE.out` is 1-indexed (same entries)\n' + new
    open(p, 'w', encoding='utf-8').write('\n'.join(L)); print('shifted', arg)
