"""assemble-port: delete from a part the def/abbrev blocks (with their preceding docstring) that Leaves.lean's leaf-fold
tail already declares in the same namespace, verbatim (checked IDENTICAL before deletion).
Usage: python3 -I mk/del_dups.py part.lean name1 name2 ..."""
import re, sys
path, names = sys.argv[1], sys.argv[2:]
L = open(path).read().split('\n')
out = []; i = 0; deleted = []
while i < len(L):
    m = re.match(r'^(def|abbrev) (\w+)', L[i])
    if m and m.group(2) in names:
        # drop the preceding docstring already copied to out
        k = len(out) - 1
        if k >= 0 and out[k].rstrip().endswith('-/'):
            while k >= 0 and not out[k].lstrip().startswith('/--'): k -= 1
            out = out[:k]
        j = i + 1
        while j < len(L) and L[j].startswith(' '): j += 1
        deleted.append(m.group(2)); i = j; continue
    out.append(L[i]); i += 1
open(path, 'w').write('\n'.join(out))
print(path, 'deleted', deleted)
