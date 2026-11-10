"""List every \\cite in a line range of a TeX source, with optional locator.
Usage: python3 -I cites.py FILE START END
Prints: line<TAB>locator<TAB>key, one per cited key. Prints no other manuscript text."""
import re, sys
path, a, b = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
lines = open(path, encoding='utf-8', errors='replace').read().split('\n')
pat = re.compile(r'\\cite[pt]?\*?(?:\[([^\]]*)\])?\{([^}]*)\}')
n = 0
for i in range(a, b + 1):
    for m in pat.finditer(lines[i - 1]):
        for k in m.group(2).split(','):
            n += 1
            print(f"{i}\t{m.group(1) or ''}\t{k.strip()}")
print(f"# total {n}", file=sys.stderr)
