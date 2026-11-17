"""Compare two DumpCompact hash dumps (scratch/fold33-piczero/DumpCompact.lean output).
Usage: python3 scratch/fold33-piczero/hashdiff.py BEFORE AFTER [OUT]
Prints the counts (before, after, only before, only after, changed) and writes the lists to OUT (default stdout):
lines `- name module` (only before), `+ name module` (only after), `~ name module type|value` (changed)."""
import sys

def load(p):
    d = {}
    for l in open(p):
        parts = l.split()
        if len(parts) < 5:
            continue
        # name module levelParams... typehash valuehash; levelParams is a list printed with spaces possibly
        d[parts[0]] = (parts[1], parts[-2], parts[-1])
    return d

a, b = load(sys.argv[1]), load(sys.argv[2])
only_a = sorted(set(a) - set(b))
only_b = sorted(set(b) - set(a))
changed = []
for n in sorted(set(a) & set(b)):
    if a[n] != b[n]:
        what = []
        if a[n][1] != b[n][1]:
            what.append("type")
        if a[n][2] != b[n][2]:
            what.append("value")
        if a[n][0] != b[n][0]:
            what.append("module")
        changed.append((n, b[n][0], "+".join(what)))
print(f"before {len(a)}, after {len(b)}, only before {len(only_a)}, only after {len(only_b)}, changed {len(changed)}")
out = open(sys.argv[3], "w") if len(sys.argv) > 3 else sys.stdout
for n in only_a:
    out.write(f"- {n} {a[n][0]}\n")
for n in only_b:
    out.write(f"+ {n} {b[n][0]}\n")
for n, m, w in changed:
    out.write(f"~ {n} {m} {w}\n")
