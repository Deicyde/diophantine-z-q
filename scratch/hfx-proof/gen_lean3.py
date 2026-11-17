r"""hfx-proof: generate the Lean table for n = 3 (mod 8): residues r = hc(omega) mod 4,
the 2-orbit (p1,p2), the root rc of the 6-orbit, and merge witnesses (x, y, mu index, s) for t -> root(t)."""
exec(open('gen_tables.py').read().split('# ---------- n = 3 mod 8')[0])
def idx(t): return 4*t[0] + 2*t[1] + t[2]
def tlit(t): return "(%d, %d, %d)" % t
entries = []
seen = set()
for a, b, c in product(range(1, 16, 2), repeat=3):
    W = ((1 + c)//2, (a - c)//2, (b - c)//2, c)
    r = md(W, 4)
    if r in seen: continue
    seen.add(r)
    cls0 = [t for t in T8 if find_witness(r, t, (0,0,0), False, 4) is not None]
    other = [t for t in T8 if t not in cls0]
    P = cls0 if len(cls0) == 2 else other
    C = other if len(cls0) == 2 else cls0
    assert len(P) == 2 and len(C) == 6
    p1, p2 = P[0], P[1]; rc = C[0]
    wits = []
    for t in T8:
        root = p1 if t in P else rc
        w = find_witness(r, t, root, False, 4)
        assert w is not None and w[4] == 0
        wits.append(w[:4])
    entries.append((r, p1, p2, rc, wits))
assert len(entries) == 64
lines = []
for (r, p1, p2, rc, wits) in entries:
    ws = ", ".join("(%d, %d, %d, %d)" % w for w in wits)
    lines.append("  ⟨⟨%d, %d, %d, %d⟩, %s, %s, %s, [%s]⟩" % (r + (tlit(p1), tlit(p2), tlit(rc), ws)))
open('tab3.lean.txt', 'w').write("def tab3 : List E3 := [\n" + ",\n".join(lines) + "]\n")
print(len(entries), "entries")
