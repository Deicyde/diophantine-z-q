r"""hfx-proof: generate the Lean table for n = 1 (mod 8): residues r = hc(omega) mod 8,
omega = tau(sqrt(-n)) = a i + b j + c k (4 | c), the class index of each t (roots 000, 110, 101) and merge
witnesses (x, y, mu index, s, b) for t -> root(t) (b = 1: alpha a uniformizer, rho = (1+i) s mu)."""
exec(open('gen_tables.py').read().split('# ---------- n = 3 mod 8')[0])
roots = [(0,0,0), (1,1,0), (1,0,1)]
entries = []
seen = set()
for a, b, c in product(range(8), repeat=3):
    if c % 4 or (a*a + b*b + c*c) % 8 != 1: continue
    W = hc_of_pure(a, b, c)
    r = md(W, 8)
    if r in seen: continue
    seen.add(r)
    cls = []; wits = []
    for t in T8:
        found = None
        for k, rt in enumerate(roots):
            w = find_witness(r, t, rt, True, 8)
            if w is not None:
                assert found is None
                found = (k, w)
        assert found is not None
        cls.append(found[0]); wits.append(found[1])
    entries.append((r, cls, wits))
assert len(entries) == 32
lines = []
for (r, cls, wits) in entries:
    ws = ", ".join("(%d, %d, %d, %d, %d)" % w for w in wits)
    cs = ", ".join(str(k) for k in cls)
    lines.append("  ⟨⟨%d, %d, %d, %d⟩, [%s], [%s]⟩" % (r + (cs, ws)))
open('tab1.lean.txt', 'w').write("def tab1 : List E1 := [\n" + ",\n".join(lines) + "]\n")
print(len(entries), "entries")
