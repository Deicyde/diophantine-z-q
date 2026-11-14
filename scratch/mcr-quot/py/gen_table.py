import json, itertools, sys
d=json.load(open('/tmp/units.json'))
def N(a,b,c,dd): return (a*a+a*c+c*c-2*b*b-2*b*dd-2*dd*dd)%3
def v(t): return "![" + ", ".join(str(x) for x in t) + "]"
lines=[]
for a,b,c,dd in itertools.product(range(3),repeat=4):
    if N(a,b,c,dd)==0:
        lines.append("  · intro h; exact absurd (by decide) h")
    else:
        n,m=d[str((a,b,c,dd))]
        lines.append(f"  · exact fun _ => ⟨{v(n)}, {v(m)}, by decide, by decide, by decide, by decide, by decide, by decide⟩")
print("\n".join(lines))
