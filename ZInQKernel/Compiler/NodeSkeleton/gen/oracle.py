# Oracle generation for the checking builder HP (ZInQKernel/Compiler/NodeSkeleton/Core.lean).
from sim import B, construction, prog
from collections import defaultdict

W = 16
LANEBASE = 1 << 42

def pairB(a, b): return b*b + a if a < b else a*a + a + b
def opkey(op, a, b): return 5*pairB(a, b) + 3 + op
def intkey(c): return 2*c if c >= 0 else 2*(-c-1) + 1

class TB(B):
    """Builder recording events."""
    def __init__(s, k):
        super().__init__(k); s.ev = []
    def node(s, n):
        j = s.table.get(n)
        hit = j is not None
        if not hit:
            j = len(s.nodes); s.table[n] = j; s.nodes.append(n)
        if n[0] == 'const': s.ev.append(('const', n[1], j, hit))
        else: s.ev.append(('op', 0 if n[0] == 'add' else 1, n[1], n[2], j, hit))
        return j
    def fresh(s):
        s.ev.append(('fresh', len(s.nodes))); return super().fresh()
    def power(s, P, Q, R):
        s.ev.append(('call', len(s.nodes))); return super().power(P, Q, R)

def run_full():
    s = TB(2)
    phi = construction(s, prog, 204, 2)
    E0 = len(s.nodes)
    s.encode(phi)
    return s, phi, E0

def make_oracle(s, E0):
    ev = s.ev
    # groups of op misses by youngest child
    groups = defaultdict(list)
    for e in ev:
        if e[0] == 'op' and not e[5]:
            groups[max(e[2], e[3])].append(e[4])
    far = {y for y, ms in groups.items() if any(i - y > W for i in ms)}
    # lanes
    lane = {}
    for y in far:
        if groups[y][0] < E0: lane[y] = 0
        elif y == E0: lane[y] = 1
    last = {}
    nl = 2
    for e in ev:
        if e[0] != 'op' or e[5]: continue
        y = max(e[2], e[3]); i = e[4]
        if y not in far: continue
        ent = y * LANEBASE + opkey(e[1], e[2], e[3])
        if y in lane:
            l = lane[y]
            if l >= 2: assert last[l] < ent
            last[l] = ent; continue
        best = None
        for l, v in last.items():
            if l >= 2 and v < ent and (best is None or v > last[best]): best = l
        if best is None: best = nl; nl += 1
        lane[y] = best; last[best] = ent
    nlanes = max(lane.values()) + 1
    # hot: targets of hits
    hits_on = defaultdict(list)
    for t, e in enumerate(ev):
        if e[0] == 'op' and e[5]: hits_on[e[4]].append(t)
    lasthit = {j: max(ts) for j, ts in hits_on.items()}
    codes = []
    for t, e in enumerate(ev):
        if e[0] != 'op': continue
        if e[5]:
            codes.append(1 + 8 * (1 if lasthit[e[4]] == t else 0))
        else:
            y = max(e[2], e[3]); i = e[4]
            hi = 1 if i in hits_on else 0
            if y in far: codes.append(2 + lane[y] + 8 * hi)
            else: codes.append(0 + 8 * hi)
    hubs = sorted(y * 8 + lane[y] for y in far)
    lanes = [[] for _ in range(nlanes)]
    for e in ev:
        if e[0] == 'op' and not e[5]:
            y = max(e[2], e[3])
            if y in far: lanes[lane[y]].append(y * LANEBASE + opkey(e[1], e[2], e[3]))
    return codes, hubs, lanes

if __name__ == '__main__':
    s, phi, E0 = run_full()
    codes, hubs, lanes = make_oracle(s, E0)
    print(len(codes), len(hubs), [len(l) for l in lanes])
