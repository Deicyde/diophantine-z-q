# Python mirror of the Lean checking builder HP.
from sim import B, construction, prog
from oracle import *

class HS:
    def __init__(s, len_, next_, adds, muls, consts, win, hot, codes, hubs, lanes, ok=True):
        s.len, s.next, s.adds, s.muls = len_, next_, adds, muls
        s.consts, s.win, s.hot = list(consts), list(win), list(hot)   # win newest first
        s.codes, s.hubs, s.lanes, s.ok = list(codes), list(hubs), [list(l) for l in lanes], ok
        s.ci = 0; s.hi = 0; s.li = [0]*len(lanes)   # cursors (instead of popping)

class HB(B):
    def __init__(s, st):
        s.st = st; s.nodes = None
    def hubstep(s):
        st = s.st
        if st.hi < len(st.hubs) and st.hubs[st.hi] // 8 == st.len:
            st.hi += 1; return 1
        return 0
    def create_plain(s, k, nx):
        st = s.st
        f = s.hubstep()
        st.win.insert(0, 2*k + f); st.len += 1; st.next = nx
    def fresh(s):
        j = s.st.len; s.create_plain(5*s.st.next + 2, s.st.next + 1); return j
    def constant(s, c):
        st = s.st; ik = intkey(c)
        for (a, j) in st.consts:
            if a == ik: return j
        j = st.len
        st.consts.insert(0, (ik, j))
        s.create_plain(5*ik + 1, st.next); return j
    def power(s, P, Q, R):
        j = s.st.len; s.create_plain(0, s.st.next + 79); return ('call', j)
    def node(s, n):
        if n[0] == 'const': return s.constant(n[1])
        st = s.st
        op = 0 if n[0] == 'add' else 1; a, b = n[1], n[2]
        if st.ci >= len(st.codes): st.ok = False; return 0
        c = st.codes[st.ci]; st.ci += 1
        k = opkey(op, a, b); kind = c % 8
        if kind == 1:
            for idx, (kk, j) in enumerate(st.hot):
                if kk == k:
                    del st.hot[idx]
                    if c // 8 == 0: st.hot.insert(0, (k, j))
                    s.hotcost += idx
                    return j
            st.ok = False; return 0
        y = max(a, b)
        if kind == 0:
            d = st.len - 1 - y
            okc = y < st.len and len(st.win) > d and all(st.win[i] // 2 != k for i in range(d)) and st.win[d] % 2 == 0
            s.scancost += d
        else:
            l = kind - 2
            ent = y * LANEBASE + k
            okc = y < st.len and k < LANEBASE and st.li[l] < len(st.lanes[l]) and st.lanes[l][st.li[l]] == ent
            if st.li[l] < len(st.lanes[l]) and st.lanes[l][st.li[l]] == ent: st.li[l] += 1
        if not okc:
            if s.verbose: print('check failed at', st.len, n, c)
            st.ok = False
        j = st.len
        f = s.hubstep()
        st.win.insert(0, 2*k + f); st.len += 1
        if op == 0: st.adds += 1
        else: st.muls += 1
        if c // 8 == 1: st.hot.insert(0, (k, j))
        return j

if __name__ == '__main__':
    s, phi, E0 = run_full()
    codes, hubs, lanes = make_oracle(s, E0)
    st = HS(2, 2, 0, 0, [], [2*(5*0+2), 2*(5*1+2)][::-1], [], codes, hubs, lanes)
    hb = HB(st); hb.verbose = True; hb.scancost = 0; hb.hotcost = 0
    phi2 = construction(hb, prog, 204, 2)
    hb.encode(phi2)
    print('ok', st.ok, 'len', st.len, 'adds', st.adds, 'muls', st.muls, 'codes used', st.ci, len(codes),
          'hubs used', st.hi, len(hubs), 'lanes', st.li, 'scan', hb.scancost, 'hot', hb.hotcost, 'maxwin?')
