"""up-h checks (prints line ranges, counts and numbers only; no manuscript text).

Usage: python3 -I checks.py N5 V13 V14 V15 V16
  each argument is a TeX source (carriage returns are stripped on reading).
  N5 = diophantine_zq.tex; V13, V14, V16 = ~/upstream/manuscripts/quartic_v{13,14,16}.tex;
  V15 = ~/upstream/research/version15/snapshots/v15-222-004/manuscript/quartic_v15.tex.

1. Locates \\section{The six-contact height estimate} and the next \\section in each file.
2. Compares the constants block and theorem statement (from the line 'Set' to the end of
   the theorem statement) across versions.
3. Prints the changed line ranges of sec:height for V13 vs N5, V14 vs V15, V15 vs V16.
4. Counts citations of project supplements (keys ending in -project) in each sec:height.
5. Numerical checks: Faltings-height lower-bound constants, and upstream's stated
   log2-bounds for the five-contact constants of V16 (H_*, H_19, C_3).
"""
import sys, difflib, math, re

def load(p):
    return open(p, encoding='utf-8').read().replace('\r', '').split('\n')

names = ['N5', 'V13', 'V14', 'V15', 'V16']
src = dict(zip(names, map(load, sys.argv[1:6])))

sec = {}
for n, L in src.items():
    a = next(i for i, x in enumerate(L) if 'label{sec:height}' in x)
    b = next(i for i in range(a + 1, len(L)) if L[i].startswith('\\section'))
    sec[n] = (a + 1, b)  # 1-based first line, last line
    print(f"{n}: sec:height L{a+1}-{b} ({b-a} lines)")

def stmt(n):
    L = src[n]; a, b = sec[n]
    s = next(i for i in range(a - 1, b) if L[i].strip() == 'Set')
    e = next(i for i in range(s, b) if 'end{align*}' in L[i])
    t = next(i for i in range(a - 1, b) if 'label{thm:height}' in L[i])
    u = next(i for i in range(t, b) if 'end{theorem}' in L[i])
    return [x.strip() for x in L[s:e + 1] + L[t:u + 1]], (s + 1, e + 1, t + 1, u + 1)

base, loc = stmt('N5')
for n in names:
    s, l = stmt(n)
    print(f"{n}: constants L{l[0]}-{l[1]}, theorem L{l[2]}-{l[3]}; identical to N5: {s == base}")

def ranges(o, n, skip_title=False):
    A = [x.strip() for x in src[o][sec[o][0] - 1:sec[o][1]]]
    B = [x.strip() for x in src[n][sec[n][0] - 1:sec[n][1]]]
    sm = difflib.SequenceMatcher(None, A, B, autojunk=False)
    out = []
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag != 'equal':
            out.append(f"{o} L{sec[o][0]+i1}-{sec[o][0]+i2-1} -> {n} L{sec[n][0]+j1}-{sec[n][0]+j2-1} ({tag})")
    return out

for o, n in [('N5', 'V13'), ('V14', 'V15'), ('V15', 'V16')]:
    r = ranges(o, n)
    print(f"diff {o} -> {n}: {len(r)} hunks")
    for x in r:
        print("   ", x)

for n in names:
    a, b = sec[n]
    keys = re.findall(r'\{([A-Za-z0-9-]*-project)\}', '\n'.join(src[n][a - 1:b]))
    c = {}
    for k in keys:
        c[k] = c.get(k, 0) + 1
    print(f"{n}: project-supplement citations in sec:height: {sum(c.values())} {dict(sorted(c.items()))}")

print("log(pi*sqrt2) =", math.log(math.pi * math.sqrt(2)), "< 3/2:", math.log(math.pi * math.sqrt(2)) < 1.5)
print("log(2/sqrt(pi)) =", math.log(2 / math.sqrt(math.pi)), "< 1:", math.log(2 / math.sqrt(math.pi)) < 1)

# primorial B_* = prod_{p <= 76176} p, log2 via a sieve
N = 76176
sieve = bytearray([1]) * (N + 1); sieve[0] = sieve[1] = 0
for i in range(2, int(N ** 0.5) + 1):
    if sieve[i]:
        sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
lgB = sum(math.log2(p) for p in range(2, N + 1) if sieve[p])
print("log2 B_* =", lgB)
# V16 L7640-7650: H_* = 2(4608^165888 + 6^100) B_*^24 + 128, claim log2 H_* < 4783227
lgH = 1 + 165888 * math.log2(4608) + 24 * lgB
print("log2 H_* ~", lgH, "< 4783227:", lgH < 4783227)
# V16 L10005ff: A_19 = 2^109 210^1800, H_19 = 2 A_19 B_*^19 + 128, claim log2 H_19 < 2093966
lgH19 = 1 + 109 + 1800 * math.log2(210) + 19 * lgB
print("log2 H_19 ~", lgH19, "< 2093966:", lgH19 < 2093966)
# V16 L30758ff: D_0 = 4608 * 210^300, C_3 = 19 D_0 B_*^3 log B_*, claim C_3 < 2^330770
lgC3 = math.log2(19) + math.log2(4608) + 300 * math.log2(210) + 3 * lgB + math.log2(lgB * math.log(2))
print("log2 C_3 ~", lgC3, "< 330770:", lgC3 < 330770)
