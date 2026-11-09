"""Compare the Lean evaluation of Σ(𝒞_d) (out_lean_40.txt, from Eval.lean) with
(1) sel2_indep.py (exact descent written for this task),
(2) sel2.py of origin/wip/rv-slot-k-proof (path given as argv[1]),
(3) PARI/GP 2.17 ellrank: dim Sel_2 = 2 + r2 + s.
Usage: python compare.py /path/to/sel2_rvproof.py out_lean_40.txt"""
import sys, json, re, importlib.util, itertools
import cypari2
from sel2_indep import selmer as sel_indep
pari = cypari2.Pari()
pari.allocatemem(2 * 10**9)

spec = importlib.util.spec_from_file_location("sel2_rvproof", sys.argv[1])
rv = importlib.util.module_from_spec(spec); spec.loader.exec_module(rv)

txt = open(sys.argv[2]).read()
txt = txt.replace('some (', '(').replace('none', 'None').replace('true', 'True').replace('false', 'False')
lean = eval(txt.strip())
dset = dict((d, ps) for d, ps in json.load(open('dset.json')))


def pairs_indep(d, ps):
    gens, elems, dim = sel_indep(d, ps)
    g = len(gens)
    out = set()
    for vec in elems:
        a = b = 1
        for i in range(g):
            if vec[i]: a *= gens[i]
            if vec[g + i]: b *= gens[i]
        out.add((a, b))
    return dim, out


def pairs_rv(d, ps):
    dim, ker, gens = rv.selmer(d, sorted(ps))
    out = set()
    for coeffs in itertools.product((0, 1), repeat=len(ker)):
        m = 0
        for c, k in zip(coeffs, ker):
            if c: m ^= k
        out.add(rv.vec_to_pair(m, gens))
    return dim, out


rows = []
bad = 0
for d, rep, lpairs in lean:
    ps = dset[d]
    card, firsts = rep
    ldim = card.bit_length() - 1
    assert 2 ** ldim == card
    idim, ipairs = pairs_indep(d, ps)
    rdim, rpairs = pairs_rv(d, ps)
    r1, r2, s, L = pari.ellrank(pari.ellinit([-d * d, 0]))
    pdim = 2 + int(r2) + int(s)
    root = int(pari.ellrootno(pari.ellinit([-d * d, 0])))
    ok_set = (set(lpairs) == ipairs == rpairs)
    ok_dim = (ldim == idim == rdim == pdim)
    ifirst = {a for a, b in ipairs}
    ok_first = all(flag == (a in ifirst) for a, flag in firsts)
    hyp = [a for a, flag in firsts if flag] if card == 8 else []
    if not (ok_set and ok_dim and ok_first):
        bad += 1
        print("MISMATCH", d, ps, ldim, idim, rdim, pdim, sorted(set(lpairs) ^ ipairs))
    rows.append(dict(d=d, primes=ps, cls=[p % 8 for p in ps], lean_card=card, lean_dim=ldim,
                     indep_dim=idim, rv_dim=rdim, pari_dim=pdim, pari_rank=[int(r1), int(r2)],
                     sha_s=int(s), rootno=root, same_group=ok_set, firsts_ok=ok_first,
                     a7_lean=[a for a, f in firsts if f], cr3_hyp=hyp))
json.dump(rows, open('cmp40.json', 'w'), indent=0)
print("d | primes (mod 8) | Lean #sols | dim Lean/indep/rv/PARI | PARI r1..r2 s | same Sel2 | firsts agree | a (|a|=7) in pi1 (Lean)")
for r in rows:
    print(r['d'], '|', ' '.join('%d(%d)' % (p, p % 8) for p in r['primes']), '|', r['lean_card'], '|',
          '%d/%d/%d/%d' % (r['lean_dim'], r['indep_dim'], r['rv_dim'], r['pari_dim']), '|',
          r['pari_rank'], r['sha_s'], '|', r['same_group'], '|', r['firsts_ok'], '|', r['a7_lean'])
print("mismatches:", bad, "of", len(rows))
