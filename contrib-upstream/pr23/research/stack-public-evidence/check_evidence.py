#!/usr/bin/env python3
"""Standalone checker for research/stack-public-evidence.

Python 3.9+ standard library only.  It imports and runs nothing from the
research packets or their generators.  For each of the 12 tables it:

  1. checks the stored and decompressed SHA-256 and byte counts of every file;
  2. parses the decimal table and checks it against the published summary;
  3. parses the plain-text rows file and checks it equals balanced/integer-ir.json;
  4. expands the sum of squares of the integer rows exactly and compares it with
     every coefficient of the decimal table;
  5. replays the diagonal map: pre-diagonal row with old x = 2^a 3^b new x, at
     the fixed S, equals (stated nonzero rational divisor) * balanced row;
  6. where present, checks that compiled-ir.json at the fixed S, minus the
     coordinates the coordinate map omits as unused, is the next IR, and
  7. replays the four factored-pole transports as algebraic identities
     (no positivity or zero-branch argument is checked).
The link raw-translated-ir.json -> compiled-ir.json (gate identities and the
compiler's reduction certificate) is NOT replayed here; see the included
gate-check reports.

It also checks the exact-rewrite certificates in rewrites/ (PR #13 cube reuse,
PR #18 row changes A and tri), that PR #16's raw IRs equal PR #13's except for
the fixed parameter, the arithmetic behind ERRATA.md, MANIFEST.json,
and, with --verify-bindings REPO, that every recorded published hash really
occurs in the named file at the named public commit (via `git show`).

Usage:  python3 -B check_evidence.py [--packet DIR] [--only LABEL ...]
                                     [--verify-bindings REPO] [--skip-tables] [--no-controls]
Thirteen negative controls (mutations made in memory) must each be refused.
Exit status 0 means every check passed.
"""
import argparse, gzip, hashlib, json, math, re, subprocess, sys, time
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)


class CheckFailure(Exception):
    pass


def need(cond, msg):
    if not cond:
        raise CheckFailure(msg)


def sha(b):
    return hashlib.sha256(b).hexdigest()


# --------------------------------------------------------------------------- files

class Packet:
    def __init__(self, root, overrides=None):
        self.root = root
        self.overrides = overrides or {}
        self.index = json.loads((root / 'INDEX.json').read_text())
        self.records = dict(self.index['files'])
        self.records.update(self.index.get('derived', {}))
        self._cache = {}

    def recorded_sha(self, ppath):
        return self.records[ppath]['sha256']

    def raw(self, ppath):
        if ppath in self.overrides:  # self-test only: mutated content, hash checks bypassed
            return self.overrides[ppath]
        if ppath not in self._cache:
            rec = self.records[ppath]
            stored = (self.root / ppath).read_bytes()
            need(len(stored) == rec['storedBytes'] and sha(stored) == rec['storedSha256'],
                 f'stored bytes/hash mismatch: {ppath}')
            data = gzip.decompress(stored) if rec['compressed'] else stored
            need(len(data) == rec['bytes'] and sha(data) == rec['sha256'],
                 f'decompressed bytes/hash mismatch: {ppath}')
            self._cache[ppath] = data
        return self._cache[ppath]

    def json(self, ppath):
        return json.loads(self.raw(ppath))


def check_manifest(root):
    man = json.loads((root / 'MANIFEST.json').read_text())
    listed = {f['path']: f for f in man['files']}
    present = {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()} - {'MANIFEST.json'}
    present = {p for p in present if '__pycache__' not in p}
    # CHECK_OUTPUT.txt records a run of this checker, so it may be absent from the manifest that run checked.
    need(set(listed) in (present, present - {'CHECK_OUTPUT.txt'}),
         f'MANIFEST.json file list differs: {sorted(set(listed) ^ present)[:5]}')
    for p, f in listed.items():
        b = (root / p).read_bytes()
        need(len(b) == f['bytes'] and sha(b) == f['sha256'], f'MANIFEST mismatch: {p}')
    return len(listed), sum(f['bytes'] for f in listed.values())


def check_bindings(packet, repo):
    """Every recorded published hash must occur in the named file at the named commit."""
    cache = {}
    def show(spec):
        if spec not in cache:
            rev, path = spec.split(':', 1)
            r = subprocess.run(['git', '-C', str(repo), 'show', f'{rev}:{path}'], capture_output=True)
            need(r.returncode == 0, f'cannot read {spec} from {repo}')
            cache[spec] = r.stdout.decode('utf8', 'replace')
        return cache[spec]
    checked = 0
    for p, rec in packet.index['files'].items():
        for b in rec.get('pathBinding', []):
            spec = b['source'].split(' ')[0]
            need(b['sha256'] == rec['sha256'] and rec['sha256'] in show(spec), f'binding not found: {p} in {spec}')
            checked += 1
        for spec in rec.get('publishedIn', []):
            need(rec['sha256'] in show(spec), f'binding not found: {p} in {spec}')
            checked += 1
    return checked


def binding_status(packet):
    """Direct publication, or statement inside a bound packet file whose content contains the hash."""
    files = packet.index['files']
    status = {}
    for p, r in files.items():
        if r.get('pathBinding') or r.get('publishedIn'):
            status[p] = 'published'
    changed = True
    while changed:
        changed = False
        for p, r in files.items():
            if p in status:
                continue
            for carrier in r.get('statedIn', []):
                if carrier in status and r['sha256'].encode() in packet.raw(carrier):
                    status[p] = 'stated in ' + carrier
                    changed = True
                    break
    for p, r in files.items():
        need((p in status) == bool(r.get('bound')), f'recorded binding flag disagrees: {p}')
    return status


# --------------------------------------------------------------------------- tables and rows

MONO = re.compile(r'x(0|[1-9][0-9]*)(?:\^([2-4]))?')
INT = re.compile(r'-?(?:0|[1-9][0-9]*)')


def parse_monomial(text, n, maxdeg):
    if text == '1':
        return ()
    ids, last = [], -1
    for factor in text.split('*'):
        m = MONO.fullmatch(factor)
        need(m is not None, f'bad monomial factor {factor!r}')
        i, e = int(m[1]), int(m[2] or 1)
        need(last < i < n, f'noncanonical or out-of-range monomial {text!r}')
        ids += [i] * e
        last = i
    need(len(ids) <= maxdeg, f'degree too high: {text!r}')
    return tuple(ids)


def parse_table(data, n, monomials):
    lines = data.decode('ascii').split('\n')
    need(lines[-1] == '', 'table does not end with a newline')
    lines = lines[:-1]
    need(lines[0] == '# Fully explicit integer quartic after an invertible diagonal change.', 'table header line 1')
    need(lines[1] == f'# Variables: {n}; input: x0; degree: 4; monomials: {monomials}.', 'table header line 2')
    need(lines[2] == '# Format: integer coefficient, TAB, monomial; sum all data rows.', 'table header line 3')
    out = {}
    for line in lines[3:]:
        c, m = line.split('\t')
        need(INT.fullmatch(c) is not None and c != '0', f'bad coefficient {c[:20]}')
        mono = parse_monomial(m, n, 4)
        need(mono not in out, f'repeated monomial {m}')
        out[mono] = int(c)
    return out


def parse_rows_text(data):
    lines = data.decode('ascii').split('\n')
    need(lines[-1] == '', 'rows file does not end with a newline')
    vmap, rows, cur = [], [], None
    n = None
    for line in lines[:-1]:
        if line.startswith('#'):
            continue
        f = line.split('\t')
        if f[0] == 'V':
            need(int(f[1]) == len(vmap), 'V lines out of order')
            vmap.append((int(f[2]), f[3]))
        elif f[0] == 'R':
            n = len(vmap)
            need(int(f[1]) == len(rows), 'R lines out of order')
            cur = {'id': int(f[2]), 'name': f[3], 'terms': {}}
            rows.append(cur)
        else:
            need(cur is not None and len(f) == 2 and INT.fullmatch(f[0]) and f[0] != '0', f'bad term line {line[:40]}')
            m = parse_monomial(f[1], n, 2)
            need(m not in cur['terms'], 'repeated monomial in a row')
            cur['terms'][m] = int(f[0])
    return vmap, rows


def sum_of_squares(rows):
    out = defaultdict(int)
    for r in rows:
        items = sorted(r.items())
        for i, (m, a) in enumerate(items):
            out[tuple(sorted(m + m))] += a * a
            for n, b in items[i + 1:]:
                out[tuple(sorted(m + n))] += 2 * a * b
    return {m: a for m, a in out.items() if a}


def fixed_s(ir_meta):
    v = ir_meta['value']
    m = re.fullmatch(r'3\^([0-9]+)', v)
    need(m is not None and ir_meta['name'] == 'S' and ir_meta['coordinate'] is False, f'unexpected S {v}')
    return int(m[1]), 3 ** int(m[1])


def numeric_rows(ir, S):
    """Rows over Q with S specialized; keys are sorted coordinate-id tuples."""
    out = {}
    for r in ir['residuals']:
        p = defaultdict(F)
        for t in r['terms']:
            need(isinstance(t['sPower'], int) and t['sPower'] >= 0, 'bad sPower')
            p[tuple(sorted(t['monomial']))] += F(t['coefficient']) * S ** t['sPower']
        need(r['name'] not in out, f'duplicate row name {r["name"]}')
        out[r['name']] = {m: a for m, a in p.items() if a}
    return out


def check_table(packet, t, log):
    R, s = t['roles'], t['publishedSummary']
    n = t['variables']
    need(s['coordinates'] == n, 'variables differ from published summary')
    tdata = packet.raw(R['table'])
    need(packet.recorded_sha(R['table']) == s['tableSha256'] and packet.records[R['table']]['bytes'] == s['tableBytes'],
         'table hash/bytes differ from published summary')
    table = parse_table(tdata, n, s['monomials'])
    need(len(table) == s['monomials'], 'monomial count')
    need({i for m in table for i in m} == set(range(n)), 'not every variable occurs')
    need(max(map(len, table)) == 4, 'degree is not 4')
    need(table.get((0, 0, 0, 0)) == 1, 'x0^4 coefficient is not 1')
    need(math.gcd(*table.values()) == 1, 'content is not 1')
    mx = max(abs(a) for a in table.values())
    need(len(str(mx)) == s['maximumCoefficientDigits'] and mx.bit_length() == s['maximumCoefficientBits'],
         'maximum coefficient digits/bits differ from published summary')
    if s.get('cExponent') is not None:
        need(mx == 28902 * 3 ** (4 * s['cExponent']), 'maximum is not 28902*c^4 with c=3^cExponent')
        mtext = f'28902*3^{4 * s["cExponent"]}'
    else:
        mtext = 'no closed form claimed'

    # Rows: text file vs JSON.
    ir = packet.json(R['rowsIr'])
    need(ir['format'] == 'diagonally-scaled-integer-quadratic-ir-v2' and ir['inputCoordinate'] == 0, 'rows IR format')
    coords = sorted(ir['coordinates'], key=lambda c: c['id'])
    need(ir['coordinates'] == coords and len(coords) == n, 'rows IR coordinates')
    compact = {c['id']: i for i, c in enumerate(coords)}
    need(coords[0]['id'] == 0 and coords[0]['name'] == 'input', 'input is not coordinate 0')
    json_rows = []
    for r in ir['residuals']:
        p = {}
        for term in r['terms']:
            need(term['sPower'] == 0, 'parameter left in integer rows')
            m = tuple(sorted(compact[i] for i in term['monomial']))
            need(len(m) <= 2 and m not in p, 'row term')
            q = F(term['coefficient'])
            need(q.denominator == 1 and q != 0, 'noninteger or zero row coefficient')
            p[m] = q.numerator
        need(p and math.gcd(*p.values()) == 1, f'row not primitive: {r["name"]}')
        json_rows.append((r['id'], r['name'], p))
    need(len(json_rows) == s['residuals'], 'residual count differs from published summary')
    vmap, text_rows = parse_rows_text(packet.raw(R['rowsText']))
    need(vmap == [(c['id'], c['name']) for c in coords], 'rows text variable map differs from rows IR')
    need([(r['id'], r['name'], r['terms']) for r in text_rows] == json_rows, 'rows text differs from rows IR')

    # Sum of squares.
    sos = sum_of_squares([p for _, _, p in json_rows])
    need(sos == table, 'sum of squares of the rows differs from the decimal table')
    log(f'  table: {n} variables, {len(table)} monomials, max {len(str(mx))} digits/{mx.bit_length()} bits ({mtext}); '
        f'SOS of {len(json_rows)} rows equals table exactly')

    # Diagonal map.
    cert = packet.json(R['diagonalCertificate'])
    pre_path = R['preDiagonalIr']
    pre = packet.json(pre_path)
    need(cert['format'] == 'diagonal-scaling-certificate-v2', 'diagonal certificate format')
    need(cert['sourceIrSha256'] == packet.recorded_sha(pre_path) and cert['newIrSha256'] == packet.recorded_sha(R['rowsIr']),
         'diagonal certificate does not name these IR files')
    need(cert['direction'] == 'old_x_i = 2^twoPower[i] * 3^threePower[i] * new_x_i', 'diagonal direction')
    E, S = fixed_s(pre['fixedParameter'])
    need(E == s['anchorExponent'] == cert['anchorExponent'] and ir['sourceFixedParameter'] == pre['fixedParameter'],
         'anchor exponent')
    need(pre['coordinates'] == ir['coordinates'], 'pre-diagonal and balanced coordinates differ')
    ids = [c['id'] for c in coords]
    a3 = {i: cert['threePowers'][str(i)] for i in ids}
    a2 = {i: cert['twoPowers'][str(i)] for i in ids}
    need(len(cert['threePowers']) == len(cert['twoPowers']) == n, 'diagonal power tables')
    need(a3[0] == a2[0] == 0, 'input is scaled')
    need(sum(1 for i in ids if a3[i] or a2[i]) == s['scaledCoordinates']
         and sum(1 for i in ids if a3[i]) == s['ternaryScaledCoordinates']
         and sum(1 for i in ids if a2[i]) == s['dyadicScaledCoordinates'], 'scaled coordinate counts')
    factor = {i: F(3) ** a3[i] * F(2) ** a2[i] for i in ids}
    need([r['id'] for r in pre['residuals']] == [r[0] for r in json_rows] == [r['id'] for r in cert['rows']]
         and [r['name'] for r in pre['residuals']] == [r[1] for r in json_rows], 'row identities differ')
    pre_rows = numeric_rows(pre, S)
    fractional = 0
    for (rid, name, new), rc in zip(json_rows, cert['rows']):
        d = F(int(rc['divisorNumerator']), int(rc['divisorDenominator']))
        need(d != 0 and int(rc['divisorDenominator']) > 0, 'zero divisor')
        fractional += d.denominator != 1
        sub = defaultdict(F)
        for m, a in pre_rows[name].items():
            for i in m:
                a *= factor[i]
            sub[tuple(sorted(compact[i] for i in m))] += a
        sub = {m: a for m, a in sub.items() if a}
        need(sub == {m: d * a for m, a in new.items()}, f'diagonal identity fails at row {name}')
    log(f'  diagonal: {len(json_rows)} rows = divisor * substituted pre-diagonal rows at S=3^{E}; '
        f'{sum(1 for i in ids if a3[i] or a2[i])} scaled coordinates, input fixed, {fractional} non-integer divisors')

    if 'compiledIr' in R:
        check_compiled_link(packet, R, log)
    if 'transportCertificate' in R:
        check_transport(packet, R, log)


def check_compiled_link(packet, R, log):
    """compiled-ir.json at the fixed S, minus the certified-unused coordinates, is the next IR."""
    nxt_path = R.get('preTransportIr', R['preDiagonalIr'])
    comp, nxt, cmap = packet.json(R['compiledIr']), packet.json(nxt_path), packet.json(R['coordinateMap'])
    need(comp['fixedParameter'] == nxt['fixedParameter'], 'fixed parameter differs')
    _, S = fixed_s(comp['fixedParameter'])
    a, b = numeric_rows(comp, S), numeric_rows(nxt, S)
    need([r['name'] for r in comp['residuals']] == [r['name'] for r in nxt['residuals']] and a == b,
         'compiled rows at fixed S differ from the next IR')
    omitted = set(cmap.get('omittedFreeCoordinates', []))
    need(not any(omitted & set(m) for row in a.values() for m in row), 'an omitted coordinate occurs in a row')
    cc = {c['id']: c for c in comp['coordinates']}
    nc = {c['id']: c for c in nxt['coordinates']}
    need(set(nc) == set(cc) - omitted and all(nc[i] == cc[i] for i in nc), 'coordinate lists differ beyond the omission')
    mp = cmap['mapping']
    need([m['sourceId'] for m in mp] == sorted(nc) and [m['compactId'] for m in mp] == list(range(len(mp)))
         and all(m['name'] == nc[m['sourceId']]['name'] for m in mp), 'coordinate map differs from the IR')
    log(f'  compiled: {len(a)} compiled rows at S equal the next IR\'s rows; {len(omitted)} unused coordinates '
        f'omitted; coordinate map ({len(mp)} entries) consistent')


# --------------------------------------------------------------------------- numeric polynomials (coordinate ids)

def padd(*ps):
    out = defaultdict(F)
    for p in ps:
        for m, a in p.items():
            out[m] += a
    return {m: a for m, a in out.items() if a}


def pscale(p, a):
    a = F(a)
    return {m: v * a for m, v in p.items() if v * a}


def pmul(p, q):
    out = defaultdict(F)
    for m, a in p.items():
        for k, b in q.items():
            out[tuple(sorted(m + k))] += a * b
    return {m: a for m, a in out.items() if a}


def psub(p, mapping, var):
    out = {}
    for m, a in p.items():
        term = {(): F(a)}
        for x in m:
            term = pmul(term, mapping.get(x, var(x)))
        out = padd(out, term)
    return out


def proportional(a, b):
    """Return the nonzero rational c with a == c*b, or None."""
    if not a or not b or set(a) != set(b):
        return None
    m = next(iter(a))
    c = a[m] / b[m]
    return c if c and all(a[k] == c * b[k] for k in a) else None


def check_transport(packet, R, log):
    cert = packet.json(R['transportCertificate'])
    src_path, dst_path = R['preTransportIr'], R['preDiagonalIr']
    need(cert['sourceSha256'] == packet.recorded_sha(src_path) and cert['candidateSha256'] == packet.recorded_sha(dst_path),
         'transport certificate does not name these IR files')
    src, dst = packet.json(src_path), packet.json(dst_path)
    need(src['fixedParameter'] == dst['fixedParameter'], 'fixed parameter changed')
    _, S = fixed_s(src['fixedParameter'])
    old, new = numeric_rows(src, S), numeric_rows(dst, S)
    V = lambda i: {(i,): F(1)}
    def terms(ts):
        p = defaultdict(F)
        for t in ts:
            p[tuple(sorted(t['monomial']))] += F(t['coefficient']) * S ** t['sPower']
        return {m: a for m, a in p.items() if a}
    need([b['prefix'] for b in cert['blocks']] == ['detector0', 'detector1', 'detector2', 'scalar'], 'transport blocks')
    touched, removed, renamed = set(), set(), set()
    for b in cert['blocks']:
        p = b['prefix']
        s, v, Q, Q2, s2 = b['s'], b['newV'], b['newQ'], b['newQSquare'], b['removedSquare']
        L = {int(k): terms(x) for k, x in b['reverseLift'].items()}
        need(set(L) == {v, Q, Q2, s2}, 'reverse lift slots')
        ss = pmul(V(s), V(s))
        need(L[Q] == pmul(V(s), V(Q)) and L[Q2] == pmul(ss, V(Q2)) and L[s2] == ss, 'reverse lift q,q2,s2')
        H, bcoef = terms(b['semanticOldH']), terms(b['positiveConicInput'])
        need(psub(H, L, V) == pmul(V(s), V(v)), 'reverse lift does not give H = s*v')
        names = {p + x for x in ['.Bh.definition', '.q2.definition', '.s2.definition', '.secondConic']}
        need(set(b['privateConsumerRows']) == names, 'private consumer list')
        consumers = {nm for nm, row in old.items() if any({v, Q, Q2, s2} & set(m) for m in row)}
        need(consumers == names, f'{p}: private slots occur outside the four rows')
        # Old semantic forms (the zero-branch algebra rests on these).
        need(proportional(old[p + '.s2.definition'], padd(V(s2), pscale(ss, -1))) is not None, 'old s2 row form')
        need(proportional(old[p + '.q2.definition'], padd(V(Q2), pscale(pmul(V(Q), V(Q)), -1))) is not None, 'old q2 row form')
        old_conic = padd(pscale(pmul(bcoef, V(Q2)), 17), pscale(pmul(H, H), 3),
                         pscale(pmul(V(s2), H), -2), pscale(pmul(V(s2), V(s2)), -1))
        need(proportional(old[p + '.secondConic'], old_conic) is not None,
             f'{p}: old conic is not 17 b q2 + 3 H^2 - 2 s2 H - s2^2')
        new_conic = padd(pscale(pmul(bcoef, V(Q2)), 17), pscale(pmul(V(v), V(v)), 3),
                         pscale(pmul(V(s), V(v)), -2), pscale(ss, -1))
        need(proportional(new[p + '.secondConic'], new_conic) is not None,
             f'{p}: new conic is not 17 b Q2 + 3 v^2 - 2 s v - s^2')
        # Lift identities.
        need(psub(old[p + '.s2.definition'], L, V) == {}, 's2 row does not vanish under the lift')
        need(p + '.s2.definition' not in new, 's2 row not removed')
        ratios = {}
        for end, mult in [('.Bh.definition', {(): F(1)}), ('.q2.definition', ss), ('.secondConic', ss)]:
            nm = p + end
            c = proportional(psub(old[nm], L, V), pmul(mult, new[nm]))
            need(c is not None, f'lift identity fails: {nm}')
            need(new[nm] == terms(b['normalizedNewRows'][nm]), f'certificate row differs from IR: {nm}')
            ratios[nm] = c
        touched |= names
        removed.add(s2)
        renamed.add(v)
        b['_ratios'] = ratios
    need(set(old) - set(new) == {p + '.s2.definition' for p in ['detector0', 'detector1', 'detector2', 'scalar']}
         and set(new) <= set(old), 'transport row set')
    unchanged = [nm for nm in new if nm not in touched]
    need(all(new[nm] == old[nm] for nm in unchanged), 'an outside row changed under transport')
    oc = {c['id']: c for c in src['coordinates']}
    nc = {c['id']: c for c in dst['coordinates']}
    need(set(nc) == set(oc) - removed, 'transport coordinate set')
    for i, c in nc.items():
        o = dict(oc[i])
        if i in renamed:
            o['name'] = c['name']
        need(c == o, f'coordinate {i} changed')
    need(nc[0] == oc[0] and oc[0]['name'] == 'input', 'input changed')
    log(f'  transport: 4 blocks; s2 rows vanish, Bh/q2/conic rows lift to nonzero multiples (q2, conic times s^2); '
        f'{len(unchanged)} outside rows identical; {len(oc)}->{len(nc)} coordinates')


# --------------------------------------------------------------------------- named polynomials (formal S)

def named_decoder(ir):
    names = {c['id']: c['name'] for c in ir['coordinates']}
    need(len(set(names.values())) == len(names), 'duplicate coordinate names')
    def poly(ts):
        out = defaultdict(F)
        for t in ts:
            out[tuple(sorted([names[i] for i in t['monomial']] + ['$S'] * t['sPower']))] += F(t['coefficient'])
        return {m: a for m, a in out.items() if a}
    rows = {}
    for r in ir['residuals']:
        need(r['name'] not in rows, 'duplicate row')
        rows[r['name']] = poly(r['terms'])
    return names, rows, poly


def nvar(x):
    return {(x,): F(1)}


def dec(enc):
    out = defaultdict(F)
    for c, m in enc:
        out[tuple(sorted(m))] += F(c)
    return {m: a for m, a in out.items() if a}


def check_ideal_certificate(packet, path, log):
    cert = packet.json(path)
    need(cert['format'] == 'stack-public-evidence-ideal-certificate-v1', 'certificate format')
    systems = {}
    for key in ('old', 'new'):
        ref = cert[key]
        need(packet.records[ref['packetPath']]['sha256'] == ref['sha256'], 'certificate names another file')
        ir = packet.json(ref['packetPath'])
        need(ir['fixedParameter'] == {'name': 'S', 'value': '3^2010', 'coordinate': False}, 'fixed parameter')
        names, rows, poly = named_decoder(ir)
        systems[key] = (ir, set(names.values()), rows, poly)
    (oir, ocoords, O, op), (nir, ncoords, N, np_) = systems['old'], systems['new']
    d = cert['expectedDelta']
    changed = sorted(nm for nm in set(O) & set(N) if O[nm] != N[nm])
    need(sorted(set(O) - set(N)) == d['deletedRows'] and sorted(set(N) - set(O)) == d['addedRows']
         and changed == d['changedRows'], 'row delta differs from the certificate')
    need(sorted(ocoords - ncoords) == d['removedCoordinates'] and sorted(ncoords - ocoords) == d['addedCoordinates'],
         'coordinate delta differs')
    # Guards identical after naming.
    def guards(ir, poly):
        return {g['name']: (poly(g['expression']), poly(g['inverse'])) for g in ir['guards']}
    need(guards(oir, op) == guards(nir, np_), 'inverse guards differ')
    # Displayed constants: r and L are the actual decodings, and mu*(1+k*L) = 42 r.
    r, L = dec(cert['r']), dec(cert['L'])
    ri, W, T0 = 'scalar.rInverse', 'scalar.W2.quadratic', 'scalar.preparationT.quadratic'
    need(O['scalar.rInverse.definition'] == padd(pmul(r, nvar(ri)), {(): F(-1)}), 'r is not the actual decoding')
    need(N['scalar.rInverse.definition'] == O['scalar.rInverse.definition'], 'r*ri row changed')
    need(O['scalar.preparationT.definition'] == padd(nvar(T0), pscale(pmul(L, nvar(W)), -1)), 'L is not the actual decoding')
    mu, k = F(cert['displayedConstants']['mu']), F(cert['displayedConstants']['k'])
    need(pscale(padd({(): F(1)}, pscale(L, k)), mu) == pscale(r, 42), 'mu*(1+k*L) != 42*r')
    for direction in cert['directions']:
        T = {'old': O, 'new': N}[direction['targetSystem']]
        B = {'old': O, 'new': N}[direction['baseSystem']]
        tco = {'old': ocoords, 'new': ncoords}[direction['targetSystem']]
        bco = {'old': ocoords, 'new': ncoords}[direction['baseSystem']] | {'$S'}
        M = {x: dec(e) for x, e in direction['map'].items()}
        need(set(M) <= tco and 'input' not in M, 'map keys')
        need(all(set(m) <= bco for p in M.values() for m in p), 'map uses unknown base coordinates')
        need(all(x in bco for x in tco - set(M)), 'an unmapped target coordinate is missing from the base system')
        listed = {i['row']: i for i in direction['identities']}
        for nm, row in T.items():
            img = psub(row, M, nvar)
            if nm in listed:
                comb = {}
                for bname, mult in listed[nm]['combination']:
                    comb = padd(comb, pmul(dec(mult), B[bname]))
                need(img == comb, f'{direction["direction"]}: identity fails for {nm}')
            else:
                need(nm in B and img == B[nm], f'{direction["direction"]}: unlisted row {nm} not identical')
    log(f'  {path}: A row operations, tri witness maps and Bh_new = {mu}*Bh_old verified as ideal memberships in both '
        f'directions over all {len(N)} new and {len(O)} old raw rows (formal S); guards identical')


def check_cube_spec(packet, path, log):
    spec = packet.json(path)
    need(spec['format'] == 'stack-public-evidence-cube-reuse-v1', 'cube spec format')
    sys_ = {}
    for key in ('before', 'after'):
        ref = spec[key]
        need(packet.records[ref['packetPath']]['sha256'] == ref['sha256'], 'spec names another file')
        ir = packet.json(ref['packetPath'])
        names, rows, poly = named_decoder(ir)
        vals = {k: poly(v['terms']) for k, v in ir['values'].items()}
        sys_[key] = (ir, names, rows, poly, vals)
    (bir, bn, B, bp, bv), (air, an, A, ap, av) = sys_['before'], sys_['after']
    need(bir['fixedParameter'] == air['fixedParameter'], 'fixed parameter changed')
    d = spec['expectedDelta']
    changed = sorted(nm for nm in set(A) & set(B) if A[nm] != B[nm])
    need(sorted(set(B) - set(A)) == d['deletedRows'] and sorted(set(A) - set(B)) == d['addedRows']
         and changed == d['changedRows'], 'row delta differs')
    def guards(ir, poly):
        return {g['name']: (poly(g['expression']), poly(g['inverse'])) for g in ir['guards']}
    need(guards(bir, bp) == guards(air, ap), 'inverse guards differ')
    common = set(bv) & set(av)
    need(all(bv[k] == av[k] for k in common), 'a common named value changed')
    # Contact polynomial coefficients.
    cs = [F(1)]
    for root in map(F, spec['contactRoots']):
        out = [F(0)] * (len(cs) + 1)
        for j, c in enumerate(cs):
            out[j] -= root * c
            out[j + 1] += c
        cs = out
    consts = {'c2': cs[2], 'c3': cs[3], 'c4': cs[4]}
    def expr(entries, vals):
        out = {}
        for c, factors in entries:
            term = {(): F(consts[c]) if isinstance(c, str) else F(c)}
            for f in factors:
                term = pmul(term, vals[f])
            out = padd(out, term)
        return out
    for rows, vals, items in [(A, av, spec['afterIdentities']), (B, bv, spec['beforeIdentities'])]:
        for it in items:
            target = padd(expr(it['lhs'], vals), pscale(expr(it['rhs'], vals), -1))
            need(proportional(rows[it['row']], target) is not None, f'row identity fails: {it["row"]}')
    # Affine cubic alias.
    X = {('#x',): F(1)}
    for ca in spec['cubicAliases']:
        mapping = {}
        def solve(value, target):
            unknown = [(m, c) for m, c in value.items() if m and m[0] not in mapping]
            need(len(unknown) == 1 and len(unknown[0][0]) == 1, 'alias is not solvable for one coordinate')
            (mono, c), = unknown
            known = psub({m: a for m, a in value.items() if m != mono}, mapping, nvar)
            mapping[mono[0]] = pscale(padd(target, pscale(known, -1)), 1 / c)
        xx = pmul(X, X)
        solve(av[ca['t']], X)
        solve(av[ca['square']], xx)
        solve(av[ca['middle']], padd(pmul(xx, X), pscale(xx, cs[4]), pscale(X, cs[3]), {(): cs[2]}))
        cube = av[ca['cube']]
        need(all(len(m) <= 1 for m in cube), 'deltaCubed is not affine')
        need(ca['cube'] + '.quadratic' not in set(an.values()), 'deltaCubed owns a coordinate')
        delta = padd(pscale(X, ca['slope']), {(): F(-1)})
        need(psub(cube, mapping, nvar) == pmul(pmul(delta, delta), delta), 'deltaCubed is not (98t-1)^3')
    unchanged = len(set(A) & set(B)) - len(changed)
    log(f'  {path}: 12 rows deleted, 9 added, 3 changed, {unchanged} identical; every added/changed/deleted row is a '
        f'nonzero multiple of its displayed definition; 3 affine cubes equal (98t-1)^3; guards and '
        f'{len(common)} common named values identical')


def check_same_raw(packet, la, lb, log):
    """PR #16 changes only the fixed anchor: its raw IR equals #13's apart from fixedParameter."""
    tables = {t['label']: t for t in packet.index['tables']}
    a = packet.json(tables[la]['roles']['rawIr'])
    b = packet.json(tables[lb]['roles']['rawIr'])
    diff = sorted(k for k in set(a) | set(b) if a.get(k) != b.get(k))
    need(diff == ['fixedParameter'], f'raw IRs differ in {diff}')
    log(f'  {lb} raw IR equals {la} raw IR in every field except fixedParameter '
        f'({a["fixedParameter"]["value"]} -> {b["fixedParameter"]["value"]})')


def check_errata(log):
    a = [F(1), F(-2, 5)]
    for j in range(2, 14):
        a.append(a[-1] * F(4 * j - 5, 4 * j + 1))
    need(a[13].denominator == 5 ** 2 * 7 * 17 * 29 * 37 * 41 * 53, 'a13 denominator (j>=2 reading)')
    b = [F(1)]
    for j in range(1, 14):
        b.append(b[-1] * F(4 * j - 5, 4 * j + 1))
    need(b[1] == F(-1, 5) and b[13] == a[13] / 2, 'alternative reading')
    log('  errata: with a0=1, a1=-2/5 and a_j/a_(j-1)=(4j-5)/(4j+1) for j>=2, den(a13)=5^2*7*17*29*37*41*53; '
        'applying the ratio at j=1 gives a1=-1/5 and halves a13')


# --------------------------------------------------------------------------- negative controls

def negative_controls(root, log):
    """Each mutation, made in memory, must be refused by the intended check."""
    base = Packet(root)
    tables = {t['label']: t for t in base.index['tables']}
    def J(path):
        return json.loads(base.raw(path))
    def dump(obj):
        return json.dumps(obj).encode()
    def table_bump(path):
        lines = base.raw(path).decode().split('\n')
        i = next(i for i, l in enumerate(lines) if not l.startswith('#') and l.split('\t')[1] == 'x0*x1') \
            if any(l.endswith('\tx0*x1') for l in lines) else 10
        c, m = lines[i].split('\t')
        lines[i] = f'{int(c) + 1}\t{m}'
        return '\n'.join(lines).encode()
    def rows_text_bump(path):
        lines = base.raw(path).decode().split('\n')
        i = next(i for i, l in enumerate(lines) if l and l[0] in '-0123456789')
        c, m = lines[i].split('\t')
        lines[i] = f'{int(c) + 1}\t{m}'
        return '\n'.join(lines).encode()
    def both_rows_bump(t):
        R = t['roles']
        ir = J(R['rowsIr'])
        term = ir['residuals'][5]['terms'][0]
        term['coefficient'] = str(-int(term['coefficient']))
        coords = sorted(c['id'] for c in ir['coordinates'])
        compact = {c: i for i, c in enumerate(coords)}
        target = tuple(sorted(compact[i] for i in term['monomial']))
        lines = base.raw(R['rowsText']).decode().split('\n')
        r = [i for i, l in enumerate(lines) if l.startswith('R\t')][5]
        j = r + 1
        while True:
            c, m = lines[j].split('\t')
            if m == '1' and target == () or m != '1' and tuple(sum(([int(f.split('^')[0][1:])] * int(f.split('^')[1] if '^' in f else 1) for f in m.split('*')), [])) == target:
                lines[j] = f'{-int(c)}\t{m}'
                break
            j += 1
        return {R['rowsIr']: dump(ir), R['rowsText']: '\n'.join(lines).encode()}
    def cert_edit(path, fn):
        obj = J(path)
        fn(obj)
        return {path: dump(obj)}
    def divisor(o):
        r = next(r for r in o['rows'] if r['divisorNumerator'] != '1')
        r['divisorNumerator'] = str(int(r['divisorNumerator']) * 3)
    def power(o):
        k = next(k for k, v in o['threePowers'].items() if v)
        o['threePowers'][k] += 1
    def lift(o):
        b = o['blocks'][3]
        k = str(b['newV'])
        b['reverseLift'][k][0]['coefficient'] = str(F(b['reverseLift'][k][0]['coefficient']) * 2)
    def conic_input(o):
        b = o['blocks'][0]
        b['positiveConicInput'][0]['coefficient'] = str(F(b['positiveConicInput'][0]['coefficient']) + 1)
    def outside_consumer(t):
        path = t['roles']['preTransportIr']
        o = J(path)
        cert = J(t['roles']['transportCertificate'])
        slot = cert['blocks'][0]['removedSquare']
        o['residuals'][0]['terms'].append({'sPower': 0, 'monomial': [slot], 'coefficient': '1'})
        return {path: dump(o)}
    def ideal(o):
        o['directions'][1]['identities'][4]['combination'][1][1][0][0] = '0'
    def ideal_mu(o):
        o['displayedConstants']['mu'] = '184460384539621'
    def cube_root(o):
        o['contactRoots'][2] = '1/51'
    def cube_row(path):
        o = J(path)
        r = next(r for r in o['residuals'] if r['name'] == 'detector1.eSixth.definition')
        r['terms'][0]['coefficient'] = str(F(r['terms'][0]['coefficient']) + 1)
        return {path: dump(o)}
    def conic_row(path):
        o = J(path)
        r = next(r for r in o['residuals'] if r['name'] == 'scalar.secondConic')
        r['terms'][0]['coefficient'] = str(F(r['terms'][0]['coefficient']) + 1)
        return {path: dump(o)}
    t9, t17 = tables['pr09-385'], tables['pr17-380']
    R9, R17 = t9['roles'], t17['roles']
    noop = lambda *a: None
    controls = [
        ('table coefficient +1', lambda: {R17['table']: table_bump(R17['table'])},
         lambda p: check_table(p, t17, noop), 'sum of squares'),
        ('rows text coefficient +1', lambda: {R17['rowsText']: rows_text_bump(R17['rowsText'])},
         lambda p: check_table(p, t17, noop), 'rows text differs'),
        ('same row term negated in rows JSON and text', lambda: both_rows_bump(t17),
         lambda p: check_table(p, t17, noop), 'sum of squares'),
        ('diagonal divisor *3', lambda: cert_edit(R17['diagonalCertificate'], divisor),
         lambda p: check_table(p, t17, noop), 'diagonal identity fails'),
        ('diagonal power +1', lambda: cert_edit(R9['diagonalCertificate'], power),
         lambda p: check_table(p, t9, noop), 'diagonal identity fails'),
        ('transport lift coefficient *2', lambda: cert_edit(R9['transportCertificate'], lift),
         lambda p: check_transport(p, R9, noop), 'H = s*v'),
        ('transport conic input +1', lambda: cert_edit(R17['transportCertificate'], conic_input),
         lambda p: check_transport(p, R17, noop), 'conic is not'),
        ('outside consumer of a private slot', lambda: outside_consumer(t9),
         lambda p: check_transport(p, R9, noop), 'private slots occur outside'),
        ('ideal multiplier zeroed', lambda: cert_edit('rewrites/pr18-rows-A-tri.json', ideal),
         lambda p: check_ideal_certificate(p, 'rewrites/pr18-rows-A-tri.json', noop), 'identity fails'),
        ('Bh rescaling constant +1', lambda: cert_edit('rewrites/pr18-rows-A-tri.json', ideal_mu),
         lambda p: check_ideal_certificate(p, 'rewrites/pr18-rows-A-tri.json', noop), 'mu*(1+k*L)'),
        ('PR #18 second conic coefficient +1', lambda: conic_row(tables['pr18-379']['roles']['rawIr']),
         lambda p: check_ideal_certificate(p, 'rewrites/pr18-rows-A-tri.json', noop), 'scalar.secondConic'),
        ('contact root 1/50 -> 1/51', lambda: cert_edit('rewrites/pr13-cube-reuse-order45.json', cube_root),
         lambda p: check_cube_spec(p, 'rewrites/pr13-cube-reuse-order45.json', noop), 'Fmiddle'),
        ('PR #13 eSixth row coefficient +1', lambda: cube_row(tables['pr13-380']['roles']['rawIr']),
         lambda p: check_cube_spec(p, 'rewrites/pr13-cube-reuse-order45.json', noop), 'eSixth'),
    ]
    for name, mutate, run, expect in controls:
        packet = Packet(root, overrides=mutate())
        try:
            run(packet)
        except (CheckFailure, KeyError, ValueError) as e:
            need(expect in str(e), f'control {name!r} refused for the wrong reason: {e}')
            log(f'  refused: {name} ({e})')
            continue
        raise CheckFailure(f'control accepted: {name}')


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--packet', type=Path, default=Path(__file__).resolve().parent)
    ap.add_argument('--only', nargs='*')
    ap.add_argument('--verify-bindings', type=Path, metavar='REPO')
    ap.add_argument('--skip-tables', action='store_true')
    ap.add_argument('--no-controls', action='store_true', help='skip the negative controls')
    args = ap.parse_args()
    t0 = time.time()
    log = lambda s: print(s, flush=True)
    packet = Packet(args.packet)
    failures = 0
    def run(label, fn, *a):
        nonlocal failures
        t = time.time()
        try:
            fn(*a)
            log(f'PASS {label} ({time.time() - t:.1f}s)')
        except (CheckFailure, KeyError, ValueError, AssertionError) as e:
            failures += 1
            log(f'FAIL {label}: {type(e).__name__}: {e}')
    def files():
        for p in packet.records:
            packet.raw(p)
        st = binding_status(packet)
        nd = sum(1 for v in st.values() if v == 'published')
        log(f'  {len(packet.records)} files: stored and decompressed SHA-256/bytes match; '
            f'{nd} directly published, {len(st) - nd} stated in a bound file, '
            f'{len(packet.index["files"]) - len(st)} unbound, {len(packet.index.get("derived", {}))} derived here')
    run('manifest', lambda: log('  %d files, %d bytes' % check_manifest(packet.root)))
    run('file hashes and bindings', files)
    if args.verify_bindings:
        run('published bindings via git', lambda: log(f'  {check_bindings(packet, args.verify_bindings)} '
                                                      'recorded hashes found in the named public files'))
    if not args.skip_tables:
        for t in packet.index['tables']:
            if args.only and t['label'] not in args.only:
                continue
            log(f'{t["label"]} (PR #{t["pr"]}, head {t["head"][:8]})')
            run(t['label'], check_table, packet, t, log)
    run('rewrites/pr13-cube-reuse-order45.json', check_cube_spec, packet, 'rewrites/pr13-cube-reuse-order45.json', log)
    run('rewrites/pr13-cube-reuse-order47.json', check_cube_spec, packet, 'rewrites/pr13-cube-reuse-order47.json', log)
    run('rewrites/pr18-rows-A-tri.json', check_ideal_certificate, packet, 'rewrites/pr18-rows-A-tri.json', log)
    run('PR #16 source = PR #13 source (order 45)', check_same_raw, packet, 'pr13-380', 'pr16-380', log)
    run('PR #16 source = PR #13 source (order 47)', check_same_raw, packet, 'pr13-383-order47', 'pr16-383-order47', log)
    run('errata arithmetic', check_errata, log)
    if not args.no_controls:
        run('negative controls (13 in-memory mutations)', negative_controls, args.packet, log)
    log(f'{"ALL CHECKS PASSED" if not failures else f"{failures} CHECK(S) FAILED"} in {time.time() - t0:.1f}s '
        f'(Python {sys.version.split()[0]})')
    sys.exit(1 if failures else 0)


if __name__ == '__main__':
    main()
