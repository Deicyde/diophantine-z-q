"""Derive the plain-text row files and the exact-rewrite certificates.

Provenance tool.  Reads only files already in this packet (via INDEX.json) and
writes derived files that check_evidence.py verifies independently: every
rows-<n>.txt must equal balanced/integer-ir.json and square-sum to the table,
and every identity in rewrites/*.json is re-expanded by the checker.
Python standard library only; imports nothing from the stack.

    python3 -B tools/derive.py PACKET_DIR
"""
import gzip, hashlib, json, sys
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path

GZ = dict(compresslevel=9, mtime=0)


def sha(b):
    return hashlib.sha256(b).hexdigest()


def read(packet, ppath):
    b = (packet / ppath).read_bytes()
    return gzip.decompress(b) if ppath.endswith('.gz') else b


def monomial_text(m):
    if not m:
        return '1'
    out, i = [], 0
    while i < len(m):
        j = i
        while j < len(m) and m[j] == m[i]:
            j += 1
        out.append(f'x{m[i]}' + (f'^{j-i}' if j - i > 1 else ''))
        i = j
    return '*'.join(out)


def rows_text(label, pr, ir):
    coords = sorted(ir['coordinates'], key=lambda c: c['id'])
    compact = {c['id']: k for k, c in enumerate(coords)}
    nterms = sum(len(r['terms']) for r in ir['residuals'])
    lines = ['# stack-public-evidence balanced rows v1',
             f'# Table {label} (PR #{pr}): variables {len(coords)}; rows {len(ir["residuals"])}; terms {nterms}.',
             '# The decimal table equals the sum over all rows below of (row)^2, exactly, over the integers.',
             '# V<TAB>k<TAB>irCoordinateId<TAB>name : table variable xk is IR coordinate irCoordinateId (increasing ids).',
             '# R<TAB>k<TAB>irResidualId<TAB>name   : starts row k; each following line until the next R is one term.',
             '# <integer><TAB><monomial>            : monomial is 1, xi, xi*xj with i<j, or xi^2, as in the table.']
    for k, c in enumerate(coords):
        lines.append(f'V\t{k}\t{c["id"]}\t{c["name"]}')
    for k, r in enumerate(ir['residuals']):
        lines.append(f'R\t{k}\t{r["id"]}\t{r["name"]}')
        terms = []
        for t in r['terms']:
            assert t['sPower'] == 0
            m = tuple(sorted(compact[i] for i in t['monomial']))
            q = F(t['coefficient'])
            assert q.denominator == 1 and q != 0
            terms.append((len(m), m, q.numerator))
        for _, m, c in sorted(terms):
            lines.append(f'{c}\t{monomial_text(m)}')
    return ('\n'.join(lines) + '\n').encode()


# ---- named polynomials over Q (formal S as the name '$S') -------------------

def add(*ps):
    out = defaultdict(F)
    for p in ps:
        for m, a in p.items():
            out[m] += a
    return {m: a for m, a in out.items() if a}


def scale(p, a):
    a = F(a)
    return {m: v * a for m, v in p.items() if v * a}


def mul(p, q):
    out = defaultdict(F)
    for m, a in p.items():
        for n, b in q.items():
            out[tuple(sorted(m + n))] += a * b
    return {m: a for m, a in out.items() if a}


def var(n):
    return {(n,): F(1)}


def const(a):
    return {(): F(a)} if a else {}


def decode(ir):
    names = {c['id']: c['name'] for c in ir['coordinates']}
    def poly(terms):
        out = defaultdict(F)
        for t in terms:
            out[tuple(sorted([names[i] for i in t['monomial']] + ['$S'] * t['sPower']))] += F(t['coefficient'])
        return {m: a for m, a in out.items() if a}
    return {r['name']: poly(r['terms']) for r in ir['residuals']}


def enc(p):
    return [[str(a), list(m)] for m, a in sorted(p.items(), key=lambda x: (len(x[0]), x[0]))]


def pr18_certificate(old_ir, new_ir, old_ref, new_ref):
    O, N = decode(old_ir), decode(new_ir)
    W, To, Tn = 'scalar.W2.quadratic', 'scalar.preparationT.quadratic', 'scalar.preparationT'
    bh, en, rin, norm = 'scalar.Bh.quadratic', 'scalar.normalized_e', 'scalar.rInverse', 'scalar.N'
    g0, g1 = 'S.chart.x.0.definition', 'S.chart.x.1.definition'
    u = [f'scalar.shiftedS.rootTimesInverseRoot.definition.{i}' for i in (0, 1)]
    ab = [(F(-39, 8), F(18)), (F(9, 2), F(-39, 4))]
    mu, k = F(184460384539620), F(521079743268, 81331739215)
    # r from the row r*ri-1; L from the row T0-L*W2 (both exact decodings of the actual rows).
    rr = add(O['scalar.rInverse.definition'], const(1))
    r = {tuple(v for v in m if v != rin): a for m, a in rr.items()}
    assert all(m.count(rin) == 1 for m in rr)
    rest = add(var(To), scale(O['scalar.preparationT.definition'], -1))
    L = {tuple(v for v in m if v != W): a for m, a in rest.items()}
    assert all(m.count(W) == 1 for m in rest)
    e, n2 = var(en), mul(var(norm), var(norm))
    forward = {
        'direction': 'old solution -> new solution',
        'targetSystem': 'new', 'baseSystem': 'old',
        'map': {Tn: enc(scale(mul(r, var(W)), 42)), bh: enc(scale(var(bh), mu))},
        'identities': [
            {'row': u[0], 'combination': [[u[0], enc(const(1))], [g0, enc(const(ab[0][0]))], [g1, enc(const(ab[0][1]))]]},
            {'row': u[1], 'combination': [[u[1], enc(const(1))], [g0, enc(const(ab[1][0]))], [g1, enc(const(ab[1][1]))]]},
            {'row': 'scalar.preparationT.definition',
             'combination': [['scalar.rInverse.definition', enc(scale(var(W), 42))],
                             ['scalar.W2.definition', enc(const(42))]]},
            {'row': 'scalar.Bh.definition',
             'combination': [['scalar.Bh.definition', enc(const(mu))],
                             ['scalar.preparationT.definition', enc(scale(e, mu * k))]]},
            {'row': 'scalar.secondConic', 'combination': [['scalar.secondConic', enc(const(1))]]},
        ]}
    reverse = {
        'direction': 'new solution -> old solution',
        'targetSystem': 'old', 'baseSystem': 'new',
        'map': {W: enc(n2), To: enc(mul(L, n2)), bh: enc(scale(var(bh), 1 / mu))},
        'identities': [
            {'row': u[0], 'combination': [[u[0], enc(const(1))], [g0, enc(const(-ab[0][0]))], [g1, enc(const(-ab[0][1]))]]},
            {'row': u[1], 'combination': [[u[1], enc(const(1))], [g0, enc(const(-ab[1][0]))], [g1, enc(const(-ab[1][1]))]]},
            {'row': 'scalar.W2.definition', 'combination': []},
            {'row': 'scalar.preparationT.definition', 'combination': []},
            {'row': 'scalar.Bh.definition',
             'combination': [['scalar.Bh.definition', enc(const(1 / mu))],
                             ['scalar.preparationT.definition', enc(scale(mul(e, r), 1 / mu))],
                             ['scalar.rInverse.definition', enc(scale(mul(e, var(Tn)), -1 / mu))]]},
            {'row': 'scalar.secondConic', 'combination': [['scalar.secondConic', enc(const(1))]]},
        ]}
    return {
        'format': 'stack-public-evidence-ideal-certificate-v1',
        'layer': 'PR #18 scalar-row-reduction: row changes A and tri',
        'old': old_ref, 'new': new_ref,
        'polynomialEncoding': 'list of [rational coefficient, sorted list of coordinate names]; "$S" is the formal fixed parameter S',
        'meaning': ('For each direction, apply "map" (coordinate name -> polynomial in the base system; unmapped names '
                    'are the identity) to every row of the target system. A listed row must equal the sum of '
                    'multiplier*row over its combination of base rows; every unlisted target row must equal the '
                    'base row of the same name. Hence each map sends solutions to solutions. Neither map touches '
                    'the input or any coordinate outside "map".'),
        'expectedDelta': {
            'deletedRows': ['scalar.W2.definition'], 'addedRows': [],
            'changedRows': sorted(u + ['scalar.preparationT.definition', 'scalar.Bh.definition', 'scalar.secondConic']),
            'removedCoordinates': sorted([W, To]), 'addedCoordinates': [Tn]},
        'displayedConstants': {'A.u0': ['-39/8', '18'], 'A.u1': ['9/2', '-39/4'], 'mu': str(mu), 'k': str(k),
                               'claim': 'mu*(1+k*L) = 42*r, with r and L decoded from the actual rows'},
        'r': enc(r), 'L': enc(L),
        'directions': [forward, reverse],
    }


ROOTS = ['0', '1/49', '1/50', '1/2450', '32/1225']


def cube_spec(before_ref, after_ref, high):
    after, before = [], []
    for i in range(3):
        p = f'detector{i}.'
        after += [
            {'row': p + 'Fsquare.definition', 'lhs': [[1, [p + 'Fsquare']]], 'rhs': [[1, [p + 't', p + 't']]]},
            {'row': p + 'Fmiddle.definition', 'lhs': [[1, [p + 'Fmiddle']]],
             'rhs': [[1, [p + 'Fsquare', p + 't']], ['c4', [p + 'Fsquare']], ['c3', [p + 't']], ['c2', []]]},
            {'row': p + 'eCubed.definition', 'lhs': [[1, [p + 'eCubed']]],
             'rhs': [[1, [p + 'q1CubedForWeights', p + 'deltaCubed']]]},
            {'row': p + 'eSixth.definition', 'lhs': [[1, [p + 'eSixth']]], 'rhs': [[1, [p + 'eCubed', p + 'eCubed']]]},
            {'row': p + 'eTwelfth.definition', 'lhs': [[1, [p + 'eTwelfth']]], 'rhs': [[1, [p + 'eSixth', p + 'eSixth']]]},
            {'row': p + 'q12.definition', 'lhs': [[1, [p + 'q12', p + 'eDelta']]], 'rhs': [[1, [p + 'eTwelfth', p + 'eTwelfth']]]},
        ]
        before += [
            {'row': p + 'mixA.definition', 'lhs': [[1, [p + 'mixA']]], 'rhs': [[1, [p + 'eDelta', p + 'eDelta']]]},
            {'row': p + 'mixB.definition', 'lhs': [[1, [p + 'mixB']]], 'rhs': [[1, [p + 'mixA', p + 'eDelta']]]},
            {'row': p + 'mixC.definition', 'lhs': [[1, [p + 'mixC']]], 'rhs': [[1, [p + 'q1CubedForWeights', p + 'mixB']]]},
            {'row': p + 'mixD.definition', 'lhs': [[1, [p + 'mixD']]], 'rhs': [[1, [p + 'mixC', p + 'mixC']]]},
            {'row': p + 'q12.definition', 'lhs': [[1, [p + 'q12', p + 'eDelta']]], 'rhs': [[1, [p + 'mixD', p + 'mixD']]]},
        ]
    return {
        'format': 'stack-public-evidence-cube-reuse-v1',
        'layer': f'PR #13 detector-cube-reuse ({high})',
        'before': before_ref, 'after': after_ref,
        'meaning': ('Row-level certificate. Each listed row must be a nonzero rational multiple of '
                    'sum(lhs) - sum(rhs), where each entry is [coefficient, product of named values] and the '
                    'named values are the affine "values" of that raw IR. c2,c3,c4 are the coefficients of '
                    't^2,t^3,t^4 in prod(t - root). The cubic alias deltaCubed must be affine, own no coordinate, '
                    'and equal (98t-1)^3 after solving the t, Fsquare, Fmiddle aliases for their coordinates. '
                    'All other rows, the inverse guards and every common named value must be identical.'),
        'contactRoots': ROOTS,
        'expectedDelta': {
            'deletedRows': sorted(f'detector{i}.{n}.definition' for i in range(3) for n in ['mixA', 'mixB', 'mixC', 'mixD']),
            'addedRows': sorted(f'detector{i}.{n}.definition' for i in range(3) for n in ['eCubed', 'eSixth', 'eTwelfth']),
            'changedRows': sorted(f'detector{i}.q12.definition' for i in range(3))},
        'afterIdentities': after, 'beforeIdentities': before,
        'cubicAliases': [{'t': f'detector{i}.t', 'square': f'detector{i}.Fsquare', 'middle': f'detector{i}.Fmiddle',
                          'cube': f'detector{i}.deltaCubed', 'slope': 98} for i in range(3)],
    }


REPORT = ('Existing producer report or small certificate from the build at this head; no published hash '
          '(several such files carry timing fields, cf. conditional-quartic-reduction/EXPECTED_OUTPUTS.json '
          '"diagnosticsNotByteCompared"). Included as the existing check record; check_evidence.py does not rely on it.')
UNBOUND_REASONS = {
    'transportCertificate': ('No published hash for any layer. Included because it states the four factored-pole maps; '
                             'check_evidence.py re-derives every identity it states from the pre-transport and '
                             'pre-diagonal IRs, so its content is verified rather than trusted.'),
    'preTransportIr': ('detector-cube-reuse/EXPECTED.json binds only builder, raw, final and polynomial files. Included '
                       'as the compiled input of the transport; check_evidence.py checks it equals compiled-ir.json at '
                       'the fixed S and transports exactly to the bound final/integer-candidate-ir.json.'),
    'compiledIr': ('Not bound for #13 (see preTransportIr). Included as the compiled IR; its link to the bound raw IR is '
                   'covered only by the included, likewise unbound, gate-check report.'),
    'reductionCertificate': ('Not bound for #13. Included as the compiler\'s reduction certificate (raw -> compiled); '
                             'not replayed by check_evidence.py.'),
    'baselineRawIr': ('The cube build\'s baseline/raw-translated-ir.json for the optional order-47 route: the source '
                      'before cube reuse, anchor 3^2016. No published hash. Included because the order-47 cube-reuse '
                      'certificate compares against it; that check requires every row other than the 24 named ones, '
                      'every guard and every common named value to be identical to the bound order-47 raw IR.'),
}


def main():
    packet = Path(sys.argv[1])
    index = json.loads((packet / 'INDEX.json').read_text())
    tables = {t['label']: t for t in index['tables']}
    derived = {}
    for t in index['tables']:
        ir = json.loads(read(packet, t['roles']['rowsIr']))
        data = rows_text(t['label'], t['pr'], ir)
        ppath = f'tables/{t["label"]}/rows-{t["variables"]}.txt.gz'
        stored = gzip.compress(data, **GZ)
        (packet / ppath).write_bytes(stored)
        t['roles']['rowsText'] = ppath
        derived[ppath] = {'packetPath': ppath, 'sha256': sha(data), 'bytes': len(data), 'storedSha256': sha(stored),
                          'storedBytes': len(stored), 'compressed': True, 'derivedFrom': [t['roles']['rowsIr']],
                          'bound': False, 'derivedBy': 'tools/derive.py'}
    for t in index['tables']:
        for role, ppath in t['roles'].items():
            rec = index['files'].get(ppath)
            if rec is not None and not rec['bound'] and 'unboundReason' not in rec:
                rec['unboundReason'] = UNBOUND_REASONS.get(role, REPORT)
    def ref(label, role):
        p = tables[label]['roles'][role]
        return {'table': label, 'role': role, 'packetPath': p, 'sha256': index['files'][p]['sha256']}
    rw = packet / 'rewrites'
    rw.mkdir(exist_ok=True)
    outs = {
        'rewrites/pr18-rows-A-tri.json': pr18_certificate(
            json.loads(read(packet, tables['pr17-380']['roles']['rawIr'])),
            json.loads(read(packet, tables['pr18-379']['roles']['rawIr'])),
            ref('pr17-380', 'rawIr'), ref('pr18-379', 'rawIr')),
        'rewrites/pr13-cube-reuse-order45.json': cube_spec(ref('pr12-383', 'rawIr'), ref('pr13-380', 'rawIr'), 'default order 45, anchor 3^2130'),
        'rewrites/pr13-cube-reuse-order47.json': cube_spec(ref('pr13-383-order47', 'baselineRawIr'), ref('pr13-383-order47', 'rawIr'), 'optional order 47, anchor 3^2016'),
    }
    for p, obj in outs.items():
        data = (json.dumps(obj, indent=1) + '\n').encode()
        (packet / p).write_bytes(data)
        derived[p] = {'packetPath': p, 'sha256': sha(data), 'bytes': len(data), 'storedSha256': sha(data),
                      'storedBytes': len(data), 'compressed': False, 'bound': False, 'derivedBy': 'tools/derive.py',
                      'derivedFrom': sorted({v['packetPath'] for k, v in obj.items() if k in ('old', 'new', 'before', 'after')})}
    index['derived'] = derived
    (packet / 'INDEX.json').write_text(json.dumps(index, indent=1) + '\n')
    print('derived', len(derived))


if __name__ == '__main__':
    main()
