"""Render docs/one-proof/OPEN.md and the other generated contributor files from the Lean data and the tables.

Inputs (run from the repository root):
* docs/one-proof/open-statements.json, written by `lake env lean scripts/one_proof/OpenStatements.lean`
  (the open hypotheses of ZInQ.OneProof.frozenTarget, read off the Lean build);
* docs/one-proof/kinds.tsv, the classification of each hypothesis (the source of truth for counts, packets,
  labels, tiers, flag classes and area issues);
* docs/one-proof/claims.tsv, who holds what (only a public claim line, on the claims issue or in a draft pull
  request that links it, holds a hypothesis, and the project's own holds may point at a pushed branch; a project
  brief is shown as project interest, free to claim; a released claim shows as open);
* docs/one-proof/reviews.tsv and credits.tsv, the ledgers of statement checks and credit;
* docs/one-proof/issues.json, the claim issue, the statement-checks issue, the packet issues and the issue that
  logs folds and landings;
* scratch/contrib-kit/DischargesTest-output.txt, the saved output of scratch/contrib-kit/DischargesTest.lean.

Outputs: docs/one-proof/OPEN.md, docs/one-proof/pages-wanted.md, the worked example in
docs/one-proof/CONTRIBUTING.md (between its worked-example markers) and the count block of STATUS.md (between
its open-count markers).

Usage: python3 scripts/one_proof/render_open.py [--check]
With --check, nothing is written: exit 1 if any output differs from what the inputs give, if a marker block is
missing, if the tables are inconsistent (hypotheses missing from kinds.tsv or no longer open, duplicate rows, a
flag without a class, a strictest-reading flag that does not match the strict columns, a value outside the fixed
vocabularies, an unheld hypothesis without an area issue, a held claim without a link), or if a generated,
contributor-facing or table file contains text that must not be public (session or worker labels, host names,
HTML markers, local paths).
"""
import csv, json, os, re, sys
from collections import Counter

D = 'docs/one-proof/'
EXAMPLE_OUT = 'scratch/contrib-kit/DischargesTest-output.txt'
CONTRIBUTING = D + 'CONTRIBUTING.md'
STATUS = 'STATUS.md'
FRONTIER = 'docs/research/frontier.md'
ISSUES = D + 'issues.json'
EX_BEGIN, EX_END = '<!-- worked-example:begin -->', '<!-- worked-example:end -->'
ST_BEGIN, ST_END = '<!-- open-count:begin -->', '<!-- open-count:end -->'

FLAG_CLASSES = ['pending-reading', 'reading-risk', 'restricted', 'unread', 'unverified-table',
                'unverified-locator', 'pending-review', 'strictest', 'note']
PAGES_WANTED = ['pending-reading', 'reading-risk', 'unread', 'unverified-table', 'unverified-locator',
                'pending-review']
LABELS = {
    'good-first': 'a good first target',
    'outside-first': 'offered to outside contributors first',
    'narrowing': 'pending narrowing: a narrower restatement is planned, so it is not offered as stated',
    'wave': "taken by the project's gap push",
    'plumbing-hold': 'not offered: a plumbing change removes it',
    'reading-hold': 'not offered: waits on a ruling about a reading',
    'project-interest': 'project interest, free to claim',
    'bigger': 'a bigger investment',
    'long-pole': 'statement checks first; Lean only at Mathlib scale',
}
NOT_OFFERED = ('plumbing-hold', 'reading-hold', 'narrowing', 'wave')
PACKETS = {
    'R1': 'Reduction block: SGA 7 I Exp. IX, BLR 1.2 Prop. 4, Serre-Tate 1968',
    'R2': 'Unread locators: SGA 3, EGA IV, Faltings 1983 Lemma 5, GIT, BLR 1.4, 7.2, 7.3',
    'R3': 'Tian-Yuan-Zhang and Gross-Zagier',
    'R4': 'The discriminant-6 Shimura curve',
    'R5': 'Heights',
    'R6': 'Theta and Siegel forms',
    'R7': 'p-adic Hodge theory and modular Galois representations',
    'R8': 'Faithfulness of the Lean definitions',
    'R9': 'Reading A of Tian-Yuan-Zhang Theorem 3.5',
    'R10': 'Picard scheme and Weil pairing',
}
TIERS = {'T1', 'T1-T2', 'T2', 'T2-T3', 'T2-T4', 'T3', 'T3-T4', 'T4'}
HOLDS = {'held', 'interest', 'released'}
HOLDER_KINDS = {'outside', 'project', 'maintainer'}
NUMBER = {1: 'one', 2: 'two', 3: 'three', 4: 'four', 5: 'five', 6: 'six', 7: 'seven', 8: 'eight', 9: 'nine'}
VERDICTS = {'YES', 'CONSEQUENCE', 'NO-statement', 'NO-locator', 'UNVERIFIED'}
COPIES = {'library-print', 'author-copy', 'scan'}
EVIDENCE = {'HUMAN-READ', 'AI-READ'}
CREDIT_KINDS = {'proof', 'reduction', 'statement-check', 'statement-fix', 'review', 'referee', 'setup'}
ISSUE_REF = re.compile(r'[\w.-]+/[\w.-]+#\d+')
# text that must not appear in generated, contributor-facing or table files. Site-specific patterns
# (session, user, host and worker names) stay out of the repository: put them in a file of
# `regex<TAB>label` lines named by $ONE_PROOF_HYGIENE_FILE.
HYGIENE = [
    (re.compile(r'<!--\s*zinq'), 'an HTML worker marker'),
    (re.compile(r'/Users/|/home/(?!runner/)\w+/|\.swarm-worktrees'), 'a local path'),
]
if os.environ.get('ONE_PROOF_HYGIENE_FILE'):
    for row in open(os.environ['ONE_PROOF_HYGIENE_FILE']).read().splitlines():
        if row.strip() and not row.startswith('#'):
            rx, what = row.split('\t', 1)
            HYGIENE.append((re.compile(rx), what))
PUBLIC_DOCS = ['CONTRIBUTING.md', D + 'CONTRIBUTING.md', D + 'STATEMENT-CHECKS.md']
TABLES = [D + 'kinds.tsv', D + 'claims.tsv', D + 'reviews.tsv', D + 'credits.tsv', D + 'fold-queue.tsv']


def read_tsv(path, required=True):
    if not os.path.exists(path):
        if required:
            sys.exit(f'missing {path}')
        return []
    with open(path, newline='') as fh:
        return [{k: (v or '') for k, v in r.items() if k is not None} for r in csv.DictReader(fh, delimiter='\t')]


def words(n):
    return NUMBER.get(n, str(n))


def anchor(f):
    return f.lower()


def cell(s):
    """Text safe inside a Markdown table cell."""
    return s.replace('|', '\\|')


def issue_url(ref):
    repo, num = ref.split('#')
    return f'https://github.com/{repo}/issues/{num}'


def issue_link(ref):
    """`owner/repo#n` as a Markdown link."""
    repo, num = ref.split('#')
    return f'[{repo.split("/")[0]} #{num}]({issue_url(ref)})'


def load():
    data = json.load(open(D + 'open-statements.json'))
    kinds_rows = read_tsv(D + 'kinds.tsv')
    issues = {'claims_issue': 'Deicyde/diophantine-z-q#14', 'statement_checks_issue': '', 'packet_issues': {},
              'log_issue': 'Deicyde/diophantine-z-q#3'}
    if os.path.exists(ISSUES):
        issues.update(json.load(open(ISSUES)))
    return dict(
        hyps=data['hypotheses'],
        kinds={r['field']: r for r in kinds_rows},
        kinds_rows=kinds_rows,
        claims_rows=read_tsv(D + 'claims.tsv'),
        reviews=read_tsv(D + 'reviews.tsv', required=False),
        credits=read_tsv(D + 'credits.tsv', required=False),
        issues=issues,
    )


def kinds_row_problems(r, open_fields, held):
    """Problems of one kinds.tsv row (also used by autofold.py on the rows it adds)."""
    problems, f = [], r['field']
    classes = [x for x in r['flag_class'].split(',') if x]
    if bool(r['flag'].strip()) != bool(classes):
        problems.append(f'kinds.tsv: {f}: a flag needs a flag_class and a flag_class needs a flag')
    bad = [x for x in classes if x not in FLAG_CLASSES]
    if bad:
        problems.append(f'kinds.tsv: {f}: unknown flag_class {bad}')
    if ('strictest' in classes) != (r['strict'] != r['strictest']):
        problems.append(f"kinds.tsv: {f}: flag_class 'strictest' must be set exactly when strict and "
                        'strictest differ')
    if r['label'] and r['label'] not in LABELS:
        problems.append(f"kinds.tsv: {f}: unknown label {r['label']!r}")
    if r['packet'] and r['packet'] not in PACKETS:
        problems.append(f"kinds.tsv: {f}: unknown packet {r['packet']!r}")
    if r['tier'] and r['tier'] not in TIERS:
        problems.append(f"kinds.tsv: {f}: unknown tier {r['tier']!r}")
    if r['area_issue'] and not ISSUE_REF.fullmatch(r['area_issue']):
        problems.append(f'kinds.tsv: {f}: area_issue must look like owner/repo#123')
    if not r['area_issue'] and f in open_fields and f not in held:
        problems.append(f'kinds.tsv: {f} is not held and has no area_issue')
    if r['strict'] not in ('LEAF', 'GLUE') or r['strictest'] not in ('LEAF', 'GLUE'):
        problems.append(f'kinds.tsv: {f}: strict and strictest must be LEAF or GLUE')
    return problems


def validate(m):
    """Consistency problems of the tables (each a string)."""
    problems = []
    hyps, kinds = m['hyps'], m['kinds']
    open_fields = [h['field'] for h in hyps]
    for name, rows in (('kinds.tsv', m['kinds_rows']), ('claims.tsv', m['claims_rows'])):
        dup = sorted(f for f, c in Counter(r['field'] for r in rows).items() if c > 1)
        if dup:
            problems.append(f'{name} has more than one row for {dup}')
    missing = sorted(set(open_fields) - set(kinds))
    stale = sorted(set(kinds) - set(open_fields))
    if missing:
        problems.append(f'kinds.tsv does not classify the open hypotheses {missing}')
    if stale:
        problems.append(f'kinds.tsv has rows for hypotheses that are no longer open: {stale}')
    for h in hyps:
        k = kinds.get(h['field'])
        if k and (k['bundle'] == 'frozenTarget') != (h['bundle'] == 'frozenTarget'):
            problems.append(f"kinds.tsv: {h['field']} has bundle {k['bundle']}, the Lean data says {h['bundle']}")
    held = set()
    for c in m['claims_rows']:
        f, hold, kind = c['field'], c['hold'], c['holder_kind']
        if f not in open_fields:
            problems.append(f'claims.tsv names {f}, which is not an open hypothesis')
        if hold not in HOLDS:
            problems.append(f'claims.tsv: {f}: hold must be one of {sorted(HOLDS)}, not {hold!r}')
        if kind not in HOLDER_KINDS:
            problems.append(f'claims.tsv: {f}: holder_kind must be one of {sorted(HOLDER_KINDS)}')
        if hold == 'held':
            held.add(f)
            if not c['claim_url'].startswith('https://github.com/'):
                problems.append(f'claims.tsv: {f} is held but has no GitHub link to the claim, branch or PR')
        if hold == 'interest' and (kind != 'project' or c['claim_url']):
            problems.append(f'claims.tsv: {f}: an interest row is a project row with no claim_url')
        if kind == 'project' and c['public_holder'] != 'project':
            problems.append(f"claims.tsv: {f}: a project holder's public_holder is 'project'")
        if kind in ('outside', 'maintainer') and not re.fullmatch(r'[A-Za-z0-9-]+', c['public_holder']):
            problems.append(f'claims.tsv: {f}: public_holder must be a GitHub login')
    for r in m['kinds_rows']:
        problems += kinds_row_problems(r, open_fields, held)
    for r in m['reviews']:
        f = r['field']
        if f not in kinds:
            problems.append(f'reviews.tsv: {f!r} is not a hypothesis in kinds.tsv')
        if r['verdict'] not in VERDICTS:
            problems.append(f"reviews.tsv: {f}: unknown verdict {r['verdict']!r}")
        if r['copy'] not in COPIES:
            problems.append(f"reviews.tsv: {f}: copy must be one of {sorted(COPIES)}")
        if r['evidence'] not in EVIDENCE:
            problems.append(f"reviews.tsv: {f}: evidence must be HUMAN-READ or AI-READ")
        if r['known_reader'] not in ('', 'yes'):
            problems.append(f"reviews.tsv: {f}: known_reader is empty or yes")
        if not r['ai_use']:
            problems.append(f'reviews.tsv: {f}: ai_use must be stated (none, or what a tool did)')
    for r in m['credits']:
        if r['kind'] not in CREDIT_KINDS:
            problems.append(f"credits.tsv: {r['item']}: unknown kind {r['kind']!r}")
    iss = m['issues']
    refs = [iss.get('claims_issue', ''), iss.get('log_issue', '')] \
        + ([iss['statement_checks_issue']] if iss.get('statement_checks_issue') else []) \
        + list(iss.get('packet_issues', {}).values())
    for ref in refs:
        if not ISSUE_REF.fullmatch(ref or ''):
            problems.append(f'issues.json: {ref!r} must look like owner/repo#123')
    for p in iss.get('packet_issues', {}):
        if p not in PACKETS:
            problems.append(f'issues.json: unknown packet {p!r}')
    return problems


def human_reads(m):
    """Field -> number of distinct readers with a HUMAN-READ reading."""
    readers = {}
    for r in m['reviews']:
        if r['evidence'] == 'HUMAN-READ' and r['quote'] and r['edition'] and r['page'] and r['ai_use']:
            readers.setdefault(r['field'], set()).add(r['reader'].lower())
    return {f: len(s) for f, s in readers.items()}


def render(m):
    hyps, kinds, iss = m['hyps'], m['kinds'], m['issues']
    h_fields = [h['field'] for h in hyps if h['bundle'] != 'frozenTarget']
    tops = [h['field'] for h in hyps if h['bundle'] == 'frozenTarget']
    claims = {c['field']: c for c in m['claims_rows']}
    reads = human_reads(m)
    n = len(h_fields)
    strict = Counter(kinds[f]['strict'] for f in h_fields)
    strictest = Counter(kinds[f]['strictest'] for f in h_fields)
    by_kind = Counter(kinds[f]['kind'] for f in h_fields)
    n_flags = sum(1 for f in h_fields if kinds[f]['strict'] != kinds[f]['strictest'])
    claims_url = issue_url(iss['claims_issue'])
    checks_ref = iss.get('statement_checks_issue') or ''

    def holder(c):
        if c['holder_kind'] == 'project':
            return 'the project'
        return f"[@{c['public_holder']}](https://github.com/{c['public_holder']})"

    def status(f):
        c = claims.get(f)
        if c and c['hold'] == 'held':
            return f"held by {holder(c)} ([claim]({c['claim_url']}))"
        lab = kinds[f]['label']
        if lab in NOT_OFFERED:
            return LABELS[lab]
        if (c and c['hold'] == 'interest') or lab == 'project-interest':
            return 'project interest, free to claim'
        if c and c['hold'] == 'released':
            return f"open (last released by {holder(c)}" + (f": {c['status']})" if c['status'] else ')')
        return 'open'

    def free(f):
        c = claims.get(f)
        return not (c and c['hold'] == 'held') and kinds[f]['label'] not in NOT_OFFERED

    def packet_venue(p):
        ref = iss.get('packet_issues', {}).get(p) or checks_ref or iss['claims_issue']
        return f'[{ref.split("/")[0]} #{ref.split("#")[1]}]({issue_url(ref)})'

    count_lines = [
        f'**{n} hypotheses of the H part** (in the bundles '
        f'`{"`, `".join(sorted({h["bundle"] for h in hyps if h["bundle"] != "frozenTarget"}))}`), '
        f'plus {len(tops)} hypotheses of the Tian–Yuan–Zhang and Gross–Zagier parts listed at the end.',
        '',
        f'* **Strict count: {strictest["LEAF"]} published / {strictest["GLUE"]} glue** (the strictest flagged reading; '
        + (f'{strict["LEAF"]}/{strict["GLUE"]} without the {words(n_flags)} strictest-reading '
           f'flag{"s" if n_flags != 1 else ""}).' if n_flags else 'no hypothesis carries a strictest-reading flag).'),
    ]

    out = []
    w = out.append
    w('# Open statements of the single proof')
    w('')
    w('<!-- Generated by scripts/one_proof/render_open.py from open-statements.json (the Lean build), kinds.tsv,')
    w('claims.tsv, reviews.tsv, credits.tsv and issues.json. Do not edit by hand: edit those, or regenerate the JSON')
    w('after a fold. -->')
    w('')
    w('`ZInQ.OneProof.frozenTarget` (`ZInQKernel/OneProof/Main.lean`) is a Lean theorem, checked by the kernel with no')
    w('`sorry` and only the standard axioms, that proves the frozen target `ZInQ.FrozenTarget`, the theorem that Z is')
    w('Diophantine in Q (the 11/5 manuscript, Theorem 1.1), from the hypotheses below. Everything else is proved.')
    w('Each hypothesis is a Lean `Prop`; proving one in Lean, or reducing it to statements printed in the literature,')
    w('removes it. See')
    w('[CONTRIBUTING.md](CONTRIBUTING.md) for how to contribute and check a proof.')
    edition = D + 'edition.json'
    if os.path.exists(edition):
        e = json.load(open(edition))
        w('')
        w(f"**Edition {e['edition']}**, cut at commit `{e['commit']}` on {e['date']}. A claimed statement keeps its "
          'form for the edition (see "Editions" in the root CONTRIBUTING.md).')
    w('')
    out.extend(count_lines)
    w('* LEAF means a published, refereed theorem stated over genuine definitions in its printed form, or a consequence')
    w('  of it that is never stronger. GLUE is everything else: a consequence of one theorem, a composite of several,')
    w('  project glue, or a leaf whose published form is still pending a reading (`kinds.tsv`, column `flag`).')
    w(f'* By kind: ' + ', '.join(f'{k} {v}' for k, v in sorted(by_kind.items())) + '.')
    w('')
    w('## How to help')
    w('')
    w('* **Prove a statement in Lean**: pick a row whose status is open or "project interest, free to claim", claim')
    w(f'  it on [issue #{iss["claims_issue"].split("#")[1]}]({claims_url}) with a line `Claiming <field> at <commit>`')
    w('  (the field name as in the first column), and follow [CONTRIBUTING.md](CONTRIBUTING.md).')
    w('* **Check a statement against its printed source** (no Lean needed): pick a packet below and follow')
    w('  [STATEMENT-CHECKS.md](STATEMENT-CHECKS.md). [pages-wanted.md](pages-wanted.md) lists the printed pages a')
    w('  reader can check.')
    w('* Tiers come from a model triage that no person has reviewed yet; treat them as a rough guide.')
    log_ref = iss['log_issue']
    w(f'* The project logs its folds and landings on [issue #{log_ref.split("#")[1]}]({issue_url(log_ref)}).')
    w('')

    w('## Good first targets')
    w('')
    firsts = [f for f in h_fields + tops if kinds[f]['label'] in ('good-first', 'outside-first') and free(f)]
    if firsts:
        for f in firsts:
            k = kinds[f]
            extra = [k['kind']] + ([f"tier {k['tier']}"] if k['tier'] else []) + \
                    ([issue_link(k['area_issue'])] if k['area_issue'] else [])
            w(f"* [`{f}`](#{anchor(f)}): {LABELS[k['label']]}; " + ', '.join(extra) + '.')
    else:
        w('None at the moment.')
    w('')

    w('## Held')
    w('')
    w('A hypothesis is held only by a public claim line, on the claims issue or in a draft pull request that links it')
    w("(the project's own holds may point at a pushed branch). A claim with no public activity for 14 days gets one")
    w('ping, and is released if there is no reply within 7 days of the ping.')
    w('')
    held = [f for f in h_fields + tops if f in claims and claims[f]['hold'] == 'held']
    if held:
        w('| hypothesis | holder | since |')
        w('| --- | --- | --- |')
        for f in held:
            c = claims[f]
            who = 'the project' if c['holder_kind'] == 'project' else f"@{c['public_holder']}"
            w(f"| [`{f}`](#{anchor(f)}) | {cell(who)} ([claim]({cell(c['claim_url'])})) | {cell(c['since'])} |")
    else:
        w('Nothing is held.')
    w('')

    w('## Packets')
    w('')
    w('A packet is a set of statements decided by reading one block of the literature. Claim a packet with a line')
    w('`Claiming reading <packet>` on its own issue if it has one, otherwise on the statement-checks issue'
      + ('' if checks_ref else f', and until that issue is opened on [issue #{iss["claims_issue"].split("#")[1]}]({claims_url})')
      + '; see [STATEMENT-CHECKS.md](STATEMENT-CHECKS.md).')
    w('')
    for p in PACKETS:
        members = [f for f in h_fields + tops if kinds[f]['packet'] == p]
        if not members:
            continue
        w(f'### Packet {p}')
        w('')
        w(f'{PACKETS[p]}. Claim it on {packet_venue(p)}.')
        w('')
        for f in members:
            k = kinds[f]
            cls = ', '.join(x for x in k['flag_class'].split(',') if x and x != 'note')
            w(f"* [`{f}`](#{anchor(f)}) ({k['strictest']}" + (f'; {cls}' if cls else '') + f"): {k['source']}")
        w('')

    w('## Index')
    w('')
    w('| hypothesis | bundle | kind | strict | flag class | label | tier | area | human reads | status |')
    w('| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |')
    order = sorted(h_fields, key=lambda f: (kinds[f]['strictest'] != 'GLUE', kinds[f]['bundle'], f.lower()))
    for f in order + tops:
        k = kinds[f]
        area = issue_link(k['area_issue']) if k['area_issue'] else ''
        w(f"| [`{f}`](#{anchor(f)}) | {cell(k['bundle'])} | {cell(k['kind'])} | {k['strictest']} | "
          f"{cell(k['flag_class'].replace(',', ', '))} | {cell(k['label'])} | {cell(k['tier'])} | {area} | "
          f"{reads.get(f, 0)} | {cell(status(f))} |")
    w('')

    hmap = {h['field']: h for h in hyps}

    def section(f, top=False):
        h, k = hmap[f], kinds[f]
        w(f'### {f}')
        w('')
        if top:
            w(f"* Argument `{f}` of `frozenTarget`; kind **{k['kind']}**, strict **{k['strictest']}**"
              + (f"; flag: {k['flag']}" if k['flag'] else '') + '.')
        else:
            w(f"* Bundle field `HDec.HSyn.{h['bundle']}.{f}`; kind **{k['kind']}**, strict **{k['strictest']}**"
              + (f"; flag: {k['flag']}" if k['flag'] else '') + '.')
        w(f"* Source: {k['source']}")
        bits = []
        if k['packet']:
            bits.append(f"packet [{k['packet']}](#packet-{k['packet'].lower()})")
        if k['label']:
            bits.append(f"label {k['label']} ({LABELS[k['label']]})")
        if k['tier']:
            bits.append(f"tier {k['tier']} (model triage, unreviewed)")
        if k['area_issue']:
            bits.append(f"discussion: {issue_link(k['area_issue'])}")
        if bits:
            w('* ' + '; '.join(bits) + '.')
        r = reads.get(f, 0)
        w(f"* Human readings recorded: {r if r else 'none'}.")
        w(f'* Status: {status(f)}.')
        w('')
        w('```lean')
        w(h['type'])
        w('```')
        if h['docstring'].strip():
            w('')
            for line in h['docstring'].strip().splitlines():
                w('> ' + line.strip())
        w('')

    w('## The hypotheses')
    w('')
    for f in order:
        section(f)
    w('## Tian–Yuan–Zhang and Gross–Zagier hypotheses')
    w('')
    w("These are `frozenTarget`'s other arguments (outside the H bundles); they are not part of the counts above.")
    w('')
    for f in tops:
        section(f, top=True)
    if m['credits']:
        w('## Credits')
        w('')
        w('| item | kind | contributor | AI-assisted | link |')
        w('| --- | --- | --- | --- | --- |')
        for r in m['credits']:
            w(f"| {cell(r['item'])} | {cell(r['kind'])} | {cell(r['contributor'])} | {cell(r['ai_assisted'])} | "
              f"{cell(r['url'])} |")
        w('')
    open_md = '\n'.join(out)

    pw = ['# Pages wanted', '',
          '<!-- Generated by scripts/one_proof/render_open.py from kinds.tsv. Do not edit by hand. -->', '',
          'Printed statements that a reader with the book or paper can check against the Lean statement in',
          '[OPEN.md](OPEN.md). How to do it, and what makes a reading count: [STATEMENT-CHECKS.md](STATEMENT-CHECKS.md).',
          '']
    for cls in PAGES_WANTED:
        rows = [f for f in h_fields + tops if cls in kinds[f]['flag_class'].split(',')]
        if not rows:
            continue
        pw += [f'## {cls}', '']
        for f in rows:
            k = kinds[f]
            pw.append(f"* [`{f}`](OPEN.md#{anchor(f)})" + (f" (packet {k['packet']})" if k['packet'] else '')
                      + f": {k['source']}. Flag: {k['flag']}")
        pw.append('')
    pages = '\n'.join(pw)

    status_lines = [count_lines[0].replace('listed at the end.', 'listed at the end of docs/one-proof/OPEN.md.')] \
        + count_lines[1:]
    status_block = '\n'.join([ST_BEGIN] + status_lines +
                             [f'* By kind: ' + ', '.join(f'{k} {v}' for k, v in sorted(by_kind.items())) + '.',
                              '* Generated from docs/one-proof/OPEN.md by scripts/one_proof/render_open.py.', ST_END])
    return open_md, pages, status_block


def splice(text, begin, end, body):
    """Replace what lies between the begin and end marker lines; None if the markers are absent."""
    i, j = text.find(begin), text.find(end)
    if i < 0 or j < 0 or j < i:
        return None
    return text[:i] + body + text[j + len(end):]


def outputs(m):
    """(path -> intended content of every generated file or block, problems with the marker blocks)."""
    open_md, pages, status_block = render(m)
    res = {D + 'OPEN.md': open_md + '\n', D + 'pages-wanted.md': pages + '\n'}
    problems = []
    text = open(CONTRIBUTING).read() if os.path.exists(CONTRIBUTING) else ''
    if EX_BEGIN in text:
        if not os.path.exists(EXAMPLE_OUT) or not open(EXAMPLE_OUT).read().strip():
            problems.append(f'{EXAMPLE_OUT} is missing or empty: run scratch/contrib-kit/DischargesTest.lean and '
                            'save its output there')
        else:
            example = open(EXAMPLE_OUT).read().rstrip('\n')
            body = EX_BEGIN + '\n```\n' + example + '\n```\n' + EX_END
            new = splice(text, EX_BEGIN, EX_END, body)
            if new is None:
                problems.append(f'{CONTRIBUTING}: the worked-example markers are out of order')
            else:
                res[CONTRIBUTING] = new
    if os.path.exists(STATUS):
        new = splice(open(STATUS).read(), ST_BEGIN, ST_END, status_block)
        if new is None:
            problems.append(f'{STATUS} has no {ST_BEGIN} ... {ST_END} block for the counts')
        else:
            res[STATUS] = new
    return res, problems


def hygiene(paths):
    problems = []
    for p in paths:
        if not os.path.exists(p):
            continue
        for i, line in enumerate(open(p).read().splitlines(), 1):
            for rx, what in HYGIENE:
                if rx.search(line):
                    problems.append(f'{p}:{i}: {what}: {line.strip()[:100]}')
    return problems


def main():
    m = load()
    problems = validate(m)
    if problems:
        print('\n'.join(problems))
        sys.exit(1)
    res, marker_problems = outputs(m)
    if '--check' in sys.argv:
        problems += marker_problems
        for p, content in res.items():
            if not os.path.exists(p) or open(p).read() != content:
                problems.append(f'{p} is out of date: run python3 scripts/one_proof/render_open.py')
        problems += hygiene(list(res) + PUBLIC_DOCS + TABLES)
        if os.path.exists(EXAMPLE_OUT):
            got = re.search(r'#discharges: (\d+) open hypotheses', open(EXAMPLE_OUT).read())
            if got and int(got.group(1)) != len(m['hyps']):
                print(f'note: {EXAMPLE_OUT} was made with {got.group(1)} open hypotheses, the Lean data has '
                      f"{len(m['hyps'])}: rerun scratch/contrib-kit/DischargesTest.lean after the fold")
        if os.path.exists(FRONTIER) and 'OPEN.md' not in open(FRONTIER).read(4000):
            print(f"note: {FRONTIER}'s header does not say that the public count is docs/one-proof/OPEN.md's")
        if problems:
            print('\n'.join(problems))
            sys.exit(1)
        print(f"ok: {len(m['hyps'])} open hypotheses, all classified; {len(res)} generated files up to date")
        return
    for p, content in res.items():
        if not os.path.exists(p) or open(p).read() != content:
            open(p, 'w').write(content)
            print(f'wrote {p}')
    for p in marker_problems:
        print('note:', p)
    h_fields = [h['field'] for h in m['hyps'] if h['bundle'] != 'frozenTarget']
    sc = Counter(m['kinds'][f]['strictest'] for f in h_fields)
    print(f"{len(h_fields)} H hypotheses, strictest {sc['LEAF']}/{sc['GLUE']}, {len(m['hyps']) - len(h_fields)} others")


if __name__ == '__main__':
    main()
