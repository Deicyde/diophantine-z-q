"""Read public claims from GitHub and reconcile docs/one-proof/claims.tsv with them.

Claims live in four places, named in docs/one-proof/issues.json: the claims issue (and pull requests that
link it), the statement-checks issue, the packet issues of the no-Lean readings, plus the older upstream area
issues. This script reads them (read-only), parses the claim lines, and reports or writes what claims.tsv
should say. It never posts anything: pings and releases are printed as a queue for the fork owner's batched
posting run.

Claim lines (one per line of a comment or pull request body; backticks around a name are allowed; quoted
lines and fenced code blocks are ignored):
  Claiming <name>[, <name> ...] at <commit>   names are Lean field names, frontier IDs (H-101 or H101, T-3,
                                               Z-1), ranges of IDs (H-98-H-102) or Lean constant names;
                                               `at <commit>` is optional here
  Claiming reading <packet>                    a no-Lean reading packet, R1-R10
  Releasing <name>[, ...]: <what blocked you>  releases at once; a line by the project account that names
                                               @login releases that holder's claim
  Progress <name>: <text>                      optional; any comment by the holder counts as activity
  Ping (claim lapse): <name>                   written by the batched run when it pings a holder

The last action per field per person wins. Frontier IDs and constant names are mapped to fields through
docs/one-proof/frontier-crosswalk.tsv (optional) and docs/one-proof/open-statements.json; every ID or
CamelCase name in a claim's name list that maps to no open field is reported, not dropped.

Rows of claims.tsv: `hold` is held, interest (project rows only) or released (the blocker is in `status`,
cleaned by public_text()). By default the script never changes a project row; it reports what it would change
for the integrator. It changes an outside or maintainer row only on a parsed claim, a parsed Releasing line, or
the lapse rule. With --project-claims (the claims-sync workflow, the only writer of claims.tsv) it also writes
project rows from the project's own claim and release lines, drops rows whose field is no longer open, and
holds an outside login with no row in credits.tsv to one held row; plan() has the rules.

Usage, from anywhere:
  sync_claims.py --fetch OUT.json            fetch the comments and pull requests to OUT.json, then stop
  sync_claims.py [--from-json FILE]          report what claims.tsv would become (default: fetch first)
  sync_claims.py [--from-json FILE] --write [--project-claims] [--today YYYY-MM-DD]
                                             update claims.tsv in place
  sync_claims.py [--from-json FILE] --check FIELD [FIELD ...]
                                             exit 1 if a field is held by someone other than the project or
                                             is labelled good-first or outside-first in kinds.tsv
  sync_claims.py [--from-json FILE] --sweep [--today YYYY-MM-DD]
                                             print the ping and release queue (TSV) under the lapse policy
"""
import argparse
import csv
import datetime
import json
import os
import re
import subprocess
import sys
import tempfile

# ---- configuration -------------------------------------------------------------------------------------

DEFAULT_ISSUES = {'claims_issue': 'Deicyde/diophantine-z-q#14', 'statement_checks_issue': '',
                  'packet_issues': {}}
UPSTREAM = 'elliotglazer/diophantine-z-q'
UPSTREAM_ISSUES = [37, 74, 76] + list(range(78, 87))   # older claims here stay valid
PROJECT_LOGINS = {'deicyde'}           # the project account (casefolded)
MAINTAINER_LOGINS = {'elliotglazer'}   # the upstream owner (casefolded)
PROJECT_HOLDER = 'project'             # public_holder of project rows
PING_DAYS = 14                         # no activity for this long brings one ping
RELEASE_DAYS = 7                       # no reply this long after the ping releases the claim
PING_DELTA = datetime.timedelta(days=PING_DAYS)
RELEASE_DELTA = datetime.timedelta(days=RELEASE_DAYS)
PING_TEXT = 'Ping (claim lapse): {field}'   # the marker line the batched run writes in a ping
NEW_COLUMNS = ['holder_kind', 'public_holder', 'claim_url', 'hold']
OFFER_LABELS = ('good-first', 'outside-first')
RANGE_MAX = 30                         # longest ID range expanded
ID_DIGITS = 6                          # longest number read in an ID range (int() refuses over 4300 digits)
STATUS_MAX = 200                       # longest release text written to claims.tsv

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DOCS = os.path.join(ROOT, 'docs', 'one-proof')
UTC = datetime.timezone.utc

# ---- parsing helpers -----------------------------------------------------------------------------------

HTML_COMMENT = re.compile(r'<!--.*?-->', re.S)
FENCE = re.compile(r'^ {0,3}(`{3,}|~{3,})')
LINE = re.compile(r'^[\s*_-]*(?:(Claiming|Releasing|Progress)\s+|(Ping \(claim lapse\)):\s*)(.*)$')
READING = re.compile(r'^reading\s+(R\d+)\b')
ID_FULL = re.compile(r'([HTZ])-?(\d+)')
ID = re.compile(r'(?<![\w.])([HTZ])-?(\d+)(?!\w|\.\w)')
RANGE = re.compile(r'(?<![\w.])([HTZ])-?(\d+)[-\u2013](?:\1-?)?(\d+)(?!\w|\.\w)')
LABEL = re.compile(r'\b(?:W\d+|[Ww]orker\s+\d+)\b')
LEAD_LABEL = re.compile(r'^\s*(?:W\d+|[Ww]orker\s+\d+)\b\s*:?\s*')
MENTION = re.compile(r'(?<![\w@/])@([A-Za-z0-9][A-Za-z0-9-]*)')
BACKTICK = re.compile(r'`([^`]*)`')
IDENT = re.compile(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*")
HEX = re.compile(r'[0-9a-f]{7,40}')
CAMEL = re.compile(r'[a-z0-9][A-Z]|[A-Z]{2}[a-z]')
NOT_NAMES = {'arXiv', 'GitHub', 'LaTeX', 'TeX'}
# where the list of names in a claim line ends
CLAIM_END = re.compile(r'\s+at\s|;|:|\.\s|\.$|\s-{1,2}\s|\u2014|\u2013\s')
# for public_text(): an HTML comment (to its end, or to the end of the text) or tag; an absolute path (/a/b, ~/a/b,
# C:\a\b) with at least two separators, not inside a URL or a relative path
TAG = re.compile(r'<!--.*?(?:-->|$)|</?[A-Za-z][\w-]*(?:\s[^<>]*)?/?>', re.S)
ABS_PATH = re.compile(r'(?<![\w.:/\\~-])(?:~/|/|[A-Za-z]:[\\/])[^\s/\\]*(?:[\\/][^\s/\\]*)+')
PATH_TAIL = '.,;:!?)]}>\'"`'           # punctuation after a path, kept when the path is replaced
# render_open.py's built-in 'a local path' hygiene pattern: a token matching it anywhere would fail the folds'
# render_open.py --check, so public_text replaces the whole token (ABS_PATH misses paths glued to ':' or '.').
LOCAL_PATH = re.compile(r'/Users/|/home/(?!runner/)\w+/|\.swarm-worktrees')
QUOTES = '"\'\u201c\u201d\u2018\u2019'


def key_of(login):
    return (login or '').casefold()


def kind_of(login):
    k = key_of(login)
    if k in PROJECT_LOGINS:
        return 'project'
    if k in MAINTAINER_LOGINS:
        return 'maintainer'
    return 'outside'


def holder_name(login):
    """The public_holder value for a login: the login itself, or 'project' for the project account."""
    return PROJECT_HOLDER if kind_of(login) == 'project' else login


def holder_key(login):
    """The key a holder is matched on: 'project' for the project account, else the casefolded login."""
    return PROJECT_HOLDER if kind_of(login) == 'project' else key_of(login)


def holder_kind(public_holder):
    return 'project' if public_holder == PROJECT_HOLDER else kind_of(public_holder)


def parse_time(s):
    return datetime.datetime.strptime(s.replace('Z', '+0000'), '%Y-%m-%dT%H:%M:%S%z')


def when(node):
    """max(createdAt, lastEditedAt): an edited claim counts from the edit."""
    t = parse_time(node.get('createdAt') or node['updatedAt'])
    if node.get('lastEditedAt'):
        t = max(t, parse_time(node['lastEditedAt']))
    return t


def head_constant(ty):
    """The constant a hypothesis type is about (as in scripts/one_proof/frontier_crosswalk.py)."""
    body = ty.rsplit(',', 1)[-1] if ty.lstrip().startswith('∀') else ty
    tok = body.strip().split()[0] if body.strip() else ''
    return tok.strip('()')


def read_tsv(path):
    """(header, rows) of a tab-separated file; rows are dicts, missing trailing cells are ''."""
    with open(path, newline='', encoding='utf-8') as fh:
        lines = list(csv.reader(fh, delimiter='\t', quoting=csv.QUOTE_NONE))
    if not lines:
        return [], []
    header = lines[0]
    rows = [{h: (r[i] if i < len(r) else '') for i, h in enumerate(header)}
            for r in lines[1:] if any(c.strip() for c in r)]
    return header, rows


def write_tsv(path, header, rows):
    clean = lambda v: (v or '').replace('\t', ' ').replace('\n', ' ')
    out = ['\t'.join(header)] + ['\t'.join(clean(r.get(h)) for h in header) for r in rows]
    with open(path, 'w', encoding='utf-8') as fh:
        fh.write('\n'.join(out) + '\n')


def split_ref(ref):
    repo, n = ref.rsplit('#', 1)
    return repo, int(n)


class Config:
    """The claim threads: the claims issue, the statement-checks issue, the packet issues, the area issues."""

    def __init__(self, issues=None):
        cfg = dict(DEFAULT_ISSUES)
        cfg.update(issues or {})
        self.claims = split_ref(cfg['claims_issue'])
        self.checks = split_ref(cfg['statement_checks_issue']) if cfg.get('statement_checks_issue') else None
        self.packets = {p: split_ref(r) for p, r in (cfg.get('packet_issues') or {}).items() if r}
        self.fork = self.claims[0]
        self.claims_key = '%s#%d' % self.claims
        repo, n = self.claims
        self.links = re.compile(r'(?<![\w/#])#%d\b|%s(?:#|/issues/)%d\b' % (n, re.escape(repo), n))

    @classmethod
    def load(cls, path):
        if path and os.path.exists(path):
            with open(path, encoding='utf-8') as fh:
                return cls(json.load(fh))
        return cls()

    def role(self, repo, n):
        if (repo, n) == self.claims:
            return 'claims'
        if self.checks and (repo, n) == self.checks:
            return 'checks'
        if (repo, n) in self.packets.values():
            return 'packet'
        if repo == UPSTREAM and n in UPSTREAM_ISSUES:
            return 'area'
        return None

    def fetch_plan(self):
        """repo -> issue numbers to fetch."""
        plan = {self.fork: [self.claims[1]]}
        for ref in ([self.checks] if self.checks else []) + sorted(self.packets.values()):
            plan.setdefault(ref[0], [])
            if ref[1] not in plan[ref[0]]:
                plan[ref[0]].append(ref[1])
        plan.setdefault(UPSTREAM, [])
        plan[UPSTREAM] += [n for n in UPSTREAM_ISSUES if n not in plan[UPSTREAM]]
        return plan


class Fields:
    """The open fields and the maps from frontier IDs and Lean constant names to them."""

    def __init__(self, open_path, crosswalk_path=None, kinds_path=None):
        with open(open_path, encoding='utf-8') as fh:
            hyps = json.load(fh)['hypotheses']
        self.open = [h['field'] for h in hyps]
        self.open_set = set(self.open)
        self.by_const = {}
        for h in hyps:
            c = head_constant(h['type'])
            if c:
                self.by_const.setdefault(c, h['field'])
        self.crosswalk = None
        if crosswalk_path and os.path.exists(crosswalk_path):
            self.crosswalk = {r['id']: r for r in read_tsv(crosswalk_path)[1]}
        self.kinds = {}
        if kinds_path and os.path.exists(kinds_path):
            self.kinds = {r['field']: r for r in read_tsv(kinds_path)[1]}

    def labels(self, field):
        return {x.strip() for x in (self.kinds.get(field, {}).get('label') or '').split(',') if x.strip()}

    def _const(self, name):
        for c, f in self.by_const.items():
            if c == name or c.endswith('.' + name) or name.endswith('.' + c):
                return f
        for row in (self.crosswalk or {}).values():
            c = self._lean_const(row.get('lean_name') or '')
            f = row.get('field') or ''
            if c and f in self.open_set and (c == name or c.endswith('.' + name) or name.endswith('.' + c)):
                return f
        last = name.rsplit('.', 1)[-1]
        lower = last[:1].lower() + last[1:]
        return lower if lower in self.open_set else None

    @staticmethod
    def _lean_const(lean):
        lean = lean.split(' : ', 1)[1] if ' : ' in lean else lean
        return head_constant(lean) if lean.strip() else ''

    def resolve(self, name):
        """(field, '') or (None, reason)."""
        if name in self.open_set:
            return name, ''
        m = ID_FULL.fullmatch(name)
        if m:
            name = f'{m.group(1)}-{m.group(2)}'
            if self.crosswalk is None:
                return None, 'frontier ID, and no crosswalk file to map it'
            row = self.crosswalk.get(name)
            if row is None:
                return None, 'frontier ID not in the crosswalk'
            if (row.get('field') or '') in self.open_set:
                return row['field'], ''
            lean = row.get('lean_name') or ''
            if ' : ' in lean and lean.split(' : ', 1)[0].strip() in self.open_set:
                return lean.split(' : ', 1)[0].strip(), ''
            c = self._lean_const(lean)
            f = self._const(c) if c else None
            if f:
                return f, ''
            return None, 'frontier ID maps to no open field'
        f = self._const(name)
        if f:
            return f, ''
        return None, 'names no open field'


def looks_like_name(t):
    """A token that is meant as a Lean name: dotted with a capital, or CamelCase."""
    if t in NOT_NAMES:
        return False
    return ('.' in t and any(ch.isupper() for ch in t)) or bool(CAMEL.search(t))


def names_in(text, fields):
    """Resolve the names in the list part of a claim, release or progress line.

    Returns (resolved fields in order, [(name, reason)] for names that map to no open field). Frontier
    IDs, ranges of them, backticked names, dotted constant names and CamelCase words are reported when they
    map to no open field; other bare words count only when they are an open field or a constant of one.
    Worker labels (W16, Worker 5) and @mentions are dropped.
    """
    found, unmatched = [], []

    def add(name, strict):
        f, why = fields.resolve(name)
        if f:
            if f not in found:
                found.append(f)
        elif strict and (name, why) not in unmatched:
            unmatched.append((name, why))

    text = MENTION.sub(' ', LABEL.sub(' ', text))
    for m in BACKTICK.finditer(text):
        t = m.group(1).strip()
        if t and not re.search(r'[\s/]', t) and not HEX.fullmatch(t):
            add(t, True)
    rest = BACKTICK.sub(' ', text)
    for m in RANGE.finditer(rest):
        letter, lo, hi = m.group(1), m.group(2), m.group(3)
        lo, hi = (int(lo), int(hi)) if max(len(lo), len(hi)) <= ID_DIGITS else (0, 0)   # (0, 0): reported below
        if lo < hi <= lo + RANGE_MAX:
            for n in range(lo, hi + 1):
                add(f'{letter}-{n}', True)
        elif (m.group(0), 'range not supported') not in unmatched:
            unmatched.append((m.group(0), 'range not supported'))
    rest = RANGE.sub(' ', rest)
    for m in ID.finditer(rest):
        add(f'{m.group(1)}-{m.group(2)}', True)
    rest = ID.sub(' ', rest)
    for m in IDENT.finditer(rest):
        t = m.group(0)
        if HEX.fullmatch(t):
            continue
        add(t, looks_like_name(t))
    return found, unmatched


def claim_parts(rest, fields):
    """(name list, the rest of the line) of a claim line, after a leading worker label is dropped.

    The list ends at ` at `, `;`, `:`, a full stop and the like. When the text before a `:` names nothing
    (a label such as 'for the project:'), the list is the text after it.
    """
    rest = LEAD_LABEL.sub('', rest, count=1)
    cut = CLAIM_END.search(rest)
    if not cut:
        return rest, ''
    head, after = rest[:cut.start()], rest[cut.end():]
    if cut.group(0) == ':' and names_in(head, fields) == ([], []):
        cut2 = CLAIM_END.search(after)
        return (after[:cut2.start()], after[cut2.end():]) if cut2 else (after, '')
    return head, after


def visible_lines(body):
    """The lines of a body outside HTML comments, fenced code blocks and quotes."""
    body = HTML_COMMENT.sub('', body or '')
    fence = None
    for line in body.splitlines():
        m = FENCE.match(line)
        if m:
            if fence is None:
                fence = m.group(1)[0]
                continue
            if m.group(1)[0] == fence:
                fence = None
                continue
        if fence is not None or line.lstrip().startswith('>'):
            continue
        yield line


def parse_lines(body):
    """Yield (verb, rest of line) for each claim, release, progress or ping line of a body."""
    for line in visible_lines(body):
        m = LINE.match(line.replace('**', ''))
        if m:
            yield (m.group(1) or 'Ping'), m.group(3).strip()


# ---- reading the data ----------------------------------------------------------------------------------

def comment_of(c, fallback_url):
    return {'login': (c.get('author') or {}).get('login') or 'ghost', 'date': when(c),
            'url': c.get('url') or fallback_url, 'body': c.get('body') or ''}


def load_threads(data, cfg=None):
    """The fetched issues and pull requests that can carry claims, keyed 'owner/repo#n'."""
    cfg = cfg or Config()
    threads = {}
    for repo, rd in data.get('repos', {}).items():
        for issue in rd.get('issues', []):
            n = issue['number']
            role = cfg.role(repo, n)
            if role is None:
                continue
            url = issue.get('url') or issue_url(repo, n)
            threads[f'{repo}#{n}'] = {'key': f'{repo}#{n}', 'role': role, 'url': url,
                                      'comments': [comment_of(c, url) for c in issue.get('comments', [])]}
        if repo != cfg.fork:
            continue
        for pr in rd.get('pullRequests', []):
            if not cfg.links.search(pr.get('body') or ''):
                continue
            login = (pr.get('author') or {}).get('login') or 'ghost'
            last = pr.get('lastCommitDate')
            url = pr.get('url') or f'https://github.com/{repo}/pull/{pr["number"]}'
            body = {'login': login, 'date': when(pr), 'url': url, 'body': pr.get('body') or ''}
            threads[f'{repo}#{pr["number"]}'] = {
                'key': f'{repo}#{pr["number"]}', 'role': 'pr', 'url': url, 'login': login,
                'last_commit': parse_time(last) if last else None, 'draft': bool(pr.get('isDraft')),
                'comments': [body] + [comment_of(c, url) for c in pr.get('comments', [])]}
    return threads


def issue_url(repo, n):
    return f'https://github.com/{repo}/issues/{n}'


def parse_events(threads, fields):
    """All claim, release, progress and ping actions, the names that matched no open field, and open
    fields named on a claim line after its name list (not counted)."""
    events, unmatched, mentions = [], [], []
    for th in threads.values():
        for c in th['comments']:
            body_mentions = [m.group(1).rstrip('-') for m in MENTION.finditer('\n'.join(visible_lines(c['body'])))]
            for verb, rest in parse_lines(c['body']):
                kind = {'Claiming': 'claim', 'Releasing': 'release', 'Progress': 'progress', 'Ping': 'ping'}[verb]
                if kind == 'ping' and kind_of(c['login']) != 'project':
                    continue
                e = {'kind': kind, 'login': c['login'], 'date': c['date'], 'url': c['url'],
                     'thread': th['key'], 'thread_url': th['url'], 'fields': [], 'packet': '',
                     'blocker': '', 'for': []}
                if kind == 'ping':
                    e['for'] = body_mentions
                elif kind == 'release' and kind_of(c['login']) == 'project':
                    e['for'] = [m.group(1).rstrip('-') for m in MENTION.finditer(rest.partition(':')[0])]
                m = READING.match(rest)
                if m:
                    e['packet'] = m.group(1)
                    if kind == 'release' and ':' in rest:
                        e['blocker'] = rest.split(':', 1)[1].strip()
                    events.append(e)
                    continue
                tail = ''
                if kind == 'claim':
                    names, tail = claim_parts(rest, fields)
                elif kind == 'ping':
                    names = rest
                else:
                    names, _, blocker = LEAD_LABEL.sub('', rest, count=1).partition(':')
                    e['blocker'] = blocker.strip() if kind == 'release' else ''
                found, bad = names_in(names, fields)
                e['fields'] = found
                for name, why in bad:
                    unmatched.append({'name': name, 'reason': why, 'url': c['url'], 'login': c['login']})
                if kind == 'claim' and not found and not bad:
                    unmatched.append({'name': 'Claiming ' + rest[:60], 'reason': 'claim line names no open field',
                                      'url': c['url'], 'login': c['login']})
                if tail:
                    later, _ = names_in(tail, fields)
                    for f in later:
                        if f not in found:
                            mentions.append({'field': f, 'url': c['url'], 'login': c['login']})
                if found:
                    events.append(e)
    events.sort(key=lambda e: e['date'])
    return events, unmatched, mentions


def subjects_of(e):
    return ['reading ' + e['packet']] if e['packet'] else e['fields']


def compute_holds(events):
    """(subject, holder key) -> hold state; subject is a field or 'reading R<n>'. The last action wins.

    A Releasing line by the project account that names @login releases that holder's claim instead of the
    project's own. A release whose claim is not in the fetch (a branch-held project row, or a claim in a pull
    request that has closed) is kept with claim None; plan() releases a row on it only with project_claims.
    """
    st = {}
    for e in events:
        if e['kind'] in ('progress', 'ping'):
            continue
        for s in subjects_of(e):
            if e['kind'] == 'claim':
                k = (s, holder_key(e['login']))
                urls = (st.get(k) or {}).get('urls', set()) | {e['url']}
                st[k] = {'subject': s, 'login': e['login'], 'active': True, 'claim': e, 'release': None,
                         'urls': urls}
                continue
            for login in e['for'] or [e['login']]:
                k = holder_key(login)
                cur = st.get((s, k))
                if cur is None:
                    cur = {'subject': s, 'login': login, 'claim': None}
                cur.update(active=False, release=e)
                st[(s, k)] = cur
    return st


def active_by_holder(st):
    """(field, holder key) -> the active hold (field holds only)."""
    return {k: h for k, h in st.items() if h['active'] and not k[0].startswith('reading ')}


# ---- the lapse policy ----------------------------------------------------------------------------------

def lapse(st, events, threads, now, cfg=None):
    """(action, subject, holder key, hold, thread url, last activity, ping date) under the lapse policy.

    action is 'ping', 'release' or 'project-stale'. A ping is a project comment on the claim thread (or the
    claims issue) with the line `Ping (claim lapse): <field>` that mentions the holder, posted at least
    PING_DAYS after the holder's last activity. A claim is released RELEASE_DAYS after such a ping when the
    holder has not been active since.
    """
    cfg = cfg or Config()
    out = []
    for (s, k), h in sorted(st.items()):
        if not h['active']:
            continue
        claim = h['claim']
        th = threads.get(claim['thread'], {'comments': [], 'url': claim['thread_url']})
        dates = [claim['date']]
        dates += [c['date'] for c in th['comments'] if holder_key(c['login']) == k]
        dates += [e['date'] for e in events
                  if e['kind'] == 'progress' and holder_key(e['login']) == k and s in subjects_of(e)]
        for t in threads.values():   # commits and comments on the holder's pull requests that claim it
            if t['role'] != 'pr' or holder_key(t.get('login')) != k:
                continue
            if any(e['thread'] == t['key'] and e['kind'] == 'claim' and s in subjects_of(e) for e in events):
                if t.get('last_commit'):
                    dates.append(t['last_commit'])
                dates += [c['date'] for c in t['comments'] if holder_key(c['login']) == k]
        last = max(dates)
        if k == PROJECT_HOLDER:
            if now - last >= PING_DELTA:
                out.append(('project-stale', s, k, h, th['url'], last, None))
            continue
        pings = [e['date'] for e in events
                 if e['kind'] == 'ping' and s in subjects_of(e) and e['thread'] in (claim['thread'], cfg.claims_key)
                 and k in {key_of(x) for x in e['for']} and e['date'] - last >= PING_DELTA]
        if pings:
            if now - min(pings) >= RELEASE_DELTA:
                out.append(('release', s, k, h, th['url'], last, min(pings)))
        elif now - last >= PING_DELTA:
            out.append(('ping', s, k, h, th['url'], last, None))
    return out


def sweep(st, events, threads, now, cfg=None):
    """Print the ping and release queue."""
    rows = lapse(st, events, threads, now, cfg)
    print('action\tfield\tholder\tthread\tlast_activity')
    for a, s, k, h, url, last, _ in rows:
        print('\t'.join([a, s, holder_name(h['login']), url, last.strftime('%Y-%m-%d')]))
    return rows


# ---- claims.tsv ----------------------------------------------------------------------------------------

BRANCH_URL = re.compile(r'^https://github\.com/([^/]+/[^/]+)/tree/(.+)$')
PR_URL = re.compile(r'^https://github\.com/([^/]+/[^/]+)/pull/(\d+)')
COMMENT_URL = re.compile(r'^https://github\.com/([^/]+/[^/]+)/(?:issues|pull)/(\d+)#issuecomment-')


def url_state(url, data, threads):
    """'valid', 'gone', 'unbacked' or 'unverified' for a claim_url that no parsed claim backs."""
    repos = data.get('repos', {})
    m = BRANCH_URL.match(url)
    if m:
        branches = repos.get(m.group(1), {}).get('branches')
        if branches is None:
            return 'unverified'
        return 'valid' if m.group(2) in branches else 'gone'
    m = PR_URL.match(url)
    if m and '#issuecomment' not in url:
        prs = repos.get(m.group(1), {}).get('pullRequests')
        if prs is None:
            return 'unverified'
        return 'valid' if any(p['number'] == int(m.group(2)) for p in prs) else 'gone'
    m = COMMENT_URL.match(url)
    if m and f'{m.group(1)}#{m.group(2)}' in threads:
        return 'unbacked'   # the thread was read and has no parsed active claim by this holder
    return 'unverified'


def new_row(header, f, h, hold, status):
    c = h['claim']
    r = {k: '' for k in header}
    r.update(field=f, task='', status=status, since=c['date'].strftime('%Y-%m-%d'), issue=c['thread'],
             holder_kind=kind_of(h['login']), public_holder=holder_name(h['login']), claim_url=c['url'],
             hold=hold)
    return r


def public_text(text):
    """Free text from a comment, fit for a claims.tsv cell: HTML comments and tags removed, absolute paths
    replaced by [path], whitespace collapsed, leading quote characters dropped, at most STATUS_MAX characters."""
    def path(m):
        tail = m.group(0)[len(m.group(0).rstrip(PATH_TAIL)):]
        return '[path]' + tail
    text = ABS_PATH.sub(path, TAG.sub(' ', text or ''))
    text = ' '.join('[path]' if LOCAL_PATH.search(t) else t for t in text.split()).lstrip(QUOTES + ' ')
    return text if len(text) <= STATUS_MAX else text[:STATUS_MAX - 3].rstrip() + '...'


def release_status(h, lapsed):
    if lapsed is not None:
        return f'lapsed: no reply within {RELEASE_DAYS} days of the ping of {lapsed.strftime("%Y-%m-%d")}'
    return public_text((h['release'] or {}).get('blocker')) or 'released'


def release_since(h, since):
    """h if it is a released hold whose Releasing line is dated on or after since (a row's YYYY-MM-DD), else None.

    Its claim need not be in the fetch. The date check keeps an older release from undoing a newer hold.
    """
    if h and not h['active'] and h['release'] and h['release']['date'].strftime('%Y-%m-%d') >= (since or ''):
        return h
    return None


def plan(header, rows, st, data, threads, fields, lapsed=None, project_claims=False, credited=frozenset()):
    """The new header and rows of claims.tsv, plus what changed and what the integrator should look at.

    lapsed maps (field, holder key) to the ping date for claims the lapse rule releases.
    project_claims: the mode of the claims-sync workflow, the only writer of claims.tsv. It also writes project rows
    from the project's own public claim and release lines (project rows without such lines are still left alone),
    and it
    - drops rows whose field is no longer open (a fold discharged it);
    - lets a claim take a released row of any holder, and an outside or maintainer claim take a project interest row;
    - releases a held row on a Releasing line dated on or after the row's since, even when the claim it releases
      is not in the fetch;
    - writes at most one held row for an outside login not in credited (casefolded logins with a row in
      credits.tsv): its earliest claim (by date, then field name), and reports the others.
    """
    lapsed = lapsed or {}
    header = list(header) + [c for c in NEW_COLUMNS if c not in header]
    active = active_by_holder(st)
    released = {k: h for k, h in st.items()
                if not h['active'] and h['claim'] and h['release'] and not k[0].startswith('reading ')}
    out, changes, notes, matched, removed, deferred = [], [], [], set(), [], {}

    def snap(r):
        return (r.get('hold') or '', r.get('claim_url') or '', r.get('public_holder') or '', r.get('status') or '')

    def capped(k):
        """True if the one-claim rule allows holder key k one held row."""
        return project_claims and k != PROJECT_HOLDER and kind_of(k) == 'outside' and k not in credited

    def hold_row(r, h):
        """Mark r held on its own holder's active claim h."""
        cur = r.get('claim_url') or ''
        keep = cur and '#issuecomment' not in cur and url_state(cur, data, threads) not in ('gone', 'unbacked')
        if r['hold'] != 'held':
            r.update(status='claimed', since=h['claim']['date'].strftime('%Y-%m-%d'), issue=h['claim']['thread'])
        r.update(hold='held', claim_url=cur if keep else h['claim']['url'], public_holder=h['login'])

    for r in rows:
        if project_claims and r['field'] not in fields.open_set:
            removed.append(r)
            continue
        r = dict(r)
        f = r['field']
        ph = r.get('public_holder') or PROJECT_HOLDER
        r['public_holder'] = ph
        r['holder_kind'] = r.get('holder_kind') or holder_kind(ph)
        k = PROJECT_HOLDER if r['holder_kind'] == 'project' else key_of(ph)
        matched.add((f, k))
        h = active.get((f, k))
        if not r.get('hold'):   # a row from before the hold column: start from the evidence
            if h and not r.get('claim_url'):
                r['claim_url'] = h['claim']['url']
            r['hold'] = ('held' if r.get('claim_url') else
                         'interest' if r['holder_kind'] == 'project' else 'released')
        cur = r.get('claim_url') or ''
        before = snap(r)
        # the release of a held row with no active claim; with project_claims, its claim need not be in the fetch
        rel = (release_since(st.get((f, k)), r.get('since')) if project_claims and not h and r['hold'] == 'held'
               else released.get((f, k)))
        if r['holder_kind'] == 'project' and project_claims and h and r['hold'] != 'held':
            r.update(hold='held', claim_url=h['claim']['url'], status='claimed',
                     since=h['claim']['date'].strftime('%Y-%m-%d'), issue=h['claim']['thread'])
            changes.append((f, r['public_holder'], before, snap(r)))
            out.append(r)
            continue
        if r['holder_kind'] == 'project' and project_claims and not h and r['hold'] == 'held' and rel:
            r.update(hold='released', status=release_status(rel, None))
            changes.append((f, r['public_holder'], before, snap(r)))
            out.append(r)
            continue
        if r['holder_kind'] == 'project':
            # the integrator manages project rows: report, never change
            if h and r['hold'] != 'held':
                notes.append(f'{f}: project row is {r["hold"]}, but a project claim backs it: {h["claim"]["url"]}')
            elif not h and r['hold'] == 'held':
                state = url_state(cur, data, threads)
                if rel:
                    notes.append(f'{f}: held project row, but the project released it: {rel["release"]["url"]}')
                elif state == 'gone':
                    notes.append(f'{f}: held project row, but its branch or pull request is gone: {cur}')
                elif state == 'unbacked':
                    notes.append(f'{f}: held project row; no parsed claim on that thread backs {cur}')
            elif h and COMMENT_URL.match(cur) and cur not in h.get('urls', set()):
                notes.append(f'{f}: held project row cites {cur}; the newest project claim is {h["claim"]["url"]}')
            out.append(r)
            continue
        if h and (f, k) in lapsed:
            r.update(hold='released', status=release_status(h, lapsed[(f, k)]), public_holder=h['login'])
        elif h and r['hold'] != 'held' and capped(k):
            deferred[(f, k)] = r   # claimed again: the one-claim rule decides below, in claim order
        elif h:
            hold_row(r, h)
        elif rel and r['hold'] == 'held':
            # a release whose claim is not in the fetch keeps the row's login (a mention may differ in case)
            r.update(hold='released', status=release_status(rel, None),
                     public_holder=rel['login'] if rel['claim'] else ph)
        elif r['hold'] == 'held':
            state = url_state(cur, data, threads)
            if state in ('gone', 'unbacked', 'unverified'):
                notes.append(f'{f}: kept held by {ph}; no parsed claim backs it ({state}): {cur}')
        if snap(r) != before:
            changes.append((f, r['public_holder'], before, snap(r)))
        out.append(r)

    by_field = {}
    for r in out:
        by_field.setdefault(r['field'], r)
    holders = {key_of(r['public_holder']) for r in out if r['hold'] == 'held' and r['holder_kind'] != 'project'}

    def over(f, h):
        notes.append(f'{f}: claimed by {h["login"]} ({h["claim"]["url"]}), over the one-claim rule (one held row '
                     'until a first contribution is in credits.tsv); not written')

    def taken(f, h, r):
        notes.append(f'{f}: claimed by {h["login"]} ({h["claim"]["url"]}), but claims.tsv has a '
                     f'{r["hold"]} row for {r["public_holder"]}; left for the integrator')

    adds = []
    for (f, k), h in sorted(active.items(), key=lambda kv: (kv[1]['claim']['date'], kv[0])):
        if (f, k) in deferred:   # the holder's own released row, claimed again
            r = deferred[(f, k)]
            if r['hold'] == 'held':   # an earlier claim in this loop took it
                taken(f, h, r)
            elif k in holders:
                over(f, h)
            else:
                before = snap(r)
                hold_row(r, h)
                changes.append((f, r['public_holder'], before, snap(r)))
                holders.add(k)
            continue
        if (f, k) in matched or f not in fields.open_set:
            continue
        r = by_field.get(f)
        hold, status = ('released', release_status(h, lapsed[(f, k)])) if (f, k) in lapsed else ('held', 'claimed')
        if k == PROJECT_HOLDER and not project_claims:
            if r is None:
                notes.append(f'{f}: project claim with no claims.tsv row (for the integrator): {h["claim"]["url"]}')
            continue
        # a row this claim takes: a released one (by default, only a non-project one), or a project interest row
        free = r is not None and (
            (r['hold'] == 'released' and (project_claims or r['holder_kind'] != 'project'))
            or (project_claims and r['holder_kind'] == 'project' and r['hold'] == 'interest'))
        if hold == 'held' and (r is None or free) and capped(k) and k in holders:
            over(f, h)
            continue
        if r is None:
            r = new_row(header, f, h, hold, status)
            adds.append(r)
            out.append(r)
            by_field[f] = r
        elif hold == 'released':
            continue
        elif free:
            before = snap(r)
            r.update(new_row(header, f, h, hold, status))
            changes.append((f, r['public_holder'], before, snap(r)))
        else:
            taken(f, h, r)
            continue
        if hold == 'held':
            holders.add(k)
    for (f, k), h in sorted(released.items(), key=lambda kv: (kv[1]['release']['date'], kv[0])):
        if (f, k) in matched or f not in fields.open_set or k == PROJECT_HOLDER or f in by_field:
            continue
        r = new_row(header, f, h, 'released', release_status(h, None))
        adds.append(r)
        out.append(r)
        by_field[f] = r
    not_open = sorted({r['field'] for r in out if r['field'] not in fields.open_set})
    return header, out, {'adds': adds, 'changes': changes, 'notes': notes, 'not_open': not_open, 'removed': removed}


# ---- the modes -----------------------------------------------------------------------------------------

def report(rows, info, st, unmatched, mentions, fields):
    w = print
    w('# claims.tsv after sync: held rows')
    w('field\tholder_kind\tpublic_holder\tclaim_url')
    held = [r for r in rows if r.get('hold') == 'held']
    for r in held:
        w('\t'.join([r['field'], r['holder_kind'], r['public_holder'], r['claim_url']]))
    w('')
    w('# rows to add')
    w('field\tholder_kind\tpublic_holder\thold\tsince\tissue\tclaim_url')
    for r in info['adds']:
        w('\t'.join([r['field'], r['holder_kind'], r['public_holder'], r['hold'], r['since'], r['issue'],
                     r['claim_url']]))
    w('')
    w('# rows that change')
    w('field\tpublic_holder\tbefore\tafter')
    for f, ph, old, new in info['changes']:
        w('\t'.join([f, ph, ' '.join(x for x in old if x) or '(none)', ' '.join(x for x in new if x)]))
    w('')
    if info.get('removed'):
        w('# rows removed (field no longer open)')
        w('field\tholder_kind\tpublic_holder\thold\tclaim_url')
        for r in info['removed']:
            w('\t'.join(r.get(c) or '' for c in ('field', 'holder_kind', 'public_holder', 'hold', 'claim_url')))
        w('')
    w('# unmatched names (map to no open field)')
    w('name\treason\tholder\turl')
    seen = set()
    for u in unmatched:
        if (u['name'], u['url']) in seen:
            continue
        seen.add((u['name'], u['url']))
        w('\t'.join([u['name'], u['reason'], holder_name(u['login']), u['url']]))
    extra = list(info['notes'])
    for m in mentions:
        extra.append(f'{m["field"]}: named on a claim line after its list of names, not counted: {m["url"]}')
    counts = {}
    for r in held:
        counts.setdefault(r['field'], []).append(r['public_holder'])
    for f, hs in sorted(counts.items()):
        if len(hs) > 1:
            extra.append(f'{f}: held by more than one holder: {", ".join(hs)}')
    per_person = {}
    for (s, k), h in st.items():
        if h['active'] and kind_of(h['login']) == 'outside' and not s.startswith('reading '):
            per_person.setdefault(h['login'], []).append(s)
    for login, fs in sorted(per_person.items()):
        if len(fs) > 1:
            extra.append(f'{login}: more than one open claim: {", ".join(sorted(fs))}')
    for (s, k), h in sorted(st.items()):
        if s.startswith('reading ') and h['active']:
            extra.append(f'{s}: held by {holder_name(h["login"])} ({h["claim"]["url"]})')
    for (s, k), h in sorted(st.items()):
        if not h['active'] and h['release'] and h['release']['blocker']:
            who, by = holder_name(h['login']), holder_name(h['release']['login'])
            extra.append(f'{s}: released ({who}) on {h["release"]["date"].strftime("%Y-%m-%d")}'
                         + (f' by {by}' if by != who else '') + f': {h["release"]["blocker"]}')
    for f in info['not_open']:
        extra.append(f'{f}: claims.tsv row names no open field')
    if extra:
        w('')
        w('# notes')
        for line in extra:
            w(line)


def check(names, st, rows, fields):
    problems = []
    for name in names:
        f, why = fields.resolve(name)
        if f is None:
            problems.append(f'{name}: {why}')
            continue
        for label in OFFER_LABELS:
            if label in fields.labels(f):
                problems.append(f'{f}: labelled {label} in kinds.tsv, offered to outside contributors first')
        for (s, k), h in sorted(st.items()):
            if s == f and h['active'] and kind_of(h['login']) != 'project':
                problems.append(f'{f}: held by {h["login"]} ({kind_of(h["login"])}): {h["claim"]["url"]}')
        for r in rows:
            ph = r.get('public_holder') or PROJECT_HOLDER
            if r['field'] == f and r.get('hold') == 'held' and holder_kind(ph) != 'project':
                msg = f'{f}: claims.tsv lists it held by {ph}'
                if r.get('claim_url'):
                    msg += f': {r["claim_url"]}'
                problems.append(msg)
    out = []
    for p in problems:
        if p not in out:
            out.append(p)
    for p in out:
        print('refused: ' + p)
    if not out:
        print('ok: ' + ', '.join(names) + ' free for a project brief')
    return 1 if out else 0


# ---- fetching (the only network path) ------------------------------------------------------------------

COMMENTS = 'pageInfo { hasNextPage endCursor } nodes { url createdAt lastEditedAt body author { login } }'
PRS = ('pageInfo { hasNextPage endCursor } nodes { number url isDraft body createdAt updatedAt lastEditedAt '
       'author { login } commits(last: 1) { nodes { commit { committedDate } } } '
       f'comments(first: 100) {{ {COMMENTS} }} }}')
BRANCHES = 'pageInfo { hasNextPage endCursor } nodes { name }'


def gh_graphql(query, **variables):
    """One read-only GraphQL call. gh exits non-zero when the response carries errors, so the output is
    parsed whenever there is any; errors are printed, and only missing data is fatal."""
    cmd = ['gh', 'api', 'graphql', '-f', 'query=' + query]
    for k, v in variables.items():
        cmd += ['-f', f'{k}={v}']
    proc = subprocess.run(cmd, capture_output=True, text=True)
    if proc.stderr.strip():
        print(proc.stderr.strip(), file=sys.stderr)
    try:
        res = json.loads(proc.stdout) if proc.stdout.strip() else {}
    except ValueError:
        res = {}
    if res.get('errors'):
        print('GitHub GraphQL errors: ' + json.dumps(res['errors']), file=sys.stderr)
    repo = (res.get('data') or {}).get('repository')
    if repo is None:
        raise SystemExit(f'no data from GitHub (gh exit status {proc.returncode})')
    return repo


def fetch_repo(repo, issues, with_prs):
    owner, name = repo.split('/')
    head = 'query($owner: String!, $name: String!%s) { repository(owner: $owner, name: $name) { %s } }'
    parts = [f'i{n}: issue(number: {n}) {{ number url comments(first: 100) {{ {COMMENTS} }} }}' for n in issues]
    if with_prs:
        parts.append(f'prs: pullRequests(states: OPEN, first: 100) {{ {PRS} }}')
        parts.append(f'refs: refs(refPrefix: "refs/heads/", first: 100) {{ {BRANCHES} }}')
    rd = gh_graphql(head % ('', ' '.join(parts)), owner=owner, name=name)

    def rest(conn, first_page, field):
        nodes, page = list(first_page['nodes']), first_page['pageInfo']
        while page['hasNextPage']:
            nxt = gh_graphql(head % (', $after: String!', conn.replace('AFTER', '$after')),
                             owner=owner, name=name, after=page['endCursor'])
            for key in field:
                nxt = nxt[key]
            nodes += nxt['nodes']
            page = nxt['pageInfo']
        return nodes

    out = {'issues': []}
    for n in issues:
        node = rd.get(f'i{n}')
        if node is None:
            print(f'{repo}#{n}: not found', file=sys.stderr)
            continue
        comments = rest(f'issue(number: {n}) {{ comments(first: 100, after: AFTER) {{ {COMMENTS} }} }}',
                        node['comments'], ['issue', 'comments'])
        out['issues'].append({'number': n, 'url': node['url'], 'comments': comments})
    if with_prs:
        prs = rest(f'pullRequests(states: OPEN, first: 100, after: AFTER) {{ {PRS} }}', rd['prs'],
                   ['pullRequests'])
        for p in prs:
            commits = p.pop('commits', {}).get('nodes') or []
            p['lastCommitDate'] = commits[0]['commit']['committedDate'] if commits else None
            p['comments'] = rest(f'pullRequest(number: {p["number"]}) {{ comments(first: 100, after: AFTER) '
                                 f'{{ {COMMENTS} }} }}', p['comments'], ['pullRequest', 'comments'])
        out['pullRequests'] = prs
        refs = rest(f'refs(refPrefix: "refs/heads/", first: 100, after: AFTER) {{ {BRANCHES} }}', rd['refs'],
                    ['refs'])
        out['branches'] = [r['name'] for r in refs]
    return out


def fetch(path, cfg=None):
    cfg = cfg or Config()
    repos = {repo: fetch_repo(repo, issues, repo == cfg.fork) for repo, issues in cfg.fetch_plan().items()}
    data = {'fetched_at': datetime.datetime.now(UTC).strftime('%Y-%m-%dT%H:%M:%SZ'), 'repos': repos}
    with open(path, 'w', encoding='utf-8') as fh:
        json.dump(data, fh, indent=1, ensure_ascii=False)
    return data


# ---- entry point ---------------------------------------------------------------------------------------

def main(argv=None):
    ap = argparse.ArgumentParser(description='Reconcile claims.tsv with the public claims on GitHub.')
    ap.add_argument('--fetch', metavar='OUT.json', help='fetch to OUT.json and stop (the only network path)')
    ap.add_argument('--from-json', metavar='FILE', help='read a file written by --fetch instead of fetching')
    mode = ap.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true', help='update claims.tsv in place')
    mode.add_argument('--check', nargs='+', metavar='FIELD', help='refuse fields not free for a project brief')
    mode.add_argument('--sweep', action='store_true', help='print the ping and release queue')
    ap.add_argument('--project-claims', action='store_true',
                    help="with --write: also write project rows from the project's public claim lines, drop rows "
                         'whose field is no longer open and apply the one-claim rule (the claims-sync workflow, '
                         'the only writer of claims.tsv)')
    ap.add_argument('--today', metavar='YYYY-MM-DD',
                    help='count the lapse policy from this date at 00:00 UTC (default: now)')
    ap.add_argument('--claims', default=os.path.join(DOCS, 'claims.tsv'))
    ap.add_argument('--kinds', default=os.path.join(DOCS, 'kinds.tsv'))
    ap.add_argument('--credits', default=os.path.join(DOCS, 'credits.tsv'),
                    help='with --project-claims: logins in its contributor column are exempt from the one-claim rule')
    ap.add_argument('--open', default=os.path.join(DOCS, 'open-statements.json'))
    ap.add_argument('--crosswalk', default=os.path.join(DOCS, 'frontier-crosswalk.tsv'))
    ap.add_argument('--issues', default=os.path.join(DOCS, 'issues.json'),
                    help='the claim, statement-checks and packet issues (defaults apply if it is missing)')
    a = ap.parse_args(argv)

    cfg = Config.load(a.issues)
    if a.fetch:
        fetch(a.fetch, cfg)
        print(f'wrote {a.fetch}')
        return 0
    if a.from_json:
        with open(a.from_json, encoding='utf-8') as fh:
            data = json.load(fh)
    else:
        with tempfile.TemporaryDirectory() as tmp:
            data = fetch(os.path.join(tmp, 'claims.json'), cfg)

    fields = Fields(a.open, a.crosswalk, a.kinds)
    threads = load_threads(data, cfg)
    events, unmatched, mentions = parse_events(threads, fields)
    st = compute_holds(events)
    header, rows = read_tsv(a.claims)
    now = (datetime.datetime.strptime(a.today, '%Y-%m-%d').replace(tzinfo=UTC) if a.today
           else datetime.datetime.now(UTC))

    if a.check:
        return check(a.check, st, rows, fields)
    if a.sweep:
        sweep(st, events, threads, now, cfg)
        return 0
    lapsed = {(s, k): ping for a_, s, k, h, url, last, ping in lapse(st, events, threads, now, cfg)
              if a_ == 'release'}
    credited = set()
    if a.project_claims and os.path.exists(a.credits):
        credited = {key_of(r.get('contributor', '').strip().lstrip('@')) for r in read_tsv(a.credits)[1]}
    new_header, new_rows, info = plan(header, rows, st, data, threads, fields, lapsed,
                                      project_claims=a.project_claims, credited=credited)
    if a.write:
        write_tsv(a.claims, new_header, new_rows)
        print(f'wrote {a.claims}: {len(new_rows)} rows, {len(info["adds"])} added, '
              f'{len(info["changes"])} changed')
    report(new_rows, info, st, unmatched, mentions, fields)
    return 0


if __name__ == '__main__':
    sys.exit(main())
