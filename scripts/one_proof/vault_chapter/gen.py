"""Generate blueprint/roadmap/height-decomposition/ from docs/one-proof/open-statements.json,
docs/one-proof/kinds.tsv and chapter_text.py.

Usage, from the repository root after each fold: python3 -I scripts/one_proof/vault_chapter/gen.py

Keeps the article_id of every file it rewrites; a new file gets the ID autoform-bot would give it
(a hash of its path and content). The bundles are read from open-statements.json (every bundle but frozenTarget's), and the top
theorem is the one in ZInQKernel/OneProof/H/ that takes exactly those bundles. Refuses to run when the H fields of
open-statements.json differ from those in chapter_text.py or when the kinds do not add up.
"""
import csv, hashlib, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from chapter_text import GROUPS, LEAVES  # noqa: E402

vault = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else '.')
CH = os.path.join(vault, 'blueprint/roadmap/height-decomposition')
SRC = os.path.join(vault, 'blueprint/sources/height-decomposition-locators.md')

data = json.load(open(os.path.join(vault, 'docs/one-proof/open-statements.json')))
BUNDLES = sorted({h['bundle'] for h in data['hypotheses']} - {'frozenTarget'})
# The top theorem: the sixContactMin_of_open* whose binders are exactly the current bundles.
tops = []
hdir = os.path.join(vault, 'ZInQKernel/OneProof/H')
for name in os.listdir(hdir):
    if name.endswith('.lean'):
        for m in re.finditer(r'^theorem (sixContactMin_of_open\d+) ((?:\(\w+ : \w+\) ?)+):', open(os.path.join(hdir, name)).read(), re.M):
            if sorted(re.findall(r': (\w+)\)', m.group(2))) == BUNDLES:
                tops.append('HDec.HSyn.' + m.group(1))
assert len(tops) == 1, tops
TOP_LEAN = tops[0]
hyps = [h for h in data['hypotheses'] if h['bundle'] in BUNDLES]
kinds = {r['field']: r for r in csv.DictReader(open(os.path.join(vault, 'docs/one-proof/kinds.tsv')), delimiter='\t')}
fields = [h['field'] for h in hyps]
lean = {h['field']: f"HDec.HSyn.{h['bundle']}.{h['field']}" for h in hyps}  # the Prop names have copies under scratch/, which the scanner reads
if set(fields) != set(LEAVES):
    sys.exit(f'fields differ: new {sorted(set(fields) - set(LEAVES))}, gone {sorted(set(LEAVES) - set(fields))}')
kind = {f: kinds[f]['kind'] for f in fields}
count = {k: sum(1 for f in fields if kind[f] == k) for k in ('published', 'consequence', 'composite', 'project glue')}
assert sum(count.values()) == len(fields), count
assert count['project glue'] == sum(1 for f in fields if LEAVES[f]['group'] is None), count
for f in fields:
    if kind[f] != 'published':
        assert kinds[f]['strict'] != 'LEAF', (f, kinds[f]['strict'])
    assert (kinds[f]['strict'] == 'LEAF') == (kind[f] == 'published'), f
assert len({LEAVES[f]['slug'] for f in fields}) == len(fields)
assert len({LEAVES[f]['anchor'] for f in fields}) == len(fields)

WORDS = {1: 'one', 2: 'two', 3: 'three', 4: 'four', 5: 'five', 6: 'six', 7: 'seven', 8: 'eight', 9: 'nine',
         10: 'ten', 11: 'eleven', 12: 'twelve', 34: 'thirty-four', 44: 'forty-four', 45: 'forty-five'}


def w(n):
    return WORDS.get(n, str(n))


KIND_SENTENCE = {
    'published': 'It is a published statement: the printed theorem, or a direct instance of it that needs no argument.',
    'consequence': 'It is not printed in this form but follows from published theorems; reaching it from the print '
                   'takes further theorems, which are not proved here.',
    'composite': 'No single source prints it.',
    'project glue': "No published statement has this form; it is a step of the project's own argument.",
}

# Statement dependencies inside the chapter (an article whose statement uses another's objects).
DEPS = {
    'gagaMorphism': ['uniformizationLeafAll'],
    'picZeroAbVar': ['picRepresentableAbVar'],
    'phiAmpleIsogeny': ['picZeroAbVar'],
    'weilPairingMumford': ['picZeroAbVar', 'phiAmpleIsogeny'],
}


def slugify(heading):
    s = re.sub(r'[^\w\s-]', '', heading).strip().lower()
    return re.sub(r'[\s]+', '-', s)


def old_id(path):
    if not os.path.exists(path):
        return None
    m = re.search(r'^article_id: (af_[0-9a-f]{24})$', open(path).read(), re.M)
    return m.group(1) if m else None


def front(path, **kv):
    aid = old_id(path)
    lines = ['---'] + ([f'article_id: {aid}'] if aid else []) + [f'{k}: {v}' for k, v in kv.items()] + ['---', '']
    return '\n'.join(lines)


def _tokens(line):
    """Split at spaces outside $...$ math, [link text] and the (url) right after it."""
    out, cur, math, br, url, prev = [], '', False, 0, False, ''
    for ch in line:
        if ch == '$' and not url:
            math = not math
        elif not math:
            if ch == '[':
                br += 1
            elif ch == ']':
                br = max(0, br - 1)
            elif ch == '(' and prev == ']' and br == 0:
                url = True
            elif ch == ')' and url:
                url = False
        if ch == ' ' and not math and br == 0 and not url:
            if cur:
                out.append(cur)
            cur = ''
        else:
            cur += ch
        prev = ch
    if cur:
        out.append(cur)
    return out


def wrap(line, width=100):
    lines, cur = [], ''
    for t in _tokens(line):
        if cur and len(cur) + 1 + len(t) > width:
            lines.append(cur)
            cur = t
        else:
            cur = f'{cur} {t}' if cur else t
    if cur:
        lines.append(cur)
    return '\n'.join(lines)


def para(text):
    """Rewrap prose at 100 columns; display-math lines ($$...) stay as they are."""
    out, buf = [], []
    for raw in text.strip().split('\n'):
        ln = raw.strip()
        if ln.startswith('$$') or ln.endswith('$$') or ln.startswith('\\qquad'):
            if buf:
                out.append(wrap(' '.join(buf)))
                buf = []
            out.append(ln)
        else:
            buf.append(ln)
    if buf:
        out.append(wrap(' '.join(buf)))
    return '\n'.join(out)


def path_of(f):
    g = LEAVES[f]['group']
    return os.path.join(CH, g, LEAVES[f]['slug'] + '.md') if g else os.path.join(CH, LEAVES[f]['slug'] + '.md')


def rel(f, frm):
    return os.path.relpath(path_of(f), os.path.dirname(frm))


written = []


ROADMAP = os.path.join(vault, 'blueprint/roadmap')


def new_id(path, text):
    """autoform-bot's _proposed_id (article_identity.py): path ID and the source's SHA-256."""
    rel_path = os.path.relpath(path, ROADMAP)
    path_id = os.path.dirname(rel_path) if os.path.basename(rel_path) == 'README.md' else rel_path[:-3]
    digest = hashlib.sha256(b'autoform-article-id/v1\0')
    digest.update(len(path_id.encode()).to_bytes(8, 'big'))
    digest.update(path_id.encode())
    digest.update(hashlib.sha256(text.encode()).hexdigest().encode('ascii'))
    return f'af_{digest.hexdigest()[:24]}'


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    if path.startswith(ROADMAP) and not re.search(r'^article_id: ', text, re.M):
        text = text.replace('---\n', f'---\narticle_id: {new_id(path, text)}\n', 1)
    with open(path, 'w') as fh:
        fh.write(text.rstrip('\n') + '\n')
    written.append(path)


group_fields = {g['dir']: [f for f in fields if LEAVES[f]['group'] == g['dir']] for g in GROUPS}
groups = [g for g in GROUPS if group_fields[g['dir']]]

# ---- leaf articles ----
for f in fields:
    L = LEAVES[f]
    p = path_of(f)
    origin = 'bridged' if kind[f] == 'project glue' else 'cited'
    body = [front(p, declaration='def', origin=origin, statement='formalized', lean=lean[f]), f"# {L['title']}", '',
            para(L['statement']), '']
    tail = KIND_SENTENCE[kind[f]]
    if L['caveat'].strip():
        tail += ' ' + L['caveat'].strip()
    tail += ' It is a hypothesis, not proved here.'
    body += [para(tail), '']
    body += ['## Depends on', '']
    body += ([f"- [{LEAVES[d]['title']}]({rel(d, p)})" for d in DEPS[f]] if f in DEPS else ['None.']) + ['']
    src_rel = os.path.relpath(SRC, os.path.dirname(p))
    body += ['## Sources', '', f"- [{L['anchor']}]({src_rel}#{slugify(L['anchor'])})"]
    write(p, '\n'.join(body))

# ---- group containers ----
for g in groups:
    p = os.path.join(CH, g['dir'], 'README.md')
    fs = group_fields[g['dir']]
    ks = [kind[f] for f in fs]
    PHRASE = {'published': ('is a published statement', 'are published statements'),
              'consequence': ('is a consequence of published theorems', 'are consequences of published theorems'),
              'composite': ('combines several published theorems', 'combine several published theorems')}
    present = [(k, ks.count(k)) for k in PHRASE if ks.count(k)]
    body = [front(p), f"# {g['title']}", '', para(g['intro']), '']
    if len(fs) == 1:
        body += ['It is not proved here.', '']
    elif len(present) == 1:
        body += [para(f"All {w(len(fs))} {PHRASE[present[0][0]][1]}; none is proved here."), '']
    else:
        parts = [f"{w(n)} {PHRASE[k][n > 1]}" for k, n in present]
        body += [para(f"Of these {w(len(fs))} statements, {', '.join(parts[:-1])} and {parts[-1]}; none is proved here."), '']
    body += [f"- [{LEAVES[f]['title']}]({LEAVES[f]['slug']}.md)" for f in fs]
    write(p, '\n'.join(body))

# ---- top theorem ----
glue = [f for f in fields if LEAVES[f]['group'] is None]
assert len(glue) <= 1, glue
nlit = len(fields) - len(glue)
top = os.path.join(CH, 'minimal-height-from-leaves.md')
glue_links = ', '.join(f"[{LEAVES[f]['title'].lower()}]({LEAVES[f]['slug']}.md)" for f in glue)
group_links = ', '.join(f"[{g['title'][0].lower() + g['title'][1:] if not g['title'].startswith(('Shimura', 'Néron', 'Faltings', 'Galois')) else g['title']}]({g['dir']}/README.md)" for g in groups)
body = [front(top, declaration='theorem', origin='bridged', statement='formalized', proof='formalized', lean=TOP_LEAN),
        f'# The minimal height hypothesis from {w(len(fields))} statements', '',
        para(f"""
The [minimal height hypothesis](../main/six-contact-min.md) follows from the {w(len(fields))} statements
of this chapter taken together: {w(nlit) + ' statements' if glue else 'theorems'} from the literature, grouped by
the theory they come from ({group_links}){f", and one step of the project's own argument, {glue_links}" if glue else ''}.
Of the {w(nlit)} statements from the literature, {w(count['published'])} are published statements, some of
them specialized or weakened; {w(count['consequence'])} are consequences of published theorems, which take
further theorems to reach from the print; and {w(count['composite'])} combine several published theorems.
None of the {w(len(fields))} is proved here.
"""), '',
        para(f"""
The proof follows the manuscript's proof of its Theorem 4.1 at the one instance the main theorem uses,
which the project has split into named steps, each proved from these statements and the steps before
it. Among them are the existence of an unramified vertical prime above each prime $p>324$ in the Hecke
cover, {'from the local inertia statement and the moduli description of the Shimura curves' if glue else "along the steps of the project's Lemma NV"}; the
inequalities between heights, from the analytic uniformization, the existence of Néron models, the bounds
of the section on heights and the results on semistable reduction and Néron models;
the Galois representation of a newform as a subrepresentation of the Tate module of $J_1(N)$, with its
semisimplicity and its conductor; and the last stretch, from the level bound, the theta point and the
height inequalities to the minimal height hypothesis.
"""), '',
        '## Depends on', '', '- [The minimal height hypothesis](../main/six-contact-min.md)', '',
        '## Proof depends on', '']
body += [f"- [{LEAVES[f]['title']}]({rel(f, top)})" for f in fields]
body += ['', '## Sources', '', f"- [The decomposition](../../sources/height-decomposition-locators.md#the-decomposition)"]
write(top, '\n'.join(body))

# ---- chapter container ----
readme = os.path.join(CH, 'README.md')
body = [front(readme), '# The minimal height hypothesis from the literature', '',
        para(f"""
This chapter proves the [minimal height hypothesis](../main/six-contact-min.md) from {w(len(fields))}
statements: {f'{w(nlit)} ' if glue else ''}theorems from the literature, some of them specialized, weakened or
combined{", and one step of the project's own argument" if glue else ''}. The manuscript's route to the hypothesis uses
twenty-three research-level theorems, thirty-five textbook theorems and twenty glue steps; the project
has split these into smaller statements, proved many of them, and replaced others by published
statements from which it derives them. What remains is listed here, grouped by the theory each statement
comes from; the groups follow the project's own classification, and their boundaries are a matter of
convenience.
"""), '',
        para(f"""
Of the {w(nlit)} statements from the literature, {w(count['published'])} are published statements: the
printed theorem, or a direct instance of it that needs no argument. {w(count['consequence']).capitalize()}
are consequences of published theorems, which take further theorems to reach from the print, and
{w(count['composite'])} combine several published theorems.{f' The remaining statement, {glue_links}, has no published form.' if glue else ''} None of the {w(len(fields))} is proved here, and every step from
them to the minimal height hypothesis is.
"""), '',
        '## The theorem', '',
        f'- [The minimal height hypothesis from {w(len(fields))} statements](minimal-height-from-leaves.md)', '']
if glue:
    body += ["## The project's step", ''] + [f"- [{LEAVES[f]['title']}]({LEAVES[f]['slug']}.md)" for f in glue] + ['']
body += ['## The statements from the literature', '']
body += [f"- [{g['title']}]({g['dir']}/README.md)" for g in groups]
write(readme, '\n'.join(body))

# ---- sources page ----
body = ['# Locators for the decomposition of the minimal height hypothesis', '',
        para("""
The decomposition follows the project-authored note `docs/research/h-decomposition.md` and the fold notes
under `docs/research/` that changed it (section 3 of `docs/research/leaf-fold9.md` groups the statements
by the theory they come from), and the list `docs/one-proof/OPEN.md`, generated from the build, which
gives each statement's source, its kind and who is working on it. These are notes written for this
project, not published sources. The locators below are those of `docs/one-proof/OPEN.md`. An audit of
the citations against the primary sources by AI agents with web access (`docs/research/locators.md`)
read some of them, as marked; the others are unverified.
"""), '', '## The decomposition', '',
        para(f"""
The minimal height hypothesis is proved from the {w(len(fields))} statements of the chapter in the
project's assembly of the proof of the manuscript's Theorem 4.1; the trust assessment of that proof is
the project-authored note `docs/research/h-trust.md`.
"""), '']
for f in fields:
    L = LEAVES[f]
    body += [f"## {L['anchor']}", '', para(L['src']), '']
write(SRC, '\n'.join(body))

# ---- the coverage row ----
cov = os.path.join(vault, 'blueprint/coverage/README.md')
kinds_text = (f"{w(count['published'])} published statements, {w(count['consequence'])} consequences of published "
              f"theorems and {w(count['composite'])} that combine several published theorems")
row = ('| Section 4 replaced: the minimal height hypothesis from statements of the literature (project notes '
       'h-decomposition, leaf-fold9 §3; docs/one-proof/OPEN.md) | `DECOMPOSED` | The [height-decomposition chapter]'
       '(../roadmap/height-decomposition/README.md) proves [the minimal height hypothesis from '
       f'{w(len(fields))} statements](../roadmap/height-decomposition/minimal-height-from-leaves.md): '
       + (f"{w(nlit)} from the literature ({kinds_text}), grouped by the theory they come from, and "
          f"[one step of the project's own argument](../roadmap/height-decomposition/{LEAVES[glue[0]]['slug']}.md)"
          if glue else f"all from the literature ({kinds_text}), grouped by the theory they come from")
       + f'. None of the {w(len(fields))} is proved here. |')
lines = open(cov).read().split('\n')
hits = [i for i, ln in enumerate(lines) if ln.startswith('| Section 4 replaced: the minimal height hypothesis')]
if hits:
    lines[hits[0]] = row
else:
    lines.insert(next(i for i, ln in enumerate(lines) if ln.startswith('| Section 4, last step:')), row)
open(cov, 'w').write('\n'.join(lines))

# ---- articles of statements gone since the last run ----
removed = []
for dirpath, _, files in os.walk(CH, topdown=False):
    for name in files:
        path = os.path.join(dirpath, name)
        if name.endswith('.md') and path not in written:
            os.remove(path)
            removed.append(os.path.relpath(path, vault))
    if not os.listdir(dirpath):
        os.rmdir(dirpath)
print(f'{len(written)} files; kinds {count}; removed {removed}')
