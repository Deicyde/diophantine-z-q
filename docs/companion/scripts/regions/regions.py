#!/usr/bin/env python3
"""Place the manuscript's items on the PDF by matching their words to the PDF's own text.

Adapted from tools/regions2.py.  Page hints come from 5-word anchors that occur once in
the TeX and once in the PDF, instead of an earlier regions file.  A numbered statement
starts at the row of its printed heading ("Theorem 1.1"); a numbered display is the block
of rows around its printed tag ("(3.1)") between the neighbouring prose.

For each passage (TeX line range), the prose words of the source are aligned with the
words of the PDF's text layer.  The first and last matched words give the first and last
typeset rows.  Box edges are put in the white space between rows, a row shared by two
neighbouring passages goes to both of them, identical extents are merged, and nested boxes
are drawn at different widths.

Usage: regions.py <tex> <pdf> <items.json> <workdir> <regions.json> <report.json>
"""
import difflib
import html
import json
import os
import re
import subprocess
import sys
import unicodedata

TEX, PDF, ITEMS, WORK, OUT, REPORT = sys.argv[1:7]
PAGE_W, PAGE_H = 612.0, 792.0
MID = 306.0
BODY_TOP, BODY_BOTTOM = 60.0, 738.0
DPI = 144
SCALE = DPI / 72.0


def blank_keep_newlines(m):
    return re.sub(r'[^\n]', ' ', m.group(0))


def detex(src):
    s = re.sub(r'(?<!\\)%[^\n]*', blank_keep_newlines, src)
    s = s.replace('\\$', '  ').replace('\\%', '  ').replace('\\&', '  ')
    envs = r'equation\*?|align\*?|gather\*?|multline\*?|eqnarray\*?|displaymath|alignat\*?|flalign\*?'
    s = re.sub(r'\\begin\{(' + envs + r')\}.*?\\end\{\1\}', blank_keep_newlines, s, flags=re.S)
    s = re.sub(r'\\\[.*?\\\]', blank_keep_newlines, s, flags=re.S)
    s = re.sub(r'\$\$.*?\$\$', blank_keep_newlines, s, flags=re.S)
    s = re.sub(r'\\\(.*?\\\)', blank_keep_newlines, s, flags=re.S)
    s = re.sub(r'\$[^$]*\$', blank_keep_newlines, s, flags=re.S)
    s = re.sub(r'\\(label|ref|eqref|cite|begin|end|input|include|bibitem|pageref|url|href)\*?(\[[^\]\n]*\])?\{[^}\n]*\}',
               blank_keep_newlines, s)
    s = re.sub(r'\\[a-zA-Z]+\*?', blank_keep_newlines, s)
    return s


def norm_token(w):
    w = unicodedata.normalize('NFKC', w).lower()
    return re.sub(r'[^a-z]', '', w)


src = open(TEX, encoding='utf-8').read()
src_lines = src.split('\n')
plain_lines = detex(src).split('\n')
TEX_TOK = []       # (token, line)
for n, line in enumerate(plain_lines, 1):
    for w in re.findall(r"[A-Za-z][A-Za-z']*", line):
        t = norm_token(w)
        if len(t) >= 2:
            TEX_TOK.append((t, n))

# a source line "has content" when it would put ink on the page
CONTENT = [False] * (len(src_lines) + 2)
for n, line in enumerate(src_lines, 1):
    l = re.sub(r'(?<!\\)%.*', '', line)
    l = re.sub(r'\\(begin|end|label)\*?(\[[^\]]*\])?\{[^}]*\}', '', l)
    l = l.replace('\\[', '').replace('\\]', '')
    CONTENT[n] = bool(re.search(r'[A-Za-z0-9]', l))


def content_count(lo, hi):
    """Number of content lines n with lo <= n <= hi."""
    return sum(1 for n in range(max(1, lo), min(len(src_lines), hi) + 1) if CONTENT[n])


# ---- the PDF: rows and words -------------------------------------------------
xml = subprocess.run(['pdftotext', '-bbox-layout', PDF, '-'], capture_output=True, text=True).stdout
PAGES = {}        # page -> {'rows': [[y0, y1], ...], 'tokens': [(tok, row, xMin)]}
page = 0
cur_lines = []
for raw in xml.split('\n'):
    m = re.search(r'<page ', raw)
    if m:
        page += 1
        cur_lines = []
        PAGES[page] = {'lines': cur_lines}
        continue
    m = re.search(r'<line xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)"', raw)
    if m:
        cur_lines.append({'y0': float(m.group(2)), 'y1': float(m.group(4)), 'words': []})
        continue
    m = re.search(r'<word xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)">(.*?)</word>', raw)
    if m and cur_lines:
        cur_lines[-1]['words'].append((float(m.group(1)), float(m.group(2)), float(m.group(4)), html.unescape(m.group(5)),
                                       float(m.group(3))))

for p, info in PAGES.items():
    lines = [l for l in info['lines'] if l['words']]
    lines.sort(key=lambda l: (l['y0'] + l['y1']) / 2)
    rows = []
    for l in lines:
        if rows:
            r = rows[-1]
            overlap = min(r['y1'], l['y1']) - max(r['y0'], l['y0'])
            if overlap > 0.6 * min(r['y1'] - r['y0'], l['y1'] - l['y0']):
                r['y0'] = min(r['y0'], l['y0'])
                r['y1'] = max(r['y1'], l['y1'])
                r['words'] += l['words']
                continue
        rows.append({'y0': l['y0'], 'y1': l['y1'], 'words': list(l['words'])})
    body = []
    for r in rows:
        text = ' '.join(w[3] for w in r['words']).strip()
        if r['y0'] > 700 and re.fullmatch(r'\d{1,3}', text):
            continue                      # the page number
        if r['y1'] < BODY_TOP or r['y0'] > BODY_BOTTOM:
            continue
        body.append(r)
    toks = []
    for i, r in enumerate(body):
        for x0, y0, y1, w, _ in sorted(r['words']):
            for piece in re.findall(r"[A-Za-zÀ-ɏﬀ-ﬆ][A-Za-zÀ-ɏﬀ-ﬆ']*", w):
                t = norm_token(piece)
                if len(t) >= 2:
                    toks.append((t, i, x0))
    info['rows'] = body
    info['tokens'] = toks

# ---- ink rows, to keep edges off the text ------------------------------------
INK = {}


def ink(p):
    if p not in INK:
        base = os.path.join(WORK, f'ink-{p}')
        subprocess.run(['pdftoppm', '-gray', '-r', str(DPI), '-f', str(p), '-l', str(p), PDF, base], check=True)
        path = next(os.path.join(WORK, f) for f in os.listdir(WORK) if f.startswith(f'ink-{p}-') and f.endswith('.pgm'))
        data = open(path, 'rb').read()
        os.remove(path)
        m = re.match(rb'P5\s+(\d+)\s+(\d+)\s+(\d+)\s', data)
        w, h = int(m.group(1)), int(m.group(2))
        px = data[m.end():]
        x0, x1 = int(58 * SCALE), int(554 * SCALE)
        INK[p] = [min(px[r * w + x0:r * w + x1]) < 170 for r in range(h)]
    return INK[p]


def on_ink(p, y):
    rows = ink(p)
    r = int(round(y * SCALE))
    return 0 <= r < len(rows) and rows[r]


def to_gap(p, y, reach=3.5):
    """The nearest y within `reach` points that lies on a blank pixel row."""
    if not on_ink(p, y):
        return y
    step = 1.0 / SCALE
    k = 1
    while k * step <= reach:
        for cand in (y - k * step, y + k * step):
            if not on_ink(p, cand):
                return cand
        k += 1
    return y


def sep_above(p, i):
    rows = PAGES[p]['rows']
    y = rows[i]['y0'] - 2.0 if i == 0 else (rows[i - 1]['y1'] + rows[i]['y0']) / 2
    return to_gap(p, y)


def sep_below(p, i):
    rows = PAGES[p]['rows']
    y = rows[i]['y1'] + 2.0 if i == len(rows) - 1 else (rows[i]['y1'] + rows[i + 1]['y0']) / 2
    return to_gap(p, y)


# ---- align one passage ---------------------------------------------------------
def first_tok_at_or_after(line):
    lo, hi = 0, len(TEX_TOK)
    while lo < hi:
        mid = (lo + hi) // 2
        if TEX_TOK[mid][1] < line:
            lo = mid + 1
        else:
            hi = mid
    return lo


NEIGHBOURS = {}   # span -> (row of the last matched word before it, row of the first after it)
SHARED = {}       # span -> the (page, row) it shares with the text before or after it


def place(a, b, pages_hint):
    p_lo = max(1, min(pages_hint) - 1)
    p_hi = min(len(PAGES), max(pages_hint) + 1)
    pdf = []         # (tok, page, row, x)
    for p in range(p_lo, p_hi + 1):
        pdf += [(t, p, r, x) for t, r, x in PAGES[p]['tokens']]
    i0 = first_tok_at_or_after(a - 30)
    i1 = first_tok_at_or_after(b + 31)
    tex = TEX_TOK[i0:i1]
    sm = difflib.SequenceMatcher(None, [t for t, _ in tex], [t[0] for t in pdf], autojunk=False)
    pairs = {}
    for blk in sm.get_matching_blocks():
        if blk.size >= 2 or (blk.size == 1 and len(tex[blk.a][0]) >= 7):
            for k in range(blk.size):
                pairs[blk.a + k] = blk.b + k
    idx = sorted(pairs)
    inside = [i for i in idx if a <= tex[i][1] <= b]
    before = [i for i in idx if tex[i][1] < a]
    after = [i for i in idx if tex[i][1] > b]
    u = pdf[pairs[before[-1]]] if before else None
    n = pdf[pairs[after[0]]] if after else None
    u_line = tex[before[-1]][1] if before else None
    n_line = tex[after[0]][1] if after else None

    def key(t):
        return (t[1], t[2])

    NEIGHBOURS[(a, b)] = (key(u) if u else None, key(n) if n else None)

    def step(pos, k):
        """Move k rows forward (k may be negative) from (page, row), across pages."""
        p, r = pos
        while k > 0:
            if r + 1 < len(PAGES[p]['rows']):
                r += 1
            elif p + 1 <= len(PAGES):
                p, r = p + 1, 0
            k -= 1
        while k < 0:
            if r > 0:
                r -= 1
            elif p > 1:
                p, r = p - 1, len(PAGES[p - 1]['rows']) - 1
            k += 1
        return (p, r)

    def rows_between(lo, hi):
        """Number of rows strictly between two (page, row) positions."""
        if lo >= hi:
            return 0
        count = 0
        pos = step(lo, 1)
        while pos < hi and count < 400:
            count += 1
            nxt = step(pos, 1)
            if nxt == pos:
                break
            pos = nxt
        return count

    how = 'words'
    if inside:
        s = pdf[pairs[inside[0]]]
        e = pdf[pairs[inside[-1]]]
        s_line, e_line = tex[inside[0]][1], tex[inside[-1]][1]
        start, end = key(s), key(e)
        # the start: a row the text before also occupies belongs to both
        if u is not None and key(u) == start:
            SHARED.setdefault((a, b), set()).add(start)
        elif u is not None:
            m = rows_between(key(u), start)
            c_out = content_count(u_line + 1, a - 1)
            c_in = content_count(a, s_line - 1)
            if m and c_in:
                keep_out = int(c_out * m / (c_in + c_out) + 0.5)
                start = step(key(u), 1 + keep_out)
        # the end: a row the text after also occupies belongs to both
        if n is not None and key(n) == end:
            SHARED.setdefault((a, b), set()).add(end)
        elif n is not None:
            m = rows_between(end, key(n))
            c_in = content_count(e_line + 1, b)
            c_out = content_count(b + 1, n_line - 1)
            if m and c_in:
                take = int(c_in * m / (c_in + c_out) + 0.5)
                end = step(end, take)
    elif u is not None and n is not None and rows_between(key(u), key(n)) > 0:
        how = 'between'
        m = rows_between(key(u), key(n))
        c_before = content_count(u_line + 1, a - 1)
        c_in = content_count(a, b)
        c_after = content_count(b + 1, n_line - 1)
        total = max(1, c_before + c_in + c_after)
        first = int(c_before * m / total + 0.5)
        last = max(first, int((c_before + c_in) * m / total + 0.5) - 1)
        start = step(key(u), 1 + first)
        end = step(key(u), 1 + min(last, m - 1))
    elif u is not None and n is not None:
        # a span with no word of its own between two matched neighbours on touching rows:
        # it sits on the row where the following text starts, or on the previous one
        how = 'neighbours'
        start = end = key(n) if n[3] >= MID or key(u) == key(n) else key(u)
    else:
        return None, 'unplaced'
    if end < start:
        end = start
    return (start, end), how


# ---- the driver ------------------------------------------------------------------
import hashlib
from collections import Counter

KIND_WORD = {'theorem': 'Theorem', 'proposition': 'Proposition', 'lemma': 'Lemma',
             'corollary': 'Corollary', 'definition': 'Definition', 'remark': 'Remark'}
NPAGES = len(PAGES)


def step_rows(pos, k):
    p, r = pos
    while k > 0:
        if r + 1 < len(PAGES[p]['rows']):
            r += 1
        elif p + 1 <= NPAGES:
            p, r = p + 1, 0
        k -= 1
    while k < 0:
        if r > 0:
            r -= 1
        elif p > 1:
            p, r = p - 1, len(PAGES[p - 1]['rows']) - 1
        k += 1
    return (p, r)


# page hints: 5-word sequences that occur exactly once in the TeX and once in the PDF
TT = [t for t, _ in TEX_TOK]
tex_grams = Counter(tuple(TT[i:i + 5]) for i in range(len(TT) - 4))
tex_pos = {}
for i in range(len(TT) - 4):
    g = tuple(TT[i:i + 5])
    if tex_grams[g] == 1:
        tex_pos[g] = TEX_TOK[i][1]
PT = [(t, p) for p in range(1, NPAGES + 1) for t, _, _ in PAGES[p]['tokens']]
pdf_grams = Counter(tuple(t for t, _ in PT[i:i + 5]) for i in range(len(PT) - 4))
anchors = []
for i in range(len(PT) - 4):
    g = tuple(t for t, _ in PT[i:i + 5])
    if pdf_grams[g] == 1 and g in tex_pos:
        anchors.append((tex_pos[g], PT[i][1]))
# longest chain increasing in both line and page order
import bisect
tails, tails_idx, prev = [], [], [-1] * len(anchors)
for k, (line, _) in enumerate(anchors):
    j = bisect.bisect_right(tails, line)
    if j == len(tails):
        tails.append(line)
        tails_idx.append(k)
    else:
        tails[j] = line
        tails_idx[j] = k
    prev[k] = tails_idx[j - 1] if j else -1
chain = []
k = tails_idx[-1]
while k >= 0:
    chain.append(anchors[k])
    k = prev[k]
chain.reverse()
CHAIN_LINES = [c[0] for c in chain]


def page_hint(a, b):
    i = bisect.bisect_right(CHAIN_LINES, a) - 1
    j = bisect.bisect_left(CHAIN_LINES, b)
    lo = chain[i][1] if i >= 0 else 1
    hi = chain[j][1] if j < len(chain) else NPAGES
    return [lo, hi]


def row_text(p, r):
    return [w[3] for w in sorted(PAGES[p]['rows'][r]['words'])]


def find_heading(kind, number, pages):
    """(page, row) of the row that starts with the printed heading of a statement."""
    want = [KIND_WORD[kind], number]
    hits = []
    for p in range(max(1, pages[0] - 1), min(NPAGES, pages[1] + 1) + 1):
        for r, row in enumerate(PAGES[p]['rows']):
            ws = sorted(row['words'])
            t = [unicodedata.normalize('NFKC', w[3]) for w in ws]
            if len(t) >= 2 and t[0] == want[0] and ws[0][0] < 80 and \
                    (t[1] == want[1] + '.' or (t[1] == want[1] and len(t) > 2 and t[2].startswith('('))):
                hits.append((p, r))
    return hits


def is_tag_word(w, number, row_words, gap):
    """A printed tag sits at the right margin, apart from the words before it."""
    if w[3] != f'({number})' or w[4] < 530:
        return False
    before = [v[4] for v in row_words if v[0] < w[0]]
    return not before or max(before) < w[0] - gap


TAG_ROWS = {}    # (page, row) -> number, for every printed display tag


def find_tag(number, pages, gap=10):
    hits = []
    for p in range(max(1, pages[0] - 1), min(NPAGES, pages[1] + 1) + 1):
        for r, row in enumerate(PAGES[p]['rows']):
            if any(is_tag_word(w, number, row['words'], gap) for w in row['words']):
                hits.append((p, r))
    if not hits and gap:
        return find_tag(number, pages, 0)    # a display as wide as the line: the tag is one space apart
    return hits


data = json.load(open(ITEMS, encoding='utf-8'))
items = data['items']
for x in items:
    if x['kind'] == 'equation':
        for h in find_tag(x['number'], page_hint(x['lines'][0][0], x['lines'][-1][1])):
            TAG_ROWS.setdefault(h, set()).add(x['number'])

TRIMMED = []
extents = {}       # id -> [(start, end)]
how = {}
unplaced = {}
anchor_rows = {}   # id -> (page, row) of the printed number
for x in items:
    exts, hows = [], []
    for a, b in x['lines']:
        hint = page_hint(a, b)
        res, hw = place(a, b, hint)
        if x['kind'] in KIND_WORD and (a, b) == tuple(x['lines'][0]):
            hits = find_heading(x['kind'], x['number'], hint)
            if len(hits) != 1:
                unplaced[x['id']] = f'printed heading found {len(hits)} times near pages {hint}'
                res = None
            else:
                anchor_rows[x['id']] = hits[0]
                if res is None or res[1] < hits[0]:
                    res = (hits[0], hits[0])
                res = (hits[0], max(res[1], hits[0]))
                hw += '+heading'
        if x['kind'] == 'equation':
            hits = find_tag(x['number'], hint)
            if len(hits) != 1:
                unplaced[x['id']] = f'printed tag found {len(hits)} times near pages {hint}'
                res = None
            else:
                t = hits[0]
                anchor_rows[x['id']] = t
                u, n = NEIGHBOURS.get((a, b), (None, None))
                lo, hi = (res if res else (t, t))
                lo, hi = min(lo, t), max(hi, t)
                if u is not None and u < t:
                    lo = max(lo, step_rows(u, 1))
                if n is not None and t < n:
                    hi = min(hi, step_rows(n, -1))
                # stop at rows holding another display's tag
                pos = t
                while pos > lo:
                    q = step_rows(pos, -1)
                    if q in TAG_ROWS and x['number'] not in TAG_ROWS[q]:
                        lo = step_rows(q, 1)
                        break
                    pos = q
                pos = t
                while pos < hi:
                    q = step_rows(pos, 1)
                    if q in TAG_ROWS and x['number'] not in TAG_ROWS[q]:
                        hi = step_rows(q, -1)
                        break
                    pos = q
                # a row joined to the block by ink (a fraction's numerator or denominator) belongs to it
                ulim = step_rows(u, 1) if u is not None and u < t else None
                nlim = step_rows(n, -1) if n is not None and t < n else None
                while lo[1] > 0 and on_ink(lo[0], sep_above(*lo)) and (ulim is None or lo > ulim):
                    lo = step_rows(lo, -1)
                while hi[1] < len(PAGES[hi[0]]['rows']) - 1 and on_ink(hi[0], sep_below(*hi)) and \
                        (nlim is None or hi < nlim):
                    hi = step_rows(hi, 1)
                # prose rows (starting at the left margin) at either end of the block are not the display
                def prose(pos):
                    ws = PAGES[pos[0]]['rows'][pos[1]]['words']
                    return pos != t and min(w[0] for w in ws) < 73.5
                while lo < t and prose(lo):
                    lo = step_rows(lo, 1)
                    TRIMMED.append(x['id'])
                while hi > t and prose(hi):
                    hi = step_rows(hi, -1)
                    TRIMMED.append(x['id'])
                res = (lo, hi)
                hw += '+tag'
        hows.append(hw)
        if res:
            exts.append(res)
    if x['id'] not in unplaced and not exts:
        unplaced[x['id']] = 'no word of its lines or of its neighbours matched the PDF'
    if x['id'] in unplaced:
        exts = []
    extents[x['id']] = exts
    how[x['id']] = hows

# ---- boxes: one per page of each extent -----------------------------------------
parts = {}
boxes = set()
for x in items:
    parts[x['id']] = []
    for (start, end) in extents[x['id']]:
        for p in range(start[0], end[0] + 1):
            rows = PAGES[p]['rows']
            if not rows:
                continue
            r0 = start[1] if p == start[0] else 0
            r1 = end[1] if p == end[0] else len(rows) - 1
            if (p, r0, r1) not in parts[x['id']]:
                parts[x['id']].append((p, r0, r1))
            boxes.add((p, r0, r1))
by_page = {}
for (p, r0, r1) in boxes:
    by_page.setdefault(p, []).append((r0, r1))
depth = {}
for p, ivs in by_page.items():
    ivs = sorted(set(ivs), key=lambda iv: (iv[1] - iv[0], iv))
    for iv in ivs:
        inner = [depth[(p,) + j] for j in ivs if j != iv and iv[0] <= j[0] and j[1] <= iv[1] and (p,) + j in depth]
        depth[(p,) + iv] = 1 + max(inner) if inner else 0

PX = {}


def page_pixels(p):
    if p not in PX:
        PX.clear()
        base = os.path.join(WORK, f'px-{p}')
        subprocess.run(['pdftoppm', '-gray', '-r', str(DPI), '-f', str(p), '-l', str(p), PDF, base], check=True)
        path = next(os.path.join(WORK, f) for f in os.listdir(WORK) if f.startswith(f'px-{p}-') and f.endswith('.pgm'))
        raw = open(path, 'rb').read()
        os.remove(path)
        m = re.match(rb'P5\s+(\d+)\s+(\d+)\s+(\d+)\s', raw)
        PX[p] = (int(m.group(1)), int(m.group(2)), raw[m.end():])
    return PX[p]


def column_on_ink(p, x, y0, y1):
    w, h, px = page_pixels(p)
    c = int(round(x * SCALE))
    return any(px[r * w + c] < 170 for r in range(max(0, int(y0 * SCALE)), min(h, int(y1 * SCALE) + 1)))


def row_on_ink(p, y, x0, x1):
    w, h, px = page_pixels(p)
    r = int(round(y * SCALE))
    return 0 <= r < h and min(px[r * w + int(x0 * SCALE):r * w + int(x1 * SCALE)]) < 170


rects = {}
edges_on_ink = []
for (p, r0, r1) in sorted(boxes):
    d = min(depth[(p, r0, r1)], 7)
    top = sep_above(p, r0)
    bot = sep_below(p, r1)
    x0 = 66.0 - 3.0 * d
    x1 = 546.0 + 3.0 * d
    bad = [e for e, hit in (('top', row_on_ink(p, top, x0, x1)), ('bottom', row_on_ink(p, bot, x0, x1)),
                            ('left', column_on_ink(p, x0, top, bot)), ('right', column_on_ink(p, x1, top, bot))) if hit]
    if bad:
        edges_on_ink.append([f'p{p:03d}-r{r0:03d}-{r1:03d}', bad])
    rects[(p, r0, r1)] = (x0, top, x1, bot)


def frac(r):
    x0, top, x1, bot = r
    return [round(x0 / PAGE_W, 6), round(top / PAGE_H, 6), round((x1 - x0) / PAGE_W, 6), round((bot - top) / PAGE_H, 6)]


# ---- check: a crop of every numbered item's rect holds its printed number ---------------
def crop_text(p, r):
    x0, top, x1, bot = r
    out = subprocess.run(['pdftotext', '-r', '72', '-f', str(p), '-l', str(p), '-x', str(int(x0)), '-y', str(int(top)),
                          '-W', str(int(x1 - x0 + 0.999)), '-H', str(int(bot - top + 0.999)), '-layout', PDF, '-'],
                         capture_output=True, text=True).stdout
    return unicodedata.normalize('NFKC', ' '.join(out.split()))


number_check = {}
for x in items:
    if x['kind'] == 'passage' or not parts[x['id']]:
        continue
    want = f"{KIND_WORD[x['kind']]} {x['number']}" if x['kind'] in KIND_WORD else f"({x['number']})"
    found = []
    for (p, r0, r1) in parts[x['id']]:
        t = crop_text(p, rects[(p, r0, r1)])
        if (re.search(re.escape(want) + r'(?![\d])', t)):
            found.append(p)
    number_check[x['id']] = found

# ---- overlaps -------------------------------------------------------------------------
lines_of = {x['id']: set(n for a, b in x['lines'] for n in range(a, b + 1)) for x in items}
shared_of = {x['id']: set().union(*[SHARED.get((a, b), set()) for a, b in x['lines']]) for x in items}
regs_by_page = {}
for x in items:
    for part in parts[x['id']]:
        regs_by_page.setdefault(part[0], []).append((x['id'], part))
overlaps, bad_overlaps = [], []
seen = set()
for p, regs in regs_by_page.items():
    for i in range(len(regs)):
        for j in range(i + 1, len(regs)):
            (ia, pa), (ib, pb) = regs[i], regs[j]
            if ia == ib:
                continue
            ra, rb = rects[pa], rects[pb]
            ov = min(ra[3], rb[3]) - max(ra[1], rb[1])
            if ov <= 0.01:
                continue
            la, lb = lines_of[ia], lines_of[ib]
            if la <= lb or lb <= la:
                why = 'nested'
            elif la & lb:
                why = 'shared lines'
            elif max(pa[1], pb[1]) == min(pa[2], pb[2]) and \
                    (p, pa[2] if pa[1] < pb[1] else pb[2]) in shared_of[ia] & shared_of[ib]:
                why = 'shared row'
            else:
                why = None
            key2 = tuple(sorted((ia, ib)))
            if key2 in seen:
                continue
            seen.add(key2)
            (overlaps if why else bad_overlaps).append([key2[0], key2[1], why or 'disjoint lines', p])

pdf_bytes = open(PDF, 'rb').read()
result = {
    'pdf': {'url': 'https://raw.githubusercontent.com/elliotglazer/diophantine-z-q/'
                   '97cec7fdd757d9a8e4f468151a47a6d3610fb2f2/diophantine_zq.pdf',
            'sha256': hashlib.sha256(pdf_bytes).hexdigest(), 'bytes': len(pdf_bytes), 'pages': NPAGES},
    'coordinates': 'fractions of the displayed page (MediaBox 612x792, no rotation), from the top left: [x, y, w, h]',
    'method': 'TeX words aligned to the PDF text layer (pdftotext -bbox-layout); statements start at their printed '
              'heading, displays are the rows around their printed tag; edges in the blank space between rows, '
              'checked against the page rendered at 144 dpi',
    'layout_check': {'rebuild': 'pdflatex (TeX Live on the build host), run twice', 'pages': [147, NPAGES],
                     'pages with identical text': 0, 'first differing page': 1,
                     'result': 'the committed PDF (xdvipdfmx) is not reproduced; pdfsavepos markers not used'},
    'items': {x['id']: [{'page': p, 'rect': frac(rects[(p, r0, r1)]), 'key': f'p{p:03d}-r{r0:03d}-{r1:03d}'}
                        for (p, r0, r1) in parts[x['id']]] for x in items if parts[x['id']]},
    'unplaced': unplaced,
    'overlaps': overlaps,
}
json.dump(result, open(OUT, 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
report = {
    'items': len(items), 'placed': sum(1 for x in items if parts[x['id']]), 'unplaced': unplaced,
    'regions': sum(len(v) for v in parts.values()), 'distinct boxes': len(boxes),
    'how': Counter(h for v in how.values() for h in v),
    'page anchors': len(chain),
    'numbered items whose number is not in a crop': sorted(k for k, v in number_check.items() if not v),
    'edges on ink': edges_on_ink,
    'overlaps not explained by nesting or shared lines': bad_overlaps,
    'overlaps explained': len(overlaps),
    'displays trimmed of a prose row': TRIMMED,
}
json.dump(report, open(REPORT, 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
print(json.dumps({k: (v if not isinstance(v, (list, dict)) or len(v) < 12 else len(v)) for k, v in report.items()}, indent=0))
