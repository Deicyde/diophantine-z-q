"""Comment/string-aware hygiene scan (offline tool): forbidden tokens in code (not comments/strings)."""
import sys, os, json, re, collections
sys.path.insert(0, os.path.dirname(__file__))
from leanlex import lex
from graph import ROOT, path_of
FORBID_IDENT = {'sorry', 'admit', 'axiom', 'native_decide', 'run_cmd', 'run_tac', 'initialize', 'builtin_initialize',
                'syntax', 'macro', 'macro_rules', 'elab', 'elab_rules', 'notation', 'infix', 'infixl', 'infixr',
                'prefix', 'postfix', 'declare_syntax_cat', 'implemented_by', 'extern'}
FORBID_SYM = {'#eval', '#exit', '#r2nos_type_eq_warn'}
def scan(path):
    src = open(os.path.join(ROOT, path), encoding='utf-8').read()
    toks = lex(src)
    hits = collections.Counter()
    for i, (k, a, b) in enumerate(toks):
        t = src[a:b]
        if k == 'ident':
            base = t.split('.')[-1]
            if t in FORBID_IDENT:
                hits[t] += 1
            elif t.startswith('r2nos_') or t.startswith('p2m_') or (t.startswith('w03_') and t != 'w03_exact_reverting'):
                hits[t] += 1
            elif t == 'import' and i + 2 < len(toks) and src[toks[i + 2][1]:toks[i + 2][2]].endswith('PortUtilExt'):
                hits['import PortUtilExt'] += 1
        elif k == 'sym' and t == '#':
            nxt = toks[i + 1] if i + 1 < len(toks) else None
            if nxt and nxt[1] == b and nxt[0] == 'ident':
                w = '#' + src[nxt[1]:nxt[2]]
                if w in FORBID_SYM or w in ('#eval', '#print', '#check', '#exit', '#synth', '#reduce'):
                    hits[w] += 1
    return hits
if __name__ == '__main__':
    mods = json.load(open(sys.argv[1]))
    tot = collections.Counter(); per = {}
    for m in mods:
        h = scan(path_of(m))
        if h:
            per[m] = dict(h)
        tot.update(h)
    print(json.dumps({'files': len(mods), 'totals': tot, 'files_with_hits': len(per)}, indent=1))
    for m, h in sorted(per.items()):
        print(m.split('.')[-1][:80], h)
