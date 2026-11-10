#!/usr/bin/env python3
"""Compare labelled statements (and the proofs that follow them) in two TeX files.

Usage: python3 -I stmts.py OLD.tex NEW.tex label [label ...]
For each label, find the environment (theorem, lemma, proposition, ...) whose
\\begin line or following line carries \\label{label}; report its line number in
both files, whether the statement block is byte-identical (carriage returns
removed), and whether the immediately following proof block is identical.
Prints only labels, line numbers, line counts and verdicts, no manuscript text.
"""
import re
import sys

BEGIN = re.compile(r'\\begin\{(theorem|lemma|proposition|corollary|definition|hypothesis|remark)\}')


def read(p):
    with open(p, encoding='utf-8', errors='replace') as f:
        return f.read().replace('\r', '').split('\n')


def block(lines, label):
    for i, l in enumerate(lines):
        if '\\label{%s}' % label in l:
            j = i
            while j >= 0 and not BEGIN.search(lines[j]):
                j -= 1
            if j < 0 or i - j > 3:
                return None
            env = BEGIN.search(lines[j]).group(1)
            k = j
            while '\\end{%s}' % env not in lines[k]:
                k += 1
            stmt = lines[j:k + 1]
            # proof following
            m = k + 1
            while m < len(lines) and lines[m].strip() == '':
                m += 1
            proof = None
            if m < len(lines) and lines[m].startswith('\\begin{proof}'):
                n = m
                depth = 0
                while True:
                    depth += lines[n].count('\\begin{proof}') - lines[n].count('\\end{proof}')
                    if depth == 0:
                        break
                    n += 1
                proof = (m + 1, lines[m:n + 1])
            return (j + 1, stmt, proof)
    return None


def main():
    A, B = read(sys.argv[1]), read(sys.argv[2])
    for lab in sys.argv[3:]:
        a, b = block(A, lab), block(B, lab)
        if not a or not b:
            print(f'{lab}: missing (old {bool(a)}, new {bool(b)})')
            continue
        s = 'identical' if a[1] == b[1] else 'CHANGED'
        if a[2] and b[2]:
            p = 'identical' if a[2][1] == b[2][1] else \
                f'CHANGED ({len(a[2][1])} -> {len(b[2][1])} lines)'
            pl = f'proof L{a[2][0]}/L{b[2][0]}'
        else:
            p, pl = 'no adjacent proof', ''
        print(f'{lab}: old L{a[0]} new L{b[0]}; statement {s} '
              f'({len(a[1])}/{len(b[1])} lines); {pl} {p}')


if __name__ == '__main__':
    main()
