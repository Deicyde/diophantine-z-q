"""Extract a labelled environment (theorem/proposition/lemma) from a TeX file.
usage: extract.py FILE LABEL  -> prints start line and the environment text."""
import sys, re
f, lab = sys.argv[1], sys.argv[2]
L = open(f, encoding='utf-8').read().split('\n')
for i, l in enumerate(L):
    if '\\label{%s}' % lab in l:
        m = re.search(r'\\begin\{(\w+)\}', l)
        j = i
        while not m:
            j -= 1; m = re.search(r'\\begin\{(\w+)\}', L[j])
        env = m.group(1); k = i
        while '\\end{%s}' % env not in L[k]: k += 1
        print('%d-%d' % (j + 1, k + 1)); print('\n'.join(L[j:k + 1])); break
