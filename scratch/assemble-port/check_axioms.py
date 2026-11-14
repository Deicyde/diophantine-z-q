"""Count `#print axioms` reports in a Lean output file (multi-line reports joined) and list any that are not exactly
[propext, Classical.choice, Quot.sound]. Usage: python3 -I check_axioms.py out.txt"""
import re, sys
s = open(sys.argv[1]).read()
reps = re.findall(r"^'(.+?)' depends on axioms: \[([^\]]*)\]", s, re.S | re.M)
noax = re.findall(r"'([^']+)' does not depend on any axioms", s)
std = {'propext', 'Classical.choice', 'Quot.sound'}
bad = [(n, a) for n, a in reps if set(x.strip() for x in a.replace('\n', ' ').split(',')) - std]
print('reports:', len(reps), ' no-axiom reports:', len(noax), ' nonstandard:', len(bad))
for n, a in bad: print('  NONSTANDARD', n, a)
for name in sys.argv[2:]:
    print(name, 'reported' if any(n == name for n, _ in reps) else 'NOT REPORTED')
