"""Check Lean's answer to `#print axioms ZInQ.OneProof.frozenTarget`.

Usage: python3 -I scripts/one_proof/check_axioms.py OUTPUT_FILE [THEOREM]

OUTPUT_FILE holds what `lake env lean` printed for a file that imports `ZInQKernel.OneProof.Main` and runs
`#print axioms THEOREM` (THEOREM defaults to ZInQ.OneProof.frozenTarget). The script prints a short Markdown
summary and exits 1 unless the report is there and every axiom in it is one of the three standard ones:
propext, Classical.choice, Quot.sound. A `sorry` shows up as the axiom `sorryAx`, so it fails the check.

The open hypotheses of the theorem are premises in its statement, so they never appear in this list; the list
says only which axioms the Lean proof itself uses.
"""
import os
import re
import sys

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def parse(text, theorem):
    """The set of axioms Lean reports for `theorem`, or None if the report is missing."""
    flat = ' '.join(text.split())
    name = re.escape(theorem)
    if re.search(rf"'{name}' does not depend on any axioms", flat):
        return set()
    found = re.search(rf"'{name}' depends on axioms: \[([^\]]*)\]", flat)
    if not found:
        return None
    return {a.strip() for a in found.group(1).split(',') if a.strip()}


def main(argv):
    if len(argv) < 2:
        sys.exit(__doc__)
    theorem = argv[2] if len(argv) > 2 else 'ZInQ.OneProof.frozenTarget'
    with open(argv[1], encoding='utf-8', errors='replace') as fh:
        axioms = parse(fh.read(), theorem)
    print(f'### Axioms of `{theorem}`')
    print()
    commit = os.environ.get('GITHUB_SHA', '')
    if commit:
        print(f'Commit: `{commit}`')
        print()
    if axioms is None:
        print('**Fail:** the output has no axiom report for this theorem.')
        return 1
    print('Axioms: ' + (', '.join(f'`{a}`' for a in sorted(axioms)) or 'none'))
    print()
    extra = sorted(axioms - ALLOWED)
    if extra:
        print('**Fail:** not standard axioms: ' + ', '.join(f'`{a}`' for a in extra))
        return 1
    print('**Pass:** only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
