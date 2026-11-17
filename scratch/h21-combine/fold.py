#!/usr/bin/env python3
"""h21-combine: reproduce the manual Main fold h21S -> h21GP on any head whose `frozenTarget` still has the binder
`(h21S : ZInQ.Contrib.H21CSteps.TYZThm21Span)` and its two uses `(ZInQ.Contrib.H21CSteps.tyzThm21PairsC_of_span h21S)`
(autofold.py folds bundle fields only; h21S is a top-level binder). Further autofolds of the bundles `r`, `t`, `l` do
not touch these strings, so the script applies unchanged after them.

Usage, from the repository root (the Contrib modules TYZThm21GChar, H21Lcal, TYZThm21GP must be present):
    python3 scratch/h21-combine/fold.py            # dry run: report what would change
    python3 scratch/h21-combine/fold.py --write    # edit Main.lean and docs/one-proof/kinds.tsv
Then build and run the checks (scratch/h21-combine/checks.sh TAG), render_open.py and frontier_crosswalk.py.
"""
import sys

MAIN = "ZInQKernel/OneProof/Main.lean"
KINDS = "docs/one-proof/kinds.tsv"
ROW = "scratch/h21-combine/kinds-row.tsv"

IMP_OLD = "import ZInQKernel.Contrib.OneProof.TYZThm21Span\n"
IMP_NEW = IMP_OLD + "import ZInQKernel.Contrib.OneProof.TYZThm21GP\n"
BIND_OLD = "(h21S : ZInQ.Contrib.H21CSteps.TYZThm21Span)"
BIND_NEW = "(h21GP : ZInQ.Contrib.H21Combine.TYZThm21SpanGP)"
USE_OLD = "(ZInQ.Contrib.H21CSteps.tyzThm21PairsC_of_span h21S)"
USE_NEW = "(ZInQ.Contrib.H21Combine.tyzThm21PairsC_of_GP h21GP)"
DOC_ANCHOR = "Thm 2.4(1) as the span of the six `f_δ`; `H21CSteps.tyzThm21PairsC_of_span`).\n"
DOC_NEW = DOC_ANCHOR + """
h21-combine replaced `h21S` by `h21GP` (`ZInQ.Contrib.H21Combine.TYZThm21SpanGP`: `h21S` with TYZ's genus character
`χ_{d₁,d₂}`, the character of `K_n(√d₂*)` through Tau Ceti's Artin map, h21-gchar, and TYZ's printed `𝓛²` split on
`ord_{s=1}`, h21-lcal; `H21Combine.tyzThm21PairsC_of_GP`, through `H21GChar.tyzChiCl_eq_gchar` and
`H21Lcal.lcalSqPrinted_eq`).
"""


def main():
    write = "--write" in sys.argv
    s = open(MAIN).read()
    for old, n in [(IMP_OLD, 1), (BIND_OLD, 1), (USE_OLD, 2), (DOC_ANCHOR, 1)]:
        c = s.count(old)
        if c != n:
            sys.exit(f"fold.py: expected {n} occurrence(s) of {old!r} in {MAIN}, found {c}")
    s = s.replace(IMP_OLD, IMP_NEW).replace(BIND_OLD, BIND_NEW).replace(USE_OLD, USE_NEW)
    s = s.replace(DOC_ANCHOR, DOC_NEW)
    k = open(KINDS).read().splitlines(keepends=True)
    idx = [i for i, l in enumerate(k) if l.startswith("frozenTarget\th21S\t")]
    if len(idx) != 1:
        sys.exit(f"fold.py: expected one kinds row frozenTarget/h21S, found {len(idx)}")
    row = [l for l in open(ROW).read().splitlines(keepends=True) if l.startswith("frozenTarget\th21GP\t")]
    assert len(row) == 1
    k[idx[0]:idx[0] + 1] = row
    print(f"Main: binder {BIND_OLD} -> {BIND_NEW}, 2 uses, import TYZThm21GP; kinds: row h21S -> h21GP (line {idx[0] + 1})")
    if write:
        open(MAIN, "w").write(s)
        open(KINDS, "w").write("".join(k))
        print("written")


if __name__ == "__main__":
    main()
