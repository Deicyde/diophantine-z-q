#!/usr/bin/env python3
"""gr14-narrow: the manual fold of `gaudronRemondThm14` to `GapGR.GaudronRemondThm14Fwd`, as exact edits.

Usage: python3 -I scratch/gr14-narrow/apply_fold.py ROOT [--dry-run]
ROOT is a checkout at the base 43513d87 (leaf-fold25) with ZInQKernel/Contrib/OneProof/GR14Narrow{.lean,/} present.
Every edit asserts that its old text occurs exactly once (per file) before replacing it.
Written for the integration lead; gr14-narrow ran it only on a private copy of the tree (never on the worktree).
"""
import sys, pathlib

H = "ZInQKernel/OneProof/H/"
GR_OLD = "  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14\n"
GR_NEW = "  gaudronRemondThm14 : _root_.GapGR.GaudronRemondThm14Fwd\n"
R19_OLD = "  r19 : ZInQ.DefFaltings.R19_GaudronRemond\n"
R19_NEW = "  r19 : _root_.GapGR.R19Fwd\n"

EDITS = [
    # imports
    (H + "TailD.lean", "import ZInQKernel.OneProof.Genus.Bridge\n",
     "import ZInQKernel.OneProof.Genus.Bridge\nimport ZInQKernel.Contrib.OneProof.GR14Narrow.Chain\n"),
    (H + "TailZ4.lean", "import ZInQKernel.OneProof.H.TailZ3\n",
     "import ZInQKernel.OneProof.H.TailZ3\nimport ZInQKernel.Contrib.OneProof.GR14Narrow.Leaf\n"),
    # the R19 structures on the live path: ResearchLeaves3, OpenResearchLeaves2, 5, 7
    (H + "TailD.lean", R19_OLD, R19_NEW),
    (H + "TailE.lean", R19_OLD, R19_NEW),
    (H + "TailN.lean", R19_OLD, R19_NEW),
    (H + "TailX.lean", R19_OLD, R19_NEW),
    # researchLeaves3_of (dead; from the old ResearchLeaves, whose r19 keeps the two-sided type)
    (H + "TailD.lean", "    r19 := r.r19,\n", "    r19 := _root_.GapGR.r19Fwd_of_r19 r.r19,\n"),
    # reverseIsogeny_of_leaves3 (its only use, TailK L308, is rerouted below): removed
    (H + "TailD.lean",
     "namespace HSyn.G0RevIsog\n\ntheorem reverseIsogeny_of_leaves3 (r : HSyn.ResearchLeaves3) (hDimF : G0Split.DimFinite) :\n"
     "    G0Split.ReverseIsogeny :=\n  reverseIsogeny_of_exists (isogenyReverseExists_of_r19 r.r19 r.h5.1 hDimF)\n\n"
     "end HSyn.G0RevIsog\n",
     "-- gr14-narrow: `HSyn.G0RevIsog.reverseIsogeny_of_leaves3` removed; `gluePieces_of_open4` (TailK) uses\n"
     "-- `GapGR.reverseIsogeny_of_weil` (ZInQKernel/Contrib/OneProof/GR14Narrow/Chain.lean).\n"),
    # E3-E4: the forward half suffices
    (H + "TailD.lean", "  exact transfer_core r.r19 h20 r.r21 ",
     "  exact _root_.GapGR.transfer_core_fwd r.r19 h20 r.r21 "),
    # G17: reverse isogeny from the K̄-point quasi-inverse leaf (= isogenyQuasiInverse_lf7 milneIsogenyQuasiInverse)
    (H + "TailK.lean", "    reverseIsogeny := G0RevIsog.reverseIsogeny_of_leaves3 r3 G0Split.dimFinite\n",
     "    reverseIsogeny := _root_.GapGR.reverseIsogeny_of_weil mulIsogeny_proved l.isogenyQuasiInverse\n"),
    # the row R19 from the forward leaf
    (H + "TailZ4.lean",
     "    _root_.ZInQ.LeafPush2.R18_Javanpeykar ∧ _root_.ZInQ.DefFaltings.R19_GaudronRemond ∧\n",
     "    _root_.ZInQ.LeafPush2.R18_Javanpeykar ∧ _root_.GapGR.R19Fwd ∧\n"),
    (H + "TailZ4.lean", "    _root_.ZInQ.HeightSplit.r19_of_leaves r.gaudronRemondThm14 hN1 r.semistableReductionThm\n",
     "    _root_.GapGR.r19Fwd_of_leaves r.gaudronRemondThm14 hN1 r.semistableReductionThm\n"),
]
# the field in every bundle generation that carries it (OpenResearchLeaves8 ... 22; 10-13 are dead but are
# changed too, so that every `gaudronRemondThm14 := r.gaudronRemondThm14` copy stays well typed)
for f in ["TailZ4", "TailZ9", "TailZ15", "TailZ17", "TailZ19", "TailZ22", "TailZ23", "TailZ25", "TailZ26",
          "TailZ27", "TailZ28", "TailZ29", "TailZ33", "TailZ34", "TailZ35"]:
    EDITS.append((H + f + ".lean", GR_OLD, GR_NEW))


def main():
    root = pathlib.Path(sys.argv[1])
    dry = "--dry-run" in sys.argv
    texts = {}
    for path, old, new in EDITS:
        p = root / path
        s = texts.get(path, p.read_text())
        n = s.count(old)
        if n != 1:
            sys.exit(f"{path}: expected 1 occurrence, found {n}: {old[:80]!r}")
        texts[path] = s.replace(old, new)
        print(f"ok {path}: {old.strip()[:70]!r}")
    if not dry:
        for path, s in texts.items():
            (root / path).write_text(s)
    print(f"{len(EDITS)} edits in {len(texts)} files" + (" (dry run)" if dry else ""))


if __name__ == "__main__":
    main()
