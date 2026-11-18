"""ss-faltings generator: writes the chain of the top theorem (default `sixContactMin_of_open76`, module TailZ83) rerouted off SGA 7 IX
Cor. 3.3 (the research field `sga7_IX_Cor3_3_Def34` and its descendants) onto Faltings' invariance of the semistable
height (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`, Faltings 1983) and Raynaud's criterion
(`ZInQ.SSFaltings.SemistableReductionThmIF`, proved in `Contrib/OneProof/SSFaltings.lean`), as one Lean module.

It copies, verbatim up to the renaming `X -> X_sf` (structures `X -> XSF`), every declaration reachable from the top
through declarations whose type mentions a carrier (a structure with a seed field) or a seed type, or whose value
reads a seed field (scratch/ss-faltings/taintS-out.txt), with
* the Cor. 3.3 fields (`sga7_IX_Cor3_3_Def34`, `sga7_IX_Cor3_3`, `sga7_IX_3_3_SHpre`, `sga7_IX_3_3_SH`, `sga7_IX_3_3`,
  `semistablePersistsSHcp`) of a structure replaced by one field `faltingsSemistableHeightBC : FaltingsSemistableHeightBC`
  (their docstrings dropped), and every assignment of them by `faltingsSemistableHeightBC := X.faltingsSemistableHeightBC`;
* height-split's fields SS1 `semistableReductionThm` -> `semistableReductionThmIF : SemistableReductionThmIF`, SS2
  `semistableNeronBaseChange` -> `faltingsSemistableHeightBC`, SS3 `semistablePersists` dropped;
* the binder `hSS : SemistableReductionThm ∧ SemistablePersists` -> `hSS : SemistableReductionThmIF`;
* `ss1_ss3_of14NF_hf_gm_pz_eb` (SS1 and SS3 through Cor. 3.3) -> `SSFaltings.semistableReductionThmIF_of_raynaud`;
* the two readers `heightRowsNo20_of8_hf_eb`, `r20Lower_of8_hf_eb` -> SSFaltings' `r18_of_leavesF`, `r19_of_leavesF`,
  `r21_of_leavesF`, `r22_of_upperF`, `stableHeightFinite_ofF`, `r20Lower_of_leavesF`.
Every edit target is checked: the script stops with an error if one is missing (so it can be rerun on a tree where
another fold changed the chain first; then rerun TaintS.lean on the new top before this script).

Usage (repository root): python3 scratch/ss-faltings/gen/gen_chain.py OUT.lean [TOP_MODULE TOP_THEOREM]"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import copylib
from copylib import emit, find_decl

# TailH erases TauCeti instances at top level: replay `attribute [-instance]` too (sga735-finish's fix)
copylib.CTX = re.compile(copylib.CTX.pattern[:-1] + r"|attribute \[-instance)")

H = "ZInQKernel/OneProof/H/"
TOPMOD = sys.argv[2] if len(sys.argv) > 2 else "ZInQKernel.OneProof.H.TailZ83"
TOP = "HDec.HSyn." + (sys.argv[3] if len(sys.argv) > 3 else "sixContactMin_of_open76")
TS = "scratch/ss-faltings/taintS-out.txt"
F = "_root_.ZInQ.SSFaltings.FaltingsSemistableHeightBC"
IF = "_root_.ZInQ.SSFaltings.SemistableReductionThmIF"
COR33 = ["sga7_IX_Cor3_3_Def34", "sga7_IX_Cor3_3", "sga7_IX_3_3_SHpre", "sga7_IX_3_3_SH", "sga7_IX_3_3",
         "semistablePersistsSHcp"]
SSF = ["semistableReductionThm", "semistableNeronBaseChange", "semistablePersists"]
NEWF = "faltingsSemistableHeightBC"
NEWIF = "semistableReductionThmIF"
WORD = lambda w: r"(?<![\w'.])" + re.escape(w) + r"(?![\w'])"


def parse_lines(path):
    out = {}
    for l in open(path).read().split("\n"):
        m = re.match(r"^([TS]) (\S+) (\S+) USES \[(.*)\]$", l)
        if m:
            kind, mod, name, uses = m.groups()
            out[name] = (kind, mod, [u.strip() for u in uses.split(",") if u.strip()])
    return out


def carriers_of(path):
    for l in open(path).read().split("\n"):
        if l.startswith("carriers "):
            return set(re.findall(r"HDec\.[\w.]+", l))
    raise SystemExit("no carriers line in " + path)


def mod2file(m):
    return m.replace(".", "/") + ".lean"


def newname(n):
    m = re.match(r"^(.*?)('*)$", n)
    base, pr = m.groups()
    if base[0].isupper() and "_" not in base:
        return base + "SF" + pr
    return base + "_sf" + pr


def strip_comments(t):
    return re.sub(r"--.*|/-[\s\S]*?-/", "", t)


def edit_structure(txt, name):
    """Field declarations: Cor. 3.3 fields -> one `faltingsSemistableHeightBC`; SS fields renamed/dropped."""
    lines = txt.split("\n")
    out, i, have_f, n_cor, n_ss = [], 0, False, 0, 0
    # pending docstring lines (a field's docstring precedes it)
    while i < len(lines):
        l = lines[i]
        if re.match(r"^  /--", l):
            j = i
            while "-/" not in lines[j]:
                j += 1
            doc = lines[i:j + 1]
            nxt = lines[j + 1] if j + 1 < len(lines) else ""
            m = re.match(r"^  (\w+) : ", nxt)
            if m and (m.group(1) in COR33 or m.group(1) in SSF):
                i = j + 1  # drop the docstring with its field
                continue
            out.extend(doc)
            i = j + 1
            continue
        m = re.match(r"^  (\w+) : (.*)$", l)
        if m and m.group(1) in COR33:
            if i + 1 < len(lines) and re.match(r"^    \S", lines[i + 1]):
                raise SystemExit(f"{name}: multi-line field {m.group(1)}")
            n_cor += 1
            if not have_f:
                out.append(f"  /-- ss-faltings: Faltings 1983, invariance of the height of a semistable Néron model under "
                           f"finite extension (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`); replaces the SGA 7 IX Cor. 3.3 "
                           f"fields. -/")
                out.append(f"  {NEWF} : {F}")
                have_f = True
            i += 1
            continue
        if m and m.group(1) in SSF:
            if i + 1 < len(lines) and re.match(r"^    \S", lines[i + 1]):
                raise SystemExit(f"{name}: multi-line field {m.group(1)}")
            n_ss += 1
            f = m.group(1)
            if f == "semistableReductionThm":
                out.append("  /-- ss-faltings: semistable reduction over every number field containing `K(A[15])`, from "
                           "Raynaud's criterion (`ZInQ.SSFaltings.semistableReductionThmIF_of_raynaud`); replaces SS1 and "
                           "SS3. -/")
                out.append(f"  {NEWIF} : {IF}")
            elif f == "semistableNeronBaseChange":
                if have_f:
                    raise SystemExit(f"{name}: both a Cor. 3.3 field and SS2")
                out.append("  /-- ss-faltings: Faltings 1983, invariance of the height of a semistable Néron model under "
                           "finite extension; replaces SS2 (SGA 7 IX Cor. 3.3). -/")
                out.append(f"  {NEWF} : {F}")
                have_f = True
            i += 1
            continue
        out.append(l)
        i += 1
    return "\n".join(out), n_cor, n_ss


def edit_assignments(txt, name):
    """`field := expr` lines of structure instances."""
    lines = txt.split("\n")
    out, n = [], 0
    done_f = set()  # one `faltingsSemistableHeightBC :=` per instance block (keyed by the `where` line index)
    block = -1
    for idx, l in enumerate(lines):
        if re.search(r"\bwhere\s*$", l) or re.search(r":= \{\s*$", l):
            block = idx
        m = re.match(r"^(\s+)(\w+) := (.*)$", l)
        if m and (m.group(2) in COR33 or m.group(2) in SSF):
            ind, f, rhs = m.groups()
            if idx + 1 < len(lines) and re.match(r"^" + ind + r"  \S", lines[idx + 1]) and not re.match(r"^\s+\w+ := ", lines[idx + 1]):
                raise SystemExit(f"{name}: multi-line assignment of {f}")
            n += 1
            if f == "semistablePersists":
                continue
            if f == "semistableReductionThm":
                if rhs.strip() == "hSS.1":
                    out.append(f"{ind}{NEWIF} := hSS")
                else:
                    mv = re.search(r"\b(\w+)\.semistableReductionThm\b", rhs)
                    if not mv:
                        raise SystemExit(f"{name}: SS1 assignment not from a field or hSS.1: {rhs}")
                    out.append(f"{ind}{NEWIF} := {mv.group(1)}.{NEWIF}")
                continue
            # Cor. 3.3 field or SS2: read the source bundle's `faltingsSemistableHeightBC`
            mv = re.search(r"\b(\w+)\.(" + "|".join(COR33 + ["semistableNeronBaseChange"]) + r")\b", rhs)
            if not mv:
                raise SystemExit(f"{name}: assignment of {f} reads no Cor. 3.3 field: {rhs}")
            if block in done_f:
                continue
            done_f.add(block)
            out.append(f"{ind}{NEWF} := {mv.group(1)}.{NEWF}")
            continue
        out.append(l)
    return "\n".join(out), n


SS13_BODY = (
    "  _root_.ZInQ.SSFaltings.semistableReductionThmIF_of_raynaud (raynaudSemistable_of14_hf_gm_eb_sf r t)\n"
    "    t.mumfordTorsionAlgClosed t.mulEtaleAbelianScheme\n"
    "    (_root_.GapNeron.neronSchemeModelExistsNF t.neronSchemeExtensionExists)\n"
    "    (_root_.ReductGlue.semistableLocalGlobal_leaf (_root_.CToPrinted.neronLocalizesDVR_of_printed r.blr_1_2_4))")

# each row: alternatives (old reader -> new reader); exactly one alternative of each row must occur in
# `heightRowsNo20_of8_hf_eb` (bost-gr9, fold-b112, moved R21 from TailY's `r21_of_leaves'` to `BostGR9.r21_of_grBost'`)
READER_SUBS = [
    [("_root_.ZInQ.HeightSplit.r18_of_leaves", "_root_.ZInQ.SSFaltings.r18_of_leavesF")],
    [("_root_.ZInQ.HeightSplit.r19_of_leaves", "_root_.ZInQ.SSFaltings.r19_of_leavesF")],
    [("_root_.ZInQ.HeightSplit.r21_of_leaves'", "_root_.ZInQ.SSFaltings.r21_of_leavesF"),
     ("_root_.ZInQ.BostGR9.r21_of_grBost'", "_root_.ZInQ.SSFaltings.r21_of_grBostF'")],
    [("_root_.ZInQ.HeightSplit.r22_of_upper", "_root_.ZInQ.SSFaltings.r22_of_upperF")],
    [("_root_.ZInQ.HeightSplit.stableHeightFinite_of'", "_root_.ZInQ.SSFaltings.stableHeightFinite_ofF")],
]


def carrier_modules(path):
    out = {}
    for l in open(path).read().split("\n"):
        m = re.match(r"^C (\S+) (\S+)$", l)
        if m:
            out[m.group(2)] = m.group(1)
    return out


def main():
    nodes = parse_lines(TS)
    carriers = carriers_of(TS)

    cmods = carrier_modules(TS)

    def carrier_file(cs):
        if cs not in cmods:
            raise SystemExit("no module line (C ...) for carrier " + cs + " in " + TS)
        p = mod2file(cmods[cs])
        if not re.search(r"^structure " + cs.split(".")[-1] + r" ", open(p).read(), re.M):
            raise SystemExit("carrier " + cs + " not found in " + p)
        return p
    cfile = {cs: carrier_file(cs) for cs in carriers}

    def parent(n):
        return next((cs for cs in carriers if n.startswith(cs + ".")), None)

    def is_proj(n):
        cs = parent(n)
        if cs is None:
            return False
        return not find_decl(cfile[cs], cs.split(".")[-1] + "." + n.split(".")[-1])
    copy, todo = set(), [TOP]
    while todo:
        c = todo.pop()
        if c in copy or is_proj(c) or c in carriers:
            continue
        if c not in nodes:
            continue
        copy.add(c)
        todo.extend(nodes[c][2])
    if TOP not in copy:
        raise SystemExit(f"top {TOP} not in the taint output")
    items = []
    for c in sorted(copy):
        mod = nodes[c][1]
        cs = parent(c)
        short = c.split(".")[-1] if cs is None else cs.split(".")[-1] + "." + c.split(".")[-1]
        items.append((mod2file(mod), short, None, c))
    for s in sorted(carriers):
        items.append((cfile[s], s.split(".")[-1], ("structure",), s))
    order, seen = [], set()

    def visit(m):
        if m in seen:
            return
        seen.add(m)
        f = mod2file(m)
        if not os.path.exists(f):
            return
        for l in open(f):
            if l.startswith("import "):
                i = l.split()[1]
                if i.startswith("ZInQKernel"):
                    visit(i)
        order.append(f)
    sys.setrecursionlimit(100000)
    visit(TOPMOD)
    rank = {f: i for i, f in enumerate(order)}
    ren = {}
    for f, s, k, full in items:
        if "." not in s:
            ren[s] = newname(s)
    uniq = {}
    for f, s, k, full in items:
        if f not in rank:
            raise SystemExit(f"{f} not imported by {TOPMOD}")
        hits = find_decl(f, s) if k is None else find_decl(f, s, k)
        if len(hits) != 1:
            raise SystemExit(f"{s} in {f}: {len(hits)} hits")
        uniq[(f, s)] = (rank[f], hits[0], f, s, k, full)
    for need in ["ss1_ss3_of14NF_hf_gm_pz_eb", "heightRowsNo20_of8_hf_eb", "r20Lower_of8_hf_eb",
                 "raynaudSemistable_of14_hf_gm_eb", "researchLeaves9_of_open14_hf_gm_pz_eb"]:
        if not any(s == need for (_, s) in uniq):
            raise SystemExit(f"edit target {need} not in the copied set")
    hss_old = re.compile(r"\(hSS : _root_\.ZInQ\.HeightSplit\.SemistableReductionThm ∧ "
                         r"_root_\.ZInQ\.HeightSplit\.SemistablePersists\)")
    blocks, seen_top, log = [], set(), []
    cnt = {"cor33_fields": 0, "ss_fields": 0, "assign": 0, "hss": 0, "ss13": 0, "rows": 0, "r20": 0}
    for _, _, f, s, k, full in sorted(uniq.values()):
        txt = emit(f, s, ren, (), k, 0, seen_top)
        if k == ("structure",):
            txt, a, b = edit_structure(txt, s)
            cnt["cor33_fields"] += a
            cnt["ss_fields"] += b
        txt, a = edit_assignments(txt, s)
        cnt["assign"] += a
        txt, a = hss_old.subn(f"(hSS : {IF})", txt)
        cnt["hss"] += a
        if s == "ss1_ss3_of14NF_hf_gm_pz_eb":
            new = re.sub(r"_root_\.ZInQ\.HeightSplit\.SemistableReductionThm ∧ _root_\.ZInQ\.HeightSplit\.SemistablePersists :=\n"
                         r"[\s\S]*?\nend HSyn", IF + " :=\n" + SS13_BODY + "\nend HSyn", txt, count=1)
            if new == txt:
                raise SystemExit("ss1_ss3_of14NF_hf_gm_pz_eb: statement/body not found")
            txt = new
            cnt["ss13"] += 1
        if s == "heightRowsNo20_of8_hf_eb":
            for alts in READER_SUBS:
                hit = [(a, b) for a, b in alts if re.search(re.escape(a) + r"(?![\w'])", txt)]
                if len(hit) != 1:
                    raise SystemExit(f"heightRowsNo20_of8_hf_eb: {len(hit)} of the readers {[a for a, _ in alts]} found")
                a, b = hit[0]
                txt = re.sub(re.escape(a) + r"(?![\w'])", b, txt)
            n1 = len(re.findall(r"\br\.semistableReductionThm\b", txt))
            n2 = len(re.findall(r"\br\.semistableNeronBaseChange\b", txt))
            if n1 != 5 or n2 != 5:
                raise SystemExit(f"heightRowsNo20_of8_hf_eb: {n1} SS1, {n2} SS2 reads (expected 5, 5)")
            txt = re.sub(r"\br\.semistableReductionThm\b",
                         f"(_root_.ZInQ.SSFaltings.semistableReductionThm_of_IF r.{NEWIF})", txt)
            txt = re.sub(r"\br\.semistableNeronBaseChange\b", f"r.{NEWF}", txt)
            cnt["rows"] += 1
        if s == "r20Lower_of8_hf_eb":
            a = "_root_.ZInQ.HeightSplit.r20Lower_of_leaves'"
            if a not in txt or not re.search(r"r\.semistableReductionThm r\.semistableNeronBaseChange r\.semistablePersists", txt):
                raise SystemExit("r20Lower_of8_hf_eb: reader call not found")
            txt = txt.replace(a, "_root_.ZInQ.SSFaltings.r20Lower_of_leavesF")
            txt = txt.replace("r.semistableReductionThm r.semistableNeronBaseChange r.semistablePersists",
                              f"r.{NEWIF} r.{NEWF}")
            cnt["r20"] += 1
        body = strip_comments(txt)
        for bad in COR33 + SSF + ["SemistablePersistsSHcp", "SGA7_IX_3_3_SHpre", "SGA7_IX_Cor3_3", "HeightSplit.SemistablePersists",
                                  "HeightSplit.SemistableNeronBaseChange", "HeightSplit.SemistableReductionThm",
                                  "ss1_ss3_of_cpNF", "semistableNeronBaseChange_noSGA3", "shpre_of_cor33"]:
            if re.search(r"(?<![\w'])" + re.escape(bad) + r"(?![\w'])", body):
                raise SystemExit(f"{s}: still mentions {bad}")
        txt = re.sub(r'^local notation "Kd\[" d "\]" => .*\n', "", txt, flags=re.M)
        txt = re.sub(r"Kd\[([^\]]+)\]", r"(AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (\1) : Polynomial ℚ))", txt)
        blocks.append(txt)
        log.append(f"{f}:{s}")
    if cnt["ss13"] != 1 or cnt["rows"] != 1 or cnt["r20"] != 1 or cnt["cor33_fields"] < 1 or cnt["ss_fields"] < 1:
        raise SystemExit(f"edit counts {cnt}")
    hdr = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "header.lean")).read()
    hdr = hdr.replace("@TOPMOD@", TOPMOD).replace("@TOP@", TOP.split(".")[-1])
    top_new = TOP.split(".")[-1] + "_sf"
    open(sys.argv[1], "w").write(hdr + "\n" + "\n".join(blocks) + f"\n#print axioms HDec.HSyn.{top_new}\n")
    print(len(blocks), "blocks;", len(copy), "declarations,", len(carriers), "structures; edits", cnt)
    open("scratch/ss-faltings/gen/copied.txt", "w").write("\n".join(log) + "\n")


if __name__ == "__main__":
    main()
