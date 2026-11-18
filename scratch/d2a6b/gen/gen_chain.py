"""d2a6-reroute generator (copied and rerun by d2a6b; R6U now carries Y3RouteA.Y3FullThreeRepZ30): writes the chain of `sixContactMin_of_open72` rerouted from R6 (SGA 7 IX 3.5 through
`sga7_IX_3_5_ForwardGeom_Def34`) to `D2A6.R6U` (RaynaudWildNF, diophantine_zq.tex L814-818, and the model of
Y3, L443-477/L529-530), as one Lean module.

It copies, verbatim up to the renaming `X -> X_u` (structures `X -> XU`), every declaration reachable from
`sixContactMin_of_open72` through declarations whose type mentions `PkgI2.RaynaudCriterionNF` or a structure carrying
an IX 3.5 field (`r6`, `semistableUnipotent`, `sga7_IX_3_5_ForwardGeom`, `sga7_IX_3_5_ForwardGeom_Def34`), or whose
value reads such a field (scratch/d2a6b/taintD-out.txt, taintD2-out.txt), with
* `PkgI2.RaynaudCriterionNF.{0}` -> `_root_.HDec.D2A6.R6U` (every occurrence);
* the fields `semistableUnipotent`, `sga7_IX_3_5_ForwardGeom`, `sga7_IX_3_5_ForwardGeom_Def34` -> one field
  `r6u : _root_.HDec.D2A6.R6U`; every assignment of `r6u` or `r6` that reads `X.r6u`/`X.r6` becomes `X.r6u`/`X.r6`
  (the old producers `semistableUnipotent_of_forwardGeom`, `sga7_IX_3_5_ForwardGeom_of_def34`,
  `raynaudCriterion_ofK5` drop out);
* `raynaudCriterionNF_of14_hf_gm_eb` (r6 from Raynaud + IX 3.5 + Neron) -> `r.r6u`;
* the terminal readers of R6 replaced by the wrappers of `Contrib/OneProof/D2A6Wrap.lean` (same signatures, `R6U`):
  `raynaudPlace_of_R6`, `tateWildK_of_R6`, `torsFix_of_descent` (D2), `modelG3G6_of_leaves3` (A6), `good_of_QML3`
  (kernel field; its `3 ∈ T(u)` argument becomes `T324 ⊆ T(u)`).
Usage (repository root): python3 scratch/d2a6b/gen/gen_chain.py OUT.lean"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import copylib
from copylib import emit, find_decl

# TailH erases TauCeti instances at top level: replay `attribute [-instance]` too (sga735-finish's fix)
copylib.CTX = re.compile(copylib.CTX.pattern[:-1] + r"|attribute \[-instance)")

H = "ZInQKernel/OneProof/H/"
TOP = "HDec.HSyn.sixContactMin_of_open73"  # d2a6b on f3402e89: TailZ80 (bost-gr9 bypass), below the count-neutral TailZ81-83 conversions
TD = "scratch/d2a6b/taintD-out.txt"
TD2 = "scratch/d2a6b/taintD2-out.txt"
R6U = "_root_.HDec.D2A6.R6U"
OLDF = ["sga7_IX_3_5_ForwardGeom_Def34", "sga7_IX_3_5_ForwardGeom", "semistableUnipotent"]
TERMINAL = {
    "HDec.G15Ram.raynaudPlace_of_R6": "raynaudPlace_of_R6U",
    "HDec.G15Ram.tateWildK_of_R6": "tateWildK_of_R6U",
    "HDec.G15Ram.torsFix_of_descent": "torsFix_of_R6U",
    "HDec.HSyn.modelG3G6_of_leaves3": "modelG3G6_of_leaves3U",
    "HDec.G0ModField.KernelField.good_of_QML3": "good_of_QML3U",
}
# R6 conversions between the two `PkgI2` copies: identities on `R6U`, their call sites are rewritten to `X.r6`
EXCLUDE = {"HDec.HSyn.raynaudCriterion_ofK5"}


def parse_lines(path, section=None):
    """{name: (module, uses)} from `T/S module name USES [..]` lines (in `section` if given)."""
    out, cur = {}, None
    for l in open(path).read().split("\n"):
        m = re.match(r"^===== (\S+)", l)
        if m:
            cur = m.group(1)
            continue
        if section and cur != section:
            continue
        m = re.match(r"^([TS]) (\S+) (\S+) USES \[(.*)\]$", l)
        if m:
            kind, mod, name, uses = m.groups()
            out[name] = (kind, mod, [u.strip() for u in uses.split(",") if u.strip()])
    return out


def carriers_of(path, section=None):
    cur = None
    for l in open(path).read().split("\n"):
        m = re.match(r"^===== (\S+)", l)
        if m:
            cur = m.group(1)
        if l.startswith("carriers ") and (section is None or cur == section):
            return set(re.findall(r"HDec\.[\w.]+", l))
    raise SystemExit("no carriers line in " + path)


def mod2file(m):
    return m.replace(".", "/") + ".lean"


def newname(n):
    m = re.match(r"^(.*?)('*)$", n)
    base, pr = m.groups()
    if base[0].isupper() and "_" not in base:
        return base + "U" + pr
    return base + "_u" + pr


def main():
    nodes = parse_lines(TD, "IX35")
    nodes2 = parse_lines(TD2)
    for k, v in nodes2.items():
        if k not in nodes:
            nodes[k] = v
        else:
            nodes[k] = (nodes[k][0], nodes[k][1], sorted(set(nodes[k][2]) | set(v[2])))
    carriers = carriers_of(TD, "IX35") | carriers_of(TD2)
    def carrier_file(cs):
        # d2a6b: bost-gr9 copied the bundles into `HDec.HSyn.GR9` under the same short names (TailZ80): match the
        # namespace of the declaration, not only its short name
        short = cs.split(".")[-1]
        hits = []
        for cand in sorted(os.listdir(H)):
            p = H + cand
            if not (cand.endswith(".lean") and re.search(r"^structure " + short + r" ", open(p).read(), re.M)):
                continue
            for i in find_decl(p, short, ("structure",)):
                ns = ".".join(n for op, _, _ in copylib.context(p, i)[1:]
                              for n in [re.sub(r"^namespace ", "", op)] if op.startswith("namespace "))
                if (ns + "." + short) == cs:
                    hits.append((p, i))
        if len(hits) != 1:
            raise SystemExit(f"carrier {cs}: {len(hits)} declarations {hits}")
        return hits[0][0]
    cfile = {cs: carrier_file(cs) for cs in carriers}

    def parent(n):
        return next((cs for cs in carriers if n.startswith(cs + ".")), None)

    def is_proj(n):
        cs = parent(n)
        if cs is None:
            return False
        # `theorem Carrier.x` declared in the source is a dot-notation lemma, not a projection
        return not find_decl(cfile[cs], cs.split(".")[-1] + "." + n.split(".")[-1])
    # reachability from the top through copied nodes
    copy, todo = set(), [TOP]
    while todo:
        c = todo.pop()
        if c in copy or c in TERMINAL or c in EXCLUDE or is_proj(c) or c in carriers:
            continue
        if c not in nodes:
            continue
        copy.add(c)
        todo.extend(nodes[c][2])
    # structures: carriers used by copied declarations (their types) -- copy all carriers that are referenced
    used_carriers = set()
    for c in copy:
        for u in nodes[c][2]:
            if u in carriers or is_proj(u):
                used_carriers.add(u if u in carriers else next(k for k in carriers if u.startswith(k + ".")))
    # carriers mentioned only in types: include every carrier whose name occurs in a copied declaration's source
    items = []
    for c in sorted(copy):
        mod = nodes[c][1]
        cs = parent(c)
        short = c.split(".")[-1] if cs is None else cs.split(".")[-1] + "." + c.split(".")[-1]
        items.append((mod2file(mod), short, None, c))
    # module order
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
    visit("ZInQKernel.OneProof.H.TailZ80")
    rank = {f: i for i, f in enumerate(order)}
    for s in sorted(carriers):
        if cfile[s] not in rank:
            # d2a6b: bundles above the chain top (TailZ81-83's OpenResearchLeaves55-57) are not copied
            continue
        items.append((cfile[s], s.split(".")[-1], ("structure",), s))
    ren = {}
    for f, s, k, full in items:
        if "." not in s:
            ren[s] = newname(s)
    for full, w in TERMINAL.items():
        s = full.split(".")[-1]
        if s in ren:
            raise SystemExit(f"terminal {s} also copied")
        ren[s] = w
    uniq = {}
    for f, s, k, full in items:
        hits = find_decl(f, s) if k is None else find_decl(f, s, k)
        if len(hits) != 1:
            raise SystemExit(f"{s} in {f}: {len(hits)} hits")
        uniq[(f, s)] = (rank[f], hits[0], f, s, k, full)
    swap_r6 = re.compile(r"(?<![\w.'])(_root_\.)?(HDec\.)?PkgI2\.RaynaudCriterionNF(\.\{0\})?(?![\w'])")
    blocks, seen_top, log = [], set(), []
    n_fix = {"r14": 0, "qml3": 0}
    for _, _, f, s, k, full in sorted(uniq.values()):
        txt = emit(f, s, ren, (), k, 0, seen_top)
        txt = swap_r6.sub(R6U, txt)
        # field declarations of the old IX 3.5 fields -> `r6u : R6U`
        for fld in OLDF:
            txt = re.sub(r"^(\s+)" + fld + r" : .*$", r"\1r6u : " + R6U, txt, flags=re.M)
        for fld in OLDF:
            txt = re.sub(r"(?<![\w'])" + fld + r"(?![\w'])", "r6u", txt)
        # assignments reading the field
        txt = re.sub(r"^(\s+)r6u := .*?\b(\w+)\.r6u\b.*$", r"\1r6u := \2.r6u", txt, flags=re.M)
        txt = re.sub(r"^(\s+)r6 := .*?\b(\w+)\.r6\b.*$", r"\1r6 := \2.r6", txt, flags=re.M)
        if s == "raynaudCriterionNF_of14_hf_gm_eb":
            body = re.search(r":=\n(  _root_\.GapNeron\.raynaudCriterion_leavesNF[\s\S]*?)\nend HSyn", txt)
            if not body:
                raise SystemExit("raynaudCriterionNF_of14_hf_gm_eb: body not found")
            txt = txt.replace(body.group(1), "  r.r6u")
            n_fix["r14"] += 1
        if "good_of_QML3U" in txt:
            new = txt.replace("(three_mem_T u))", "(_root_.HDec.D2A6.T324_subset_T u))")
            if new == txt:
                raise SystemExit(f"{s}: good_of_QML3U call without `(three_mem_T u))`")
            txt = new
            n_fix["qml3"] += 1
        for bad in ["semistableUnipotent_of_forwardGeom", "sga7_IX_3_5_ForwardGeom_of_def34", "raynaudCriterion_ofK5",
                    "raynaudCriterion_leavesNF"]:
            if re.search(r"(?<![\w'])" + bad + r"(?![\w'])", re.sub(r"--.*|/-[\s\S]*?-/", "", txt)):
                raise SystemExit(f"{s}: still mentions {bad}")
        txt = re.sub(r'^local notation "Kd\[" d "\]" => .*\n', "", txt, flags=re.M)
        txt = re.sub(r"Kd\[([^\]]+)\]", r"(AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (\1) : Polynomial ℚ))", txt)
        blocks.append(txt)
        log.append(f"{f}:{s}")
    if n_fix["r14"] != 1 or n_fix["qml3"] < 1:
        raise SystemExit(f"edit counts {n_fix}")
    hdr = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "header.lean")).read()
    open(sys.argv[1], "w").write(hdr + "\n" + "\n".join(blocks) +
                                 "\n#print axioms HDec.HSyn.sixContactMin_of_open73_u\n")
    print(len(blocks), "blocks;", len(copy), "declarations,", len(carriers), "structures; edits", n_fix)
    open("scratch/d2a6b/gen/copied.txt", "w").write("\n".join(log) + "\n")


if __name__ == "__main__":
    main()
