"""Render the next bundle and scratch checks without modifying the active Main."""
import json
import re
from pathlib import Path

work = Path("scratch/hecke-sqrt")
spec = json.loads((work / "autofold.json").read_text())
row, = spec["discharges"]
assert not row["leaves"]
field = row["field"]
base = spec["base"]["bundle"].split(".")[-1]
nxt = spec["next"]["bundle"].split(".")[-1]
top = spec["next"]["top"].split(".")[-1]
old = spec["base"]["top"].split(".")[-1]
source = Path("ZInQKernel/Contrib/OneProof/Y3X6/Top.lean").read_text()
body = source.split(f"structure {base} : Prop where\n", 1)[1].split("\n\n", 1)[0]
body, count = re.subn(rf"(?m)^  /-- [^\n]*\n  {field} : [^\n]*\n?", "", body)
assert count == 1
fields = re.findall(r"(?m)^  (\w+) :", body)
assert len(fields) == 30
inits = "\n".join(f"  {f} := n.{f}" for f in fields)
proof = row["proof"].format(n="n")
imports = "\n".join(f"import {m}" for m in spec["imports"])
fold = f"""{imports}

/-! The next research bundle after `{base}`, discharging the Hecke square root. -/

namespace HDec.HSyn

/-- The open research hypotheses of the Hecke square root fold. -/
structure {nxt} : Prop where
{body.rstrip()}

/-- Supply the former glue field from the surviving `Y₃ → ℙ¹ⱼ` hypothesis. -/
theorem openResearchLeaves59Y3_of_60Y3 (n : {nxt}) : {base} where
{inits}
  {field} := {proof}

/-- The `Y₃` route with one fewer open hypothesis. -/
theorem {top} (r : {nxt}) (t : OpenTextbookLeaves18) (l : OpenAddedLeaves27) :
    ZInQ.SixContactMin :=
  {old} (openResearchLeaves59Y3_of_60Y3 r) t l

end HDec.HSyn

#print axioms HDec.HSyn.{top}
"""
Path(spec["next"]["module"].replace(".", "/") + ".lean").write_text(fold)

pre = Path("scratch/y3-x6b/MainDryRun.lean").read_text()
sig = pre[pre.index("namespace ZInQ.OneProof\n"):]
pre_imports = pre[:pre.index("\n\n")]
after = pre_imports + "\nimport " + spec["next"]["module"]
next_sig = sig.replace(base, nxt).replace(old, top)
(work / "MainDryRun.lean").write_text(after + "\n\n" + next_sig)
engine = Path("ZInQKernel/OneProof/Discharges.lean").read_text()
# The ordinary command treats Contrib structures as atomic. For this check,
# also unpack this specific contribution bundle, which stands in for the
# eventual integrator's OneProof bundle.
engine, count = re.subn(
    r"isStructure env s && isOneProofModule env s &&",
    f"isStructure env s && (isOneProofModule env s ||\n"
    f"    s == `{spec['base']['bundle']} || s == `{spec['next']['bundle']}) &&",
    engine,
)
assert count == 1
(work / "Discharges.lean").write_text(
    after + "\n\n" + engine + "\n" + sig + "\n#discharges\n\n"
    + next_sig.replace("ZInQ.OneProof.frozenTarget", "ZInQ.OneProof.frozenTargetAfter")
    + """
run_cmd do
  let before ← liftTermElabM ZInQ.OneProof.Discharges.openHyps
  let after ← liftTermElabM (ZInQ.OneProof.Discharges.openHyps `ZInQ.OneProof.frozenTargetAfter)
  let suffix := fun (label : String) => (label.splitOn ".").getLast!
  let b := before.map (fun h => suffix h.label)
  let a := after.map (fun h => suffix h.label)
  unless b.filter (· != "heckeSqrtBranchAny") == a && a.size + 1 == b.size do
    throwError "unexpected open-list delta"
  logInfo m!"Open hypotheses including pole completeness: {b.size} → {a.size}; only heckeSqrtBranchAny removed"
"""
)
