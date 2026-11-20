"""Verify the saved Lean runs and render the proposed board patch without editing the board."""

import csv
import difflib
import io
import json
import re
import sys
from collections import Counter
from pathlib import Path

SCRATCH = Path(__file__).resolve().parent
sys.path.insert(0, "scripts/one_proof")
import render_open


def read_run(name):
    raw = (SCRATCH / f"{name}-discharges.txt").read_text()
    plain = re.sub(r"(?m)^scratch/kolyv-weil-port/CheckHeadline\.lean:\d+:\d+: info: ", "", raw)
    records = re.findall(r"(?ms)^DISCHARGES .*?(?=^DISCHARGES |^#discharges:)", plain)
    assert not re.search(r"warning:|error:|sorryAx", raw), name
    metrics = tuple(map(int, re.search(
        r"#discharges: (\d+) open hypotheses, (\d+) theorems checked, (\d+) discharge one", plain
    ).groups()))
    assert len(records) == metrics[2]
    axioms = dict(re.findall(r"(?s)'([^'\n]+)' depends on axioms: \[([^\]]+)\]", plain))
    assert set(axioms) == {
        "ZInQ.OneProof.frozenTarget",
        "ZInQ.Manuscript.KolyvWeil.kolyvaginThm1_of_prints",
        "ZInQ.Manuscript.KolyvWeil.poleCompleteness_of_restrictedConverseGenuine_print",
    }
    assert all(a.split() == ["propext,", "Classical.choice,", "Quot.sound"] for a in axioms.values())
    labels = json.loads(re.search(r"(?m)^OPEN-LABELS (.*)$", plain)[1])
    entries = [json.loads(line) for line in re.findall(r"(?m)^RANK-ENTRY (.*)$", plain)]
    assert len(labels) == len(set(labels)) == metrics[0]
    return metrics, Counter(records), labels, entries


before, old_hits, old_labels, old_entries = read_run("baseline")
after, new_hits, new_labels, new_entries = read_run("spliced")
rank_names = {"hB": "hB6", "hK": "hKPrint"}
assert new_labels == [rank_names.get(h, h) for h in old_labels]
assert [h["field"] for h in old_entries] == list(rank_names)
assert [h["field"] for h in new_entries] == list(rank_names.values())
assert before[:2] == after[:2] and before[2] == after[2] + 1
assert not new_hits - old_hits
removed, = (old_hits - new_hits).elements()
assert removed.splitlines() == [
    "DISCHARGES [hK] by ZInQ.Manuscript.KolyvWeil.kolyvaginThm1_of_prints",
    "  still assumes: [ZInQ.Manuscript.KolyvWeil.BCDTThmA6, ZInQ.Manuscript.KolyvWeil.KolyvaginThm1Print]",
    "  axioms: [propext, Classical.choice, Quot.sound]",
], removed
for label, metrics in (("Baseline", before), ("Spliced", after)):
    print(f"{label}: {metrics[0]} open hypotheses, {metrics[1]} theorems checked, {metrics[2]} matches.")
print(f"Only removed match:\n{removed.rstrip()}\n")

model = render_open.load()
assert not render_open.validate(model)
assert [h["field"] for h in model["hyps"]] == [h.split(".")[-1] for h in old_labels]
assert [h["type"] for h in old_entries] == [model_entry["type"] for model_entry in model["hyps"]
                                           if model_entry["field"] in rank_names]
kinds_path = Path("docs/one-proof/kinds.tsv")
open_path = Path("docs/one-proof/OPEN.md")
board = open_path.read_text()
assert render_open.render(model)[0].rstrip("\n") == board.rstrip("\n")
spec = json.loads(Path("scratch/kolyv-weil-fold/autofold.json").read_text())["discharges"][0]["leaves"]
replacements = {entry["name"]: entry for entry in spec}
old_rows = model["kinds_rows"]
new_rows = []
for row in old_rows:
    field = row["field"]
    if field in rank_names:
        name = rank_names[field]
        row = {**row, "field": name, "rated_by": "the reading desk"}
        leaf = replacements[name]
        for key in ("kind", "flag", "strict", "strictest", "source", "flag_class"):
            row[key] = leaf[key].replace("the owner's ruling", "the lead's ruling")
        row["flag"] = row["flag"].removesuffix(".")
    new_rows.append(row)
new_by_name = {h["field"]: h for h in new_entries}
model["kinds_rows"] = new_rows
model["kinds"] = {r["field"]: r for r in new_rows}
model["hyps"] = [new_by_name.get(rank_names.get(h["field"]), h) for h in model["hyps"]]
assert not render_open.validate(model)

def count(stage, col, rows):
    scopes = ([r for r in rows if r["bundle"] != "frozenTarget"],
              [r for r in rows if r["bundle"] == "frozenTarget"], rows)
    counts = [Counter(r[col] for r in scope) for scope in scopes]
    print(f"{stage} {col}: " + "; ".join(f"{label} {c['LEAF']} LEAF / {c['GLUE']} GLUE"
                                         for label, c in zip(("H", "other", "all"), counts)))


for stage, rows in (("Baseline", old_rows), ("Spliced", new_rows)):
    for col in ("strict", "strictest"):
        count(stage, col, rows)
count("If hKPrint is admitted in strict only,", "strict",
      [{**r, "strict": "LEAF"} if r["field"] == "hKPrint" else r for r in new_rows])
count("If hKPrint is admitted in strictest too,", "strictest",
      [{**r, "strictest": "LEAF"} if r["field"] == "hKPrint" else r for r in new_rows])

tsv = io.StringIO(newline="")
writer = csv.DictWriter(tsv, list(old_rows[0]), delimiter="\t", lineterminator="\n")
writer.writeheader()
writer.writerows(new_rows)
patch = []
new_board = render_open.render(model)[0].rstrip("\n") + board[len(board.rstrip("\n")):]
for path, proposed in ((kinds_path, tsv.getvalue()), (open_path, new_board)):
    patch.append(f"diff --git a/{path} b/{path}\n")
    patch.extend(difflib.unified_diff(path.read_text().splitlines(keepends=True),
                                     proposed.splitlines(keepends=True), f"a/{path}", f"b/{path}", n=1))
(SCRATCH / "board.patch").write_text("".join(patch))
