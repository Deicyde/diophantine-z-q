"""Check the proposed replacement without writing the catalog or a fold."""
import csv
from pathlib import Path
import sys

sys.path.insert(0, str(Path("scripts/one_proof").resolve()))
import autofold

rows, columns = autofold.load_kinds()
old, = [row for row in rows if row["field"] == "scholzeH1AbVar"]
new = dict(old,
           field="scholzeH1Narrow",
           flag=("pending review: dimension restricted to g = 2; no numbered clause removed "
                 "(de Rham, filtration range, and the rank of Fil^1 all retained); Hodge numbers "
                 "at L10996 uncited; algebraic/analytic and pro-etale/classical comparison "
                 "dictionaries still required; Scholze journal locator UNVERIFIED"),
           source=("diophantine_zq.tex lem:de-rham-descent L10939-10965 and L10996; "
                   "Scholze, Forum Math. Pi 1 (2013), Cor. 1.8 and Thms. 9.1, 9.3 (UNVERIFIED), "
                   "with the corrigendum, Forum Math. Pi 4 (2016) e6"),
           rated_by="pending review")
new["flag_class"] = autofold.flag_class(new["flag"], new["strict"], new["strictest"])
after = [new if row is old else row for row in rows]
fields = {row["field"] for row in after}
problems = autofold.render_open.kinds_row_problems(new, fields, set())
assert not problems, problems

with (Path(__file__).parent / "kinds-row.tsv").open("w") as f:
    w = csv.DictWriter(f, fieldnames=columns, delimiter="\t", lineterminator="\n")
    w.writeheader()
    w.writerow(new)

assert new["kind"] == "consequence" and new["strict"] == new["strictest"] == "GLUE"
print("Catalog row passes kinds_row_problems.")
for label, rs in [("base", rows), ("proposed", after)]:
    n, leaf, glue, leaf_s, glue_s = autofold.counts(rs)
    leaves_strict = sum(r["strict"] == "LEAF" for r in rs)
    leaves_strictest = sum(r["strictest"] == "LEAF" for r in rs)
    print(f"{label}: H {n} total; strict {leaf} LEAF / {glue} GLUE; "
          f"strictest {leaf_s} LEAF / {glue_s} GLUE.")
    print(f"{label}: headline {len(rs)} total; strict {leaves_strict} LEAF / {len(rs)-leaves_strict} GLUE; "
          f"strictest {leaves_strictest} LEAF / {len(rs)-leaves_strictest} GLUE.")
assert autofold.counts(after) == autofold.counts(rows)
