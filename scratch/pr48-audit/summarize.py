"""Rank suggested import cuts. Their elaboration must still be checked by Lean."""

import json
import sys
from collections import defaultdict
from pathlib import Path

data_path, path_map, output_path = map(Path, sys.argv[1:])
paths = dict(line.split("\t") for line in path_map.read_text().splitlines())
scope = set(paths)
imports = defaultdict(set)
refs = defaultdict(set)
mods = {}
witness = {}
done = None

for row in data_path.read_text().splitlines():
    kind, src, item = row.split("\t")
    if kind == "DONE":
        assert done is None
        done = (int(src), int(item))
        continue
    assert src in scope, row
    if kind in {"IMPORT", "KERNEL"}:
        assert item in scope, row
        (imports if kind == "IMPORT" else refs)[src].add(item)
    else:
        assert kind in {"MODULE", "WITNESS"}, row
        target = mods if kind == "MODULE" else witness
        assert src not in target
        target[src] = int(item)

assert done == (len(mods), len(scope)), "incomplete audit"
assert len(mods) > 0 and len(witness) > 0
entry = "ZInQKernel.Contrib.OneProof.DSThm966PrintedProof"
vendor_prefix = "ZInQKernel/Contrib/CloudB3SC5DeligneSerre/Vendor/AnthropicFLT/"
vendor = {module for module, path in paths.items() if path.startswith(vendor_prefix)}
assert entry in mods and entry in witness


def closure(graph, dropped=None):
    seen = {entry}
    stack = [entry]
    while stack:
        node = stack.pop()
        for dependency in graph.get(node, ()):
            if (node, dependency) == dropped or dependency in seen:
                continue
            seen.add(dependency)
            stack.append(dependency)
    return seen


def counts(modules):
    size = bytes_ = 0
    for module in modules:
        with Path(paths[module]).open("rb") as stream:
            for line in stream:
                size += 1
                bytes_ += len(line)
    return {"modules": len(modules), "lines": size, "bytes": bytes_}


imported = closure(imports)
required = closure(refs)
assert set(witness) <= required <= imported <= scope
sizes = {module: counts({module})["lines"] for module in imported & vendor}
cuts = []
for src in required:
    for dep in imports[src] - required:
        lost = imported - closure(imports, dropped=(src, dep))
        if not lost & vendor or lost & required:
            continue
        cuts.append({
            "file": paths[src],
            "drop_import": dep,
            "unreachable_vendor_modules": len(lost & vendor),
            "unreachable_vendor_lines": sum(sizes[m] for m in lost & vendor),
            "unreachable_files": [paths[m] for m in sorted(lost)],
        })
cuts.sort(key=lambda d: (-d["unreachable_vendor_lines"], d["file"], d["drop_import"]))
report = {
    "entry": entry,
    "added_modules": len(scope),
    "loaded_modules": len(mods),
    "imported_vendored_source": counts(imported & vendor),
    "witness_vendored_source": counts(set(witness) & vendor),
    "kernel_closure_preserving_declarations_in_retained_files": counts(required & vendor),
    "single_edge_candidates": len(cuts),
    "top_single_edge_candidates": cuts[:20],
    "interpretation": "Candidate cuts preserve stored declaration references. Tactics and other elaboration dependencies require a fresh source build.",
}
output_path.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report | {"top_single_edge_candidates": [
    {key: val for key, val in cut.items() if key != "unreachable_files"}
    for cut in cuts[:6]
]}, indent=2))
