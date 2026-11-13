#!/usr/bin/env python3
"""Fail unless Check.lean reports every bridge theorem and only allowed axioms."""
import json
from pathlib import Path
import re
import sys

EXPECTED = {
    "AxiomBridge.pkgI2_of_proper_geometricallyIntegral",
    "AxiomBridge.pkgI2_of_axiom",
    "AxiomBridge.axiom_of_pkgI2",
    "AxiomBridge.abelianVariety_iff",
    "AxiomBridge.jacobian_isAbelianVariety",
    "AxiomBridge.exists_pkgI2_jacobian",
    "AxiomBridge.geometricallyConnected_of_geometricallyIntegral",
    "AxiomBridge.pkgI2_isAbelianScheme_of_fibres",
    "AxiomBridge.pkgI2_hasGoodReduction_of_faltings",
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def validate(text):
    seen = {}
    for name, raw in re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", text, re.M):
        if name in seen:
            raise ValueError("Duplicate axiom report for " + name)
        seen[name] = set(x.strip() for x in raw.split(",") if x.strip())
    for name in re.findall(r"^'([^']+)' does not depend on any axioms$", text, re.M):
        if name in seen:
            raise ValueError("Duplicate axiom report for " + name)
        seen[name] = set()
    missing = EXPECTED - seen.keys()
    if missing:
        raise ValueError("Missing axiom reports: " + ", ".join(sorted(missing)))
    for name, axioms in seen.items():
        if axioms - ALLOWED:
            raise ValueError("Forbidden axioms for " + name + ": " + ", ".join(sorted(axioms - ALLOWED)))
    return {name: sorted(seen[name]) for name in sorted(EXPECTED)}


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: check_axiom_output.py AXIOMS.log")
    print(json.dumps(validate(Path(sys.argv[1]).read_text()), indent=2))
