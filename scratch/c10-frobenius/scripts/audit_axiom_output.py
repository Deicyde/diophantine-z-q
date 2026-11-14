#!/usr/bin/env python3
"""Strict checks for exact Lean transitive-axiom reports, not proof verification."""
from __future__ import annotations

import argparse
from pathlib import Path
import re
from collections.abc import Iterable

ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
REPORT = re.compile(
    r"^'([^'\n]+)' (?:depends on axioms: \[([^\]]*)\]|"
    r"does not depend on any axioms)\s*$",
    re.MULTILINE,
)
REPORT_HEADER = re.compile(
    r"^'([^'\n]+)' (?:depends on axioms:|does not depend on any axioms)",
    re.MULTILINE,
)
DIAGNOSTIC = re.compile(r"\b(?:error|warning)(?:\([^\n]*?\))?:")


def audit_reports(text: str, expected: Iterable[str]) -> dict[str, frozenset[str]]:
    names = list(expected)
    if not names or len(set(names)) != len(names):
        raise ValueError("Expected declarations must be nonempty and unique")
    if DIAGNOSTIC.search(text):
        raise ValueError("Compiler output contains an error or warning")
    matches = list(REPORT.finditer(text))
    if len(matches) != len(REPORT_HEADER.findall(text)):
        raise ValueError("Malformed axiom report")
    found: dict[str, frozenset[str]] = {}
    for match in matches:
        name, raw = match.groups()
        if name in found:
            raise ValueError(f"Duplicate report: {name}")
        tokens = [] if not raw else [token.strip() for token in raw.split(",")]
        if any(not token for token in tokens):
            raise ValueError(f"Malformed axiom list: {name}")
        axioms = frozenset(tokens)
        if axioms - ALLOWED_AXIOMS:
            raise ValueError(f"Unexpected axioms for {name}: {sorted(axioms - ALLOWED_AXIOMS)}")
        found[name] = axioms
    if set(found) != set(names):
        missing, extra = set(names) - set(found), set(found) - set(names)
        raise ValueError(f"Report names differ: missing={sorted(missing)}, extra={sorted(extra)}")
    return found


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path)
    parser.add_argument("--expected", action="append", required=True)
    args = parser.parse_args()
    reports = audit_reports(args.log.read_text(), args.expected)
    print(f"PASS: {len(reports)} exact declaration reports; standard axioms only")


if __name__ == "__main__":
    main()
