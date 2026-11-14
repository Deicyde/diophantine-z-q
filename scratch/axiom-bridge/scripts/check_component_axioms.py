#!/usr/bin/env python3
"""Audit the new component log without changing the original nine-checker."""
import json
from pathlib import Path
import re
import sys

EXPECTED = {
    'AxiomBridge.pointsBaseChangeMulEquiv',
    'AxiomBridge.pointsBaseChangeMulEquiv_natural',
    'AxiomBridge.TateConsumer.tate_free_finite',
    'AxiomBridge.TateConsumer.rational_tate_finite',
    'AxiomBridge.TateConsumer.tateModuleFree',
    'AxiomBridge.NativeContinuity.continuous_toMatrix_galRep',
    'AxiomBridge.NativeContinuity.continuous_trace_galRep',
    'AxiomBridge.NativeContinuity.c10_three_native_matrix_continuous',
    'AxiomBridge.NativeContinuity.c10_native_trace_continuous',
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def validate(text):
    seen = {}
    for name, raw in re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", text, re.M):
        if name in seen:
            raise ValueError('Duplicate axiom report: ' + name)
        seen[name] = {part.strip() for part in raw.split(',') if part.strip()}
    if set(seen) != EXPECTED:
        raise ValueError('Component reports missing or unexpected: ' + repr(set(seen) ^ EXPECTED))
    for name, axioms in seen.items():
        if axioms - ALLOWED:
            raise ValueError('Forbidden component axiom: ' + name + repr(axioms - ALLOWED))
    return {name: sorted(seen[name]) for name in sorted(seen)}

if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise SystemExit('usage: check_component_axioms.py COMPONENTS.log')
    print(json.dumps(validate(Path(sys.argv[1]).read_text()), indent=2))
