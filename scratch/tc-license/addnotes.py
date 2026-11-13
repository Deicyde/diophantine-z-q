#!/usr/bin/env python3
"""Insert the Apache-2.0 §4(b) modification line directly under the provenance line."""
import re, sys
root = sys.argv[1] + '/ZInQKernel/Contrib/TauCeti/'
notes = {
 'NumberTheory/ClassFieldTheory/Formation/InvariantKernel.lean': 'Sylow field `isPGroup` renamed to `isPGroup\'` (older Mathlib)',
 'RepresentationTheory/Homological/ContCohomology/Coinduced/Discrete.lean': 'explicit arguments `G A` in the `IsZeroApply`, `IsAddApply`, `IsSMulApply ℕ` instances (older Mathlib)',
 'RepresentationTheory/Homological/GroupCohomology/PrimeIndex.lean': 'Sylow field `isPGroup` renamed to `isPGroup\'`, 2 places (older Mathlib)',
 'RepresentationTheory/Homological/TateCohomology/TrivialityCriterion.lean': 'Sylow field `isPGroup` renamed to `isPGroup\'` (older Mathlib)',
 'Topology/Algebra/Group/Profinite/Generation.lean': '`rfl` added after `simp` in `TauCeti.convergesToOne_iff` (older Mathlib)',
 'Topology/Algebra/Group/Profinite/Sylow/Basic.lean': 'Sylow field `isPGroup` renamed to `isPGroup\'` (older Mathlib)',
 'Topology/Algebra/Group/Profinite/Sylow/Containment.lean': 'added `import ZInQKernel.Contrib.TauCeti.MathlibBackport.Sylow` (older Mathlib)',
 'Topology/Algebra/Group/Profinite/Sylow/Existence.lean': 'Sylow field `isPGroup` renamed to `isPGroup\'` (older Mathlib)',
}
prov = re.compile(r'^-- Vendored from Tau Ceti \(.*\), Apache-2\.0\.\n', re.M)
for rel, what in notes.items():
    p = root + rel
    t = open(p, encoding='utf-8').read()
    assert '-- Modified for the Z-in-Q kernel' not in t, rel
    m = prov.search(t); assert m, rel
    line = f'-- Modified for the Z-in-Q kernel: {what}.\n'
    t = t[:m.end()] + line + t[m.end():]
    open(p, 'w', encoding='utf-8').write(t)
    print(rel)
