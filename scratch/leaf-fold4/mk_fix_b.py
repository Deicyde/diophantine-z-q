#!/usr/bin/env python3
"""part a30: `G0Galois.ConjTwistNontrivial` (g10-odd) is deleted; Leaves.lean (leaf-fold) declares it with
the same body (checked)."""
import re
P = 'parts/a30_g10.lean'
p = open(P).read().split('\n'); L = open('olean/LPrefix.lean').read()
for n in ['ConjTwistNontrivial']:
    i = next(i for i,l in enumerate(p) if re.match(r'^(noncomputable )?(def|abbrev) %s\b' % n, l))
    s = i
    while s > 0 and p[s-1].strip() != '': s -= 1
    if s < i and not p[s].startswith('/--'):  # a docstring with a blank line inside: go back to its start
        s = max(j for j in range(i) if p[j].startswith('/--'))
    e = i
    while e < len(p) and p[e].strip() != '': e += 1
    assert '\n'.join(p[i:e]) in L, n
    p = p[:s] + ['-- (leaf-fold2) `G0Galois.%s` deleted: Leaves.lean (leaf-fold) declares it with the same body.' % n] + p[e:]
open(P,'w').write('\n'.join(p)); print('ok')
# part a30: conj-twist's later commit 3ecdd95e added `[NumberField K]` to `ConjUniformization` (N3a); the rest of
# the copied lines 206-1612 is unchanged (diff checked). The definition is updated to the current text so that
# the later sections (part b05) apply.
P = 'parts/a30_g10.lean'; s = open(P).read()
old = "def ConjUniformization : Prop :=\n  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)"
new = "def ConjUniformization : Prop :=\n  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)"
assert s.count(old) == 1
open(P, 'w').write(s.replace(old, new)); print('ok a30 N3a')
