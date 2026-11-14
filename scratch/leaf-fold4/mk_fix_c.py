#!/usr/bin/env python3
"""TailC edits (after mk_a75.py):
1. a75 (kernel-field New.lean, later commits): its section FS4Copy (copy of g0-fibresimple: B6_isUnit ...
   centralizerOfMatrixEnd0_of_homFree) and the `G0FibreSimple.RigidityHom` copy in section RigCopy are
   deleted: part 40 declares all of them (names checked, same source).
2. a75: `hR1.2.2.2` (R1's naturality clause) becomes `hR1.2.2.2.1`: after pin-apply `R1fpProps` has six
   clauses (g0-assemble2 §4 made the same change elsewhere).
3. a95: `set_option synthInstance.maxHeartbeats 400000 in` on `ofPlus_xi'_pow_ne_zero` (an
   `IsDedekindFiniteMonoid (Localization.Away p)` search times out with the Contrib modules in scope)."""
import re
P='parts/a75_kernelfield.lean'; a=open(P).read()
s=a.index('section FS4Copy'); e=a.index('end FS4Copy')+len('end FS4Copy')
p40=open('parts/40_fibresimple.lean').read()
for n in re.findall(r'^(?:noncomputable )?(?:def|theorem|abbrev) (\S+)', a[s:e], re.M):
    assert re.search(r'^(?:noncomputable )?(?:def|theorem|abbrev) %s\b' % re.escape(n), p40, re.M), n
a=a[:s]+'-- (leaf-fold2) section FS4Copy deleted: part 40 declares B6_isUnit ... centralizerOfMatrixEnd0_of_homFree.'+a[e:]
blk_s=a.index('namespace G0FibreSimple', a.index('section RigCopy')); blk_e=a.index('end G0FibreSimple', blk_s)+len('end G0FibreSimple')
assert 'def RigidityHom' in a[blk_s:blk_e] and a[blk_s:blk_e].count('def ')==1
a=a[:blk_s]+'-- (leaf-fold2) the copy of `G0FibreSimple.RigidityHom` is deleted: part 40 declares it.'+a[blk_e:]
assert a.count('obtain ⟨Q, hQ, hbc⟩ := hR1.2.2.2 K Qbar K.val yK PK hyK')==1
a=a.replace('obtain ⟨Q, hQ, hbc⟩ := hR1.2.2.2 K Qbar K.val yK PK hyK','obtain ⟨Q, hQ, hbc⟩ := hR1.2.2.2.1 K Qbar K.val yK PK hyK')
open(P,'w').write(a)
P='parts/a95_g9.lean'; b=open(P).read()
t="theorem ofPlus_xi'_pow_ne_zero (n : ℕ)"
assert b.count(t)==1
i=b.index(t)
b=b[:i]+'-- (leaf-fold2) instance-search budget, see mk_fix_c.py\nset_option synthInstance.maxHeartbeats 400000 in\n'+b[i:]
open(P,'w').write(b); print('ok')
