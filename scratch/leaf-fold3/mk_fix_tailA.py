#!/usr/bin/env python3
"""Two edits to the copied g0-assemble parts that the leaf-fold base (HDec Leaves.lean) needs:
1. part 70: the eight declarations leaf-fold copied into Leaves.lean (`resQ`, `Vb`, `tate`, `Intertwines`,
   `G10Out` from g10-odd; `toRingEquivQ`, `cycQ`, `R14Det` from g0-mod-galois) are deleted here; their
   bodies are textually identical to Leaves.lean's (checked below), so the names resolve to those.
2. part 77: `equivariant_of_asModule`'s `simp` calls no longer close their goals with the kernel Contrib
   modules in scope (Tau Ceti); replaced by explicit rewrites (same statement)."""
import re
p = open('parts/70_galois.lean').read().split('\n')
L = open('olean/LPrefix.lean').read()
dele = set()
for n in ['resQ','Vb','tate','Intertwines','G10Out','toRingEquivQ','cycQ','R14Det']:
    i = next(i for i,l in enumerate(p) if re.match(r'^(noncomputable )?(def|abbrev) %s\b' % n, l))
    s = i
    while s > 0 and p[s-1].strip() != '': s -= 1
    if s < i and not p[s].startswith('/--'):  # a docstring with a blank line inside: go back to its start
        s = max(j for j in range(i) if p[j].startswith('/--'))
    e = i
    while e < len(p) and p[e].strip() != '': e += 1
    assert '\n'.join(p[i:e]) in L, n
    p[s] = '-- (leaf-fold2) `G0Galois.%s` deleted: Leaves.lean (leaf-fold) declares it with the same body.' % n
    dele |= set(range(s+1, e))
p = [l for j,l in enumerate(p) if j not in dele]
open('parts/70_galois.lean','w').write('\n'.join(p))
s = open('parts/77_newform.lean').read()
old = """            map_add' := fun v w => by simp
            map_smul' := fun c v => by
              rw [ρ.asModuleEquiv_symm_map_smul, φ.map_smul,
                Representation.asModuleEquiv_map_smul]
              simp
            left_inv := fun v => by simp
            right_inv := fun w => by simp }, fun g v => ?_⟩
  simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  rw [ρ.asModuleEquiv_symm_map_rho, φ.map_smul, Representation.asModuleEquiv_map_smul]
  simp
"""
new = """            map_add' := fun v w => by simp only [map_add]
            map_smul' := fun c v => by
              rw [ρ.asModuleEquiv_symm_map_smul, φ.map_smul,
                Representation.asModuleEquiv_map_smul, AlgHom.commutes, Module.algebraMap_end_apply]
              rfl
            left_inv := fun v => by
              dsimp only
              rw [σ.asModuleEquiv.symm_apply_apply, φ.symm_apply_apply,
                ρ.asModuleEquiv.apply_symm_apply]
            right_inv := fun w => by
              dsimp only
              rw [ρ.asModuleEquiv.symm_apply_apply, φ.apply_symm_apply,
                σ.asModuleEquiv.apply_symm_apply] }, fun g v => ?_⟩
  -- (leaf-fold2) explicit rewrites instead of `simp` (see mk_fix_tailA.py)
  simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  rw [ρ.asModuleEquiv_symm_map_rho, φ.map_smul, Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_of]
"""
assert s.count(old) == 1
open('parts/77_newform.lean','w').write(s.replace(old, new))
print('ok')
