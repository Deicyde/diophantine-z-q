# Generate the hdec-adopt5a modules of ZInQKernel/HDecomp/ from the scratch drafts (run from the
# worktree root: python3 -I scratch/hdec-adopt5a/adopt5a.py). No draft contains a verbatim copy of
# existing HDecomp code (scratch/hdec-adopt3/dups.py), so each draft becomes one module with the
# same imports; only `import` and `#print` lines are moved, and long lines are wrapped.
import re, os, subprocess
D = 'ZInQKernel/HDecomp/'
DOC = ('/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt5a from\n'
       '`scratch/{src}`{extra}.\n'
       'The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/\n')
DRAFTS = [  # (module, draft path, label, extra)
    ('ModCurves/C9.lean', 'scratch/c9-rhof/C9.lean', 'c9-rhof/C9.lean', ''),
    ('ModCurves/E1Sub.lean', 'scratch/e1-sub/E1Sub.lean', 'e1-sub/E1Sub.lean', ''),
    ('ModCurves/X1Belyi.lean', 'scratch/x1-belyi/X1Belyi.lean', 'x1-belyi/X1Belyi.lean', ''),
    ('Faltings/HodgeLattice.lean', 'scratch/hodge-lattice/HodgeLattice.lean',
     'hodge-lattice/HodgeLattice.lean', ''),
    ('Faltings/H5Neron.lean', 'scratch/hdec-adopt5a/src/H5Neron.lean', 'h5-neron/H5Neron.lean',
     '\n(branch `wip/h5-neron` at b7c1dc21, not yet merged into this base)'),
]
# Hand-wrapped code lines (whitespace-only changes; checked by same.py), applied before wrap.py.
R = {
 '  ∀ (K : Type) [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K] (W : WeierstrassCurve K) [W.IsElliptic]\n':
 '  ∀ (K : Type) [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K] (W : WeierstrassCurve K)\n'
 '    [W.IsElliptic]\n',
 'theorem nTors_card (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (N : ℕ) (hN : 0 < N)\n':
 'theorem nTors_card (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (N : ℕ)\n'
 '    (hN : 0 < N)\n',
 "  have hsub : (minpoly Qj (xCoord P)).rootSet Kbar ⊆ xCoord '' (nTors EjBar N : Set EjBar.toAffine.Point) := by\n":
 "  have hsub : (minpoly Qj (xCoord P)).rootSet Kbar ⊆\n"
 "      xCoord '' (nTors EjBar N : Set EjBar.toAffine.Point) := by\n",
 '      = ((minpoly Qj (xCoord P)).rootSet Kbar).ncard := Nat.card_eq_fintype_card.symm.trans (Nat.card_coe_set_eq _)\n':
 '      = ((minpoly Qj (xCoord P)).rootSet Kbar).ncard :=\n'
 '        Nat.card_eq_fintype_card.symm.trans (Nat.card_coe_set_eq _)\n',
 "    _ ≤ (xCoord '' (nTors EjBar N : Set EjBar.toAffine.Point)).ncard := Set.ncard_le_ncard hsub (hfin.image _)\n":
 "    _ ≤ (xCoord '' (nTors EjBar N : Set EjBar.toAffine.Point)).ncard :=\n"
 "        Set.ncard_le_ncard hsub (hfin.image _)\n",
 '    have hratF : algebraMap ℚ (fieldX1 P) = (algebraMap Qj (fieldX1 P)).comp (algebraMap ℚ Qj) := RingHom.ext_rat _ _\n':
 '    have hratF : algebraMap ℚ (fieldX1 P) = (algebraMap Qj (fieldX1 P)).comp (algebraMap ℚ Qj) :=\n'
 '      RingHom.ext_rat _ _\n',
 '    𝒢.unitSection.stalkMap s (𝒢.G.left.presheaf.germ ⊤ (𝒢.unitSection s) (TopologicalSpace.Opens.mem_top _)\n':
 '    𝒢.unitSection.stalkMap s (𝒢.G.left.presheaf.germ ⊤ (𝒢.unitSection s)\n'
 '      (TopologicalSpace.Opens.mem_top _)\n',
 '    (S).presheaf.germ ⊤ s (TopologicalSpace.Opens.mem_top _) ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c) := by\n':
 '    (S).presheaf.germ ⊤ s (TopologicalSpace.Opens.mem_top _)\n'
 '      ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c) := by\n',
 '    IsUnit ((S).presheaf.germ ⊤ s (TopologicalSpace.Opens.mem_top _) ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv t)) ↔\n':
 '    IsUnit ((S).presheaf.germ ⊤ s (TopologicalSpace.Opens.mem_top _)\n'
 '        ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv t)) ↔\n',
 '      Module.rank (IsLocalRing.ResidueField 𝒢.genStalk) (IsLocalRing.CotangentSpace 𝒢.genStalk) := by\n':
 '      Module.rank (IsLocalRing.ResidueField 𝒢.genStalk)\n'
 '        (IsLocalRing.CotangentSpace 𝒢.genStalk) := by\n',
 '    refine (isLocalization_iff (nonZeroDivisors (𝓞 L)) κ).mpr ⟨fun y => ?_, fun z => ?_, fun {x y} h => ?_⟩\n':
 '    refine (isLocalization_iff (nonZeroDivisors (𝓞 L)) κ).mpr\n'
 '      ⟨fun y => ?_, fun z => ?_, fun {x y} h => ?_⟩\n',
 '    ((Scheme.Hom.comp_apply _ _ _).trans (congrArg (fun y => 𝒢.unitSection y) (toGeneric_pt (L := L))))\n':
 '    ((Scheme.Hom.comp_apply _ _ _).trans\n'
 '      (congrArg (fun y => 𝒢.unitSection y) (toGeneric_pt (L := L))))\n',
 '  refine ⟨fun f g _ => toUnit_unique _ _, fun g => ⟨toUnit Y, hom_ext_of_iso_unit (bcUnitIso K L) _ _⟩⟩\n':
 '  refine ⟨fun f g _ => toUnit_unique _ _,\n'
 '    fun g => ⟨toUnit Y, hom_ext_of_iso_unit (bcUnitIso K L) _ _⟩⟩\n',
 '    ⟨fun _ _ => toUnit_unique _ _, fun z => ⟨fun _ => Submodule.mem_top, fun _ => toUnit_unique _ _⟩,\n':
 '    ⟨fun _ _ => toUnit_unique _ _,\n'
 '      fun z => ⟨fun _ => Submodule.mem_top, fun _ => toUnit_unique _ _⟩,\n',
 "because `i` is injective; `rhoFL_subrep_JL` restates this with `res i`). This is the `U'` that `PkgI3.E1_exists_hom_ne_zero`\n":
 "because `i` is injective; `rhoFL_subrep_JL` restates this with `res i`). This is the `U'` that\n"
 "`PkgI3.E1_exists_hom_ne_zero`\n",
 '/-- **Main result, final form.** `HodgeLatticeTheorem` from one scheme-theoretic fact (local rings of\n':
 '/-- **Main result, final form.** `HodgeLatticeTheorem` from one scheme-theoretic fact (local rings\n'
 'of\n',
 'abelian variety). Mathlib + project only; no `sorry`, no `axiom`. See `docs/research/h5-neron.md`. -/\n':
 'abelian variety). Mathlib + project only; no `sorry`, no `axiom`. See\n'
 '`docs/research/h5-neron.md`. -/\n',
}
made = []; prints = []; used = set()
for dst, src, label, extra in DRAFTS:
    L = open(src, encoding='utf-8').read().splitlines(keepends=True)
    imps = [l.split()[1] for l in L if l.startswith('import ')]
    used |= {l for l in L if l in R}
    L = [R.get(l, l) for l in L]
    body = [l for l in L if not l.startswith('import ')]
    prints += [(dst, l.split()[2]) for l in body if l.startswith('#print axioms ')]
    body = [l for l in body if not re.match(r'#(print|check|eval|exit)', l)]
    while body and not body[0].strip(): body.pop(0)
    while body and not body[-1].strip(): body.pop()
    res = []
    for l in body:  # collapse runs of blank lines left by the cuts
        if not l.strip() and res and not res[-1].strip(): continue
        res.append(l)
    out = (['import ' + i + '\n' for i in imps] + ['\n', DOC.format(src=label, extra=extra), '\n']
           + res)
    open(D + dst, 'w', encoding='utf-8').write(''.join(out)); made.append(D + dst)
assert used == set(R), set(R) - used
subprocess.run(['python3', '-I', 'scratch/hdec-adopt/wrap.py'] + made)
with open('scratch/hdec-adopt5a/prints.txt', 'w') as f:
    for dst, n in prints: f.write(dst + ' ' + n + '\n')
print('\n'.join(made))
