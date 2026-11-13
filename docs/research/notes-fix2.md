# notes-fix2: fixes for items 1, 3, 4, 6, 7 of the fork's issue #2

Items 2, 5 and 8 (in `scratch/h-decomposition/Leaves.lean`, being ported by other tasks) are
untouched. Issue text: `scratch/notes-fix2/issue2.md`; log and compiler outputs: `scratch/notes-fix2/`.

1. `scratch/leaf-qm-fp/QMLeaves.lean`, `LeafQM.AV.fibre_conjugates_isomorphic`: statement and proof replaced by the kernel's strengthened version (`ZInQKernel/HDecomp/QM/Leaves.lean`: the conclusion now has `Y₃`, `π`, a point `y` with `π(y) = j₀` and `Φ y = [P]`); docstring updated. Compiles (`lake env lean`, exit 0, 0 errors, 28/28 axiom checks standard).
3. `scratch/leaf-qm-fp/QMLeaves.lean`, docstring of `structure QML3`: replaced by the kernel wording (`QM/Structures.lean`: fixed `μ`, characteristic 0, lattice cores only for N5's `μ` on `Λ = 𝒪`, published locators UNVERIFIED, not unique without fixing `μ`). Same compile as item 1.
4. `scratch/rv-qm-polar/QMPolar.lean`: the header (§§5-8; §5 "argued, not compiled at the level of tori"; §8 bullet now "lattice steps of Lemma P for N5's `μ` on `Λ = 𝒪`", with the list of non-compiled steps), the §8 title ("Riemann form on the lattice `𝒪`") and the `lemmaP_lattice` docstring now match the kernel's `QM/Polar.lean`; `diff` against the kernel file shows only the import of `LeafQM`'s order, one line break and the `#print axioms` trailer. Compiles (exit 0, 0 errors, 10/10 axiom checks standard).
6. `scratch/rv-blueprints/R16Transfer.lean`: header rewritten for what the file declares (`BPModCurves.AbVar`, its `IsCommMonObj` instance, `exists_quotient_transfer`), with the M1 context; the copied curve/Jacobian bullets are gone. Compiles (exit 0, no warnings, axioms standard).
7. `scratch/hdec-adopt2/log.md:32`: "93 of them" → "90 of them … (182 before)", with the explanation that 93 is the line count of `axioms_section.lean` (3 header lines + 90 `#print axioms` lines, checked by `wc -l`/`grep -c`). No Lean file.
