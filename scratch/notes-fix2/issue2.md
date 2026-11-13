# Fork issue #2 (fact-check of scratch files against the kernel): items as given to notes-fix2

Copied from the task statement (the issue itself is on GitHub, unreachable from the devserver).
Items 2, 5 and 8 touch `scratch/h-decomposition/Leaves.lean` (being ported by two other tasks)
and are left alone by notes-fix2.

1. `scratch/leaf-qm-fp/QMLeaves.lean:1367-1375`: the docstring of `fibre_conjugates_isomorphic`
   says `P` lies at a point of `Y₃` over `j₀`, but the conclusion does not mention `j₀`; copy the
   kernel's strengthened statement (`ZInQKernel/HDecomp/QM/Leaves.lean`, near line 500) with its
   proof if it compiles in the scratch file, otherwise mark the scratch declaration as superseded.
3. `scratch/leaf-qm-fp/QMLeaves.lean:207-210`: the `QML3` docstring states Lemma P (principal
   polarization exists and is unique) without characteristic 0 or a fixed `μ`; use the kernel
   docstring's wording above `structure QML3` in `ZInQKernel/HDecomp/QM/Structures.lean`.
4. `scratch/rv-qm-polar/QMPolar.lean` (line 12, line 31, the §8 title near 568, the
   `lemmaP_lattice` docstring near 713-717) claims Lemma P on every QM torus `ℂ²/𝒪v` while the
   Lean proves only the lattice statement for N5's `μ` on `Λ = 𝒪`; mirror the corrected kernel copy
   `ZInQKernel/HDecomp/QM/Polar.lean`.
6. `scratch/rv-blueprints/R16Transfer.lean:3-19`: the header was copied from `Jacobian.lean`;
   rewrite it for what the file declares (`AbVar`, its commutativity instance,
   `exists_quotient_transfer`).
7. `scratch/hdec-adopt2/log.md:32` says 93 new axiom entries; hdec-adopt2 added 90 (182 before; 93
   was the line count of `axioms_section.lean` with its header); correct it with that explanation.
