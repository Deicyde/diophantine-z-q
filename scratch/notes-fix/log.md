# notes-fix results log

- 01:47 start. Base 883c4ddf. No earlier run.
- 01:48 Lean: strengthened `LeafQM.AV.fibre_conjugates_isomorphic` (QM/Leaves.lean) to exhibit Y, Φ, π
  (with R1fpProps, R2fpProps), a ℚ̄-point y with π(y) = j₀ and Φ y = [P]; same proof via
  exists_fibre_object + conj_twist_of_rational. Docstrings: Lemma P "lattice cores compiled for N5's μ
  on Λ = 𝒪 only" (QML3, R1fp, QMLeaves); char 0 in R5fp, R5fpCount; R1heckeProps twist parenthesis
  (rv-qm-polar repair 3); Polar.lean header/§8/lemmaP_lattice no longer claim "every QM torus" as compiled.
- 01:48 started `lake build ZInQKernel` (full, no project oleans in the worktree). QM modules built OK
  (QM.Structures 21s, QM.Polar 11s, QM.Leaves 6.1s).
- 01:50-02:10 doc edits, one commit per note: hdec-adopt2 (90/182 verified with git: 182 -> 272 at
  9a826482), leaf-adopt (115 lines / 114 decls, L19202, 19350 lines, five fields verified at 01267822),
  def-faltings (16th #print axioms verified), rv-jac-ext, rv-qm-polar, leaf-qm-fp, leaf-push2 (72 theorems,
  15 print lines verified), rv-blueprints, bp-analytic (section Hom 994-1087 verified), leaf-modcurves,
  glue-t32a (2266 lines, verbatim range diffed SAME), bp-qmmoduli, bp-hecke-fe.
- 01:55 `lake build ZInQKernel`: exit 0, 9991 jobs, 7m37s, 0 errors (build1.txt). VERIFIED.
- 01:57 `lake env lean scripts/print_axioms.lean`: exit 0, 399/399 lists exactly
  [propext, Classical.choice, Quot.sound] (python check; 42 lists are line-wrapped). VERIFIED.
