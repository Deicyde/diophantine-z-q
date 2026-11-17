# derham-print (fleet summary)

**Result:** the research field `deRhamH1AbVarT` (GLUE) is proved in Lean from two printed-form leaves and the
textbook field `mumfordTorsionAlgClosed`. `#discharges` shows it discharged, with only the standard axioms. The
autofold dry run gives GLUE 21 → 20 (strict and strictest) and leaves 16 → 18. The generated
`sixContactMin_of_open39` compiles with only the standard axioms.

- New leaves: `DeRhamPrint.DeRhamVpAbVarPrinted`, Fontaine's theorem that `V_p(A)` is de Rham with the printed
  `D_dR`, as recorded in Berger 2004 §I.3; and `DeRhamPrint.BdRInvariantsPrinted`, Fontaine's `B_dR^{G_K} = K` in
  dimension form. Both are rated printed form, unread; locators UNVERIFIED. They are the same statements as
  dict-galois's unfolded pair, so one statement check covers both.
- Duality `V → V^∨` is a Lean proof (dict-galois's generic algebra, reused). `dim V_p A < ∞` comes from T26.
- **Period-ring dictionary closed in Lean** (`ZInQKernel/Contrib/OneProof/DeRhamPrintTDict.lean`): `t = log[ε]` is
  constructed in the kernel's `B_dR^+` for any compatible system of roots of unity (one exists). It satisfies
  `t = ξ·unit`, `B_dR ≅ B_dR^+[1/t]` as `B_dR^+`-algebras, and the Galois action extends uniquely. A `[1/t]`
  print (Berger) is now definition-level, which closes the gap in OPEN.md's kernel-wide B_dR reading.
- Finding: Faltings 1989, Tsuji 1999 and Scholze 2013 Cor. 1.8 are stated for `H^i_ét` (Scholze for rigid
  spaces). They cannot be stated over genuine Lean definitions today, so the Tate-module form is the closest
  print. The consumers need only `dim D_dR`, which is the de Rham clause read by G9.

**Compiles:** `ZInQKernel/Contrib/OneProof/DeRhamPrint.lean` and `DeRhamPrintTDict.lean`;
`scratch/derham-print/{Statement,TDict,Discharges,Axioms,FoldDryRun}.lean`. Spec: `scratch/derham-print/autofold.json`.
Report: `docs/research/derham-print.md`.

**Remains:** statement checks of the two leaves against the prints. Optionally, `σ(t) = χ(σ)t` would remove
the `B_dR^{G_K}=K` leaf, via the Weil pairing `V^∨ ≅ V(-1)`. The fold itself is left to the integrator.
