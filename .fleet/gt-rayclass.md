# gt-rayclass

**Result.** The two GLUE fields `rayClassCMAb` and `shimuraFamilyAb` of `OpenResearchLeaves19` are proved in one
contribution, `ZInQKernel/Contrib/OneProof/RayClassShimura.lean` (145 KB). The only new input is
`RayClassCFT.ShimuraMainThmIDeligneY3AbU`: Shimura's Main Theorem I in Deligne's adelic form on `Y₃`, with the
moduli clause at every `u ∈ 𝒪̂^×`. The proof also uses the kept textbook fields `uniformizationLeafAll` and
`gagaMorphism`.
- `rayClassCMAb` is proved directly in its abelian-scheme form. It uses no `MumfordRigidityCore`.
- `ClassNumberOneB` (Eichler, adelic form) is now proved: `classNumberOneB_proof`, from the chain's
  `HDec.QMSplit.CNO.principal_of_lattice`, adelic denominators, and ℤ̂-approximation through `PadicInt.appr` and
  the Chinese remainder theorem. It is no longer a leaf.
- `shimuraFamilyAb` comes from `mainThmI_of_U` followed by `shimuraFamilyAb_of_mainThmI`.

**Compiles (VERIFIED).**
- The file: 0 errors.
- `lake build` of Main, Discharges and the module: success.
- `#discharges` matches both fields; all axioms are `[propext, Classical.choice, Quot.sound]`.
- The autofold dry-run module (`scratch/gt-rayclass/FoldCheck.lean`) compiles.
- Strict count: `45/13 on 58 -> 45/12 on 57; strictest 44/14 -> 44/13`.

**Classification.** The new field is entered as **composite** (GLUE), not as a leaf. It combines three printed
results, all locators UNVERIFIED:
- fine-moduli representability (`R1fpPropsAb`);
- Deligne 1971 §4's complex moduli interpretation (clauses 1-3 and U);
- Shimura 1967's reciprocity law (clause 4).

Each clause is weaker than the print. The U form adds only what the print gives on the second component of `Y₃`.
Splitting it into "for every Ψ" leaves would make a false statement (report §3). If a reader re-rates it as
published, the strict count becomes 46/11.

**Remains.** The one composite input. A person still has to read Deligne 1971 §4 and Shimura 1967 to check the
classification. Report: `docs/research/gt-rayclass.md`.
