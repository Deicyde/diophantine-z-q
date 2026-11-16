# nos-converse (fleet summary)

**Verdict.** `NOSProof.NOSConverseSep` (Serre–Tate 1968 Thm 1, (c) ⇒ (a)) **cannot be proved from the open fields**,
so the target (`r7a` removed, −1, no new leaf) is not reached. There are two reasons, both checked by reading the
Lean statements of every field:

1. Only `neronSchemeExtensionExists` builds a scheme over a DVR, and only over rings of integers of number fields.
   The converse over every field therefore needs BLR §1.4 Thm 3 over an arbitrary DVR, which is not a field.
2. At number fields, the last step of Serre–Tate's proof is in no field and not in Mathlib: if the identity component
   of the Néron special fibre is an abelian variety, then `A` has good reduction (properness).

**Recommendation:** keep `NOSConverseSep` as the leaf.

**Main result (compiles, standard axioms).** `ZInQKernel/Contrib/OneProof/NOSConverseReduction.lean`:

* `neronOggShafarevich_of_open : NeronSchemeModelExistsDVR → neronBaseChangeStrictHenselization →
  raynaudSemistableSH → mumfordTorsionAlgClosed → TorsionInjectsSpecialFibre → DimensionRelation →
  AbelianReductionGood → r7a`.
* `nosConverseNF_of_open`: the same at number fields, with the field `neronSchemeExtensionExists` in place of the
  general BLR theorem.
* Open inputs:
  * `AbelianReductionGood`, LEAF, printed form pending reading (Serre–Tate §1–2 / BLR 7.4 / EGA IV 15.7.10;
    `k` vs `k̄` reading risk);
  * `TorsionInjectsSpecialFibre`, GLUE (needs `[m]` étale on smooth group schemes);
  * `DimensionRelation`, GLUE (`dim B + r ≤ g`).
* Proved outright along Serre–Tate's proof:
  * `InertiaFixedRational`, from `isInertia_of_fixes`: `Aut(K̄/E) ⊆ I_w` for gt-shpair's inertia field, any
    characteristic;
  * `ComponentIndexBound`, from `index_bound`: an open subgroup of a quasi-compact group scheme over `k̄` has finite
    index on `k̄`-points;
  * `NeronSpecialFibreComm` (Néron models of abelian varieties are commutative);
  * `SemiAbelianTorsionBound` (`#U(k̄)[m] ≤ m^r·m^{2a}`);
  * `RankZeroAbelian` (torus rank 0 ⇒ abelian);
  * the counting argument itself.
* `#discharges` re-run (`scratch/nos-converse/Discharges-output.txt`): `r7a` is discharged by
  `neronOggShafarevich_of_open` from the seven inputs above. The autofold dry run (`autofold.json`) gives
  `34/11 → 34/14` and is refused. Do not fold.

**Consumer.** The one live use (LPrefix l. 856, QM surfaces over number fields) reads only the number-field form:
`goodReduction_of_QM_rational3_of_algNF` compiles with `NOSConverseNF` in place of `r7a`. No weaker statement
supplied by the bundles serves it, because the `ℓ`-independence of inertia-triviality is exactly the converse's
content. Substituting the weaker printed leaf `NOSConverseNF` would need a rethread of LPrefix, TailC and TailF.

**Remains.** `TorsionInjectsSpecialFibre`, `DimensionRelation` and the leaf `AbelianReductionGood` (plus BLR 1.4/3
over any DVR, for the general form). Report: docs/research/nos-converse.md. Log: scratch/nos-converse/log.md.
