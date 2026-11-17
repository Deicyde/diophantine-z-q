# y3-audit log

## 2026-11-17 part (1)

- Merged origin/main (27657ffb; frozenTarget over OpenResearchLeaves40, top sixContactMin_of_open58) into wip/y3-audit (clean).
- lean/.lake/build copied from ~/dzq/lean/.lake/build (upstream ZInQ prefix); .lake/build Main.olean matches merged Main.lean (sha1 identical sources in hcm-weierstrass).
- Probe.lean (metaprogram): dependency closure of ZInQ.OneProof.frozenTarget (types, values incl. theorem values, inductive ctors): 273124 constants; 380 constants mention R1fpPropsAb/R1fpProps/PtEquiv/R1fam*/R1univ*/QMAbScheme/QMFamily/IsFibreOf/ShimuraMainThmIDeligneY3AbU; output scratch/y3-audit/probe_out.tsv (VERIFIED, compiled).
  - SGRSplit.ShimuraIntegralModelRep NOT in the closure (VERIFIED): no integral property of Y3 used.
  - fieldPt arguments in values: Qbar, Complex, generic, Subtype (IntermediateField K ⊆ Qbar: RationalFibre, rationalFibre_of_le, KernelField, fieldDescentUnr, fibreDegree_of, residueImage_comp_eq_of_pt), CommRingCat.carrier (residue fields, exists_surjective_of_R1fp) (VERIFIED).
  - Universal family used (QMFamily/IsFibreOf in values): x6ModuliWitness_of_coarse, classify, heckeOfFine_proof, phi_part, elkies_coordinate, R1UnivRigid conversions (VERIFIED).
- Direct consumers of the field shimuraMainThmIDeligneY3AbU in the live copy (EichlerBoundCopy.lean): shimuraFamilyAb_of_U, rayClassCMAb_of_leaves, y3ConnectedAb_of_U, gonzalezRotgerX6Ab_of_print, x6ModuliWitness_of_coarse (VERIFIED, grep).
- R16CoreY unrelated to Y3 (VERIFIED reading R16Split.lean:534).
- Rigidity at level 3 (STANDARD argument, Serre's lemma): Aut(A,ι,η) = roots of unity u in End_O(A) with u-1 ∈ 3End_O(A); |u-1|^2 ≤ 4 < 9 ⇒ u = 1.
- Verdict committed: .fleet/y3-audit-verdict.md.

## part (2)

- ZInQKernel/Contrib/OneProof/Y3RepresentableQ.lean: Y3RepresentableQ (representability over Q, QMAbSchemeP, locally noetherian Q-schemes, QMFamFibre, ∃!), y3FineModuliAbP_of_rep(') and shimuraMainThmIDeligneY3AbU_of_rep('): COMPILED (lake build + lake env lean, no errors) 04:09.
- mumfordTorsionAlgClosed is proved on main (ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof), so the primed versions need no textbook hypothesis.
- scratch/y3-audit/GenFib.lean: ShimuraIntegralModelRep → Y3RepresentableQ via genFib + abBC (base change of QMAbScheme): in progress.
