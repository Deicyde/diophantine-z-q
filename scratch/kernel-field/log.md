# kernel-field results log

- 05:22 merged origin/wip/{qm-pin,mobius-glue} (g0-mod-field, g4-weilres, inertia-homs, morph-descend already in base).
- KernelField.lean assembled by assemble.sh from verbatim copies: Descend.lean 3-401, InertiaHoms.lean 7-2089,
  G4Closed.lean 1867-1897, Dim.lean 107-305, ModField.lean 17-end (#print lines dropped), then New.lean.
  Copy alone: 0 errors (VERIFIED, build0.txt, ~50 s).
- §6.1 conjugacyData_of_maps (pure algebra: c = n/d well defined, cocycle, inflation, c(1,1)=1,
  kernel identity from |V[n]| = n^4): compiles, 0 errors (VERIFIED, build1.txt).
- §6.2-6.5 compiled, 0 errors, no sorry (VERIFIED, build2.txt). #print axioms = [propext, Classical.choice, Quot.sound] for
  conjugacyData_of_maps, kernelField_core, kernelField_of_model, good_of_QML3, conj_dim, kernelFieldExists_of_pieces.
  Headline: kernelFieldExists_of_pieces (hHFF : HomFreeFinite) (hNOS : NOS) (hRay : RaynaudCriterion) (hTors : TorsionStructure)
    (hCount : TorsionCountPts) (hMaps : ConjMapsOnHomField) : KernelFieldExists.
