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
- 05:48 torsionCountPts_of_leaf (TorsionCountPts from leaf PkgI2.TorsionStructure, via exists_closure_equiv + MonObj.comp_pow)
  and kernelFieldExists_of_leaves (hHFF hNOS hRay hTors hMaps : ConjMapsOnHomField) : KernelFieldExists compiled,
  standard axioms only (VERIFIED, build3.txt).
- 05:51 §6.6: FS5 FibreComTrivial copied verbatim (namespace G0FibreSimple); ConjMapsNoCM (NoCM as explicit
  hypothesis com P.q = ℤ); conjMapsOnHomField_of (FS5 + ConjMapsNoCM → ConjMapsOnHomField) and
  kernelFieldExists_of_leaves_FS5 compiled, standard axioms (VERIFIED, build4.txt).
- 06:0x §6.7 aut_O_inner (every ring automorphism of 𝒪 is conjugation by a unit of B = (2,-3)_ℚ; via
  QuaternionAlgebra.Basis.liftHom on α(i), α(j), RingHom.injective (B simple), TSkolemKW.leafSkolemNoether, agreement on
  2a ∈ ℤ[1,i,j,ij]) compiled, standard axioms (VERIFIED, build5.txt). Import added: ZInQKernel.HDecomp.Textbook.SkolemNoether.
- §6.8 algebra: exists_nat_mul_mem_O, int_of_rat_mem_O, center_O (centre of 𝒪 is ℤ), faithful_O (𝒪 acts faithfully on
  V with |V[n]| = n^4, via star/norm form + aniso_rat) compiled, standard axioms (VERIFIED, build6.txt).
- §6.8 split: endBC copied from bp-qmmoduli; ConjIsogMapsAt (geometric clauses, O-linearity, discrepancy as endomorphism up
  to e ≠ 0); conjMaps_of_qm (TorsCount + End = ι(O) + ConjIsogMapsAt → ConjMaps); ConjIsogMaps, EndEqOOnHomField (Props);
  conjMapsNoCM_of; kernelFieldExists_of_split (HFF, NOS, Raynaud, TorsionStructure, FS5, ConjIsogMaps, EndEqOOnHomField)
  compiled, standard axioms (VERIFIED, build7.txt).
- 06:1x EndEqOOnHomField split into EndEqOFibre (one QM surface over ℚ̄: com = ℤ ⟹ End = ι(O)) and EndTransport (to the Hom
  field); endEqOOnHomField_of, kernelFieldExists_of_split' compiled, standard axioms (VERIFIED, build_final.txt).
