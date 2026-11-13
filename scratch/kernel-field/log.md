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
- conjIsogMapsAt_bot (sanity: ConjIsogMapsAt satisfiable for A over ⊥ with the Galois action) compiled (VERIFIED).
- The 4 leaves are bundle fields: ResearchLeaves.r6 (RaynaudCriterion), r7a (NOS); TextbookLeaves.t5 (TorsionStructure),
  t6 (HomFreeFinite) (VERIFIED by reading scratch/h-decomposition/Leaves.lean L32972-33100).
- 06:18 §6.9: copied Tail.lean 38-117, 152-164, 208-282 (B6_isUnit, qmBasis, qm_embeds_end0, FS4 + its proof from T6);
  OMaximal (pure algebra Prop: subring of B ⊇ O with integral elements is ⊆ O); endEqOFibre_of (T27 + T6 + OMaximal →
  EndEqOFibre) and kernelFieldExists_of_split'' (leaves HFF, NOS, Raynaud, TorsionStructure, T27; glue FS5, OMaximal,
  EndTransport, ConjIsogMaps) compiled, standard axioms (VERIFIED, build_final.txt).
- 06:4x §6.10 OMaximal PROVED (oMaximal): int_of_integral (integral ⟹ trd, nrd ∈ ℤ, via modByMonic by X²-tX+n and
  IsIntegrallyClosed.eq_map_mul_C_of_dvd), zmod3_aux/zmod8_aux by decide, lattice argument. Python check
  (omax_cosets.py, sympy/fractions): of the 36 classes of O^∨/O only 0 has integral norm (VERIFIED, computed).
  kernelFieldExists_of_final (leaves HFF, NOS, Raynaud, TorsionStructure, T27; glue FS5, EndTransport, ConjIsogMaps)
  compiled, standard axioms (VERIFIED, build_final.txt).
- blinear_of_twisted_iso (Skolem–Noether descent on homomorphisms: from A7's twisted QM iso e : (A, ι∘α) ≅ (A', ι'),
  μ = e.φ ∘ ι(b), b = N·u ≠ 0, is 𝒪-linear) compiled, standard axioms (VERIFIED, build_final.txt).
- Finding: EndTransport needs rigidity: IsBaseChangeOf / IsModelOver record only a scheme iso (with ι, η compatibility),
  not the group law; η(0)=0 gives 0 ↦ 0, and g0-fibresimple's leaf RigidityHom then makes it a homomorphism.
