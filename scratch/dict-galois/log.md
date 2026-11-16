# dict-galois results log

Base: origin/main e22df37cd (leaf-fold30). Fields (kinds.tsv): research/deRhamH1AbVarT, research/hodgeTateDecompAbVar,
research/r7a, added/tateTwistInvariants. Statements: `ZInQ.Contrib.HodgeSplit.{DeRhamH1AbVarT, HodgeTateDecompAbVar,
TateTwistInvariants}` (ZInQKernel/OneProof/H/TailS.lean l. 1992, 347, 69), `PkgI2.NeronOggShafarevich.{0}`
(ZInQKernel/HDecomp/Objects.lean l. 861).

## Setup
- 03:10 build tree copied from ~/dzq-wt/isj1-dict (.lake/build, lean/.lake/build); `lake build
  +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` started (LPrefix and the chain rebuild).

## Findings (VERIFIED = read in the tree)
- Tau Ceti (vendored, ZInQKernel/Contrib/TauCeti) has: `inertiaSubgroup K` = Gal(K̄/K^ur) for a nonarchimedean
  local field; `mem_inertiaSubgroup_of_mk_eq_artinMap` (lifts of Art(unit) lie in inertia);
  `localCyclotomicCharacter_artinMap_padic` (χ(Art_{ℚ_p}(u)) = u⁻¹); `localCyclotomicCharacter_continuous`.
  VERIFIED (read).
- `cyc p σ` (pkg-I4) and `TauCeti.localCyclotomicCharacter p ℚ_[p] σ` are both
  `cyclotomicCharacter (AlgebraicClosure ℚ_[p]) p σ.toRingEquiv` (PadicAlgCl is an abbrev). VERIFIED (read).
- T26 (`PkgI3.TateModuleFree`) is proved from the textbook field `mumfordTorsionAlgClosed`:
  `T5Torsion.TateFree.tateModuleFree_of_torsionStructure (AvSplit.Final.h25 hM)` (LF4T5.lean, TailQ.lean). VERIFIED (read).
- unipotent-b/gt-unip proved (ZInQKernel/Contrib/OneProof/UnipotentForward.lean): `torsion_from_sepClosure`
  (A(Ω)[m] comes from A(K^s), from MulEtaleAbelianScheme), `inertiaRestrict'` (K̄-inertia restricts to K^s-inertia).
  VERIFIED (read).

## Compile outcomes (all `lake env lean`, after the chain build; standard axioms checked with #print axioms)
- 03:41 chain build finished (30 min, exit 0).
- TateTwist.lean: compiles; `TateTwistDict.tateTwistInvariants_of_printed` [propext, Classical.choice, Quot.sound]. VERIFIED.
- HodgeTate.lean: compiles; `HodgeTateDict.hodgeTateDecompAbVar_of_printed` standard axioms. VERIFIED.
- DeRham.lean: compiles after moving the algebra to a generic field `B` (`DeRhamDict.Gen`): with a local
  `Field (BdR p)` instance, `sub_smul`/`LinearMap.ker_eq_bot` on `B ⊗ V` fail to unify (two Semiring paths, and
  AddCommGroup vs AddCommMonoid on the tensor product); `add_smul` works. Instantiation by `@Gen.finrank_Hsp ...
  (bdrField p) (inferInstance : Algebra ℚ_[p] (BdR p))` unifies at default transparency. Standard axioms. VERIFIED.
- NOSSep.lean: compiles; `NOSSepDict.neronOggShafarevich_of_sep` standard axioms. VERIFIED.
- OldStatements.lean: the four chain statements copied verbatim, each `Iff.rfl` to the original. VERIFIED.
- Contrib files ZInQKernel/Contrib/OneProof/{TateTwistInvariants,HodgeTateDecompAbVar,DeRhamH1AbVarT,
  NeronOggShafarevichSep}.lean (local notation expanded): `lake build` OK (25 s).
- `#discharges` (scratch/dict-galois/Discharges.lean, output Discharges-output.txt): VERIFIED
  - DISCHARGES [OpenAddedLeaves17.tateTwistInvariants] by TateTwistDict.tateTwistInvariants_of_printed; still assumes [TateTwistDict.TateTwistInvariantsPrinted]
  - DISCHARGES [OpenResearchLeaves26.hodgeTateDecompAbVar] by HodgeTateDict.hodgeTateDecompAbVar_of_printed; still assumes [HodgeTateDict.HodgeTateDecompAbVarPrinted, AvSplit.MumfordTorsionAlgClosed]
  - DISCHARGES [OpenResearchLeaves26.deRhamH1AbVarT] by DeRhamDict.deRhamH1AbVarT_of_leaves; still assumes [DeRhamDict.DeRhamVpAbVarT, DeRhamDict.BdRInvariantsOver, AvSplit.MumfordTorsionAlgClosed]
  - DISCHARGES [OpenResearchLeaves26.r7a] by NOSSepDict.neronOggShafarevich_of_sep; still assumes [NOSSepDict.NeronOggShafarevichSep]
  - all axioms [propext, Classical.choice, Quot.sound].
- autofold.json dry run: strict 40/8 on 48 -> 41/8 on 49, strictest 39/9 -> 40/9 (GLUE unchanged, one more leaf).
  Dry-run module (AutofoldDry.lean, line 1 stripped) compiles; `HDec.HSyn.sixContactMin_of_open35` standard axioms. VERIFIED.
