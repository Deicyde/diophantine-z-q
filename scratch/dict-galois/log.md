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
