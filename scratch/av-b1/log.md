# av-b1 results log

Fields: t6 `PkgI3.HomFreeFinite`, t7 `PkgI3.CharPolyIndepOfEll`, t8 `PkgI3.PoincareReducibility`
(leaf-fold3 §2.2; definitions in ZInQKernel/HDecomp/Objects.lean §3, identical text in
scratch/leaf-fold3/Leaves3.lean under `HDec.PkgI3`).

## 2026-11-13 ~18:15 PST
- Merged origin/wip/leaf-fold3 (f7951690).
- ZInQKernel/Contrib/AVB1/BaseChange.lean: `bcHom` (Hom base change, additive), `bcHom_injective`
  (projection A_L → A flat+surjective ⇒ epi), `tateBC_homT` (naturality), `tateBC_bijective_closure`
  (T_ℓ(A) → T_ℓ(A_{K̄}) bijective, K̄ = AlgebraicClosure K, no hypothesis). Compiled (lake build), VERIFIED.
- ZInQKernel/Contrib/AVB1/AlgClosed.lean: `homFreeFinite_of_algClosed : HomFreeFiniteAlgClosed →
  PkgI3.HomFreeFinite`, `charPolyIndepOfEll_of_algClosed : CharPolyIndepOfEllAlgClosed →
  PkgI3.CharPolyIndepOfEll`. Compiled, axioms [propext, Classical.choice, Quot.sound] (VERIFIED,
  scratch/av-b1/Axioms1.lean).

## ~18:22 PST
- ZInQKernel/Contrib/AVB1/Poincare.lean: `poincareReducibility_of_pieces : PoincareComplement →
  ImageFactorization → SimpleSurjIsogeny → PkgI3.PoincareReducibility`. Glue proved: `f = i ∘ h` ⇒
  `(f, g) = (i, g) ∘ (h ▷ Z)`; `h ▷ Z` finite+surjective by `MorphismProperty.pullbackMap`;
  composition. Compiled, axioms standard three (VERIFIED, Axioms1.lean).
- Pitfall: `MorphismProperty.pullbackMap (P := @Surjective.{0})` needs an explicit
  `IsStableUnderComposition` instance (`IsMultiplicative.toIsStableUnderComposition`); instance search fails.

## 18:25 PST
- scratch/av-b1/verbatim_check.py: 26 declarations identical in Objects.lean, scratch/pkg-I3/I3.lean,
  Leaves3.lean (HDec.PkgI3): ALL IDENTICAL (VERIFIED).
- scratch/av-b1/mk_check.py → AVB1Check.lean (111 374 lines, md5 in check.md5): Leaves3.lean + AVB1 files
  renamed `_root_.PkgI3 → _root_.HDec.PkgI3` inside `namespace HDec` + check_tail.lean. Flat run started
  18:24 (`lake env lean`, one process).

## 19:01 PST — flat run 2 (run 1 failed: AlgClosed.lean lacked its closing `end ZInQ.Contrib.AVB1`, fixed)
- `lake env lean scratch/av-b1/AVB1Check.lean` (660161e571cb…): EXIT 0 in 1027 s, 0 errors,
  no sorry; 297 axiom reports, all [propext, Classical.choice, Quot.sound], incl.
  HDec.AVB1Check.{t6_of_algClosed, t7_of_algClosed, t8_of_pieces, t6_t7_t8_of_avb1} (VERIFIED).

## 19:19 PST — flat run 3 (adds SimpleImageIsogeny route)
- Poincare.lean: `SimpleImageIsogeny` (GLUE), `simpleImageIsogeny_of_pieces`,
  `poincareReducibility_of_simpleImage : PoincareComplement → SimpleImageIsogeny → PkgI3.PoincareReducibility`
  (lake build OK, Axioms1.lean standard three, VERIFIED).
- `lake env lean scratch/av-b1/AVB1Check.lean` (md5 9a77a965…): EXIT 0 in 1027 s, 0 errors, no sorry, 301 axiom
  reports; the 13 AVB1 ones (check_axioms_run3.txt) all [propext, Classical.choice, Quot.sound], incl.
  HDec.AVB1Check.{t6_of_algClosed, t7_of_algClosed, t8_of_pieces, t8_of_simpleImage, t6_t7_t8_of_avb1,
  t6_t7_t8_of_avb1'} (VERIFIED). AVB1Check.lean and check_out.txt are not committed (regenerate: mk_check.py).
