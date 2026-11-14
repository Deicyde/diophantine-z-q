# av-b1 results log

Fields: t6 `PkgI3.HomFreeFinite`, t7 `PkgI3.CharPolyIndepOfEll`, t8 `PkgI3.PoincareReducibility`
(leaf-fold3 §2.2; definitions in ZInQKernel/HDecomp/Objects.lean §3, identical text in
scratch/leaf-fold3/Leaves3.lean under `HDec.PkgI3`).

## 2026-11-13 18:20 PST
- Merged origin/wip/leaf-fold3 (f7951690).
- ZInQKernel/Contrib/AVB1/BaseChange.lean: `bcHom` (Hom base change, additive), `bcHom_injective`
  (projection A_L → A flat+surjective ⇒ epi), `tateBC_homT` (naturality), `tateBC_bijective_closure`
  (T_ℓ(A) → T_ℓ(A_{K̄}) bijective, K̄ = AlgebraicClosure K, no hypothesis). Compiled (lake build), VERIFIED.
- ZInQKernel/Contrib/AVB1/AlgClosed.lean: `homFreeFinite_of_algClosed : HomFreeFiniteAlgClosed →
  PkgI3.HomFreeFinite`, `charPolyIndepOfEll_of_algClosed : CharPolyIndepOfEllAlgClosed →
  PkgI3.CharPolyIndepOfEll`. Compiled, axioms [propext, Classical.choice, Quot.sound] (VERIFIED,
  scratch/av-b1/Axioms1.lean).

## 18:30 PST
- ZInQKernel/Contrib/AVB1/Poincare.lean: `poincareReducibility_of_pieces : PoincareComplement →
  ImageFactorization → SimpleSurjIsogeny → PkgI3.PoincareReducibility`. Glue proved: `f = i ∘ h` ⇒
  `(f, g) = (i, g) ∘ (h ▷ Z)`; `h ▷ Z` finite+surjective by `MorphismProperty.pullbackMap`;
  composition. Compiled, axioms standard three (VERIFIED, Axioms1.lean).
- Pitfall: `MorphismProperty.pullbackMap (P := @Surjective.{0})` needs an explicit
  `IsStableUnderComposition` instance (`IsMultiplicative.toIsStableUnderComposition`); instance search fails.
