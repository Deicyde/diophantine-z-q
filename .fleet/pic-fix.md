# pic-fix: status

**Result.** `phiAmpleIsogeny` now rests on two printed leaves, a fold of −1. `picZeroAbVar` now has
`PicZeroSmooth` as its only GLUE.

**phiAmpleIsogeny.**
* New leaf `PicFix.MumfordKLFiniteSectionAC`: Mumford §6 App. 1 in its printed form, for `L` ample with a nonzero
  global section (`L = 𝒪(D)` with `D = Z(s)` effective).
* The ample case is proved in Lean: `L^m` has a nonzero section, `L^m` is ample (`isAmple_pow`), and
  `K(L) ⊆ K(L^m)` (`phi_pow`).
* `PicFix.phiAmpleIsogeny_of_printed` assumes only that leaf and `MumfordPhiSurjectiveAC`.
* `picZeroPtsTranslInv` was already a theorem in PicDictionary and is not an assumption.
* `scratch/pic-fix/autofold.json` dry run: `34/11 on 45 -> 36/10 on 46; strictest 34/11 -> 36/10`.

**picZeroAbVar.**
* New leaf `PicFix.KleimanPicZeroProper`: Kleiman 9.5.4 for `X` proper and geometrically normal (Mathlib's
  `geometrically`, normal = stalks are integrally closed domains).
* The abelian-variety case is proved from the vendored lemma "smooth ⇒ localizations are integrally closed
  domains".
* `PicFix.picZeroAbVar_of_printed` assumes `PicLocFinType`, `IdentityComponentLFT`, `PicZeroSmooth` and that leaf.
* In `autofold-both.json`, `picZeroSmooth`'s flag begins "pending reading", so it counts GLUE. Stacks 00TV is
  noted as proved on main. Dry run: `34/11 on 45 -> 39/10 on 49`.

**What compiles** (standard axioms only):
* `ZInQKernel/Contrib/OneProof/PhiAmpleIsogeny.lean` and `ZInQKernel/Contrib/OneProof/PicZeroAbVar.lean`;
* `#discharges` (`scratch/pic-fix/discharges.txt`);
* both dry-run fold modules.

**What remains:**
* a one-statement print for `PicZeroSmooth` (BLR 8.4, FGA Explained 9.5 or Milne 1986 §10);
* readings of the UNVERIFIED locators (Mumford §6 App. 1, Kleiman 9.5.4, BLR 8.2 Thm 3);
* `weilPairingMumford` was left alone. It can use `mumfordKLFiniteAC_of_section`, and its four pending
  Weil-pairing leaves need "pending reading" flags before a fold.

Report: `docs/research/pic-fix.md`. Log: `scratch/pic-fix/log.md`.
