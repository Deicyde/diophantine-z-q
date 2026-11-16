# pic-fix log

Base: wip/pic-dict 4e95795b + merge of origin/main (2880fef1e) = 5f3b22f2d. Build tree copied from ~/dzq-check2
(at 2880fef1e); `lake build ZInQKernel.Contrib.OneProof.PicDictionary` OK (12811 jobs, 3 min).

## (1) KLFinite, printed form

* New leaf `PicFix.MumfordKLFiniteSectionAC`: k = k̄, X : AbVar k, c₀ ample with a nonzero global section
  `s : 𝟙 ⟶ modX c₀` ⇒ `{x | phi c₀ x = 1}` finite (Mumford §6 App. 1, (iv) ⇒ (ii), L = 𝒪(D), D effective).
* Glue proved (scratch/pic-fix/KLSection.lean), VERIFIED compiled, axioms [propext, Classical.choice, Quot.sound]:
  * `mk_tensorPow`: [M^{⊗n}] = [M]^n;
  * `support_tensorPowSection`: supp Z(s^{⊗m}) = supp Z(s), m > 0 (local generator, vendored
    `exists_tensorPowSectionOne_eq_pow_smul`, `Hom.ideal_zeroLocus`, Mathlib `basicOpen_pow`);
  * `isAmple_pow`: IsAmple c ⇒ IsAmple (c^n), n > 0;
  * `exists_pow_section`: ample on nonempty X ⇒ some c^m (m > 0) has a nonzero section (`zeroLocus_eq_bot_iff`);
  * `phi_pow`: φ_{L^n}(x) = φ_L(x)^n, so K(L) ⊆ K(L^n) (no theorem of the square needed);
  * `mumfordKLFiniteAC_of_section : MumfordKLFiniteSectionAC → MumfordKLFiniteAC`;
  * `phiAmpleIsogeny_of_printed (hKL : MumfordKLFiniteSectionAC) (h8 : MumfordPhiSurjectiveAC) : PhiAmpleIsogeny`.
* picZeroPtsTranslInv: not an assumption of phiAmpleIsogeny_final (already a theorem in PicDictionary,
  `picZeroPtsTranslInv_of_leaves` with `pushforwardUnitUniversal`, `geomIntegralProd` proved). It is used for
  surjectivity, not finiteness, so the restatement does not touch it.

## (2) PicZeroProper, printed form

* New leaf `PicFix.KleimanPicZeroProper`: K field, X : Over (Spec K) proper and `geometrically IsNormalScheme`
  (Mathlib's `geometrically`; `IsNormalScheme X := ∀ x, IsDomain 𝒪_{X,x} ∧ IsIntegrallyClosed 𝒪_{X,x}`, Stacks 033H),
  P representing `picardFunctor X.hom`, V open with underlying set the identity component ⇒ `IsProper (V.ι ≫ P.hom)`.
* Glue proved (scratch/pic-fix/PicZeroProperN.lean), VERIFIED compiled, standard axioms:
  * `isNormalScheme_of_smooth_field` (vendored FLT `Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime`
    with R = field (UFD), Mathlib `IsAffineOpen.isLocalization_stalk`);
  * `geometricallyNormal_of_smooth`; `picZeroProper_of_kleiman : KleimanPicZeroProper → PicDict.PicZeroProper`;
  * `picZeroAbVar_of_printed (h1 : PicLocFinType) (h2 : IdentityComponentLFT) (h3a : PicZeroSmooth)
    (h3b : KleimanPicZeroProper) : PicZeroAbVar`.

## Deliverable files

* ZInQKernel/Contrib/OneProof/PhiAmpleIsogeny.lean, ZInQKernel/Contrib/OneProof/PicZeroAbVar.lean (namespace PicFix;
  copies of the two scratch files without `#print axioms`). `lake build` of both + Main + Discharges OK.
* `#discharges` (scratch/pic-fix/Discharges.lean → discharges.txt), VERIFIED:
  * `[OpenAddedLeaves17.phiAmpleIsogeny] by PicFix.phiAmpleIsogeny_of_printed` still assumes
    `[PicFix.MumfordKLFiniteSectionAC, PicDict.MumfordPhiSurjectiveAC]`, standard axioms;
  * `[OpenAddedLeaves17.picZeroAbVar] by PicFix.picZeroAbVar_of_printed` still assumes `[PicDict.PicLocFinType,
    PicDict.IdentityComponentLFT, PicDict.PicZeroSmooth, PicFix.KleimanPicZeroProper]`, standard axioms;
  * totals: 56 open hypotheses, 3080 theorems checked, 19 discharge one.
* Autofold dry runs on this base (top TailZ42, sixContactMin_of_open35), VERIFIED (module compiled, line 1 stripped,
  `sixContactMin_of_open36` standard axioms):
  * autofold.json (phiAmpleIsogeny alone; leaves mumfordKLFiniteSectionAC, mumfordPhiSurjectiveAC):
    `strict count: 34/11 on 45 -> 36/10 on 46; strictest 34/11 -> 36/10` (GLUE −1);
  * autofold-both.json (+ picZeroAbVar; leaves picLocFinType, identityComponentLFT, picZeroSmooth flagged
    "pending reading", kleimanPicZeroProper): `34/11 on 45 -> 39/10 on 49; strictest 34/11 -> 39/10`
    (GLUE −1 in total; picZeroAbVar's only GLUE is now picZeroSmooth).
