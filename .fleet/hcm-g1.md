# hcm-g1 (fleet note)

**Result.** `hCM : T5Glue.ShimuraMainCM` is proved from a g = 1 leaf plus two textbook leaves, with all glue proved
and only the standard axioms:
`HcmG1.shimuraMainCM_of_g1 : ShimuraThm54 → WeierstrassUniformization → WeierstrassParam → T5Glue.ShimuraMainCM`
(`ZInQKernel/Contrib/OneProof/ShimuraMainCMG1.lean`). The file imports only `RingClassLattice`.

**The new leaf.** `ShimuraThm54` is Shimura 1971 Thm 5.4 (UNVERIFIED locator), stated over:
* Mathlib's `WeierstrassCurve ℂ` with `IsElliptic`;
* `IsAnalyticIso`: a surjective group homomorphism `ℂ → E(ℂ)` with kernel the lattice and holomorphic coordinates off
  it, which is equivalent to an analytic isomorphism `ℂ/L ≅ E(ℂ)`;
* `T5Glue.ArtinCond` (Tau Ceti's arithmetic Artin map), `sInvLat` and `latHat`;
* every lattice of `K`, of any order.

It is rated printed form, flag unread. The final theorem no longer uses `MainTheoremCMArith`, `WeierstrassAbVar`,
`HomLatticeCorr`, the AbVar layer or the adelic dictionary.

**Normalization.** I could not read Shimura §5.2, but a PARI computation settles the direction: for `K = ℚ(√−23)`,
`𝔭 | 2`, the arithmetic Frobenius sends `j(𝒪_K)` to `j(𝔭⁻¹)` (`scratch/hcm-g1/frob_check.py`). That is the
direction `ShimuraMainCM` and the leaf fix. A reading can change only the textual match.

**What compiles (VERIFIED).**
* `lake build` of Main, Discharges and the new file: OK (12995 jobs).
* `#discharges`: DISCHARGES [hCM] by `HcmG1.shimuraMainCM_of_g1`, which still assumes the three leaves; axioms
  standard.
* `FoldCheck.lean` (`frozenTarget` with `hCM` replaced by the three leaves): axioms standard.
* `autofold.json` is written. `autofold.py` refuses it ("not a field of the current bundles: ['hCM']"), so the fold is
  manual.

**What remains.**
* A reading of Shimura 1971 Thm 5.4 / §5.2 (locator and wording).
* The manual fold of `hCM`. It counts −1 GLUE against the re-rated count.

Report: `docs/research/hcm-g1.md`.
