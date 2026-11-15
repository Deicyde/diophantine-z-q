# gt-x6facts (2026-11-14)

**Result.** `babaGranathRationalAb` is discharged. It is proved from the bundle field `elkiesEquationsX6Ab` plus
one new witness-free leaf, `QMPairsCMExist`: over ℚ̄ there are QM pairs with CM by ℤ[i], ℤ[ζ₃] and ℤ[√−6].
* The new leaf is strictly weaker than the field it replaces. It follows from `BabaGranathRationalAb` alone
  (`qmPairsCMExist_of_babaGranath`, through `ShimuraSplit.surj_of_fibre`), so under Elkies the two are equivalent
  (`babaGranathRationalAb_iff`).
* `QMPairsCMExist` is further reduced to its printed setting over ℂ (`QMPairsCMExistC`, Shimura 1967 §§1-3). The
  other inputs are the bundle field `shimuraTaniyamaQbar` and the chain's T11(b) (`qmPairsCMExist_of_C`).

`gonzalezRotgerX6Ab` is not reduced. It stays a published leaf (GR 2006 Thm 5.12), because NoCM uses it for
arbitrary CM orders. Its predictions at the three elliptic CM points match Elkies' conic (computed with PARI:
degree 2, residue fields ℚ(i), ℚ(√−3), ℚ(√−3), 2 points each).

**Compiles (VERIFIED).**
* `ZInQKernel/Contrib/OneProof/X6Facts.lean` imports only `TailZ22` and builds. Every theorem has axioms
  `[propext, Classical.choice, Quot.sound]`.
* `#discharges` (`scratch/gt-x6facts/discharges.txt`): `OpenResearchLeaves16.babaGranathRationalAb` is discharged
  by `babaGranathRationalAb_of_elkies` (still assumes `ElkiesEquationsX6Ab`, `QMPairsCMExist`) and by
  `babaGranathRationalAb_of_printed` (still assumes `ElkiesEquationsX6Ab`, `ShimuraTaniyamaQbar`,
  `QMPairsCMExistC`).
* The autofold spec `scratch/gt-x6facts/autofold-spec.json` dry-runs with the strict count unchanged (47/14 on 61:
  one LEAF replaced by one LEAF). Its generated module `FoldDryRun.lean` compiles.

**What remains.**
* `QMPairsCMExist` needs a QM abelian surface object (E×E or a genus-2 Jacobian as `PkgI3.AbVar`), which is not
  available today.
* The ℂ-form fold must be written by hand, because autofold's `{n}` cannot reach the added bundle.
* Trade-off: after the fold, the CM assignment of `t` rests on Elkies' leaf, which is flagged GLUE in
  `kinds.tsv`, instead of on Baba–Granath's §3.1 table reading.

Report: docs/research/gt-x6facts.md.
