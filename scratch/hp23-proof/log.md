# hp23-proof results log

Target: `H29Split.TYZProp23Printed` (hP23), `ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean` L488.
Base: wip/hfx-proof 779d0d7d + merge origin/main (c1e4ed1b) = ee2f8a65.
Build tree: reflink copy of the neron-flt worktree's .lake/build (same Main.lean), then
`lake build ZInQKernel.Contrib.OneProof.TYZTestVectorExists` (scratch/hp23-proof/build1.txt).

## Plan (route of hfx-proof report §7)
1. `tv_eq_sign`: every test vector is `±F` on the double coset `DC(twoRep t)` (from the partition data of
   hfx-proof's `testVector_of_partition`; `fOf F ∈ π_ℤ^{U_n}` + generation + rank one).
2. n ≡ 3: F ∈ {−3, 1}, odd.
3. n ≡ 1: F ∈ {1, −1} off the classes with t.2.2 = 1; `h²` lies in a class with t.2.2 = 0 by the invariant
   `nrd ∈ 2^ℤ(1 + 4ℤ₂)` at 2 (`Good`), with even valuations of `nrd γ` at odd primes.

## Lean (compiled)
- `HP23Proof/Good.lean`: `Good` (= 2^ℤ(1+4ℤ₂)), group laws, `good_sq`, `not_good_int` (m ≡ 3 mod 4), `good_nat`,
  `good_rat` (positive rational with even odd valuations), `even_padicValRat_of_eq`. COMPILES.
- `HP23Proof/Generic.lean`: `PartData`, `inPiZ_fOf`, `tv_eq_sign` (every test vector is ±F on the double cosets),
  `nrdH_βZ_mod4` (decide +kernel), `sq_class` (h² ∈ DC(twoRep t) ⇒ t.2.2 = 0, given H ≤ SgC with Good norms at 2). COMPILES.
- `HP23Proof/Case3.lean`: `partition_three` (copy of hfx `testVector_three` returning PartData; F ∈ {−3,1} odd). COMPILES.
- `HP23Proof/Case1.lean`: `partition_one8` (copy of hfx `testVector_one8` returning PartData, oddness off t.2.2 = 1,
  C1 with Good norms), `tab1_c_ne_two` and `nrd4_check` (decide +kernel), `good_of_loc2OK`. COMPILES.
- `TYZProp23Printed.lean`: `ZInQ.Contrib.HP23Proof.tyzProp23Printed : H29Split.TYZProp23Printed`. COMPILES.
  grep: no sorry/native_decide/axiom/#eval/run_cmd/syntax/macro/notation in the new files.
- `#discharges` (scratch/hp23-proof/Discharges.lean, output Discharges-output.txt):
  `DISCHARGES [hP23] by ZInQ.Contrib.HP23Proof.tyzProp23Printed`, still assumes [], axioms
  [propext, Classical.choice, Quot.sound]. VERIFIED.
- FoldCheck.lean: `frozenTarget_noP23` and `frozenTarget_noHfxP23` compile, standard axioms. VERIFIED.

## Findings
- TYZProp23Printed is true as stated (VERIFIED, compiled), for every test vector (test vectors are exactly ±F).
- n ≡ 1 (mod 8): f_n = 0 exactly on the classes with χ₀(nrd) = −1; squares avoid them by the invariant
  χ₀∘nrd (trivial on B^× and on H). VERIFIED (compiled).
