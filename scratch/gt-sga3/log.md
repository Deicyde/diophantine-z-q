# gt-sga3 results log

Target: `CToPrinted.SGA3_VIB_3_10` (ZInQKernel/OneProof/H/TailZ19.lean L199):
`∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom], IsOpen (idCompSet G)`.

## Statement audit
- VERIFIED (read): `idCompSet G = {x | x ∈ connectedComponentIn (f⁻¹{f x}) (e (f x))}`, the union of the
  identity components of the fibres (fibre with subspace topology ≃ₜ scheme fibre, Mathlib `fiberHomeo`).
- STANDARD: true (SGA 3 VI_B 3.10 / EGA IV₃ 15.6.5 for smooth G; numbers UNVERIFIED). Not vacuous.
- Its proof in the literature needs EGA IV machinery (limits to noetherian bases, constructibility of
  connectedness of fibres) that Mathlib 4.35 lacks (VERIFIED by survey: no scheme-level constructibility,
  no limit descent of group schemes with connected-fibre control).

## Plan (reduction)
- New leaf `SGA3_VIB_3_10_Nbhd`: for each s, `G⁰` contains an open neighbourhood of `e(s)` (a consequence of
  SGA 3 VI_B 3.10, weaker).
- Glue (Lean): from the leaf + bundle leaf `AVGlue.GeomConnOfRationalPoint` to the full statement:
  translation argument through the fibre over κ(x).

## Compile log
- Part 1 (topology: union of meeting open irreducibles; chain lemma; noetherian quasi-sober point with
  irreducible generizations has an irreducible open nbhd): compiles (VERIFIED).
- Part 2 (`exists_irred_nbhd`: locally noetherian scheme with domain stalks): compiles.
- Part 3 (smooth over field ⇒ stalks regular (CloudW07 `Smooth.isRegularLocalRing_stalk`) ⇒ domains
  (CloudW07 `IsRegularLocalRing.isDomain`); `geomConn_open` from the leaf): compiles.
- Part 4 (`mem_cc_of_mem_idCompSet`, `subset_idCompSet`, `mul_mem`: G⁰ closed under μ over any S, from
  `GeomConnOfRationalPoint`): compiles.
- Part 5 (`exists_point`: translation through κ(x); `sga3_VIB_3_10_of_nbhd`): compiles; `#print axioms
  SGA3IdComp.sga3_VIB_3_10_of_nbhd` = [propext, Classical.choice, Quot.sound] (VERIFIED, scratch/gt-sga3/Part1.lean).
- Contribution file ZInQKernel/Contrib/OneProof/SGA3IdComp.lean = Part1.lean + header (imports TailZ19, CloudW07
  SmoothSourceDescent and RegularLocalRing.Domain).
- Note: fresh worktree lacked lean/.lake ("unknown module prefix ZInQ"); copied from ../gt-blr (identical lean/ZInQ).
- lake build +Main +Discharges +Contrib.OneProof.SGA3IdComp: exit 0 (VERIFIED).
- #discharges (scratch/gt-sga3/Discharges.lean), VERIFIED output:
  DISCHARGES [OpenResearchLeaves16.sga3_VIB_3_10] by SGA3IdComp.sga3_VIB_3_10_of_nbhd
    still assumes: [SGA3IdComp.SGA3_VIB_3_10_Nbhd, AVGlue.GeomConnOfRationalPoint]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 67 open hypotheses, 528 theorems checked, 1 discharge one
